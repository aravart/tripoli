// ben.h
// author: bsnyder@cs.wisc.edu (Benjamin Snyder)

#ifndef FST_LIB_BEN_H__
#define FST_LIB_BEN_H__

#include <cstring>
#include <exception>
using std::invalid_argument;
#include <algorithm>
#include <unordered_map>
using std::unordered_map;
#include <unordered_set>
using std::unordered_set;

#include <set>
#include <utility>
#include <tuple>
#include <vector>
using std::pair;
using std::make_pair;
using std::tuple;
using std::vector;

#include <fst/fst.h>
#include <fst/mutable-fst.h>
#include <fst/matcher.h>
#include <fst/compose.h>
#include <fst/extensions/pdt/compose.h>
#include <fst/util.h>

namespace fst {

bool ReadIntVectors(const string& filename, vector<vector<int64> > *vectors);
bool ReadNumberedStrings(const string& filename, vector<string> *strings);


typedef int64 Label;  // arc label
typedef int64 Symbol; // grammar symbol
typedef int64 StateId;
typedef int64 RuleId;
typedef vector<Symbol> Rule;  // grammar rule

const int64 kNoRuleId   =  -1;  // Not a valid rule ID

template <class W>
class RuleArc : public ArcTpl<W> {
public:
  RuleArc(Label i, Label o, const Weight& w, StateId s, RuleId r) : ArcTpl<W>(i, o, w, s), rule(r) {}
  RuleId rule;
};


enum ReachType { REACH_UNKNOWN,
                 REACH_YES,
                 REACH_NO = 0};

class GrammarInfo {
public:
  GrammarInfo(Symbol max_term, Symbol max_preterm, Symbol max_nonterm,
              vector<Rule> rules = vector<Rule>(), vector<Symbol> labels_to_symbols = vector<Symbol>())
          : max_term_(max_term), max_preterm_(max_preterm), max_nonterm_(max_nonterm),
            labels_to_symbols_(labels_to_symbols) {

    if (max_term <= 0)
      invalid_argument("max_term should be > 0");
    if (max_preterm != max_term*2)
      invalid_argument("max_preterm should be 2 * max_term");
    if (max_nonterm <= max_preterm)
      invalid_argument("max_nonterm should be > max_preterm");

    SetRules(rules);

    for (Symbol pt = max_term + 1; pt <= max_preterm; ++pt) {
      Symbol t = ToTerm(pt);
      symbol_reach_[pt][t] = REACH_YES;
    }
  }

  static GrammarInfo *Read(const string symbolfile, const string rulefile, const string labelfile) {
    Symbol max_term;
    Symbol max_preterm;
    Symbol max_nonterm;
    vector<Rule> rules;
    vector<Symbol> labels_to_symbols;
    if (!ReadIntVectors(rulefile, &rules))
      invalid_argument("cannot read rule file");
    if (!ReadSymbolFile(symbolfile, &max_term, &max_preterm, &max_nonterm))
      invalid_argument("cannot read grammar-symbols file");
    if (!ReadLabelFile(labelfile, &labels_to_symbols, max_term))
      invalid_argument("cannot read labels file");
    return new GrammarInfo(max_term, max_preterm, max_nonterm, rules, labels_to_symbols);
  }

  static bool ReadSymbolFile(const string& filename, Symbol *max_term,
                      Symbol *max_preterm, Symbol *max_nonterm) {
    vector<string> symbols;
    ReadNumberedStrings(filename, &symbols);
    bool in_preterms = false;
    bool in_nonterms = false;
    size_t i = 1;
    for (; i < symbols.size(); ++i) {
      string sym = symbols[i];
      if (sym[0] == '_') {
        if (!in_preterms && !in_nonterms) {
          *max_term = i - 1;
          in_preterms = true;
        }
        if (!in_preterms)
          return false;
        if (strcmp(sym.c_str() + 1, symbols[i - *max_term].c_str()))
          return false;
      }
      else if (in_preterms) {
        *max_preterm = i - 1;
        in_preterms = false;
        in_nonterms = true;
      }
    }
    if (in_nonterms) {
      *max_nonterm = i;
      return true;
    }
    return false;
  }

  static bool ReadLabelFile(const string& filename, vector<Symbol> *labels_to_symbols, const Symbol max_term) {
    vector<string> labels;
    ReadNumberedStrings(filename, &labels);
    labels_to_symbols->push_back(-1);
    for (size_t i = 1; i < labels.size(); ++i) {
      string label = labels[i];
      if (label[0] != '+' && label[0] != '-') {
        if (i > max_term)
          return false;
        labels_to_symbols->push_back(i);
      }
      else {
        if (i <= max_term) return false;
        char *sym_str = strpbrk(label.c_str(), "P");
        if (!sym_str) return false;
        bool err;
        Symbol sym = StrToInt64(sym_str, filename, i, false, &err);
        if (err) return false;
        labels_to_symbols->push_back(sym);
      }
    }
    return true;
  }

  bool IsTerm(Symbol s) { return s > 0 && s <= max_term_; }
  bool IsPreterm(Symbol s) { return s > max_term_ && s <= max_preterm_; }
  bool IsNonterm(Symbol s) { return s > max_preterm_ && s <= max_nonterm_; }
  Symbol LabelToSymbol(Label l) { return labels_to_symbols_[l]; }

  Symbol ToPreterm(Symbol t) {
    if (t <= max_term_)
      return max_term_ + t;
    else return -1;
  }
  Symbol ToTerm(Symbol pt) {
    if (pt > max_term_ && pt <= max_preterm_)
      return pt - max_term_
    else return -1;
  }

  bool SymbolCanReach(Symbol nonterm, Symbol term) {
    if (IsTerm(nonterm) || !IsTerm(term))
      invalid_argument("SymbolCanReach: nonterm must not be term, and term must be term");

    ReachType cached = symbol_reach_[nonterm][term];
    if (cached != REACH_UNKNOWN)
      return cached;

    symbol_reach_[nonterm][term] = REACH_NO;  // prevent infinite loops
    vector<Symbol> replacements = replacement_symbols_[nonterm];
    for (vector<Symbol>::const_iterator it = replacements.begin();
                                        it != replacements.end(); ++it) {
      if (SymbolCanReach(*it, term)) {
        symbol_reach_[nonterm][term] = REACH_YES;
        return true;
      }
    }
    return false;
  }

  bool RuleCanReach(RuleId rule, Symbol term) {
    //TODO cache separately for speed-up
    return SymbolCanReach(rules_[rule][1], term);
  }

  void ValidateRule(Rule rule) {
    if (rule.size() < 2)
      invalid_argument("invalid rule: must have at least two symbols");
    if (rule.size() == 2 && IsPreterm(rule[0]) && IsTerm(rule[1])) { // unary terminal production
      Symbol pterm = rule[0];
      Symbol term = rule[1];
      if (ToTerm(pterm) != term)
        invalid_argument("invalid rule: preterm and term do not match in unary production");
    }
    else {  // not a unary terminal production
      Rule::const_iterator it = rule.begin();
    if (!IsNonterm(*it))
      invalid_argument("invalid rule: non-unary production must have non-terminal left-hand symbol");
    for (++it; it != rule.end(); ++it)
      if (!(IsNonterm(*it) || IsPreterm(*it)))
        invalid_argument("invalid rule: non-unary production must not have terminal right-hand symbols");
    }
  }

  void SetRules(const vector<Rule>& rules) {
    rules_ = rules;
    replacement_symbols_ = vector<vector<Symbol> >(max_nonterm_+1, vector<Symbol>());
    for (ssize_t i = 0; i < rules.size(); ++i) {
      Rule rule = rules[i];
      ValidateRule(rule);
      Symbol lsym = rule[0];
      Symbol rsym = rule[1];
      vector<Symbol> repls = replacement_symbols_[lsym];
      if (std::find(repls.begin(), repls.end(), rsym) == repls.end())
        repls.push_back(rsym);
    }
  }

private:
  Symbol max_term_;    // assume first terminal is 1 (0 reserved for epsilon)
  Symbol max_preterm_; // assume min_preterm_ is max_term_ + 1, assume max_preterm_ == max_term_ * 2
  Symbol max_nonterm_; // assume min_nonterm_ is max_preterm_ + 1
  vector<Symbol> labels_to_symbols_;
  vector<Rule> rules_;
  vector<vector<ReachType> > symbol_reach_;
  vector<vector<Symbol> > replacement_symbols_;
  // replacement_symbols_[s] is a vector of symbols which appear as the left-most symbol of the RHS of a production from s
};

template <typename T>
class SetFilterState {
public:
  SetFilterState() {}
  SetFilterState(set<T> s) : set_(s) {}
  SetFilterState(T s) { set_.insert(s); }
  SetFilterState(SetFilterState &sfs) : set_(sfs.GetState()) {}

  static const SetFilterState NoState() { return SetFilterState(kNoStateId); }

  size_t Hash() const {
    size_t h = 0;
    set<T>::const_iterator iter;
    for (iter = set_.begin(); iter != set_.end(); ++iter) {
      h ^= h << 1  ^ *iter;
    }
    return h;
  }

  bool operator==(const SetFilterState &f) const {
    return set_ == f.set_;
  }

  bool operator!=(const SetFilterState &f) const {
    return set_ != f.set_;
  }

  const set<T> &GetState() const { return set_; }

  void Union(set<T> set2) {
    set_.insert(set2.begin(), set2.end());
  }

  const bool Contains(const T t) const { return set_.find(t) != set_.end() }

private:
  set<T> set_;

};

template <class M1, class M2>
class BenComposeFilter {
public:
  typedef typename M1::FST FST;
  typedef typename M2::FST PDT;
  typedef RuleArc Arc;
  typedef SetFilterState<RuleId> FilterState;
  typedef M1 Matcher1;
  typedef M2 Matcher2;

  BenComposeFilter(const GrammarInfo &grammar, const FST &fst, const PDT &pdt,
                   M1 *matcher1 = 0, M2 *matcher2 = 0)
          : matcher1_(matcher1 ? matcher1 : new M1(fst, MATCH_OUTPUT)),
            matcher2_(matcher2 ? matcher2 : new M2(pdt, MATCH_INPUT)),
            fst_(matcher1_->GetFst()),
            pdt_(matcher2_->GetFst()),
            s1_(kNoStateId),
            s2_(kNoStateId),
            f_(kNoStateId) {}

  BenComposeFilter(const BenComposeFilter<M1, M2> &filter, bool safe = false)
          : matcher1_(filter.matcher1_->Copy(safe)),
            matcher2_(filter.matcher2_->Copy(safe)),
            fst_(matcher1_->GetFst()),
            pdt_(matcher2_->GetFSt()),
            s1_(kNoStateId),
            s2_(kNoStateId),
            f_(kNoStateId) {}

  ~BenComposeFilter() {
    delete matcher1_;
    delete matcher2_;
  }

  FilterState Start() const { return FilterState(); }

  void SetState(StateId s1, StateId s2, const FilterState &f) {
    if (s1_ == s1 && s2_ == s2 && f == f_)
      return;
    s1_ = s1;
    s2_ = s2;
    f_ = f;
  }

  FilterState FilterArc(Arc *arc1, Arc *arc2) const {
    if (f_.Contains(arc2->rule))
      return FilterState::NoState()
  }
}


bool ReadIntVectors(const string& filename, vector<vector<int64> > *vectors) {
  ifstream strm(filename.c_str());
  if (!strm) {
    LOG(ERROR) << "ReadIntVectors: Can't open file: " << filename;
    return false;
  }
  const int kLineLen = 8096;
  char line[kLineLen];
  size_t nline = 0;
  vectors->clear();
  while (strm.getline(line, kLineLen)) {
    ++nline;
    vector<char *> col;
    SplitToVector(line, "\n\t ", &col, true);
    // empty line or comment?
    if (col.size() == 0 || col[0][0] == '\0' || col[0][0] == '#')
      continue;

    bool err;
    vector<int64> vec;
    for (ssize_t i = 0; i < col.size(); ++i) {
      int64 n = StrToInt64(col[i], filename, nline, false, &err);
      if (err) return false;
      vec.push_back(n);
    }
    vectors->push_back(vec);
  }
  return true;
}

bool ReadNumberedStrings(const string& filename, vector<string> *strings) {
  ifstream strm(filename.c_str());
  if (!strm) {
    LOG(ERROR) << "ReadNumberedStrings: Can't open file: " << filename;
    return false;
  }
  const int klinelen = 8096;
  char s1[kLineLen];
  size_t nline = 0;
  strings->clear();
  int prevn = -1;
  bool err;
  while (strm.getline(s1, kLineLen)) {
    ++nline;
    if (char *s2 = strpbrk("\t ", line))
      *s2 = '\0';
    int64 n = StrToInt64(s1, filename, nline, false, &err);
    if (err) return false;
    if (n <= prevn) return false;
    for (; prevn < n; ++prevn)
      strings->push_back("");
    strings->push_back(s2);
  }
  return true;
}

template <class F1, class F2, class F3>
class TripleFilterState {
public:
  TripleFilterState() : f1_(F1::NoState()), f2_(F2::NoState()), f3_(F3::NoState()) {}
  TripleFilterState(const F1 &f1, const F2 &f2, const F3 &f3) : f1_(f1), f2_(f2), f3_(f3) {}

  static const TripleFilterState NoState() { return TripleFilterState(); }

  size_t Hash() const {
    size_t h1 = f1_.Hash();
    size_t h2 = f2_.Hash();
    size_t h3 = f3_.Hash();
    const int lshift = 5;
    const int rshift = CHAR_BIT * sizeof(size_t) - 5;
    h1 = h1 << lshift ^ h1 >> rshift ^ h2;
    return h1 << lshift ^ h1 >> rshift ^ h3;
  }

  bool operator==(const TripleFilterState &f) const {
    return f1_ == f.f1_ && f2_ == f.f2_ && f3_ == f.f3_;
  }

  bool operator!=(const PairFilterState &f) const {
    return f1_ != f.f1_ || f2_ != f.f2_ || f3 != f.f3_;
  }

  const F1 &GetState1() const { return f1_; }
  const F2 &GetState2() const { return f2_; }
  const F3 &GetState3() const { return f3_; }

  void SetState(const F1 &f1, const F2 &f2, const F3 &f3) {
    f1_ = f1;
    f2_ = f2;
    f3_ = f3;
  }

private:
  F1 f1_;
  F2 f2_;
  F3 f3_;
};




};



#endif   // FST_LIB_BEN_H__