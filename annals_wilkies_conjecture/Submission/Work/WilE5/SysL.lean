/-
  WilE5 — the *profile* (level-indexed test-order bound) layer on top of `Sys.lean`.

  Why this exists.  The flat-leaf correctness (`Strat.flatLeafGood`) needs, at a state `σ`, the
  tests of order up to `Me.eval (∑ atomDeg (hFun σ.B) + 2p + atomDeg ψ)` (`hMu`), where `Me` is
  `E3_identity`'s multiplicity polynomial.  The state's own degrees *grow* with the level (every
  child appends one operator value as a new pivot), so a *single* global test-order bound `Mtest`
  cannot work: the pivot degrees are bounded by `(q·Mtest)^k` while `hMu` needs
  `Mtest ≥ Me.eval ((q·Mtest)^k D)`, which has no solution for a non-constant `Me` as soon as
  `q ≥ 2`.

  Exactly as in Gabrielov–Vorobjov's algorithm (`M_0, M_1, …, M_n` of GV 1995 §3), the test order
  must therefore be a *function of the level*.  We index it by `σ.B.length` (a state with `k`
  pivots is at level `k`; every child of a level-`k` state has level `k+1` and the levels are
  bounded by `q`), and write `Ml : ℕ → ℕ` for the profile.

  The definitions here are *definitionally* the `Sys.lean` ones with `M := Ml σ.B.length`, so all
  the lemmas already proved in `Sys.lean`/`Strat` apply verbatim.
-/
import Submission.Work.WilE5.Sys
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

variable {p q r : ℕ}

/-! ## §1. The profile-indexed objects -/

/-- The list of tests of a state under the test-order profile `Ml`.  The profile is evaluated at
the state's level `σ.B.length`. -/
def testLP (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) : List (Test q) :=
  testL q (Ml σ.B.length) NΦ

/-- The preceding valid tests of a test, under the test-order profile. -/
def precP (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) (t : Test q) : List (Test q) :=
  prec (Ml σ.B.length) NΦ σ t

/-- The flatness equations of a state under the test-order profile. -/
def flatEqsP (c : EAChain (p + q) r) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) :
    List (EAPoly (p + q) r) :=
  flatEqs c (Ml σ.B.length) NΦ σ

/-- The flat leaf of a state under the test-order profile. -/
def flatSemiPfP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r) :
    SemiPf (p + q) :=
  flatSemiPf X (Ml σ.B.length) NΦ σ

/-- The flat leaf as a stratum, under the test-order profile. -/
def flatStratumP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q X.r) :
    Stratum p q :=
  flatStratum X (Ml σ.B.length) NΦ σ

/-- The accumulated vanishing conditions of a child, under the profile. -/
def childΞP (c : EAChain (p + q) r) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) (t : Test q) :
    List (EAPoly (p + q) r) :=
  childΞ c (Ml σ.B.length) NΦ σ t

/-- A child of a state, under the profile. -/
def childStP (c : EAChain (p + q) r) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) (t : Test q)
    (s : Bool) : St p q r :=
  childSt c (Ml σ.B.length) NΦ σ t s

/-- The children of a state, under the profile. -/
def childrenP (c : EAChain (p + q) r) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) :
    List (St p q r) :=
  (testLP Ml NΦ σ).flatMap fun t => [childStP c Ml NΦ σ t false, childStP c Ml NΦ σ t true]

/-- The states at depth `n` of the recursion with profile `Ml`. -/
def levelP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) : ℕ → List (St p q X.r)
  | 0 => initStates X
  | (n + 1) => (levelP X Ml NΦ n).flatMap fun σ => childrenP X.c Ml NΦ σ

/-- All the flat leaves at depth `≤ n`, under the profile. -/
def allStrataP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (n : ℕ) :
    List (Stratum p q) :=
  (List.range (n + 1)).flatMap fun k => (levelP X Ml NΦ k).map fun σ => flatStratumP X Ml NΦ σ

/-! ## §2. `rfl`-level identification with the `Sys.lean` objects -/

theorem testLP_eq (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) :
    testLP Ml NΦ σ = testL q (Ml σ.B.length) NΦ := rfl

theorem precP_eq (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) (t : Test q) :
    precP Ml NΦ σ t = prec (Ml σ.B.length) NΦ σ t := rfl

theorem flatEqsP_eq (c : EAChain (p + q) r) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) :
    flatEqsP c Ml NΦ σ = flatEqs c (Ml σ.B.length) NΦ σ := rfl

theorem flatSemiPfP_eq {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) :
    flatSemiPfP X Ml NΦ σ = flatSemiPf X (Ml σ.B.length) NΦ σ := rfl

theorem childStP_eq (c : EAChain (p + q) r) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r)
    (t : Test q) (s : Bool) :
    childStP c Ml NΦ σ t s = childSt c (Ml σ.B.length) NΦ σ t s := rfl

theorem childrenP_eq (c : EAChain (p + q) r) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r) :
    childrenP c Ml NΦ σ = children c (Ml σ.B.length) NΦ σ := rfl

theorem flatStratumP_X {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) :
    (flatStratumP X Ml NΦ σ).X = flatSemiPfP X Ml NΦ σ := rfl

theorem flatStratumP_h {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) :
    (flatStratumP X Ml NΦ σ).h = hFun σ.B := rfl

theorem flatStratumP_j {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) :
    (flatStratumP X Ml NΦ σ).j = σ.B.length := rfl

/-! ## §3. The recursion: levels, membership -/

theorem levelP_zero {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) :
    levelP X Ml NΦ 0 = initStates X := rfl

theorem levelP_succ {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ) (n : ℕ) :
    levelP X Ml NΦ (n + 1) = (levelP X Ml NΦ n).flatMap fun σ => childrenP X.c Ml NΦ σ := rfl

theorem mem_levelP_succ {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ n : ℕ)
    {τ : St p q X.r} :
    τ ∈ levelP X Ml NΦ (n + 1) ↔
      ∃ σ ∈ levelP X Ml NΦ n, τ ∈ childrenP X.c Ml NΦ σ := by
  rw [levelP_succ, List.mem_flatMap]

/-- A child of a state with profile `Ml` has level one more than its parent. -/
theorem childStP_level (c : EAChain (p + q) r) (Ml : ℕ → ℕ) (NΦ : ℕ) (σ : St p q r)
    (t : Test q) (s : Bool) :
    (childStP c Ml NΦ σ t s).B.length = σ.B.length + 1 := by
  simp [childStP, childSt, childB]

/-- A child's system extends its parent's. -/
theorem childB_prefix (c : EAChain (p + q) r) (σ : St p q r) (t : Test q) :
    σ.B <+: childB c σ t := List.prefix_append _ _

/-! ## §4. `stSemiPf` is profile-independent -/

theorem stSemiPf_childStP {p q : ℕ} (X : SemiPf (p + q)) (Ml : ℕ → ℕ) (NΦ : ℕ)
    (σ : St p q X.r) (t : Test q) (s : Bool) :
    stSemiPf X (childStP X.c Ml NΦ σ t s) = stSemiPf X (childSt X.c (Ml σ.B.length) NΦ σ t s) :=
  rfl

end Work.WilE5
