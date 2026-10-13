/-
  WilE5 — the fibrewise stratification machinery (Gabrielov–Vorobjov, fibrewise form).

  This file sets up the objects that the construction uses:
  * multi-index lists `mList` and the test order `testLt` (sum first, then lexicographic);
  * the *state* `St`: a list `B` of equations with their pivot fibre-directions, a flatness
    family `Φ`, accumulated vanishing conditions `Ξ` (with `Ξ ⊆ Φ`) and accumulated strict
    positive conditions `ν`;
  * the fibrewise operators `yOpSt` (iterated `detOp` in the fibre directions);
  * the state's semi-Pfaffian set, its flat leaf and its children.

  Design (see DESIGN.md): every state is a "node" of a recursion; the flat leaf of a state is
  a `Good` stratum, and the union of a state's flat leaf with the flat leaves of its children
  covers the state's set.
-/
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical Filter
open scoped Topology
namespace Work.WilE5
open WilkiesDesign WilkiesDesign.E

variable {p q r : ℕ}

/-- `Basic` has a `DecidableEq` instance (its fields are lists of `MvPolynomial`s); needed for
`List.dedup` of the disjuncts of a `SemiPf`.  `Spec.lean` is frozen and does not derive it. -/
noncomputable instance instDecidableEqBasic {k r : ℕ} : DecidableEq (Basic k r) := fun A B =>
  if h : A.eqs = B.eqs ∧ A.pos = B.pos then isTrue (by cases A; cases B; simp_all)
  else isFalse (by intro hh; exact h ⟨by rw [hh], by rw [hh]⟩)

/-- The fibre over `z`: the `p` first (base) coordinates of `z` followed by the `q` coordinates
`y`.  This is the ambient point with the same base as `z` and fibre coordinates `y`. -/
def fib {p q : ℕ} (z : Fin (p + q) → ℝ) : (Fin q → ℝ) → Fin (p + q) → ℝ :=
  fun y => Fin.append (fun i : Fin p => z (Fin.castAdd q i)) y

theorem fib_base {p q : ℕ} (z : Fin (p + q) → ℝ) (y : Fin q → ℝ) (i : Fin p) :
    fib z y (Fin.castAdd q i) = z (Fin.castAdd q i) := Fin.append_left _ _ i

theorem fib_yDir {p q : ℕ} (z : Fin (p + q) → ℝ) (y : Fin q → ℝ) (l : Fin q) :
    fib z y (yDir p l) = y l := by
  have h : yDir p l = Fin.natAdd p l := rfl
  rw [h]; exact Fin.append_right _ _ l

@[simp]
theorem fib_projFirst {p q : ℕ} (z : Fin (p + q) → ℝ) (y : Fin q → ℝ) :
    projFirst p q (fib z y) = projFirst p q z := by
  funext i; exact fib_base z y i

theorem exists_castAdd_or_yDir {p q : ℕ} (i : Fin (p + q)) :
    (∃ j : Fin p, i = Fin.castAdd q j) ∨ (∃ l : Fin q, i = yDir p l) := by
  rcases lt_or_ge i.val p with h | h
  · left
    exact ⟨⟨i.val, h⟩, by ext; simp [Fin.castAdd]⟩
  · right
    exact ⟨⟨i.val - p, by have := i.isLt; omega⟩, by
      ext; simp [yDir, Fin.natAdd]; omega⟩

theorem fib_self {p q : ℕ} (z : Fin (p + q) → ℝ) : fib z (fun l => z (yDir p l)) = z := by
  funext i
  rcases exists_castAdd_or_yDir i with ⟨j, rfl⟩ | ⟨l, rfl⟩
  · rw [fib_base]
  · rw [fib_yDir]

theorem eq_fib_of_projFirst_eq {p q : ℕ} {z z' : Fin (p + q) → ℝ}
    (h : projFirst p q z' = projFirst p q z) : fib z (fun l => z' (yDir p l)) = z' := by
  funext i
  rcases exists_castAdd_or_yDir i with ⟨j, rfl⟩ | ⟨l, rfl⟩
  · rw [fib_base]; exact (congrFun h j).symm
  · rw [fib_yDir]

theorem fib_injective {p q : ℕ} (z : Fin (p + q) → ℝ) : Function.Injective (fib z) := by
  intro y y' h
  funext l
  have := congrFun h (yDir p l)
  simpa [fib_yDir] using this

/-! ## §1. Multi-indices and the test order -/

/-- Sum of the entries of a multi-index. -/
def mSum {q : ℕ} (m : Fin q → ℕ) : ℕ := ∑ i, m i

/-- All multi-indices `Fin q → ℕ` with entries `≤ M`, as a list. -/
def mList (q M : ℕ) : List (Fin q → ℕ) :=
  ((Finset.univ : Finset (Fin q → Fin (M + 1))).val.toList).map (fun f i => (f i : ℕ))

theorem mem_mList_iff {q M : ℕ} (m : Fin q → ℕ) :
    m ∈ mList q M ↔ ∀ i, m i ≤ M := by
  constructor
  · intro h i
    obtain ⟨f, -, rfl⟩ := List.mem_map.mp h
    exact Fin.le_last (f i)
  · intro h
    refine List.mem_map.mpr ⟨fun i => ⟨m i, Nat.lt_succ_of_le (h i)⟩, ?_, ?_⟩
    · exact Multiset.mem_toList.mpr (by simp)
    · funext i; rfl

/-- Lexicographic comparison of the value lists of two multi-indices. -/
def mlexLtAux : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else mlexLtAux as bs

/-- Decrement a multi-index in one direction. -/
def mDec {q : ℕ} (m : Fin q → ℕ) (l : Fin q) : Fin q → ℕ := m - Pi.single l 1

theorem mSum_mDec {q : ℕ} (m : Fin q → ℕ) (l : Fin q) (h : m l ≠ 0) :
    mSum (mDec m l) = mSum m - 1 := by
  have hp : ∀ i : Fin q, (mDec m l) i + (Pi.single l 1 : Fin q → ℕ) i = m i := by
    intro i
    simp only [mDec, Pi.sub_apply]
    by_cases hi : i = l
    · subst hi
      rw [Pi.single_eq_same]
      exact Nat.sub_add_cancel (Nat.pos_iff_ne_zero.mpr h)
    · rw [Pi.single_eq_of_ne hi]
      simp
  have h2 : (∑ i, (Pi.single l 1 : Fin q → ℕ) i) = 1 := by simp
  have h1 : mSum (mDec m l) + 1 = mSum m := by
    rw [show (1 : ℕ) = ∑ i, (Pi.single l 1 : Fin q → ℕ) i from h2.symm]
    rw [show mSum (mDec m l) = ∑ i, (mDec m l) i from rfl]
    rw [show mSum m = ∑ i, m i from rfl]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hp i
  omega

theorem mSum_mDec_le {q : ℕ} (m : Fin q → ℕ) (l : Fin q) :
    mSum (mDec m l) ≤ mSum m := by
  unfold mSum mDec
  simp only [Pi.sub_apply]
  exact Finset.sum_le_sum fun i _ => Nat.sub_le _ _

/-- The *first* (smallest) direction carrying a nonzero exponent.  This is the direction peeled
off by `opMono_step` / `fr_step`: the operator with the smallest active index sits outermost. -/
def firstDir {q : ℕ} (m : Fin q → ℕ) (h : ∃ l, m l ≠ 0) : Fin q :=
  Finset.min' (Finset.univ.filter (fun l => m l ≠ 0)) (by
    obtain ⟨l, hl⟩ := h
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩⟩)

theorem firstDir_spec {q : ℕ} (m : Fin q → ℕ) (h : ∃ l, m l ≠ 0) : m (firstDir m h) ≠ 0 := by
  have := Finset.min'_mem (Finset.univ.filter (fun l => m l ≠ 0)) (by
    obtain ⟨l, hl⟩ := h
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩⟩)
  simpa [firstDir] using this

theorem firstDir_min {q : ℕ} (m : Fin q → ℕ) (h : ∃ l, m l ≠ 0) :
    ∀ l : Fin q, m l ≠ 0 → firstDir m h ≤ l := by
  intro l hl
  exact Finset.min'_le _ l (Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩)

theorem exists_ne_zero_iff {q : ℕ} (m : Fin q → ℕ) : (∃ l, m l ≠ 0) ↔ m ≠ 0 :=
  ⟨fun ⟨l, hl⟩ h => hl (by simpa [h]), fun h => Function.ne_iff.mp h⟩

theorem mDec_mem_mList {q M : ℕ} {m : Fin q → ℕ} (hm : m ∈ mList q M) (l : Fin q) :
    mDec m l ∈ mList q M := by
  rw [mem_mList_iff] at hm ⊢
  intro i
  refine le_trans ?_ (hm i)
  simp only [mDec, Pi.sub_apply]
  exact Nat.sub_le _ _

/-! ## §2. States -/

/-- A state of the stratification recursion.  `B` is the current system (an equation together
with the fibre direction in which its Jacobian is a pivot), `Φ` the flatness family (whose
iterated fibrewise operators are required to vanish on the flat leaf), `Ξ` the accumulated
vanishing conditions and `ν` the accumulated strict positivity conditions. -/
structure St (p q r : ℕ) where
  B : List (EAPoly (p + q) r × Fin q)
  Φ : List (EAPoly (p + q) r)
  Ξ : List (EAPoly (p + q) r)
  ν : List (EAPoly (p + q) r)

/-- The equations of a state. -/
def hFun {r : ℕ} (B : List (EAPoly (p + q) r × Fin q)) : Fin B.length → EAPoly (p + q) r :=
  fun a => (B.get a).1

/-- The pivot directions of a state, as ambient indices. -/
def pivFun (B : List (EAPoly (p + q) r × Fin q)) : Fin B.length → Fin (p + q) :=
  fun a => yDir p (B.get a).2

/-- The fibre directions involved in a state. -/
def pivDirs (B : List (EAPoly (p + q) r × Fin q)) : List (Fin q) := B.map Prod.snd

/-- The one-step fibrewise operator `∂_{B,l}`. -/
def detOpSt (c : EAChain (p + q) r) (B : List (EAPoly (p + q) r × Fin q))
    (l : Fin q) (ψ : EAPoly (p + q) r) : EAPoly (p + q) r :=
  detOp c (hFun B) (pivFun B) (yDir p l) ψ

/-- The iterated fibrewise operator `∂_{B,l}^{m l}` in the fibre directions. -/
def yOpSt (c : EAChain (p + q) r) (B : List (EAPoly (p + q) r × Fin q))
    (m : Fin q → ℕ) (ψ : EAPoly (p + q) r) : EAPoly (p + q) r :=
  (List.finRange q).foldr (fun l g => (detOpSt c B l)^[m l] g) ψ

/-! ## §3. Tests -/

/-- A test: a source index `i` into the flatness family, a multi-index `m`, and the fibre
direction `l` in which one operator is peeled off. -/
structure Test (q : ℕ) where
  i : ℕ
  m : Fin q → ℕ
  l : Fin q

/-- The `i`-th element of the flatness family (defaults to `0` when out of range). -/
def testPoly {p q r : ℕ} (σ : St p q r) (i : ℕ) : EAPoly (p + q) r :=
  (σ.Φ[i]?).getD 0

/-- A test is *valid* for a state when the source is in range and the multi-index vanishes in
all pivot directions.  (Tests in `testL` moreover satisfy `m l ≠ 0` and `mDec m l ≠ 0`.) -/
def valid {p q r : ℕ} (σ : St p q r) (t : Test q) : Prop :=
  t.i < σ.Φ.length ∧ ∀ a : Fin σ.B.length, t.m (σ.B.get a).2 = 0

/-- The fibrewise operator attached to a test. -/
def opVal {p q r : ℕ} (c : EAChain (p + q) r) (σ : St p q r) (t : Test q) : EAPoly (p + q) r :=
  yOpSt c σ.B t.m (testPoly σ t.i)

/-- The peeled operator attached to a test. -/
def peelVal {p q r : ℕ} (c : EAChain (p + q) r) (σ : St p q r) (t : Test q) :
    EAPoly (p + q) r :=
  yOpSt c σ.B (mDec t.m t.l) (testPoly σ t.i)

/-- The order on tests: source index, then degree, then lexicographically, then the direction. -/
def testLt (t t' : Test q) : Bool :=
  if t.i < t'.i then true
  else if t'.i < t.i then false
  else if mSum t.m < mSum t'.m then true
  else if mSum t'.m < mSum t.m then false
  else if mlexLtAux (List.ofFn t.m) (List.ofFn t'.m) then true
  else if mlexLtAux (List.ofFn t'.m) (List.ofFn t.m) then false
  else decide (t.l < t'.l)

/-- The list of all tests: `m` has a nonzero entry in the peeled direction.  (The peeled test
`(i, mDec m l, l')` is then again in the list whenever `mDec m l ≠ 0`.) -/
def testL (q M NΦ : ℕ) : List (Test q) :=
  (((List.range NΦ).product ((mList q M).product (List.finRange q))).map
    (fun p => (⟨p.1, p.2.1, p.2.2⟩ : Test q))).filter
    (fun t => decide (t.m t.l ≠ 0))

/-- The preceding valid tests (in the list order). -/
def prec {p q r : ℕ} (M NΦ : ℕ) (σ : St p q r) (t : Test q) : List (Test q) :=
  (testL q M NΦ).filter fun t' => decide (valid σ t' && testLt t' t)

/-! ## §4. The state's set and the flat leaf -/

/-- The conjunction of the conditions of a state. -/
def stCond {p q r : ℕ} (σ : St p q r) : Basic (p + q) r :=
  ⟨σ.B.map Prod.fst ++ σ.Ξ, σ.ν⟩

/-- The state's set, inside the ambient `X`. -/
def stSemiPf {p q : ℕ} (X : SemiPf (p + q)) (σ : St p q X.r) : SemiPf (p + q) :=
  semiPfAnd X (stCond σ)

/-- The flatness equations of a state. -/
def flatEqs {p q r : ℕ} (c : EAChain (p + q) r) (M NΦ : ℕ) (σ : St p q r) :
    List (EAPoly (p + q) r) :=
  ((testL q M NΦ).filter (fun t => decide (valid σ t))).map (fun t => opVal c σ t)

/-- The flat leaf of a state, as a `SemiPf` set. -/
def flatSemiPf {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) :
    SemiPf (p + q) :=
  ⟨X.r, X.c, (X.basics.map (fun A => conj A (stCond σ))).map
    (fun A => conj A (Basic.eqsOf (flatEqs X.c M NΦ σ)))⟩

/-- The flat leaf as a stratum, with equations `hFun σ.B`. -/
def flatStratum {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) :
    Stratum p q :=
  ⟨flatSemiPf X M NΦ σ, σ.B.length, hFun σ.B⟩

theorem flatStratum_X {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) :
    (flatStratum X M NΦ σ).X = flatSemiPf X M NΦ σ := rfl

theorem flatStratum_h {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) :
    (flatStratum X M NΦ σ).h = hFun σ.B := rfl

theorem flatStratum_j {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) (σ : St p q X.r) :
    (flatStratum X M NΦ σ).j = σ.B.length := rfl

/-! ## §5. Children -/

/-- The system of a child. -/
def childB {p q r : ℕ} (c : EAChain (p + q) r) (σ : St p q r) (t : Test q) :
    List (EAPoly (p + q) r × Fin q) :=
  σ.B ++ [(peelVal c σ t, t.l)]

/-- The accumulated vanishing conditions of a child. -/
def childΞ {p q r : ℕ} (c : EAChain (p + q) r) (M NΦ : ℕ) (σ : St p q r) (t : Test q) :
    List (EAPoly (p + q) r) :=
  σ.Ξ ++ ((prec M NΦ σ t).map (fun t' => opVal c σ t')) ++ [peelVal c σ t]

/-- The accumulated strict positivity conditions of a child. -/
def childν {p q r : ℕ} (c : EAChain (p + q) r) (σ : St p q r) (t : Test q) (s : Bool) :
    List (EAPoly (p + q) r) :=
  σ.ν ++ (if s then [opVal c σ t] else [- opVal c σ t])

/-- The child of a state at a test and a sign. -/
def childSt {p q r : ℕ} (c : EAChain (p + q) r) (M NΦ : ℕ) (σ : St p q r)
    (t : Test q) (s : Bool) : St p q r :=
  ⟨childB c σ t, σ.Φ ++ childΞ c M NΦ σ t, childΞ c M NΦ σ t, childν c σ t s⟩

/-- The children of a state (one per test and sign). -/
def children {p q r : ℕ} (c : EAChain (p + q) r) (M NΦ : ℕ) (σ : St p q r) :
    List (St p q r) :=
  (testL q M NΦ).flatMap fun t => [childSt c M NΦ σ t false, childSt c M NΦ σ t true]

/-! ## §6. The initial states (cube faces) and the level recursion -/

/-- `y_l - c`. -/
def facePoly {p q r : ℕ} (l : Fin q) (c : ℝ) : EAPoly (p + q) r :=
  MvPolynomial.X (Sum.inl (yDir p l)) - MvPolynomial.C c

/-- `1 - y_l^2`. -/
def intPoly {p q r : ℕ} (l : Fin q) : EAPoly (p + q) r :=
  MvPolynomial.C 1 - MvPolynomial.X (Sum.inl (yDir p l)) * MvPolynomial.X (Sum.inl (yDir p l))

theorem eaEval_facePoly {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.X (Sum.inl i) - MvPolynomial.C a : EAPoly k r) x = x i - a := by
  simp [eaEval]

theorem eaEval_intPoly {k r : ℕ} (c : EAChain k r) (i : Fin k) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.C 1 - MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inl i) :
      EAPoly k r) x = 1 - x i ^ 2 := by
  simp [eaEval, pow_two]

/-- The initial state attached to a disjunct `A ∈ X.basics` of `X` and a face pattern:
the face equations `y_l = ±1` go into `B` (with the face direction as pivot), the conditions of
the disjunct `A` become the accumulated conditions (`Ξ := A.eqs`, `ν := A.pos ++ …`) and also
the *flatness family* (`Φ := A.eqs`, so that the equations of the chosen disjunct can be
propagated by `E3`), and the interior inequalities `1 - y_l^2` go into `ν`.

The disjunct must be part of the state's own conditions: the flat leaf is locally contained in
`{A.holds}`, which is what identifies the disjunct that is used at a point of the leaf. -/
def initSt {p q : ℕ} (X : SemiPf (p + q)) (A : Basic (p + q) X.r) (Fy : Finset (Fin q))
    (ε : {l // l ∈ Fy} → Bool) : St p q X.r :=
  ⟨Fy.attach.toList.map (fun l => (facePoly l.1 (if ε l then 1 else -1), l.1)),
    A.eqs, A.eqs, A.pos ++ Fyᶜ.attach.toList.map (fun l => intPoly l.1)⟩

/-- The initial states: one per *distinct* disjunct of `X` and face pattern.  (`dedup` matters:
the number of initial states has to be bounded by a polynomial in `X.deg`, and repeated disjuncts
can be as numerous as one likes at degree `0`.) -/
def initStates {p q : ℕ} (X : SemiPf (p + q)) : List (St p q X.r) :=
  X.basics.dedup.flatMap fun A =>
    (Finset.univ : Finset (Finset (Fin q))).toList.flatMap fun Fy =>
      ((Finset.univ : Finset ({l // l ∈ Fy} → Bool)).toList).map fun ε => initSt X A Fy ε

/-- An initial state carries a disjunct `A ∈ X.basics` whose conditions and equations it uses. -/
theorem initSt_mem_initStates {p q : ℕ} (X : SemiPf (p + q)) (A : Basic (p + q) X.r)
    (hA : A ∈ X.basics) (Fy : Finset (Fin q)) (ε : {l // l ∈ Fy} → Bool) :
    initSt X A Fy ε ∈ initStates X := by
  refine List.mem_flatMap.mpr ⟨A, List.mem_dedup.mpr hA, ?_⟩
  refine List.mem_flatMap.mpr ⟨Fy, Finset.mem_toList.mpr (Finset.mem_univ Fy), ?_⟩
  exact List.mem_map.mpr ⟨ε, Finset.mem_toList.mpr (Finset.mem_univ ε), rfl⟩

/-- Every initial state arises from a disjunct of `X`. -/
theorem exists_of_mem_initStates {p q : ℕ} (X : SemiPf (p + q)) {σ : St p q X.r}
    (h : σ ∈ initStates X) :
    ∃ A ∈ X.basics, ∃ Fy : Finset (Fin q), ∃ ε : {l // l ∈ Fy} → Bool, σ = initSt X A Fy ε := by
  simp only [initStates, List.mem_flatMap, List.mem_dedup, List.mem_map] at h
  obtain ⟨A, hA, Fy, -, ε, -, rfl⟩ := h
  exact ⟨A, hA, Fy, ε, rfl⟩

/-- The states at depth `n`. -/
def level {p q : ℕ} (X : SemiPf (p + q)) (M NΦ : ℕ) : ℕ → List (St p q X.r)
  | 0 => initStates X
  | (n + 1) => (level X M NΦ n).flatMap fun σ => children X.c M NΦ σ

/-- All the flat leaves at depth `≤ n`. -/
def allStrata {p q : ℕ} (X : SemiPf (p + q)) (M NΦ n : ℕ) : List (Stratum p q) :=
  (List.range (n + 1)).flatMap fun k =>
    (level X M NΦ k).map fun σ => flatStratum X M NΦ σ

/-! ## §7. The extended system (base-coordinate shifts), used to make `E3_identity` fibrewise -/

/-- The base-coordinate shift functions `x_i - c_i`. -/
def xShift {p q r : ℕ} (z : Fin (p + q) → ℝ) : Fin p → EAPoly (p + q) r :=
  fun i => MvPolynomial.X (Sum.inl (Fin.castAdd q i)) - MvPolynomial.C (z (Fin.castAdd q i))

/-- The extended system: the equations `h` followed by the base-coordinate shifts. -/
def extH {p q r j : ℕ} (h : Fin j → EAPoly (p + q) r) (z : Fin (p + q) → ℝ) :
    Fin (j + p) → EAPoly (p + q) r :=
  Fin.append h (xShift (q := q) z)

/-- The extended pivots: the pivots `ι` followed by the base directions. -/
def extι {p q j : ℕ} (ι : Fin j → Fin (p + q)) : Fin (j + p) → Fin (p + q) :=
  Fin.append ι fun i : Fin p => Fin.castAdd q i

theorem eaEval_xShift {p q r : ℕ} (c : EAChain (p + q) r) (z z' : Fin (p + q) → ℝ) (i : Fin p) :
    eaEval c (xShift (q := q) (r := r) z' i) z = z (Fin.castAdd q i) - z' (Fin.castAdd q i) := by
  simp [xShift, eaEval]

end Work.WilE5

end


