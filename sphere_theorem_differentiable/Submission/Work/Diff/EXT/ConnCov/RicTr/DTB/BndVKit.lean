import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.DeltaTower

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Kit for `Work.Diff.EXT.ConnCov.DTB.bndV_deltaTower`

The target `Work.Diff.EXT.ConnCov.DTB.bndV_deltaTower` bounds the **fixed-connection δ-tower**
`deltaTower G t c = ∇^{g_0,c}(∇^{g_t} − ∇^{g_0})` from the given bounds `hA` on the
fixed-connection tower of `aOf G t = g_t(δ ·, ·)`.

The proof is the **Leibniz expansion** of the pairing `aOf X Y Z = (G t).inner (δ Y X) Z`, i.e. the
iterated product rule for the covariant tower of a pointwise bilinear pairing of the *moving metric*
`g_t = G t` (whose `∇^{g_0}`-tower is `gtTower G t ·`) with the δ-tower:

  `tower (lcOf (G 0)) aOf c = Σ_{all distributions of the c directions} (∇^{g_0,i}g_t) ⊙ (∇^{g_0,c−i}δ)`.

The distribution of the `c` direction slots between the two factors is encoded by an equivalence
`e : Fin i ⊕ Fin j ≃ Fin c` (`i + j = c`), the metric factor receiving the directions
`e (Sum.inl ·)` and the δ factor the directions `e (Sum.inr ·)`: that is the definition `selTerm`.

One recursion step sends a term with data `e` to the two terms with data `shiftL e` (metric factor
differentiated) and `shiftR e` (δ factor differentiated).  The `i = 0` term is the lowering `Wterm`
of the δ-tower, whose bound (in the `g_t`-metric, where the lowering is an isometry) is the
conclusion of the target.

## Contents

* `selTerm`, `Wterm`, `eC` — the expansion term, its `i = 0` specialisation and the canonical index
  equivalence;
* `shiftL`, `shiftR` — the index bookkeeping of one recursion step, with computation rules;
* `Good` — "`τ` is a sum of at most `2^c` expansion terms of level `c` with metric level `≥ 1`".
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.DTB

open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The expansion terms -/

/-- **A term of the Leibniz expansion.**  The metric tower `∇^{g_0,i}g_t` (an `Op2 i`) is paired
with the δ-tower `∇^{g_0,j}δ` (a `VOp j`); the `c = i + j` direction slots `Fin c` are distributed
by the equivalence `e`, the metric factor receiving the directions `e (Sum.inl ·)` and the δ factor
the directions `e (Sum.inr ·)`.  The two section slots of the δ factor are exchanged (`B A`), so that
the term at `i = j = 0` is `aOf`. -/
noncomputable def selTerm (G : ℝ → SMet I M) (t : ℝ) {c i j : ℕ}
    (e : Fin i ⊕ Fin j ≃ Fin c) : Op3 (I := I) (M := M) c :=
  fun v A B C y =>
    gtTower G t i (fun a : Fin i => v (e (Sum.inl a)))
      (deltaTower G t j (fun b : Fin j => v (e (Sum.inr b))) B A) C y

/-- The canonical equivalence `Fin 0 ⊕ Fin c ≃ Fin c`. -/
noncomputable def eC (c : ℕ) : Fin 0 ⊕ Fin c ≃ Fin c :=
  Equiv.ofBijective (Sum.elim (Fin.elim0) id) (by
    constructor
    · intro x y h
      rcases x with a | b
      · exact a.elim0
      · rcases y with a | b
        · exact a.elim0
        · simpa using h
    · intro b
      exact ⟨Sum.inr b, rfl⟩)

theorem eC_inr (c : ℕ) (b : Fin c) : eC c (Sum.inr b) = b := rfl

/-- **The `i = 0` term**: the lowering of the δ-tower by the moving metric,
`Wterm c v A B C y = (G t).inner (∇^{g_0,c}δ (v) B A) C`. -/
noncomputable def Wterm (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) : Op3 (I := I) (M := M) c :=
  selTerm G t (eC c)

/-- The explicit form of `Wterm`. -/
theorem Wterm_apply (G : ℝ → SMet I M) (t : ℝ) (c : ℕ)
    (v : Fin c → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (y : M) :
    Wterm G t c v A B C y = (G t).inner y (deltaTower G t c v B A y) (C y) := by
  simp only [Wterm, selTerm, eC_inr, gtTower, gtower, gtBase]

/-- Two `i = 0` terms with the same `inr`-part are equal. -/
theorem selTerm_zero_congr (G : ℝ → SMet I M) (t : ℝ) {j c : ℕ}
    (e e' : Fin 0 ⊕ Fin j ≃ Fin c)
    (h : ∀ b : Fin j, e (Sum.inr b) = e' (Sum.inr b)) : selTerm G t e = selTerm G t e' := by
  funext v A B C y
  simp only [selTerm, gtTower, gtower, gtBase]
  rw [show (fun b : Fin j => v (e (Sum.inr b))) = fun b => v (e' (Sum.inr b)) from
    funext (fun b => by rw [h b])]

/-! ## The index bookkeeping of one recursion step

A term with data `(i, j, e)` is differentiated by `step`: the metric factor receives the new
direction (slot `0` of the new tuple) in the first output term, the δ factor in the second.  The
remaining slots are shifted by one; the two resulting index equivalences are `shiftL e` and
`shiftR e`. -/

/-- The underlying map of `shiftL`: slot `0` goes to the metric factor, everything else is shifted
by one. -/
def shiftLFun {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) : Fin (i + 1) ⊕ Fin j → Fin (c + 1) :=
  fun x => match x with
    | Sum.inl a => Fin.cases 0 (fun a' : Fin i => (e (Sum.inl a')).succ) a
    | Sum.inr b => (e (Sum.inr b)).succ

/-- The inverse of `shiftLFun`. -/
def shiftLInv {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) : Fin (c + 1) → Fin (i + 1) ⊕ Fin j :=
  fun m => Fin.cases (Sum.inl 0) (fun m' : Fin c =>
    match e.symm m' with
    | Sum.inl a => Sum.inl a.succ
    | Sum.inr b => Sum.inr b) m

/-- The underlying map of `shiftR`: slot `0` goes to the δ factor, everything else is shifted by
one. -/
def shiftRFun {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) : Fin i ⊕ Fin (j + 1) → Fin (c + 1) :=
  fun x => match x with
    | Sum.inl a => (e (Sum.inl a)).succ
    | Sum.inr b => Fin.cases 0 (fun b' : Fin j => (e (Sum.inr b')).succ) b

/-- The inverse of `shiftRFun`. -/
def shiftRInv {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) : Fin (c + 1) → Fin i ⊕ Fin (j + 1) :=
  fun m => Fin.cases (Sum.inr 0) (fun m' : Fin c =>
    match e.symm m' with
    | Sum.inl a => Sum.inl a
    | Sum.inr b => Sum.inr b.succ) m

@[simp] theorem shiftLFun_inl_zero {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    shiftLFun e (Sum.inl 0) = 0 := rfl

@[simp] theorem shiftLFun_inl_succ {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (a : Fin i) :
    shiftLFun e (Sum.inl a.succ) = (e (Sum.inl a)).succ := rfl

@[simp] theorem shiftLFun_inr {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (b : Fin j) :
    shiftLFun e (Sum.inr b) = (e (Sum.inr b)).succ := rfl

@[simp] theorem shiftLInv_zero {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    shiftLInv e 0 = Sum.inl 0 := rfl

theorem shiftLInv_succ {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (m : Fin c) :
    shiftLInv e m.succ
      = match e.symm m with
        | Sum.inl a => Sum.inl a.succ
        | Sum.inr b => Sum.inr b := rfl

@[simp] theorem shiftRFun_inl {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (a : Fin i) :
    shiftRFun e (Sum.inl a) = (e (Sum.inl a)).succ := rfl

@[simp] theorem shiftRFun_inr_zero {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    shiftRFun e (Sum.inr 0) = 0 := rfl

@[simp] theorem shiftRFun_inr_succ {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (b : Fin j) :
    shiftRFun e (Sum.inr b.succ) = (e (Sum.inr b)).succ := rfl

@[simp] theorem shiftRInv_zero {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    shiftRInv e 0 = Sum.inr 0 := rfl

theorem shiftRInv_succ {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (m : Fin c) :
    shiftRInv e m.succ
      = match e.symm m with
        | Sum.inl a => Sum.inl a
        | Sum.inr b => Sum.inr b.succ := rfl

theorem shiftLFun_leftInverse {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    Function.LeftInverse (shiftLInv e) (shiftLFun e) := by
  intro x
  rcases x with a | b
  · induction a using Fin.cases with
    | zero => rfl
    | succ a' => simp only [shiftLFun_inl_succ, shiftLInv_succ, Equiv.symm_apply_apply]
  · simp only [shiftLFun_inr, shiftLInv_succ, Equiv.symm_apply_apply]

theorem shiftLFun_rightInverse {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    Function.RightInverse (shiftLInv e) (shiftLFun e) := by
  intro m
  induction m using Fin.cases with
  | zero => rfl
  | succ m' =>
      rcases h : e.symm m' with a | b
      · have hgl : e (Sum.inl a) = m' := by rw [← h]; exact Equiv.apply_symm_apply e m'
        simp only [shiftLInv_succ, h, shiftLFun_inl_succ, hgl]
      · have hgl : e (Sum.inr b) = m' := by rw [← h]; exact Equiv.apply_symm_apply e m'
        simp only [shiftLInv_succ, h, shiftLFun_inr, hgl]

theorem shiftRFun_leftInverse {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    Function.LeftInverse (shiftRInv e) (shiftRFun e) := by
  intro x
  rcases x with a | b
  · simp only [shiftRFun_inl, shiftRInv_succ, Equiv.symm_apply_apply]
  · induction b using Fin.cases with
    | zero => rfl
    | succ b' => simp only [shiftRFun_inr_succ, shiftRInv_succ, Equiv.symm_apply_apply]

theorem shiftRFun_rightInverse {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    Function.RightInverse (shiftRInv e) (shiftRFun e) := by
  intro m
  induction m using Fin.cases with
  | zero => rfl
  | succ m' =>
      rcases h : e.symm m' with a | b
      · have hgl : e (Sum.inl a) = m' := by rw [← h]; exact Equiv.apply_symm_apply e m'
        simp only [shiftRInv_succ, h, shiftRFun_inl, hgl]
      · have hgl : e (Sum.inr b) = m' := by rw [← h]; exact Equiv.apply_symm_apply e m'
        simp only [shiftRInv_succ, h, shiftRFun_inr_succ, hgl]

/-- The index bookkeeping of one recursion step, metric factor differentiated. -/
noncomputable def shiftL {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    Fin (i + 1) ⊕ Fin j ≃ Fin (c + 1) :=
  Equiv.ofBijective (shiftLFun e)
    ⟨fun a b h => by
        have h' := congrArg (shiftLInv e) h
        rwa [shiftLFun_leftInverse e a, shiftLFun_leftInverse e b] at h',
      fun b => ⟨shiftLInv e b, shiftLFun_rightInverse e b⟩⟩

/-- The index bookkeeping of one recursion step, δ factor differentiated. -/
noncomputable def shiftR {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    Fin i ⊕ Fin (j + 1) ≃ Fin (c + 1) :=
  Equiv.ofBijective (shiftRFun e)
    ⟨fun a b h => by
        have h' := congrArg (shiftRInv e) h
        rwa [shiftRFun_leftInverse e a, shiftRFun_leftInverse e b] at h',
      fun b => ⟨shiftRInv e b, shiftRFun_rightInverse e b⟩⟩

theorem shiftL_apply {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (x : Fin (i + 1) ⊕ Fin j) : shiftL e x = shiftLFun e x := by
  simp only [shiftL, Equiv.coe_ofBijective]

theorem shiftR_apply {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c)
    (x : Fin i ⊕ Fin (j + 1)) : shiftR e x = shiftRFun e x := by
  simp only [shiftR, Equiv.coe_ofBijective]

@[simp] theorem shiftL_inl_zero {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    shiftL e (Sum.inl 0) = 0 := by rw [shiftL_apply, shiftLFun_inl_zero]

@[simp] theorem shiftL_inl_succ {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (a : Fin i) :
    shiftL e (Sum.inl a.succ) = (e (Sum.inl a)).succ := by
  rw [shiftL_apply, shiftLFun_inl_succ]

@[simp] theorem shiftL_inr {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (b : Fin j) :
    shiftL e (Sum.inr b) = (e (Sum.inr b)).succ := by rw [shiftL_apply, shiftLFun_inr]

@[simp] theorem shiftR_inl {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (a : Fin i) :
    shiftR e (Sum.inl a) = (e (Sum.inl a)).succ := by rw [shiftR_apply, shiftRFun_inl]

@[simp] theorem shiftR_inr_zero {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) :
    shiftR e (Sum.inr 0) = 0 := by rw [shiftR_apply, shiftRFun_inr_zero]

@[simp] theorem shiftR_inr_succ {i j c : ℕ} (e : Fin i ⊕ Fin j ≃ Fin c) (b : Fin j) :
    shiftR e (Sum.inr b.succ) = (e (Sum.inr b)).succ := by
  rw [shiftR_apply, shiftRFun_inr_succ]

/-- For an `i = 0` term whose `inr`-part is the identity, the `shiftR` bookkeeping keeps the
`inr`-part the identity. -/
theorem shiftR_inr_eq {c : ℕ} (e : Fin 0 ⊕ Fin c ≃ Fin c)
    (h : ∀ b : Fin c, e (Sum.inr b) = b) (b : Fin (c + 1)) :
    shiftR e (Sum.inr b) = b := by
  induction b using Fin.cases with
  | zero => simp
  | succ b' => simp [h b']

/-- The `shiftR` bookkeeping of the canonical equivalence is the canonical equivalence. -/
theorem shiftR_eC (c : ℕ) : shiftR (eC c) = eC (c + 1) := by
  refine Equiv.ext (fun x => ?_)
  rcases x with a | b
  · exact a.elim0
  · rw [shiftR_inr_eq (eC c) (fun b => rfl) b]
    exact (eC_inr (c + 1) b).symm

/-! ## The "sum of expansion terms" predicate -/

/-- `Good G t c τ` says that `τ` is a finite sum of expansion terms of level `c`, each of them with
**metric level `≥ 1`** (so that the δ-factor of such a term has level `< c`, which is what makes the
bound induction on `c` close).  The index type is an arbitrary finite type, which is what makes the
recursion `c ↦ c+1` (where the index type is replaced by `(ι ⊕ ι) ⊕ PUnit`) available. -/
def Good (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) (τ : Op3 (I := I) (M := M) c) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (i j : ι → ℕ)
    (e : (n : ι) → Fin (i n) ⊕ Fin (j n) ≃ Fin c),
    (∀ n, 1 ≤ i n) ∧ (∀ n, i n + j n = c) ∧
      τ = fun v A B C y => ∑ n : ι, selTerm G t (e n) v A B C y

end Work.Diff.EXT.ConnCov.DTB
