import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.towerEqLoweringDeltaTowerM
import Submission.Work.Diff.EXT.ConnCov.RicTowerKit
import Submission.Work.Diff.EXT.ConnCov.pack_bridge
import Submission.Work.Diff.EXT.ConnCov.aTowerFlipKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-!
# The one-atom substitution calculus for the connection flip of the Ricci tower

`Work.Diff.EXT.ConnCov.RicFlip.O` (this module) sets up the *substitution calculus* used by the
proof of `Work.Diff.EXT.ConnCov.ricFlipOfMoving`.

Writing `D_t := AMB.pD (lcOf (G t))` (the *moving* connection), `D_0 := AMB.pD (lcOf (G 0))` (the
*fixed* one) and `U := AMB.Ins (covDiff G t)` (the insertion of the connection difference), the flip
identity is `D_0 = D_t + U` on slot-additive objects.  The bound induction therefore has to bound
the **word objects** `Z_w` (`w` a word over `{D_t, U}`, applied to the base `AMB.pack (baseRic (G t))`).

The obstacle is that `D_t` cannot be applied to an arbitrary object: the correction terms of
`AMB.pD` involve the covariant derivatives of the *slot fields*, which are unbounded for a general
tuple.  For a *tensorial* object the corrections cancel, and the precise form of the cancellation is
the **chain rule**

  `D_t (Θ ∘ Φ) = (D_t Θ) ∘ Φ.shift + Θ ∘ Φ.deriv`,

where the objects have to be read as `Θ` composed with a **substitution** `Φ`.

This module provides the substitutions and everything about them that does *not* involve `AMB.pD`:

* `atomEval G t τ F` — the atom `∇^{ord}δ` (the `ord`-th covariant derivative of the connection
  difference) evaluated on the input slots `τ`;
* `OSub a b ord` — a *one-atom substitution*: a `b`-tuple whose `i`-th entry is the input slot
  `σ i`, except at the atom index `idx`, where the entry is the atom `∇^{ord}δ` applied to the slots
  `τ` (and the pair `(τ, σ ↾ {i ≠ idx})` is a bijection onto the `a` input slots);
* `OSub.eval`, `OSub.comp` — evaluation and composition;
* `OSub.eval_update_slot`, `OSub.eval_update_atom` — modifying an input slot changes exactly the
  component(s) that use it;
* `OSub.sum_reindex` — reindexing a sum over the input slots by the uses;
* `OSub.shift` and `OSub.deriv` — the two operations appearing in the chain rule, together with
  their evaluations `OSub.eval_shift`, `OSub.eval_deriv`.

The chain rule itself (and the atom Leibniz rule `atomEval_deriv` that it rests on) is the target of
the sibling module `Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubChain`.
-/

namespace Work.Diff.EXT.ConnCov.RicFlip.O

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The atom `∇^{ord}δ` applied to the argument slots `τ`. -/
noncomputable def atomEval (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) {a ord : ℕ}
    (τ : Fin (ord + 2) → Fin a) (F : Fin a → AMB.TF (I := I) (M := M)) :
    AMB.TF (I := I) (M := M) :=
  vtowerM (G t) (deltaBaseM G t) ord
    (fun l : Fin ord => F (τ (Fin.castAdd 2 l)))
    (F (τ (Fin.natAdd ord 0))) (F (τ (Fin.natAdd ord 1)))

/-- A one-atom substitution. -/
structure OSub (a b ord : ℕ) where
  idx : Fin b
  τ : Fin (ord + 2) → Fin a
  σ : Fin b → Fin a
  bij : Function.Bijective (Sum.elim τ (fun i : {i : Fin b // i ≠ idx} => σ i.1))

namespace OSub

variable {a b ord : ℕ}

theorem τ_inj (Φ : OSub a b ord) : Function.Injective Φ.τ := by
  intro l l' h
  have h1 : (Sum.inl l : Fin (ord + 2) ⊕ {i : Fin b // i ≠ Φ.idx})
      = Sum.inl l' := Φ.bij.1 (by simpa using h)
  exact Sum.inl.inj h1

theorem σ_inj (Φ : OSub a b ord) {i i' : Fin b} (h : i ≠ Φ.idx) (h' : i' ≠ Φ.idx) :
    Φ.σ i = Φ.σ i' → i = i' := by
  intro hc
  have h1 : (Sum.inr ⟨i, h⟩ : Fin (ord + 2) ⊕ {i : Fin b // i ≠ Φ.idx})
      = Sum.inr ⟨i', h'⟩ := Φ.bij.1 (by simpa using hc)
  exact congrArg Subtype.val (Sum.inr.inj h1)

theorem τ_ne_σ (Φ : OSub a b ord) (l : Fin (ord + 2)) (i : {i : Fin b // i ≠ Φ.idx}) :
    Φ.τ l ≠ Φ.σ i.1 := by
  intro hc
  have h1 : (Sum.inl l : Fin (ord + 2) ⊕ {i : Fin b // i ≠ Φ.idx})
      = Sum.inr i := Φ.bij.1 (by simpa using hc)
  exact Sum.inl_ne_inr h1

theorem σ_ne_τ (Φ : OSub a b ord) (i : {i : Fin b // i ≠ Φ.idx}) (l : Fin (ord + 2)) :
    Φ.σ i.1 ≠ Φ.τ l := fun hc => Φ.τ_ne_σ l i hc.symm

/-- The evaluation of the substitution on a tuple. -/
noncomputable def eval (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (Φ : OSub a b ord)
    (F : Fin a → AMB.TF (I := I) (M := M)) : Fin b → AMB.TF (I := I) (M := M) :=
  fun i => if i = Φ.idx then atomEval G t Φ.τ F else F (Φ.σ i)

theorem eval_atom {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} (Φ : OSub a b ord)
    (F : Fin a → AMB.TF (I := I) (M := M)) :
    Φ.eval G t F Φ.idx = atomEval G t Φ.τ F := by
  rw [eval]; exact if_pos rfl

theorem eval_slot {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} (Φ : OSub a b ord)
    (F : Fin a → AMB.TF (I := I) (M := M)) {i : Fin b} (h : i ≠ Φ.idx) :
    Φ.eval G t F i = F (Φ.σ i) := by
  rw [eval]; exact if_neg h

/-- The composition of an object with a substitution. -/
noncomputable def comp (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (Φ : OSub a b ord)
    (Θ : AMB.Fam (I := I) (M := M) b) : AMB.Fam (I := I) (M := M) a :=
  fun F => Θ (Φ.eval G t F)

/-- The atom is unaffected by modifying a slot that it does not use. -/
theorem atomEval_update {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} (Φ : OSub a b ord)
    (F : Fin a → AMB.TF (I := I) (M := M)) (s : Fin a) (W : AMB.TF (I := I) (M := M))
    (hs : ∀ l, Φ.τ l ≠ s) :
    atomEval G t Φ.τ (Function.update F s W) = atomEval G t Φ.τ F := by
  simp only [atomEval]
  have h1 : ∀ l : Fin (ord + 2), (Function.update F s W) (Φ.τ l) = F (Φ.τ l) :=
    fun l => Function.update_of_ne (hs l) W F
  have hfun : (fun l : Fin ord => (Function.update F s W) (Φ.τ (Fin.castAdd 2 l)))
      = fun l : Fin ord => F (Φ.τ (Fin.castAdd 2 l)) := by
    funext l; exact h1 _
  rw [hfun, h1 (Fin.natAdd ord 0), h1 (Fin.natAdd ord 1)]

/-- **Modifying one input slot changes only the component that uses it** (projection component). -/
theorem eval_update_slot {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} (Φ : OSub a b ord)
    (F : Fin a → AMB.TF (I := I) (M := M)) (i : Fin b) (h : i ≠ Φ.idx)
    (W : AMB.TF (I := I) (M := M)) :
    Φ.eval G t (Function.update F (Φ.σ i) W)
      = Function.update (Φ.eval G t F) i W := by
  have hdisj : ∀ l : Fin (ord + 2), Φ.τ l ≠ Φ.σ i := fun l => Φ.τ_ne_σ l ⟨i, h⟩
  funext j
  by_cases hji : j = i
  · rw [hji, eval_slot Φ (Function.update F (Φ.σ i) W) h,
      Function.update_self (Φ.σ i) W F,
      Function.update_self i W (Φ.eval G t F)]
  · by_cases hj : j = Φ.idx
    · rw [hj, eval_atom,
        Function.update_of_ne (Ne.symm h) W (Φ.eval G t F), eval_atom,
        Φ.atomEval_update F (Φ.σ i) W hdisj]
    · rw [eval_slot Φ (Function.update F (Φ.σ i) W) hj,
        Function.update_of_ne hji W (Φ.eval G t F), eval_slot Φ F hj]
      have hne : Φ.σ j ≠ Φ.σ i := fun hc => hji (Φ.σ_inj hj h hc)
      rw [Function.update_of_ne hne W F]

/-- **Modifying one input slot used by the atom changes only the atom component.** -/
theorem eval_update_atom {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} (Φ : OSub a b ord)
    (F : Fin a → AMB.TF (I := I) (M := M)) (l : Fin (ord + 2))
    (W : AMB.TF (I := I) (M := M)) :
    Φ.eval G t (Function.update F (Φ.τ l) W)
      = Function.update (Φ.eval G t F) Φ.idx
          (atomEval G t Φ.τ (Function.update F (Φ.τ l) W)) := by
  funext j
  by_cases hj : j = Φ.idx
  · rw [hj, eval_atom,
      Function.update_self Φ.idx (atomEval G t Φ.τ (Function.update F (Φ.τ l) W))
        (Φ.eval G t F)]
  · rw [eval_slot Φ (Function.update F (Φ.τ l) W) hj, Function.update_of_ne hj]
    have hne : Φ.σ j ≠ Φ.τ l := Φ.σ_ne_τ ⟨j, hj⟩ l
    rw [Function.update_of_ne hne W F, eval_slot Φ F hj]

/-- **Reindexing a sum over the input slots** by the uses of the substitution. -/
theorem sum_reindex (Φ : OSub a b ord) (f : Fin a → ℝ) :
    (∑ s : Fin a, f s)
      = (∑ l : Fin (ord + 2), f (Φ.τ l))
        + ∑ i : {i : Fin b // i ≠ Φ.idx}, f (Φ.σ i.1) := by
  rw [← Φ.bij.sum_comp f, Fintype.sum_sum_type]
  rfl


/-! ## The shift -/

/-- The projection part of the shifted substitution. -/
noncomputable def shiftσ {a b : ℕ} (σ : Fin b → Fin a) : Fin (b + 1) → Fin (a + 1) :=
  Fin.cases 0 (fun j : Fin b => (σ j).succ)

@[simp] theorem shiftσ_zero {a b : ℕ} (σ : Fin b → Fin a) : shiftσ σ 0 = 0 := rfl
@[simp] theorem shiftσ_succ {a b : ℕ} (σ : Fin b → Fin a) (j : Fin b) :
    shiftσ σ j.succ = (σ j).succ := rfl

theorem shiftσ_eq_zero_iff {a b : ℕ} {σ : Fin b → Fin a} {i : Fin (b + 1)} :
    shiftσ σ i = 0 ↔ i = 0 := by
  constructor
  · intro h
    by_contra h0
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
    rw [shiftσ_succ] at h
    exact Fin.succ_ne_zero (σ j) h
  · rintro rfl; rfl

theorem shiftσ_inj' (Φ : OSub a b ord) {i i' : Fin (b + 1)}
    (hi : i ≠ Φ.idx.succ) (hi' : i' ≠ Φ.idx.succ)
    (h : shiftσ Φ.σ i = shiftσ Φ.σ i') : i = i' := by
  by_cases h0 : i = 0
  · rw [h0, shiftσ_zero] at h
    rw [h0, shiftσ_eq_zero_iff.mp h.symm]
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
    by_cases h0' : i' = 0
    · rw [h0', shiftσ_zero] at h
      rw [shiftσ_succ] at h
      exact absurd h (Fin.succ_ne_zero (Φ.σ j))
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0'
      simp only [shiftσ_succ, Fin.succ_inj] at h
      have hj : j ≠ Φ.idx := fun hc => hi (by rw [hc])
      have hj' : j' ≠ Φ.idx := fun hc => hi' (by rw [hc])
      rw [Φ.σ_inj hj hj' h]

/-- **The shift**: a fresh component at index `0` reading the fresh slot `0`; all the other
components and slots are shifted by one. -/
noncomputable def shift (Φ : OSub a b ord) : OSub (a+1) (b+1) ord where
  idx := Φ.idx.succ
  τ := fun l => (Φ.τ l).succ
  σ := shiftσ Φ.σ
  bij := by
    have key : ∀ (l : Fin (ord + 2)) (i : Fin (b+1)), i ≠ Φ.idx.succ →
        (Φ.τ l).succ ≠ shiftσ Φ.σ i := by
      intro l i hi
      by_cases h0 : i = 0
      · rw [h0, shiftσ_zero]; exact Fin.succ_ne_zero _
      · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
        rw [shiftσ_succ]
        exact fun hc => Φ.τ_ne_σ l ⟨j, fun hj => hi (by rw [hj])⟩ (Fin.succ_injective _ hc)
    constructor
    · rintro x y h
      rcases x with l | i
      · rcases y with l' | i'
        · exact congrArg Sum.inl (Φ.τ_inj (Fin.succ_injective _ h))
        · exact absurd h (key l i'.1 i'.2)
      · rcases y with l' | i'
        · exact absurd h.symm (key l' i.1 i.2)
        · exact congrArg Sum.inr (Subtype.ext (Φ.shiftσ_inj' i.2 i'.2 h))
    · rintro m
      by_cases h0 : m = 0
      · refine ⟨Sum.inr ⟨0, fun hc => Fin.succ_ne_zero _ hc.symm⟩, ?_⟩
        rw [h0]; rfl
      · obtain ⟨m', rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
        obtain ⟨x, hx⟩ := Φ.bij.2 m'
        rcases x with l | i
        · refine ⟨Sum.inl l, ?_⟩
          simp only [Sum.elim_inl] at hx
          show (Φ.τ l).succ = m'.succ
          rw [hx]
        · refine ⟨Sum.inr ⟨i.1.succ, fun hc => i.2 (Fin.succ_injective _ hc)⟩, ?_⟩
          simp only [Sum.elim_inr] at hx
          show shiftσ Φ.σ i.1.succ = m'.succ
          rw [shiftσ_succ, hx]

/-! ## The derived substitution -/

/-- The atom-argument part of the derived substitution. -/
noncomputable def derivτ {a ord : ℕ} (τ : Fin (ord + 2) → Fin a) :
    Fin ((ord + 1) + 2) → Fin (a + 1) :=
  Fin.cases 0 (fun l : Fin (ord + 2) => (τ l).succ)

@[simp] theorem derivτ_zero {a ord : ℕ} (τ : Fin (ord + 2) → Fin a) : derivτ τ 0 = 0 := rfl
@[simp] theorem derivτ_succ {a ord : ℕ} (τ : Fin (ord + 2) → Fin a) (l : Fin (ord + 2)) :
    derivτ τ l.succ = (τ l).succ := rfl

/-- **The derived substitution**: the atom `∇^{ord}δ` is replaced by `∇^{ord+1}δ` applied to the
fresh slot `0` (the direction) and the old argument slots. -/
noncomputable def deriv (Φ : OSub a b ord) : OSub (a+1) b (ord+1) where
  idx := Φ.idx
  τ := derivτ Φ.τ
  σ := fun i => (Φ.σ i).succ
  bij := by
    have key : ∀ (l : Fin ((ord+1) + 2)) (i : Fin b), i ≠ Φ.idx →
        derivτ Φ.τ l ≠ (Φ.σ i).succ := by
      intro l i hi
      by_cases h0 : l = 0
      · rw [h0]; exact fun hc => Fin.succ_ne_zero _ hc.symm
      · obtain ⟨l', rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
        rw [derivτ_succ]
        exact fun hc => Φ.τ_ne_σ l' ⟨i, hi⟩ (Fin.succ_injective _ hc)
    have key2 : ∀ (l l' : Fin ((ord+1) + 2)), derivτ Φ.τ l = derivτ Φ.τ l' → l = l' := by
      intro l l' h
      by_cases h0 : l = 0
      · rw [h0, derivτ_zero] at h
        by_cases h1 : l' = 0
        · rw [h0, h1]
        · obtain ⟨l'', rfl⟩ := Fin.exists_succ_eq_of_ne_zero h1
          rw [derivτ_succ] at h
          exact absurd h.symm (Fin.succ_ne_zero _)
      · obtain ⟨l₁, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
        by_cases h1 : l' = 0
        · rw [h1, derivτ_zero] at h
          exact absurd h (Fin.succ_ne_zero _)
        · obtain ⟨l₂, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h1
          rw [derivτ_succ, derivτ_succ, Fin.succ_inj] at h
          rw [Φ.τ_inj h]
    constructor
    · rintro x y h
      rcases x with l | i
      · rcases y with l' | i'
        · exact congrArg Sum.inl (key2 l l' h)
        · exact absurd h (key l i'.1 i'.2)
      · rcases y with l' | i'
        · exact absurd h.symm (key l' i.1 i.2)
        · exact congrArg Sum.inr (Subtype.ext (Φ.σ_inj i.2 i'.2 (Fin.succ_injective _ h)))
    · rintro m
      by_cases h0 : m = 0
      · exact ⟨Sum.inl 0, by rw [h0]; rfl⟩
      · obtain ⟨m', rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
        obtain ⟨x, hx⟩ := Φ.bij.2 m'
        rcases x with l | i
        · refine ⟨Sum.inl l.succ, ?_⟩
          simp only [Sum.elim_inl] at hx
          show (Φ.τ l).succ = m'.succ
          rw [hx]
        · refine ⟨Sum.inr i, ?_⟩
          simp only [Sum.elim_inr] at hx
          show (Φ.σ i.1).succ = m'.succ
          rw [hx]

/-! ## The evaluations of the shifted and derived substitutions -/

theorem eval_shift {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} (Φ : OSub a b ord)
    (F : Fin (a+1) → AMB.TF (I := I) (M := M)) :
    (Φ.shift).eval G t F
      = Fin.cons (F 0) (Φ.eval G t (fun j : Fin a => F j.succ)) := by
  funext i
  by_cases h0 : i = 0
  · rw [h0, Fin.cons_zero]
    show (Φ.shift).eval G t F 0 = F 0
    rw [eval_slot (Φ.shift) F (fun hc => Fin.succ_ne_zero Φ.idx hc.symm)]
    rfl
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero h0
    by_cases hj : j = Φ.idx
    · rw [hj, Fin.cons_succ]
      exact ((eval_atom (Φ := Φ.shift) F).trans
        (eval_atom (Φ := Φ) (fun j : Fin a => F j.succ)).symm)
    · rw [eval_slot (Φ.shift) F (fun hc => hj (Fin.succ_injective _ hc)),
        Fin.cons_succ, eval_slot Φ (fun j : Fin a => F j.succ) hj]
      rfl

theorem eval_deriv {G : ℝ → Submission.Diff.SMet I M} {t : ℝ} (Φ : OSub a b ord)
    (F : Fin (a+1) → AMB.TF (I := I) (M := M)) :
    (Φ.deriv).eval G t F
      = Function.update (Φ.eval G t (fun j : Fin a => F j.succ)) Φ.idx
          (atomEval G t (derivτ Φ.τ) F) := by
  funext i
  by_cases hi : i = Φ.idx
  · rw [hi]
    exact ((eval_atom (Φ := Φ.deriv) F).trans
      (Function.update_self Φ.idx (atomEval G t (derivτ Φ.τ) F)
        (Φ.eval G t (fun j : Fin a => F j.succ))).symm)
  · rw [eval_slot (Φ.deriv) F hi, Function.update_of_ne hi,
      eval_slot Φ (fun j : Fin a => F j.succ) hi]
    rfl

end OSub

/-! ## The iterated packed derivative -/

/-- The `k`-fold iteration of `AMB.pD cov` on a packed object of arity `3`. -/
noncomputable def pDiter (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (T : AMB.Fam (I := I) (M := M) 3) : ∀ k : ℕ, AMB.Fam (I := I) (M := M) (k + 3)
  | 0 => T
  | k + 1 => AMB.pD cov (pDiter cov T k)

@[simp] theorem pDiter_zero (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (T : AMB.Fam (I := I) (M := M) 3) : pDiter cov T 0 = T := rfl

@[simp] theorem pDiter_succ (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (T : AMB.Fam (I := I) (M := M) 3) (k : ℕ) :
    pDiter cov T (k + 1) = AMB.pD cov (pDiter cov T k) := rfl

end Work.Diff.EXT.ConnCov.RicFlip.O
