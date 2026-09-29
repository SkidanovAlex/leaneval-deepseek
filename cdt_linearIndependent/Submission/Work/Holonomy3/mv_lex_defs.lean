import Mathlib
import Submission.Work.Holonomy3.jensen_mean_ineq

/-!
# Multivariable lexicographic-minimum coefficient bound: local definitions

This file sets up the vocabulary for the lemma `Work.Holonomy3.mv_lexmin_coeff_le_integral`:
the torus parameterisation, the normalised torus measure, the evaluation of a finitely supported
multi-index family, and the "slice along the first coordinate" operation used in the induction.

* `tor s` is the torus point `(e^{2πi s_j})_j`;
* `torMeasure d` is the normalised measure on the parameter cube `[0,1]^d`;
* `pevalF c z` is `∑_m c m * ∏_j z_j^{m_j}` for a finitely supported family `c`;
* `sliceF c t` is the family `m ↦ c (t :: m)` of coefficients of the `t`-th power of the first
  variable;
* `LexMinF c n` says that `n` is the lexicographically minimal element of the support of `c`
  (lex order with the *first* coordinate the most significant).
-/

namespace Work.Holonomy3

open scoped BigOperators

noncomputable section

/-- The torus point with parameter `s : Fin d → ℝ`. -/
def tor {d : ℕ} (s : Fin d → ℝ) : Fin d → ℂ :=
  fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (s j : ℂ))

/-- The normalised measure on the parameter cube `[0,1]^d`. -/
abbrev torMeasure (d : ℕ) : MeasureTheory.Measure (Fin d → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin d => MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1))

/-- Evaluation of a finitely supported coefficient family at a point. -/
def pevalF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (z : Fin d → ℂ) : ℂ :=
  ∑ m ∈ c.support, c m * ∏ j, z j ^ (m j)

/-- The multi-index `t :: m` obtained by prepending `t` as the first coordinate. -/
def consIdx {d : ℕ} (t : ℕ) (m : Fin d →₀ ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.cons t fun i => m i)

/-- `consIdx t` is injective. -/
theorem consIdx_inj {d : ℕ} (t : ℕ) {m m' : Fin d →₀ ℕ} (h : consIdx t m = consIdx t m') :
    m = m' := by
  have h2 : (Finsupp.equivFunOnFinite (consIdx t m) : Fin (d + 1) → ℕ)
      = Finsupp.equivFunOnFinite (consIdx t m') := by rw [h]
  simp only [consIdx] at h2
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
  have h3 : (fun i => m i) = (fun i => m' i) := (Fin.cons_inj.mp h2).2
  exact Finsupp.ext (fun i => congrFun h3 i)

/-- Injectivity of `consIdx t` as a `Set.InjOn` statement (the form needed by
`Finsupp.comapDomain`). -/
theorem consIdx_injOn {d : ℕ} (t : ℕ) (s : Set (Fin d →₀ ℕ)) :
    Set.InjOn (consIdx t) s :=
  fun _ _ _ _ h => consIdx_inj t h

/-- Slicing a coefficient family along the first coordinate: `sliceF c t` is the family of
coefficients of the `t`-th power of the first variable. -/
def sliceF {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (t : ℕ) : (Fin d →₀ ℕ) →₀ ℂ :=
  Finsupp.comapDomain (consIdx t) c (consIdx_injOn t _)

@[simp]
theorem sliceF_apply {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) (t : ℕ) (m : Fin d →₀ ℕ) :
    sliceF c t m = c (consIdx t m) :=
  Finsupp.comapDomain_apply _ _ _ _

/-- The defining coordinate formula for `consIdx`. -/
theorem consIdx_apply {d : ℕ} (t : ℕ) (m : Fin d →₀ ℕ) :
    (consIdx t m : Fin (d + 1) → ℕ) = Fin.cons t (fun i => m i) := by
  funext a
  have h := Finsupp.equivFunOnFinite_apply
    (Finsupp.equivFunOnFinite.symm (Fin.cons t (fun i => m i))) a
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The `0`-th coordinate of `consIdx t m` is `t`. -/
@[simp]
theorem consIdx_zero {d : ℕ} (t : ℕ) (m : Fin d →₀ ℕ) : consIdx t m (0 : Fin (d + 1)) = t := by
  rw [consIdx_apply, Fin.cons_zero]

/-- The remaining coordinates of `consIdx t m` are those of `m`. -/
@[simp]
theorem consIdx_succ {d : ℕ} (t : ℕ) (m : Fin d →₀ ℕ) (i : Fin d) :
    consIdx t m i.succ = m i := by
  rw [consIdx_apply, Fin.cons_succ]

/-- Total degree of `consIdx`. -/
theorem consIdx_degree {d : ℕ} (t : ℕ) (m : Fin d →₀ ℕ) :
    (consIdx t m).degree = t + m.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fin.sum_univ_succ]
  simp

/-- The point `(w, z₁, …, z_d)` of `ℂ^{d+1}`. -/
def consPt {d : ℕ} (w : ℂ) (z : Fin d → ℂ) : Fin (d + 1) → ℂ := Fin.cons w z

/-- The tail of a multi-index on `Fin (d+1)`: drop the first coordinate. -/
def tailIdx {d : ℕ} (m : Fin (d + 1) →₀ ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m i.succ)

@[simp]
theorem tailIdx_apply {d : ℕ} (m : Fin (d + 1) →₀ ℕ) (i : Fin d) : tailIdx m i = m i.succ := by
  have h := Finsupp.equivFunOnFinite_apply
    (Finsupp.equivFunOnFinite.symm (fun i : Fin d => m i.succ)) i
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- `consIdx` and `tailIdx` are inverse to each other. -/
@[simp]
theorem consIdx_tailIdx {d : ℕ} (m : Fin (d + 1) →₀ ℕ) : consIdx (m 0) (tailIdx m) = m := by
  ext j
  refine Fin.cases ?_ ?_ j
  · simp
  · intro i; simp

@[simp]
theorem tailIdx_consIdx {d : ℕ} (t : ℕ) (m : Fin d →₀ ℕ) : tailIdx (consIdx t m) = m := by
  ext i
  simp

/-- The set of first coordinates occurring in the support of `c`, where `c` is a family of
multi-indices on `Fin (d+1)`. -/
def suppFst {d : ℕ} (c : (Fin (d + 1) →₀ ℕ) →₀ ℂ) : Finset ℕ :=
  c.support.image (fun m => m 0)

theorem mem_suppFst {d : ℕ} {c : (Fin (d + 1) →₀ ℕ) →₀ ℂ} {t : ℕ} :
    t ∈ suppFst c ↔ ∃ m ∈ c.support, m 0 = t := by
  simp [suppFst]

/-- `n` is the lexicographically minimal element of the support of `c`, for the lexicographic
order in which the first coordinate is the most significant. -/
def LexMinF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (n : Fin d →₀ ℕ) : Prop :=
  n ∈ c.support ∧ ∀ m ∈ c.support, toLex n ≤ toLex m

/-- A finitely supported family is homogeneous of degree `D` if every multi-index in its support
has total degree `D`. -/
def IsHomogF {d : ℕ} (c : (Fin d →₀ ℕ) →₀ ℂ) (D : ℕ) : Prop :=
  ∀ m ∈ c.support, m.degree = D

end

end Work.Holonomy3
