import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.torus_uniqueness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Lipschitz bound for the lower-order part of the flat DeTurck nonlinearity

Let `Φ` be a nonlinearity of DeTurck shape (`Work.Diff.STE.Flat.IsDeTurckNonlin`), i.e. on the
non-degenerate locus

`Φ (x, (A, L, B)) = secOpFlat A B + N (x, (A, L))`,

where `secOpFlat A B = (reMat A)⁻¹ • B` is the *linear* principal part in the second derivative
`B`, and `N` is a `C^∞` function of the value and the first jet only.

The lemma proved here is the quantitative statement that the *nonlinear* part of `Φ` is Lipschitz
on the elliptic region: there is a constant `C ≥ 0` such that

`‖Φ (x, J₁) - Φ (x, J₂) - secOpFlat J₁.1 (J₁.2.2 - J₂.2.2)‖ ≤ C (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖)`

for all `x ∈ [0,1]ⁿ` and all pairs of jets `J₁`, `J₂` whose metric matrix is uniformly elliptic
with constant `lam > 0` and whose entries (and inverse entries) are bounded by `M`.  Note that the
second derivatives `J.2.2` do *not* appear on the right-hand side: the term `secOpFlat J₁.1 (…)`
subtracts the first-order (in `B`) part of the difference of `Φ`, leaving a remainder that
depends Lipschitz-continuously on the value and the first jet only.

This is the input of the Galerkin energy argument: the difference of two solutions is controlled
by the linearisation of the principal part plus a Lipschitz lower order term.

## Proof

Write `Φ (x, J) = secOpFlat J.1 J.2.2 + N (x, (J.1, J.2.1))` (the decomposition supplied by
`hshape`, applied at the two jets; the ellipticity forces `det (reMat J.1) ≠ 0`, so that the
decomposition is legal).  Then

`Φ (x, J₁) - Φ (x, J₂) - secOpFlat J₁.1 (J₁.2.2 - J₂.2.2)
  = (secOpFlat J₁.1 B₂ - secOpFlat J₂.1 B₂) + (N (x, (A₁,L₁)) - N (x, (A₂,L₂)))`

with `B₂ = J₂.2.2`.  The two summands are bounded separately:

* the first by `n⁴ M³ ‖A₁ - A₂‖`: this is the *algebraic* part.  Since
  `(reMat A₁)⁻¹ - (reMat A₂)⁻¹ = (reMat A₁)⁻¹ ((reMat A₂) - (reMat A₁)) (reMat A₂)⁻¹`
  (`Matrix.inv_sub_inv`), every entry of the difference of the inverses is bounded by
  `n² M² ‖A₁ - A₂‖` (the given entry bounds on the inverses multiply the bound on the entries of
  `A₂ - A₁`, which is at most the norm of `A₂ - A₁`), and the entries of `B₂` are bounded by `M`.

* the second by `C₂ (‖A₁ - A₂‖ + ‖L₁ - L₂‖)`: here `N` is `C^∞` on the open set
  `{det (reMat A) ≠ 0}`, and the admissible region is *compact and convex* (bounded entries +
  ellipticity is an intersection of closed half spaces, and is preserved by convex combinations
  because the quadratic form is linear in the matrix).  Hence the general lemma
  `exists_lipschitz_of_contDiffOn_compact_convex` applies to `(x, w) ↦ N (x, w)` on
  `[0,1]ⁿ × admissible`: a `C¹` function on a compact convex subset of its open domain has a
  finite Lipschitz constant (mean value inequality, the bound on the derivative coming from
  `IsCompact.exists_bound_of_continuousOn`).
-/

namespace Work.Diff.STE.flat.galerkin

/-! ## The quadratic form and the admissible region -/

/-- The quadratic form `∑ᵢ ∑ⱼ (reMat A)ᵢⱼ ξᵢ ξⱼ` of the real part of a matrix. -/
def quadF {n : ℕ} (A : Work.Diff.STE.Flat.MatC n) (ξ : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, Work.Diff.STE.Flat.reMat A i j * ξ i * ξ j

/-- The cube `[0,1]ⁿ` of the torus, in the "`Set.pi`" form. -/
def cubeN (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ : Fin n => Set.Icc (0:ℝ) 1

/-- The admissible region of the Galerkin argument: pairs (value, first jet) with entries bounded
by `M` and with the quadratic form of the metric matrix bounded below by `lam ‖·‖²`. -/
def jetAdm (n : ℕ) (lam M : ℝ) :
    Set (Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n)) :=
  {w | ‖w.1‖ ≤ M ∧ ‖w.2‖ ≤ M ∧ ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i)^2 ≤ quadF w.1 ξ}

lemma continuous_quadF {n : ℕ} (ξ : Fin n → ℝ) :
    Continuous (fun A : Work.Diff.STE.Flat.MatC n => quadF A ξ) := by
  simp only [quadF, Work.Diff.STE.Flat.reMat_apply]
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous (fun A : Work.Diff.STE.Flat.MatC n => (A i j).re) :=
    Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply i))
  exact (h1.mul continuous_const).mul continuous_const

/-- `reMat` is additive. -/
lemma reMat_add {n : ℕ} (A A' : Work.Diff.STE.Flat.MatC n) :
    Work.Diff.STE.Flat.reMat (A + A')
      = Work.Diff.STE.Flat.reMat A + Work.Diff.STE.Flat.reMat A' := by
  ext i j; simp [Work.Diff.STE.Flat.reMat]

/-- `reMat` is `ℝ`-homogeneous. -/
lemma reMat_smul {n : ℕ} (a : ℝ) (A : Work.Diff.STE.Flat.MatC n) :
    Work.Diff.STE.Flat.reMat (a • A) = a • Work.Diff.STE.Flat.reMat A := by
  ext i j; simp [Work.Diff.STE.Flat.reMat, Complex.mul_re]

/-- `reMat` commutes with subtraction. -/
lemma reMat_coe_sub {n : ℕ} (A A' : Work.Diff.STE.Flat.MatC n) :
    (Work.Diff.STE.Flat.reMat A' - Work.Diff.STE.Flat.reMat A)
      = Work.Diff.STE.Flat.reMat (A' - A) := by
  ext i j; simp [Work.Diff.STE.Flat.reMat]

/-- The quadratic form is additive in the matrix. -/
lemma quadF_add {n : ℕ} (A A' : Work.Diff.STE.Flat.MatC n) (ξ : Fin n → ℝ) :
    quadF (A + A') ξ = quadF A ξ + quadF A' ξ := by
  simp only [quadF, reMat_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_apply]; ring

/-- The quadratic form is homogeneous in the matrix. -/
lemma quadF_smul {n : ℕ} (a : ℝ) (A : Work.Diff.STE.Flat.MatC n) (ξ : Fin n → ℝ) :
    quadF (a • A) ξ = a * quadF A ξ := by
  simp only [quadF, reMat_smul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply]; ring

/-- The quadratic form of a convex combination is the convex combination of the quadratic
forms. -/
lemma quadF_add_smul {n : ℕ} (a b : ℝ) (A A' : Work.Diff.STE.Flat.MatC n)
    (ξ : Fin n → ℝ) :
    quadF (a • A + b • A') ξ = a * quadF A ξ + b * quadF A' ξ := by
  rw [quadF_add, quadF_smul, quadF_smul]

lemma isCompact_cubeN {n : ℕ} : IsCompact (cubeN n) :=
  isCompact_univ_pi fun _ => isCompact_Icc

lemma convex_cubeN {n : ℕ} : Convex ℝ (cubeN n) :=
  convex_pi fun _ _ => convex_Icc 0 1

lemma isClosed_jetAdm {n : ℕ} {lam M : ℝ} : IsClosed (jetAdm n lam M) := by
  have h1 : IsClosed {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) |
      ‖w.1‖ ≤ M} :=
    isClosed_le (continuous_norm.comp continuous_fst) continuous_const
  have h2 : IsClosed {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) |
      ‖w.2‖ ≤ M} :=
    isClosed_le (continuous_norm.comp continuous_snd) continuous_const
  have h3 : IsClosed {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) |
      ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i)^2 ≤ quadF w.1 ξ} := by
    have heq : {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) |
        ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i)^2 ≤ quadF w.1 ξ}
        = ⋂ ξ : Fin n → ℝ, {w | lam * ∑ i, (ξ i)^2 ≤ quadF w.1 ξ} := by
      ext w; simp
    rw [heq]
    exact isClosed_iInter fun ξ =>
      isClosed_le continuous_const ((continuous_quadF ξ).comp continuous_fst)
  rw [show jetAdm n lam M =
      ({w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) | ‖w.1‖ ≤ M}
        ∩ {w | ‖w.2‖ ≤ M}) ∩ {w | ∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i)^2 ≤ quadF w.1 ξ} by
    ext w; simp [jetAdm, and_assoc]]
  exact (h1.inter h2).inter h3

lemma convex_jetAdm {n : ℕ} {lam M : ℝ} : Convex ℝ (jetAdm n lam M) := by
  intro w hw w' hw' a b ha hb hab
  obtain ⟨hw1, hw2, hw3⟩ := hw
  obtain ⟨hw1', hw2', hw3'⟩ := hw'
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.smul_fst, Prod.fst_add]
    calc ‖a • w.1 + b • w'.1‖ ≤ ‖a • w.1‖ + ‖b • w'.1‖ := norm_add_le _ _
      _ = a * ‖w.1‖ + b * ‖w'.1‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * M + b * M :=
          add_le_add (mul_le_mul_of_nonneg_left hw1 ha) (mul_le_mul_of_nonneg_left hw1' hb)
      _ = M := by rw [← add_mul, hab, one_mul]
  · simp only [Prod.smul_snd, Prod.snd_add]
    calc ‖a • w.2 + b • w'.2‖ ≤ ‖a • w.2‖ + ‖b • w'.2‖ := norm_add_le _ _
      _ = a * ‖w.2‖ + b * ‖w'.2‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * M + b * M :=
          add_le_add (mul_le_mul_of_nonneg_left hw2 ha) (mul_le_mul_of_nonneg_left hw2' hb)
      _ = M := by rw [← add_mul, hab, one_mul]
  · intro ξ
    simp only [Prod.smul_fst, Prod.fst_add]
    rw [quadF_add_smul]
    have hcast : lam * ∑ i, (ξ i)^2
        = a * (lam * ∑ i, (ξ i)^2) + b * (lam * ∑ i, (ξ i)^2) := by
      rw [← add_mul, hab, one_mul]
    rw [hcast]
    exact add_le_add (mul_le_mul_of_nonneg_left (hw3 ξ) ha)
      (mul_le_mul_of_nonneg_left (hw3' ξ) hb)

lemma isCompact_jetAdm {n : ℕ} {lam M : ℝ} : IsCompact (jetAdm n lam M) := by
  refine (isCompact_closedBall (0 : Work.Diff.STE.Flat.MatC n ×
    (Fin n → Work.Diff.STE.Flat.MatC n)) M).of_isClosed_subset isClosed_jetAdm ?_
  intro w hw
  obtain ⟨h1, h2, -⟩ := hw
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le h1 h2

/-! ## Ellipticity forces non-degeneracy

This is a local copy of `Work.Diff.STE.flat.det_ne_zero_of_quadForm_le`, whose module cannot be
imported next to `torus_uniqueness` (both declare `sum_sum_mul_eq_dotProduct`). -/

lemma sum_sum_mul_eq_dotProduct_gk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ i, ∑ j, A i j * v i * v j = dotProduct v (A.mulVec v) := by
  rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma sum_sq_pos_of_ne_zero_gk {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < ∑ i, (v i) ^ 2 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hk' : v k ≠ 0 := by simpa using hk
  have hpos := Finset.sum_pos' (s := Finset.univ) (fun i _ => sq_nonneg (v i))
    ⟨k, Finset.mem_univ k, sq_pos_of_ne_zero hk'⟩
  simpa using hpos

/-- A real matrix whose quadratic form dominates `lam ‖·‖²` with `lam > 0` is nonsingular. -/
lemma det_ne_zero_of_quadForm_gk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {lam : ℝ}
    (hlam : 0 < lam)
    (h : ∀ v : Fin n → ℝ, lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, A i j * v i * v j) :
    A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h0 : ∑ i, ∑ j, A i j * v i * v j = 0 := by
    rw [sum_sum_mul_eq_dotProduct_gk, hv, dotProduct_zero]
  have hvpos : 0 < ∑ i, (v i) ^ 2 := sum_sq_pos_of_ne_zero_gk hvne
  have hle := h v
  rw [h0] at hle
  linarith [mul_pos hlam hvpos]

/-- Every point of the admissible region lies in the domain of smoothness of a DeTurck
nonlinearity. -/
lemma jetAdm_subset_det {n : ℕ} {lam M : ℝ} (hlam : 0 < lam) :
    jetAdm n lam M ⊆ {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) |
      (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} := by
  intro w hw
  exact det_ne_zero_of_quadForm_gk _ hlam (fun ξ => by simpa only [quadF] using hw.2.2 ξ)

/-! ## A `C¹` function on a compact convex subset of its open domain is Lipschitz -/

lemma exists_lipschitz_of_contDiffOn_compact_convex
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {U : Set E} (hU : IsOpen U) {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKU : K ⊆ U) {f : E → G} (hf : ContDiffOn ℝ (1 : WithTop ℕ∞) f U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K, ‖f y - f x‖ ≤ L * ‖y - x‖ := by
  have hcont : ContinuousOn (fun z => fderiv ℝ f z) K := by
    intro z hz
    have hca : ContDiffAt ℝ (1 : WithTop ℕ∞) f z := hf.contDiffAt (hU.mem_nhds (hKU hz))
    exact (hca.continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have hbdd : ∀ z ∈ K, ‖fderiv ℝ f z‖ ≤ max C 0 := fun z hz => (hC z hz).trans (le_max_left _ _)
  have hderiv : ∀ z ∈ K, HasFDerivWithinAt f (fderiv ℝ f z) K z := by
    intro z hz
    have hca : ContDiffAt ℝ (1 : WithTop ℕ∞) f z := hf.contDiffAt (hU.mem_nhds (hKU hz))
    exact (hca.differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbdd hKc hx hy

/-- **The lower-order part of a DeTurck nonlinearity is Lipschitz on the elliptic region.** -/
lemma n_lipschitz {n : ℕ}
    (N : (Fin n → ℝ) × (Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n)) →
      Work.Diff.STE.Flat.MatC n)
    (hNsm : ContDiffOn ℝ (⊤ : ℕ∞) N
      (Set.univ ×ˢ {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) |
        (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    (lam M : ℝ) (hlam : 0 < lam) (_hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ cubeN n, ∀ w₁ ∈ jetAdm n lam M, ∀ w₂ ∈ jetAdm n lam M,
      ‖N (x, w₁) - N (x, w₂)‖ ≤ L * (‖w₁.1 - w₂.1‖ + ‖w₁.2 - w₂.2‖) := by
  have hU₂ : IsOpen {w : Work.Diff.STE.Flat.MatC n ×
      (Fin n → Work.Diff.STE.Flat.MatC n) | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0} := by
    have hcont : Continuous (fun w : Work.Diff.STE.Flat.MatC n ×
        (Fin n → Work.Diff.STE.Flat.MatC n) => (Work.Diff.STE.Flat.reMat w.1).det) := by
      refine Continuous.matrix_det ?_
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact Complex.continuous_re.comp
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst))
    have heq : {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n) |
        (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}
        = (fun w => (Work.Diff.STE.Flat.reMat w.1).det) ⁻¹' {y : ℝ | y ≠ 0} := rfl
    rw [heq]
    exact isOpen_ne.preimage hcont
  have hU : IsOpen (Set.univ ×ˢ {w : Work.Diff.STE.Flat.MatC n ×
      (Fin n → Work.Diff.STE.Flat.MatC n) | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}) :=
    (isOpen_univ : IsOpen (Set.univ : Set (Fin n → ℝ))).prod hU₂
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_of_contDiffOn_compact_convex hU
    (isCompact_cubeN.prod isCompact_jetAdm)
    (convex_cubeN.prod convex_jetAdm)
    (fun p hp => ⟨Set.mem_univ _, jetAdm_subset_det hlam hp.2⟩)
    (hNsm.of_le (by simp))
  refine ⟨L, hL0, ?_⟩
  intro x hx w₁ hw₁ w₂ hw₂
  have h := hL (x, w₂) ⟨hx, hw₂⟩ (x, w₁) ⟨hx, hw₁⟩
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hL0)
  rw [Prod.mk_sub_mk, Prod.norm_def, sub_self, norm_zero, max_eq_right (norm_nonneg _),
    Prod.norm_def]
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

/-! ## The algebraic bound for the principal part -/

/-- **Difference of the entries of two matrix inverses.**  If the entries of `P⁻¹`, `Q⁻¹` are
bounded by `M` and those of `Q - P` by `δ`, then every entry of `P⁻¹ - Q⁻¹` is bounded by
`n² M² δ`. -/
lemma inv_sub_inv_entry_bound {n : ℕ} {P Q : Matrix (Fin n) (Fin n) ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0)
    (hiP : ∀ i j, ‖P⁻¹ i j‖ ≤ M) (hiQ : ∀ i j, ‖Q⁻¹ i j‖ ≤ M) {δ : ℝ}
    (hδ : ∀ i j, ‖(Q - P) i j‖ ≤ δ) :
    ∀ c d, ‖(P⁻¹ - Q⁻¹) c d‖ ≤ (n : ℝ)^2 * M * M * δ := by
  intro c d
  have hPQ : IsUnit P ↔ IsUnit Q :=
    ⟨fun _ => (Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hQ),
     fun _ => (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr hP)⟩
  rw [Matrix.inv_sub_inv hPQ]
  simp only [Matrix.mul_apply]
  calc ‖∑ k : Fin n, (∑ l : Fin n, P⁻¹ c l * (Q - P) l k) * Q⁻¹ k d‖
      ≤ ∑ k : Fin n, ‖(∑ l : Fin n, P⁻¹ c l * (Q - P) l k) * Q⁻¹ k d‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin n, (∑ l : Fin n, M * δ) * M := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        refine le_trans (mul_le_mul_of_nonneg_left (hiQ k d) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right ?_ hM)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul (hiP c l) (hδ l k) (norm_nonneg _) hM
    _ = (n : ℝ)^2 * M * M * δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The principal part of a DeTurck nonlinearity, with a *fixed* second jet `B`, is Lipschitz in
the metric matrix `A` on the elliptic region, with constant `n⁴ M³`. -/
lemma norm_secOpFlat_sub_le {n : ℕ} {A₁ A₂ : Work.Diff.STE.Flat.MatC n}
    {B : Fin n → Fin n → Work.Diff.STE.Flat.MatC n} {M : ℝ} (hM : 0 ≤ M)
    (hdet₁ : (Work.Diff.STE.Flat.reMat A₁).det ≠ 0)
    (hdet₂ : (Work.Diff.STE.Flat.reMat A₂).det ≠ 0)
    (hinv₁ : ∀ i j, ‖((Work.Diff.STE.Flat.reMat A₁)⁻¹) i j‖ ≤ M)
    (hinv₂ : ∀ i j, ‖((Work.Diff.STE.Flat.reMat A₂)⁻¹) i j‖ ≤ M)
    (hB : ∀ c d i j, ‖B c d i j‖ ≤ M) :
    ‖Work.Diff.STE.Flat.secOpFlat A₁ B - Work.Diff.STE.Flat.secOpFlat A₂ B‖
      ≤ (n : ℝ)^4 * M^3 * ‖A₁ - A₂‖ := by
  have hδ : ∀ k l, ‖(Work.Diff.STE.Flat.reMat A₂ - Work.Diff.STE.Flat.reMat A₁) k l‖
      ≤ ‖A₁ - A₂‖ := by
    intro k l
    rw [reMat_coe_sub]
    calc ‖Work.Diff.STE.Flat.reMat (A₂ - A₁) k l‖ ≤ ‖(A₂ - A₁) k l‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ‖(A₂ - A₁) k‖ := norm_le_pi_norm _ _
      _ ≤ ‖A₂ - A₁‖ := norm_le_pi_norm _ _
      _ = ‖A₁ - A₂‖ := norm_sub_rev _ _
  have hentry := inv_sub_inv_entry_bound (P := Work.Diff.STE.Flat.reMat A₁)
    (Q := Work.Diff.STE.Flat.reMat A₂) hM hdet₁ hdet₂ hinv₁ hinv₂ hδ
  have hC0 : 0 ≤ (n : ℝ)^2 * M * M * ‖A₁ - A₂‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hM) hM) (norm_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  have hdecomp : (Work.Diff.STE.Flat.secOpFlat A₁ B - Work.Diff.STE.Flat.secOpFlat A₂ B) i j
      = ∑ c, ∑ d, ((((Work.Diff.STE.Flat.reMat A₁)⁻¹ - (Work.Diff.STE.Flat.reMat A₂)⁻¹)
          c d : ℝ) : ℂ) * B c d i j := by
    simp only [Work.Diff.STE.Flat.secOpFlat, Pi.sub_apply, Matrix.sub_apply]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.ofReal_sub, sub_mul]
  rw [hdecomp]
  calc ‖∑ c, ∑ d, ((((Work.Diff.STE.Flat.reMat A₁)⁻¹ - (Work.Diff.STE.Flat.reMat A₂)⁻¹)
        c d : ℝ) : ℂ) * B c d i j‖
      ≤ ∑ c, ∑ d, ‖((((Work.Diff.STE.Flat.reMat A₁)⁻¹ - (Work.Diff.STE.Flat.reMat A₂)⁻¹)
        c d : ℝ) : ℂ) * B c d i j‖ := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun c _ => ?_)
        exact norm_sum_le _ _
    _ ≤ ∑ c, ∑ d, ((n : ℝ)^2 * M * M * ‖A₁ - A₂‖) * M := by
        refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
        rw [norm_mul, Complex.norm_real]
        exact mul_le_mul (hentry c d) (hB c d i j) (norm_nonneg _) hC0
    _ = (n : ℝ)^4 * M^3 * ‖A₁ - A₂‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `secOpFlat` is additive in its second argument (it is `(reMat A)⁻¹` contracted with `B`). -/
lemma secOpFlat_sub_arg {n : ℕ} (A : Work.Diff.STE.Flat.MatC n)
    (B C : Fin n → Fin n → Work.Diff.STE.Flat.MatC n) :
    Work.Diff.STE.Flat.secOpFlat A (B - C)
      = Work.Diff.STE.Flat.secOpFlat A B - Work.Diff.STE.Flat.secOpFlat A C := by
  ext i j
  simp only [Work.Diff.STE.Flat.secOpFlat, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_sub]

/-! ## The target -/

theorem nDiff_bound_quadForm {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (lam : ℝ) (hlam : 0 < lam) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Fin n → ℝ), (∀ i, x i ∈ Set.Icc (0:ℝ) 1) →
      ∀ (J₁ J₂ : Work.Diff.STE.Flat.Jet n),
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤
        ∑ i, ∑ j, Work.Diff.STE.Flat.reMat J₁.1 i j * ξ i * ξ j) →
      (∀ ξ : Fin n → ℝ, lam * ∑ i, (ξ i) ^ 2 ≤
        ∑ i, ∑ j, Work.Diff.STE.Flat.reMat J₂.1 i j * ξ i * ξ j) →
      (∀ i j, ‖J₁.1 i j‖ ≤ M) → (∀ i j, ‖J₂.1 i j‖ ≤ M) →
      (∀ i j, ‖((Work.Diff.STE.Flat.reMat J₁.1)⁻¹) i j‖ ≤ M) →
      (∀ i j, ‖((Work.Diff.STE.Flat.reMat J₂.1)⁻¹) i j‖ ≤ M) →
      (∀ c i j, ‖J₁.2.1 c i j‖ ≤ M) → (∀ c i j, ‖J₂.2.1 c i j‖ ≤ M) →
      (∀ c d i j, ‖J₁.2.2 c d i j‖ ≤ M) → (∀ c d i j, ‖J₂.2.2 c d i j‖ ≤ M) →
      ‖Φ (x, J₁) - Φ (x, J₂) - Work.Diff.STE.Flat.secOpFlat J₁.1 (J₁.2.2 - J₂.2.2)‖
        ≤ C * (‖J₁.1 - J₂.1‖ + ‖J₁.2.1 - J₂.2.1‖) := by
  obtain ⟨_hΦsm, N, hNsm, hNΦ, _hNper⟩ := hshape
  obtain ⟨C₂, hC₂0, hC₂⟩ := n_lipschitz N hNsm lam M hlam hM
  refine ⟨(n:ℝ)^4 * M^3 + C₂,
    add_nonneg (mul_nonneg (by positivity) (pow_nonneg hM 3)) hC₂0, ?_⟩
  intro x hx J₁ J₂ hE₁ hE₂ hA₁ hA₂ hinv₁ hinv₂ hL₁ hL₂ hB₁ hB₂
  have hxmem : x ∈ cubeN n := Set.mem_univ_pi.mpr hx
  have hdet₁ : (Work.Diff.STE.Flat.reMat J₁.1).det ≠ 0 :=
    det_ne_zero_of_quadForm_gk _ hlam (fun ξ => by simpa only [quadF] using hE₁ ξ)
  have hdet₂ : (Work.Diff.STE.Flat.reMat J₂.1).det ≠ 0 :=
    det_ne_zero_of_quadForm_gk _ hlam (fun ξ => by simpa only [quadF] using hE₂ ξ)
  have hΦ₁ : Φ (x, J₁) = Work.Diff.STE.Flat.secOpFlat J₁.1 J₁.2.2 + N (x, (J₁.1, J₁.2.1)) :=
    hNΦ x J₁.1 J₁.2.1 J₁.2.2 hdet₁
  have hΦ₂ : Φ (x, J₂) = Work.Diff.STE.Flat.secOpFlat J₂.1 J₂.2.2 + N (x, (J₂.1, J₂.2.1)) :=
    hNΦ x J₂.1 J₂.2.1 J₂.2.2 hdet₂
  have hK₁ : (J₁.1, J₁.2.1) ∈ jetAdm n lam M :=
    ⟨(pi_norm_le_iff_of_nonneg hM).mpr
        (fun i => (pi_norm_le_iff_of_nonneg hM).mpr (fun j => hA₁ i j)),
     (pi_norm_le_iff_of_nonneg hM).mpr (fun c => (pi_norm_le_iff_of_nonneg hM).mpr
        (fun i => (pi_norm_le_iff_of_nonneg hM).mpr (fun j => hL₁ c i j))), hE₁⟩
  have hK₂ : (J₂.1, J₂.2.1) ∈ jetAdm n lam M :=
    ⟨(pi_norm_le_iff_of_nonneg hM).mpr
        (fun i => (pi_norm_le_iff_of_nonneg hM).mpr (fun j => hA₂ i j)),
     (pi_norm_le_iff_of_nonneg hM).mpr (fun c => (pi_norm_le_iff_of_nonneg hM).mpr
        (fun i => (pi_norm_le_iff_of_nonneg hM).mpr (fun j => hL₂ c i j))), hE₂⟩
  have h₁ := norm_secOpFlat_sub_le hM hdet₁ hdet₂ hinv₁ hinv₂ (B := J₂.2.2) hB₂
  have h₂ := hC₂ x hxmem (J₁.1, J₁.2.1) hK₁ (J₂.1, J₂.2.1) hK₂
  have hdec : Φ (x, J₁) - Φ (x, J₂) - Work.Diff.STE.Flat.secOpFlat J₁.1 (J₁.2.2 - J₂.2.2)
      = (Work.Diff.STE.Flat.secOpFlat J₁.1 J₂.2.2 - Work.Diff.STE.Flat.secOpFlat J₂.1 J₂.2.2)
        + (N (x, (J₁.1, J₁.2.1)) - N (x, (J₂.1, J₂.2.1))) := by
    rw [hΦ₁, hΦ₂, secOpFlat_sub_arg]
    abel
  rw [hdec]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add h₁ h₂) ?_
  have hL10 : 0 ≤ (n : ℝ) ^ 4 * M ^ 3 := mul_nonneg (by positivity) (pow_nonneg hM 3)
  nlinarith [norm_nonneg (J₁.1 - J₂.1), norm_nonneg (J₁.2.1 - J₂.2.1), hL10, hC₂0]

end Work.Diff.STE.flat.galerkin
