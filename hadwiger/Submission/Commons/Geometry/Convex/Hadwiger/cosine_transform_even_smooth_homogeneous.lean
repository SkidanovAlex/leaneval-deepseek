import Mathlib
import Submission.Commons.Analysis.MeasureTheory.integral_cosine_separable
import Submission.Commons.Analysis.MeasureTheory.exists_radial_normalization
import Submission.Commons.Analysis.MeasureTheory.harmonic_coeff_decay_any
import Submission.Commons.Analysis.MeasureTheory.cosine_even_eigenvalue_decay
import Submission.Commons.Analysis.MeasureTheory.harmonic_fourier_residual
import Submission.Commons.Analysis.MeasureTheory.harmonic_sup_norm_bound
import Submission.Commons.Analysis.MeasureTheory.integral_even_mul_odd
import Submission.Commons.Analysis.MeasureTheory.harmonic_cross_degree_orthogonal
import Submission.Commons.Analysis.MeasureTheory.harmonic_polynomial_L2_dense_even
import Submission.Commons.Algebra.MvPolynomial.exists_harmonic_orthonormal_basis
import Submission.Commons.Algebra.MvPolynomial.homogeneous_eval_smul
import Submission.Commons.Algebra.MvPolynomial.harmHom_finrank_le
import Submission.Commons.Algebra.Binomial.harmonic_dim_arith

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section
namespace Commons.Geometry.Convex.Hadwiger

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical ENNReal NNReal Pointwise Topology
open Filter



/-- The antipodal reflection on the unit sphere. -/
def reflSphere {V : Type*} [NormedAddCommGroup V] (θ : Metric.sphere (0 : V) 1) :
    Metric.sphere (0 : V) 1 :=
  ⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using (mem_sphere_zero_iff_norm.mp θ.2)⟩

@[simp] lemma reflSphere_coe {V : Type*} [NormedAddCommGroup V]
    (θ : Metric.sphere (0 : V) 1) : (reflSphere θ : V) = -θ.1 := rfl

lemma reflSphere_involutive {V : Type*} [NormedAddCommGroup V]
    (θ : Metric.sphere (0 : V) 1) : reflSphere (reflSphere θ) = θ := by
  apply Subtype.ext
  simp [reflSphere]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

lemma unit_mem {x : V} (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- The function `x ↦ φ ‖x‖ * g (x/‖x‖)` (with value `0` at the origin). -/
def radialLift (φ : ℝ → ℝ) (g : Metric.sphere (0 : V) 1 → ℝ) : V → ℝ :=
  fun x => if hx : x = 0 then 0
    else φ ‖x‖ * g ⟨‖x‖⁻¹ • x, unit_mem hx⟩

@[simp] lemma radialLift_zero (φ : ℝ → ℝ) (g : Metric.sphere (0 : V) 1 → ℝ) :
    radialLift φ g 0 = 0 := by simp [radialLift]

lemma radialLift_apply_ne {φ : ℝ → ℝ} {g : Metric.sphere (0 : V) 1 → ℝ}
    {x : V} (hx : x ≠ 0) :
    radialLift φ g x = φ ‖x‖ * g ⟨‖x‖⁻¹ • x, unit_mem hx⟩ := by
  simp only [radialLift, dif_neg hx]

lemma neg_normalize {x : V} (hx : x ≠ 0) :
    (⟨‖-x‖⁻¹ • (-x), unit_mem (neg_ne_zero.mpr hx)⟩ : Metric.sphere (0:V) 1)
      = reflSphere (⟨‖x‖⁻¹ • x, unit_mem hx⟩ : Metric.sphere (0:V) 1) := by
  apply Subtype.ext
  show ‖-x‖⁻¹ • (-x) = - (‖x‖⁻¹ • x)
  rw [norm_neg, smul_neg]

lemma radialLift_neg {φ : ℝ → ℝ} {g : Metric.sphere (0 : V) 1 → ℝ}
    (hg : ∀ θ, g (reflSphere θ) = g θ) :
    ∀ x : V, radialLift φ g (-x) = radialLift φ g x := by
  intro x
  by_cases hx : x = 0
  · subst hx; simp [radialLift]
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [radialLift_apply_ne (φ := φ) (g := g) hnx, radialLift_apply_ne (φ := φ) (g := g) hx,
      neg_normalize hx, hg, norm_neg]

lemma radialLift_continuousOn_compl {φ : ℝ → ℝ} {g : Metric.sphere (0 : V) 1 → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) :
    ContinuousOn (radialLift φ g) ({0}ᶜ : Set V) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hdir : Continuous (fun y : ({0}ᶜ : Set V) => (homeomorphUnitSphereProd V y).1) :=
    continuous_fst.comp (homeomorphUnitSphereProd V).continuous
  have hcont : Continuous (fun y : ({0}ᶜ : Set V) =>
      φ ‖(y : V)‖ * g (homeomorphUnitSphereProd V y).1) :=
    (hφ.comp (continuous_norm.comp continuous_subtype_val)).mul (hg.comp hdir)
  refine hcont.congr (fun y => ?_)
  have hy : (y : V) ≠ 0 := fun h => y.2 (by simp [h])
  rw [Set.domRestrict_apply, radialLift_apply_ne (φ := φ) (g := g) hy]
  rw [show ((homeomorphUnitSphereProd V y).1 : Metric.sphere (0:V) 1)
      = ⟨‖(y:V)‖⁻¹ • (y:V), unit_mem hy⟩ from Subtype.ext (by
        rw [homeomorphUnitSphereProd_apply_fst_coe])]

lemma radialLift_continuous {φ : ℝ → ℝ} {g : Metric.sphere (0 : V) 1 → ℝ}
    (hφ : Continuous φ) (hg : Continuous g) (hφ0 : φ 0 = 0) :
    Continuous (radialLift φ g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [ContinuousAt, radialLift_zero]
    obtain ⟨C, hC⟩ := (isCompact_univ (X := Metric.sphere (0:V) 1)).exists_bound_of_continuousOn
      hg.continuousOn
    set C' : ℝ := max C 0 with hC'def
    have hC'nn : 0 ≤ C' := le_max_right _ _
    have hbound : ∀ y : V, ‖radialLift φ g y‖ ≤ C' * |φ ‖y‖| := by
      intro y
      by_cases hy : y = 0
      · subst hy; rw [radialLift_zero, norm_zero]; exact mul_nonneg hC'nn (abs_nonneg _)
      · rw [radialLift_apply_ne (φ := φ) (g := g) hy, norm_mul, Real.norm_eq_abs]
        have h1 : ‖g ⟨‖y‖⁻¹ • y, unit_mem hy⟩‖ ≤ C' :=
          le_trans (hC _ (mem_univ _)) (le_max_left _ _)
        calc |φ ‖y‖| * ‖g _‖ ≤ |φ ‖y‖| * C' :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ = C' * |φ ‖y‖| := by ring
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (Eventually.of_forall hbound) ?_
    have h1 : Tendsto (fun y : V => φ ‖y‖) (𝓝 0) (𝓝 0) := by
      have hnorm : Tendsto (fun y : V => ‖y‖) (𝓝 (0:V)) (𝓝 (0:ℝ)) := by
        simpa using (continuous_norm : Continuous (fun y : V => ‖y‖)).tendsto (0:V)
      have h2 : Tendsto (fun y : V => φ ‖y‖) (𝓝 (0:V)) (𝓝 (φ 0)) :=
        (hφ.tendsto (0:ℝ)).comp hnorm
      simpa [hφ0] using h2
    have h2 : Tendsto (fun y : V => |φ ‖y‖|) (𝓝 0) (𝓝 0) := by
      simpa using h1.abs
    simpa using (tendsto_const_nhds.mul h2)
  · exact (radialLift_continuousOn_compl hφ hg).continuousAt
      (isOpen_compl_singleton.mem_nhds (by simpa using hx))

lemma exists_norm_bound_of_compactSupport {φ : ℝ → ℝ} (hφs : HasCompactSupport φ) :
    ∃ R : ℝ, ∀ x : V, φ ‖x‖ ≠ 0 → ‖x‖ ≤ R := by
  have hc : IsCompact (tsupport φ) := hφs
  have hb : Bornology.IsBounded (tsupport φ) := hc.isBounded
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0:ℝ)).mp hb
  refine ⟨r, fun x hx => ?_⟩
  have hxs : ‖x‖ ∈ tsupport φ := subset_tsupport _ (by simpa [Function.mem_support] using hx)
  have h2 := hr hxs
  simpa [Metric.mem_closedBall, dist_eq_norm] using h2

lemma inner_norm_smul {u x : V} (hu : u ≠ 0) :
    |inner ℝ u x| = ‖u‖ * |inner ℝ (‖u‖⁻¹ • u) x| := by
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have h1 : u = ‖u‖ • (‖u‖⁻¹ • u) := by
    rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  conv_lhs => rw [h1]
  rw [inner_smul_left, abs_mul,
    show (starRingEnd ℝ) ‖u‖ = ‖u‖ from rfl, abs_of_nonneg (norm_nonneg u)]





variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]

lemma assemble_main
    (p : V → ℝ)
    (hph : ∀ (a : ℝ) (x : V), 0 ≤ a → p (a • x) = a * p x)
    (g : Metric.sphere (0 : V) 1 → ℝ) (hgcont : Continuous g)
    (hgeven : ∀ θ, g (reflSphere θ) = g θ)
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : φ 0 = 0) (hφs : HasCompactSupport φ)
    (hφnorm : (∫ r : Set.Ioi (0 : ℝ), (r : ℝ) * φ r
        ∂(MeasureTheory.Measure.volumeIoiPow (Module.finrank ℝ V - 1))) = 1)
    (hgT : ∀ u : Metric.sphere (0 : V) 1,
      (∫ θ : Metric.sphere (0 : V) 1, |inner ℝ (u : V) (θ : V)| * g θ
        ∂MeasureTheory.volume.toSphere) = p (u : V)) :
    ∃ f : V → ℝ, Continuous f ∧ (∀ x : V, f (-x) = f x) ∧
      (∃ R : ℝ, ∀ x : V, f x ≠ 0 → ‖x‖ ≤ R) ∧
      (∀ u : V, p u = ∫ x : V, |inner ℝ u x| * f x) := by
  refine ⟨radialLift φ g, radialLift_continuous hφ hgcont hφ0,
    radialLift_neg hgeven, ?_, ?_⟩
  · obtain ⟨R, hR⟩ := exists_norm_bound_of_compactSupport (V := V) hφs
    refine ⟨R, fun x hx => hR x ?_⟩
    by_cases hx0 : x = 0
    · subst hx0; simp [radialLift] at hx
    · rw [radialLift_apply_ne (φ := φ) (g := g) hx0] at hx
      exact fun hc => hx (by rw [hc, zero_mul])
  · intro u
    by_cases hu : u = 0
    · subst hu
      have hp0 : p 0 = 0 := by
        have h := hph 0 0 (le_refl 0); simpa using h
      rw [hp0]
      simp [radialLift]
    · set θu : Metric.sphere (0 : V) 1 := ⟨‖u‖⁻¹ • u, unit_mem hu⟩ with hθu
      have hθucoe : (θu : V) = ‖u‖⁻¹ • u := by rw [hθu]
      have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
      have hspec : ∀ (r : Set.Ioi (0 : ℝ)) (θ : Metric.sphere (0 : V) 1),
          radialLift φ g (r.1 • (θ : V)) = (fun s : Set.Ioi (0:ℝ) => φ s.1) r * g θ := by
        intro r θ
        have hrpos : 0 < r.1 := r.2
        have hne : r.1 • (θ : V) ≠ 0 := by
          intro h
          have h0 : (θ : V) = 0 := by
            have := congrArg (fun z => r.1⁻¹ • z) h
            simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hrpos)] using this
          have hnormθ : ‖(θ : V)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
          rw [h0] at hnormθ
          simp at hnormθ
        have hnormr : ‖r.1 • (θ : V)‖ = r.1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos,
            mem_sphere_zero_iff_norm.mp θ.2, mul_one]
        have hθeq : (⟨‖r.1 • (θ : V)‖⁻¹ • (r.1 • (θ : V)), unit_mem hne⟩
              : Metric.sphere (0 : V) 1) = θ := by
          apply Subtype.ext
          show ‖r.1 • (θ : V)‖⁻¹ • (r.1 • (θ : V)) = (θ : V)
          rw [hnormr, smul_smul, inv_mul_cancel₀ (ne_of_gt hrpos), one_smul]
        rw [radialLift_apply_ne (φ := φ) (g := g) hne, hθeq, hnormr]
      have hsep : (∫ x : V, |inner ℝ (θu : V) x| * radialLift φ g x) = p (θu : V) := by
        have h := Commons.Analysis.MeasureTheory.integral_cosine_separable (V := V)
          (θu : V) g (fun s : Set.Ioi (0:ℝ) => φ s.1) (radialLift φ g) hspec
        beta_reduce at h
        rw [hgT θu, hφnorm, mul_one] at h
        exact h
      calc p u
          = p (‖u‖ • (θu : V)) := by
              rw [hθucoe, smul_smul, mul_inv_cancel₀ hnorm, one_smul]
        _ = ‖u‖ * p (θu : V) := by
              rw [hph ‖u‖ (θu : V) (norm_nonneg u)]
        _ = ‖u‖ * (∫ x : V, |inner ℝ (θu : V) x| * radialLift φ g x) := by rw [hsep]
        _ = ∫ x : V, ‖u‖ * (|inner ℝ (θu : V) x| * radialLift φ g x) := by
              rw [MeasureTheory.integral_const_mul]
        _ = ∫ x : V, |inner ℝ u x| * radialLift φ g x := by
              refine MeasureTheory.integral_congr_ae
                (Eventually.of_forall (fun x => ?_))
              beta_reduce
              have hx : |inner ℝ u x| = ‖u‖ * |inner ℝ (θu : V) x| := by
                rw [hθucoe]; exact inner_norm_smul hu
              rw [hx]; ring




set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped BigOperators



abbrev ctE (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev ctSph (n : ℕ) := Metric.sphere (0 : ctE n) 1

def polyFun {n : ℕ} (Y : MvPolynomial (Fin n) ℝ) : ctSph n → ℝ :=
  fun θ => MvPolynomial.eval (fun i : Fin n => (θ : ctE n) i) Y

noncomputable def hbVec (n k : ℕ) [Nonempty (Fin n)] :
    Fin (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k))
      → Commons.Algebra.MvPolynomial.harmHom n k :=
  Classical.choose (Commons.Algebra.MvPolynomial.exists_orthonormalBasis_harmHom (n := n) (k := k))

lemma hbVec_orth {n k : ℕ} [Nonempty (Fin n)]
    (i j : Fin (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k))) :
    Commons.Algebra.MvPolynomial.harmBilin n k (hbVec n k i) (hbVec n k j)
      = if i = j then (1 : ℝ) else 0 :=
  (Classical.choose_spec (Commons.Algebra.MvPolynomial.exists_orthonormalBasis_harmHom
    (n := n) (k := k))).1 i j

noncomputable def hbPoly (n k : ℕ) [Nonempty (Fin n)] :
    Fin (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k)) → MvPolynomial (Fin n) ℝ :=
  fun j => ((hbVec n k j : Commons.Algebra.MvPolynomial.harmHom n k) : MvPolynomial (Fin n) ℝ)

lemma hbPoly_mem {n k : ℕ} [Nonempty (Fin n)]
    (j : Fin (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k))) :
    hbPoly n k j ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k :=
  (Commons.Algebra.MvPolynomial.mem_harmHom.mp (hbVec n k j).2).1

lemma hbPoly_lap {n k : ℕ} [Nonempty (Fin n)]
    (j : Fin (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k))) :
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (hbPoly n k j))) = 0 := by
  have h := (Commons.Algebra.MvPolynomial.mem_harmHom.mp (hbVec n k j).2).2
  rwa [Commons.Algebra.MvPolynomial.lapLM_apply] at h

lemma hbPoly_orth {n k : ℕ} [Nonempty (Fin n)]
    (i j : Fin (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k))) :
    (∫ θ : ctSph n, polyFun (hbPoly n k i) θ * polyFun (hbPoly n k j) θ ∂volume.toSphere)
      = if i = j then (1 : ℝ) else 0 := by
  have h := hbVec_orth (n := n) (k := k) i j
  rw [Commons.Algebra.MvPolynomial.harmBilin_apply,
    Commons.Algebra.MvPolynomial.harmPair] at h
  exact h

/-- For a homogeneous polynomial of degree `k`, evaluation at `-θ` is `(-1)^k` times the value. -/
lemma polyFun_refl {n k : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) (θ : ctSph n) :
    polyFun P (reflSphere θ) = (-1 : ℝ) ^ k * polyFun P θ := by
  have h1 : (reflSphere θ : ctE n) = (-1 : ℝ) • (θ : ctE n) := by
    rw [reflSphere_coe, neg_smul, one_smul]
  have h2 := Commons.Algebra.MvPolynomial.homogeneous_eval_smul P hP (-1 : ℝ) (θ : ctE n)
  simp only [polyFun]
  rw [show (fun i : Fin n => (reflSphere θ : ctE n) i) = (fun i : Fin n => ((-1:ℝ) • (θ:ctE n)) i) from by
    rw [h1]]
  rw [h2]


lemma hbVec_span {n k : ℕ} [Nonempty (Fin n)] :
    Submodule.span ℝ (Set.range (hbVec n k)) = ⊤ :=
  (Classical.choose_spec (Commons.Algebra.MvPolynomial.exists_orthonormalBasis_harmHom
    (n := n) (k := k))).2

lemma hbPoly_span {n k : ℕ} [Nonempty (Fin n)] (H : MvPolynomial (Fin n) ℝ)
    (hH : H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlap : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0) :
    ∃ c : Fin (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k)) → ℝ,
      ∀ θ : ctSph n, polyFun H θ =
        ∑ j : Fin (Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k)),
          c j * polyFun (hbPoly n k j) θ := by
  have hHmem : H ∈ Commons.Algebra.MvPolynomial.harmHom n k :=
    Commons.Algebra.MvPolynomial.mem_harmHom.mpr ⟨hH, by
      rwa [Commons.Algebra.MvPolynomial.lapLM_apply]⟩
  have hmem : (⟨H, hHmem⟩ : Commons.Algebra.MvPolynomial.harmHom n k)
      ∈ Submodule.span ℝ (Set.range (hbVec n k)) := by
    rw [hbVec_span]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun ℝ] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, fun θ => ?_⟩
  have h2 : H = ∑ j, c j • hbPoly n k j := by
    have h3 : ((∑ j, c j • hbVec n k j : Commons.Algebra.MvPolynomial.harmHom n k) :
        MvPolynomial (Fin n) ℝ) = H := by rw [hc]
    rw [← h3]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  rw [h2, polyFun, MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Commons.Algebra.MvPolynomial.eval_smul_sphere]
  rfl



section Main

abbrev dK (n k : ℕ) : ℕ := Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n k)

noncomputable def Yfam (n : ℕ) (k : ℕ) [Nonempty (Fin n)] :
    Fin (dK n k) → MvPolynomial (Fin n) ℝ := fun j => hbPoly n k j

variable {n : ℕ} [Nonempty (Fin n)]

lemma Yfam_mem' (k : ℕ) (j : Fin (dK n k)) :
    Yfam n k j ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k := hbPoly_mem j

lemma Yfam_lap' (k : ℕ) (j : Fin (dK n k)) :
    (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i (Yfam n k j))) = 0 := hbPoly_lap j

lemma Yfam_orth' (k : ℕ) (i j : Fin (dK n k)) :
    (∫ θ : ctSph n, polyFun (Yfam n k i) θ * polyFun (Yfam n k j) θ ∂volume.toSphere)
      = if i = j then (1 : ℝ) else 0 := hbPoly_orth i j

lemma Yfam_L2' (k : ℕ) (j : Fin (dK n k)) :
    (∫ θ : ctSph n, (polyFun (Yfam n k j) θ)^2 ∂volume.toSphere) = 1 := by
  have h := Yfam_orth' (n := n) k j j
  rw [if_pos rfl] at h
  simpa only [pow_two] using h

lemma Yfam_span' (k : ℕ) (H : MvPolynomial (Fin n) ℝ)
    (hH : H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlap : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0) :
    ∃ c : Fin (dK n k) → ℝ,
      ∀ θ : ctSph n, polyFun H θ = ∑ j : Fin (dK n k), c j * polyFun (Yfam n k j) θ :=
  hbPoly_span H hH hlap

lemma polyFun_odd {n k : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) (hk : Odd k) :
    ∀ θ : ctSph n, polyFun P (reflSphere θ) = - polyFun P θ := by
  intro θ
  rw [polyFun_refl P hP θ, hk.neg_one_pow]
  ring

lemma polyFun_even {n k : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) (hk : Even k) :
    ∀ θ : ctSph n, polyFun P (reflSphere θ) = polyFun P θ := by
  intro θ
  rw [polyFun_refl P hP θ, hk.neg_one_pow, one_mul]

/-- Pairing of two basis elements (different degrees). -/
lemma Yfam_pair_ne {n : ℕ} [Nonempty (Fin n)] {k l : ℕ} (hkl : k ≠ l)
    (i : Fin (dK n k)) (j : Fin (dK n l)) :
    (∫ θ : ctSph n, polyFun (Yfam n k i) θ * polyFun (Yfam n l j) θ ∂volume.toSphere) = 0 :=
  Commons.Analysis.MeasureTheory.harmonic_cross_degree_orthogonal hkl (Yfam n k i) (Yfam n l j)
    (Yfam_mem' k i) (Yfam_mem' l j) (Yfam_lap' k i) (Yfam_lap' l j)

/-- `dK n 0 ≤ 1`. -/
lemma dK_zero_le_one (n : ℕ) [Nonempty (Fin n)] : (dK n 0 : ℝ) ≤ 1 := by
  haveI : Module.Finite ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ 0) :=
    Commons.Algebra.MvPolynomial.homogeneousSubmodule_finiteDimensional
  haveI : Module.Finite ℝ (Commons.Algebra.MvPolynomial.harmHom n 0) :=
    Submodule.finiteDimensional_of_le
      (S₁ := Commons.Algebra.MvPolynomial.harmHom n 0)
      (S₂ := MvPolynomial.homogeneousSubmodule (Fin n) ℝ 0) inf_le_left
  have hle : Module.finrank ℝ (Commons.Algebra.MvPolynomial.harmHom n 0)
      ≤ Module.finrank ℝ (MvPolynomial.homogeneousSubmodule (Fin n) ℝ 0) :=
    Submodule.finrank_mono inf_le_left
  rw [Commons.Algebra.MvPolynomial.finrank_homogeneousSubmodule] at hle
  have h1 : (n + 0 - 1).choose 0 = 1 := Nat.choose_zero_right _
  rw [h1] at hle
  exact_mod_cast hle

end Main

section Bounds

noncomputable def blkA {n : ℕ} [Nonempty (Fin n)]
    (cc : (m : ℕ) → Fin (dK n (2*m)) → ℝ) (m : ℕ) : ctSph n → ℝ :=
  fun θ => ∑ j : Fin (dK n (2*m)), cc m j * polyFun (Yfam n (2*m) j) θ

noncomputable def blkG {n : ℕ} [Nonempty (Fin n)]
    (cc : (m : ℕ) → Fin (dK n (2*m)) → ℝ) (lam : ℕ → ℝ) (m : ℕ) : ctSph n → ℝ :=
  fun θ => ∑ j : Fin (dK n (2*m)), (cc m j / lam m) * polyFun (Yfam n (2*m) j) θ

lemma zpow_neg_le_neg_of_le {a b : ℝ} {k : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-(k:ℤ)) ≤ a ^ (-(k:ℤ)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hak : (0:ℝ) < a ^ k := pow_pos ha k
  have hbk : (0:ℝ) < b ^ k := pow_pos hb k
  have hle : a ^ k ≤ b ^ k := pow_le_pow_left₀ (le_of_lt ha) hab k
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  exact (inv_le_inv₀ hbk hak).mpr hle

end Bounds


section Bounds2

lemma blkG_bound {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {cc : (m : ℕ) → Fin (dK n (2*m)) → ℝ} (lam : ℕ → ℝ) {K : ℕ}
    {Cc CLam Csup Cdim : ℝ}
    (hCc : ∀ (m : ℕ) (j : Fin (dK n (2*m))),
      |cc m j| ≤ Cc * ((((2*m : ℕ) : ℝ) + 1) ^ (-(((K + 2*n : ℕ) : ℤ)))))
    (hinv : ∀ m : ℕ, |(lam m)⁻¹| ≤ CLam * (((m:ℝ)+1) ^ ((K:ℤ))))
    (hsup : ∀ (k : ℕ) (j : Fin (dK n k)) (θ : ctSph n),
      |polyFun (Yfam n k j) θ| ≤ Csup * ((((k:ℝ)+1)) ^ ((n:ℤ))))
    (hdim : ∀ k : ℕ, 2 ≤ k → (dK n k : ℝ) ≤ Cdim * ((((k:ℝ)+1)) ^ (((n-2:ℕ):ℤ))))
    (hCc0 : 0 ≤ Cc) (hCL : 0 ≤ CLam) (hSu : 0 ≤ Csup) (hCd : 0 ≤ Cdim)
    (m : ℕ) (θ : ctSph n) :
    ‖blkG cc lam m θ‖ ≤ (Cc*CLam*Csup*Cdim*(2:ℝ)^(n-2) + Cc*CLam*Csup + 1)
      * (((m:ℝ)+1) ^ (-(2:ℤ))) := by
  set X : ℝ := ((2*m : ℕ) : ℝ) + 1 with hX
  set Y : ℝ := (m:ℝ) + 1 with hY
  have hYpos : 0 < Y := by rw [hY]; positivity
  have hXpos : 0 < X := by rw [hX]; positivity
  have hXY : Y ≤ X := by rw [hX, hY]; push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
  have hYne : Y ≠ 0 := ne_of_gt hYpos
  have hXne : X ≠ 0 := ne_of_gt hXpos
  have hXcomb : X ^ (-(((K + 2*n : ℕ) : ℤ))) * X ^ ((n:ℤ)) = X ^ (-(((K + n : ℕ) : ℤ))) := by
    rw [← zpow_add₀ hXne]
    congr 1
    push_cast
    ring
  have hYcomb : Y ^ (-(((K + n : ℕ) : ℤ))) * Y ^ ((K:ℤ)) = Y ^ (-(n:ℤ)) := by
    rw [← zpow_add₀ hYne]
    congr 1
    push_cast
    ring
  have hterm : ∀ j : Fin (dK n (2*m)),
      ‖(cc m j / lam m) * polyFun (Yfam n (2*m) j) θ‖ ≤ Cc * CLam * Csup * Y ^ (-(n:ℤ)) := by
    intro j
    have h1 := hCc m j
    have h2 := hinv m
    have h3 := hsup (2*m) j θ
    have h3' : |polyFun (Yfam n (2*m) j) θ| ≤ Csup * X ^ ((n:ℤ)) := by simpa only [hX] using h3
    have h1' : |cc m j| ≤ Cc * X ^ (-(((K + 2*n : ℕ) : ℤ))) := by simpa only [hX] using h1
    have h2' : |(lam m)⁻¹| ≤ CLam * Y ^ ((K:ℤ)) := by simpa only [hY] using h2
    have hCcXnn : (0:ℝ) ≤ Cc * X ^ (-(((K + 2*n : ℕ) : ℤ))) :=
      mul_nonneg hCc0 (zpow_nonneg (le_of_lt hXpos) _)
    have hCLYnn : (0:ℝ) ≤ CLam * Y ^ ((K:ℤ)) := mul_nonneg hCL (zpow_nonneg (le_of_lt hYpos) _)
    calc ‖(cc m j / lam m) * polyFun (Yfam n (2*m) j) θ‖
        = |cc m j| * |(lam m)⁻¹| * |polyFun (Yfam n (2*m) j) θ| := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, div_eq_mul_inv, abs_mul]
      _ ≤ (Cc * X ^ (-(((K + 2*n : ℕ) : ℤ)))) * (CLam * Y ^ ((K:ℤ)))
            * (Csup * X ^ ((n:ℤ))) := by
          apply mul_le_mul
          · exact mul_le_mul h1' h2' (abs_nonneg _) hCcXnn
          · exact h3'
          · exact abs_nonneg _
          · exact mul_nonneg hCcXnn hCLYnn
      _ = Cc * CLam * Csup * (X ^ (-(((K + 2*n : ℕ) : ℤ))) * X ^ ((n:ℤ))) * Y ^ ((K:ℤ)) := by
          ring
      _ = Cc * CLam * Csup * X ^ (-(((K + n : ℕ) : ℤ))) * Y ^ ((K:ℤ)) := by rw [hXcomb]
      _ ≤ Cc * CLam * Csup * Y ^ (-(((K + n : ℕ) : ℤ))) * Y ^ ((K:ℤ)) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left
            · exact zpow_neg_le_neg_of_le hYpos hXY
            · exact mul_nonneg (mul_nonneg hCc0 hCL) hSu
          · exact zpow_nonneg (le_of_lt hYpos) _
      _ = Cc * CLam * Csup * (Y ^ (-(((K + n : ℕ) : ℤ))) * Y ^ ((K:ℤ))) := by ring
      _ = Cc * CLam * Csup * Y ^ (-(n:ℤ)) := by rw [hYcomb]
  have hsum : ‖blkG cc lam m θ‖ ≤ (dK n (2*m) : ℝ) * (Cc * CLam * Csup * Y ^ (-(n:ℤ))) := by
    rw [blkG]
    calc ‖∑ j : Fin (dK n (2*m)), (cc m j / lam m) * polyFun (Yfam n (2*m) j) θ‖
        ≤ ∑ j : Fin (dK n (2*m)), ‖(cc m j / lam m) * polyFun (Yfam n (2*m) j) θ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin (dK n (2*m)), Cc * CLam * Csup * Y ^ (-(n:ℤ)) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = (dK n (2*m) : ℝ) * (Cc * CLam * Csup * Y ^ (-(n:ℤ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hY2nn : (0:ℝ) ≤ Y ^ (-(n:ℤ)) := zpow_nonneg (le_of_lt hYpos) _
  have hCcCLCS : (0:ℝ) ≤ Cc * CLam * Csup := mul_nonneg (mul_nonneg hCc0 hCL) hSu
  have hpow2nn : (0:ℝ) ≤ Cc*CLam*Csup*Cdim*(2:ℝ)^(n-2) := by
    have hA : (0:ℝ) ≤ Cc*CLam*Csup*Cdim := mul_nonneg hCcCLCS hCd
    exact mul_nonneg hA (pow_nonneg (by norm_num) _)
  by_cases hm : m = 0
  · subst hm
    have hd0 : (dK n (2*0) : ℝ) ≤ 1 := by simpa using dK_zero_le_one n
    have hYeq : Y = 1 := by rw [hY]; norm_num
    have hYm : Y ^ (-(n:ℤ)) = 1 := by rw [hYeq, one_zpow]
    have hY2 : Y ^ (-(2:ℤ)) = 1 := by rw [hYeq, one_zpow]
    rw [hYm, mul_one] at hsum
    rw [hY2, mul_one]
    refine le_trans hsum ?_
    have hstep : (dK n (2*0) : ℝ) * (Cc*CLam*Csup) ≤ Cc*CLam*Csup := by
      have h := mul_le_mul_of_nonneg_right hd0 hCcCLCS
      rwa [one_mul] at h
    have hfin : Cc*CLam*Csup ≤ Cc*CLam*Csup*Cdim*(2:ℝ)^(n-2) + Cc*CLam*Csup + 1 := by
      linarith
    exact le_trans hstep hfin
  · have hdim2 : 2 ≤ 2*m := by omega
    have hd := hdim (2*m) hdim2
    have hd' : (dK n (2*m) : ℝ) ≤ Cdim * X ^ (((n-2:ℕ):ℤ)) := by simpa only [hX] using hd
    have hX2Y : X ≤ 2 * Y := by rw [hX, hY]; push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    have hXle : X ^ (((n-2:ℕ):ℤ)) ≤ (2*Y) ^ (((n-2:ℕ):ℤ)) :=
      zpow_le_zpow_left₀ (by positivity) (le_of_lt hXpos) hX2Y
    have hmul : (2*Y) ^ (((n-2:ℕ):ℤ)) = (2:ℝ)^(((n-2:ℕ):ℤ)) * Y ^ (((n-2:ℕ):ℤ)) := by
      rw [mul_zpow]
    have hpowcast : (2:ℝ)^(((n-2:ℕ):ℤ)) = (2:ℝ)^(n-2) := zpow_natCast _ _
    have hYcomb2 : Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ)) = Y ^ (-(2:ℤ)) := by
      rw [← zpow_add₀ hYne]
      congr 1
      push_cast
      omega
    have hXle' : X ^ (((n-2:ℕ):ℤ)) ≤ (2:ℝ)^(n-2) * Y ^ (((n-2:ℕ):ℤ)) := by
      rw [← hpowcast]
      rw [hmul] at hXle
      exact hXle
    have hmain : X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ))
        ≤ (2:ℝ)^(n-2) * (Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ))) := by
      calc X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ))
          ≤ ((2:ℝ)^(n-2) * Y ^ (((n-2:ℕ):ℤ))) * Y ^ (-(n:ℤ)) :=
            mul_le_mul_of_nonneg_right hXle' hY2nn
        _ = (2:ℝ)^(n-2) * (Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ))) := by ring
    have hkey : Cc * CLam * Csup * Cdim * (X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ)))
        ≤ Cc * CLam * Csup * Cdim * (2:ℝ)^(n-2) * Y ^ (-(2:ℤ)) := by
      calc Cc * CLam * Csup * Cdim * (X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ)))
          ≤ Cc * CLam * Csup * Cdim
              * ((2:ℝ)^(n-2) * (Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ)))) :=
            mul_le_mul_of_nonneg_left hmain (mul_nonneg hCcCLCS hCd)
        _ = Cc * CLam * Csup * Cdim * (2:ℝ)^(n-2) * (Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ))) := by ring
        _ = Cc * CLam * Csup * Cdim * (2:ℝ)^(n-2) * Y ^ (-(2:ℤ)) := by rw [hYcomb2]
    calc ‖blkG cc lam m θ‖
        ≤ (dK n (2*m) : ℝ) * (Cc * CLam * Csup * Y ^ (-(n:ℤ))) := hsum
      _ ≤ (Cdim * X ^ (((n-2:ℕ):ℤ))) * (Cc * CLam * Csup * Y ^ (-(n:ℤ))) :=
          mul_le_mul_of_nonneg_right hd' (mul_nonneg hCcCLCS hY2nn)
      _ = Cc * CLam * Csup * Cdim * (X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(n:ℤ))) := by ring
      _ ≤ Cc * CLam * Csup * Cdim * (2:ℝ)^(n-2) * Y ^ (-(2:ℤ)) := hkey
      _ ≤ (Cc*CLam*Csup*Cdim*(2:ℝ)^(n-2) + Cc*CLam*Csup + 1) * Y ^ (-(2:ℤ)) := by
          apply mul_le_mul_of_nonneg_right ?_ (zpow_nonneg (le_of_lt hYpos) _)
          linarith [hpow2nn]

end Bounds2

section Tools

lemma integrable_of_continuous_finiteMeasure {α : Type*} [TopologicalSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := α)).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC x (mem_univ x)))

lemma summable_shift_zpow : Summable (fun m : ℕ => (((m:ℝ)+1) ^ (-(2:ℤ)))) := by
  have h1 : Summable (fun n : ℕ => ((n:ℝ) ^ (2:ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have h2 : Summable (fun m : ℕ => ((((m+1 : ℕ) : ℝ)) ^ (2:ℝ))⁻¹) :=
    (summable_nat_add_iff 1).mpr h1
  refine h2.congr (fun m => ?_)
  simp [zpow_neg]

lemma blkA_bound {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {cc : (m : ℕ) → Fin (dK n (2*m)) → ℝ} {K : ℕ}
    {Cc Csup Cdim : ℝ}
    (hCc : ∀ (m : ℕ) (j : Fin (dK n (2*m))),
      |cc m j| ≤ Cc * ((((2*m : ℕ) : ℝ) + 1) ^ (-(((K + 2*n : ℕ) : ℤ)))))
    (hsup : ∀ (k : ℕ) (j : Fin (dK n k)) (θ : ctSph n),
      |polyFun (Yfam n k j) θ| ≤ Csup * ((((k:ℝ)+1)) ^ ((n:ℤ))))
    (hdim : ∀ k : ℕ, 2 ≤ k → (dK n k : ℝ) ≤ Cdim * ((((k:ℝ)+1)) ^ (((n-2:ℕ):ℤ))))
    (hCc0 : 0 ≤ Cc) (hSu : 0 ≤ Csup) (hCd : 0 ≤ Cdim)
    (m : ℕ) (θ : ctSph n) :
    ‖blkA cc m θ‖ ≤ (Cc*Csup*Cdim*(2:ℝ)^(n-2) + Cc*Csup + 1)
      * (((m:ℝ)+1) ^ (-(2:ℤ))) := by
  set X : ℝ := ((2*m : ℕ) : ℝ) + 1 with hX
  set Y : ℝ := (m:ℝ) + 1 with hY
  have hYpos : 0 < Y := by rw [hY]; positivity
  have hXpos : 0 < X := by rw [hX]; positivity
  have hXY : Y ≤ X := by rw [hX, hY]; push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
  have hYne : Y ≠ 0 := ne_of_gt hYpos
  have hXne : X ≠ 0 := ne_of_gt hXpos
  have hXcomb : X ^ (-(((K + 2*n : ℕ) : ℤ))) * X ^ ((n:ℤ)) = X ^ (-(((K + n : ℕ) : ℤ))) := by
    rw [← zpow_add₀ hXne]
    congr 1
    push_cast
    ring
  have hterm : ∀ j : Fin (dK n (2*m)), ‖cc m j * polyFun (Yfam n (2*m) j) θ‖
      ≤ Cc * Csup * Y ^ (-(((K+n:ℕ)):ℤ)) := by
    intro j
    have h1 := hCc m j
    have h3 := hsup (2*m) j θ
    have h3' : |polyFun (Yfam n (2*m) j) θ| ≤ Csup * X ^ ((n:ℤ)) := by simpa only [hX] using h3
    have h1' : |cc m j| ≤ Cc * X ^ (-(((K + 2*n : ℕ) : ℤ))) := by simpa only [hX] using h1
    have hCcXnn : (0:ℝ) ≤ Cc * X ^ (-(((K + 2*n : ℕ) : ℤ))) :=
      mul_nonneg hCc0 (zpow_nonneg (le_of_lt hXpos) _)
    calc ‖cc m j * polyFun (Yfam n (2*m) j) θ‖
        = |cc m j| * |polyFun (Yfam n (2*m) j) θ| := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (Cc * X ^ (-(((K + 2*n : ℕ) : ℤ)))) * (Csup * X ^ ((n:ℤ))) :=
          mul_le_mul h1' h3' (abs_nonneg _) hCcXnn
      _ = Cc * Csup * (X ^ (-(((K + 2*n : ℕ) : ℤ))) * X ^ ((n:ℤ))) := by ring
      _ = Cc * Csup * X ^ (-(((K + n : ℕ) : ℤ))) := by rw [hXcomb]
      _ ≤ Cc * Csup * Y ^ (-(((K + n : ℕ) : ℤ))) := by
          apply mul_le_mul_of_nonneg_left
          · exact zpow_neg_le_neg_of_le hYpos hXY
          · exact mul_nonneg hCc0 hSu
  have hsum : ‖blkA cc m θ‖ ≤ (dK n (2*m) : ℝ) * (Cc * Csup * Y ^ (-(((K+n:ℕ)):ℤ))) := by
    rw [blkA]
    calc ‖∑ j : Fin (dK n (2*m)), cc m j * polyFun (Yfam n (2*m) j) θ‖
        ≤ ∑ j : Fin (dK n (2*m)), ‖cc m j * polyFun (Yfam n (2*m) j) θ‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin (dK n (2*m)), Cc * Csup * Y ^ (-(((K+n:ℕ)):ℤ)) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = (dK n (2*m) : ℝ) * (Cc * Csup * Y ^ (-(((K+n:ℕ)):ℤ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hSynn : (0:ℝ) ≤ Y ^ (-(((K+n:ℕ)):ℤ)) := zpow_nonneg (le_of_lt hYpos) _
  have hCcCS : (0:ℝ) ≤ Cc * Csup := mul_nonneg hCc0 hSu
  by_cases hm : m = 0
  · subst hm
    have hd0 : (dK n (2*0) : ℝ) ≤ 1 := by simpa using dK_zero_le_one n
    have hYeq : Y = 1 := by rw [hY]; norm_num
    have hYS : Y ^ (-(((K+n:ℕ)):ℤ)) = 1 := by rw [hYeq, one_zpow]
    have hY2 : Y ^ (-(2:ℤ)) = 1 := by rw [hYeq, one_zpow]
    rw [hYS, mul_one] at hsum
    rw [hY2, mul_one]
    refine le_trans hsum ?_
    have hstep : (dK n (2*0) : ℝ) * (Cc*Csup) ≤ Cc*Csup := by
      have h := mul_le_mul_of_nonneg_right hd0 hCcCS
      rwa [one_mul] at h
    have hfin : Cc*Csup ≤ Cc*Csup*Cdim*(2:ℝ)^(n-2) + Cc*Csup + 1 := by
      have h0 : (0:ℝ) ≤ Cc*Csup*Cdim*(2:ℝ)^(n-2) :=
        mul_nonneg (mul_nonneg hCcCS hCd) (pow_nonneg (by norm_num) _)
      linarith
    exact le_trans hstep hfin
  · have hdim2 : 2 ≤ 2*m := by omega
    have hd := hdim (2*m) hdim2
    have hd' : (dK n (2*m) : ℝ) ≤ Cdim * X ^ (((n-2:ℕ):ℤ)) := by simpa only [hX] using hd
    have hX2Y : X ≤ 2 * Y := by rw [hX, hY]; push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
    have hXle : X ^ (((n-2:ℕ):ℤ)) ≤ (2*Y) ^ (((n-2:ℕ):ℤ)) :=
      zpow_le_zpow_left₀ (by positivity) (le_of_lt hXpos) hX2Y
    have hmul : (2*Y) ^ (((n-2:ℕ):ℤ)) = (2:ℝ)^(((n-2:ℕ):ℤ)) * Y ^ (((n-2:ℕ):ℤ)) := by
      rw [mul_zpow]
    have hpowcast : (2:ℝ)^(((n-2:ℕ):ℤ)) = (2:ℝ)^(n-2) := zpow_natCast _ _
    have hYcomb2 : Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ)) = Y ^ (-(((K+2:ℕ)):ℤ)) := by
      rw [← zpow_add₀ hYne]
      congr 1
      push_cast
      omega
    have hXle' : X ^ (((n-2:ℕ):ℤ)) ≤ (2:ℝ)^(n-2) * Y ^ (((n-2:ℕ):ℤ)) := by
      rw [← hpowcast]
      rw [hmul] at hXle
      exact hXle
    have hmain : X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ))
        ≤ (2:ℝ)^(n-2) * (Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ))) := by
      calc X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ))
          ≤ ((2:ℝ)^(n-2) * Y ^ (((n-2:ℕ):ℤ))) * Y ^ (-(((K+n:ℕ)):ℤ)) :=
            mul_le_mul_of_nonneg_right hXle' hSynn
        _ = (2:ℝ)^(n-2) * (Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ))) := by ring
    have hkey : Cc * Csup * Cdim * (X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ)))
        ≤ Cc * Csup * Cdim * (2:ℝ)^(n-2) * Y ^ (-(2:ℤ)) := by
      have hK : (2:ℕ) ≤ K + 2 := by omega
      calc Cc * Csup * Cdim * (X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ)))
          ≤ Cc * Csup * Cdim
              * ((2:ℝ)^(n-2) * (Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ)))) :=
            mul_le_mul_of_nonneg_left hmain (mul_nonneg hCcCS hCd)
        _ = Cc * Csup * Cdim * (2:ℝ)^(n-2)
              * (Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ))) := by ring
        _ ≤ Cc * Csup * Cdim * (2:ℝ)^(n-2) * Y ^ (-(2:ℤ)) := by
            have h1Y : 1 ≤ Y := by rw [hY]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
            have hYZle : Y ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ)) ≤ Y ^ (-(2:ℤ)) := by
              rw [hYcomb2]
              exact zpow_le_zpow_right₀ h1Y (by push_cast; omega)
            exact mul_le_mul_of_nonneg_left hYZle
              (mul_nonneg (mul_nonneg hCcCS hCd) (pow_nonneg (by norm_num) _))
    calc ‖blkA cc m θ‖
        ≤ (dK n (2*m) : ℝ) * (Cc * Csup * Y ^ (-(((K+n:ℕ)):ℤ))) := hsum
      _ ≤ (Cdim * X ^ (((n-2:ℕ):ℤ))) * (Cc * Csup * Y ^ (-(((K+n:ℕ)):ℤ))) :=
          mul_le_mul_of_nonneg_right hd' (mul_nonneg hCcCS hSynn)
      _ = Cc * Csup * Cdim * (X ^ (((n-2:ℕ):ℤ)) * Y ^ (-(((K+n:ℕ)):ℤ))) := by ring
      _ ≤ Cc * Csup * Cdim * (2:ℝ)^(n-2) * Y ^ (-(2:ℤ)) := hkey
      _ ≤ (Cc*Csup*Cdim*(2:ℝ)^(n-2) + Cc*Csup + 1) * Y ^ (-(2:ℤ)) := by
          apply mul_le_mul_of_nonneg_right ?_ (zpow_nonneg (le_of_lt hYpos) _)
          have h0 : (0:ℝ) ≤ Cc*Csup*Cdim*(2:ℝ)^(n-2) :=
            mul_nonneg (mul_nonneg hCcCS hCd) (pow_nonneg (by norm_num) _)
          linarith

end Tools

section MainProof

lemma integral_blkG_eq_blkA {n : ℕ} [Nonempty (Fin n)] [Nontrivial (ctE n)]
    {cc : (m : ℕ) → Fin (dK n (2*m)) → ℝ} {lam : ℕ → ℝ}
    (hlamne : ∀ m : ℕ, lam m ≠ 0)
    (hlam : ∀ (m : ℕ) (P : MvPolynomial (Fin n) ℝ),
      P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ (2*m) →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0 →
      ∀ u : ctSph n,
        (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * polyFun P θ ∂volume.toSphere)
          = lam m * polyFun P u)
    (m : ℕ) (u : ctSph n) :
    (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * blkG cc lam m θ ∂volume.toSphere)
      = blkA cc m u := by
  have hcontj : ∀ j : Fin (dK n (2*m)), Continuous (fun θ : ctSph n =>
      |inner ℝ (u : ctE n) (θ : ctE n)| * ((cc m j / lam m) * polyFun (Yfam n (2*m) j) θ)) := by
    intro j
    refine Continuous.mul ?_ (continuous_const.mul ?_)
    · exact continuous_abs.comp (continuous_const.inner continuous_subtype_val)
    · exact Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n (2*m) j)
  unfold blkG blkA
  rw [show (fun θ : ctSph n => |inner ℝ (u : ctE n) (θ : ctE n)|
        * (∑ j : Fin (dK n (2*m)), (cc m j / lam m) * polyFun (Yfam n (2*m) j) θ))
      = (fun θ : ctSph n => ∑ j : Fin (dK n (2*m)),
          |inner ℝ (u : ctE n) (θ : ctE n)| * ((cc m j / lam m) * polyFun (Yfam n (2*m) j) θ)) from by
        funext θ; rw [Finset.mul_sum]]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [show (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)|
          * ((cc m j / lam m) * polyFun (Yfam n (2*m) j) θ) ∂volume.toSphere)
        = ∫ θ : ctSph n, (cc m j / lam m)
          * (|inner ℝ (u : ctE n) (θ : ctE n)| * polyFun (Yfam n (2*m) j) θ) ∂volume.toSphere from
          MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => by ring))]
    rw [MeasureTheory.integral_const_mul,
      hlam m (Yfam n (2*m) j) (Yfam_mem' (2*m) j) (Yfam_lap' (2*m) j) u]
    field_simp [hlamne m]
  · intro j _
    exact integrable_of_continuous_finiteMeasure (hcontj j)

lemma integral_Yfam_mul_H {n : ℕ} [Nonempty (Fin n)] {k : ℕ}
    (j : Fin (dK n k)) (H : MvPolynomial (Fin n) ℝ)
    (c : Fin (dK n k) → ℝ)
    (hc : ∀ θ : ctSph n, polyFun H θ = ∑ i : Fin (dK n k), c i * polyFun (Yfam n k i) θ) :
    (∫ θ : ctSph n, polyFun (Yfam n k j) θ * polyFun H θ ∂volume.toSphere) = c j := by
  have hcontj : Continuous (fun θ : ctSph n => polyFun (Yfam n k j) θ
      * (∑ i : Fin (dK n k), c i * polyFun (Yfam n k i) θ)) := by
    refine Continuous.mul (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n k j)) ?_
    refine continuous_finsetSum _ (fun i _ => continuous_const.mul ?_)
    exact Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n k i)
  rw [show (∫ θ : ctSph n, polyFun (Yfam n k j) θ * polyFun H θ ∂volume.toSphere)
      = ∫ θ : ctSph n, polyFun (Yfam n k j) θ
          * (∑ i : Fin (dK n k), c i * polyFun (Yfam n k i) θ) ∂volume.toSphere from
        MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => by beta_reduce; rw [hc θ]))]
  rw [show (fun θ : ctSph n => polyFun (Yfam n k j) θ
        * (∑ i : Fin (dK n k), c i * polyFun (Yfam n k i) θ))
      = (fun θ : ctSph n => ∑ i : Fin (dK n k),
          c i * (polyFun (Yfam n k j) θ * polyFun (Yfam n k i) θ)) from by
        funext θ; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro i _; ring]
  rw [MeasureTheory.integral_finset_sum]
  · rw [show (∑ i : Fin (dK n k), (∫ θ : ctSph n,
          c i * (polyFun (Yfam n k j) θ * polyFun (Yfam n k i) θ) ∂volume.toSphere))
        = ∑ i : Fin (dK n k), c i * (∫ θ : ctSph n,
          polyFun (Yfam n k j) θ * polyFun (Yfam n k i) θ ∂volume.toSphere) from by
        apply Finset.sum_congr rfl; intro i _; rw [MeasureTheory.integral_const_mul]]
    rw [show (∑ i : Fin (dK n k), c i * (∫ θ : ctSph n,
          polyFun (Yfam n k j) θ * polyFun (Yfam n k i) θ ∂volume.toSphere))
        = ∑ i : Fin (dK n k), c i * (if j = i then (1:ℝ) else 0) from by
        apply Finset.sum_congr rfl; intro i _
        rw [Yfam_orth' k j i]]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [show j ≠ i from fun h => hij h.symm]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro i _
    refine integrable_of_continuous_finiteMeasure (Continuous.mul continuous_const ?_)
    exact Continuous.mul (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n k j))
      (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n k i))

end MainProof

section MainProof2

lemma integral_blkA_mul_eq_sum {n : ℕ} [Nonempty (Fin n)]
    {cc : (m : ℕ) → Fin (dK n (2*m)) → ℝ} (H : MvPolynomial (Fin n) ℝ) (m : ℕ) :
    (∫ θ : ctSph n, blkA cc m θ * polyFun H θ ∂volume.toSphere)
      = ∑ j : Fin (dK n (2*m)), cc m j
          * (∫ θ : ctSph n, polyFun (Yfam n (2*m) j) θ * polyFun H θ ∂volume.toSphere) := by
  unfold blkA
  rw [show (fun θ : ctSph n => (∑ j : Fin (dK n (2*m)), cc m j * polyFun (Yfam n (2*m) j) θ)
        * polyFun H θ)
      = (fun θ : ctSph n => ∑ j : Fin (dK n (2*m)),
          cc m j * (polyFun (Yfam n (2*m) j) θ * polyFun H θ)) from by
        funext θ; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl; intro j _
    exact MeasureTheory.integral_const_mul _ _
  · intro j _
    exact integrable_of_continuous_finiteMeasure (Continuous.mul continuous_const
      (Continuous.mul (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n (2*m) j))
        (Commons.Algebra.MvPolynomial.continuous_eval_sphere n H)))

lemma integral_Yfam_mul_H_zero {n : ℕ} [Nonempty (Fin n)] [Nontrivial (ctE n)]
    {k : ℕ} (H : MvPolynomial (Fin n) ℝ)
    (c : Fin (dK n k) → ℝ)
    (hc : ∀ θ : ctSph n, polyFun H θ = ∑ i : Fin (dK n k), c i * polyFun (Yfam n k i) θ)
    (m : ℕ) (j : Fin (dK n (2*m))) (hne : 2*m ≠ k) :
    (∫ θ : ctSph n, polyFun (Yfam n (2*m) j) θ * polyFun H θ ∂volume.toSphere) = 0 := by
  rw [show (∫ θ : ctSph n, polyFun (Yfam n (2*m) j) θ * polyFun H θ ∂volume.toSphere)
      = ∫ θ : ctSph n, polyFun (Yfam n (2*m) j) θ
          * (∑ i : Fin (dK n k), c i * polyFun (Yfam n k i) θ) ∂volume.toSphere from
        MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => by beta_reduce; rw [hc θ]))]
  rw [show (fun θ : ctSph n => polyFun (Yfam n (2*m) j) θ
        * (∑ i : Fin (dK n k), c i * polyFun (Yfam n k i) θ))
      = (fun θ : ctSph n => ∑ i : Fin (dK n k),
          c i * (polyFun (Yfam n (2*m) j) θ * polyFun (Yfam n k i) θ)) from by
        funext θ; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro i _; ring]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero; intro i _
    rw [MeasureTheory.integral_const_mul,
      Yfam_pair_ne (k := 2*m) (l := k) hne j i, mul_zero]
  · intro i _
    exact integrable_of_continuous_finiteMeasure (Continuous.mul continuous_const
      (Continuous.mul (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n (2*m) j))
        (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n k i))))

lemma integral_blkA_mul_H {n : ℕ} [Nonempty (Fin n)] [Nontrivial (ctE n)]
    {cc : (m : ℕ) → Fin (dK n (2*m)) → ℝ} {p : ctE n → ℝ} (hpe : ∀ x : ctE n, p (-x) = p x)
    (hpcont : Continuous p)
    (hcc : ∀ (m : ℕ) (j : Fin (dK n (2*m))),
      cc m j = ∫ θ : ctSph n, p (θ:ctE n) * polyFun (Yfam n (2*m) j) θ ∂volume.toSphere)
    {k : ℕ} (H : MvPolynomial (Fin n) ℝ) (hH : H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k)
    (hlap : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0)
    (M : ℕ) (hM : k < 2*M) :
    (∫ θ : ctSph n, (∑ m ∈ Finset.range M, blkA cc m θ) * polyFun H θ ∂volume.toSphere)
      = ∫ θ : ctSph n, p (θ:ctE n) * polyFun H θ ∂volume.toSphere := by
  obtain ⟨c, hc⟩ := Yfam_span' k H hH hlap
  have hpcont' : Continuous (fun θ : ctSph n => p (θ:ctE n)) := hpcont.comp continuous_subtype_val
  have hLHS : (∫ θ : ctSph n, (∑ m ∈ Finset.range M, blkA cc m θ) * polyFun H θ ∂volume.toSphere)
      = ∑ m ∈ Finset.range M,
          (∫ θ : ctSph n, blkA cc m θ * polyFun H θ ∂volume.toSphere) := by
    rw [show (fun θ : ctSph n => (∑ m ∈ Finset.range M, blkA cc m θ) * polyFun H θ)
        = (fun θ : ctSph n => ∑ m ∈ Finset.range M, blkA cc m θ * polyFun H θ) from by
          funext θ; rw [Finset.sum_mul]]
    rw [MeasureTheory.integral_finset_sum]
    · intro m _
      unfold blkA
      exact integrable_of_continuous_finiteMeasure (Continuous.mul
        (continuous_finsetSum _ (fun j _ => continuous_const.mul
          (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n (2*m) j))))
        (Commons.Algebra.MvPolynomial.continuous_eval_sphere n H))
  have hpform : (∫ θ : ctSph n, p (θ:ctE n) * polyFun H θ ∂volume.toSphere)
      = ∑ j : Fin (dK n k),
          c j * (∫ θ : ctSph n, p (θ:ctE n) * polyFun (Yfam n k j) θ ∂volume.toSphere) := by
    rw [show (∫ θ : ctSph n, p (θ:ctE n) * polyFun H θ ∂volume.toSphere)
        = ∫ θ : ctSph n, p (θ:ctE n)
            * (∑ j : Fin (dK n k), c j * polyFun (Yfam n k j) θ) ∂volume.toSphere from
          MeasureTheory.integral_congr_ae (Eventually.of_forall (fun θ => by beta_reduce; rw [hc θ]))]
    rw [show (fun θ : ctSph n => p (θ:ctE n)
          * (∑ j : Fin (dK n k), c j * polyFun (Yfam n k j) θ))
        = (fun θ : ctSph n => ∑ j : Fin (dK n k),
            c j * (p (θ:ctE n) * polyFun (Yfam n k j) θ)) from by
          funext θ; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
          intro j _; ring]
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl; intro j _
      exact MeasureTheory.integral_const_mul _ _
    · intro j _
      exact integrable_of_continuous_finiteMeasure (Continuous.mul continuous_const
        (Continuous.mul hpcont' (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n k j))))
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨m₀, hm₀⟩ := hk
    have hm₀' : k = 2*m₀ := by omega
    subst hm₀'
    have hm0M : m₀ ∈ Finset.range M := Finset.mem_range.mpr (by omega)
    have hterm0 : (∫ θ : ctSph n, blkA cc m₀ θ * polyFun H θ ∂volume.toSphere)
        = ∑ j : Fin (dK n (2*m₀)), cc m₀ j * c j := by
      rw [integral_blkA_mul_eq_sum H m₀]
      exact Finset.sum_congr rfl (fun j _ => by rw [integral_Yfam_mul_H j H c hc])
    have htermne : ∀ m : ℕ, m ≠ m₀ →
        (∫ θ : ctSph n, blkA cc m θ * polyFun H θ ∂volume.toSphere) = 0 := by
      intro m hmne
      have h2 : 2*m ≠ 2*m₀ := by omega
      rw [show (∫ θ : ctSph n, blkA cc m θ * polyFun H θ ∂volume.toSphere)
          = ∑ j : Fin (dK n (2*m)), cc m j * (0:ℝ) from by
            rw [integral_blkA_mul_eq_sum H m]
            exact Finset.sum_congr rfl (fun j _ => by
              rw [integral_Yfam_mul_H_zero H c hc m j h2, mul_zero])]
      simp
    have hsum0 : (∑ m ∈ Finset.range M, (∫ θ : ctSph n, blkA cc m θ * polyFun H θ ∂volume.toSphere))
        = ∑ j : Fin (dK n (2*m₀)), cc m₀ j * c j := by
      rw [Finset.sum_eq_single m₀]
      · exact hterm0
      · intro m _ hmne; exact htermne m hmne
      · intro hm0; exact absurd hm0M hm0
    rw [hLHS, hsum0, hpform]
    apply Finset.sum_congr rfl; intro j _
    rw [← hcc m₀ j]; ring
  · have hodd : Odd k := hk
    have h2mne : ∀ m : ℕ, 2*m ≠ k := by
      intro m h
      rw [← h] at hodd
      exact (Nat.not_odd_iff_even.mpr ⟨m, by omega⟩) hodd
    have hLzero : (∫ θ : ctSph n, (∑ m ∈ Finset.range M, blkA cc m θ) * polyFun H θ ∂volume.toSphere) = 0 := by
      rw [hLHS]
      apply Finset.sum_eq_zero; intro m _
      rw [show (∫ θ : ctSph n, blkA cc m θ * polyFun H θ ∂volume.toSphere)
          = ∑ j : Fin (dK n (2*m)), cc m j * (0:ℝ) from by
            rw [integral_blkA_mul_eq_sum H m]
            exact Finset.sum_congr rfl (fun j _ => by
              rw [integral_Yfam_mul_H_zero H c hc m j (h2mne m), mul_zero])]
      simp
    have hRzero : (∫ θ : ctSph n, p (θ:ctE n) * polyFun H θ ∂volume.toSphere) = 0 := by
      rw [hpform]
      apply Finset.sum_eq_zero; intro j _
      have hz : (∫ θ : ctSph n, (fun θ : ctSph n => p (θ:ctE n)) θ * polyFun (Yfam n k j) θ ∂volume.toSphere) = 0 :=
        Commons.Analysis.MeasureTheory.integral_even_mul_odd (ctE n)
          (fun θ => by simpa using hpe (θ : ctE n))
          (polyFun_odd (Yfam n k j) (Yfam_mem' k j) hodd)
      rw [hz, mul_zero]
    rw [hLzero, hRzero]

end MainProof2

section EuclidMain

theorem euclid_surjective {n : ℕ} (hn : 2 ≤ n)
    (p : ctE n → ℝ) (hpe : ∀ x : ctE n, p (-x) = p x)
    (hph : ∀ (a : ℝ) (x : ctE n), 0 ≤ a → p (a • x) = a * p x)
    (hpcont : Continuous p) (hps : ContDiffOn ℝ ⊤ p {x : ctE n | x ≠ 0}) :
    ∃ g : ctSph n → ℝ, Continuous g ∧ (∀ θ : ctSph n, g (reflSphere θ) = g θ) ∧
      ∀ u : ctSph n,
        (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * g θ ∂volume.toSphere) = p (u : ctE n) := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (ctE n) := inferInstance
  obtain ⟨c0, hc0pos, K, lam, hlam0ne, hlamdecay, hlameig⟩ :=
    Commons.Analysis.MeasureTheory.cosine_even_eigenvalue_decay (n := n) hn
  obtain ⟨Csup, hCsuppos, hCsup⟩ := Commons.Analysis.MeasureTheory.harmonic_sup_norm_bound (n := n)
  obtain ⟨Cc, hCc⟩ :=
    Commons.Analysis.MeasureTheory.harmonic_coeff_decay_any (n := n) (K + 2*n) p hpcont hps
  -- sup bound in zpow shape
  have hsup : ∀ (k : ℕ) (j : Fin (dK n k)) (θ : ctSph n),
      |polyFun (Yfam n k j) θ| ≤ (max Csup 1) * ((((k:ℝ)+1)) ^ ((n:ℤ))) := by
    intro k j θ
    have h1 := hCsup k (Yfam n k j) (Yfam_mem' k j) (Yfam_lap' k j) (Yfam_L2' k j) θ
    have hbase : (1:ℝ) ≤ (k:ℝ)+1 := by linarith [show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k]
    have hexp : ((n:ℝ)-2)/2 ≤ ((n:ℤ) : ℝ) := by
      have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      simp only [Int.cast_natCast]
      linarith
    calc |polyFun (Yfam n k j) θ| ≤ Csup * (((k:ℝ)+1) ^ (((n:ℝ)-2)/2)) := h1
      _ ≤ Csup * (((k:ℝ)+1) ^ ((n:ℤ))) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCsuppos)
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ ≤ (max Csup 1) * (((k:ℝ)+1) ^ ((n:ℤ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _)
            (zpow_nonneg (by positivity) _)
  have hcd : ∀ (m : ℕ) (j : Fin (dK n (2*m))),
      |(∫ θ : ctSph n, p (θ:ctE n) * polyFun (Yfam n (2*m) j) θ ∂volume.toSphere)|
        ≤ Cc * ((((2*m : ℕ) : ℝ) + 1) ^ (-(((K + 2*n : ℕ) : ℤ)))) := by
    intro m j
    exact hCc (2*m) (Yfam n (2*m) j) (Yfam_mem' (2*m) j) (Yfam_lap' (2*m) j)
      (Yfam_L2' (2*m) j)
  -- dimension bound
  have hdim : ∀ (k : ℕ), 2 ≤ k →
      (dK n k : ℝ) ≤ (2 * (n:ℝ)^(n-2)) * ((((k:ℝ)+1)) ^ (((n-2:ℕ):ℤ))) := by
    intro k hk
    have h1 := Commons.Algebra.MvPolynomial.harmHom_finrank_le (n := n) (k := k) hn hk
    rw [zpow_natCast]
    exact h1
  -- lam ≠ 0
  have hlamne : ∀ m : ℕ, lam m ≠ 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; exact hlam0ne
    · intro h0
      have h1 := hlamdecay m hm
      rw [h0, abs_zero] at h1
      have h2 : 0 < (m:ℝ) ^ (-(K:ℤ)) := zpow_pos (by exact_mod_cast hm) _
      nlinarith [hc0pos, h2]
  -- the inverse of lam
  let CLam : ℝ := max ((|lam 0|)⁻¹) (c0⁻¹)
  have hCLamnn : 0 ≤ CLam := by
    refine le_trans ?_ (le_max_left _ _)
    exact inv_nonneg.mpr (abs_nonneg _)
  have hCLamc0 : c0⁻¹ ≤ CLam := le_max_right _ _
  have hinv : ∀ m : ℕ, |(lam m)⁻¹| ≤ CLam * (((m:ℝ)+1) ^ ((K:ℤ))) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have hstep : |(lam 0)⁻¹| ≤ CLam := by
        rw [abs_inv]
        exact le_max_left _ _
      rw [show ((0:ℕ):ℝ) + 1 = (1:ℝ) from by norm_num, one_zpow, mul_one]
      exact hstep
    · have h1 := hlamdecay m hm
      have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      have h2 : (0:ℝ) < c0 * (m:ℝ) ^ (-(K:ℤ)) := mul_pos hc0pos (zpow_pos hmR _)
      have h3 : (|lam m|)⁻¹ ≤ (c0 * (m:ℝ) ^ (-(K:ℤ)))⁻¹ :=
        (inv_le_inv₀ (abs_pos.mpr (hlamne m)) h2).mpr h1
      have h4 : (c0 * (m:ℝ) ^ (-(K:ℤ)))⁻¹ = c0⁻¹ * (m:ℝ) ^ (K:ℤ) := by
        rw [mul_inv, ← zpow_neg, neg_neg]
      have h5 : |(lam m)⁻¹| = (|lam m|)⁻¹ := abs_inv _
      rw [h5]
      calc (|lam m|)⁻¹ ≤ (c0 * (m:ℝ) ^ (-(K:ℤ)))⁻¹ := h3
        _ = c0⁻¹ * (m:ℝ) ^ (K:ℤ) := h4
        _ ≤ CLam * (m:ℝ) ^ (K:ℤ) :=
            mul_le_mul_of_nonneg_right hCLamc0 (zpow_nonneg (le_of_lt hmR) _)
        _ ≤ CLam * ((m:ℝ)+1) ^ ((K:ℤ)) :=
            mul_le_mul_of_nonneg_left
              (zpow_le_zpow_left₀ (by positivity) (le_of_lt hmR) (by linarith)) hCLamnn
  -- rescaled constants
  let Cc' : ℝ := max Cc 0
  have hCc'nn : 0 ≤ Cc' := le_max_right _ _
  have hcd' : ∀ (m : ℕ) (j : Fin (dK n (2*m))),
      |(∫ θ : ctSph n, p (θ:ctE n) * polyFun (Yfam n (2*m) j) θ ∂volume.toSphere)|
        ≤ Cc' * ((((2*m : ℕ) : ℝ) + 1) ^ (-(((K + 2*n : ℕ) : ℤ)))) := by
    intro m j
    refine le_trans (hcd m j) ?_
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    exact zpow_nonneg (by positivity) _
  let Csup' : ℝ := max Csup 1
  have hCsup'pos : 0 < Csup' := lt_of_lt_of_le hCsuppos (le_max_left _ _)
  have hCsup'nn : 0 ≤ Csup' := le_of_lt hCsup'pos
  have hsup' : ∀ (k : ℕ) (j : Fin (dK n k)) (θ : ctSph n),
      |polyFun (Yfam n k j) θ| ≤ Csup' * ((((k:ℝ)+1)) ^ ((n:ℤ))) := hsup
  let Cdim : ℝ := 2 * (n:ℝ)^(n-2)
  let Cdim' : ℝ := max Cdim 0
  have hCdim'nn : 0 ≤ Cdim' := le_max_right _ _
  have hdim' : ∀ (k : ℕ), 2 ≤ k →
      (dK n k : ℝ) ≤ Cdim' * ((((k:ℝ)+1)) ^ (((n-2:ℕ):ℤ))) := by
    intro k hk
    refine le_trans (hdim k hk) ?_
    apply mul_le_mul_of_nonneg_right (le_max_left _ _)
    exact zpow_nonneg (by positivity) _
  -- the coefficient functional
  let cc : (m : ℕ) → Fin (dK n (2*m)) → ℝ :=
    fun m j => ∫ θ : ctSph n, p (θ:ctE n) * polyFun (Yfam n (2*m) j) θ ∂volume.toSphere
  have hcc : ∀ (m : ℕ) (j : Fin (dK n (2*m))),
      cc m j = ∫ θ : ctSph n, p (θ:ctE n) * polyFun (Yfam n (2*m) j) θ ∂volume.toSphere :=
    fun m j => rfl
  have hcd'' : ∀ (m : ℕ) (j : Fin (dK n (2*m))),
      |cc m j| ≤ Cc' * ((((2*m : ℕ) : ℝ) + 1) ^ (-(((K + 2*n : ℕ) : ℤ)))) := hcd'
  -- majorant constants
  let BG : ℝ := Cc'*CLam*Csup'*Cdim'*(2:ℝ)^(n-2) + Cc'*CLam*Csup' + 1
  let BA : ℝ := Cc'*Csup'*Cdim'*(2:ℝ)^(n-2) + Cc'*Csup' + 1
  have hblkG : ∀ (m : ℕ) (θ : ctSph n), ‖blkG cc lam m θ‖ ≤ BG * (((m:ℝ)+1) ^ (-(2:ℤ))) :=
    fun m θ => blkG_bound hn lam hcd'' hinv hsup' hdim' hCc'nn hCLamnn hCsup'nn hCdim'nn m θ
  have hblkA : ∀ (m : ℕ) (θ : ctSph n), ‖blkA cc m θ‖ ≤ BA * (((m:ℝ)+1) ^ (-(2:ℤ))) :=
    fun m θ => blkA_bound hn hcd'' hsup' hdim' hCc'nn hCsup'nn hCdim'nn m θ
  have hsumG : Summable (fun m : ℕ => BG * (((m:ℝ)+1) ^ (-(2:ℤ)))) :=
    summable_shift_zpow.mul_left BG
  have hsumA : Summable (fun m : ℕ => BA * (((m:ℝ)+1) ^ (-(2:ℤ)))) :=
    summable_shift_zpow.mul_left BA
  -- series
  let G : ctSph n → ℝ := fun θ => ∑' m, blkG cc lam m θ
  let A : ctSph n → ℝ := fun θ => ∑' m, blkA cc m θ
  have hHasG : HasSumUniformlyOn (fun m : ℕ => blkG cc lam m) G Set.univ :=
    HasSumUniformlyOn.of_norm_le_summable hsumG (fun m θ _ => hblkG m θ)
  have hHasA : HasSumUniformlyOn (fun m : ℕ => blkA cc m) A Set.univ :=
    HasSumUniformlyOn.of_norm_le_summable hsumA (fun m θ _ => hblkA m θ)
  have hblkGcont : ∀ m : ℕ, Continuous (blkG cc lam m) := by
    intro m
    show Continuous (fun θ : ctSph n => ∑ j : Fin (dK n (2*m)),
      (cc m j / lam m) * polyFun (Yfam n (2*m) j) θ)
    exact continuous_finsetSum Finset.univ (fun j _ => continuous_const.mul
      (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n (2*m) j)))
  have hblkAcont : ∀ m : ℕ, Continuous (blkA cc m) := by
    intro m
    show Continuous (fun θ : ctSph n => ∑ j : Fin (dK n (2*m)),
      cc m j * polyFun (Yfam n (2*m) j) θ)
    exact continuous_finsetSum Finset.univ (fun j _ => continuous_const.mul
      (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Yfam n (2*m) j)))
  have hTuG : TendstoUniformly
      (fun M : ℕ => fun θ : ctSph n => ∑ m ∈ Finset.range M, blkG cc lam m θ) G atTop :=
    tendstoUniformly_tsum_nat hsumG (fun m θ => hblkG m θ)
  have hTuA : TendstoUniformly
      (fun M : ℕ => fun θ : ctSph n => ∑ m ∈ Finset.range M, blkA cc m θ) A atTop :=
    tendstoUniformly_tsum_nat hsumA (fun m θ => hblkA m θ)
  have hGcont : Continuous G := hTuG.continuous
    (Eventually.of_forall (fun M => continuous_finsetSum (Finset.range M)
      (fun m _ => hblkGcont m))).frequently
  have hAcont : Continuous A := hTuA.continuous
    (Eventually.of_forall (fun M => continuous_finsetSum (Finset.range M)
      (fun m _ => hblkAcont m))).frequently
  have hblkGeven : ∀ (m : ℕ) (θ : ctSph n), blkG cc lam m (reflSphere θ) = blkG cc lam m θ := by
    intro m θ
    show (∑ j : Fin (dK n (2*m)), (cc m j / lam m) * polyFun (Yfam n (2*m) j) (reflSphere θ))
        = ∑ j : Fin (dK n (2*m)), (cc m j / lam m) * polyFun (Yfam n (2*m) j) θ
    exact Finset.sum_congr rfl (fun j _ => by
      rw [polyFun_even (Yfam n (2*m) j) (Yfam_mem' (2*m) j) ⟨m, by omega⟩])
  have hGeven : ∀ θ : ctSph n, G (reflSphere θ) = G θ := by
    intro θ
    show (∑' m, blkG cc lam m (reflSphere θ)) = ∑' m, blkG cc lam m θ
    exact tsum_congr (fun m => hblkGeven m θ)
  refine ⟨G, hGcont, hGeven, fun u => ?_⟩
  -- T of the blocks
  have hTG : ∀ m : ℕ, ∀ u : ctSph n,
      (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * blkG cc lam m θ ∂volume.toSphere)
        = blkA cc m u := fun m u => integral_blkG_eq_blkA hlamne hlameig m u
  -- A is even
  have hblkAeven : ∀ (m : ℕ) (θ : ctSph n), blkA cc m (reflSphere θ) = blkA cc m θ := by
    intro m θ
    show (∑ j : Fin (dK n (2*m)), cc m j * polyFun (Yfam n (2*m) j) (reflSphere θ))
        = ∑ j : Fin (dK n (2*m)), cc m j * polyFun (Yfam n (2*m) j) θ
    exact Finset.sum_congr rfl (fun j _ => by
      rw [polyFun_even (Yfam n (2*m) j) (Yfam_mem' (2*m) j) ⟨m, by omega⟩])
  have hAeven : ∀ θ : ctSph n, A (reflSphere θ) = A θ := by
    intro θ
    show (∑' m, blkA cc m (reflSphere θ)) = ∑' m, blkA cc m θ
    exact tsum_congr (fun m => hblkAeven m θ)
  -- T of the blocks
  have hTG : ∀ m : ℕ, ∀ u : ctSph n,
      (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * blkG cc lam m θ ∂volume.toSphere)
        = blkA cc m u := fun m u => integral_blkG_eq_blkA hlamne hlameig m u
  have hTGM : ∀ M : ℕ, ∀ u : ctSph n,
      (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)|
          * (∑ m ∈ Finset.range M, blkG cc lam m θ) ∂volume.toSphere)
        = ∑ m ∈ Finset.range M, blkA cc m u := by
    intro M u
    rw [show (fun θ : ctSph n => |inner ℝ (u : ctE n) (θ : ctE n)|
          * (∑ m ∈ Finset.range M, blkG cc lam m θ))
        = (fun θ : ctSph n => ∑ m ∈ Finset.range M,
            |inner ℝ (u : ctE n) (θ : ctE n)| * blkG cc lam m θ) from by
          funext θ; rw [Finset.mul_sum]]
    rw [MeasureTheory.integral_finset_sum]
    · exact Finset.sum_congr rfl (fun m _ => hTG m u)
    · intro m _
      exact integrable_of_continuous_finiteMeasure (Continuous.mul
        (continuous_abs.comp (continuous_const.inner continuous_subtype_val)) (hblkGcont m))
  have hBGnn : (0:ℝ) ≤ BG := by
    have h1 : (0:ℝ) ≤ Cc'*CLam*Csup'*Cdim'*(2:ℝ)^(n-2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hCc'nn hCLamnn) hCsup'nn) hCdim'nn
      |> fun h => mul_nonneg h (pow_nonneg (by norm_num) _)
    have h2 : (0:ℝ) ≤ Cc'*CLam*Csup' := mul_nonneg (mul_nonneg hCc'nn hCLamnn) hCsup'nn
    have h3 : BG = Cc'*CLam*Csup'*Cdim'*(2:ℝ)^(n-2) + Cc'*CLam*Csup' + 1 := rfl
    linarith [h1, h2]
  have hBAnn : (0:ℝ) ≤ BA := by
    have h1 : (0:ℝ) ≤ Cc'*Csup'*Cdim'*(2:ℝ)^(n-2) :=
      mul_nonneg (mul_nonneg hCc'nn hCsup'nn) hCdim'nn
      |> fun h => mul_nonneg h (pow_nonneg (by norm_num) _)
    have h2 : (0:ℝ) ≤ Cc'*Csup' := mul_nonneg hCc'nn hCsup'nn
    have h3 : BA = Cc'*Csup'*Cdim'*(2:ℝ)^(n-2) + Cc'*Csup' + 1 := rfl
    linarith [h1, h2]
  have hMBGnn : (0:ℝ) ≤ ∑' m : ℕ, BG * (((m:ℝ)+1) ^ (-(2:ℤ))) :=
    tsum_nonneg (fun m => mul_nonneg hBGnn (zpow_nonneg (by positivity) _))
  have hMBAnn : (0:ℝ) ≤ ∑' m : ℕ, BA * (((m:ℝ)+1) ^ (-(2:ℤ))) :=
    tsum_nonneg (fun m => mul_nonneg hBAnn (zpow_nonneg (by positivity) _))
  have hlimG : ∀ u : ctSph n, Tendsto (fun M : ℕ =>
      (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)|
        * (∑ m ∈ Finset.range M, blkG cc lam m θ) ∂volume.toSphere))
      atTop (𝓝 (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * G θ ∂volume.toSphere)) := by
    intro u
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : ctSph n => ‖(u : ctE n)‖ * ((∑' m : ℕ, BG * (((m:ℝ)+1) ^ (-(2:ℤ)))) + 1)) ?_ ?_ ?_ ?_
    · intro M
      exact (Continuous.mul (continuous_abs.comp (continuous_const.inner continuous_subtype_val))
        (continuous_finsetSum (Finset.range M) (fun m _ => hblkGcont m))).aestronglyMeasurable
    · exact integrable_of_continuous_finiteMeasure continuous_const
    · intro M
      filter_upwards with θ
      rw [Real.norm_eq_abs, abs_mul, abs_abs]
      have hθn : ‖(θ : ctE n)‖ = 1 := mem_sphere_zero_iff_norm.mp θ.2
      have h1 : |inner ℝ (u : ctE n) (θ : ctE n)| ≤ ‖(u : ctE n)‖ := by
        have := abs_real_inner_le_norm (u : ctE n) (θ : ctE n)
        rwa [hθn, mul_one] at this
      have h2 : |∑ m ∈ Finset.range M, blkG cc lam m θ| ≤ ∑' m : ℕ, BG * (((m:ℝ)+1) ^ (-(2:ℤ))) := by
        rw [← Real.norm_eq_abs]
        refine le_trans (norm_sum_le _ _) ?_
        refine le_trans (Finset.sum_le_sum (fun m _ => hblkG m θ)) ?_
        exact Summable.sum_le_tsum _ (fun m _ => mul_nonneg hBGnn (zpow_nonneg (by positivity) _)) hsumG
      calc |inner ℝ (u : ctE n) (θ : ctE n)| * |∑ m ∈ Finset.range M, blkG cc lam m θ|
          ≤ ‖(u : ctE n)‖ * (∑' m : ℕ, BG * (((m:ℝ)+1) ^ (-(2:ℤ)))) :=
            mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
        _ ≤ ‖(u : ctE n)‖ * ((∑' m : ℕ, BG * (((m:ℝ)+1) ^ (-(2:ℤ)))) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    · filter_upwards with θ
      have hsumθ : Summable (fun m : ℕ => blkG cc lam m θ) :=
        Summable.of_norm_bounded hsumG (fun m => hblkG m θ)
      have h1 := hsumθ.hasSum.tendsto_sum_nat
      have h2 := h1.const_mul |inner ℝ (u : ctE n) (θ : ctE n)|
      show Tendsto (fun M : ℕ => |inner ℝ (u : ctE n) (θ : ctE n)|
        * (∑ m ∈ Finset.range M, blkG cc lam m θ)) atTop
        (𝓝 (|inner ℝ (u : ctE n) (θ : ctE n)| * G θ))
      rw [show G θ = ∑' m, blkG cc lam m θ from rfl]
      exact h2
  have hAlim : ∀ u : ctSph n, Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, blkA cc m u)
      atTop (𝓝 (A u)) := by
    intro u
    have hsum : Summable (fun m : ℕ => blkA cc m u) :=
      Summable.of_norm_bounded hsumA (fun m => hblkA m u)
    have h := hsum.hasSum.tendsto_sum_nat
    rw [show A u = ∑' m, blkA cc m u from rfl]
    exact h
  have hGA : ∀ u : ctSph n,
      (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * G θ ∂volume.toSphere) = A u := by
    intro u
    have h1' : Tendsto (fun M : ℕ => ∑ m ∈ Finset.range M, blkA cc m u) atTop
        (𝓝 (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * G θ ∂volume.toSphere)) := by
      refine (hlimG u).congr' ?_
      filter_upwards with M
      exact hTGM M u
    exact tendsto_nhds_unique h1' (hAlim u)
  -- orthogonality to harmonic restrictions
  have horth : ∀ (k : ℕ) (H : MvPolynomial (Fin n) ℝ),
      H ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k →
      (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i H)) = 0 →
      (∫ θ : ctSph n, (A θ - p (θ : ctE n)) * polyFun H θ ∂volume.toSphere) = 0 := by
    intro k H hH hlap
    obtain ⟨C, hC⟩ := (isCompact_univ (X := ctSph n)).exists_bound_of_continuousOn
      (Commons.Algebra.MvPolynomial.continuous_eval_sphere n H).continuousOn
    have hC' : ∀ θ : ctSph n, |polyFun H θ| ≤ |C| := fun θ =>
      le_trans (by simpa [polyFun, Real.norm_eq_abs] using hC θ (mem_univ θ)) (le_abs_self C)
    have hCnn : 0 ≤ |C| := abs_nonneg C
    have hlim : Tendsto (fun M : ℕ => (∫ θ : ctSph n,
        (∑ m ∈ Finset.range M, blkA cc m θ) * polyFun H θ ∂volume.toSphere))
        atTop (𝓝 (∫ θ : ctSph n, A θ * polyFun H θ ∂volume.toSphere)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ : ctSph n => |C| * ((∑' m : ℕ, BA * (((m:ℝ)+1) ^ (-(2:ℤ)))) + 1)) ?_ ?_ ?_ ?_
      · intro M
        exact (Continuous.mul (continuous_finsetSum (Finset.range M) (fun m _ => hblkAcont m))
          (Commons.Algebra.MvPolynomial.continuous_eval_sphere n H)).aestronglyMeasurable
      · exact integrable_of_continuous_finiteMeasure continuous_const
      · intro M
        filter_upwards with θ
        rw [Real.norm_eq_abs, abs_mul]
        have h2 : |∑ m ∈ Finset.range M, blkA cc m θ| ≤ ∑' m : ℕ, BA * (((m:ℝ)+1) ^ (-(2:ℤ))) := by
          rw [← Real.norm_eq_abs]
          refine le_trans (norm_sum_le _ _) ?_
          refine le_trans (Finset.sum_le_sum (fun m _ => hblkA m θ)) ?_
          exact Summable.sum_le_tsum _ (fun m _ => mul_nonneg hBAnn (zpow_nonneg (by positivity) _)) hsumA
        calc |∑ m ∈ Finset.range M, blkA cc m θ| * |polyFun H θ|
            ≤ (∑' m : ℕ, BA * (((m:ℝ)+1) ^ (-(2:ℤ)))) * |C| :=
              mul_le_mul h2 (hC' θ) (abs_nonneg _) (le_trans (abs_nonneg _) h2)
          _ ≤ |C| * ((∑' m : ℕ, BA * (((m:ℝ)+1) ^ (-(2:ℤ)))) + 1) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left (by linarith) hCnn
      · filter_upwards with θ
        have hsumθ : Summable (fun m : ℕ => blkA cc m θ) :=
          Summable.of_norm_bounded hsumA (fun m => hblkA m θ)
        have h1 := hsumθ.hasSum.tendsto_sum_nat
        have h2 := h1.mul_const (polyFun H θ)
        show Tendsto (fun M : ℕ => (∑ m ∈ Finset.range M, blkA cc m θ) * polyFun H θ) atTop
          (𝓝 (A θ * polyFun H θ))
        rw [show A θ = ∑' m, blkA cc m θ from rfl]
        exact h2
    have hconst : Tendsto (fun M : ℕ => (∫ θ : ctSph n,
        (∑ m ∈ Finset.range M, blkA cc m θ) * polyFun H θ ∂volume.toSphere))
        atTop (𝓝 (∫ θ : ctSph n, p (θ : ctE n) * polyFun H θ ∂volume.toSphere)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop (k+1)] with M hM
      exact (integral_blkA_mul_H hpe hpcont hcc H hH hlap M (by omega)).symm
    have hEq := tendsto_nhds_unique hlim hconst
    have h1 : (∫ θ : ctSph n, (A θ - p (θ : ctE n)) * polyFun H θ ∂volume.toSphere)
        = (∫ θ : ctSph n, A θ * polyFun H θ ∂volume.toSphere)
          - (∫ θ : ctSph n, p (θ : ctE n) * polyFun H θ ∂volume.toSphere) := by
      rw [show (fun θ : ctSph n => (A θ - p (θ : ctE n)) * polyFun H θ)
          = (fun θ : ctSph n => A θ * polyFun H θ - p (θ : ctE n) * polyFun H θ) from by
            funext θ; ring]
      rw [MeasureTheory.integral_sub]
      · exact integrable_of_continuous_finiteMeasure (Continuous.mul hAcont
          (Commons.Algebra.MvPolynomial.continuous_eval_sphere n H))
      · exact integrable_of_continuous_finiteMeasure (Continuous.mul
          (hpcont.comp continuous_subtype_val)
          (Commons.Algebra.MvPolynomial.continuous_eval_sphere n H))
    rw [h1, hEq, sub_self]
  -- density argument
  have hFzero : ∀ θ : ctSph n, A θ - p (θ : ctE n) = 0 := by
    set F : ctSph n → ℝ := fun θ => A θ - p (θ : ctE n) with hF
    have hFcont : Continuous F := hAcont.sub (hpcont.comp continuous_subtype_val)
    have hFeven : ∀ θ, F (reflSphere θ) = F θ := by
      intro θ
      show A (reflSphere θ) - p ((reflSphere θ : ctE n)) = A θ - p (θ : ctE n)
      rw [hAeven θ, reflSphere_coe]
      congr 1
      exact hpe (θ : ctE n)
    have hFint : Integrable (fun θ : ctSph n => (F θ)^2) volume.toSphere :=
      integrable_of_continuous_finiteMeasure (hFcont.pow 2)
    have hs : (∫ θ : ctSph n, (F θ)^2 ∂volume.toSphere) = 0 := by
      have hkey : ∀ ε : ℝ, 0 < ε → (∫ θ : ctSph n, (F θ)^2 ∂volume.toSphere) ≤ ε := by
        intro ε hε
        obtain ⟨m, Hf, hHcond, hHbound⟩ :=
          Commons.Analysis.MeasureTheory.harmonic_polynomial_L2_dense_even F
            hFcont.aestronglyMeasurable hFeven hFint hε
        have hHcont : Continuous (fun θ : ctSph n => ∑ j : Fin m, polyFun (Hf j) θ) :=
          continuous_finsetSum Finset.univ (fun j _ =>
            Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Hf j))
        have horthF : ∀ j : Fin m, (∫ θ : ctSph n, F θ * polyFun (Hf j) θ ∂volume.toSphere) = 0 := by
          intro j
          obtain ⟨kj, hkjmem, hkjlap⟩ := hHcond j
          have h := horth kj (Hf j) hkjmem hkjlap
          simpa [hF] using h
        have hFH : (∫ θ : ctSph n, F θ * (∑ j : Fin m, polyFun (Hf j) θ) ∂volume.toSphere) = 0 := by
          rw [show (fun θ : ctSph n => F θ * (∑ j : Fin m, polyFun (Hf j) θ))
              = (fun θ : ctSph n => ∑ j : Fin m, F θ * polyFun (Hf j) θ) from by
                funext θ; rw [Finset.mul_sum]]
          rw [MeasureTheory.integral_finset_sum]
          · exact Finset.sum_eq_zero (fun j _ => horthF j)
          · intro j _
            exact integrable_of_continuous_finiteMeasure (Continuous.mul hFcont
              (Commons.Algebra.MvPolynomial.continuous_eval_sphere n (Hf j)))
        have hsplit : (∫ θ : ctSph n, (F θ)^2 ∂volume.toSphere)
            = ∫ θ : ctSph n, F θ * (F θ - (∑ j : Fin m, polyFun (Hf j) θ)) ∂volume.toSphere := by
          have h1 : (∫ θ : ctSph n, F θ * (F θ - (∑ j : Fin m, polyFun (Hf j) θ)) ∂volume.toSphere)
              = (∫ θ : ctSph n, F θ * F θ ∂volume.toSphere)
                - (∫ θ : ctSph n, F θ * (∑ j : Fin m, polyFun (Hf j) θ) ∂volume.toSphere) := by
            rw [show (fun θ : ctSph n => F θ * (F θ - (∑ j : Fin m, polyFun (Hf j) θ)))
                = (fun θ : ctSph n => F θ * F θ - F θ * (∑ j : Fin m, polyFun (Hf j) θ)) from by
                  funext θ; ring]
            rw [MeasureTheory.integral_sub]
            · exact integrable_of_continuous_finiteMeasure (hFcont.mul hFcont)
            · exact integrable_of_continuous_finiteMeasure (hFcont.mul hHcont)
          rw [h1, hFH, sub_zero]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with θ
          ring
        have hAMGM : ∀ θ : ctSph n, F θ * (F θ - (∑ j : Fin m, polyFun (Hf j) θ))
            ≤ ((F θ)^2 + (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2) / 2 := by
          intro θ
          have h1 : F θ * (F θ - (∑ j : Fin m, polyFun (Hf j) θ))
              ≤ |F θ * (F θ - (∑ j : Fin m, polyFun (Hf j) θ))| := le_abs_self _
          rw [abs_mul] at h1
          have h2 : |F θ| * |F θ - (∑ j : Fin m, polyFun (Hf j) θ)|
              ≤ ((F θ)^2 + (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2) / 2 := by
            nlinarith [sq_nonneg (|F θ| - |F θ - (∑ j : Fin m, polyFun (Hf j) θ)|),
              sq_abs (F θ), sq_abs (F θ - (∑ j : Fin m, polyFun (Hf j) θ))]
          linarith
        have h2 : (∫ θ : ctSph n, F θ * (F θ - (∑ j : Fin m, polyFun (Hf j) θ)) ∂volume.toSphere)
            ≤ (∫ θ : ctSph n, (F θ)^2 ∂volume.toSphere) / 2
              + (∫ θ : ctSph n, (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2 ∂volume.toSphere) / 2 := by
          have hint1 : Integrable (fun θ : ctSph n => ((F θ)^2
              + (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2) / 2) volume.toSphere :=
            integrable_of_continuous_finiteMeasure (((hFcont.pow 2).add
              ((hFcont.sub hHcont).pow 2)).div_const 2)
          have hint2 : Integrable (fun θ : ctSph n => F θ
              * (F θ - (∑ j : Fin m, polyFun (Hf j) θ))) volume.toSphere :=
            integrable_of_continuous_finiteMeasure
              (hFcont.mul (hFcont.sub hHcont))
          calc (∫ θ : ctSph n, F θ * (F θ - (∑ j : Fin m, polyFun (Hf j) θ)) ∂volume.toSphere)
              ≤ ∫ θ : ctSph n, ((F θ)^2 + (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2) / 2
                  ∂volume.toSphere := MeasureTheory.integral_mono hint2 hint1 hAMGM
            _ = (∫ θ : ctSph n, (F θ)^2 ∂volume.toSphere) / 2
                + (∫ θ : ctSph n, (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2 ∂volume.toSphere) / 2 := by
                rw [show (fun θ : ctSph n => ((F θ)^2 + (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2) / 2)
                    = (fun θ : ctSph n => (1/2) * ((F θ)^2
                        + (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2)) from by
                      funext θ; ring]
                rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add]
                · ring
                · exact integrable_of_continuous_finiteMeasure (hFcont.pow 2)
                · exact integrable_of_continuous_finiteMeasure ((hFcont.sub hHcont).pow 2)
        have hHbound' : (∫ θ : ctSph n,
            (F θ - (∑ j : Fin m, polyFun (Hf j) θ))^2 ∂volume.toSphere) ≤ ε := by
          simpa only [polyFun] using hHbound
        linarith [h2, hHbound', hsplit]
      have hs0 : (∫ θ : ctSph n, (F θ)^2 ∂volume.toSphere) ≤ 0 := by
        by_contra hneg
        push_neg at hneg
        have h := hkey ((∫ θ : ctSph n, (F θ)^2 ∂volume.toSphere) / 2) (by linarith)
        linarith
      exact le_antisymm hs0 (integral_nonneg (fun θ => sq_nonneg _))
    have hsq : (fun θ : ctSph n => (F θ)^2) =ᵐ[volume.toSphere] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall (fun θ => sq_nonneg (F θ))) hFint).mp hs
    have hFae : F =ᵐ[volume.toSphere] 0 := hsq.mono (fun θ hθ => by
      simpa [pow_two] using hθ)
    have : F = 0 := MeasureTheory.Measure.eq_of_ae_eq hFae hFcont continuous_zero
    intro θ
    have h := congrFun this θ
    simpa [hF] using h
  show (∫ θ : ctSph n, |inner ℝ (u : ctE n) (θ : ctE n)| * G θ ∂volume.toSphere) = p (u : ctE n)
  rw [hGA u]
  exact sub_eq_zero.mp (hFzero u)

end EuclidMain



/-- The target theorem for `EuclideanSpace ℝ (Fin n)`, `n ≥ 2`. -/
theorem euclid_target {n : ℕ} (hn : 2 ≤ n) (p : ctE n → ℝ)
    (hpe : ∀ x : ctE n, p (-x) = p x)
    (hph : ∀ (a : ℝ) (x : ctE n), 0 ≤ a → p (a • x) = a * p x)
    (hpcont : Continuous p) (hps : ContDiffOn ℝ ⊤ p {x : ctE n | x ≠ 0}) :
    ∃ f : ctE n → ℝ, Continuous f ∧ (∀ x : ctE n, f (-x) = f x) ∧
      (∃ R : ℝ, ∀ x : ctE n, f x ≠ 0 → ‖x‖ ≤ R) ∧
      (∀ u : ctE n, p u = ∫ x : ctE n, |inner ℝ u x| * f x) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (ctE n) := inferInstance
  obtain ⟨g, hgcont, hgeven, hgT⟩ := euclid_surjective hn p hpe hph hpcont hps
  obtain ⟨ψ, hψcont, hψs, hψ0, hψnorm⟩ :=
    Commons.Analysis.MeasureTheory.exists_radial_normalization (n - 1)
  exact assemble_main p hph g hgcont hgeven hψcont hψ0 hψs
    (by rw [finrank_euclideanSpace_fin]; exact hψnorm) hgT


theorem cosine_transform_even_smooth_homogeneous
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (p : V → ℝ)
    (hpe : ∀ x : V, p (-x) = p x)
    (hph : ∀ (a : ℝ) (x : V), 0 ≤ a → p (a • x) = a * p x)
    (hpcont : Continuous p)
    (hps : ContDiffOn ℝ ⊤ p {x : V | x ≠ 0}) :
    ∃ f : V → ℝ, Continuous f ∧ (∀ x : V, f (-x) = f x) ∧
      (∃ R : ℝ, ∀ x : V, f x ≠ 0 → ‖x‖ ≤ R) ∧
      (∀ u : V, p u = ∫ x : V, |inner ℝ u x| * f x) := by
  by_cases hnt : Nontrivial V
  · haveI := hnt
    by_cases h2 : 2 ≤ Module.finrank ℝ V
    · -- dimension at least two: reduce to `EuclideanSpace ℝ (Fin n)`
      set n : ℕ := Module.finrank ℝ V with hn
      let φ : V ≃ₗᵢ[ℝ] ctE n := (stdOrthonormalBasis ℝ V).repr
      let pE : ctE n → ℝ := fun y => p (φ.symm y)
      have hpeE : ∀ y : ctE n, pE (-y) = pE y := by
        intro y
        show p (φ.symm (-y)) = p (φ.symm y)
        rw [map_neg]; exact hpe _
      have hphE : ∀ (a : ℝ) (y : ctE n), 0 ≤ a → pE (a • y) = a * pE y := by
        intro a y ha
        show p (φ.symm (a • y)) = a * p (φ.symm y)
        rw [map_smul]; exact hph a _ ha
      have hpcontE : Continuous pE := hpcont.comp φ.symm.continuous
      have hpsE : ContDiffOn ℝ ⊤ pE {y : ctE n | y ≠ 0} := by
        have h2' : ContDiffOn ℝ ⊤ (φ.symm : ctE n → V) {y : ctE n | y ≠ 0} :=
          (φ.symm.contDiff.contDiffOn).mono (Set.subset_univ _)
        refine (hps.comp h2' ?_)
        intro y hy
        simpa using hy
      obtain ⟨fE, hfEcont, hfEeven, ⟨RE, hRE⟩, hfEid⟩ :=
        euclid_target h2 pE hpeE hphE hpcontE hpsE
      refine ⟨fun x => fE (φ x), hfEcont.comp φ.continuous, ?_, ⟨RE, ?_⟩, ?_⟩
      · intro x
        show fE (φ (-x)) = fE (φ x)
        rw [map_neg]; exact hfEeven (φ x)
      · intro x hx
        have h2' : ‖φ x‖ ≤ RE := hRE (φ x) hx
        rwa [LinearIsometryEquiv.norm_map] at h2'
      · intro u
        have hid := hfEid (φ u)
        have hpu : p u = pE (φ u) := by simp [pE]
        rw [hpu, hid]
        have hmp : MeasureTheory.MeasurePreserving (φ : V → ctE n) volume volume :=
          LinearIsometryEquiv.measurePreserving φ
        have hcomp := hmp.integral_comp (φ.toHomeomorph.toMeasurableEquiv).measurableEmbedding
          (fun y : ctE n => |inner ℝ (φ u) y| * fE y)
        rw [← hcomp]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        rw [LinearIsometryEquiv.inner_map_map]
    · -- one-dimensional case
      have hnpos : 0 < Module.finrank ℝ V := Module.finrank_pos
      have hn1 : Module.finrank ℝ V = 1 := by omega
      obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
      let a : V := ‖v‖⁻¹ • v
      have ha : ‖a‖ = 1 := by
        show ‖‖v‖⁻¹ • v‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
      have ha0 : a ≠ 0 := by
        intro h; rw [h, norm_zero] at ha; norm_num at ha
      have hspan : Submodule.span ℝ ({a} : Set V) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [finrank_span_singleton ha0, hn1]
      have hunit_repr : ∀ u : Metric.sphere (0 : V) 1,
          ∃ β : ℝ, |β| = 1 ∧ (u : V) = β • a := by
        intro u
        have hu : (u : V) ∈ Submodule.span ℝ ({a} : Set V) := by rw [hspan]; trivial
        rw [Submodule.mem_span_singleton] at hu
        obtain ⟨β, hβ⟩ := hu
        refine ⟨β, ?_, hβ.symm⟩
        have hun : ‖(u : V)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
        have h1 : ‖(u : V)‖ = |β| * ‖a‖ := by rw [← hβ, norm_smul, Real.norm_eq_abs]
        rw [hun, ha, mul_one] at h1
        linarith [h1]
      have habs : ∀ u θ : Metric.sphere (0 : V) 1, |inner ℝ (u : V) (θ : V)| = 1 := by
        intro u θ
        obtain ⟨β, hβ, hu⟩ := hunit_repr u
        obtain ⟨γ, hγ, hθ⟩ := hunit_repr θ
        have haa : inner ℝ a a = 1 := by
          rw [real_inner_self_eq_norm_sq, ha]; norm_num
        have hinner : inner ℝ (β • a) (γ • a) = β * γ := by
          rw [inner_smul_left, inner_smul_right, haa, mul_one]
          rfl
        rw [hu, hθ, hinner, abs_mul, hβ, hγ, one_mul]
      have hpunit : ∀ u : Metric.sphere (0 : V) 1, p (u : V) = p a := by
        intro u
        obtain ⟨β, hβ, hu⟩ := hunit_repr u
        rcases (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hβ with h | h
        · rw [hu, h, one_smul]
        · rw [hu, h, neg_smul, one_smul, hpe]
      let S : ℝ := (volume.toSphere : Measure (Metric.sphere (0 : V) 1)).real Set.univ
      have hSne : S ≠ 0 := by
        haveI : MeasureTheory.Measure.IsOpenPosMeasure
            (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) := inferInstance
        have hSpos : (volume.toSphere : Measure (Metric.sphere (0 : V) 1)) Set.univ ≠ 0 :=
          MeasureTheory.Measure.IsOpenPosMeasure.open_pos _ isOpen_univ
            ⟨⟨a, mem_sphere_zero_iff_norm.mpr ha⟩, mem_univ _⟩
        show (volume.toSphere : Measure (Metric.sphere (0 : V) 1)).real Set.univ ≠ 0
        rw [MeasureTheory.Measure.real_def, ENNReal.toReal_ne_zero]
        exact ⟨hSpos, MeasureTheory.measure_ne_top _ _⟩
      let g : Metric.sphere (0 : V) 1 → ℝ := fun _ => p a / S
      have hgT : ∀ u : Metric.sphere (0 : V) 1,
          (∫ θ : Metric.sphere (0 : V) 1, |inner ℝ (u : V) (θ : V)| * g θ
            ∂volume.toSphere) = p (u : V) := by
        intro u
        rw [show (∫ θ : Metric.sphere (0 : V) 1, |inner ℝ (u : V) (θ : V)| * g θ
              ∂volume.toSphere)
            = ∫ _θ : Metric.sphere (0 : V) 1, (p a / S) ∂volume.toSphere from
              MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by
                show |inner ℝ (u : V) (θ : V)| * g θ = p a / S
                rw [show |inner ℝ (u : V) (θ : V)| = 1 from habs u θ]
                simp [g]))]
        rw [MeasureTheory.integral_const]
        show S • (p a / S) = p (u : V)
        rw [smul_eq_mul, mul_comm S, div_mul_cancel₀ (p a) hSne]
        exact (hpunit u).symm
      obtain ⟨ψ, hψcont, hψs, hψ0, hψnorm⟩ :=
        Commons.Analysis.MeasureTheory.exists_radial_normalization (Module.finrank ℝ V - 1)
      exact assemble_main p hph g continuous_const (fun _ => rfl) hψcont hψ0 hψs hψnorm hgT
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnt
    have hp0 : p 0 = 0 := by
      have h := hph 0 0 (le_refl 0); simpa using h
    refine ⟨fun _ => 0, continuous_const, fun x => rfl, ⟨0, ?_⟩, ?_⟩
    · intro x hx; exact absurd rfl hx
    · intro u
      have hu : u = 0 := Subsingleton.elim u 0
      subst hu
      rw [hp0]
      simp

end

end Commons.Geometry.Convex.Hadwiger
