import Mathlib
import Submission.Work.Modular.Lattice

namespace Work.Modular

open Work.Modular
open scoped Manifold Real Topology
open UpperHalfPlane

set_option maxHeartbeats 800000

/-- **Gaussian decay on a discrete lattice.**  For a discrete `ℤ`-submodule `L` of a
finite-dimensional real normed space `E` and any `c > 0`, the sum `∑_{x ∈ L} exp (-c ‖x‖²)`
converges.  Since `L` is discrete the norm `‖·‖` grows at least like a positive multiple of a
lattice coordinate, so the Gaussian is dominated by `‖·‖ ^ r` for a sufficiently negative real
`r`, and `ZLattice.summable_norm_rpow` gives summability of the latter. -/
theorem summable_exp_neg_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] {c : ℝ} (hc : 0 < c) :
    Summable (fun z : L => Real.exp (-c * ‖z‖ ^ 2)) := by
  set N : ℕ := Module.finrank ℤ L + 1 with hN
  set r : ℝ := -((2 * N : ℕ) : ℝ) with hr
  have hr_lt : r < -(Module.finrank ℤ L : ℝ) := by
    rw [hr]
    have hd2 : (Module.finrank ℤ L : ℝ) < ((2 * N : ℕ) : ℝ) := by
      rw [hN]; push_cast
      have : Module.finrank ℤ L < 2 * (Module.finrank ℤ L + 1) := by omega
      exact_mod_cast this
    linarith
  have hsum : Summable (fun z : L => ‖z‖ ^ r) := ZLattice.summable_norm_rpow L r hr_lt
  refine Summable.of_norm_bounded_eventually hsum ?_
  have hL := (isLittleO_exp_neg_mul_rpow_atTop hc (-(N : ℝ))).eventuallyLE
  rw [Filter.eventually_atTop] at hL
  obtain ⟨T, hT⟩ := hL
  set T' : ℝ := max T 1 with hT'
  have hT'pos : 0 < T' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hkey : ∀ u : ℝ, T' ≤ u → Real.exp (-c * u) ≤ u ^ (-(N : ℝ)) := by
    intro u hu
    have h0 : 0 ≤ u := le_trans hT'pos.le hu
    have h1 := hT u (le_trans (le_max_left _ _) hu)
    rwa [Real.norm_of_nonneg (Real.exp_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg h0 _)] at h1
  have hclosed : IsClosed (L : Set E) := by
    have hh := @AddSubgroup.isClosed_of_discrete E _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
    simpa using hh
  have hfin2 : (Metric.ball (0 : E) (Real.sqrt T') ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed (DiscreteTopology.isDiscrete (s := (L : Set E)))
      Metric.isBounded_ball hclosed
  have hfin : ({z : L | ‖z‖ ^ 2 < T'} : Set L).Finite := by
    have hpre := hfin2.preimage_embedding (Function.Embedding.subtype (fun x : E => x ∈ L))
    refine hpre.subset ?_
    intro z hz
    simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
      Set.mem_ofPred_eq] at hz ⊢
    exact ⟨by rw [Real.lt_sqrt (norm_nonneg _)]; exact hz, z.2⟩
  refine Filter.eventually_cofinite.mpr ?_
  refine hfin.subset ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  by_contra hcon
  push Not at hcon
  have h1 : Real.exp (-c * ‖z‖ ^ 2) ≤ (‖z‖ ^ 2) ^ (-(N : ℝ)) := hkey _ hcon
  have h2 : (‖z‖ ^ 2) ^ (-(N : ℝ)) = ‖z‖ ^ r := by
    rw [hr, Real.rpow_neg (sq_nonneg _), Real.rpow_natCast, Real.rpow_neg (norm_nonneg _),
      Real.rpow_natCast, pow_mul]
  rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at hz
  exact hz (h1.trans h2.le)

/-- The theta series `Θ_L τ = ∑_{x ∈ L} exp (π i τ ‖x‖²)` of a discrete lattice `L ⊆ ℝⁿ`
is holomorphic on the upper half plane: it is a locally uniformly convergent sum of entire
functions `τ ↦ exp (π i τ ‖x‖²)`. -/
theorem thetaSeries_mdifferentiable {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] : MDiff (thetaSeries L) := by
  intro τ
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  have him : (τ : ℂ).im = τ.im := UpperHalfPlane.coe_im τ
  set d : ℝ := τ.im / 2 with hd
  have hdpos : 0 < d := by rw [hd]; positivity
  set c : ℝ := Real.pi * d with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set U : Set ℂ := {w : ℂ | d < w.im} with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef]; exact isOpen_lt continuous_const Complex.continuous_im
  have hτU : (τ : ℂ) ∈ U := by
    rw [hUdef, Set.mem_ofPred_eq, hd, him]
    linarith [τ.im_pos]
  have hsum' : Summable (fun x : L =>
      Real.exp (-c * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) := by
    simpa only [Submodule.norm_coe] using summable_exp_neg_norm_sq L hcpos
  have hterm : ∀ x : L, DifferentiableOn ℂ
      (fun w : ℂ => Complex.exp (π * Complex.I * w *
        (((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ)) : ℂ))) U := by
    intro x
    refine ((Complex.differentiable_exp.comp ?_).differentiableOn)
    fun_prop
  have hbound : ∀ x : L, ∀ w ∈ U,
      ‖Complex.exp (π * Complex.I * w * (((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ)) : ℂ))‖
        ≤ Real.exp (-c * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    intro x w hw
    rw [Complex.norm_exp]
    have hK : (0:ℝ) ≤ ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := sq_nonneg _
    have hw' : d < w.im := by simpa only [hUdef, Set.mem_ofPred_eq] using hw
    have hcd : c ≤ Real.pi * w.im := by
      rw [hc]; nlinarith [Real.pi_pos, hw']
    have hre : (π * Complex.I * w * (((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ)) : ℂ)).re
        = -Real.pi * w.im * ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]; ring
    rw [hre]
    apply Real.exp_le_exp.mpr
    nlinarith [hK, hcd]
  have hdiff : DifferentiableOn ℂ
      (fun w : ℂ => ∑' x : L, Complex.exp (π * Complex.I * w *
        (((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ)) : ℂ))) U :=
    Complex.differentiableOn_tsum_of_summable_norm hsum' hterm hUopen hbound
  have hev : (thetaSeries L ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      (fun w : ℂ => ∑' x : L, Complex.exp (π * Complex.I * w *
        (((‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 : ℝ)) : ℂ))) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with w hw
    simp only [Function.comp_apply, thetaSeries, thetaTerm, ofComplex_apply_of_im_pos hw]
  exact (hev.differentiableAt_iff).mpr (hdiff.differentiableAt (hUopen.mem_nhds hτU))

end Work.Modular
