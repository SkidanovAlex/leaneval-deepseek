import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable

namespace Commons.Analysis.Calculus

open scoped BigOperators Topology
open EuclideanSpace

/-- Uniform version of the cube bump estimate: the derivative bounds `K a` can be chosen
independently of the centre `c` (they depend only on the dimension and the side `W` of the
cube).  This is the form needed when summing over a family of cubes. -/
theorem cube_bump_deriv_bound_uniform (d : ℕ) (a_max : ℕ) (W : ℝ) (hW : 0 < W) :
    ∃ K : ℕ → ℝ, (∀ a ≤ a_max, 0 ≤ K a) ∧
      ∀ c : EuclideanSpace ℝ (Fin d),
        ∃ η : EuclideanSpace ℝ (Fin d) → ℝ,
          ContDiff ℝ a_max η ∧ (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
          (∀ x, (∀ i : Fin d, |x i - c i| ≤ W / 4) → η x = 1) ∧
          (∀ x, (∃ i : Fin d, W / 2 ≤ |x i - c i|) → η x = 0) ∧
          (∀ a ≤ a_max, ∀ x, ‖iteratedFDeriv ℝ a η x‖ ≤ K a * W ^ (-(a : ℝ))) := by
  -- The fixed one-dimensional smooth bump: `1` on `[-1/4,1/4]`, `0` outside `[-1/2,1/2]`.
  let b : ContDiffBump (0 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  -- The fixed product bump on `ℝᵈ`, independent of the centre.
  let φ : EuclideanSpace ℝ (Fin d) → ℝ := fun y => ∏ i : Fin d, (b : ℝ → ℝ) (y i)
  have hb_zero : ∀ t : ℝ, 1 / 2 ≤ |t| → b t = 0 := by
    intro t ht
    apply b.zero_of_le_dist
    simpa [b, Real.dist_eq] using ht
  have hφ_eq_zero : ∀ y, (∃ i : Fin d, 1 / 2 ≤ |y i|) → φ y = 0 := by
    intro y ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hb_zero (y i) hi)
  have hφ_eq_one : ∀ y, (∀ i : Fin d, |y i| ≤ 1 / 4) → φ y = 1 := by
    intro y hy
    apply Finset.prod_eq_one
    intro i _
    apply b.one_of_mem_closedBall
    simpa [b, Real.dist_eq] using hy i
  have hb_nonneg : ∀ t : ℝ, 0 ≤ b t := fun t => b.nonneg' t
  have hb_le_one : ∀ t : ℝ, b t ≤ 1 := fun t => b.le_one
  have hφ_nonneg : ∀ y, 0 ≤ φ y := by
    intro y
    exact Finset.prod_nonneg (fun i _ => hb_nonneg (y i))
  have hφ_le_one : ∀ y, φ y ≤ 1 := by
    intro y
    exact Finset.prod_le_one (fun i _ => hb_nonneg (y i))
      (fun i _ => hb_le_one (y i))
  have hproj_cd : ∀ i : Fin d, ContDiff ℝ (a_max : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin d) => y i) := by
    intro i
    have hproj : (fun y : EuclideanSpace ℝ (Fin d) => y i) =
        (ContinuousLinearMap.proj (R := ℝ) i).comp
          ((EuclideanSpace.equiv (Fin d) ℝ) : EuclideanSpace ℝ (Fin d) →L[ℝ] (Fin d → ℝ)) := by
      ext y; simp
    rw [hproj]
    exact ContinuousLinearMap.contDiff _
  have hφ_cd : ContDiff ℝ (a_max : ℕ∞) φ := by
    show ContDiff ℝ (a_max : ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin d) => ∏ i : Fin d, (b : ℝ → ℝ) (y i))
    apply contDiff_prod
    intro i _
    exact (b.contDiff (n := (a_max : ℕ∞))).comp (hproj_cd i)
  -- The compact cube `{z | ∀ i, |zᵢ| ≤ 1/2}` contains the support of `φ`.
  have hbox : IsCompact {z : EuclideanSpace ℝ (Fin d) | ∀ i, |z i| ≤ (1 / 2 : ℝ)} := by
    have himg : (EuclideanSpace.equiv (Fin d) ℝ).symm ''
        (Set.univ.pi fun _ : Fin d => Set.Icc (-(1 / 2) : ℝ) (1 / 2))
        = {z : EuclideanSpace ℝ (Fin d) | ∀ i, |z i| ≤ (1 / 2 : ℝ)} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩ i
        have h1 : (EuclideanSpace.equiv (Fin d) ℝ).symm w i = w i := by simp
        have h2 := hw i (Set.mem_univ i)
        rw [Set.mem_Icc] at h2
        rw [h1]; exact abs_le.mpr h2
      · intro hz
        refine ⟨EuclideanSpace.equiv (Fin d) ℝ z, ?_, by simp⟩
        intro i _
        have h1 : (EuclideanSpace.equiv (Fin d) ℝ) z i = z i := by simp
        rw [Set.mem_Icc, h1]; exact abs_le.mp (hz i)
    rw [← himg]
    exact (isCompact_univ_pi (fun _ : Fin d =>
      (isCompact_Icc : IsCompact (Set.Icc (-(1 / 2) : ℝ) (1 / 2))))).image
        (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous
  have hsupp : Function.support φ ⊆ {z : EuclideanSpace ℝ (Fin d) | ∀ i, |z i| ≤ (1 / 2 : ℝ)} := by
    intro z hz i
    by_contra h
    push Not at h
    exact hz (hφ_eq_zero z ⟨i, le_of_lt h⟩)
  have hφ_cs : HasCompactSupport φ := HasCompactSupport.of_support_subset_isCompact hbox hsupp
  -- The iterated derivatives of `φ` also have compact support.
  have hderiv_zero_outside : ∀ (a : ℕ) (z : EuclideanSpace ℝ (Fin d)), z ∉ tsupport φ →
      iteratedFDeriv ℝ a φ z = 0 := by
    intro a z hz
    have heq : φ =ᶠ[𝓝 z] (0 : EuclideanSpace ℝ (Fin d) → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hz
    have h2 : iteratedFDeriv ℝ a φ =ᶠ[𝓝 z]
        iteratedFDeriv ℝ a (0 : EuclideanSpace ℝ (Fin d) → ℝ) :=
      heq.iteratedFDeriv ℝ a
    rw [h2.eq_of_nhds]
    simp
  have hcs_deriv : ∀ a : ℕ, HasCompactSupport (fun z => iteratedFDeriv ℝ a φ z) := by
    intro a
    refine HasCompactSupport.of_support_subset_isCompact hφ_cs.isCompact ?_
    intro z hz
    by_contra hz'
    exact hz (hderiv_zero_outside a z hz')
  have hcs_norm : ∀ a : ℕ, HasCompactSupport
      (fun z : EuclideanSpace ℝ (Fin d) => ‖iteratedFDeriv ℝ a φ z‖) := by
    intro a
    refine (hcs_deriv a).mono ?_
    intro z hz
    simpa using hz
  -- The uniform constants: supremum of the derivative norms of `φ`.
  let K : ℕ → ℝ := fun a =>
    sSup (Set.range (fun z : EuclideanSpace ℝ (Fin d) => ‖iteratedFDeriv ℝ a φ z‖))
  have hK_bdd : ∀ a, a ≤ a_max → BddAbove
      (Set.range (fun z : EuclideanSpace ℝ (Fin d) => ‖iteratedFDeriv ℝ a φ z‖)) := by
    intro a ha
    have hφ_a : ContDiff ℝ (a : ℕ∞) φ := hφ_cd.of_le (by exact_mod_cast ha)
    have hcont : Continuous
        (fun z : EuclideanSpace ℝ (Fin d) => ‖iteratedFDeriv ℝ a φ z‖) :=
      (hφ_a.continuous_iteratedFDeriv (m := a) le_rfl).norm
    exact ((hcs_norm a).isCompact_range hcont).bddAbove
  have hK_nonneg : ∀ a, a ≤ a_max → 0 ≤ K a := by
    intro a ha
    exact le_trans (norm_nonneg _) (le_csSup (hK_bdd a ha) (Set.mem_range_self 0))
  have hK_bound : ∀ a, a ≤ a_max → ∀ z,
      ‖iteratedFDeriv ℝ a φ z‖ ≤ K a := by
    intro a ha z
    exact le_csSup (hK_bdd a ha) (Set.mem_range_self z)
  refine ⟨K, hK_nonneg, ?_⟩
  intro c
  refine ⟨fun x => φ (W⁻¹ • (x - c)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hφ_cd.comp ((contDiff_id.sub contDiff_const).const_smul (W⁻¹))
  · intro x; exact hφ_nonneg _
  · intro x; exact hφ_le_one _
  · intro x hx
    apply hφ_eq_one
    intro i
    have hcoord : |(W⁻¹ • (x - c)) i| = W⁻¹ * |x i - c i| := by
      rw [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hW.le)]
    rw [hcoord]
    calc W⁻¹ * |x i - c i| ≤ W⁻¹ * (W / 4) :=
          mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr hW.le)
      _ = 1 / 4 := by field_simp
  · intro x hx
    apply hφ_eq_zero
    obtain ⟨i, hi⟩ := hx
    refine ⟨i, ?_⟩
    have hcoord : |(W⁻¹ • (x - c)) i| = W⁻¹ * |x i - c i| := by
      rw [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg (inv_nonneg.mpr hW.le)]
    rw [hcoord]
    calc (1 / 2 : ℝ) = W⁻¹ * (W / 2) := by field_simp
      _ ≤ W⁻¹ * |x i - c i| := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hW.le)
  · intro a ha x
    have hφ_a : ContDiff ℝ (a : ℕ∞) φ := hφ_cd.of_le (by exact_mod_cast ha)
    have hscale : iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => φ (W⁻¹ • (x - c))) x
        = (W⁻¹) ^ a • iteratedFDeriv ℝ a φ (W⁻¹ • (x - c)) := by
      have h1 := iteratedFDeriv_comp_sub (𝕜 := ℝ)
        (f := fun z : EuclideanSpace ℝ (Fin d) => φ (W⁻¹ • z)) a c x
      have h2 := congr_fun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (f := φ) (i := a)
        (W⁻¹) hφ_a) (x - c)
      rw [h1, h2]
    have hpoweq : (W⁻¹) ^ a = W ^ (-(a : ℝ)) := by
      rw [Real.rpow_neg hW.le (a : ℝ), Real.rpow_natCast, inv_pow]
    calc ‖iteratedFDeriv ℝ a (fun x : EuclideanSpace ℝ (Fin d) => φ (W⁻¹ • (x - c))) x‖
        = ‖(W⁻¹) ^ a • iteratedFDeriv ℝ a φ (W⁻¹ • (x - c))‖ := by rw [hscale]
      _ = ‖(W⁻¹) ^ a‖ * ‖iteratedFDeriv ℝ a φ (W⁻¹ • (x - c))‖ := norm_smul _ _
      _ = (W⁻¹) ^ a * ‖iteratedFDeriv ℝ a φ (W⁻¹ • (x - c))‖ := by
            rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hW.le) a)]
      _ ≤ (W⁻¹) ^ a * K a := by
            gcongr
            exact hK_bound a ha (W⁻¹ • (x - c))
      _ = K a * W ^ (-(a : ℝ)) := by rw [hpoweq]; ring

end Commons.Analysis.Calculus