import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.FireFix.Clauses.PhysVortAeAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.FireFix.Clauses

/-! ## The pointwise bound for one vorticity slice

The proof is the chain rule for `x ↦ Ψ(ρ(x)^{3α}/B, θ(x)) • e_θ(x)` (`Ψ` the two-variable
profile slice): the product rule bounds the `e_θ`-factor by `2/r`, and the frame decomposition
`‖L‖ ≤ ‖L e_r‖ + ‖L e_θ‖ + ‖L e₃‖` together with the polar chain rules
(`Work.Cyl.fderiv_rho_theta_eR`/`eZ`/`eTheta`) bounds the profile factor by
`2|∂_zΨ|·3αρ^{3α-1}/B + 2|∂_θΨ|/ρ`.  Every ingredient is available at an *arbitrary* point of
`{r > 0}`: whenever the composite is differentiable there, the local right inverse `sect` of
`x ↦ (ρ(x)^{3α}/B, θ(x))` (`diffAt2_of_comp_sect`) upgrades that to the two-variable
differentiability of the profile. -/

lemma physVort_slice_bound {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    {τ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hAτ : 0 < A τ) (hBτ : 0 < B τ)
    {N Npz L : ℝ} (hN0 : 0 ≤ N) (hNpz0 : 0 ≤ Npz)
    (hN : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ τ| ≤ N)
    (hNpz : ∀ z θ τ' : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz)
    (hcont : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (S + 1)))
    (hτ : τ ∈ Set.Icc 0 S)
    (hsupp : ∀ z θ : ℝ, L ≤ z → Work.FTS.Regularity.profFull α g z θ τ = 0)
    {x : R3} (hr : 0 < Work.Cyl.radial x) (hθ0 : Work.Cyl.theta x ≠ 0) :
    ‖fderiv ℝ (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x‖
      ≤ psiBound α A B g τ N Npz L (Work.Cyl.rho x ^ (3 * α) / B τ) (Work.Cyl.theta x) := by
  have hρpos : 0 < Work.Cyl.rho x := lt_of_lt_of_le hr (Work.Cyl.radial_le_rho x)
  set Ψ : ℝ → ℝ → ℝ := fun z θ => Work.ConstructionInstance.profile (3 * α)
      (Work.FTS.Regularity.gSlice g τ) z θ with hΨ
  set z0 : ℝ := Work.Cyl.rho x ^ (3 * α) / B τ with hz0
  have hz0pos : 0 < z0 := by
    rw [hz0]
    exact div_pos (Real.rpow_pos_of_pos hρpos _) hBτ
  have hθmem : |Work.Cyl.theta x| < Real.pi / 2 := by
    rw [Work.Cyl.theta]
    exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hBz : B τ * z0 = Work.Cyl.rho x ^ (3 * α) := by
    rw [hz0]; field_simp
  have hpow1 : (B τ * z0) ^ (1 / (3 * α)) = Work.Cyl.rho x := by
    rw [hBz, ← Real.rpow_mul (Work.Cyl.rho_nonneg x)]
    have hexp : 3 * α * (1 / (3 * α)) = 1 := by
      rw [mul_one_div, div_self (by positivity : (3 : ℝ) * α ≠ 0)]
    rw [hexp, Real.rpow_one]
  have hpow2 : (B τ * z0) ^ ((3 * α - 1) / (3 * α)) = Work.Cyl.rho x ^ (3 * α - 1) := by
    rw [hBz, ← Real.rpow_mul (Work.Cyl.rho_nonneg x)]
    congr 1
    field_simp
  have hcosr : Work.Cyl.rho x * Real.cos (Work.Cyl.theta x) = Work.Cyl.radial x := by
    rw [cos_theta_eq x hr]
    field_simp
  have hfun : (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ)
      = fun y : R3 => (A τ)⁻¹ • (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)
          • Work.Cyl.eTheta y) := by
    funext y
    rw [Work.FTS.Regularity.physVort_apply, Work.ConstructionInstance.omegaSz_apply,
      Work.FTS.Regularity.pExp_eq, hΨ]
  by_cases hzL : z0 ≤ L
  · by_cases hd : DifferentiableAt ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
        (Work.Cyl.theta y) • Work.Cyl.eTheta y) x
    · have hD : Work.Cyl.DiffAt2 Ψ z0 (Work.Cyl.theta x) := by
        rw [hz0]
        exact diffAt2_of_differentiableAt_smul_eTheta hα hBτ hr hd
      have hDc : Work.Cyl.DiffAt2 (fun r θ => Ψ (r ^ (3 * α) / B τ) θ)
          (Work.Cyl.rho x) (Work.Cyl.theta x) := diffAt2_comp_rpow hBτ hr hD
      have hHd : DifferentiableAt ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
          (Work.Cyl.theta y)) x :=
        Work.Cyl.differentiableAt_rho_theta_comp (fun r θ => Ψ (r ^ (3 * α) / B τ) θ) x hDc hr
      have hstep1 : ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
            (Work.Cyl.theta y) • Work.Cyl.eTheta y) x‖
          ≤ |Ψ z0 (Work.Cyl.theta x)| * (2 / Work.Cyl.radial x)
            + ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
                (Work.Cyl.theta y)) x‖ := by
        have h := norm_fderiv_smul_eTheta_le
          (H := fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)) hr hHd
        simpa using h
      have hstep2 : ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
            (Work.Cyl.theta y)) x‖
          ≤ 2 * (|Work.Spaces.pz Ψ z0 (Work.Cyl.theta x)|
                * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ))
            + 2 * |Work.Spaces.pth Ψ z0 (Work.Cyl.theta x)| / Work.Cyl.rho x := by
        have h := norm_fderiv_profile_comp_le hα hBτ hr hD
        rw [← hz0] at h
        exact h
      have habs : |Ψ z0 (Work.Cyl.theta x)| ≤ 20 * (3 * α) + N := by
        have h := profile_abs_le_N hα hα13 (fun z θ hz hθ => hN z θ hz hθ) hz0pos.le
          (le_of_lt hθmem)
        simpa [hΨ] using h
      have hpz : |Work.Spaces.pz Ψ z0 (Work.Cyl.theta x)| ≤ 60 * α + Npz := by
        have h := profile_pz_le hα hα13 hNpz hcont hτ hz0pos.le (le_of_lt hθmem)
        simpa [hΨ] using h
      have hpth : |Work.Spaces.pth Ψ z0 (Work.Cyl.theta x)|
          ≤ 200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
              * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
            + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)| := by
        have h := profile_pth_le hα hα13 hz0pos.le (abs_pos.mpr hθ0) hθmem
          (Work.Cyl.differentiableAt_slice_snd Ψ z0 (Work.Cyl.theta x) hD)
        simpa [Work.Spaces.pth, hΨ] using h
      have hρnn : 0 ≤ (3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ :=
        div_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hρpos.le _)) hBτ.le
      have hb1 : |Ψ z0 (Work.Cyl.theta x)| * (2 / Work.Cyl.radial x)
          ≤ (20 * (3 * α) + N) * (2 / Work.Cyl.radial x) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      have hb2 : 2 * (|Work.Spaces.pz Ψ z0 (Work.Cyl.theta x)|
            * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ))
          ≤ 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ)) := by
        have h := mul_le_mul_of_nonneg_right hpz hρnn
        linarith
      have hb3 : 2 * |Work.Spaces.pth Ψ z0 (Work.Cyl.theta x)| / Work.Cyl.rho x
          ≤ 2 * (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
              + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
              / Work.Cyl.rho x := by
        have h1 := div_le_div_of_nonneg_right hpth hρpos.le
        have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
        rw [← mul_div_assoc, ← mul_div_assoc] at h2
        exact h2
      have hmid0 : ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
            (Work.Cyl.theta y) • Work.Cyl.eTheta y) x‖
          ≤ (20 * (3 * α) + N) * (2 / Work.Cyl.radial x)
            + 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ))
            + 2 * (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
              + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
              / Work.Cyl.rho x := by
        linarith [hstep1, hstep2, hb1, hb2, hb3]
      have hmid : ‖fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
            (Work.Cyl.theta y) • Work.Cyl.eTheta y) x‖
          ≤ (20 * (3 * α) + N) * (2 / Work.Cyl.radial x)
            + 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ)
                + (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                    * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
                  + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
                  / Work.Cyl.rho x) := by
        have hd : 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ))
              + 2 * (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                  * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
                + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
                / Work.Cyl.rho x
            = 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ)
                + (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                    * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
                  + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
                  / Work.Cyl.rho x) := by ring
        linarith [hmid0, hd.le, hd.ge]
      have hpsi : psiBound α A B g τ N Npz L z0 (Work.Cyl.theta x)
          = |(A τ)⁻¹| * ((20 * (3 * α) + N) * (2 / Work.Cyl.radial x)
              + 2 * ((60 * α + Npz) * ((3 * α) * Work.Cyl.rho x ^ (3 * α - 1) / B τ)
                  + (200 * α ^ 2 * (Real.sin (|Work.Cyl.theta x|)) ^ (α - 1)
                      * (Real.cos (Work.Cyl.theta x)) ^ (2 * α - 1)
                    + |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z0 (|Work.Cyl.theta x|)|)
                    / Work.Cyl.rho x)) := by
        rw [psiBound, if_pos hzL, hpow1, hpow2, hcosr]
        ring
      have hsmul : fderiv ℝ (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x
          = (A τ)⁻¹ • fderiv ℝ (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
              (Work.Cyl.theta y) • Work.Cyl.eTheta y) x := by
        rw [hfun]
        rw [show (fun y : R3 => (A τ)⁻¹ • (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
              (Work.Cyl.theta y) • Work.Cyl.eTheta y))
            = (A τ)⁻¹ • (fun y : R3 => Ψ (Work.Cyl.rho y ^ (3 * α) / B τ)
                (Work.Cyl.theta y) • Work.Cyl.eTheta y) from rfl]
        exact fderiv_const_smul hd (A τ)⁻¹
      rw [hpsi, hsmul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hmid (abs_nonneg _)
    · have hd' : ¬ DifferentiableAt ℝ
          (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x := by
        intro hh
        rw [hfun] at hh
        have h2 : DifferentiableAt ℝ (fun y : R3 => (A τ) • ((A τ)⁻¹ •
            (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)
              • Work.Cyl.eTheta y))) x := hh.const_smul (A τ)
        refine hd (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_))
        show Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y) • Work.Cyl.eTheta y
          = (A τ) • ((A τ)⁻¹ • (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)
              • Work.Cyl.eTheta y))
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hAτ), one_smul]
      rw [fderiv_zero_of_not_differentiableAt hd', norm_zero]
      exact psiBound_nonneg α A B g τ N Npz L z0 (Work.Cyl.theta x) (Bpos := hBτ) hN0 hNpz0 hα
        hz0pos.le (le_of_lt hθmem)
  · have hzLt : L < z0 := not_le.mp hzL
    have hfuneq : (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ)
        =ᶠ[𝓝 x] (fun _ => 0) := by
      have hcontz : ContinuousAt (fun y : R3 => Work.Cyl.rho y ^ (3 * α) / B τ) x := by
        have h1 : ContinuousAt (fun y : R3 => Work.Cyl.rho y) x := by
          have hρ : (fun y : R3 => Work.Cyl.rho y) = fun y => ‖y‖ := by
            funext y; exact Work.Cyl.rho_eq_norm y
          rw [hρ]; exact continuous_norm.continuousAt
        have h2 : ContinuousAt (fun y : R3 => Work.Cyl.rho y ^ (3 * α)) x :=
          h1.rpow_const (Or.inl (ne_of_gt hρpos))
        have h3 : ContinuousAt (fun y : R3 => Work.Cyl.rho y ^ (3 * α) * (B τ)⁻¹) x :=
          h2.mul_const _
        simpa [div_eq_mul_inv] using h3
      filter_upwards [hcontz.eventually (IsOpen.mem_nhds isOpen_Ioi hzLt)] with y hy
      show (A τ)⁻¹ • (Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y)
          • Work.Cyl.eTheta y) = 0
      have hzero : Ψ (Work.Cyl.rho y ^ (3 * α) / B τ) (Work.Cyl.theta y) = 0 := by
        have h := profile_eq_zero_of_supp (z := Work.Cyl.rho y ^ (3 * α) / B τ)
          (θ := Work.Cyl.theta y) hsupp (le_of_lt hy)
        simpa [hΨ] using h
      rw [hzero, zero_smul, smul_zero]
    have hzero : fderiv ℝ (fun y : R3 => Work.FTS.Regularity.physVort α A B g y τ) x = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq hfuneq]
      simp [fderiv_const]
    rw [hzero, norm_zero, psiBound, if_neg hzL]

theorem ae_bound_physVort {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.RegPkgGal.RegPkg' α S A B g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {N Npz L : ℝ}
    (hN : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S → |g z θ τ'| ≤ N)
    (hNpz : ∀ z θ τ', 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ' ∈ Set.Icc 0 S →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ') z θ| ≤ Npz)
    (hL : 0 < L) (hsupp : ∀ z θ : ℝ, L ≤ z → Work.FTS.Regularity.profFull α g z θ τ = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      ‖fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) =>
          Work.FTS.Regularity.physVort α A B g y τ) x‖
        ≤ Work.FTS.FireFix.Clauses.psiBound α A B g τ N Npz L
            (Work.Cyl.rho x ^ (3 * α) / B τ) (Work.Cyl.theta x) := by
  have hα := h.hα
  have hα13 := h.hα13
  have hAτ : 0 < A τ := h.hA τ hτ
  have hBτ : 0 < B τ := h.hB τ hτ
  have hIθ0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hτ0 : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
  have hN0 : 0 ≤ N := le_trans (abs_nonneg _) (hN 0 0 0 le_rfl hIθ0 hτ0)
  have hNpz0 : 0 ≤ Npz := le_trans (abs_nonneg _) (hNpz 0 0 0 le_rfl hIθ0 hτ0)
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
    volume_radial_eq_zero volume_axial_eq_zero)
  intro x hx
  by_cases hr : Work.Cyl.radial x = 0
  · exact Or.inl hr
  · by_cases ha : Work.Cyl.axial x = 0
    · exact Or.inr ha
    · exfalso
      have hθ0 : Work.Cyl.theta x ≠ 0 := by
        intro h0
        have h1 : Work.Cyl.axial x / Work.Cyl.radial x = 0 := Real.arctan_eq_zero_iff.mp h0
        rcases div_eq_zero_iff.mp h1 with h2 | h2
        · exact ha h2
        · exact hr h2
      exact hx (physVort_slice_bound (A := A) (B := B) (L := L) hα hα13 hAτ hBτ hN0 hNpz0
        (fun z θ hz hθ => hN z θ τ hz hθ hτ) hNpz (fun θ hθ => h.hcont θ hθ) hτ hsupp
        (lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)) hθ0)

end Work.FTS.FireFix.Clauses
