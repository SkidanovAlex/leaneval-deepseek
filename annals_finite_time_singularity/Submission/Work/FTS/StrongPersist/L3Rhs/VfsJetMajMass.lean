import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassDefs
import Submission.Work.FTS.StrongPersist.L3Aux.GamJetBounds
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux.gamJetMass

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false

/-! ## The `η`-weighted mass of the profile `VfsGc α = Γ/c`

This is the `m = 0` term of `VfsJetMaj`.  It is the easy one: on `Iθ` we have `(Γ/c)² ≤ 100`
(because `0 ≤ Γ ≤ 1` and `1/10 ≤ c ≤ 10`), so the integrand is dominated by `100·sin(2θ)^{-η}`
whose integral is at most `100·10000 = 10^6`. -/

/-- On `Iθ`, `(Γ/c)² ≤ 100` for `0 < α ≤ 1`. -/
private lemma gamGc_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : (VfsGc α θ) ^ 2 ≤ 100 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hdiv : VfsGc α θ ≤ 10 := by
    simp only [VfsGc]
    rw [div_le_iff₀ hcpos]
    nlinarith
  have hdiv0 : 0 ≤ VfsGc α θ := by
    simp only [VfsGc]
    exact div_nonneg hG0 hcpos.le
  nlinarith

/-- **The `η`-weighted mass of `Γ/c`.**  For `0 < α ≤ 1`,
`∫_{Iθ} (Γ/c)² sin(2θ)^{-η} ≤ 10⁶` and the integrand is integrable. -/
private lemma gamGc_eta_mass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 10 ^ 6 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hη1 : -1 < -(Work.Spaces.eta) := by simp only [Work.Spaces.eta]; norm_num
  have hη0 : -(Work.Spaces.eta) ≤ 0 := by simp only [Work.Spaces.eta]; norm_num
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hη1 hη0
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10000 := by
    have heq : 100 / (-(Work.Spaces.eta) + 1) = 10000 := by
      simp only [Work.Spaces.eta]; norm_num
    rwa [heq] at hBdS
  have h100 : MeasureTheory.IntegrableOn
      (fun θ => 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    hIntS.const_mul 100
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _
    have h2 := gamGc_sq_le α hα hα1 hθ
    nlinarith [h2, hX]
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [VfsGc, Work.Spaces.Gam]
    fun_prop
  have hIntf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    h100.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ h2) _))]
      exact h1)
  refine ⟨hIntf, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntf h100 hpt
  calc ∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ, 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := hmono
    _ = 100 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 100 * 10000 := by linarith [hBdS']
    _ = 10 ^ 6 := by norm_num

/-! ## The `α²`-weighted mass of the profile

The middle summand `α²·(Γ/c)²·sin(2θ)^{-γ}` of `VfsJetMaj`.  Here the crude bound
`∫ sin(2θ)^{-γ} = ∞` is fatal, but the vanishing of `Γ` at the endpoints saves it: the
factor `α²` exactly compensates the `1/α` of `∫ sin(2θ)^{17α/30-1} = 3000/(17α)`. -/

/-- On `Iθ` (indeed everywhere), `(Γ/c)² ≤ 100Γ²` for `0 < α ≤ 1`: this is the lower bound
`1/10 ≤ c` of `Work.Spaces.c_bounds`. -/
private lemma gamGc_sq_le_gamSq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    (VfsGc α θ) ^ 2 ≤ 100 * (Work.Spaces.Gam α θ) ^ 2 := by
  obtain ⟨hc1, _⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc2 : (1 / 100 : ℝ) ≤ (Work.Spaces.c α) ^ 2 := by nlinarith [hc1]
  have hmain : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      ≤ 100 * (Work.Spaces.Gam α θ) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (Work.Spaces.c α) ^ 2)]
    nlinarith [hc2, sq_nonneg (Work.Spaces.Gam α θ)]
  simpa only [VfsGc] using hmain

/-- `100·α²·2^{-2α/3}·(3000/(17α)) ≤ 300000/17` for `0 < α ≤ 1`. -/
private lemma alphaMass_arith (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    100 * α ^ 2 * 2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) ≤ 300000 / 17 := by
  have hpow1 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -(2 * α / 3) ≤ 0)
  have hαpow : α * 2 ^ (-(2 * α / 3)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hpow1 hα.le
    rw [mul_one] at h
    linarith [h, hα1]
  have hrew : 100 * α ^ 2 * 2 ^ (-(2 * α / 3)) * (3000 / (17 * α))
      = (300000 / 17) * (α * 2 ^ (-(2 * α / 3))) := by
    field_simp
    ring
  rw [hrew]
  have := mul_le_mul_of_nonneg_left hαpow (by norm_num : (0 : ℝ) ≤ 300000 / 17)
  simpa using this

/-- **The `α²`-weighted `γ`-mass of `Γ/c`.**  For `0 < α ≤ 1` the integrand
`α²(Γ/c)²sin(2θ)^{-γ}` is integrable on `Iθ` with integral at most `300000/17`. -/
private lemma alphaGc_mass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ,
        α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ 300000 / 17 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hp1 : -1 < 17 * α / 30 - 1 := by linarith
  have hp2 : 17 * α / 30 - 1 ≤ 0 := by linarith
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1) hp1 hp2
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hBdS
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 100 * α ^ 2 * 2 ^ (-(2 * α / 3))
          * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    intro θ hθ
    have hT0 := sin_two_nonneg_Iθ hθ
    have hTg : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hT0 _
    have hX2 := gamGc_sq_le_gamSq α hα hα1 θ
    have hG2 := Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
    calc α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ α ^ 2 * (100 * (Work.Spaces.Gam α θ) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX2 (sq_nonneg α)) hTg
      _ = (100 * α ^ 2) * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ ≤ (100 * α ^ 2) * (2 ^ (-(2 * α / 3))
            * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
          mul_le_mul_of_nonneg_left hG2 (by positivity)
      _ = 100 * α ^ 2 * 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by ring
  have hMajInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 100 * α ^ 2 * 2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) Work.Spaces.Iθ := hIntS.const_mul _
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [VfsGc, Work.Spaces.Gam]
    fun_prop
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 100 * α ^ 2 * 2 ^ (-(2 * α / 3))
          * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact hpt θ hθ
  have hf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ := by
    refine hMajInt.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg _))
      (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))]
    exact hpt θ hθ
  refine ⟨hf, ?_⟩
  calc ∫ θ in Work.Spaces.Iθ,
        α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ, 100 * α ^ 2 * 2 ^ (-(2 * α / 3))
          * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) :=
        MeasureTheory.integral_mono_ae hf hMajInt hae
    _ = (100 * α ^ 2 * 2 ^ (-(2 * α / 3)))
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (100 * α ^ 2 * 2 ^ (-(2 * α / 3))) * (3000 / (17 * α)) :=
        mul_le_mul_of_nonneg_left hBdS' (by positivity)
    _ ≤ 300000 / 17 := alphaMass_arith α hα hα1

/-! ## The `γ`-weighted jet sum -/

/-- The `γ`-weighted jet sum `VfsJetSum α` is integrable and its integral is at most
`4·10^15`, given the four individual mass bounds. -/
private lemma jetSum_mass (α : ℝ)
    (hGam : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 10 ^ 15) :
    MeasureTheory.IntegrableOn (VfsJetSum α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, VfsJetSum α θ) ≤ 4 * 10 ^ 15 := by
  have hmem : ∀ i ∈ Finset.Icc 1 4, 1 ≤ i ∧ i ≤ 4 := fun i hi => Finset.mem_Icc.mp hi
  have hInt : MeasureTheory.IntegrableOn (VfsJetSum α) Work.Spaces.Iθ :=
    integrable_finsetSum (Finset.Icc 1 4)
      (fun i hi => (hGam i (hmem i hi).1 (hmem i hi).2).1)
  refine ⟨hInt, ?_⟩
  have hsum : (∫ θ in Work.Spaces.Iθ, VfsJetSum α θ)
      = ∑ i ∈ Finset.Icc 1 4,
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    integral_finsetSum (Finset.Icc 1 4)
      (fun i hi => (hGam i (hmem i hi).1 (hmem i hi).2).1)
  rw [hsum]
  calc ∑ i ∈ Finset.Icc 1 4,
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ ∑ _i ∈ Finset.Icc 1 4, (10 ^ 15 : ℝ) :=
        Finset.sum_le_sum (fun i hi => (hGam i (hmem i hi).1 (hmem i hi).2).2)
    _ = 4 * 10 ^ 15 := by
        rw [Finset.sum_const, Nat.card_Icc]
        norm_num

/-! ## The target -/

-- `VfsJetMajMass`: the `α`-uniform angular mass of the extended majorant `VfsJetMaj` of `Γ/c`.
-- Intended namespace `Work.FTS.StrongPersist.L3Rhs`
-- (file `Submission/Work/FTS/StrongPersist/L3Rhs/VfsJetMajMass.lean`).
-- Route: `VfsJetMaj α θ = (X θ)²T^{-η} + α²(X θ)²T^{-γ} + Σ_{1≤m≤4}(dthU^[m]X θ)²T^{-γ}` with
-- `X = VfsGc α = Γ/c`, `T θ = sin(2θ)`.  The first and third groups are bounded (as
-- `IntegrableOn` and as integrals) by `10^15` via `Work.FTS.StrongPersist.L3Aux.GamJetBounds`
-- (bridge with `Work.FTS.LocData.DthIter_rad_eq`); the middle group satisfies
-- `α²X²T^{-γ} ≤ 100α²Γ²T^{-γ} ≤ 100α²2^{-2α/3}T^{17α/30-1}` and its integral is at most
-- `100·α²·3000/(17α) = 300000α/17 ≤ 300000/17` (`Work.Spaces.c_bounds`,
-- `Work.FTS.LocData.GamSq_sin_neg_gam_le`, `Work.Spaces.sin_two_rpow`).
theorem VfsJetMajMass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.L3Rhs.VfsJetMaj α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Rhs.VfsJetMaj α θ) ≤ 10 ^ 16 := by
  obtain ⟨hEtaInt, hEtaBd⟩ := gamGc_eta_mass α hα hα1
  -- `Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux.gamJetMass`
  have hGam : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 10 ^ 15 :=
    fun i hi1 hi4 => VfsJetMassAux.gamJetMass α hα hα1 i hi1 hi4
  -- `Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux.alphaJetMass` is *not* imported: that module
  -- defines a helper `VfsGc_sq_le` clashing with the sibling `gamJetMass` module's helper of
  -- the same name (both live in `Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux`), so the two
  -- cannot be imported into one environment.  The `α²`-mass is proved locally instead
  -- (`alphaGc_mass`).
  obtain ⟨hAlInt, hAlBd⟩ := alphaGc_mass α hα hα1
  obtain ⟨hJsInt, hJsBd⟩ := jetSum_mass α hGam
  refine ⟨?_, ?_⟩
  · show MeasureTheory.IntegrableOn
      (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + VfsJetSum α θ) Work.Spaces.Iθ
    exact (hEtaInt.add hAlInt).add hJsInt
  · have hSplit : (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ)
        = (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∫ θ in Work.Spaces.Iθ,
              α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          + (∫ θ in Work.Spaces.Iθ, VfsJetSum α θ) := by
      have hfun : ((fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          = (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + fun θ : ℝ => α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        funext θ; rfl
      have hAB : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          Work.Spaces.Iθ := by
        simpa only [hfun] using hEtaInt.add hAlInt
      have h1 : (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ)
          = (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            + (∫ θ in Work.Spaces.Iθ, VfsJetSum α θ) :=
        MeasureTheory.integral_add hAB hJsInt
      have h2 : (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ,
                α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        MeasureTheory.integral_add hEtaInt hAlInt
      rw [h1, h2]
    rw [hSplit]
    have harith : (10 : ℝ) ^ 6 + 300000 / 17 + 4 * 10 ^ 15 ≤ 10 ^ 16 := by norm_num
    linarith [hEtaBd, hAlBd, hJsBd, harith]

end Work.FTS.StrongPersist.L3Rhs
