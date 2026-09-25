/-
# Moser iteration: interior sup bound from the weighted power Caccioppoli inequality
-/
import Mathlib
import Submission.Work.NN.Core.jholoEnergy
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.gagliardoNirenbergGeomMean
import Submission.Work.NN.Core.Lev.nnGradBoundPoint
import Submission.Work.NN.Core.Lev.exists_polydisc_cutoff_lipschitz
import Submission.Work.NN.Core.contDiff_one_mul_of_support
import Submission.Work.NN.Core.ofReal_norm_le_liminf_eLpNorm
import Submission.Work.NN.Core.moserProductBound
import Submission.Work.NN.Core.volume_polydisc
import Submission.Work.NN.Core.Value.eLpNorm_interp

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter

namespace Work.NN.Core.Value

variable {n : ℕ}

/-- The polydisc of multiradius `r` centred at the origin. -/
abbrev Pd (r : Fin n → ℝ) : Set (Work.NN.Core.Cn n) := Work.CR.Flat.polydisc 0 r

@[simp] lemma mem_Pd {r : Fin n → ℝ} {z : Work.NN.Core.Cn n} : z ∈ Pd r ↔ ∀ j, ‖z j‖ < r j := by
  simp [Work.CR.Flat.mem_polydisc]

/-- The closed polydisc of multiradius `R` is contained in any polydisc of strictly larger
multiradius. -/
lemma closedPolydisc_subset_Pd {R ρ : Fin n → ℝ} (h : ∀ j, R j < ρ j) :
    {z : Work.NN.Core.Cn n | ∀ j, ‖z j‖ ≤ R j} ⊆ Pd ρ := by
  intro z hz
  rw [mem_Pd]
  exact fun j => lt_of_le_of_lt (hz j) (h j)

/-- The closed polydisc of multiradius `r` centred at the origin. -/
abbrev CPd (r : Fin n → ℝ) : Set (Work.NN.Core.Cn n) := {z | ∀ j, ‖z j‖ ≤ r j}

lemma CPd_mono {r r' : Fin n → ℝ} (h : ∀ j, r j ≤ r' j) : CPd r ⊆ CPd r' :=
  fun _ hz j => le_trans (hz j) (h j)

lemma Pd_subset_CPd (r : Fin n → ℝ) : Pd r ⊆ CPd r := by
  intro z hz
  rw [mem_Pd] at hz
  exact fun j => le_of_lt (hz j)

/-- The closed polydisc `{z | ∀ j, ‖z j‖ ≤ R j}` is closed. -/
lemma isClosed_closedPolydisc (R : Fin n → ℝ) :
    IsClosed {z : Work.NN.Core.Cn n | ∀ j, ‖z j‖ ≤ R j} := by
  have h : {z : Work.NN.Core.Cn n | ∀ j, ‖z j‖ ≤ R j}
      = ⋂ j, {z : Work.NN.Core.Cn n | ‖z j‖ ≤ R j} := by ext z; simp
  rw [h]
  exact isClosed_iInter fun j => isClosed_le ((continuous_apply j).norm) continuous_const

/-- The topological support of a function vanishing outside the open polydisc of multiradius `S`
is contained in the closed polydisc of multiradius `S`. -/
lemma tsupport_subset_CPd {S : Fin n → ℝ} {χ : Work.NN.Core.Cn n → ℝ}
    (hχ : ∀ z, (∃ j, S j ≤ ‖z j‖) → χ z = 0) : tsupport χ ⊆ CPd S := by
  have hsupp : Function.support χ ⊆ Pd S := by
    intro z hz
    rw [Function.mem_support] at hz
    rw [mem_Pd]
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hj⟩ := hcon
    exact hz (hχ z ⟨j, hj⟩)
  calc tsupport χ = closure (Function.support χ) := rfl
    _ ⊆ closure (Pd S) := closure_mono hsupp
    _ ⊆ CPd S := closure_minimal (Pd_subset_CPd S) (isClosed_closedPolydisc S)

/-- A function vanishing outside the open polydisc of multiradius `S` has its topological support
inside every polydisc of strictly larger multiradius. -/
lemma tsupport_subset_Pd {S ρ : Fin n → ℝ} (hSρ : ∀ j, S j < ρ j)
    {χ : Work.NN.Core.Cn n → ℝ} (hχ : ∀ z, (∃ j, S j ≤ ‖z j‖) → χ z = 0) :
    tsupport χ ⊆ Pd ρ := by
  set ρ' : Fin n → ℝ := fun j => (S j + ρ j) / 2 with hρ'def
  have hSρ' : ∀ j, S j < ρ' j := fun j => by simp only [hρ'def]; linarith [hSρ j]
  have hρ'ρ : ∀ j, ρ' j < ρ j := fun j => by simp only [hρ'def]; linarith [hSρ j]
  have hsupp : Function.support χ ⊆ Pd ρ' := by
    intro z hz
    rw [Function.mem_support] at hz
    rw [mem_Pd]
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hj⟩ := hcon
    exact hz (hχ z ⟨j, le_trans (le_of_lt (hSρ' j)) hj⟩)
  calc tsupport χ = closure (Function.support χ) := rfl
    _ ⊆ closure (Pd ρ') := closure_mono hsupp
    _ ⊆ {z : Work.NN.Core.Cn n | ∀ j, ‖z j‖ ≤ ρ' j} :=
        closure_minimal (fun z hz => by rw [mem_Pd] at hz; exact fun j => le_of_lt (hz j))
          (isClosed_closedPolydisc ρ')
    _ ⊆ Pd ρ := closedPolydisc_subset_Pd hρ'ρ

/-- A function that is continuous on a compact set and vanishes outside it is integrable. -/
lemma integrable_of_continuousOn_of_support {K : Set (Work.NN.Core.Cn n)} (hK : IsCompact K)
    {F : Work.NN.Core.Cn n → ℝ} (hF : ContinuousOn F K)
    (hsupp : Function.support F ⊆ K) : Integrable F volume := by
  have hmeas : MeasurableSet K := hK.isClosed.measurableSet
  have h1 : IntegrableOn F K volume := ContinuousOn.integrableOn_compact hK hF
  have h2 : Integrable (K.indicator F) volume := h1.integrable_indicator hmeas
  have h3 : K.indicator F = F := by
    funext z
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz]
    · have hz0 : F z = 0 := by
        by_contra h
        exact hz (hsupp (Function.mem_support.mpr h))
      rw [Set.indicator_of_notMem hz, hz0]
  rwa [h3] at h2



/-! ## Auxiliary continuity facts -/

lemma continuousOn_dCoord {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) (j : Fin n) :
    ContinuousOn (fun z => Work.CR.Flat.dCoord j u z) (Pd ρ) := by
  have hfd : ContinuousOn (fderiv ℝ u) (Pd ρ) :=
    hu.continuousOn_fderiv_of_isOpen (Work.CR.Flat.isOpen_polydisc 0 ρ) le_rfl
  have h1 : ContinuousOn (fun z => fderiv ℝ u z (Pi.single j (1 : ℂ))) (Pd ρ) :=
    hfd.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun z => fderiv ℝ u z (Pi.single j (Complex.I : ℂ))) (Pd ρ) :=
    hfd.clm_apply continuousOn_const
  have h3 : ContinuousOn (fun z => (1/2 : ℂ) * fderiv ℝ u z (Pi.single j (1 : ℂ))
      - (1/2 : ℂ) * Complex.I * fderiv ℝ u z (Pi.single j (Complex.I : ℂ))) (Pd ρ) :=
    ((continuousOn_const.mul h1).sub (continuousOn_const.mul h2))
  refine h3.congr fun z _ => ?_
  rw [Work.CR.Flat.dCoord]
  ring

lemma continuousOn_dbarCoord {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) (j : Fin n) :
    ContinuousOn (fun z => Work.CR.Flat.dbarCoord j u z) (Pd ρ) := by
  have hfd : ContinuousOn (fderiv ℝ u) (Pd ρ) :=
    hu.continuousOn_fderiv_of_isOpen (Work.CR.Flat.isOpen_polydisc 0 ρ) le_rfl
  have h1 : ContinuousOn (fun z => fderiv ℝ u z (Pi.single j (1 : ℂ))) (Pd ρ) :=
    hfd.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun z => fderiv ℝ u z (Pi.single j (Complex.I : ℂ))) (Pd ρ) :=
    hfd.clm_apply continuousOn_const
  have h3 : ContinuousOn (fun z => (1/2 : ℂ) * fderiv ℝ u z (Pi.single j (1 : ℂ))
      + (1/2 : ℂ) * Complex.I * fderiv ℝ u z (Pi.single j (Complex.I : ℂ))) (Pd ρ) :=
    ((continuousOn_const.mul h1).add (continuousOn_const.mul h2))
  refine h3.congr fun z _ => ?_
  rw [Work.CR.Flat.dbarCoord]
  ring

/-- The weighted energy density `‖u‖^{2k-2} Σ_j (‖∂_j u‖² + ‖∂̄_j u‖²)` is continuous on the
polydisc, for `u` of class `C¹` there and `k ≥ 1`. -/
lemma continuousOn_weightedEnergy {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) {k : ℕ} (hk : 1 ≤ k) :
    ContinuousOn (fun z => ‖u z‖ ^ (2*(k:ℝ) - 2) *
      ∑ j, (‖Work.CR.Flat.dCoord j u z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2)) (Pd ρ) := by
  have hexp : ((2 * (k - 1) : ℕ) : ℝ) = 2*(k:ℝ) - 2 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]; ring
  have hnorm : ContinuousOn (fun z => ‖u z‖ ^ (2*(k:ℝ) - 2)) (Pd ρ) := by
    have h1 : ContinuousOn (fun z => ‖u z‖ ^ (k - 1)) (Pd ρ) := hu.continuousOn.norm.pow (k-1)
    have h2 : ContinuousOn (fun z => (‖u z‖ ^ (k - 1)) ^ 2) (Pd ρ) := h1.pow 2
    have hfun : (fun z => ‖u z‖ ^ (2*(k:ℝ) - 2)) = fun z => (‖u z‖ ^ (k - 1)) ^ 2 := by
      funext z
      rw [← hexp, Real.rpow_natCast, ← pow_mul']
    rw [hfun]
    exact h2
  refine hnorm.mul ?_
  exact continuousOn_finsetSum _ (fun j _ =>
    ((continuousOn_dCoord hu j).norm.pow 2).add ((continuousOn_dbarCoord hu j).norm.pow 2))

/-- The weighted energy density times `χ²` is integrable, for `χ` smooth and compactly supported
inside the polydisc where `u` is `C¹`. -/
lemma integrable_chi_weightedEnergy {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) {k : ℕ} (hk : 1 ≤ k) {χ : Work.NN.Core.Cn n → ℝ}
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Pd ρ) :
    Integrable (fun z => (χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) *
      ∑ j, (‖Work.CR.Flat.dCoord j u z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2))) volume := by
  refine integrable_of_continuousOn_of_support hχcs.isCompact ?_ ?_
  · have hχcont : ContinuousOn (fun z => (χ z)^2) (tsupport χ) :=
      (hχcd.continuous.continuousOn).pow 2
    exact hχcont.mul ((continuousOn_weightedEnergy hu hk).mono hχsupp)
  · intro z hz
    rw [Function.mem_support] at hz
    refine subset_tsupport χ ?_
    rw [Function.mem_support]
    intro h0
    exact hz (by rw [h0]; ring)


/-- A function whose topological support lies in a polydisc vanishes outside it. -/
lemma eq_zero_of_not_mem_Pd {ρ : Fin n → ℝ} {χ : Work.NN.Core.Cn n → ℝ}
    (hχsupp : tsupport χ ⊆ Pd ρ) {z : Work.NN.Core.Cn n} (hz : z ∉ Pd ρ) : χ z = 0 :=
  Function.notMem_support.mp fun h => hz (hχsupp (subset_tsupport χ h))

/-- The energy density sum `Σ_j (‖∂_j u‖² + ‖∂̄_j u‖²)`. -/
abbrev energySum (u : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n) : ℝ :=
  ∑ j, (‖Work.CR.Flat.dCoord j u z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j u z‖ ^ 2)

/-- **Power Caccioppoli inequality.**  From the level-`k` weighted energy inequality (the
hypothesis at `γ = k`) one obtains the Caccioppoli inequality for the power `u^k`, with constant
`Cg k² C₀` where `Cg` controls the real differential by the Wirtinger derivatives. -/
theorem pow_caccioppoli {n : ℕ} {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) {k : ℕ} (hk : 1 ≤ k)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg)
    (hCg : ∀ z, ‖fderiv ℝ u z‖ ^ 2 ≤ Cg * energySum u z)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    {χ : Work.NN.Core.Cn n → ℝ} (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Pd ρ) (hχnn : ∀ z, 0 ≤ χ z)
    (hlev : ∫ z in Pd ρ, (χ z)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z
        ≤ C₀ * ∫ z in Pd ρ, ‖fderiv ℝ χ z‖^2 * ‖u z‖ ^ (2*(k:ℝ))) :
    ∫ z in Pd ρ, (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2
      ≤ (Cg * (k:ℝ)^2 * C₀) * ∫ z in Pd ρ, ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k := by
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkrpow : ∀ z, (‖u z‖ ^ 2) ^ k = ‖u z‖ ^ (2*(k:ℝ)) := by
    intro z
    have h2 : (2*(k:ℝ) : ℝ) = ((2*k : ℕ) : ℝ) := by push_cast; ring
    rw [h2, Real.rpow_natCast, pow_mul]
  have hexp : ∀ z, ‖u z‖ ^ (2*(k:ℝ) - 2) = (‖u z‖ ^ (k-1))^2 := by
    intro z
    have h2 : (2*(k:ℝ) - 2 : ℝ) = ((2*(k-1) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]; ring
    rw [h2, Real.rpow_natCast, ← pow_mul']
  -- ### the pointwise comparison
  have hpt : ∀ z, (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2
      ≤ (Cg * (k:ℝ)^2) * ((χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z)) := by
    intro z
    by_cases hz : z ∈ Pd ρ
    · have hd : DifferentiableAt ℝ u z :=
        (hu.differentiableOn one_ne_zero).differentiableAt
          ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hz)
      have hpow : fderiv ℝ (fun w => (u w)^k) z = ((k:ℂ) * (u z)^(k-1)) • fderiv ℝ u z := by
        rw [fderiv_fun_pow k hd, nsmul_eq_mul]
      have hnorm : ‖fderiv ℝ (fun w => (u w)^k) z‖
          = (k:ℝ) * ‖u z‖^(k-1) * ‖fderiv ℝ u z‖ := by
        rw [hpow, norm_smul, norm_mul, Complex.norm_natCast, norm_pow]
      have hsq : ‖fderiv ℝ (fun w => (u w)^k) z‖^2
          = (k:ℝ)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2)) * ‖fderiv ℝ u z‖^2 := by
        rw [hnorm, hexp z]
        ring
      have hstep : (χ z)^2 * ((k:ℝ)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * ‖fderiv ℝ u z‖^2))
          ≤ (χ z)^2 * ((k:ℝ)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * (Cg * energySum u z))) := by
        have hnn : 0 ≤ (χ z)^2 * ((k:ℝ)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2)) := by positivity
        have h2 := mul_le_mul_of_nonneg_left (hCg z) hnn
        calc (χ z)^2 * ((k:ℝ)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * ‖fderiv ℝ u z‖^2))
            = ((χ z)^2 * ((k:ℝ)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2))) * ‖fderiv ℝ u z‖^2 := by ring
          _ ≤ ((χ z)^2 * ((k:ℝ)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2))) * (Cg * energySum u z) := h2
          _ = (χ z)^2 * ((k:ℝ)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * (Cg * energySum u z))) := by ring
      calc (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2
          = (χ z)^2 * ((k:ℝ)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * ‖fderiv ℝ u z‖^2)) := by
            rw [hsq]; ring
        _ ≤ (χ z)^2 * ((k:ℝ)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * (Cg * energySum u z))) := hstep
        _ = (Cg * (k:ℝ)^2) * ((χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z)) := by
            ring
    · have hz0 : χ z = 0 := eq_zero_of_not_mem_Pd hχsupp hz
      rw [hz0]
      have : (0:ℝ)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2 = 0 := by ring
      rw [this]
      positivity
  -- ### integrability of the majorant
  have hInt : Integrable (fun z => (Cg * (k:ℝ)^2) *
      ((χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z))) volume :=
    (integrable_chi_weightedEnergy hu hk hχcd hχcs hχsupp).const_mul _
  -- ### the integral comparison
  have hmono : ∫ z in Pd ρ, (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2
      ≤ ∫ z in Pd ρ, (Cg * (k:ℝ)^2) *
          ((χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z)) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_)
      (hInt.mono_measure Measure.restrict_le_self)
      (Eventually.of_forall fun z => hpt z)
    positivity
  have hcongr : ∫ z in Pd ρ, (Cg * (k:ℝ)^2) *
        ((χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z))
      = (Cg * (k:ℝ)^2) *
        ∫ z in Pd ρ, (χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z) :=
    integral_const_mul _ _
  have hcongr2 : ∫ z in Pd ρ, (χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z)
      = ∫ z in Pd ρ, (χ z)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z :=
    integral_congr_ae (Eventually.of_forall fun z => by ring)
  have hcongr3 : ∫ z in Pd ρ, ‖fderiv ℝ χ z‖^2 * ‖u z‖ ^ (2*(k:ℝ))
      = ∫ z in Pd ρ, ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k :=
    integral_congr_ae (Eventually.of_forall fun z => by simp only [← hkrpow z])
  have hmul : (Cg * (k:ℝ)^2) *
        ∫ z in Pd ρ, (χ z)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z
      ≤ (Cg * (k:ℝ)^2) * (C₀ * ∫ z in Pd ρ, ‖fderiv ℝ χ z‖^2 * ‖u z‖ ^ (2*(k:ℝ))) :=
    mul_le_mul_of_nonneg_left hlev (by positivity)
  calc ∫ z in Pd ρ, (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2
      ≤ ∫ z in Pd ρ, (Cg * (k:ℝ)^2) *
          ((χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z)) := hmono
    _ = (Cg * (k:ℝ)^2) *
        ∫ z in Pd ρ, (χ z)^2 * (‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z) := hcongr
    _ = (Cg * (k:ℝ)^2) *
        ∫ z in Pd ρ, (χ z)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z := by rw [hcongr2]
    _ ≤ (Cg * (k:ℝ)^2) * (C₀ * ∫ z in Pd ρ, ‖fderiv ℝ χ z‖^2 * ‖u z‖ ^ (2*(k:ℝ))) := hmul
    _ = (Cg * (k:ℝ)^2 * C₀) * ∫ z in Pd ρ, ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k := by
        rw [hcongr3]; ring


/-! ## Integrability and the lintegral form of the power Caccioppoli inequality -/

/-- `‖x‖ₑ ^ 2 = ofReal (‖x‖ ^ 2)`. -/
lemma enorm_rpow_two_eq {E : Type*} [SeminormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_cast

/-- `(eLpNorm f 2 μ) ^ 2 = ∫⁻ ‖f‖ₑ ^ 2`. -/
lemma eLpNorm_two_sq_eq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ) ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by simp) hf,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- `(‖u z‖ ^ 2) ^ k = ‖u z‖ ^ (2 k)` (with the real exponent `2 k` on the right). -/
lemma norm_sq_pow_eq (u : Work.NN.Core.Cn n → ℂ) (k : ℕ) (z : Work.NN.Core.Cn n) :
    (‖u z‖ ^ 2) ^ k = ‖u z‖ ^ (2 * (k : ℝ)) := by
  have h2 : (2 * (k : ℝ) : ℝ) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
  rw [h2, Real.rpow_natCast, pow_mul]

/-- `‖u z‖ ^ (2k-2) = (‖u z‖ ^ (k-1)) ^ 2` for `k ≥ 1`. -/
lemma norm_rpow_eq_sq (u : Work.NN.Core.Cn n → ℂ) {k : ℕ} (hk : 1 ≤ k)
    (z : Work.NN.Core.Cn n) :
    ‖u z‖ ^ (2 * (k : ℝ) - 2) = (‖u z‖ ^ (k - 1)) ^ 2 := by
  have h2 : (2 * (k : ℝ) - 2 : ℝ) = ((2 * (k - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]; ring
  rw [h2, Real.rpow_natCast, ← pow_mul']

lemma continuousOn_fderiv_pow {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) (k : ℕ) :
    ContinuousOn (fderiv ℝ (fun w => (u w) ^ k)) (Pd ρ) :=
  (hu.pow k).continuousOn_fderiv_of_isOpen (Work.CR.Flat.isOpen_polydisc 0 ρ) le_rfl

/-- `χ² ‖∇(u^k)‖²` is integrable for `χ` smooth and compactly supported inside the polydisc. -/
lemma integrable_chi_gradpow {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) (k : ℕ) {χ : Work.NN.Core.Cn n → ℝ}
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Pd ρ) :
    Integrable (fun z => (χ z) ^ 2 * ‖fderiv ℝ (fun w => (u w) ^ k) z‖ ^ 2) volume := by
  refine integrable_of_continuousOn_of_support hχcs.isCompact ?_ ?_
  · exact ((hχcd.continuous.continuousOn).pow 2).mul
      (((continuousOn_fderiv_pow hu k).mono hχsupp).norm.pow 2)
  · intro z hz
    rw [Function.mem_support] at hz
    refine subset_tsupport χ (Function.mem_support.mpr ?_)
    intro h0
    exact hz (by rw [h0]; ring)

/-- `‖∇χ‖² (‖u‖²)^k` is integrable for `χ` smooth and compactly supported inside the polydisc. -/
lemma integrable_gradchi_pow {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) (k : ℕ) {χ : Work.NN.Core.Cn n → ℝ}
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Pd ρ) :
    Integrable (fun z => ‖fderiv ℝ χ z‖ ^ 2 * (‖u z‖ ^ 2) ^ k) volume := by
  refine integrable_of_continuousOn_of_support hχcs.isCompact ?_ ?_
  · have h1 : ContinuousOn (fun z => ‖fderiv ℝ χ z‖ ^ 2) (tsupport χ) :=
      ((hχcd.continuous_fderiv (by norm_num)).continuousOn).norm.pow 2
    have h2 : ContinuousOn (fun z => (‖u z‖ ^ 2) ^ k) (tsupport χ) :=
      ((hu.continuousOn.norm.pow 2).pow k).mono hχsupp
    exact h1.mul h2
  · intro z hz
    by_contra hzts
    have hdf : fderiv ℝ χ z = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq (tsupport_compl_eventuallyEq_zero hzts)]
      simp
    rw [Function.mem_support] at hz
    exact hz (by rw [hdf]; simp)

/-- **Power Caccioppoli inequality in lintegral form.** -/
theorem pow_caccioppoli_lint {n : ℕ} {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) {k : ℕ} (hk : 1 ≤ k)
    {Cg : ℝ} (hCg0 : 0 ≤ Cg)
    (hCg : ∀ z, ‖fderiv ℝ u z‖ ^ 2 ≤ Cg * energySum u z)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    {χ : Work.NN.Core.Cn n → ℝ} (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Pd ρ) (hχnn : ∀ z, 0 ≤ χ z)
    (hlev : ∫ z in Pd ρ, (χ z)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2) * energySum u z
        ≤ C₀ * ∫ z in Pd ρ, ‖fderiv ℝ χ z‖ ^ 2 * ‖u z‖ ^ (2*(k:ℝ))) :
    ∫⁻ z in Pd ρ, ENNReal.ofReal ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)
      ≤ ENNReal.ofReal (Cg * (k:ℝ)^2 * C₀) *
        ∫⁻ z in Pd ρ, ENNReal.ofReal (‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) := by
  have hL := integrable_chi_gradpow hu k hχcd hχcs hχsupp
  have hR := integrable_gradchi_pow hu k hχcd hχcs hχsupp
  have e1 := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Pd ρ))
    (f := fun z => (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)
    (hL.mono_measure Measure.restrict_le_self) (Eventually.of_forall fun z => by positivity)
  have e2 := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Pd ρ))
    (f := fun z => ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k)
    (hR.mono_measure Measure.restrict_le_self) (Eventually.of_forall fun z => by positivity)
  have hmain := pow_caccioppoli (ρ := ρ) hu hk hCg0 hCg hC₀ hχcd hχcs hχsupp hχnn hlev
  calc ∫⁻ z in Pd ρ, ENNReal.ofReal ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)
      = ENNReal.ofReal (∫ z in Pd ρ, (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2) := e1.symm
    _ ≤ ENNReal.ofReal ((Cg * (k:ℝ)^2 * C₀) *
          ∫ z in Pd ρ, ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) := ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (Cg * (k:ℝ)^2 * C₀) *
          ∫⁻ z in Pd ρ, ENNReal.ofReal (‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) := by
        rw [ENNReal.ofReal_mul (by positivity), e2]


/-! ## Auxiliary lemmas for the Moser boost -/

/-- `(eLpNorm f 2 μ) ^ 2 = ∫⁻ ofReal ‖f‖ ^ 2`. -/
lemma eLpNorm_two_sq_eq_lintegral_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Type*} [NormedAddCommGroup E] {f : α → E} (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ) ^ (2 : ℝ) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [eLpNorm_two_sq_eq_lintegral hf]
  exact lintegral_congr fun x => enorm_rpow_two_eq (f x)

/-- `eLpNorm` is insensitive to the restriction to a set outside which the function vanishes. -/
lemma eLpNorm_eq_restrict_of_support {s : Set (Work.NN.Core.Cn n)} (hs : MeasurableSet s)
    {f : Work.NN.Core.Cn n → ℂ} (hf : ∀ z ∉ s, f z = 0) (p : ENNReal) :
    eLpNorm f p volume = eLpNorm f p (volume.restrict s) := by
  have h : s.indicator f = f := by
    funext z
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hf z hz]
  calc eLpNorm f p volume = eLpNorm (s.indicator f) p volume := by rw [h]
    _ = eLpNorm f p (volume.restrict s) := MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hs

/-- Bridge: the real Fréchet derivative of `χ` is no larger than that of its complexification. -/
lemma norm_fderiv_le_ofReal_complex {χ : Work.NN.Core.Cn n → ℝ} (z : Work.NN.Core.Cn n) :
    ‖fderiv ℝ χ z‖ ≤ ‖fderiv ℝ (fun y => (χ y : ℂ)) z‖ := by
  by_cases hd : DifferentiableAt ℝ (fun y : Work.NN.Core.Cn n => (χ y : ℂ)) z
  · obtain ⟨L, hL⟩ := hd
    have hfun : (fun y : Work.NN.Core.Cn n => Complex.reCLM (χ y : ℂ)) = χ := by
      funext y; simp
    have h2 : HasFDerivAt (fun y : Work.NN.Core.Cn n => Complex.reCLM (χ y : ℂ))
        ((Complex.reCLM : ℂ →L[ℝ] ℝ).comp L) z := Complex.reCLM.hasFDerivAt.comp z hL
    rw [hfun] at h2
    rw [h2.fderiv, hL.fderiv]
    calc ‖(Complex.reCLM : ℂ →L[ℝ] ℝ).comp L‖ ≤ ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ * ‖L‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖L‖ := by rw [Complex.reCLM_norm, one_mul]
  · have hnd : ¬ DifferentiableAt ℝ χ z := by
      intro h
      refine hd ?_
      have h2 : (fun y : Work.NN.Core.Cn n => (χ y : ℂ))
          = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ χ := rfl
      rw [h2]
      exact Complex.ofRealCLM.differentiableAt.comp z h
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd,
      norm_zero, norm_zero]

/-- The complexification of a real function does not change the norm of the Fréchet derivative. -/
lemma norm_fderiv_ofReal_eq {χ : Work.NN.Core.Cn n → ℝ} (z : Work.NN.Core.Cn n) :
    ‖fderiv ℝ (fun y => (χ y : ℂ)) z‖ = ‖fderiv ℝ χ z‖ := by
  refine le_antisymm ?_ (norm_fderiv_le_ofReal_complex z)
  by_cases hd : DifferentiableAt ℝ χ z
  · exact Work.NN.Core.norm_fderiv_ofReal_le hd
  · have hnd : ¬ DifferentiableAt ℝ (fun y : Work.NN.Core.Cn n => (χ y : ℂ)) z := by
      intro h
      refine hd ?_
      have h3 : DifferentiableAt ℝ
          (fun y : Work.NN.Core.Cn n =>
            Complex.reCLM ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ) (χ y))) z :=
        Complex.reCLM.differentiableAt.comp z h
      exact h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp)
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd,
      norm_zero, norm_zero]

/-- **Pointwise bound for the Moser boost.**  With `W = χ · u^k` and `χ` supported in
`polydisc 0 S`, at every point

`‖D W‖² ≤ 2 ‖u‖^{2k} L² + 2 χ² ‖D(u^k)‖²`. -/
lemma boost_pointwise {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Pd ρ)) {k : ℕ} {χ : Work.NN.Core.Cn n → ℝ}
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχsupp : tsupport χ ⊆ Pd ρ)
    (hχnn : ∀ z, 0 ≤ χ z) (z : Work.NN.Core.Cn n) :
    ‖fderiv ℝ (fun y => (χ y : ℂ) * (u y)^k) z‖ ^ 2
      ≤ 2 * (‖u z‖ ^ 2)^k * ‖fderiv ℝ χ z‖ ^ 2
        + 2 * (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖ ^ 2 := by
  by_cases hz : z ∈ Pd ρ
  · have hd : DifferentiableAt ℝ (fun w => (u w)^k) z :=
      ((hu.pow k).differentiableOn one_ne_zero).differentiableAt
        ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hz)
    have hdc : DifferentiableAt ℝ (fun w : Work.NN.Core.Cn n => (χ w : ℂ)) z :=
      Complex.ofRealCLM.differentiableAt.comp z ((hχcd.differentiable (by simp)).differentiableAt)
    have hfd : fderiv ℝ (fun y : Work.NN.Core.Cn n => (χ y : ℂ) * (u y)^k) z
        = (u z)^k • fderiv ℝ (fun w : Work.NN.Core.Cn n => (χ w : ℂ)) z
          + (χ z : ℂ) • fderiv ℝ (fun w => (u w)^k) z := by
      rw [fderiv_fun_mul hdc hd, add_comm]
    have hnorm : ‖fderiv ℝ (fun y : Work.NN.Core.Cn n => (χ y : ℂ) * (u y)^k) z‖
        ≤ ‖u z‖^k * ‖fderiv ℝ χ z‖ + χ z * ‖fderiv ℝ (fun w => (u w)^k) z‖ := by
      rw [hfd]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_smul, norm_smul, norm_pow, Complex.norm_of_nonneg (hχnn z),
        norm_fderiv_ofReal_eq z]
    have h2 : ‖fderiv ℝ (fun y : Work.NN.Core.Cn n => (χ y : ℂ) * (u y)^k) z‖ ^ 2
        ≤ 2 * (‖u z‖^k * ‖fderiv ℝ χ z‖)^2
          + 2 * (χ z * ‖fderiv ℝ (fun w => (u w)^k) z‖)^2 := by
      have hsq : (‖u z‖^k * ‖fderiv ℝ χ z‖ + χ z * ‖fderiv ℝ (fun w => (u w)^k) z‖)^2
          ≤ 2*(‖u z‖^k * ‖fderiv ℝ χ z‖)^2
            + 2*(χ z * ‖fderiv ℝ (fun w => (u w)^k) z‖)^2 := by
        nlinarith [sq_nonneg (‖u z‖^k * ‖fderiv ℝ χ z‖
        - χ z * ‖fderiv ℝ (fun w => (u w)^k) z‖)]
      exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hsq
    have h3 : (‖u z‖^k * ‖fderiv ℝ χ z‖)^2 = (‖u z‖^2)^k * ‖fderiv ℝ χ z‖^2 := by
      rw [mul_pow, ← pow_mul', ← pow_mul, Nat.mul_comm 2 k]
    have h4 : (χ z * ‖fderiv ℝ (fun w => (u w)^k) z‖)^2
        = (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2 := by ring
    rw [h3, h4] at h2
    linarith [h2]
  · have hzts : z ∉ tsupport χ := fun h => hz (hχsupp h)
    have hW0 : (fun y : Work.NN.Core.Cn n => (χ y : ℂ) * (u y)^k) =ᶠ[𝓝 z] 0 := by
      have := tsupport_compl_eventuallyEq_zero hzts
      filter_upwards [this] with y hy
      simp [hy]
    have hd0 : fderiv ℝ (fun y : Work.NN.Core.Cn n => (χ y : ℂ) * (u y)^k) z = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq hW0]
      simp
    rw [hd0, norm_zero]
    have : (0:ℝ)^2 = 0 := by norm_num
    rw [this]
    positivity


/-- If a `ℝ≥0∞`-valued function vanishes off `t` and `t ⊆ s`, the integrals over `s` and over `t`
agree. -/
lemma lintegral_restrict_eq_of_eq_zero_off {f : Work.NN.Core.Cn n → ENNReal}
    {s t : Set (Work.NN.Core.Cn n)} (hsm : MeasurableSet s) (htm : MeasurableSet t)
    (hst : t ⊆ s) (h0 : ∀ z ∉ t, f z = 0) :
    ∫⁻ z in s, f z = ∫⁻ z in t, f z := by
  have h1 : s.indicator f = (s ∩ t).indicator f := by
    funext z
    by_cases hz : z ∈ s ∩ t
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz.1]
    · rw [Set.indicator_of_notMem hz]
      by_cases hz2 : z ∈ s
      · rw [Set.indicator_of_mem hz2]
        exact h0 z (fun hzt => hz ⟨hz2, hzt⟩)
      · rw [Set.indicator_of_notMem hz2]
  have h2 : t.indicator f = (s ∩ t).indicator f := by
    funext z
    by_cases hz : z ∈ s ∩ t
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz.2]
    · rw [Set.indicator_of_notMem hz]
      by_cases hz2 : z ∈ t
      · exact absurd ⟨hst hz2, hz2⟩ hz
      · rw [Set.indicator_of_notMem hz2]
  rw [← MeasureTheory.lintegral_indicator hsm,
    ← MeasureTheory.lintegral_indicator htm, h1, h2]

/-- A function that is continuous on a measurable set and vanishes outside it is a.e. measurable. -/
lemma aemeasurable_of_continuousOn_of_eq_zero_off {s : Set (Work.NN.Core.Cn n)}
    (hs : MeasurableSet s) {f : Work.NN.Core.Cn n → ENNReal} (hcont : ContinuousOn f s)
    (h0 : ∀ z ∉ s, f z = 0) : AEMeasurable f volume := by
  have hind : f = s.indicator f := by
    funext z
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, h0 z hz]
  rw [hind, aemeasurable_indicator_iff hs]
  exact hcont.aemeasurable hs

/-- **Lintegral form of the Moser boost step.**  With `χ` equal to `1` on the closed polydisc of
multiradius `R`, vanishing outside the open polydisc of multiradius `S`, and `‖Dχ‖ ≤ L`, the
`L²` norm of `D(χ u^k)` is bounded by `2(1+Cc)L² ∫⁻_{closed polydisc S} (‖u‖²)^k`. -/
lemma boost_lintegral {ρ S R : Fin n → ℝ} (hRS : ∀ j, R j < S j) (hSρ : ∀ j, S j < ρ j)
    {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ 1 u (Pd ρ)) {k : ℕ}
    {χ : Work.NN.Core.Cn n → ℝ}
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχvan : ∀ z, (∃ j, S j ≤ ‖z j‖) → χ z = 0)
    (hχnn : ∀ z, 0 ≤ χ z) {L Cc : ℝ}
    (hL : ∀ z, ‖fderiv ℝ (fun z => (χ z : ℂ)) z‖ ≤ L) (hCc0 : 0 ≤ Cc)
    (hCacc : ∫⁻ z in Pd ρ, ENNReal.ofReal ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)
        ≤ ENNReal.ofReal Cc * ∫⁻ z in Pd ρ, ENNReal.ofReal (‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k)) :
    ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ (fun y => (χ y : ℂ) * (u y)^k) z‖^2) ∂volume
      ≤ ENNReal.ofReal (2*(1+Cc)*L^2) * ∫⁻ z in CPd S, ENNReal.ofReal ((‖u z‖^2)^k) := by
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hχsupp : tsupport χ ⊆ Pd ρ :=
    (tsupport_subset_CPd hχvan).trans (closedPolydisc_subset_Pd hSρ)
  have hχsuppS : tsupport χ ⊆ CPd S := tsupport_subset_CPd hχvan
  have hmeasS : MeasurableSet (CPd S) := (isClosed_closedPolydisc S).measurableSet
  have hmeasρ : MeasurableSet (Pd ρ) := (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
  have hSmemρ : ∀ z ∈ CPd S, z ∈ Pd ρ := by
    intro z hz
    rw [mem_Pd]
    exact fun j => lt_of_le_of_lt (hz j) (hSρ j)
  set g1 : Work.NN.Core.Cn n → ENNReal :=
    fun z => ENNReal.ofReal ((‖u z‖^2)^k * ‖fderiv ℝ χ z‖^2) with hg1
  set f1 : Work.NN.Core.Cn n → ENNReal :=
    fun z => ENNReal.ofReal ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2) with hf1
  set f2 : Work.NN.Core.Cn n → ENNReal :=
    fun z => ENNReal.ofReal (‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) with hf2
  set gY : Work.NN.Core.Cn n → ENNReal := fun z => ENNReal.ofReal ((‖u z‖^2)^k) with hgY
  have hgvan : ∀ z ∉ tsupport χ, fderiv ℝ χ z = 0 := by
    intro z hz
    rw [Filter.EventuallyEq.fderiv_eq (tsupport_compl_eventuallyEq_zero hz)]
    simp
  have hf1van : ∀ z ∉ Pd ρ, f1 z = 0 := by
    intro z hz
    have hzts : z ∉ tsupport χ := fun h => hz (hχsupp h)
    have h0 : χ z = 0 := Function.notMem_support.mp (fun hs => hzts (subset_tsupport χ hs))
    have hz0 : χ z ^ 2 * ‖fderiv ℝ (fun w => (u w)^k) z‖ ^ 2 = 0 := by rw [h0]; ring
    simp only [hf1, hz0, ENNReal.ofReal_zero]
  have hf2van : ∀ z ∉ CPd S, f2 z = 0 := by
    intro z hz
    have hzts : z ∉ tsupport χ := fun h => hz (hχsuppS h)
    have hz0 : ‖fderiv ℝ χ z‖ ^ 2 * (‖u z‖ ^ 2)^k = 0 := by rw [hgvan z hzts]; simp
    simp only [hf2, hz0, ENNReal.ofReal_zero]
  have hg1van : ∀ z ∉ CPd S, g1 z = 0 := by
    intro z hz
    have hzts : z ∉ tsupport χ := fun h => hz (hχsuppS h)
    have hz0 : (‖u z‖ ^ 2)^k * ‖fderiv ℝ χ z‖ ^ 2 = 0 := by rw [hgvan z hzts]; simp
    simp only [hg1, hz0, ENNReal.ofReal_zero]
  have e1 : ∫⁻ z, f1 z ∂volume = ∫⁻ z in Pd ρ, f1 z := by
    rw [← MeasureTheory.lintegral_indicator hmeasρ]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Pd ρ
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hf1van z hz]
  have e2 : ∫⁻ z in Pd ρ, f2 z = ∫⁻ z in CPd S, f2 z :=
    lintegral_restrict_eq_of_eq_zero_off hmeasρ hmeasS hSmemρ hf2van
  have e4 : ∫⁻ z, g1 z ∂volume = ∫⁻ z in CPd S, g1 z := by
    rw [← MeasureTheory.lintegral_indicator hmeasS]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ CPd S
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hg1van z hz]
  have hpt : ∀ z, ENNReal.ofReal (‖fderiv ℝ (fun y => (χ y : ℂ) * (u y)^k) z‖^2)
      ≤ 2 * g1 z + 2 * f1 z := by
    intro z
    have h := boost_pointwise (k := k) hu hχcd hχsupp hχnn z
    rw [show 2 * (‖u z‖^2)^k * ‖fderiv ℝ χ z‖^2
          + 2 * (χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2
        = 2 * ((‖u z‖^2)^k * ‖fderiv ℝ χ z‖^2)
          + 2 * ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2) from by ring] at h
    have h1 : ENNReal.ofReal (2 * ((‖u z‖^2)^k * ‖fderiv ℝ χ z‖^2)) = 2 * g1 z := by
      simp only [hg1]
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    have h2 : ENNReal.ofReal (2 * ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)) = 2 * f1 z := by
      simp only [hf1]
      rw [show (2 : ENNReal) = ENNReal.ofReal 2 by simp,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    calc ENNReal.ofReal (‖fderiv ℝ (fun y => (χ y : ℂ) * (u y)^k) z‖^2)
        ≤ ENNReal.ofReal (2 * ((‖u z‖^2)^k * ‖fderiv ℝ χ z‖^2)
            + 2 * ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal (2 * ((‖u z‖^2)^k * ‖fderiv ℝ χ z‖^2))
            + ENNReal.ofReal (2 * ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = 2 * g1 z + 2 * f1 z := by rw [h1, h2]
  have hLz : ∀ z, ‖fderiv ℝ χ z‖^2 ≤ L^2 := by
    intro z
    have h1 : ‖fderiv ℝ χ z‖ ≤ L := le_trans (norm_fderiv_le_ofReal_complex z) (hL z)
    nlinarith [h1, norm_nonneg (fderiv ℝ χ z)]
  have hg1_bound : ∫⁻ z in CPd S, g1 z ≤ ENNReal.ofReal (L^2) * ∫⁻ z in CPd S, gY z := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (L^2)) _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ CPd S
    · have hX : (0:ℝ) ≤ (‖u z‖ ^ 2)^k := by positivity
      have hle : (‖u z‖^2)^k * ‖fderiv ℝ χ z‖^2 ≤ (‖u z‖^2)^k * L^2 :=
        mul_le_mul_of_nonneg_left (hLz z) hX
      calc g1 z = ENNReal.ofReal ((‖u z‖ ^ 2)^k * ‖fderiv ℝ χ z‖ ^ 2) := by simp only [hg1]
        _ ≤ ENNReal.ofReal ((‖u z‖ ^ 2)^k * L^2) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal (L^2) * gY z := by
            rw [hgY, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ L^2), mul_comm]
    · rw [hg1van z hz]
      positivity
  have hf2_bound : ∫⁻ z in CPd S, f2 z ≤ ENNReal.ofReal (L^2) * ∫⁻ z in CPd S, gY z := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (L^2)) _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ CPd S
    · have hX : (0:ℝ) ≤ (‖u z‖ ^ 2)^k := by positivity
      have hle : ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k ≤ L^2 * (‖u z‖^2)^k :=
        mul_le_mul_of_nonneg_right (hLz z) hX
      calc f2 z = ENNReal.ofReal (‖fderiv ℝ χ z‖ ^ 2 * (‖u z‖ ^ 2)^k) := by simp only [hf2]
        _ ≤ ENNReal.ofReal (L^2 * (‖u z‖ ^ 2)^k) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal (L^2) * gY z := by
            rw [hgY, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ L^2)]
    · rw [hf2van z hz]
      positivity
  have hf1_bound : ∫⁻ z in Pd ρ, f1 z
      ≤ ENNReal.ofReal Cc * (ENNReal.ofReal (L^2) * ∫⁻ z in CPd S, gY z) := by
    refine hCacc.trans ?_
    rw [e2]
    exact mul_le_mul_of_nonneg_left hf2_bound (by positivity)
  have hcont_g1 : ContinuousOn g1 (Pd ρ) := by
    rw [hg1]
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((hu.continuousOn.norm.pow 2).pow k).mul
        (((hχcd.continuous_fderiv (by norm_num)).continuousOn).norm.pow 2))
  have hvan_g1ρ : ∀ z ∉ Pd ρ, g1 z = 0 := fun z hz => hg1van z (fun h => hz (hSmemρ z h))
  have hcont_f1 : ContinuousOn f1 (Pd ρ) := by
    rw [hf1]
    exact ENNReal.continuous_ofReal.comp_continuousOn
      (((hχcd.continuous.continuousOn).pow 2).mul ((continuousOn_fderiv_pow hu k).norm.pow 2))
  calc ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ (fun y => (χ y : ℂ) * (u y)^k) z‖^2) ∂volume
      ≤ ∫⁻ z, (2 * g1 z + 2 * f1 z) ∂volume := lintegral_mono hpt
    _ = ∫⁻ z, 2 * (g1 z + f1 z) ∂volume := by
        refine lintegral_congr fun z => ?_
        ring
    _ = 2 * (∫⁻ z in CPd S, g1 z) + 2 * (∫⁻ z in Pd ρ, f1 z) := by
        rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
          MeasureTheory.lintegral_add_left'
            (aemeasurable_of_continuousOn_of_eq_zero_off hmeasρ hcont_g1 hvan_g1ρ),
          mul_add, e4, e1]
    _ ≤ 2 * (ENNReal.ofReal (L^2) * (∫⁻ z in CPd S, gY z))
          + 2 * (ENNReal.ofReal Cc * (ENNReal.ofReal (L^2) * (∫⁻ z in CPd S, gY z))) := by
        apply add_le_add
        · exact mul_le_mul' (le_refl (2 : ENNReal)) hg1_bound
        · exact mul_le_mul' (le_refl (2 : ENNReal)) hf1_bound
    _ = ENNReal.ofReal (2*(1+Cc)*L^2) * (∫⁻ z in CPd S, gY z) := by
        have hconst : ENNReal.ofReal (2*(1+Cc)*L^2)
            = 2 * ENNReal.ofReal (L^2) + 2 * (ENNReal.ofReal Cc * ENNReal.ofReal (L^2)) := by
          have hreal : 2*(1+Cc)*L^2 = 2 * L^2 + 2 * (Cc * L^2) := by ring
          rw [hreal, ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat,
            ENNReal.ofReal_mul hCc0]
        rw [hconst, add_mul]
        ring


/-- `eLpNorm f p μ` of the `k`-th power of a function. -/
lemma eLpNorm_pow_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} {k : ℕ}
    (hk : 1 ≤ k) (hf : AEStronglyMeasurable f μ) {p : ENNReal} :
    eLpNorm (fun x => f x ^ k) p μ = (eLpNorm f (p * ENNReal.ofReal (k:ℝ)) μ) ^ (k:ℝ) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h1 : eLpNorm (fun x => ‖f x‖ ^ k) p μ
      = (eLpNorm f (p * ENNReal.ofReal (k:ℝ)) μ) ^ (k:ℝ) := by
    rw [show (fun x => ‖f x‖ ^ k) = fun x => ‖f x‖ ^ (k:ℝ) by
      funext x; rw [Real.rpow_natCast]]
    exact MeasureTheory.eLpNorm_norm_rpow f hf hkpos
  rw [← h1]
  refine MeasureTheory.eLpNorm_congr_norm_ae (hf.pow k) (hf.norm.pow k) ?_
  filter_upwards with x
  rw [norm_pow, Real.norm_of_nonneg (by positivity)]

/-- **The Moser boost step.**  If `u` is `C¹` on the polydisc `polydisc 0 ρ` and satisfies the
Caccioppoli inequality for `u^k` with constant `Cc` against a cutoff `χ` which is `1` on the closed
polydisc of multiradius `R`, vanishes outside the open polydisc of multiradius `S` and satisfies
`‖Dχ‖ ≤ L`, then the `L^{2k(2n)'}` norm of `u` on the closed polydisc `R` is bounded by
`(Kb(1+L)(1+kCc))^{1/(2k)}` times its `L^{2k}` norm on the closed polydisc `S`. -/
theorem moser_boost {n : ℕ} (hn : 0 < n) :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ {ρ S R : Fin n → ℝ}, (∀ j, R j < S j) → (∀ j, S j < ρ j) →
      ∀ {u : Work.NN.Core.Cn n → ℂ} (hu : ContDiffOn ℝ 1 u (Pd ρ)) {k : ℕ} (hk : 1 ≤ k)
      {χ : Work.NN.Core.Cn n → ℝ} (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
      (hχvan : ∀ z, (∃ j, S j ≤ ‖z j‖) → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z)
      (hχle1 : ∀ z, χ z ≤ 1) (hχ1 : ∀ z, (∀ j, ‖z j‖ ≤ R j) → χ z = 1)
      {L Cc : ℝ} (hL0 : 0 ≤ L) (hCc0 : 0 ≤ Cc)
      (hL : ∀ z, ‖fderiv ℝ (fun z => (χ z : ℂ)) z‖ ≤ L)
      (hCacc : ∫⁻ z in Pd ρ, ENNReal.ofReal ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)
          ≤ ENNReal.ofReal Cc * ∫⁻ z in Pd ρ, ENNReal.ofReal (‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k)),
      eLpNorm u (ENNReal.ofReal (2 * (k:ℝ) * ((NNReal.conjExponent (2*n) : NNReal) : ℝ)))
          (volume.restrict (CPd R))
        ≤ ENNReal.ofReal ((Kb * (1 + L) * (1 + (k:ℝ) * Cc)) ^ (1 / (2 * (k:ℝ))))
          * eLpNorm u (ENNReal.ofReal (2 * (k:ℝ))) (volume.restrict (CPd S)) := by
  obtain ⟨Cg, hCgpos, hGNSlem⟩ := gagliardoNirenbergGeomMean hn
  refine ⟨Cg * Real.sqrt 2 + 1, by positivity, ?_⟩
  intro ρ S R hRS hSρ u hu k hk χ hχcd hχcs hχvan hχnn hχle1 hχ1 L Cc hL0 hCc0 hL hCacc
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  set q : ℝ := ((NNReal.conjExponent (2 * n) : NNReal) : ℝ) with hq
  have hexq : (2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)
      = ENNReal.ofReal (2 * q) := by
    rw [hq, ← ENNReal.ofReal_coe_nnreal (p := NNReal.conjExponent (2 * n)),
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  set W : Work.NN.Core.Cn n → ℂ := fun z => (χ z : ℂ) * (u z)^k with hW
  have hWcd : ContDiff ℝ 1 W := by
    rw [hW]
    exact Work.NN.Core.contDiff_one_mul_of_support (u := fun w => (u w)^k) (η := χ)
      (ρ := ρ) (r := S) hχcd hχvan hSρ (hu.pow k)
  have hWcs : HasCompactSupport W :=
    hχcs.mono' fun z hz => subset_tsupport χ (Function.mem_support.mpr (by
      intro h0
      rw [Function.mem_support] at hz
      exact hz (by rw [hW]; simp [h0])))
  have hRρ : ∀ j, R j < ρ j := fun j => lt_trans (hRS j) (hSρ j)
  set A : ENNReal := eLpNorm (fun z => (u z)^k) ((2 : ENNReal) *
    ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)) (volume.restrict (CPd R)) with hA
  set B : ENNReal := eLpNorm (fun z => (u z)^k) 2 (volume.restrict (CPd S)) with hB
  set G : ENNReal := eLpNorm W ((2 : ENNReal) *
    ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)) volume with hG
  set D : ENNReal := eLpNorm (fderiv ℝ W) 2 volume with hD
  set H : ENNReal := eLpNorm W 2 volume with hH
  have hmeasR : AEStronglyMeasurable u (volume.restrict (CPd R)) :=
    (hu.continuousOn.mono (closedPolydisc_subset_Pd hRρ)).aestronglyMeasurable
      (isClosed_closedPolydisc R).measurableSet
  have hmeasS : AEStronglyMeasurable u (volume.restrict (CPd S)) :=
    (hu.continuousOn.mono (closedPolydisc_subset_Pd hSρ)).aestronglyMeasurable
      (isClosed_closedPolydisc S).measurableSet
  have hBmeas : AEStronglyMeasurable (fun z => (u z)^k) (volume.restrict (CPd S)) :=
    ((hu.pow k).continuousOn.mono (closedPolydisc_subset_Pd hSρ)).aestronglyMeasurable
      (isClosed_closedPolydisc S).measurableSet
  have hDmeas : AEStronglyMeasurable (fderiv ℝ W) volume :=
    (hWcd.continuous_fderiv (by norm_num)).aestronglyMeasurable
  -- (i) `A ≤ G`
  have hAG : A ≤ G := by
    rw [hA, hG]
    have h1 : eLpNorm (fun z => (u z)^k) ((2 : ENNReal) *
          ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)) (volume.restrict (CPd R))
        = eLpNorm W ((2 : ENNReal) *
          ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)) (volume.restrict (CPd R)) := by
      refine MeasureTheory.eLpNorm_congr_ae ?_
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (isClosed_closedPolydisc R).measurableSet]
      exact Filter.Eventually.of_forall fun z hz => by
        simp only [hW, hχ1 z hz, Complex.ofReal_one, one_mul]
    rw [h1]
    exact MeasureTheory.eLpNorm_mono_measure _ Measure.restrict_le_self
  -- (ii) `H ≤ B`
  have hHB : H ≤ B := by
    rw [hH, hB]
    have h1 : ∀ z ∉ CPd S, W z = 0 := by
      intro z hz
      have hzS : ∃ j, S j ≤ ‖z j‖ := by
        by_contra hcon
        push Not at hcon
        exact hz (fun j => le_of_lt (hcon j))
      rw [hW]; simp [hχvan z hzS]
    rw [eLpNorm_eq_restrict_of_support (isClosed_closedPolydisc S).measurableSet h1]
    refine MeasureTheory.eLpNorm_mono ((hWcd.continuous.aestronglyMeasurable).restrict) fun z => ?_
    have h1 : ‖W z‖ = χ z * ‖u z‖ ^ k := by
      rw [hW, norm_mul, norm_pow, Complex.norm_of_nonneg (hχnn z)]
    rw [h1, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hχle1 z)
  -- (iii) `D ≤ ofReal (√(2(1+Cc)) * L) * B`
  have hBid : B ^ (2:ℝ) = ∫⁻ z in CPd S, ENNReal.ofReal ((‖u z‖^2)^k) := by
    rw [hB, eLpNorm_two_sq_eq_lintegral_ofReal (μ := volume.restrict (CPd S))
      (f := fun z => (u z)^k) hBmeas]
    refine lintegral_congr fun z => ?_
    congr 1
    rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k 2]
  have hD2 : D ^ (2:ℝ) ≤ ENNReal.ofReal (2*(1+Cc)*L^2) * B ^ (2:ℝ) := by
    have hD' : eLpNorm (fderiv ℝ W) 2 volume = D := hD.symm
    have hDlib : (eLpNorm (fderiv ℝ W) 2 volume) ^ (2:ℝ)
        = ∫⁻ z, ENNReal.ofReal (‖fderiv ℝ W z‖^2) ∂volume := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num]
      exact eLpNorm_two_sq_eq_lintegral_ofReal (f := fderiv ℝ W) (μ := volume) hDmeas
    rw [← hD', hDlib, hBid]
    exact boost_lintegral hRS hSρ hu hχcd hχcs hχvan hχnn hL hCc0 hCacc
  have hsqrt : (2*(1+Cc)*L^2) ^ (1/2:ℝ) = Real.sqrt (2*(1+Cc)) * L := by
    rw [show (2*(1+Cc)*L^2) = (2*(1+Cc)) * L^2 by ring, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*(1+Cc)), Real.sqrt_sq hL0]
  have hDle : D ≤ ENNReal.ofReal (Real.sqrt (2*(1+Cc)) * L) * B := by
    have h1 := ENNReal.rpow_le_rpow hD2 (by norm_num : (0:ℝ) ≤ 1/2)
    rw [← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
      ← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 1/2), hsqrt] at h1
    exact h1
  -- (iv) GNS and assembly
  have hGNS := hGNSlem W hWcd hWcs
  have hA2 : A ^ (2:ℝ) ≤ ENNReal.ofReal (Cg * (Real.sqrt (2*(1+Cc)) * L)) * B ^ (2:ℝ) := by
    have h1 : A ^ (2:ℝ) ≤ G ^ (2:ℝ) := ENNReal.rpow_le_rpow hAG (by norm_num)
    have h2 : G ^ (2:ℝ) ≤ ENNReal.ofReal Cg * H * D := by
      rw [hG, hH, hD, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
      exact hGNS
    have h3 : ENNReal.ofReal Cg * H * D
        ≤ ENNReal.ofReal Cg * B * (ENNReal.ofReal (Real.sqrt (2*(1+Cc)) * L) * B) :=
      mul_le_mul' (mul_le_mul' le_rfl hHB) hDle
    calc A ^ (2:ℝ) ≤ G ^ (2:ℝ) := h1
      _ ≤ ENNReal.ofReal Cg * H * D := h2
      _ ≤ ENNReal.ofReal Cg * B * (ENNReal.ofReal (Real.sqrt (2*(1+Cc)) * L) * B) := h3
      _ = ENNReal.ofReal (Cg * (Real.sqrt (2*(1+Cc)) * L)) * B ^ (2:ℝ) := by
          have hbb : ENNReal.ofReal Cg * B * (ENNReal.ofReal (Real.sqrt (2*(1+Cc)) * L) * B)
              = (ENNReal.ofReal Cg * ENNReal.ofReal (Real.sqrt (2*(1+Cc)) * L)) * (B * B) := by
            ring
          rw [hbb, ENNReal.ofReal_mul hCgpos.le,
            show B ^ (2:ℝ) = B * B by
              rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]; ring]
  -- (v) convert to the norms of `u` and take the `2k`-th root
  have hAeq : A = (eLpNorm u (ENNReal.ofReal (2 * (k:ℝ) * q)) (volume.restrict (CPd R))) ^ (k:ℝ) := by
    rw [hA, eLpNorm_pow_eq hk hmeasR, hexq, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * q)]
    congr 1
    ring
  have hBeq : B = (eLpNorm u (ENNReal.ofReal (2 * (k:ℝ))) (volume.restrict (CPd S))) ^ (k:ℝ) := by
    rw [hB, eLpNorm_pow_eq hk hmeasS]
    norm_num
  rw [hAeq, hBeq, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hA2
  have hfinal : eLpNorm u (ENNReal.ofReal (2 * (k:ℝ) * q)) (volume.restrict (CPd R))
      ≤ ENNReal.ofReal ((Cg * (Real.sqrt (2*(1+Cc)) * L)) ^ (1 / (2 * (k:ℝ))))
        * eLpNorm u (ENNReal.ofReal (2 * (k:ℝ))) (volume.restrict (CPd S)) := by
    have h1 := ENNReal.rpow_le_rpow hA2 (by positivity : (0:ℝ) ≤ 1 / (2 * (k:ℝ)))
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / (2 * (k:ℝ))),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      show (k:ℝ) * 2 = 2 * (k:ℝ) by ring,
      show (2 * (k:ℝ)) * (1 / (2 * (k:ℝ))) = 1 by field_simp,
      ENNReal.rpow_one, ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)] at h1
    exact h1
  -- the constant comparison
  refine hfinal.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have h1 : Cg * (Real.sqrt (2*(1+Cc)) * L) ≤ Cg * (Real.sqrt 2 * (1 + Cc) * L) := by
    refine mul_le_mul_of_nonneg_left ?_ hCgpos.le
    have h2 : Real.sqrt (1 + Cc) ≤ 1 + Cc := by
      have h3 : (1:ℝ) ≤ 1 + Cc := by linarith [hCc0]
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + Cc),
        Real.sqrt_nonneg (1 + Cc), h3, hCc0]
    calc Real.sqrt (2*(1+Cc)) * L = Real.sqrt 2 * Real.sqrt (1+Cc) * L := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ Real.sqrt 2 * (1 + Cc) * L := by
          refine mul_le_mul_of_nonneg_right ?_ hL0
          exact mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg 2)
  have h2 : Cg * (Real.sqrt 2 * (1 + Cc) * L)
      ≤ (Cg * Real.sqrt 2 + 1) * (1 + L) * (1 + (k:ℝ) * Cc) := by
    have hCc1 : 1 + Cc ≤ 1 + (k:ℝ) * Cc := by nlinarith [hCc0, hkR]
    have hL1 : L ≤ 1 + L := by linarith
    have h3 : Cg * Real.sqrt 2 ≤ Cg * Real.sqrt 2 + 1 := by linarith
    calc Cg * (Real.sqrt 2 * (1 + Cc) * L)
        = (Cg * Real.sqrt 2) * ((1 + Cc) * L) := by ring
      _ ≤ (Cg * Real.sqrt 2 + 1) * ((1 + (k:ℝ) * Cc) * (1 + L)) :=
          mul_le_mul h3 (mul_le_mul hCc1 hL1 (by positivity) (by positivity))
            (by positivity) (by positivity)
      _ = (Cg * Real.sqrt 2 + 1) * (1 + L) * (1 + (k:ℝ) * Cc) := by ring
  exact Real.rpow_le_rpow (by positivity) (h1.trans h2) (by positivity)

end Work.NN.Core.Value
