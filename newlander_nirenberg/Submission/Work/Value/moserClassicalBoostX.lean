import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.Value.moserCoreDefs
import Submission.Work.NN.Core.Lev.nnGradBoundPoint
import Submission.Work.NN.Core.Lev.moserTheta
import Submission.Work.NN.Assemble.coordSphere_volume_eq_zero
import Submission.Work.NN.Core.Fleet.chainMeanValueFamily

/-!
# The classical Moser boost

From the *integer level* weighted Caccioppoli inequality with a fixed constant `C₀`

  `∫ φ² ‖u‖^{2k-2} Σ_j(‖∂_j u‖² + ‖∂̄_j u‖²) ≤ C₀ ∫ ‖∇φ‖² ‖u‖^{2k}`  (`k ≥ 1`, `φ` a cutoff)

we deduce the Moser boost on polydiscs `r ⊂⊂ s ⊂⊂ ρ` for the cutoff `χ` (`= 1` on the closed
polydisc `r`, supported in `Pd s`, `‖∇χ‖ ≤ L`):

  `‖u‖_{L^{2k(2n)'}(Pd r)} ≤ (Cb (1+L) (1+k³C₀))^{1/(2k)} ‖u‖_{L^{2k}(Pd s)}`.
-/

namespace Work.Value

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology NNReal

noncomputable section

/-- The closed and the open polydisc differ by the boundary, a finite union of coordinate spheres
and hence null. -/
lemma volume_CPd_diff_PdX {n : ℕ} (r : Fin n → ℝ) :
    MeasureTheory.volume (Work.NN.Core.Value.CPd r \ Work.NN.Core.Value.Pd r) = 0 := by
  have hsub : Work.NN.Core.Value.CPd r \ Work.NN.Core.Value.Pd r
      ⊆ ⋃ j : Fin n, {z : Work.NN.Core.Cn n | ‖z j‖ = r j} := by
    intro z hz
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_setOf_eq] at hz ⊢
    by_contra hcon
    push Not at hcon
    refine hz.2 (fun j => ?_)
    have h1 : ‖z j‖ ≤ r j := hz.1 j
    have h2 : ‖z j‖ ≠ r j := fun heq => hcon j (by simpa using heq)
    simpa using lt_of_le_of_ne h1 h2
  exact MeasureTheory.measure_mono_null hsub
    (MeasureTheory.measure_iUnion_null fun j => Work.NN.Assemble.coordSphere_volume_eq_zero j (r j))

/-- The closed and the open polydisc carry the same restricted Lebesgue measure. -/
lemma restrict_CPd_eq_restrict_PdX {n : ℕ} (r : Fin n → ℝ) :
    MeasureTheory.volume.restrict (Work.NN.Core.Value.CPd r)
      = MeasureTheory.volume.restrict (Work.NN.Core.Value.Pd r) := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
  have hsub : Work.NN.Core.Value.Pd r ⊆ Work.NN.Core.Value.CPd r :=
    Work.NN.Core.Value.Pd_subset_CPd r
  have hdiff : Work.NN.Core.Value.Pd r \ Work.NN.Core.Value.CPd r = ∅ := by
    rw [Set.sdiff_eq_empty]; exact hsub
  rw [Set.symmDiff_def, hdiff, Set.union_empty]
  exact volume_CPd_diff_PdX r


/-- **The classical Moser boost.**  From the integer-level weighted Caccioppoli inequality with
constant `C₀` one obtains the `L^{2k} → L^{2k(2n)'}` boost with constant
`(Cb (1+L) (1+k³C₀))^{1/(2k)}`. -/
theorem classicalMoserBoostX {n : ℕ} (hn : 0 < n) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ {ρ : Fin n → ℝ}, (∀ j, 0 < ρ j) → ∀ {u : Work.NN.Core.Cn n → ℂ},
        ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
        (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ → tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖u z‖ ^ (2*k-2) *
              (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
            ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖ ^ (2*k)) →
        ∀ {r s : Fin n → ℝ}, (∀ j, r j < s j) → (∀ j, s j < ρ j) →
        ∀ {χ : Work.NN.Core.Cn n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
          tsupport χ ⊆ Work.CR.Flat.polydisc 0 s → (∀ z, 0 ≤ χ z) → (∀ z, χ z ≤ 1) →
          (∀ z, (∀ j, ‖z j‖ ≤ r j) → χ z = 1) →
        ∀ {L : ℝ}, 0 ≤ L → (∀ z, ‖fderiv ℝ χ z‖ ≤ L) → ∀ (k : ℕ), 1 ≤ k →
        MeasureTheory.eLpNorm u
            (ENNReal.ofReal (2 * ((k : ℝ) * Work.NN.Core.Lev.moserTheta n)))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
          ≤ (ENNReal.ofReal (Cb * (1 + L) * (1 + (k : ℝ)^3 * C₀))) ^ (1 / (2 * (k : ℝ))) *
            MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k : ℝ)))
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
  obtain ⟨Kb, hKb, hboost⟩ := Work.NN.Core.Value.moser_boost hn
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.NN.Core.Lev.nnGradBoundPoint hn
  refine ⟨2 * (Kb * (max 1 Cg)) + 1, by positivity, ?_⟩
  intro ρ hρ0 u hu hH r s hrs hsρ χ hχcd hχcs hχsupp hχnn hχle1 hχone L hL0 hLgrad k hk
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hsρle : ∀ j, s j ≤ ρ j := fun j => (hsρ j).le
  have hχsuppρ : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ :=
    hχsupp.trans (Work.CR.Flat.polydisc_mono hsρle)
  have hCgnn : 0 ≤ Cg := hCgpos.le
  have hms : MeasurableSet (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) ρ) :=
    (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
  have hpow : ∀ z : Work.NN.Core.Cn n, ‖u z‖ ^ (2*(k:ℝ) - 2) = ‖u z‖ ^ (2*k-2) := by
    intro z
    rw [show (2*(k:ℝ) - 2 : ℝ) = ((2*k-2 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega : 2 ≤ 2*k)]; push_cast; ring, Real.rpow_natCast]
  have hpow2 : ∀ z : Work.NN.Core.Cn n, ‖u z‖ ^ (2*k) = ‖u z‖ ^ (2*(k:ℝ)) := by
    intro z
    rw [show (2*(k:ℝ) : ℝ) = ((2*k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hlev : ∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2) *
        Work.NN.Core.Value.energySum u z
      ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖^2 * ‖u z‖ ^ (2*(k:ℝ)) := by
    have h := hH k hk χ hχcd hχcs hχsuppρ hχnn
    have h1 : (∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 * ‖u z‖ ^ (2*(k:ℝ) - 2) *
          Work.NN.Core.Value.energySum u z)
        = ∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 * ‖u z‖ ^ (2*k-2) *
            (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)) := by
      refine setIntegral_congr_fun hms fun z _ => ?_
      simp only [Work.NN.Core.Value.energySum, hpow z]
    have h2 : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖^2 * ‖u z‖ ^ (2*(k:ℝ)))
        = ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ χ z‖^2 * ‖u z‖ ^ (2*k) := by
      refine setIntegral_congr_fun hms fun z _ => ?_
      rw [hpow2 z]
    rw [h1, h2]
    exact h
  have hCc : ∫⁻ z in Work.CR.Flat.polydisc 0 ρ,
        ENNReal.ofReal ((χ z)^2 * ‖fderiv ℝ (fun w => (u w)^k) z‖^2)
      ≤ ENNReal.ofReal (Cg * (k:ℝ)^2 * C₀) *
        ∫⁻ z in Work.CR.Flat.polydisc 0 ρ,
          ENNReal.ofReal (‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) :=
    Work.NN.Core.Value.pow_caccioppoli_lint (ρ := ρ) hu hk hCgnn (fun z => hCg u z) hC₀.le
      hχcd hχcs hχsuppρ hχnn hlev
  have hvan : ∀ z, (∃ j, s j ≤ ‖z j‖) → χ z = 0 := by
    intro z hz
    by_contra hne
    obtain ⟨j, hj⟩ := hz
    have hmem : z ∈ tsupport χ := subset_closure (Function.mem_support.mpr hne)
    have hlt : ‖z j‖ < s j := by
      simpa using (Work.CR.Flat.mem_polydisc.mp (hχsupp hmem)) j
    exact absurd hlt (not_lt.mpr hj)
  have hLc : ∀ z, ‖fderiv ℝ (fun z => (χ z : ℂ)) z‖ ≤ L := by
    intro z
    have hd : DifferentiableAt ℝ χ z := (hχcd.differentiable (by simp)).differentiableAt
    rw [Work.NN.Core.Fleet.norm_fderiv_ofReal_eq χ z hd]
    exact hLgrad z
  have hb := hboost (ρ := ρ) (S := s) (R := r) hrs hsρ hu hk hχcd hχcs hvan hχnn hχle1 hχone
    hL0 (by positivity : (0:ℝ) ≤ Cg * (k:ℝ)^2 * C₀) hLc hCc
  have hconst : Kb * (1 + L) * (1 + (k:ℝ) * (Cg * (k:ℝ)^2 * C₀))
      ≤ (2 * (Kb * (max 1 Cg)) + 1) * (1 + L) * (1 + (k : ℝ)^3 * C₀) := by
    have hC0nn : 0 ≤ C₀ := hC₀.le
    have h1 : 1 + (k:ℝ) * (Cg * (k:ℝ)^2 * C₀) = 1 + Cg * ((k:ℝ)^3 * C₀) := by ring
    have hx : 0 ≤ (k:ℝ)^3 * C₀ := by positivity
    have hCgle : Cg ≤ max 1 Cg := le_max_right _ _
    have hmax1 : (1:ℝ) ≤ max 1 Cg := le_max_left _ _
    have h2 : 1 + Cg * ((k:ℝ)^3 * C₀) ≤ (max 1 Cg) * (1 + (k:ℝ)^3 * C₀) := by
      have hh := mul_le_mul_of_nonneg_right hCgle hx
      nlinarith [hh, hmax1, hx]
    have h4 : Kb * (max 1 Cg) * (1 + (k:ℝ)^3 * C₀) ≤ (2 * (Kb * (max 1 Cg)) + 1) * (1 + (k:ℝ)^3 * C₀) := by
      have hKbmax : 0 ≤ Kb * (max 1 Cg) := by positivity
      have hy : 0 ≤ 1 + (k:ℝ)^3 * C₀ := by positivity
      nlinarith [hKbmax, hy]
    calc Kb * (1 + L) * (1 + (k:ℝ) * (Cg * (k:ℝ)^2 * C₀))
        = Kb * (1 + L) * (1 + Cg * ((k:ℝ)^3 * C₀)) := by rw [h1]
      _ ≤ Kb * (1 + L) * ((max 1 Cg) * (1 + (k:ℝ)^3 * C₀)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Kb * (max 1 Cg) * (1 + L) * (1 + (k:ℝ)^3 * C₀) := by ring
      _ ≤ (2 * (Kb * (max 1 Cg)) + 1) * (1 + (k:ℝ)^3 * C₀) * (1 + L) := by
          have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ 1 + L)
          linarith [h5]
      _ = (2 * (Kb * (max 1 Cg)) + 1) * (1 + L) * (1 + (k : ℝ)^3 * C₀) := by ring
  have hconst' : ENNReal.ofReal ((Kb * (1 + L) * (1 + (k:ℝ) * (Cg * (k:ℝ)^2 * C₀))) ^ (1 / (2 * (k:ℝ))))
      ≤ (ENNReal.ofReal ((2 * (Kb * (max 1 Cg)) + 1) * (1 + L) * (1 + (k : ℝ)^3 * C₀))) ^ (1 / (2 * (k:ℝ))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    exact Real.rpow_le_rpow (by positivity) hconst (by positivity)
  have hexp : ENNReal.ofReal (2 * (k:ℝ) * ((NNReal.conjExponent (2 * n) : NNReal) : ℝ))
      = ENNReal.ofReal (2 * ((k : ℝ) * Work.NN.Core.Lev.moserTheta n)) := by
    rw [Work.NN.Core.Lev.moserTheta]
    congr 1
    ring
  calc MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * ((k : ℝ) * Work.NN.Core.Lev.moserTheta n)))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      = MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * ((k : ℝ) * Work.NN.Core.Lev.moserTheta n)))
        (MeasureTheory.volume.restrict (Work.NN.Core.Value.CPd r)) := by
        rw [restrict_CPd_eq_restrict_PdX r]
    _ = MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k:ℝ) * ((NNReal.conjExponent (2 * n) : NNReal) : ℝ)))
        (MeasureTheory.volume.restrict (Work.NN.Core.Value.CPd r)) := by rw [hexp]
    _ ≤ ENNReal.ofReal ((Kb * (1 + L) * (1 + (k:ℝ) * (Cg * (k:ℝ)^2 * C₀))) ^ (1 / (2 * (k:ℝ)))) *
        MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k:ℝ)))
          (MeasureTheory.volume.restrict (Work.NN.Core.Value.CPd s)) := hb
    _ ≤ (ENNReal.ofReal ((2 * (Kb * (max 1 Cg)) + 1) * (1 + L) * (1 + (k : ℝ)^3 * C₀))) ^ (1 / (2 * (k:ℝ))) *
        MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k:ℝ)))
          (MeasureTheory.volume.restrict (Work.NN.Core.Value.CPd s)) :=
        mul_le_mul' hconst' le_rfl
    _ = (ENNReal.ofReal ((2 * (Kb * (max 1 Cg)) + 1) * (1 + L) * (1 + (k : ℝ)^3 * C₀))) ^ (1 / (2 * (k:ℝ))) *
        MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k:ℝ)))
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
        rw [restrict_CPd_eq_restrict_PdX s]

end

end Work.Value
