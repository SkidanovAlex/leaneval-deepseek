import Submission.FUP.HSApply

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 10: the one-step gain, end to end

Combining the localisation estimate (`HSApply`), the transfer to the holes (`HSLoc`) and the
one-step gain (`HSGain`) into a single statement:

`∫ ‖f_{m+1}‖² ≤ (1 - (1-e²)/C_*²) ∫ ‖f_m‖²`,  `e = ∫_{‖w‖ ≥ 2L^{T-1}/5} φ`.
-/

namespace Submission.FUP

/-- The upper bound for `Ψ_{mT}` on the holes: `e = ∫_{2L^{T-1}/5 ≤ ‖w‖} φ`. -/
noncomputable def eUp (Φ : FupCutoff d) (L T : ℕ) : ℝ :=
  ∫ w in {w : ℝᵈ | 2 * (L : ℝ) ^ (T - 1) / 5 ≤ ‖w‖}, Φ.reFun w

lemma eUp_nonneg (Φ : FupCutoff d) (L T : ℕ) : 0 ≤ eUp Φ L T :=
  integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => Φ.reFun_nonneg z)

lemma Psi_le_eUp {L T n : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) {X : Set ℝᵈ}
    {x : ℝᵈ} (hx : x ∈ Ustar L X n) : Psi Φ L T X n x ≤ eUp Φ L T :=
  Psi_upper hL hT Φ hx

/-- The same bound on the corrected hole set `UstarZ`. -/
lemma Psi_le_eUpZ {L T n : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) {X : Set ℝᵈ}
    {x : ℝᵈ} (hx : x ∈ UstarZ L X n) : Psi Φ L T X n x ≤ eUp Φ L T := by
  have h := Psi_upperZ (T := T) hL Φ hx
  rwa [show (L : ℝ) ^ (n + T) * (2 * hss L (n+1) / 5) = 2 * (L : ℝ) ^ (T - 1) / 5 from by
    rw [← pow_mul_hss hL hT]; ring] at h

/-- **The one-step gain.** -/
theorem gain_step {L T m : ℕ} (hL : 3 ≤ L) (hT : 1 ≤ T)
    (Φ : FupCutoff d) (hΦr : Φ.radius ≤ 1) {N : ℝ} (hN : 1 ≤ N) {X Y : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) (hY : Y ⊆ cube (-N) N) (hpor : BoxPorous L (m * T + 1) X)
    {c₂ c₃ α Cstar : ℝ} (hCstar : 0 < Cstar)
    (hLOC : ∀ (α₁ : ℝ), 1 ≤ α₁ → ∀ (γ : ℝᵈ) (Y' : Set ℝᵈ), Y' ⊆ cube (-α₁) α₁ →
        (∀ η : ℝᵈ, (∀ i : Fin d, η i ∈ Set.Icc (-(α₁ + 1)) (α₁ + 1)) →
          AdmitsL1Damping ((fun z : ℝᵈ => η + z) '' (addSet Y' (cube (-2) 2)))
            (4 * (L : ℝ))⁻¹ c₂ c₃ α) →
        ∀ (a : (Fin d → ℤ) → (Fin d → ℝ)),
          (∀ n : Fin d → ℤ, ∀ i : Fin d, 2 * (n i : ℝ) + γ i ≤ a n i ∧
            a n i + locSide L ≤ 2 * (n i : ℝ) + γ i + 2) →
          ∀ f' : Lp ℂ 2 (volume : Measure ℝᵈ),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
              ((𝓕 f' : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y') →
            ‖f'‖ ≤ Cstar * (eLpNorm ((⋃ n : Fin d → ℤ, box (a n) (fun i => a n i + locSide L)).indicator
                (f' : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal)
    (hdamp : ∀ η : ℝᵈ,
        (∀ i : Fin d, η i ∈ Set.Icc (-(N * (rescaleFactor L T m)⁻¹) - 3)
          (N * (rescaleFactor L T m)⁻¹ + 3)) →
        AdmitsL1Damping ((fun z : ℝᵈ => η + z) ''
          (addSet ((rescaleFactor L T m)⁻¹ • Y) (cube (-4) 4)))
          (4 * (L : ℝ))⁻¹ c₂ c₃ α)
    {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ))
    (hsuppY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) :
    ∫ z, ‖indFun Φ L T X (m + 1) f z‖ ^ 2
      ≤ (1 - (1 - (eUp Φ L T) ^ 2) / Cstar ^ 2) * ∫ z, ‖indFun Φ L T X m f z‖ ^ 2 := by
  have hL1 : 1 ≤ L := by omega
  -- 1. the localisation estimate for `g_m`
  have hLOC1 := localize_gm (L := L) (T := T) (m := m) hL hT Φ hΦr hN hX hY
    hpor hCstar hLOC hdamp hf hsuppY
  -- 2. the localisation set is inside the rescaled hole set
  have hsub : locSetZ L T m X (holeSelZ (by omega) X hpor)
      ⊆ rescaleFactor L T m • UstarZ L X (m * T) :=
    locSetZ_subset_smul_UstarZ (by omega)
      (fun n => holeSelZ_empty (by omega) (by omega : 2 ≤ L) hX hpor n)
  -- 3. transfer to the holes
  have hInt := integral_le_UstarZ_of_localize (L := L) (T := T) (m := m) (by omega) Φ hX hf hsub hLOC1
  -- 4. the gain
  have hUmeas : MeasurableSet (UstarZ L X (m * T)) := measurableSet_UstarZ L X (m * T)
  exact integral_indFun_gain (L := L) (T := T) hL1 Φ hX m hf (eUp_nonneg Φ L T) hCstar hUmeas
    (fun z hz => Psi_le_eUpZ hL1 hT Φ hz) hInt

end Submission.FUP
