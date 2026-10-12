import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.integral_shift_pair_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQDl_eq_boxAvg`

The `θθ` row of the FS §8 pair kernel, in its **box-average** form.  `pinQDl` is the lattice sum
of `pinQLimDefs`; `pinQDl_eq_const` (`Submission/Work/BoseBoxFock/pinQDl_eq_const.lean`) identifies
it with the `ℓ`-lattice sum of the double integrals

    `pinQDl ℓ W = ℓ⁻³ Σ'_m ∫_y∫_x W(y)·χ_ℓ(x−y)·χ_ℓ(ℓ·latVec m − x)`,

and the present file identifies it with the average over the centred box of the window `χ_ℓ`
against the **periodisation** `latPer3`:

    `pinQDl ℓ W = ℓ⁻⁶ ∫_{w ∈ acube ℓ} ∫_{y ∈ acube ℓ} χ_ℓ(w)·latPer3 ℓ W (w−y)·χ_ℓ(y)`.

## Route

Inside the centred cube the periodisation is the finite sum
`latPer3 ℓ W (w−y) = ↑(ℓ³) Σ_{m ∈ latFinSet ℓ R} ↑(W (w−y+ℓ·latVec m))`
(`boxAvgAux.latPer3_eq_sum_latFinSet`, valid because two points of `acube ℓ` differ by at most
`√3 ℓ`, and the windows vanish off the cube).  The box integral therefore equals `ℓ³` times the
finite sum over `m` of `∫_w∫_y χ_ℓ(w)·W(w−y+ℓm)·χ_ℓ(y)`, and each of those is the
`pinQDl_eq_const` summand: the two are related by the measure preserving inner substitutions
`y ↦ w + ℓm − y` (a reflection) and `x ↦ x + y` (a translation) together with the evenness of
`χ_ℓ` and one application of Fubini — this is exactly the delegated lemma
`Work.BoseBoxFock.integral_shift_pair_eq`
(`Submission/Work/BoseBoxFock/integral_shift_pair_eq.lean`).  Finally the `∑'` of
`pinQDl_eq_const` is the finite sum over `latFinSet ℓ R` because every other summand vanishes
identically.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Abbreviations for the objects of the comparison -/

/-- The complexified scaled bump `χ_ℓ`. -/
private noncomputable def bchi (ℓ : ℝ) : E3 → ℂ :=
  fun z => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)

/-- The integrand of the box average. -/
private noncomputable def bPhi (ℓ : ℝ) (W : E3 → ℝ) : E3 → E3 → ℂ :=
  fun w y => bchi ℓ w * latPer3 ℓ W (w - y) * bchi ℓ y

/-- The *expanded* (finite sum) form of the same integrand. -/
private noncomputable def bPsi (ℓ : ℝ) (W : E3 → ℝ) (S : Finset (Fin 3 → ℤ)) : E3 → E3 → ℂ :=
  fun w y => ∑ m ∈ S,
    ((ℓ ^ 3 : ℝ) : ℂ) * (bchi ℓ w * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ y)

/-- The `m`-th summand of the `pinQDl_eq_const` double integral. -/
private noncomputable def bRhs (ℓ : ℝ) (W : E3 → ℝ) (m : Fin 3 → ℤ) : ℂ :=
  ∫ y, ∫ x, ((W y : ℝ) : ℂ) * bchi ℓ (x - y) * bchi ℓ (ℓ • latVec m - x)

/-! ## Elementary properties of the complexified bump -/

private lemma bchi_continuous (ℓ : ℝ) : Continuous (bchi ℓ) := by
  change Continuous (fun z : E3 => ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ))
  exact Complex.continuous_ofReal.comp (Submission.BoseGases.chiScale_continuous ℓ)

private lemma bchi_bdd (ℓ : ℝ) : ∃ C, ∀ x, ‖bchi ℓ x‖ ≤ C :=
  ⟨(Real.sqrt Submission.BoseGases.chiNormSq)⁻¹, fun x => by
    change ‖((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ)‖
      ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹
    rw [pinQ_norm_ofReal_complex, Real.norm_eq_abs]
    exact Submission.BoseGases.abs_chiScale_le ℓ x⟩

private lemma bchi_eq_zero_of_half_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {x : E3} (hx : ℓ / 2 < ‖x‖) :
    bchi ℓ x = 0 := by
  change ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) = 0
  rw [chiScale_eq_zero_of_half_lt hℓ hx, Complex.ofReal_zero]

private lemma bchi_neg (ℓ : ℝ) (z : E3) : bchi ℓ (-z) = bchi ℓ z := by
  change ((Submission.BoseGases.chiScale ℓ (-z) : ℝ) : ℂ)
      = ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ)
  rw [chiScale_neg]

private lemma bchi_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3}
    (hz : z ∉ Submission.BoseGases.acube ℓ) : bchi ℓ z = 0 := by
  change ((Submission.BoseGases.chiScale ℓ z : ℝ) : ℂ) = 0
  rw [chiScale_eq_zero_of_notMem_acube hℓ hz, Complex.ofReal_zero]

/-! ## The main identity -/

theorem pinQDl_eq_boxAvg {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z)
    (hW : ∀ z, R < ‖z‖ → W z = 0) :
    Work.BoseBoxFock.pinQDl ℓ W
      = (((ℓ ^ 3)⁻¹ : ℝ) * ((ℓ ^ 3)⁻¹ : ℝ)) * ∫ w in Submission.BoseGases.acube ℓ,
          ∫ y in Submission.BoseGases.acube ℓ,
            (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * Work.BoseBoxFock.latPer3 ℓ W (w - y)
              * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) := by
  classical
  obtain ⟨CW, hCW⟩ := hWb
  have hWb' : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C := ⟨CW, hCW⟩
  have hRℓ3 : (ℓ ^ 3 : ℝ) ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
  have hχc : Continuous (bchi ℓ) := bchi_continuous ℓ
  obtain ⟨Cχ, hCχ⟩ := bchi_bdd ℓ
  have hχb : ∃ C, ∀ x : E3, ‖bchi ℓ x‖ ≤ C := ⟨Cχ, hCχ⟩
  have hχs : ∀ x : E3, ℓ / 2 < ‖x‖ → bchi ℓ x = 0 := fun x hx => bchi_eq_zero_of_half_lt hℓ hx
  have hχe : ∀ z : E3, bchi ℓ (-z) = bchi ℓ z := bchi_neg ℓ
  have hχcube : ∀ z : E3, z ∉ Submission.BoseGases.acube ℓ → bchi ℓ z = 0 :=
    fun z hz => bchi_eq_zero_of_notMem_acube hℓ hz
  -- the pointwise expansion of the periodisation on a pair of points of the cube
  have hexp : ∀ w y : E3, w ∈ Submission.BoseGases.acube ℓ → y ∈ Submission.BoseGases.acube ℓ →
      latPer3 ℓ W (w - y) = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ LatFourier.latFinSet ℓ R,
          ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) :=
    fun w y hw hy => latPer3_eq_sum_latFinSet hℓ hW (norm_sub_le_of_mem_acube hℓ.le hw hy)
  -- pointwise identification of the integrand with its expanded form, on the cube
  have hpt : ∀ w y : E3, w ∈ Submission.BoseGases.acube ℓ → y ∈ Submission.BoseGases.acube ℓ →
      bPhi ℓ W w y = bPsi ℓ W (LatFourier.latFinSet ℓ R) w y := by
    intro w y hw hy
    have hexp' := hexp w y hw hy
    unfold bPhi bPsi
    rw [hexp', Finset.mul_sum]
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  -- and everywhere (both sides vanish when one of the windows does)
  have hptg : ∀ w y : E3, bPhi ℓ W w y = bPsi ℓ W (LatFourier.latFinSet ℓ R) w y := by
    intro w y
    by_cases hw : w ∈ Submission.BoseGases.acube ℓ
    · by_cases hy : y ∈ Submission.BoseGases.acube ℓ
      · exact hpt w y hw hy
      · unfold bPhi bPsi
        rw [hχcube y hy]
        simp
    · unfold bPhi bPsi
      rw [hχcube w hw]
      simp
  -- integrability of the individual summands on the product
  have hIntm : ∀ m : Fin 3 → ℤ, Integrable (fun p : E3 × E3 =>
      ((ℓ ^ 3 : ℝ) : ℂ) * (bchi ℓ p.1 * ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ p.2))
      (volume.prod volume) := by
    intro m
    refine integrable_prod_of_bdd_of_supp (ρ := ℓ / 2) (σ := ℓ / 2) ?_ ?_ ?_ ?_
    · have hA : AEStronglyMeasurable (fun p : E3 × E3 => bchi ℓ p.1) (volume.prod volume) :=
        (hχc.comp continuous_fst).aestronglyMeasurable
      have hB : AEStronglyMeasurable
          (fun p : E3 × E3 => ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ)) (volume.prod volume) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable
          (aestronglyMeasurable_comp_sub_prod hWm (ℓ • latVec m))
      have hC : AEStronglyMeasurable (fun p : E3 × E3 => bchi ℓ p.2) (volume.prod volume) :=
        (hχc.comp continuous_snd).aestronglyMeasurable
      exact ((hA.mul hB).mul hC).const_mul _
    · refine ⟨‖((ℓ ^ 3 : ℝ) : ℂ)‖ * (Cχ * CW * Cχ), fun p => ?_⟩
      have hWp : ‖((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ)‖ ≤ CW := by
        rw [pinQ_norm_ofReal_complex]
        exact hCW _
      have hCχ0 : 0 ≤ Cχ := le_trans (norm_nonneg _) (hCχ p.1)
      have hCW0 : 0 ≤ CW := le_trans (norm_nonneg _) hWp
      have h4 : ‖bchi ℓ p.1 * ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ p.2‖
          ≤ Cχ * CW * Cχ := by
        rw [norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (hCχ p.1) hWp (norm_nonneg _) hCχ0)
          (hCχ p.2) (norm_nonneg _) (mul_nonneg hCχ0 hCW0)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    · intro p hp
      rw [bchi_eq_zero_of_half_lt hℓ hp]
      ring
    · intro p hp
      rw [bchi_eq_zero_of_half_lt hℓ hp]
      ring
  have hIntΨ : Integrable (fun p : E3 × E3 =>
      bPsi ℓ W (LatFourier.latFinSet ℓ R) p.1 p.2) (volume.prod volume) := by
    change Integrable (fun p : E3 × E3 => ∑ m ∈ LatFourier.latFinSet ℓ R,
        ((ℓ ^ 3 : ℝ) : ℂ)
          * (bchi ℓ p.1 * ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ p.2))
      (volume.prod volume)
    exact integrable_finsetSum _ (fun m _ => hIntm m)
  have hIntΦ : Integrable (fun p : E3 × E3 => bPhi ℓ W p.1 p.2) (volume.prod volume) :=
    hIntΨ.congr (μ := volume.prod volume)
      (f := fun p : E3 × E3 => bPsi ℓ W (LatFourier.latFinSet ℓ R) p.1 p.2)
      (g := fun p : E3 × E3 => bPhi ℓ W p.1 p.2)
      (Filter.Eventually.of_forall (fun p => (hptg p.1 p.2).symm))
  -- the restricted integrals are the unrestricted ones
  have hinner : ∀ w : E3,
      (∫ y in Submission.BoseGases.acube ℓ, bPhi ℓ W w y) = ∫ y, bPhi ℓ W w y := by
    intro w
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
    unfold bPhi
    rw [hχcube y hy]
    ring
  have houter : (∫ w in Submission.BoseGases.acube ℓ, ∫ y, bPhi ℓ W w y)
      = ∫ w, ∫ y, bPhi ℓ W w y := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => ?_)
    have hzero : (fun y : E3 => bPhi ℓ W w y) = fun _ => (0 : ℂ) := by
      funext y
      unfold bPhi
      rw [hχcube w hw]
      ring
    rw [hzero]
    simp
  have hstep1 : (∫ w in Submission.BoseGases.acube ℓ,
        ∫ y in Submission.BoseGases.acube ℓ, bPhi ℓ W w y)
      = ∫ w in Submission.BoseGases.acube ℓ, ∫ y, bPhi ℓ W w y :=
    integral_congr_ae (Filter.Eventually.of_forall (fun w => hinner w))
  have hF1 : (∫ w, ∫ y, bPhi ℓ W w y) = ∫ p : E3 × E3, bPhi ℓ W p.1 p.2 :=
    integral_integral hIntΦ
  -- the Fubini / sum-splitting / substitution argument
  have hHeart : ∀ m : Fin 3 → ℤ,
      (∫ w, ∫ y, bchi ℓ w * ((W (w - y + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ y)
        = bRhs ℓ W m := fun m =>
    integral_shift_pair_eq (c := ℓ • latVec m) (ξ := bchi ℓ) (W := W) (ρ := R) (σ := ℓ / 2)
      hχc hχb hχs hχe hWm hWb' hW
  have hbox : (∫ w in Submission.BoseGases.acube ℓ,
        ∫ y in Submission.BoseGases.acube ℓ, bPhi ℓ W w y)
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ LatFourier.latFinSet ℓ R, bRhs ℓ W m := by
    rw [hstep1, houter, hF1]
    have hcongr : (∫ p : E3 × E3, bPhi ℓ W p.1 p.2)
        = ∫ p : E3 × E3, bPsi ℓ W (LatFourier.latFinSet ℓ R) p.1 p.2 :=
      integral_congr_ae (Filter.Eventually.of_forall (fun p => hptg p.1 p.2))
    rw [hcongr]
    change (∫ p : E3 × E3, ∑ m ∈ LatFourier.latFinSet ℓ R,
        ((ℓ ^ 3 : ℝ) : ℂ)
          * (bchi ℓ p.1 * ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ p.2))
      = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ LatFourier.latFinSet ℓ R, bRhs ℓ W m
    calc (∫ p : E3 × E3, ∑ m ∈ LatFourier.latFinSet ℓ R,
        ((ℓ ^ 3 : ℝ) : ℂ)
          * (bchi ℓ p.1 * ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ p.2))
        = ∑ m ∈ LatFourier.latFinSet ℓ R, ∫ p : E3 × E3,
            ((ℓ ^ 3 : ℝ) : ℂ)
              * (bchi ℓ p.1 * ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ p.2) :=
          integral_finsetSum _ (fun m _ => hIntm m)
      _ = ∑ m ∈ LatFourier.latFinSet ℓ R, ((ℓ ^ 3 : ℝ) : ℂ) * bRhs ℓ W m := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          have hFub : (∫ p : E3 × E3, ((ℓ ^ 3 : ℝ) : ℂ)
              * (bchi ℓ p.1 * ((W (p.1 - p.2 + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ p.2))
              = ∫ x : E3, ∫ y : E3, ((ℓ ^ 3 : ℝ) : ℂ)
                * (bchi ℓ x * ((W (x - y + ℓ • latVec m) : ℝ) : ℂ) * bchi ℓ y) :=
            integral_prod _ (hIntm m)
          refine hFub.trans ?_
          simp only [integral_const_mul]
          exact congrArg (fun z : ℂ => ((ℓ ^ 3 : ℝ) : ℂ) * z) (hHeart m)
      _ = ((ℓ ^ 3 : ℝ) : ℂ) * ∑ m ∈ LatFourier.latFinSet ℓ R, bRhs ℓ W m :=
          (Finset.mul_sum _ _ _).symm
  -- the tail of the `ℓ`-lattice sum vanishes
  have htsum : (∑' m : Fin 3 → ℤ, bRhs ℓ W m)
      = ∑ m ∈ LatFourier.latFinSet ℓ R, bRhs ℓ W m := by
    refine tsum_eq_sum (s := LatFourier.latFinSet ℓ R) (fun m hm => ?_)
    have hfar : R + Real.sqrt 3 * ℓ < ℓ * ‖latVec m‖ := by
      have h2 : (R + Real.sqrt 3 * ℓ) / ℓ < ‖latVec m‖ := by
        rw [← not_le]
        intro h
        exact hm (LatFourier.mem_latFinSet.mpr h)
      have h3 := (div_lt_iff₀ hℓ).mp h2
      linarith
    have hzero : ∀ y x : E3,
        ((W y : ℝ) : ℂ) * bchi ℓ (x - y) * bchi ℓ (ℓ • latVec m - x) = 0 := by
      intro y x
      by_cases hWy : W y = 0
      · rw [hWy]
        simp
      · have hy : ‖y‖ ≤ R := le_of_not_gt (fun h => hWy (hW y h))
        by_cases hxy : bchi ℓ (x - y) = 0
        · rw [hxy]
          simp
        · by_cases hmx : bchi ℓ (ℓ • latVec m - x) = 0
          · rw [hmx]
            simp
          · exfalso
            have h1 : ‖x - y‖ ≤ ℓ / 2 :=
              le_of_not_gt (fun hlt => hxy (bchi_eq_zero_of_half_lt hℓ hlt))
            have h2 : ‖ℓ • latVec m - x‖ ≤ ℓ / 2 :=
              le_of_not_gt (fun hlt => hmx (bchi_eq_zero_of_half_lt hℓ hlt))
            have h3 : ℓ * ‖latVec m‖ ≤ R + Real.sqrt 3 * ℓ := by
              have h4 : ‖ℓ • latVec m‖ = ‖(ℓ • latVec m - x) + (x - y) + y‖ := by
                congr 1
                abel
              have h5 : ‖(ℓ • latVec m - x) + (x - y) + y‖ ≤ R + ℓ := by
                have h6 : ‖(ℓ • latVec m - x) + (x - y)‖ ≤ ‖ℓ • latVec m - x‖ + ‖x - y‖ :=
                  norm_add_le _ _
                calc ‖(ℓ • latVec m - x) + (x - y) + y‖
                    ≤ ‖(ℓ • latVec m - x) + (x - y)‖ + ‖y‖ := norm_add_le _ _
                  _ ≤ (‖ℓ • latVec m - x‖ + ‖x - y‖) + ‖y‖ := by linarith
                  _ ≤ R + ℓ := by linarith
              have h6 : ℓ * ‖latVec m‖ ≤ R + ℓ := by
                rw [← LatFourier.latVec_norm_smul ℓ hℓ.le m, h4]
                exact h5
              have h7 : (1 : ℝ) ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
              have h8 : ℓ ≤ Real.sqrt 3 * ℓ := by
                simpa [one_mul] using mul_le_mul_of_nonneg_right h7 hℓ.le
              linarith
            linarith
    change (∫ y, ∫ x,
        ((W y : ℝ) : ℂ) * bchi ℓ (x - y) * bchi ℓ (ℓ • latVec m - x)) = 0
    have hz : (fun y : E3 => ∫ x,
        ((W y : ℝ) : ℂ) * bchi ℓ (x - y) * bchi ℓ (ℓ • latVec m - x)) = fun _ => (0 : ℂ) := by
      funext y
      rw [show (fun x : E3 =>
            ((W y : ℝ) : ℂ) * bchi ℓ (x - y) * bchi ℓ (ℓ • latVec m - x)) = fun _ => (0 : ℂ)
          from funext (fun x => hzero y x)]
      simp
    rw [hz]
    simp
  -- assembly
  rw [pinQDl_eq_const hℓ hWm hWb' hWs hWev]
  change ((ℓ ^ 3)⁻¹ : ℝ) * (∑' m : Fin 3 → ℤ, bRhs ℓ W m)
      = (((ℓ ^ 3)⁻¹ : ℝ) * ((ℓ ^ 3)⁻¹ : ℝ))
        * (∫ w in Submission.BoseGases.acube ℓ,
            ∫ y in Submission.BoseGases.acube ℓ, bPhi ℓ W w y)
  rw [htsum, hbox]
  have hc : (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hRℓ3]
    norm_num
  calc (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (∑ m ∈ LatFourier.latFinSet ℓ R, bRhs ℓ W m)
      = ((((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ))
          * ((((ℓ ^ 3)⁻¹ : ℝ) : ℂ)
              * (∑ m ∈ LatFourier.latFinSet ℓ R, bRhs ℓ W m)) := by
        rw [hc, one_mul]
    _ = ((((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (((ℓ ^ 3)⁻¹ : ℝ) : ℂ))
          * (((ℓ ^ 3 : ℝ) : ℂ)
              * (∑ m ∈ LatFourier.latFinSet ℓ R, bRhs ℓ W m)) := by
        ring

end Work.BoseBoxFock
