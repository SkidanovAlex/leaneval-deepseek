import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Stability.Cutoff
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Blocks.aemeasurable_lintegral_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open MeasureTheory Set Filter

set_option autoImplicit false

private theorem ennreal_factor_swap (c c0 A : ENNReal) : c * (c0 * A) = c0 * (c * A) := by
  ring

private theorem ennreal_factor_common (c c0 c4 A B : ENNReal) :
    c * (c0 * (c4 * A + B)) = c0 * (c4 * (c * A) + c * B) := by
  ring

/-- Pulling the angular factor `ofReal (wth θ ^ 2)` inside a `z`-`lintegral`. -/
private theorem ofReal_sq_mul_lintegral (wth : ℝ → ℝ) (θ : ℝ) (Y : ℝ → ℝ) :
    ENNReal.ofReal (wth θ ^ 2) *
        MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun z => ENNReal.ofReal (Y z))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun z => ENNReal.ofReal (wth θ ^ 2 * Y z)) := by
  rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (wth θ ^ 2)) _
    ENNReal.ofReal_ne_top]
  exact MeasureTheory.lintegral_congr
    (fun z => (ENNReal.ofReal_mul (sq_nonneg (wth θ))).symm)

/-- The radial weight `w` is continuous on the open quadrant. -/
private theorem continuousOn_w_fst :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt (mem_Q0.mp hp).1)

/-! ## Step 1: the pointwise-in-`θ` inequality -/

private theorem pointwise (C1 α : ℝ) (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ)
    (hgen : ∀ (β : ℝ) (h : ℝ → ℝ), 0 < β → β ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)) →
      ENNReal.ofReal (β ^ 2) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (β ^ 4) *
                MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
              + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))))
    (hα : 0 < α) (hα1 : α ≤ 1) (hV : SmoothOpen V) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ENNReal.ofReal (α ^ 2) *
        MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun z => ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))
      ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) *
              MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                (fun z => ENNReal.ofReal
                  ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))) := by
  have h := hgen α (fun z' => V z' θ) hα hα1 (hV.curry_z hθ)
  -- the three rewriting identities, pulling `ofReal (wth θ ^ 2)` inside
  have hL : ENNReal.ofReal (wth θ ^ 2) *
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal
          ((Work.Spaces.w z) ^ 2 * (z * deriv (fun z' => V z' θ) z) ^ 2))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2)) := by
    rw [ofReal_sq_mul_lintegral]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    ring
  have hA : ENNReal.ofReal (wth θ ^ 2) *
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal
          ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv (fun z' => V z' θ)) z) ^ 2))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal
          ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2)) := by
    rw [ofReal_sq_mul_lintegral]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
    ring
  have hB : ENNReal.ofReal (wth θ ^ 2) *
      MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))
      = MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2)) := by
    rw [ofReal_sq_mul_lintegral]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    ring
  have hmul : ENNReal.ofReal (wth θ ^ 2) * (ENNReal.ofReal (α ^ 2) * MeasureTheory.lintegral
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => ENNReal.ofReal
          ((Work.Spaces.w z) ^ 2 * (z * deriv (fun z' => V z' θ) z) ^ 2)))
      ≤ ENNReal.ofReal (wth θ ^ 2) *
        (ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal
                ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv (fun z' => V z' θ)) z) ^ 2))
            + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2)))) :=
    mul_le_mul_of_nonneg_left h (zero_le : (0 : ENNReal) ≤ _)
  have hL'
      : ENNReal.ofReal (wth θ ^ 2) * (ENNReal.ofReal (α ^ 2) * MeasureTheory.lintegral
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
          (fun z => ENNReal.ofReal
            ((Work.Spaces.w z) ^ 2 * (z * deriv (fun z' => V z' θ) z) ^ 2)))
        = ENNReal.ofReal (α ^ 2) * MeasureTheory.lintegral
            (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal
              ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2)) := by
    rw [ennreal_factor_swap, hL]
  have hR' : ENNReal.ofReal (wth θ ^ 2) *
        (ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal
                ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv (fun z' => V z' θ)) z) ^ 2))
            + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (V z θ) ^ 2))))
      = ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal
                ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
            + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
              (fun z => ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))) := by
    rw [ennreal_factor_common, hA, hB]
  rw [hL', hR'] at hmul
  exact hmul




/-- **Unconditional subadditivity of the Lebesgue integral with measurable cofactors.**
For arbitrary (possibly nonmeasurable) `f` and measurable `g, h`:
`∫⁻ f·(g+h) ≤ ∫⁻ f·g + ∫⁻ f·h`.  This is the direction of `le_lintegral_add` that is not
available unconditionally in Mathlib; the proof uses the characterisation of the integral as a
supremum over measurable functions below it, splitting such a `u` into `u₁ ≤ f·g` and `u₂ ≤ f·h`
by the ratio `g/(g+h)`, with the two cases `g = ⊤` and `g + h = ⊤` treated separately. -/
private theorem lintegral_mul_add_le_aux {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {f g h : α → ENNReal} (hg : Measurable g) (hh : Measurable h) :
    MeasureTheory.lintegral μ (fun a => f a * (g a + h a))
      ≤ MeasureTheory.lintegral μ (fun a => f a * g a)
        + MeasureTheory.lintegral μ (fun a => f a * h a) := by
  classical
  rw [← iSup_lintegral_measurable_le_eq_lintegral (μ := μ)
    (fun a => f a * (g a + h a))]
  refine iSup_le fun u => iSup_le fun hum => iSup_le fun hule => ?_
  let ratio : α → ENNReal := fun a => g a * (g a + h a)⁻¹
  let ratio2 : α → ENNReal := fun a => h a * (g a + h a)⁻¹
  let S : Set α := {a | g a = ⊤} ∩ {a | g a + h a = ⊤}
  let T : Set α := {a | g a ≠ ⊤} ∩ {a | g a + h a = ⊤}
  let u1 : α → ENNReal := fun a => u a * ratio a + S.indicator u a
  let u2 : α → ENNReal := fun a => u a * ratio2 a + T.indicator u a
  have hratio : Measurable ratio := hg.mul (hg.add hh).inv
  have hratio2 : Measurable ratio2 := hh.mul (hg.add hh).inv
  have hgTop : MeasurableSet {a : α | g a = ⊤} := hg (measurableSet_singleton ⊤)
  have hghTop : MeasurableSet {a : α | g a + h a = ⊤} :=
    (hg.add hh) (measurableSet_singleton ⊤)
  have hS : MeasurableSet S := hgTop.inter hghTop
  have hT : MeasurableSet T := hgTop.compl.inter hghTop
  have hu1m : Measurable u1 := (hum.mul hratio).add (hum.indicator hS)
  have hu2m : Measurable u2 := (hum.mul hratio2).add (hum.indicator hT)
  have hratio_top : ∀ a, g a = ⊤ → ratio a = 0 := by
    intro a ha
    have hsum_top : g a + h a = ⊤ := by rw [ha]; simp
    simp only [ratio, hsum_top, ENNReal.inv_top, mul_zero]
  have hratio_gh_top : ∀ a, g a + h a = ⊤ → ratio a = 0 := by
    intro a ha
    simp only [ratio, ha, ENNReal.inv_top, mul_zero]
  have hratio2_top : ∀ a, g a + h a = ⊤ → ratio2 a = 0 := by
    intro a ha
    simp only [ratio2, ha, ENNReal.inv_top, mul_zero]
  have hS_of : ∀ a, g a = ⊤ → a ∈ S := by
    intro a ha
    refine ⟨ha, ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [ha]
    simp
  have hS_not' : ∀ a, g a ≠ ⊤ → a ∉ S := fun a hne hmem => hne hmem.1
  have hS_not : ∀ a, g a + h a ≠ ⊤ → a ∉ S := fun a hne hmem => hne hmem.2
  have hT_of : ∀ a, g a ≠ ⊤ → g a + h a = ⊤ → a ∈ T := fun a h1 h2 => ⟨h1, h2⟩
  have hT_not : ∀ a, g a = ⊤ → a ∉ T := fun a htop hmem => hmem.1 htop
  have hT_not' : ∀ a, g a + h a ≠ ⊤ → a ∉ T := fun a hne hmem => hne hmem.2
  have hsum : ∀ a, u1 a + u2 a = u a := by
    intro a
    by_cases hg_top : g a = ⊤
    · have hgh_top : g a + h a = ⊤ := by rw [hg_top]; simp
      simp only [u1, u2, Set.indicator_of_mem (hS_of a hg_top) u,
        Set.indicator_of_notMem (hT_not a hg_top) u, hratio_top a hg_top,
        hratio2_top a hgh_top]
      ring
    · by_cases hgh_top : g a + h a = ⊤
      · simp only [u1, u2, Set.indicator_of_notMem (hS_not' a hg_top) u,
          Set.indicator_of_mem (hT_of a hg_top hgh_top) u, hratio_gh_top a hgh_top,
          hratio2_top a hgh_top]
        ring
      · have hS' : a ∉ S := hS_not a hgh_top
        have hT' : a ∉ T := hT_not' a hgh_top
        by_cases h0 : g a + h a = 0
        · have hu0 : u a = 0 := by
            have hle0 : u a ≤ f a * (g a + h a) := hule a
            rw [h0, mul_zero] at hle0
            exact le_antisymm hle0 bot_le
          simp only [u1, u2, Set.indicator_of_notMem hS' u,
            Set.indicator_of_notMem hT' u, hu0]
          simp
        · have hinv := ENNReal.mul_inv_cancel h0 hgh_top
          simp only [u1, u2, Set.indicator_of_notMem hS' u,
            Set.indicator_of_notMem hT' u, add_zero]
          simp only [ratio, ratio2]
          calc u a * (g a * (g a + h a)⁻¹) + u a * (h a * (g a + h a)⁻¹)
              = u a * ((g a + h a) * (g a + h a)⁻¹) := by ring
            _ = u a * 1 := by rw [hinv]
            _ = u a := mul_one _
  have hle1 : ∀ a, u1 a ≤ f a * g a := by
    intro a
    have hu_le : u a ≤ f a * (g a + h a) := hule a
    by_cases hg_top : g a = ⊤
    · have hgh_top : g a + h a = ⊤ := by rw [hg_top]; simp
      have hfg : f a * (g a + h a) = f a * g a := by rw [hgh_top, hg_top]
      simp only [u1, Set.indicator_of_mem (hS_of a hg_top) u, hratio_top a hg_top,
        mul_zero, zero_add]
      exact le_trans hu_le (le_of_eq hfg)
    · by_cases hgh_top : g a + h a = ⊤
      · simp only [u1, Set.indicator_of_notMem (hS_not' a hg_top) u, add_zero,
          hratio_gh_top a hgh_top, mul_zero]
        exact bot_le
      · have hS' : a ∉ S := hS_not a hgh_top
        simp only [u1, Set.indicator_of_notMem hS' u, add_zero]
        simp only [ratio]
        by_cases h0 : g a + h a = 0
        · have hg0 : g a = 0 := (add_eq_zero.mp h0).1
          have hL : u a * (g a * (g a + h a)⁻¹) = 0 := by
            rw [h0, ENNReal.inv_zero, hg0, zero_mul, mul_zero]
          have hR : f a * g a = 0 := by rw [hg0, mul_zero]
          rw [hL, hR]
        · have hinv := ENNReal.mul_inv_cancel h0 hgh_top
          calc u a * (g a * (g a + h a)⁻¹)
              ≤ (f a * (g a + h a)) * (g a * (g a + h a)⁻¹) :=
                mul_le_mul_of_nonneg_right hu_le bot_le
            _ = (f a * g a) * ((g a + h a) * (g a + h a)⁻¹) := by ring
            _ = (f a * g a) * 1 := by rw [hinv]
            _ = f a * g a := mul_one _
  have hle2 : ∀ a, u2 a ≤ f a * h a := by
    intro a
    have hu_le : u a ≤ f a * (g a + h a) := hule a
    by_cases hg_top : g a = ⊤
    · have hgh_top : g a + h a = ⊤ := by rw [hg_top]; simp
      simp only [u2, Set.indicator_of_notMem (hT_not a hg_top) u, add_zero,
        hratio2_top a hgh_top, mul_zero]
      exact bot_le
    · by_cases hgh_top : g a + h a = ⊤
      · have hh_top : h a = ⊤ := by
          rcases ENNReal.add_eq_top.mp hgh_top with h' | h'
          · exact absurd h' hg_top
          · exact h'
        have hfg : f a * (g a + h a) = f a * h a := by rw [hgh_top, hh_top]
        simp only [u2, Set.indicator_of_mem (hT_of a hg_top hgh_top) u,
          hratio2_top a hgh_top, mul_zero, zero_add]
        exact le_trans hu_le (le_of_eq hfg)
      · have hT' : a ∉ T := hT_not' a hgh_top
        simp only [u2, Set.indicator_of_notMem hT' u, add_zero]
        simp only [ratio2]
        by_cases h0 : g a + h a = 0
        · have hh0 : h a = 0 := (add_eq_zero.mp h0).2
          have hL : u a * (h a * (g a + h a)⁻¹) = 0 := by
            rw [h0, ENNReal.inv_zero, hh0, zero_mul, mul_zero]
          have hR : f a * h a = 0 := by rw [hh0, mul_zero]
          rw [hL, hR]
        · have hinv := ENNReal.mul_inv_cancel h0 hgh_top
          calc u a * (h a * (g a + h a)⁻¹)
              ≤ (f a * (g a + h a)) * (h a * (g a + h a)⁻¹) :=
                mul_le_mul_of_nonneg_right hu_le bot_le
            _ = (f a * h a) * ((g a + h a) * (g a + h a)⁻¹) := by ring
            _ = (f a * h a) * 1 := by rw [hinv]
            _ = f a * h a := mul_one _
  calc MeasureTheory.lintegral μ u
      = MeasureTheory.lintegral μ (fun a => u1 a + u2 a) :=
        MeasureTheory.lintegral_congr (fun a => (hsum a).symm)
    _ = MeasureTheory.lintegral μ u1 + MeasureTheory.lintegral μ u2 :=
        MeasureTheory.lintegral_add_left hu1m u2
    _ ≤ MeasureTheory.lintegral μ (fun a => f a * g a)
          + MeasureTheory.lintegral μ (fun a => f a * h a) :=
        add_le_add (MeasureTheory.lintegral_mono hle1) (MeasureTheory.lintegral_mono hle2)


/-- **The `θ`-integrated weighted Agmon inequality (the interface consumed by the term-by-term
assembly of `HkNorm_Dz_amgm`).**

Assume the one-dimensional weighted Agmon inequality in `lintegral` form with constant `C1`
(`FTS/EllipticEst/Blocks/DzAgmonLintegral`):

  `∀ β h, 0 < β → β ≤ 1 → C^∞ h on (0,∞) →`
  `ofReal(β²) ∫⁻_z ofReal(w(z)² (z h')²) ≤ ofReal(C1²) ( ofReal(β⁴) ∫⁻_z ofReal(w(z)² (z²h'')²) + ∫⁻_z ofReal(w(z)² h²) )`.

Then the same inequality holds with the `z`-integration *inside* an angular integration with an
arbitrary nonnegative angular weight `wth`:

  `ofReal(α²) ∫⁻_θ∈(0,π/2) ∫⁻_{z>0} ofReal((D_zV · w z · wth θ)²)`
  `  ≤ ofReal(C1²) ( ofReal(α⁴) ∫⁻_θ ∫⁻_z ofReal((z² ∂_z²V · w z · wth θ)²) + ∫⁻_θ ∫⁻_z ofReal((V · w z · wth θ)²) )`

for every `V` smooth (`C^∞`) on the open quadrant and every `0 < α ≤ 1`.

ROUTE.  For `θ ∈ (0,π/2)` apply `hgen` to the slice `h = V(·,θ)` (smooth on `(0,∞)` by
`Work.FTS.EllipticEst.SmoothOpen.curry_z`), rewrite
`z · ∂_z(V(·,θ)) = D_z V (·,θ)` and `z² ∂_z²(V(·,θ)) = z² ∂_z²V (·,θ)` (definitional), multiply
both sides by `ofReal (wth θ)²` (`≥ 0`) and use
`ofReal(wth θ²) * ofReal(u²) = ofReal((wth θ · u)²)` together with `lintegral_const_mul` to move
the `θ`-weight inside the `z`-lintegral, then integrate the resulting inequality over
`θ ∈ (0,π/2)` (`lintegral_mono`).  A.e. (for `θ ∈ (0,π/2)`) suffices, so no smoothness at
`θ = 0, π/2` is needed; the a.e. strong measurability of the `z`-slices of the integrand comes
from continuity of the uncurried integrand on the open quadrant
(`Work.Spaces.aesm_of_continuousOn_Qd`, `SmoothOpen.continuousOn_*`). -/
theorem TermAgmon (C1 : ℝ) (hC1 : 0 < C1)
    (hgen : ∀ (β : ℝ) (h : ℝ → ℝ), 0 < β → β ≤ 1 →
      ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ)) →
      ENNReal.ofReal (β ^ 2) *
          MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
            (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (β ^ 4) *
                MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal
                    ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
              + MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                  (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)))) :
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ) (wth : ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ wth θ) →
      ENNReal.ofReal (α ^ 2) *
          (MeasureTheory.lintegral
              (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
              (fun θ => MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                (fun z => ENNReal.ofReal
                  ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2))))
        ≤ ENNReal.ofReal (C1 ^ 2) *
            (ENNReal.ofReal (α ^ 4) *
                (MeasureTheory.lintegral
                    (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                    (fun θ => MeasureTheory.lintegral
                      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                      (fun z => ENNReal.ofReal
                        ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))))
              + (MeasureTheory.lintegral
                  (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
                  (fun θ => MeasureTheory.lintegral
                    (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
                    (fun z => ENNReal.ofReal
                      ((V z θ * Work.Spaces.w z * wth θ) ^ 2))))) := by
  intro α V wth hα hα1 hV hwth
  set cf : ℝ → ENNReal := fun θ => ENNReal.ofReal (wth θ ^ 2) with hcf
  set Lf : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((Work.Spaces.Dz V z θ * Work.Spaces.w z * wth θ) ^ 2) with hLf
  set Af : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2)
    with hAf
  set Bf : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2) with hBf
  set A0 : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z) ^ 2) with hA0
  set B0 : ℝ → ENNReal := fun θ => ∫⁻ z in Set.Ioi (0 : ℝ),
    ENNReal.ofReal ((V z θ * Work.Spaces.w z) ^ 2) with hB0
  -- the pointwise-in-θ inequality
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ENNReal.ofReal (α ^ 2) * Lf θ
        ≤ ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ) := by
    intro θ hθ
    exact pointwise C1 α V wth hgen hα hα1 hV hθ
  have hmono : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal (α ^ 2) * Lf θ)
      ≤ ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall (fun θ hθ => hpt θ hθ)
  -- splitting off the common angular factor
  have hAf_cf : ∀ θ, Af θ = cf θ * A0 θ := by
    intro θ
    show (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z * wth θ) ^ 2))
      = ENNReal.ofReal (wth θ ^ 2) * (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z) ^ 2))
    rw [ofReal_sq_mul_lintegral wth θ
      (fun z => (z ^ 2 * Work.Spaces.pzIter 2 V z θ * Work.Spaces.w z) ^ 2)]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    ring
  have hBf_cf : ∀ θ, Bf θ = cf θ * B0 θ := by
    intro θ
    show (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal ((V z θ * Work.Spaces.w z * wth θ) ^ 2))
      = ENNReal.ofReal (wth θ ^ 2) * (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((V z θ * Work.Spaces.w z) ^ 2))
    rw [ofReal_sq_mul_lintegral wth θ (fun z => (V z θ * Work.Spaces.w z) ^ 2)]
    refine MeasureTheory.lintegral_congr (fun z => ?_)
    congr 1
    ring
  -- a.e. measurability of the angular slices of the two radial integrals
  have hA0m : AEMeasurable A0 (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (p.1 ^ 2 * Work.Spaces.pzIter 2 V p.1 p.2 * Work.Spaces.w p.1) ^ 2) Q0 :=
      (((continuousOn_fst.pow 2).mul ((hV.pzIter 2).continuousOn)).mul
        continuousOn_w_fst).pow 2
    have h := aemeasurable_lintegral_of_continuousOn_Qd hcont
    simpa only [hA0] using h
  have hB0m : AEMeasurable B0 (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ =>
        (V p.1 p.2 * Work.Spaces.w p.1) ^ 2) Q0 :=
      (((hV.continuousOn).mul continuousOn_w_fst)).pow 2
    have h := aemeasurable_lintegral_of_continuousOn_Qd hcont
    simpa only [hB0] using h
  obtain ⟨A0', hA0'meas, hA0'ae⟩ := hA0m
  obtain ⟨B0', hB0'meas, hB0'ae⟩ := hB0m
  -- the unconditional subadditivity with measurable cofactors
  have hkey := lintegral_mul_add_le_aux
    (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (f := cf) (g := fun θ => ENNReal.ofReal (α ^ 4) * A0' θ) (h := B0')
    (hA0'meas.const_mul _) hB0'meas
  -- rewriting the two sides of `hkey`
  have hi : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ))
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          cf θ * (ENNReal.ofReal (α ^ 4) * A0' θ + B0' θ) := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hA0'ae, hB0'ae] with θ h1 h2
    rw [hAf_cf θ, hBf_cf θ, h1, h2]
    ring
  have hii : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        cf θ * (ENNReal.ofReal (α ^ 4) * A0' θ))
      = ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Af θ) := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (α ^ 4)) _
      ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hA0'ae] with θ h1
    rw [hAf_cf θ, h1]
    ring
  have hiii : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), cf θ * B0' θ)
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Bf θ := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hB0'ae] with θ h1
    rw [← h1, hBf_cf θ]
  have hsub : (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ))
      ≤ ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Af θ)
        + ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Bf θ := by
    rw [hi]
    calc (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          cf θ * (ENNReal.ofReal (α ^ 4) * A0' θ + B0' θ))
        ≤ (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
              cf θ * (ENNReal.ofReal (α ^ 4) * A0' θ))
            + ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), cf θ * B0' θ := hkey
      _ = ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Af θ)
            + ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Bf θ := by rw [hii, hiii]
  calc ENNReal.ofReal (α ^ 2) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Lf θ)
      = ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), ENNReal.ofReal (α ^ 2) * Lf θ :=
        (MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (α ^ 2)) _
          ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
          ENNReal.ofReal (C1 ^ 2) * (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ) := hmono
    _ = ENNReal.ofReal (C1 ^ 2) *
          (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (ENNReal.ofReal (α ^ 4) * Af θ + Bf θ)) :=
        MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (C1 ^ 2)) _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C1 ^ 2) *
          (ENNReal.ofReal (α ^ 4) * (∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Af θ)
            + ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Bf θ) :=
        mul_le_mul_of_nonneg_left hsub (zero_le : (0 : ENNReal) ≤ _)


end Work.FTS.EllipticEst.Blocks
