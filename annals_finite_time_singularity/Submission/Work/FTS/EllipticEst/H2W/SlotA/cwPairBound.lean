import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
-- (the former import of `AngSecond/I1_ibp.lean` is dropped: this file only used
-- `AngSecond.abs_cw_le_two` from it, which is now reproduced locally below.  Importing `I1_ibp`
-- pulled in `AngSecond/I1_cut_alt.lean`, whose declarations clash with the `AngClean/I1_cut_alt`
-- copy for every consumer that needs both — see the note at `abs_cw_le_two_Iz`.)

/-!
# The Cauchy–Schwarz bound on the transfer term of `I₁`

In the chain for the `I₁` lower bound (Elgindi, Annals **194** (2021), tex 873–890) the term
produced by the `(w²)'`-part of the radial integration by parts is

```
X = - ⟨U, cw·B⟩ ,      U = z∂_zu ,  B = ∂_θ²u ,  cw z = 2 - 4/(1+z) = 2(z-1)/(1+z) ,
```

with `⟨g,h⟩ = AngSecond.IP g h = ∫_z∫_θ g h w²σ` and `σ θ = sin(2θ)^{-η}`.  Since `|cw z| ≤ 2` on
`z ≥ 0` (`AngSecond.abs_cw_le_two`) and the pairing is Cauchy–Schwarz
(`AngSecond.IP_cauchy_schwarz`),

```
⟨cw·U, B⟩ ≤ 2 √⟨U,U⟩ √⟨B,B⟩ ,
```

which is the `hX` input of the algebraic core `H2W.Ae.i1Lower_algebra_eta` (whose `hX` is stated
as `X ≥ -2 √(A·B)` with `A = ⟨U,U⟩`, `B = ⟨B,B⟩`).

## Design

The only structural fact used is that `cw` depends on `z` alone, so that in the `θ`-integral it
can be pulled out (`Integrable.const_mul` / `integral_const_mul`); the `z`-marginal is then
integrable by `Integrable.mono'` against `K * ‖marginal‖` because `|cw| ≤ 2` on `Iz`.  This is the
content of `IPMem_const_mul_left` below, applied to `cw` and to `cw · U` (the latter via the
symmetric form `IPMem U (cw·U)`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- `cw z = 2(z-1)/(1+z) = 2 - 4/(1+z)` is continuous on `Iz = [0,∞)`. -/
theorem continuousOn_cw :
    ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z) Work.Spaces.Iz := by
  have h1 : ContinuousOn (fun z : ℝ => 2 - 4 / (1 + z)) Work.Spaces.Iz := by
    refine continuousOn_const.sub ?_
    have h2 : ContinuousOn (fun z : ℝ => (1 + z : ℝ)) Work.Spaces.Iz := by fun_prop
    exact continuousOn_const.div h2 (fun z hz => by
      simp only [Work.Spaces.Iz, Set.mem_Ici] at hz
      positivity)
  refine h1.congr (fun z hz => ?_)
  have hz' : (1 : ℝ) + z ≠ 0 := by
    simp only [Work.Spaces.Iz, Set.mem_Ici] at hz
    positivity
  unfold Work.FTS.EllipticEst.AngSecond.cw
  field_simp
  ring

/-- `cw` is bounded by `2` on `Iz`.

(The statement and proof of `AngSecond.abs_cw_le_two` are reproduced here so that this file does
not import `AngSecond/I1_ibp.lean`: that module pulls in `AngSecond/I1_cut_alt.lean`, which
redeclares most of `AngClean/I1_cut_alt.lean` under the same namespace, and the two modules
together are a duplicate-declaration error for every consumer whose cone needs the
`AngClean`-side copy as well (e.g. `AeI1Fts/I1Paper_mixed.lean`).) -/
theorem abs_cw_le_two_Iz {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    |Work.FTS.EllipticEst.AngSecond.cw z| ≤ 2 := by
  have hz0 : (0 : ℝ) ≤ z := by
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : |z - 1| ≤ 1 + z := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Work.FTS.EllipticEst.AngSecond.cw, abs_div, abs_mul, abs_of_pos h1]
  rw [div_le_iff₀ h1]
  have h3 : |(2 : ℝ)| = 2 := by norm_num
  rw [h3]
  linarith

/-- **Honesty is preserved by multiplying the first slot by a `z`-only bounded factor.** -/
theorem IPMem_const_mul_left (c : ℝ → ℝ) (K : ℝ)
    (hc : ∀ z ∈ Work.Spaces.Iz, |c z| ≤ K)
    (hcaesm : AEStronglyMeasurable c (volume.restrict Work.Spaces.Iz))
    (U B : ℝ → ℝ → ℝ) (hUB : Work.FTS.EllipticEst.AngSecond.IPMem U B) :
    Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => c z * U z θ) B := by
  constructor
  · intro z hz
    refine ((hUB.1 z hz).const_mul (c z)).congr (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  · set M : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, U z θ * B z θ
      * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ with hM
    have hMint : MeasureTheory.Integrable M (volume.restrict Work.Spaces.Iz) := hUB.2
    have haesm : AEStronglyMeasurable (fun z => c z * M z) (volume.restrict Work.Spaces.Iz) :=
      hcaesm.mul hMint.aestronglyMeasurable
    have hbound : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), ‖c z * M z‖ ≤ K * ‖M z‖ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hc z hz) (abs_nonneg _)
    have hint : MeasureTheory.Integrable (fun z => c z * M z) (volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Integrable.mono' (hMint.norm.const_mul K) haesm hbound
    refine hint.congr (Filter.Eventually.of_forall (fun z => ?_))
    show c z * M z = ∫ θ in Work.Spaces.Iθ, (c z * U z θ) * B z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ
    have h1 : (∫ θ in Work.Spaces.Iθ, (c z * U z θ) * B z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        = ∫ θ in Work.Spaces.Iθ, c z * (U z θ * B z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      ring
    rw [h1, hM, MeasureTheory.integral_const_mul]

/-- **`IPMem` is symmetric in its two slots.** -/
theorem IPMem_symm {g h : ℝ → ℝ → ℝ} (hgh : Work.FTS.EllipticEst.AngSecond.IPMem g h) :
    Work.FTS.EllipticEst.AngSecond.IPMem h g := by
  constructor
  · intro z hz
    refine (hgh.1 z hz).congr (Filter.Eventually.of_forall (fun θ => ?_))
    ring
  · refine hgh.2.congr (Filter.Eventually.of_forall (fun z => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    ring

/-- **The transfer pairing is at most `2√⟨U,U⟩√⟨B,B⟩`** — the `hX` input of
`H2W.Ae.i1Lower_algebra_eta`. -/
theorem IP_cw_le (U B : ℝ → ℝ → ℝ)
    (hUU : Work.FTS.EllipticEst.AngSecond.IPMem U U)
    (hBB : Work.FTS.EllipticEst.AngSecond.IPMem B B)
    (hUB : Work.FTS.EllipticEst.AngSecond.IPMem U B) :
    Work.FTS.EllipticEst.AngSecond.IP (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U)
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) := by
  have hcw_aesm : AEStronglyMeasurable (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.cw z)
      (volume.restrict Work.Spaces.Iz) :=
    continuousOn_cw.aestronglyMeasurable measurableSet_Ici
  have hc : ∀ z ∈ Work.Spaces.Iz, |Work.FTS.EllipticEst.AngSecond.cw z| ≤ 2 :=
    fun z hz => abs_cw_le_two_Iz hz
  have hcwUB : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B :=
    IPMem_const_mul_left _ 2 hc hcw_aesm U B hUB
  have hcwUU : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
      (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) :=
    IPMem_const_mul_left _ 2 hc hcw_aesm U (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
      (IPMem_symm (IPMem_const_mul_left _ 2 hc hcw_aesm U U hUU))
  -- ## `⟨cw·U, cw·U⟩ ≤ 4⟨U,U⟩`
  have hquad : Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
      ≤ 4 * Work.FTS.EllipticEst.AngSecond.IP U U := by
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        ≤ 4 * (∫ θ in Work.Spaces.Iθ, U z θ * U z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      intro z hz
      have hR : MeasureTheory.IntegrableOn (fun θ => 4 * (U z θ * U z θ
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ))
          Work.Spaces.Iθ :=
        (hUU.1 z hz).const_mul 4
      have hL : MeasureTheory.IntegrableOn (fun θ => (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
          Work.Spaces.Iθ :=
        ((hUU.1 z hz).const_mul (Work.FTS.EllipticEst.AngSecond.cw z ^ 2)).congr
          (Filter.Eventually.of_forall (fun θ => by ring))
      have hpt : ∀ θ ∈ Work.Spaces.Iθ, (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ
          ≤ 4 * (U z θ * U z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
        intro θ hθ
        have hw := Work.FTS.EllipticEst.AngSecond.w2_nonneg z
        have hs := Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ
        have h2 := abs_cw_le_two_Iz hz
        have hcw2 : Work.FTS.EllipticEst.AngSecond.cw z ^ 2 ≤ 4 := by
          have h4 := pow_le_pow_left₀
            (abs_nonneg (Work.FTS.EllipticEst.AngSecond.cw z)) h2 2
          norm_num at h4
          exact h4
        have hnn : 0 ≤ U z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ :=
          mul_nonneg (mul_nonneg (sq_nonneg _) hw) hs
        calc (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
              * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
              * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ
            = Work.FTS.EllipticEst.AngSecond.cw z ^ 2
              * (U z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
          _ ≤ 4 * (U z θ ^ 2 * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) :=
              mul_le_mul_of_nonneg_right hcw2 hnn
          _ = 4 * (U z θ * U z θ * Work.FTS.EllipticEst.AngSecond.w2 z
                * Work.FTS.EllipticEst.AngSecond.sig θ) := by ring
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_mono_ae hL hR
        ((MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall hpt))
    have hR : MeasureTheory.IntegrableOn (fun z => 4 * (∫ θ in Work.Spaces.Iθ, U z θ * U z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ))
        Work.Spaces.Iz :=
      hUU.2.const_mul 4
    have hout : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
        ≤ ∫ z in Work.Spaces.Iz, 4 * (∫ θ in Work.Spaces.Iθ, U z θ * U z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := by
      refine MeasureTheory.integral_mono_ae hcwUU.2 hR ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
      exact hinner z hz
    calc Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
              * (Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
              * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, 4 * (∫ θ in Work.Spaces.Iθ, U z θ * U z θ
            * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ) := hout
      _ = 4 * Work.FTS.EllipticEst.AngSecond.IP U U := by
          rw [MeasureTheory.integral_const_mul]
          rfl
  -- ## Cauchy–Schwarz and the square root
  have hcs := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz hcwUU hBB hcwUB
  have hsqrt : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ))
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U) := by
    have h1 := Real.sqrt_le_sqrt hquad
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith [Real.sqrt_nonneg (4 : ℝ), h]
    rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4] at h1
  calc Work.FTS.EllipticEst.AngSecond.IP
        (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B
      ≤ |Work.FTS.EllipticEst.AngSecond.IP
          (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B| := le_abs_self _
    _ ≤ Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ)
            (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) := hcs
    _ ≤ (2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U))
          * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) :=
        mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)

/-- **The transfer pairing in the `√(A·B)` shape** consumed by
`H2W.Ae.i1Lower_algebra_eta`. -/
theorem IP_cw_le_sqrt (U B : ℝ → ℝ → ℝ)
    (hUU : Work.FTS.EllipticEst.AngSecond.IPMem U U)
    (hBB : Work.FTS.EllipticEst.AngSecond.IPMem B B)
    (hUB : Work.FTS.EllipticEst.AngSecond.IPMem U B) :
    Work.FTS.EllipticEst.AngSecond.IP (fun z θ => Work.FTS.EllipticEst.AngSecond.cw z * U z θ) B
      ≤ 2 * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U
          * Work.FTS.EllipticEst.AngSecond.IP B B) := by
  have h1 := IP_cw_le U B hUU hBB hUB
  have h2 : Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U
      * Work.FTS.EllipticEst.AngSecond.IP B B)
      = Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP U U)
        * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP B B) := by
    refine Real.sqrt_mul ?_ _
    rw [Work.FTS.EllipticEst.AngSecond.IP]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z _ =>
      MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
        mul_nonneg (mul_nonneg (mul_self_nonneg (U z θ))
          (Work.FTS.EllipticEst.AngSecond.w2_nonneg z))
          (Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ)))
  rw [h2]
  exact le_trans h1 (le_of_eq (by ring))

end Work.FTS.EllipticEst.H2W.SlotA
