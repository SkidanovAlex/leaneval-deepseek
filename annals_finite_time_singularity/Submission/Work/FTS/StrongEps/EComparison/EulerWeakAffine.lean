/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EulerWeakAffine`

If a locally integrable function `F` on an open interval `(a,b)` is orthogonal to every smooth
compactly supported test function on `(a,b)` whose zeroth and first moments vanish, then `F`
agrees almost everywhere on `(a,b)` with an affine function `t ↦ c₁ + c₂ * t`.

## The argument

Write `M₀ ψ = ∫_{a..b} ψ` and `M₁ ψ = ∫_{a..b} t * ψ t` for the two moments.  The hypothesis says
that the linear functional `L ψ = ∫_{a..b} ψ * F` vanishes on `ker M₀ ∩ ker M₁`.  It therefore
suffices to exhibit two test functions `η₁`, `η₂` with moment vectors `(M₀,M₁)` equal to `(1,0)`
and `(0,1)`: then for every test function `ψ` the function `ψ - (M₀ ψ) * η₁ - (M₁ ψ) * η₂` is a
test function with vanishing moments, so

`∫ ψ * F = (M₀ ψ) * ∫ η₁ * F + (M₁ ψ) * ∫ η₂ * F`.

Such a pair is built from a single `C^∞` bump `χ` supported in `(a,b)` with `∫ χ = 1`
(`Work.FTS.StrongEps.EComparison.existsBumpMoments`), which additionally satisfies
`∫ deriv χ = 0` and `∫ t * deriv χ t = -1` (the fundamental theorem of calculus and one
integration by parts).  The moment matrix of the pair `(χ, deriv χ)` is therefore
`[[1, c], [0, -1]]` with `c = ∫ t * χ t`, and its dual basis is

`η₁ = χ + c * deriv χ`,  `η₂ = -deriv χ`.

Then the function `F - (∫ η₁ * F) - (∫ η₂ * F) · t` is orthogonal to *every* test function, and
the fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`, Mathlib) finishes the proof.
-/
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Submission.Work.FTS.StrongEps.EComparison.existsBumpMoments

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

set_option autoImplicit false

/-- A function vanishing outside the open interval `(a,b)` has the same integral over `a..b` as
over the whole line. -/
theorem intervalIntegral_eq_integral_of_vanishing {a b : ℝ} (hab : a ≤ b) {φ : ℝ → ℝ}
    (hφ : ∀ x ∉ Set.Ioo a b, φ x = 0) : (∫ x in a..b, φ x) = ∫ x, φ x := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => hφ x (fun hc => hx ⟨hc.1, hc.2.le⟩))

/-- If `F` is locally integrable on `(a,b)` and `ψ` is continuous with compact support in `(a,b)`,
then `ψ * F` is globally integrable. -/
theorem integrable_mul_of_locallyIntegrableOn_Ioo {a b : ℝ} {F ψ : ℝ → ℝ}
    (hF : LocallyIntegrableOn F (Set.Ioo a b)) (hψcont : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (hψsup : tsupport ψ ⊆ Set.Ioo a b) :
    Integrable (fun x => ψ x * F x) := by
  let K : Set ℝ := tsupport ψ
  have hK : IsCompact K := hψcs
  have hFK : IntegrableOn F K := hF.integrableOn_compact_subset hψsup hK
  have hFind : Integrable (K.indicator F) := by
    rw [integrable_indicator_iff hK.measurableSet]
    exact hFK
  have hkey : Integrable (fun x => ψ x • (K.indicator F) x) :=
    LocallyIntegrable.integrable_smul_left_of_hasCompactSupport hFind.locallyIntegrable hψcont hψcs
  have hprod : (fun x => ψ x * F x) = fun x => ψ x • (K.indicator F) x := by
    funext x
    by_cases hx : x ∈ K
    · simp [Set.indicator_of_mem hx, smul_eq_mul]
    · have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [Set.indicator_of_notMem hx, hz]
  rwa [hprod]

/-- **The two-moment elimination.**  Given the moment identities of a normalised bump `χ` on
`(a,b)`, the pairing of `F` against an arbitrary test function is a fixed linear combination of
the first two moments of that test function. -/
theorem momentRepresentation {a b : ℝ} {F : ℝ → ℝ}
    (hF : LocallyIntegrableOn F (Set.Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b → (∫ t in a..b, ψ t) = 0 → (∫ t in a..b, t * ψ t) = 0 →
      (∫ t in a..b, ψ t * F t) = 0)
    {χ : ℝ → ℝ} (hχcd : ContDiff ℝ ∞ χ) (hχcs : HasCompactSupport χ)
    (hχsup : tsupport χ ⊆ Set.Ioo a b) (hχint : (∫ t in a..b, χ t) = 1)
    (hχd0 : (∫ t in a..b, deriv χ t) = 0) (hχd1 : (∫ t in a..b, t * deriv χ t) = -1) :
    ∃ c₁ c₂ : ℝ, ∀ ψ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      tsupport ψ ⊆ Set.Ioo a b →
      (∫ t in a..b, ψ t * F t) = c₁ * (∫ t in a..b, ψ t) + c₂ * (∫ t in a..b, t * ψ t) := by
  -- the first moment of `χ`, and the dual pair `η₁`, `η₂`
  set c : ℝ := ∫ t in a..b, t * χ t with hc
  set η₁ : ℝ → ℝ := fun t => χ t + c * deriv χ t with hη₁
  set η₂ : ℝ → ℝ := fun t => (-1 : ℝ) * deriv χ t with hη₂
  have hχcont : Continuous χ := hχcd.continuous
  have hdχ : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχcd).2
  have hdcont : Continuous (deriv χ) := hdχ.continuous
  have hcd : ∀ n : ℕ, ContDiff ℝ n χ := fun n => hχcd.of_le (WithTop.coe_le_coe.mpr le_top)
  have hdcd : ∀ n : ℕ, ContDiff ℝ n (deriv χ) := fun n => hdχ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hη₁cd : ∀ n : ℕ, ContDiff ℝ n η₁ := by
    intro n
    rw [hη₁]
    simpa only [smul_eq_mul] using (hcd n).add ((hdcd n).const_smul c)
  have hη₂cd : ∀ n : ℕ, ContDiff ℝ n η₂ := by
    intro n
    rw [hη₂]
    simpa only [smul_eq_mul] using (hdcd n).const_smul (-1 : ℝ)
  have hη₁cont : Continuous η₁ := (hη₁cd 0).continuous
  have hη₂cont : Continuous η₂ := (hη₂cd 0).continuous
  -- interval integrability of the pieces
  have hχII : IntervalIntegrable χ volume a b := hχcont.intervalIntegrable a b
  have hdII : IntervalIntegrable (deriv χ) volume a b := hdcont.intervalIntegrable a b
  have htχII : IntervalIntegrable (fun t : ℝ => t * χ t) volume a b :=
    (continuous_id.mul hχcont).intervalIntegrable a b
  have htdII : IntervalIntegrable (fun t : ℝ => t * deriv χ t) volume a b :=
    (continuous_id.mul hdcont).intervalIntegrable a b
  have hη₁II : IntervalIntegrable η₁ volume a b := hη₁cont.intervalIntegrable a b
  have hη₂II : IntervalIntegrable η₂ volume a b := hη₂cont.intervalIntegrable a b
  -- supports
  have hη₁sup : tsupport η₁ ⊆ Set.Ioo a b := by
    rw [hη₁]
    refine (tsupport_binop_subset (fun x y : ℝ => x + y) (by norm_num) χ
      (fun t => c * deriv χ t)).trans ?_
    exact union_subset hχsup (((tsupport_mul_subset_right (f := fun _ : ℝ => c)).trans
      (tsupport_deriv_subset)).trans hχsup)
  have hη₂sup : tsupport η₂ ⊆ Set.Ioo a b := by
    rw [hη₂]
    exact ((tsupport_mul_subset_right (f := fun _ : ℝ => (-1 : ℝ))).trans
      (tsupport_deriv_subset)).trans hχsup
  have hη₁cs : HasCompactSupport η₁ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport η₁).trans (hη₁sup.trans Ioo_subset_Icc_self))
  have hη₂cs : HasCompactSupport η₂ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport η₂).trans (hη₂sup.trans Ioo_subset_Icc_self))
  -- the moment identities making `(η₁, η₂)` the dual basis of `(M₀, M₁)`
  have hm₁ : (∫ t in a..b, η₁ t) = 1 := by
    have hs : (∫ t in a..b, η₁ t) = (∫ t in a..b, χ t) + ∫ t in a..b, c * deriv χ t := by
      calc (∫ t in a..b, η₁ t) = ∫ t in a..b, (χ t + c * deriv χ t) :=
            intervalIntegral.integral_congr (fun t _ => by simp only [hη₁])
        _ = _ := intervalIntegral.integral_add hχII (hdII.const_mul c)
    rw [hs, intervalIntegral.integral_const_mul, hχd0, mul_zero, add_zero, hχint]
  have hm₂ : (∫ t in a..b, t * η₁ t) = 0 := by
    have hs : (∫ t in a..b, t * η₁ t)
        = (∫ t in a..b, t * χ t) + ∫ t in a..b, c * (t * deriv χ t) := by
      calc (∫ t in a..b, t * η₁ t) = ∫ t in a..b, (t * χ t + c * (t * deriv χ t)) :=
            intervalIntegral.integral_congr (fun t _ => by simp only [hη₁]; ring)
        _ = _ := intervalIntegral.integral_add htχII (htdII.const_mul c)
    rw [hs, intervalIntegral.integral_const_mul, hχd1, ← hc]
    ring
  have hn₁ : (∫ t in a..b, η₂ t) = 0 := by
    have hs : (∫ t in a..b, η₂ t) = ∫ t in a..b, (-1 : ℝ) * deriv χ t :=
      intervalIntegral.integral_congr (fun t _ => by simp only [hη₂])
    rw [hs, intervalIntegral.integral_const_mul, hχd0, mul_zero]
  have hn₂ : (∫ t in a..b, t * η₂ t) = 1 := by
    have hs : (∫ t in a..b, t * η₂ t) = ∫ t in a..b, (-1 : ℝ) * (t * deriv χ t) :=
      intervalIntegral.integral_congr (fun t _ => by simp only [hη₂]; ring)
    rw [hs, intervalIntegral.integral_const_mul, hχd1]
    norm_num
  -- the two candidate constants
  have hIFη₁ : Integrable (fun t => η₁ t * F t) :=
    integrable_mul_of_locallyIntegrableOn_Ioo hF hη₁cont hη₁cs hη₁sup
  have hIFη₂ : Integrable (fun t => η₂ t * F t) :=
    integrable_mul_of_locallyIntegrableOn_Ioo hF hη₂cont hη₂cs hη₂sup
  refine ⟨∫ t in a..b, η₁ t * F t, ∫ t in a..b, η₂ t * F t, ?_⟩
  intro ψ hψcd hψcs hψsup
  -- the corrected test function
  set M : ℝ := ∫ t in a..b, ψ t with hM
  set N : ℝ := ∫ t in a..b, t * ψ t with hN
  set ψ₀ : ℝ → ℝ := fun t => ψ t - M * η₁ t - N * η₂ t with hψ₀
  have hψcont : Continuous ψ := (hψcd 0).continuous
  have hψII : IntervalIntegrable ψ volume a b := hψcont.intervalIntegrable a b
  have htψII : IntervalIntegrable (fun t : ℝ => t * ψ t) volume a b :=
    (continuous_id.mul hψcont).intervalIntegrable a b
  have hψ₀cd : ∀ n : ℕ, ContDiff ℝ n ψ₀ := by
    intro n
    rw [hψ₀]
    have h1 : ContDiff ℝ (↑n) (fun t : ℝ => ψ t - M * η₁ t) := by
      simpa only [smul_eq_mul] using (hψcd n).sub ((hη₁cd n).const_smul M)
    simpa only [smul_eq_mul] using h1.sub ((hη₂cd n).const_smul N)
  have hψ₀sup : tsupport ψ₀ ⊆ Set.Ioo a b := by
    rw [hψ₀]
    refine (tsupport_binop_subset (fun x y : ℝ => x - y) (by norm_num)
      (fun t => ψ t - M * η₁ t) (fun t => N * η₂ t)).trans ?_
    refine union_subset ?_ (((tsupport_mul_subset_right (f := fun _ : ℝ => N)).trans hη₂sup))
    refine (tsupport_binop_subset (fun x y : ℝ => x - y) (by norm_num) ψ
      (fun t => M * η₁ t)).trans ?_
    exact union_subset hψsup (((tsupport_mul_subset_right (f := fun _ : ℝ => M)).trans hη₁sup))
  have hψ₀cs : HasCompactSupport ψ₀ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport ψ₀).trans (hψ₀sup.trans Ioo_subset_Icc_self))
  -- its moments vanish
  have hψ₀m0 : (∫ t in a..b, ψ₀ t) = 0 := by
    have hMη₁ : IntervalIntegrable (fun t : ℝ => M * η₁ t) volume a b := hη₁II.const_mul M
    have hNη₂ : IntervalIntegrable (fun t : ℝ => N * η₂ t) volume a b := hη₂II.const_mul N
    calc (∫ t in a..b, ψ₀ t) = ∫ t in a..b, (ψ t - (M * η₁ t + N * η₂ t)) :=
          intervalIntegral.integral_congr (fun t _ => by simp only [hψ₀]; ring)
      _ = (∫ t in a..b, ψ t) - ∫ t in a..b, (M * η₁ t + N * η₂ t) :=
          intervalIntegral.integral_sub hψII (hMη₁.add hNη₂)
      _ = (∫ t in a..b, ψ t) - ((∫ t in a..b, M * η₁ t) + ∫ t in a..b, N * η₂ t) := by
          rw [intervalIntegral.integral_add hMη₁ hNη₂]
      _ = M - (M * (∫ t in a..b, η₁ t) + N * (∫ t in a..b, η₂ t)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hM]
      _ = 0 := by rw [hm₁, hn₁]; ring
  have hψ₀m1 : (∫ t in a..b, t * ψ₀ t) = 0 := by
    have hMη₁ : IntervalIntegrable (fun t : ℝ => M * (t * η₁ t)) volume a b :=
      ((continuous_id.mul hη₁cont).intervalIntegrable a b).const_mul M
    have hNη₂ : IntervalIntegrable (fun t : ℝ => N * (t * η₂ t)) volume a b :=
      ((continuous_id.mul hη₂cont).intervalIntegrable a b).const_mul N
    calc (∫ t in a..b, t * ψ₀ t)
        = ∫ t in a..b, (t * ψ t - (M * (t * η₁ t) + N * (t * η₂ t))) :=
          intervalIntegral.integral_congr (fun t _ => by simp only [hψ₀]; ring)
      _ = (∫ t in a..b, t * ψ t) - ∫ t in a..b, (M * (t * η₁ t) + N * (t * η₂ t)) :=
          intervalIntegral.integral_sub htψII (hMη₁.add hNη₂)
      _ = (∫ t in a..b, t * ψ t)
            - ((∫ t in a..b, M * (t * η₁ t)) + ∫ t in a..b, N * (t * η₂ t)) := by
          rw [intervalIntegral.integral_add hMη₁ hNη₂]
      _ = N - (M * (∫ t in a..b, t * η₁ t) + N * (∫ t in a..b, t * η₂ t)) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← hN]
      _ = 0 := by rw [hm₂, hn₂]; ring
  have hkey : (∫ t in a..b, ψ₀ t * F t) = 0 := h ψ₀ hψ₀cd hψ₀cs hψ₀sup hψ₀m0 hψ₀m1
  -- expanding the pairing of `ψ₀` with `F`
  have hIFψ : Integrable (fun t => ψ t * F t) :=
    integrable_mul_of_locallyIntegrableOn_Ioo hF hψcont hψcs hψsup
  have hsplit : (∫ t in a..b, ψ₀ t * F t)
      = (∫ t in a..b, ψ t * F t) - M * (∫ t in a..b, η₁ t * F t)
        - N * (∫ t in a..b, η₂ t * F t) := by
    have h1 : IntervalIntegrable (fun t : ℝ => ψ t * F t) volume a b := hIFψ.intervalIntegrable
    have h2 : IntervalIntegrable (fun t : ℝ => M * (η₁ t * F t)) volume a b :=
      hIFη₁.intervalIntegrable.const_mul M
    have h3 : IntervalIntegrable (fun t : ℝ => N * (η₂ t * F t)) volume a b :=
      hIFη₂.intervalIntegrable.const_mul N
    calc (∫ t in a..b, ψ₀ t * F t)
        = ∫ t in a..b, ((ψ t * F t - M * (η₁ t * F t)) - N * (η₂ t * F t)) :=
          intervalIntegral.integral_congr (fun t _ => by simp only [hψ₀]; ring)
      _ = (∫ t in a..b, (ψ t * F t - M * (η₁ t * F t)))
            - ∫ t in a..b, N * (η₂ t * F t) :=
          intervalIntegral.integral_sub (h1.sub h2) h3
      _ = ((∫ t in a..b, ψ t * F t) - ∫ t in a..b, M * (η₁ t * F t))
            - ∫ t in a..b, N * (η₂ t * F t) := by rw [intervalIntegral.integral_sub h1 h2]
      _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hgoal : (∫ t in a..b, ψ t * F t)
      = (∫ t in a..b, η₁ t * F t) * M + (∫ t in a..b, η₂ t * F t) * N := by
    linarith [hkey, hsplit]
  exact hgoal

/-- **Orthogonality to test functions with two vanishing moments forces affinity.**  If a locally
integrable `F` on `(a,b)` is orthogonal (as a distribution) to every smooth compactly supported
test function on `(a,b)` whose zeroth and first moments vanish, then `F` is almost everywhere
affine on `(a,b)`. -/
theorem EulerWeakAffine {a b : ℝ} (hab : a < b) {F : ℝ → ℝ} (hF : MeasureTheory.LocallyIntegrableOn F (Set.Ioo a b))
    (h : ∀ ψ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b →
      (∫ t in a..b, ψ t) = 0 → (∫ t in a..b, t * ψ t) = 0 → (∫ t in a..b, ψ t * F t) = 0) :
    ∃ c₁ c₂ : ℝ, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioo a b)), F t = c₁ + c₂ * t := by
  obtain ⟨χ, hχcd, hχcs, hχsup, hχint, hχd0, hχd1⟩ := existsBumpMoments hab
  obtain ⟨c₁, c₂, hkey⟩ := momentRepresentation hF h hχcd hχcs hχsup hχint hχd0 hχd1
  refine ⟨c₁, c₂, ?_⟩
  -- `F - (c₁ + c₂ ·)` is orthogonal to every test function
  have hfli : LocallyIntegrableOn (fun t => F t - (c₁ + c₂ * t)) (Set.Ioo a b) :=
    hF.sub (((continuous_const.add (continuous_const.mul continuous_id)).locallyIntegrable).locallyIntegrableOn _)
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioo a b → F t - (c₁ + c₂ * t) = 0 := by
    refine IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo hfli ?_
    intro ψ hψcd hψcs hψsup
    have hψcd' : ∀ n : ℕ, ContDiff ℝ n ψ := fun n => hψcd.of_le (WithTop.coe_le_coe.mpr le_top)
    have hψcont : Continuous ψ := (hψcd' 0).continuous
    have hIFψ : Integrable (fun t => ψ t * F t) :=
      integrable_mul_of_locallyIntegrableOn_Ioo hF hψcont hψcs hψsup
    have hIψ : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψcs
    have htψ : Integrable (fun t => t * ψ t) :=
      (continuous_id.mul hψcont).integrable_of_hasCompactSupport hψcs.mul_left
    have h1 : (∫ t in a..b, ψ t * (F t - (c₁ + c₂ * t))) = 0 := by
      have hIFψII : IntervalIntegrable (fun t : ℝ => ψ t * F t) volume a b := hIFψ.intervalIntegrable
      have hIψII : IntervalIntegrable ψ volume a b := hψcont.intervalIntegrable a b
      have htψII : IntervalIntegrable (fun t : ℝ => t * ψ t) volume a b :=
        (continuous_id.mul hψcont).intervalIntegrable a b
      calc (∫ t in a..b, ψ t * (F t - (c₁ + c₂ * t)))
          = ∫ t in a..b, (ψ t * F t - c₁ * ψ t - c₂ * (t * ψ t)) :=
            intervalIntegral.integral_congr (fun t _ => by ring)
        _ = (∫ t in a..b, ψ t * F t) - c₁ * (∫ t in a..b, ψ t)
              - c₂ * (∫ t in a..b, t * ψ t) := by
            rw [intervalIntegral.integral_sub (hIFψII.sub (hIψII.const_mul c₁)) (htψII.const_mul c₂),
              intervalIntegral.integral_sub hIFψII (hIψII.const_mul c₁),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        _ = 0 := by rw [hkey ψ hψcd' hψcs hψsup]; ring
    have hvan : ∀ x ∉ Set.Ioo a b, ψ x * (F x - (c₁ + c₂ * x)) = 0 := by
      intro x hx
      have hxψ : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun hc => hx (hψsup hc))
      rw [hxψ, zero_mul]
    have hconv : (∫ x, ψ x • (F x - (c₁ + c₂ * x)))
        = ∫ x in a..b, ψ x * (F x - (c₁ + c₂ * x)) := by
      simp only [smul_eq_mul]
      exact (intervalIntegral_eq_integral_of_vanishing hab.le hvan).symm
    rw [hconv, h1]
  -- transfer the a.e. statement to the restricted measure
  rw [ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae] with t ht hmem
  linarith [ht hmem]

end Work.FTS.StrongEps.EComparison
