/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `sin(2θ)`-weighted Hardy inequality on the open interval

For `0 ≤ η < 1` and a function `v` of class `C¹` on `(0,π/2)` whose endpoint *traces* vanish,
`v → 0` at `0⁺` and at `(π/2)⁻`, one has

  `∫ ofReal (v² cos²(2θ) sin(2θ)^{-(2+η)}) ≤ K · ∫ ofReal ((v')² sin(2θ)^{-η})`,
  `K = (π/4)^{2+η} · 2^η · 4/(1+η)²`,

as an inequality of Lebesgue integrals in `ℝ≥0∞` — so *no* integrability hypothesis on the
left-hand side is needed, and the left-hand side is finite as soon as the right-hand one is.
This is the ingredient that converts the `w²`-weighted `V`-energy of a weak-class datum into an
`N`-bound for the slice `U u z · = z ∂_z u (z,·)`.

## Route

* `powerHardy_at` — the sharp power-weighted Hardy inequality on a compact interval `[ε,a]`
  anchored at `ε` (a `C¹` function vanishing at the left endpoint).
* `powerHardy_open` — its form on the *open* interval `(0,a)` with a vanishing left trace, as a
  `∫⁻`-inequality; obtained from `powerHardy_at` on the truncations `[a/(n+2), a - a/(n+3)]` and
  Fatou's lemma.
* `lintegral_reflect_Ioo`, `lintegral_split_pi` — the reflection `θ ↦ 2a - θ` of a Lebesgue
  integral, and the splitting at the midpoint `π/4`.
* the proof of `powerHardySinOpen` splits `(0,π/2)` at `π/4`, compares the `sin(2θ)`-weights with
  the powers `φ^{-(2+η)}`, `φ^{-η}` on `(0,π/4)` (valid because `sin(2φ) ≥ (4/π)φ` there) and
  applies `powerHardy_open`; the right half is handled by the same bound for the reflected slice
  `φ ↦ v (π/2 - φ)` and transported back by `lintegral_reflect_Ioo`.

## Provenance

The three lemmas `powerHardy_at`, `lintegral_Ioo_ofReal_eq`, `powerHardy_open` and the two
interval lemmas `lintegral_reflect_Ioo`, `lintegral_split_pi` are reproduced from the sibling
module `Submission/Work/FTS/EllipticEst/TT/sliceHardyWeak.lean` (which is being reworked in
place and does not currently build); they are kept in the namespace of this module so that
`Work.FTS.EllipticEst.AeI1Fts.N_bound` rests on buildable modules only.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeI1Fts

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary lemmas (see the provenance note above) -/

/-- **The sharp power-weighted Hardy inequality on `[ε,a]` with the anchor at `ε`.**

For `0 < ε < a`, `0 ≤ η < 1` and `g` of class `C¹` on `[ε,a]` with `g ε = 0`,

  `∫_ε^a g(t)² t^{-(2+η)} dt ≤ 4/(1+η)² ∫_ε^a g'(t)² t^{-η} dt`.

Proof: the completion of squares
`0 ≤ (g'(t) - (1+η)/2·g(t)/t)² t^{-η}` rewrites as
`(1+η)²/4·g²t^{-(2+η)} ≤ g'²t^{-η} - (1+η)/2·Ψ'(t)` with `Ψ(t) = g(t)²t^{-(1+η)}`; integrating over
`[ε,a]` and applying the fundamental theorem of calculus, whose left boundary term
`Ψ(ε) = 0` vanishes because `g ε = 0` and whose right boundary term
`-((1+η)/2)Ψ(a) ≤ 0` has the favourable sign, gives the claim.

The within-derivative `d = derivWithin g (Icc ε a)` is used so that every integrand is continuous
on the *closed* interval `[ε,a]` (the two-sided derivative `deriv g` need not be); on the interior
they agree. -/
theorem powerHardy_at {ε a η : ℝ} (hε : 0 < ε) (hεa : ε < a) (hη0 : 0 ≤ η) (hη1 : η < 1)
    {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g (Set.Icc ε a)) (h0 : g ε = 0) :
    (∫ t in ε..a, g t ^ 2 * t ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * ∫ t in ε..a, (deriv g t) ^ 2 * t ^ (-η) := by
  have hεle : ε ≤ a := le_of_lt hεa
  set d : ℝ → ℝ := derivWithin g (Set.Icc ε a) with hddef
  have hdu : UniqueDiffOn ℝ (Set.Icc ε a) := uniqueDiffOn_Icc hεa
  have hdc : ContinuousOn d (Set.Icc ε a) :=
    hg.continuousOn_derivWithin hdu le_rfl
  have hgc : ContinuousOn g (Set.Icc ε a) := hg.continuousOn
  -- `d` agrees with the two-sided derivative on the interior
  have hdeq : ∀ t ∈ Set.Ioo ε a, d t = deriv g t := by
    intro t ht
    exact derivWithin_of_mem_nhds (mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)
  -- the auxiliary function `Ψ` and its derivative `φ` (written with `d`)
  set Ψ : ℝ → ℝ := fun t => g t ^ 2 * t ^ (-(1 + η)) with hΨdef
  set φ : ℝ → ℝ := fun t =>
    2 * (g t * d t * t ^ (-(1 + η))) - (1 + η) * (g t ^ 2 * t ^ (-(2 + η))) with hφdef
  have hrpow1 : ContinuousOn (fun t : ℝ => t ^ (-(1 + η))) (Set.Icc ε a) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1)))
  have hrpow2 : ContinuousOn (fun t : ℝ => t ^ (-(2 + η))) (Set.Icc ε a) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1)))
  have hΨc : ContinuousOn Ψ (Set.Icc ε a) := by
    simp only [hΨdef]; exact (hgc.pow 2).mul hrpow1
  have hφc : ContinuousOn φ (Set.Icc ε a) := by
    simp only [hφdef]
    exact (((hgc.mul hdc).mul hrpow1).const_mul 2).sub ((hgc.pow 2 |>.mul hrpow2).const_mul (1 + η))
  have hIφ : IntervalIntegrable φ volume ε a := hφc.intervalIntegrable_of_Icc hεle
  -- the derivative identity on the interior
  have hderiv : ∀ x ∈ Set.Ioo ε a, HasDerivAt Ψ (φ x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans hε hx.1)
    have hmem : Set.Icc ε a ∈ 𝓝 x :=
      mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
    have hdx : deriv g x = d x := (hdeq x hx).symm
    have hd : HasDerivAt g (d x) x := by
      have h1 : HasDerivAt g (deriv g x) x :=
        (hg.differentiableOn_one.differentiableAt hmem).hasDerivAt
      rwa [← hdx]
    have h1 : HasDerivAt (fun s : ℝ => g s ^ 2) (2 * g x ^ 1 * d x) x := hd.pow 2
    have h2 : HasDerivAt (fun s : ℝ => s ^ (-(1 + η))) (-(1 + η) * x ^ (-(1 + η) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0)
    have h3 := h1.mul h2
    rw [show -(1 + η) - 1 = -(2 + η) by ring] at h3
    simp only [hΨdef, hφdef]
    refine h3.congr_deriv ?_
    ring
  -- the fundamental theorem of calculus
  have hFTC : (∫ t in ε..a, φ t) = Ψ a - Ψ ε :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hεle hΨc hderiv hIφ
  have hΨε : Ψ ε = 0 := by
    simp only [hΨdef, h0]; ring
  -- the pointwise completion of squares
  have hpt : ∀ t ∈ Set.Ioo ε a,
      (1 + η) ^ 2 / 4 * (g t ^ 2 * t ^ (-(2 + η)))
        ≤ (d t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * φ t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hε ht.1
    simp only [hφdef]
    have hid1 : t ^ 2 * t ^ (-(2 + η)) = t ^ (-η) := by
      rw [← Real.rpow_two t, ← Real.rpow_add ht0]; congr 1; ring
    have hid2 : t * t ^ (-(1 + η)) = t ^ (-η) := by
      have h := Real.rpow_add ht0 (1 : ℝ) (-(1 + η))
      rw [show (1 : ℝ) + (-(1 + η)) = -η by ring] at h
      rw [Real.rpow_one] at h
      exact h.symm
    have h2 : (g t / t) ^ 2 * t ^ 2 = g t ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 ht0.ne')]
    have hx1 : g t ^ 2 * t ^ (-(2 + η)) = (g t / t) ^ 2 * t ^ (-η) := by
      calc g t ^ 2 * t ^ (-(2 + η)) = ((g t / t) ^ 2 * t ^ 2) * t ^ (-(2 + η)) := by rw [h2]
        _ = (g t / t) ^ 2 * (t ^ 2 * t ^ (-(2 + η))) := by ring
        _ = (g t / t) ^ 2 * t ^ (-η) := by rw [hid1]
    have hx2 : g t * d t * t ^ (-(1 + η)) = (g t / t) * d t * t ^ (-η) := by
      have h3 : (g t / t) * t = g t := div_mul_cancel₀ (g t) ht0.ne'
      calc g t * d t * t ^ (-(1 + η))
          = ((g t / t) * t) * d t * t ^ (-(1 + η)) := by rw [h3]
        _ = (g t / t) * d t * (t * t ^ (-(1 + η))) := by ring
        _ = (g t / t) * d t * t ^ (-η) := by rw [hid2]
    rw [hx1, hx2]
    nlinarith [mul_nonneg (Real.rpow_nonneg ht0.le (-η))
      (sq_nonneg (d t - (1 + η) / 2 * (g t / t)))]
  -- integrability of the two integrands of the pointwise bound
  have hint1 : IntervalIntegrable (fun t : ℝ => g t ^ 2 * t ^ (-(2 + η))) volume ε a :=
    ((hgc.pow 2).mul hrpow2).intervalIntegrable_of_Icc hεle
  have hint3 : IntervalIntegrable (fun t : ℝ => d t ^ 2 * t ^ (-η)) volume ε a := by
    have hc : ContinuousOn (fun t : ℝ => d t ^ 2 * t ^ (-η)) (Set.Icc ε a) :=
      (hdc.pow 2).mul (continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1))))
    exact hc.intervalIntegrable_of_Icc hεle
  have hmono : ∫ t in ε..a, (1 + η) ^ 2 / 4 * (g t ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in ε..a, ((d t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * φ t) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hεle
      (hint1.const_mul _) (hint3.add (hIφ.const_mul _)) hpt
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [intervalIntegral.integral_add hint3 (hIφ.const_mul _),
    intervalIntegral.integral_const_mul] at hmono
  rw [hFTC, hΨε, sub_zero] at hmono
  have hle : (-(1 + η) / 2) * Ψ a ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_trans hε.le hεle) _))
  have hkey : (1 + η) ^ 2 / 4 * (∫ t in ε..a, g t ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in ε..a, (d t) ^ 2 * t ^ (-η) := by
    linarith [hmono, hle]
  -- replace `d` by `deriv g` on the interior
  have hdint : (∫ t in ε..a, (d t) ^ 2 * t ^ (-η))
      = ∫ t in ε..a, (deriv g t) ^ 2 * t ^ (-η) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_singleton a)
    intro x hx
    simp only [Set.mem_setOf_eq, not_imp] at hx
    obtain ⟨hxmem, hxne⟩ := hx
    by_contra hxa
    simp only [Set.mem_singleton_iff] at hxa
    rw [Set.uIoc_of_le hεle] at hxmem
    have hxlt : x < a := lt_of_le_of_ne hxmem.2 hxa
    exact hxne (by rw [hdeq x ⟨hxmem.1, hxlt⟩])
  rw [hdint] at hkey
  have hsq : (0 : ℝ) < (1 + η) ^ 2 := pow_pos (by linarith) 2
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq]
  nlinarith [hkey, hsq]

/-! ## The open-interval version -/

/-- The bridge between an `∫⁻`-integral over `Ioo b c` of `ofReal h` and the real interval
integral of `h`, for a nonnegative interval-integrable `h`. -/
private theorem lintegral_Ioo_ofReal_eq (b c : ℝ) (hbc : b ≤ c) {h : ℝ → ℝ}
    (hint : IntervalIntegrable h volume b c) (hnn : ∀ t ∈ Set.Ioc b c, 0 ≤ h t) :
    (∫⁻ t in Set.Ioo b c, ENNReal.ofReal (h t)) = ENNReal.ofReal (∫ t in b..c, h t) := by
  have h1 : Set.Ioc b c =ᵐ[volume] Set.Ioo b c :=
    (MeasureTheory.Ioc_ae_eq_Icc).trans (MeasureTheory.Ioo_ae_eq_Icc).symm
  rw [← setLIntegral_congr h1]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (show Integrable h (volume.restrict (Set.Ioc b c)) from hint.1)
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc |>.mpr
      (Filter.Eventually.of_forall fun t ht => hnn t ht))]
  rw [intervalIntegral.integral_of_le hbc]

/-- **The sharp power-weighted Hardy inequality on the open interval `(0,a)`.**

For `0 < a`, `0 ≤ η < 1` and `f` of class `C¹` on `(0,a)` whose trace at `0⁺` vanishes (and which
is a.e. strongly measurable for the measure restricted to `(0,a)`, as every slice of a function
continuous on that interval is),

  `∫_{(0,a)} f(t)² t^{-(2+η)} dt ≤ 4/(1+η)² ∫_{(0,a)} f'(t)² t^{-η} dt`

as an inequality of Lebesgue integrals in `ℝ≥0∞` (so no integrability hypothesis is needed
beyond the measurability of the slice).

Proof: for `e n = a/(n+2)` and `A n = a - a/(n+3)` the truncated functions `f - f (e n)` are `C¹`
on `[e n, A n]` with `(f - f (e n)) (e n) = 0`, so `powerHardy_at` gives the inequality on each
`[e n, A n]`; since `f (e n) → 0` and `(e n, A n) ↑ (0,a)`, Fatou's lemma gives the claim. -/
theorem powerHardy_open {a η : ℝ} (ha : 0 < a) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hfm : AEMeasurable f (volume.restrict (Set.Ioo 0 a)))
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 a))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    (∫⁻ t in Set.Ioo 0 a, ENNReal.ofReal (f t ^ 2 * t ^ (-(2 + η))))
      ≤ ENNReal.ofReal (4 / (1 + η) ^ 2)
        * (∫⁻ t in Set.Ioo 0 a, ENNReal.ofReal ((deriv f t) ^ 2 * t ^ (-η))) := by
  have hK : (0 : ℝ) ≤ 4 / (1 + η) ^ 2 := by positivity
  set T : Set ℝ := Set.Ioo (0 : ℝ) a with hTdef
  have hT : MeasurableSet T := hTdef ▸ measurableSet_Ioo
  set μ : Measure ℝ := volume.restrict T with hμ
  have hμs : ∀ {s : Set ℝ}, MeasurableSet s → s ⊆ T → μ.restrict s = volume.restrict s := by
    intro s hs hsub
    rw [hμ, Measure.restrict_restrict hs, Set.inter_eq_left.mpr hsub]
  set e : ℕ → ℝ := fun n => a / ((n : ℝ) + 2) with he
  set A : ℕ → ℝ := fun n => a - a / ((n : ℝ) + 3) with hAe
  -- scalar facts about the cut-off sequences
  have hepos : ∀ n : ℕ, 0 < e n := fun n => div_pos ha (by positivity)
  have he_sub : ∀ n : ℕ, Set.Ioo (e n) (A n) ⊆ T := fun n t ht =>
    ⟨lt_trans (hepos n) ht.1, lt_trans ht.2 (by
      have h : 0 < a / ((n : ℝ) + 3) := div_pos ha (by positivity)
      simp only [hAe]; linarith)⟩
  have hAa : ∀ n : ℕ, A n < a := by
    intro n
    have h : 0 < a / ((n : ℝ) + 3) := div_pos ha (by positivity)
    simp only [hAe]; linarith
  have heA : ∀ n : ℕ, e n < A n := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : a / ((n : ℝ) + 2) ≤ a / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h2 : a / ((n : ℝ) + 3) ≤ a / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    simp only [he, hAe]; linarith
  -- the truncated integrands
  set u : ℕ → ℝ → ℝ≥0∞ := fun n t => Set.indicator (Set.Ioo (e n) (A n))
      (fun s => ENNReal.ofReal ((f s - f (e n)) ^ 2 * s ^ (-(2 + η)))) t with hu
  have hu_apply : ∀ (n : ℕ) (t : ℝ), u n t = Set.indicator (Set.Ioo (e n) (A n))
      (fun s => ENNReal.ofReal ((f s - f (e n)) ^ 2 * s ^ (-(2 + η)))) t := by
    intro n t; rw [hu]
  -- a.e. measurability of the two power functions on `(0,a)`
  have hpow : AEMeasurable (fun t : ℝ => t ^ (-(2 + η))) μ := by
    rw [hμ]
    exact (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht.1))).aemeasurable
      measurableSet_Ioo
  have hpow' : AEMeasurable (fun t : ℝ => t ^ (-η)) μ := by
    rw [hμ]
    exact (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht.1))).aemeasurable
      measurableSet_Ioo
  have humeas : ∀ n : ℕ, AEMeasurable (u n) μ := by
    intro n
    have h1 : AEMeasurable (fun s : ℝ => f s - f (e n)) μ := hfm.sub aemeasurable_const
    have h2 : AEMeasurable (fun s : ℝ => (f s - f (e n)) ^ 2) μ := by
      refine (h1.mul h1).congr (Filter.Eventually.of_forall fun s => ?_)
      simp only [Pi.mul_apply, pow_two]
    have h3 : AEMeasurable (fun s : ℝ => (f s - f (e n)) ^ 2 * s ^ (-(2 + η))) μ := h2.mul hpow
    have hbase : AEMeasurable (fun s : ℝ =>
        ENNReal.ofReal ((f s - f (e n)) ^ 2 * s ^ (-(2 + η)))) μ :=
      ENNReal.continuous_ofReal.aemeasurable.comp_aemeasurable h3
    have hfun : u n = (Set.Ioo (e n) (A n)).indicator (fun s : ℝ =>
        ENNReal.ofReal ((f s - f (e n)) ^ 2 * s ^ (-(2 + η)))) := by
      funext t; rw [hu]
    rw [hfun]
    have hmono : AEMeasurable ((Set.Ioo (e n) (A n)).indicator (fun s : ℝ =>
        ENNReal.ofReal ((f s - f (e n)) ^ 2 * s ^ (-(2 + η))))) μ :=
      hbase.indicator measurableSet_Ioo
    exact hmono
  -- the target functional, written in the restricted measure
  have hD : (∫⁻ t in Set.Ioo 0 a, ENNReal.ofReal ((deriv f t) ^ 2 * t ^ (-η)))
      = ∫⁻ t, T.indicator (fun s => ENNReal.ofReal ((deriv f s) ^ 2 * s ^ (-η))) t ∂μ := by
    rw [show Set.Ioo (0 : ℝ) a = T from hTdef.symm]
    rw [MeasureTheory.lintegral_indicator hT, hμs (s := T) hT (le_refl T)]
  -- the bound for each truncated integrand
  have hub : ∀ n : ℕ, (∫⁻ t, u n t ∂μ)
      ≤ ENNReal.ofReal (4 / (1 + η) ^ 2)
        * (∫⁻ t, T.indicator (fun s => ENNReal.ofReal ((deriv f s) ^ 2 * s ^ (-η))) t ∂μ) := by
    intro n
    have hε : 0 < e n := hepos n
    have hεA : e n < A n := heA n
    have hAa' : A n < a := hAa n
    have hsub : Set.Icc (e n) (A n) ⊆ T := fun t ht =>
      ⟨lt_of_lt_of_le hε ht.1, lt_of_le_of_lt ht.2 hAa'⟩
    -- `powerHardy_at` on `[e n, A n]`
    have hg : ContDiffOn ℝ 1 (fun t : ℝ => f t - f (e n)) (Set.Icc (e n) (A n)) :=
      (hf.mono hsub).sub contDiffOn_const
    have hg0 : (fun t : ℝ => f t - f (e n)) (e n) = 0 := by simp
    have hP := powerHardy_at hε hεA hη0 hη1 hg hg0
    have hdereq : ∀ t ∈ Set.uIcc (e n) (A n),
        deriv (fun s : ℝ => f s - f (e n)) t = deriv f t := by
      intro t ht
      have htmem : t ∈ Set.Icc (e n) (A n) := by rwa [Set.uIcc_of_le hεA.le] at ht
      have hnb : T ∈ 𝓝 t := isOpen_Ioo.mem_nhds (hsub htmem)
      have h1 : HasDerivAt f (deriv f t) t :=
        ((hf.differentiableOn (by simp)).differentiableAt hnb).hasDerivAt
      exact (h1.sub_const (f (e n))).deriv
    have hP' : (∫ t in (e n)..(A n), (f t - f (e n)) ^ 2 * t ^ (-(2 + η)))
        ≤ 4 / (1 + η) ^ 2 * ∫ t in (e n)..(A n), (deriv f t) ^ 2 * t ^ (-η) := by
      refine hP.trans_eq ?_
      congr 1
      exact intervalIntegral.integral_congr fun t ht => by rw [hdereq t ht]
    -- integrability of the real integrands
    have hcont1 : ContinuousOn (fun t : ℝ => (f t - f (e n)) ^ 2 * t ^ (-(2 + η)))
        (Set.Icc (e n) (A n)) :=
      (((hf.continuousOn.mono hsub).sub continuousOn_const).pow 2).mul
        (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1))))
    have hcont2 : ContinuousOn (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η)) (Set.Icc (e n) (A n)) := by
      have hdc : ContinuousOn (deriv f) T :=
        hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
      exact ((hdc.mono hsub).pow 2).mul
        (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_of_lt_of_le hε ht.1))))
    have hint1 : IntervalIntegrable (fun t : ℝ => (f t - f (e n)) ^ 2 * t ^ (-(2 + η)))
        volume (e n) (A n) := hcont1.intervalIntegrable_of_Icc hεA.le
    have hint2 : IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η))
        volume (e n) (A n) := hcont2.intervalIntegrable_of_Icc hεA.le
    -- the left-hand side, as a real interval integral
    have hAi : (∫⁻ t, u n t ∂μ)
        = ENNReal.ofReal (∫ t in (e n)..(A n), (f t - f (e n)) ^ 2 * t ^ (-(2 + η))) := by
      rw [show (∫⁻ t, u n t ∂μ) = ∫⁻ t, (Set.Ioo (e n) (A n)).indicator
            (fun s => ENNReal.ofReal ((f s - f (e n)) ^ 2 * s ^ (-(2 + η)))) t ∂μ from by
        rw [hu]]
      rw [MeasureTheory.lintegral_indicator measurableSet_Ioo]
      rw [show (∫⁻ t in Set.Ioo (e n) (A n),
            ENNReal.ofReal ((f t - f (e n)) ^ 2 * t ^ (-(2 + η))) ∂μ)
          = ∫⁻ t in Set.Ioo (e n) (A n),
            ENNReal.ofReal ((f t - f (e n)) ^ 2 * t ^ (-(2 + η))) ∂volume from by
        rw [hμs measurableSet_Ioo (he_sub n)]]
      exact lintegral_Ioo_ofReal_eq (e n) (A n) hεA.le hint1
        (fun t ht => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (le_of_lt (lt_trans hε ht.1)) _))
    rw [hAi]
    -- the right-hand side is bounded below by the interval integral
    have hB1 : (∫⁻ t, T.indicator (fun s => ENNReal.ofReal ((deriv f s) ^ 2 * s ^ (-η)))
          t ∂μ)
        = ∫⁻ t in T, ENNReal.ofReal ((deriv f t) ^ 2 * t ^ (-η)) ∂volume := by
      rw [MeasureTheory.lintegral_indicator hT, hμs (s := T) hT (le_refl T)]
    have hB2 : ENNReal.ofReal (∫ t in (e n)..(A n), (deriv f t) ^ 2 * t ^ (-η))
        ≤ ∫⁻ t in T, ENNReal.ofReal ((deriv f t) ^ 2 * t ^ (-η)) ∂volume := by
      rw [← lintegral_Ioo_ofReal_eq (e n) (A n) hεA.le hint2
        (fun t ht => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (le_of_lt (lt_trans hε ht.1)) _))]
      exact MeasureTheory.lintegral_mono_set (he_sub n)
    rw [hB1]
    calc ENNReal.ofReal (∫ t in (e n)..(A n), (f t - f (e n)) ^ 2 * t ^ (-(2 + η)))
        ≤ ENNReal.ofReal (4 / (1 + η) ^ 2 * ∫ t in (e n)..(A n), (deriv f t) ^ 2 * t ^ (-η)) :=
          ENNReal.ofReal_le_ofReal hP'
      _ = ENNReal.ofReal (4 / (1 + η) ^ 2)
            * ENNReal.ofReal (∫ t in (e n)..(A n), (deriv f t) ^ 2 * t ^ (-η)) :=
          ENNReal.ofReal_mul hK
      _ ≤ ENNReal.ofReal (4 / (1 + η) ^ 2)
            * (∫⁻ t in T, ENNReal.ofReal ((deriv f t) ^ 2 * t ^ (-η)) ∂volume) := by
          have h := mul_le_mul_left hB2 (ENNReal.ofReal (4 / (1 + η) ^ 2))
          calc ENNReal.ofReal (4 / (1 + η) ^ 2)
                * ENNReal.ofReal (∫ t in (e n)..(A n), (deriv f t) ^ 2 * t ^ (-η))
              = ENNReal.ofReal (∫ t in (e n)..(A n), (deriv f t) ^ 2 * t ^ (-η))
                * ENNReal.ofReal (4 / (1 + η) ^ 2) := by rw [mul_comm]
            _ ≤ (∫⁻ t in T, ENNReal.ofReal ((deriv f t) ^ 2 * t ^ (-η)) ∂volume)
                * ENNReal.ofReal (4 / (1 + η) ^ 2) := h
            _ = ENNReal.ofReal (4 / (1 + η) ^ 2)
                * (∫⁻ t in T, ENNReal.ofReal ((deriv f t) ^ 2 * t ^ (-η)) ∂volume) := by
                rw [mul_comm]
  -- the pointwise limit of the truncated integrands
  have hlim : ∀ t, Filter.liminf (fun n : ℕ => u n t) Filter.atTop
      = T.indicator (fun s => ENNReal.ofReal (f s ^ 2 * s ^ (-(2 + η)))) t := by
    intro t
    by_cases ht : t ∈ T
    · have hlt : 0 < t := ht.1
      have hta : t < a := ht.2
      have he_tend : Filter.Tendsto e Filter.atTop (nhds 0) := by
        have h2 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop :=
          tendsto_atTop_add_const_right Filter.atTop (2 : ℝ)
            (tendsto_natCast_atTop_atTop (R := ℝ))
        simpa only [he] using h2.const_div_atTop a
      have hA_tend : Filter.Tendsto A Filter.atTop (nhds a) := by
        have h3 : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 3) Filter.atTop Filter.atTop :=
          tendsto_atTop_add_const_right Filter.atTop (3 : ℝ)
            (tendsto_natCast_atTop_atTop (R := ℝ))
        have h4 : Filter.Tendsto (fun n : ℕ => a / ((n : ℝ) + 3)) Filter.atTop (nhds 0) :=
          h3.const_div_atTop a
        have h5 : Filter.Tendsto (fun _ : ℕ => a) Filter.atTop (nhds a) := tendsto_const_nhds
        simpa only [hAe, sub_zero] using h5.sub h4
      have hev : ∀ᶠ n : ℕ in Filter.atTop, t ∈ Set.Ioo (e n) (A n) := by
        filter_upwards [he_tend.eventually (eventually_lt_nhds hlt),
          hA_tend.eventually (eventually_gt_nhds hta)] with n h1 h2
        exact ⟨h1, h2⟩
      have he_mem : ∀ᶠ n : ℕ in Filter.atTop, e n ∈ Set.Ioi (0 : ℝ) := by
        filter_upwards with n; exact hepos n
      have hfe : Filter.Tendsto (fun n : ℕ => f (e n)) Filter.atTop (nhds 0) :=
        h0.comp (tendsto_nhdsWithin_iff.mpr ⟨he_tend, he_mem⟩)
      have hkey : Filter.Tendsto (fun n : ℕ => u n t) Filter.atTop
          (nhds (ENNReal.ofReal (f t ^ 2 * t ^ (-(2 + η))))) := by
        have h4 : Filter.Tendsto (fun n : ℕ => f t - f (e n)) Filter.atTop (nhds (f t - 0)) :=
          tendsto_const_nhds.sub hfe
        have h5 : Filter.Tendsto
            (fun n : ℕ => (f t - f (e n)) ^ 2 * t ^ (-(2 + η))) Filter.atTop
            (nhds (f t ^ 2 * t ^ (-(2 + η)))) := by
          simpa using (h4.pow 2).mul tendsto_const_nhds
        have h6 := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h5
        have heq : (fun n : ℕ => u n t) =ᶠ[Filter.atTop]
            (fun n : ℕ => ENNReal.ofReal ((f t - f (e n)) ^ 2 * t ^ (-(2 + η)))) := by
          filter_upwards [hev] with n hn
          rw [hu_apply n t, Set.indicator_of_mem hn]
        exact h6.congr' heq.symm
      rw [hkey.liminf_eq, Set.indicator_of_mem ht]
    · have hev : ∀ᶠ n : ℕ in Filter.atTop, u n t = 0 := by
        by_cases hle : t ≤ 0
        · filter_upwards with n
          rw [hu_apply n t]
          exact Set.indicator_of_notMem
            (fun h => absurd h.1 (not_lt.mpr (le_trans hle (le_of_lt (hepos n))))) _
        · have hlt : 0 < t := not_le.mp hle
          have hta : a ≤ t := by
            by_contra h
            exact ht ⟨hlt, not_le.mp h⟩
          filter_upwards with n
          rw [hu_apply n t]
          exact Set.indicator_of_notMem
            (fun h => absurd h.2 (not_lt.mpr (le_trans (le_of_lt (hAa n)) hta))) _
      have h1 : Filter.Tendsto (fun n : ℕ => u n t) Filter.atTop (nhds (0 : ℝ≥0∞)) :=
        (tendsto_const_nhds (x := (0 : ℝ≥0∞))).congr' (hev.mono fun n h => h.symm)
      rw [h1.liminf_eq, Set.indicator_of_notMem ht]
  -- assemble
  calc (∫⁻ t in Set.Ioo 0 a, ENNReal.ofReal (f t ^ 2 * t ^ (-(2 + η))))
      = ∫⁻ t in T, ENNReal.ofReal (f t ^ 2 * t ^ (-(2 + η))) ∂volume :=
        (show (∫⁻ t in Set.Ioo 0 a, ENNReal.ofReal (f t ^ 2 * t ^ (-(2 + η))))
            = ∫⁻ t in T, ENNReal.ofReal (f t ^ 2 * t ^ (-(2 + η))) ∂volume from by
          rw [show Set.Ioo (0 : ℝ) a = T from hTdef.symm])
    _ = ∫⁻ t in T, ENNReal.ofReal (f t ^ 2 * t ^ (-(2 + η))) ∂μ := by
        rw [hμs (s := T) hT (le_refl T)]
    _ = ∫⁻ t, Filter.liminf (fun n : ℕ => u n t) Filter.atTop ∂μ := by
        rw [show (∫⁻ t in T, ENNReal.ofReal (f t ^ 2 * t ^ (-(2 + η))) ∂μ)
            = ∫⁻ t, T.indicator (fun s => ENNReal.ofReal (f s ^ 2 * s ^ (-(2 + η)))) t ∂μ from
          (MeasureTheory.lintegral_indicator hT _).symm]
        exact MeasureTheory.lintegral_congr (fun t => (hlim t).symm)
    _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ t, u n t ∂μ) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le' humeas
    _ ≤ ENNReal.ofReal (4 / (1 + η) ^ 2)
        * (∫⁻ t, T.indicator (fun s => ENNReal.ofReal ((deriv f s) ^ 2 * s ^ (-η)))
            t ∂μ) :=
        Filter.liminf_le_of_frequently_le
          (Filter.Eventually.frequently (Filter.Eventually.of_forall hub))
    _ = ENNReal.ofReal (4 / (1 + η) ^ 2)
        * (∫⁻ t in Set.Ioo 0 a, ENNReal.ofReal ((deriv f t) ^ 2 * t ^ (-η))) := by
        rw [hD]

/-- **Reflection of a Lebesgue integral about the point `a`**:
`∫_{(2a-c, 2a-b)} F (2a - θ) dθ = ∫_{(b,c)} F`. -/
private theorem lintegral_reflect_Ioo (a b c : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ θ in Set.Ioo (2 * a - c) (2 * a - b), F (2 * a - θ)) = ∫⁻ φ in Set.Ioo b c, F φ := by
  have hg : MeasurableEmbedding (fun θ : ℝ => 2 * a - θ) := by
    have h : (fun θ : ℝ => 2 * a - θ) = fun θ : ℝ => (2 * a) + (-θ) := rfl
    rw [h]
    exact MeasurableEmbedding.comp (MeasurableEquiv.addLeft (2 * a)).measurableEmbedding
      (MeasurableEquiv.neg ℝ).measurableEmbedding
  have hmap : MeasureTheory.Measure.map (fun θ : ℝ => 2 * a - θ) volume = volume :=
    MeasureTheory.Measure.map_sub_left_eq_self volume (2 * a)
  have hset : ∀ θ : ℝ, 2 * a - θ ∈ Set.Ioo b c ↔ θ ∈ Set.Ioo (2 * a - c) (2 * a - b) := by
    intro θ; simp only [Set.mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith
  calc (∫⁻ θ in Set.Ioo (2 * a - c) (2 * a - b), F (2 * a - θ))
      = ∫⁻ θ, (Set.Ioo (2 * a - c) (2 * a - b)).indicator (fun θ => F (2 * a - θ)) θ :=
        (MeasureTheory.lintegral_indicator measurableSet_Ioo _).symm
    _ = ∫⁻ θ, ((Set.Ioo b c).indicator F) (2 * a - θ) := by
        refine MeasureTheory.lintegral_congr fun θ => ?_
        by_cases h : θ ∈ Set.Ioo (2 * a - c) (2 * a - b)
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hset θ).mpr h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
          exact fun hc => h ((hset θ).mp hc)
    _ = ∫⁻ ψ, ((Set.Ioo b c).indicator F) ψ
          ∂(MeasureTheory.Measure.map (fun θ : ℝ => 2 * a - θ) volume) :=
        (MeasurableEmbedding.lintegral_map hg _).symm
    _ = ∫⁻ ψ, ((Set.Ioo b c).indicator F) ψ ∂volume := by rw [hmap]
    _ = ∫⁻ φ in Set.Ioo b c, F φ := MeasureTheory.lintegral_indicator measurableSet_Ioo _

/-- **Splitting a `∫⁻`-integral on `(0,π/2)` at the midpoint `π/4`.** -/
private theorem lintegral_split_pi (G : ℝ → ℝ≥0∞) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2), G θ)
      = (∫⁻ θ in Set.Ioo 0 (Real.pi / 4), G θ)
        + ∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ := by
  have h1 : Set.Ioo (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioc (0 : ℝ) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc).trans (MeasureTheory.Ioc_ae_eq_Icc).symm
  have h2 : Set.Ioo (0 : ℝ) (Real.pi / 4) =ᵐ[volume] Set.Ioc (0 : ℝ) (Real.pi / 4) :=
    (MeasureTheory.Ioo_ae_eq_Icc).trans (MeasureTheory.Ioc_ae_eq_Icc).symm
  have h3 : Set.Ioo (Real.pi / 4) (Real.pi / 2) =ᵐ[volume]
      Set.Ioc (Real.pi / 4) (Real.pi / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc).trans (MeasureTheory.Ioc_ae_eq_Icc).symm
  rw [setLIntegral_congr h1, setLIntegral_congr h2, setLIntegral_congr h3]
  have hunion : Set.Ioc (0 : ℝ) (Real.pi / 2)
      = Set.Ioc 0 (Real.pi / 4) ∪ Set.Ioc (Real.pi / 4) (Real.pi / 2) := by
    ext x; simp only [Set.mem_Ioc, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : x ≤ Real.pi / 4
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨not_le.mp h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 (by linarith [Real.pi_pos])⟩
      · exact ⟨by linarith [Real.pi_pos], h2⟩
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) (Real.pi / 4)) (Set.Ioc (Real.pi / 4) (Real.pi / 2)) :=
    Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)
  rw [hunion, MeasureTheory.lintegral_union measurableSet_Ioc hdisj]

/-! ## The `sin(2θ)`-weighted Hardy inequality on `(0,π/2)` -/

/-- On `(0,π/4)`: `(4/π)φ ≤ sin(2φ)`, `sin(2φ) ≤ 2φ`, and `0 < sin(2φ)`. -/
theorem sinTwoBounds {φ : ℝ} (h0 : 0 < φ) (hq : φ < Real.pi / 4) :
    (4 / Real.pi) * φ ≤ Real.sin (2 * φ) ∧ Real.sin (2 * φ) ≤ 2 * φ ∧ 0 < Real.sin (2 * φ) := by
  have h2φ0 : 0 ≤ 2 * φ := by linarith
  have h2φπ : 2 * φ ≤ Real.pi := by linarith [hq, Real.pi_pos]
  have hpos : 0 < Real.sin (2 * φ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hle : (4 / Real.pi) * φ ≤ Real.sin (2 * φ) := by
    have h := Real.mul_le_sin h2φ0 (by linarith)
    have he : 2 / Real.pi * (2 * φ) = (4 / Real.pi) * φ := by ring
    rwa [he] at h
  exact ⟨hle, Real.sin_le h2φ0, hpos⟩

theorem powerHardySinOpen {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {v : ℝ → ℝ}
    (hvm : AEMeasurable v (volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hv : ContDiffOn ℝ 1 v (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto v (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hπ : Filter.Tendsto v (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
        ENNReal.ofReal (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η))))
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
        * (∫⁻ θ in Set.Ioo 0 (Real.pi / 2),
            ENNReal.ofReal ((deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))) := by
  have hq0 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hqP : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  let F : ℝ → ℝ≥0∞ := fun θ =>
    ENNReal.ofReal (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + η)))
  let G : ℝ → ℝ≥0∞ := fun θ => ENNReal.ofReal ((deriv v θ) ^ 2 * (Real.sin (2 * θ)) ^ (-η))
  have halfBound : ∀ {u : ℝ → ℝ},
      AEMeasurable u (volume.restrict (Set.Ioo 0 (Real.pi / 4))) →
      ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 4)) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
          ENNReal.ofReal (u φ ^ 2 * (Real.cos (2 * φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + η))))
        ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
          * (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              ENNReal.ofReal ((deriv u φ) ^ 2 * (Real.sin (2 * φ)) ^ (-η))) := by
    intro u hum hu hu0
    -- (1) the left-hand comparison
    have key1 : (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
          ENNReal.ofReal (u φ ^ 2 * (Real.cos (2 * φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + η))))
        ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η))
          * (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              ENNReal.ofReal (u φ ^ 2 * φ ^ (-(2 + η)))) := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine MeasureTheory.lintegral_mono_ae ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
        (Filter.Eventually.of_forall fun φ hφ => ?_)
      obtain ⟨hsinle, hsinle2, hsinpos⟩ := sinTwoBounds hφ.1 hφ.2
      have hfac : (Real.sin (2 * φ)) ^ (-(2 + η)) ≤ (Real.pi / 4) ^ (2 + η) * φ ^ (-(2 + η)) := by
        have h1 : (Real.sin (2 * φ)) ^ (-(2 + η)) ≤ ((4 / Real.pi) * φ) ^ (-(2 + η)) := by
          refine Real.rpow_le_rpow_of_nonpos (mul_pos (by positivity) hφ.1) hsinle (by linarith)
        have h2 : ((4 / Real.pi) * φ) ^ (-(2 + η))
            = (Real.pi / 4) ^ (2 + η) * φ ^ (-(2 + η)) := by
          rw [Real.mul_rpow (by positivity) hφ.1.le]
          have h4 : (4 / Real.pi) ^ (-(2 + η)) = (Real.pi / 4) ^ (2 + η) := by
            rw [show (4 / Real.pi : ℝ) = (Real.pi / 4)⁻¹ by ring,
              Real.inv_rpow (le_of_lt hq0), ← Real.rpow_neg (le_of_lt hq0)]
            ring_nf
          rw [h4]
        rw [h2] at h1
        exact h1
      have hcos : (Real.cos (2 * φ)) ^ 2 ≤ 1 := Real.cos_sq_le_one (2 * φ)
      have hmain : (Real.cos (2 * φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + η))
          ≤ (Real.pi / 4) ^ (2 + η) * φ ^ (-(2 + η)) := by
        calc (Real.cos (2 * φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + η))
            ≤ 1 * (Real.sin (2 * φ)) ^ (-(2 + η)) :=
              mul_le_mul_of_nonneg_right hcos (Real.rpow_nonneg hsinpos.le _)
          _ = (Real.sin (2 * φ)) ^ (-(2 + η)) := one_mul _
          _ ≤ (Real.pi / 4) ^ (2 + η) * φ ^ (-(2 + η)) := hfac
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hq0.le _)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc u φ ^ 2 * (Real.cos (2 * φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + η))
          = u φ ^ 2 * ((Real.cos (2 * φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + η))) := by ring
        _ ≤ u φ ^ 2 * ((Real.pi / 4) ^ (2 + η) * φ ^ (-(2 + η))) :=
            mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
        _ = (Real.pi / 4) ^ (2 + η) * (u φ ^ 2 * φ ^ (-(2 + η))) := by ring
    -- (2) the radial Hardy inequality
    have key2 := powerHardy_open hq0 hη0 hη1 hum hu hu0
    -- (3) the right-hand comparison
    have key3 : (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
          ENNReal.ofReal ((deriv u φ) ^ 2 * φ ^ (-η)))
        ≤ ENNReal.ofReal (2 ^ η)
          * (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              ENNReal.ofReal ((deriv u φ) ^ 2 * (Real.sin (2 * φ)) ^ (-η))) := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine MeasureTheory.lintegral_mono_ae ?_
      refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
        (Filter.Eventually.of_forall fun φ hφ => ?_)
      obtain ⟨hsinle, hsinle2, hsinpos⟩ := sinTwoBounds hφ.1 hφ.2
      have hcmp : φ ^ (-η) ≤ 2 ^ η * (Real.sin (2 * φ)) ^ (-η) := by
        have h1 : (2 * φ) ^ (-η) ≤ (Real.sin (2 * φ)) ^ (-η) :=
          Real.rpow_le_rpow_of_nonpos hsinpos hsinle2 (by linarith)
        have h2 : (2 * φ) ^ (-η) = 2 ^ (-η) * φ ^ (-η) :=
          Real.mul_rpow (by norm_num) hφ.1.le
        have h4 : 2 ^ η * (2 * φ) ^ (-η) = φ ^ (-η) := by
          rw [h2, ← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          rw [show η + -η = 0 by ring, Real.rpow_zero, one_mul]
        calc φ ^ (-η) = 2 ^ η * (2 * φ) ^ (-η) := h4.symm
          _ ≤ 2 ^ η * (Real.sin (2 * φ)) ^ (-η) :=
              mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by norm_num) η)
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) η)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (deriv u φ) ^ 2 * φ ^ (-η) ≤ (deriv u φ) ^ 2 * (2 ^ η * (Real.sin (2 * φ)) ^ (-η)) :=
            mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
        _ = 2 ^ η * ((deriv u φ) ^ 2 * (Real.sin (2 * φ)) ^ (-η)) := by ring
    -- assembly
    calc (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
          ENNReal.ofReal (u φ ^ 2 * (Real.cos (2 * φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + η))))
        ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η))
            * (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
                ENNReal.ofReal (u φ ^ 2 * φ ^ (-(2 + η)))) := key1
      _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η))
            * (ENNReal.ofReal (4 / (1 + η) ^ 2)
                * (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
                    ENNReal.ofReal ((deriv u φ) ^ 2 * φ ^ (-η)))) :=
          mul_le_mul_right key2 (ENNReal.ofReal ((Real.pi / 4) ^ (2 + η)))
      _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η))
            * (ENNReal.ofReal (4 / (1 + η) ^ 2)
                * (ENNReal.ofReal (2 ^ η)
                    * (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
                        ENNReal.ofReal ((deriv u φ) ^ 2 * (Real.sin (2 * φ)) ^ (-η))))) := by
          refine mul_le_mul_right ?_ _
          exact mul_le_mul_right key3 _
      _ = ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
            * (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
                ENNReal.ofReal ((deriv u φ) ^ 2 * (Real.sin (2 * φ)) ^ (-η))) := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 + η) * 2 ^ η),
            ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Real.pi / 4) ^ (2 + η))]
          ring
  -- ## the left half
  have hleft : (∫⁻ θ in Set.Ioo 0 (Real.pi / 4), F θ)
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
        * (∫⁻ θ in Set.Ioo 0 (Real.pi / 4), G θ) :=
    halfBound (hvm.mono_measure (MeasureTheory.Measure.restrict_mono
        (s := Set.Ioo 0 (Real.pi / 4)) (s' := Set.Ioo 0 (Real.pi / 2))
        (fun x hx => ⟨hx.1, lt_trans hx.2 hqP⟩) le_rfl))
      (hv.mono (fun x hx => ⟨hx.1, lt_trans hx.2 hqP⟩)) h0
  -- ## the right half, through the reflection `φ ↦ π/2 - φ`
  have hright : (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ)
      ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
        * (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ) := by
    set w : ℝ → ℝ := fun φ => v (Real.pi / 2 - φ) with hwdef
    have hwm : AEMeasurable w (volume.restrict (Set.Ioo 0 (Real.pi / 4))) := by
      rw [hwdef]
      refine (hv.continuousOn.comp (by fun_prop) ?_).aemeasurable measurableSet_Ioo
      intro φ hφ
      exact ⟨by linarith [hφ.2, Real.pi_pos], by linarith [hφ.1]⟩
    have hw : ContDiffOn ℝ 1 w (Set.Ioo 0 (Real.pi / 4)) := by
      rw [hwdef]
      refine hv.comp (by fun_prop) ?_
      intro φ hφ
      exact ⟨by linarith [hφ.2, Real.pi_pos], by linarith [hφ.1]⟩
    have hw0 : Filter.Tendsto w (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      rw [hwdef]
      refine hπ.comp ?_
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h1 : Filter.Tendsto (fun φ : ℝ => Real.pi / 2 - φ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds (Real.pi / 2)) := by
          have h2 := (tendsto_const_nhds (x := Real.pi / 2)
            (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))).sub
            (tendsto_id.mono_right (nhdsWithin_le_nhds))
          simpa using h2
        exact h1
      · filter_upwards [self_mem_nhdsWithin] with φ hφ
        exact sub_lt_self _ (Set.mem_Ioi.mp hφ)
    have hderivw : ∀ φ ∈ Set.Ioo 0 (Real.pi / 4), deriv w φ = -deriv v (Real.pi / 2 - φ) := by
      intro φ _
      rw [hwdef]
      exact deriv_comp_const_sub v (Real.pi / 2) φ
    have hwbound := halfBound (u := w) hwm hw hw0
    -- ## the two transfers
    have hreflF : (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
          ENNReal.ofReal (w φ ^ 2 * (Real.cos (2 * φ)) ^ 2 * (Real.sin (2 * φ)) ^ (-(2 + η))))
        = ∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ := by
      have hg := lintegral_reflect_Ioo (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)
        (fun x : ℝ => ENNReal.ofReal (v x ^ 2 * (Real.cos (2 * x)) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + η))))
      rw [show 2 * (Real.pi / 4) - Real.pi / 2 = (0 : ℝ) by ring,
          show 2 * (Real.pi / 4) - Real.pi / 4 = (Real.pi / 4 : ℝ) by ring] at hg
      calc (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              ENNReal.ofReal (w φ ^ 2 * (Real.cos (2 * φ)) ^ 2
                * (Real.sin (2 * φ)) ^ (-(2 + η))))
          = ∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              (fun x : ℝ => ENNReal.ofReal (v x ^ 2 * (Real.cos (2 * x)) ^ 2
                * (Real.sin (2 * x)) ^ (-(2 + η)))) (Real.pi / 2 - φ) := by
            refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
            rw [hwdef]
            refine congrArg ENNReal.ofReal ?_
            rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.cos_pi_sub,
              Real.sin_pi_sub]
            ring
        _ = ∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              (fun x : ℝ => ENNReal.ofReal (v x ^ 2 * (Real.cos (2 * x)) ^ 2
                * (Real.sin (2 * x)) ^ (-(2 + η)))) (2 * (Real.pi / 4) - φ) := by
            refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
            congr 1
            ring
        _ = ∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
              (fun x : ℝ => ENNReal.ofReal (v x ^ 2 * (Real.cos (2 * x)) ^ 2
                * (Real.sin (2 * x)) ^ (-(2 + η)))) θ := hg
        _ = ∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ := rfl
    have hreflG : (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
          ENNReal.ofReal ((deriv w φ) ^ 2 * (Real.sin (2 * φ)) ^ (-η)))
        = ∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ := by
      have hg := lintegral_reflect_Ioo (Real.pi / 4) (Real.pi / 4) (Real.pi / 2)
        (fun x : ℝ => ENNReal.ofReal ((deriv v x) ^ 2 * (Real.sin (2 * x)) ^ (-η)))
      rw [show 2 * (Real.pi / 4) - Real.pi / 2 = (0 : ℝ) by ring,
          show 2 * (Real.pi / 4) - Real.pi / 4 = (Real.pi / 4 : ℝ) by ring] at hg
      calc (∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              ENNReal.ofReal ((deriv w φ) ^ 2 * (Real.sin (2 * φ)) ^ (-η)))
          = ∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              (fun x : ℝ => ENNReal.ofReal ((deriv v x) ^ 2 * (Real.sin (2 * x)) ^ (-η)))
                (Real.pi / 2 - φ) := by
            refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun φ hφ => ?_)
            rw [hderivw φ hφ]
            refine congrArg ENNReal.ofReal ?_
            rw [show 2 * (Real.pi / 2 - φ) = Real.pi - 2 * φ by ring, Real.sin_pi_sub]
            ring
        _ = ∫⁻ φ in Set.Ioo 0 (Real.pi / 4),
              (fun x : ℝ => ENNReal.ofReal ((deriv v x) ^ 2 * (Real.sin (2 * x)) ^ (-η)))
                (2 * (Real.pi / 4) - φ) := by
            refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo (fun φ _ => ?_)
            congr 1
            ring
        _ = ∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2),
              (fun x : ℝ => ENNReal.ofReal ((deriv v x) ^ 2 * (Real.sin (2 * x)) ^ (-η))) θ :=
            hg
        _ = ∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ := rfl
    rw [hreflF, hreflG] at hwbound
    exact hwbound
  -- ## split at `π/4` and assemble
  calc (∫⁻ θ in Set.Ioo 0 (Real.pi / 2), F θ)
      = (∫⁻ θ in Set.Ioo 0 (Real.pi / 4), F θ)
        + (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), F θ) := lintegral_split_pi F
    _ ≤ ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
          * (∫⁻ θ in Set.Ioo 0 (Real.pi / 4), G θ)
        + ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
          * (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ) := add_le_add hleft hright
    _ = ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
          * ((∫⁻ θ in Set.Ioo 0 (Real.pi / 4), G θ)
            + (∫⁻ θ in Set.Ioo (Real.pi / 4) (Real.pi / 2), G θ)) := by ring
    _ = ENNReal.ofReal ((Real.pi / 4) ^ (2 + η) * 2 ^ η * (4 / (1 + η) ^ 2))
          * (∫⁻ θ in Set.Ioo 0 (Real.pi / 2), G θ) := by rw [lintegral_split_pi G]

end Work.FTS.EllipticEst.AeI1Fts
