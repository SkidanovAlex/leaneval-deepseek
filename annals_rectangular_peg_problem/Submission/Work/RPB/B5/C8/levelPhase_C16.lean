import Mathlib
import Submission.Work.RPB.B5.chordSurf_rhoChart_full

open scoped ContDiff

set_option autoImplicit false

namespace Work.RPB.B5.C8

/-- **`levelPhase_C16`.**  The chord phase `a : (τ,t,r) ↦ a τ t r`, which is only a phase of the
chord direction for `r ≥ 0`, is *even to infinite order* in `r` at `r = 0` (the half chord has a
smooth even representative and the phase differences vanish to all orders on the two sides); hence
the function `ρ ↦ a τ t (√ρ)` of `ρ = r²` extends to a `C¹⁶` function `Θ` of `(τ,t,ρ)` on the whole
strip `Icc 0 1 ×ˢ univ ×ˢ univ`, still agreeing with `a τ t (√ρ)` for small `ρ > 0`.

The proof is the order-`16` instance of the (order-generic) strip phase lift: the smooth even
half chord gives the regularised phase integrand `regF`, whose odd `r`-primitive `L` satisfies
`L τ t r = a τ t r - a τ t 0` for `0 < r < 3π/4`; `evenChart` turns `L` into a `C¹⁶` function of
`ρ`, and adding `a τ t 0` closes the identity.  This is the order-`16` companion of
`Work.RPB.B5.phaseLiftStrip` (order `8`) and `Work.RPB.B5.C12.phaseLiftStrip_12_smooth`
(order `12`). -/
theorem levelPhase_C16 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ∃ s : ℝ, 0 < s ∧ ∃ Θ : ℝ → ℝ → ℝ → ℝ,
      ContDiffOn ℝ 16 (fun z : ℝ × (ℝ × ℝ) => Θ z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ ρ ∈ Set.Ioo (0 : ℝ) s,
        Θ τ t ρ = a τ t (Real.sqrt ρ)) := by
  -- the smooth, even, `2π`-periodic representative of the half chord
  obtain ⟨hc, hc_sm, hc_even, hc_per, hc_zero, hc_half⟩ :=
    Work.RPB.B5.halfChordSmooth CI.c CI.smooth CI.per
  have hne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, |r| < Real.pi → hc τ t r ≠ 0 :=
    Work.RPB.B5.hc_ne_zero hc_zero hc_half CI.inj CI.imm
  set ρa : ℝ := 3 * Real.pi / 4 with hρadef
  have hρapi : ρa < Real.pi := by rw [hρadef]; linarith [Real.pi_pos]
  -- the regularised integrand
  have hreg_sm : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => regF hc ρa z.1 z.2.1 z.2.2) :=
    regF_contDiff hc ρa hc_sm (fun τ t s =>
      regDen_ne_zero hc Real.pi hne ρa (7 * Real.pi / 8)
        (by rw [hρadef]; linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) τ t s)
  have hreg_odd : ∀ τ t s, regF hc ρa τ t (-s) = -regF hc ρa τ t s :=
    fun τ t s => regF_neg hc hc_sm hc_even ρa τ t s
  have hreg_per : ∀ τ t s, regF hc ρa τ (t + 2 * Real.pi) s = regF hc ρa τ t s :=
    regF_per hc hc_sm hc_per ρa
  -- the primitive of the phase derivative, in `ρ`-free form
  let L : ℝ → ℝ → ℝ → ℝ := fun τ t r => r * ∫ u in (0 : ℝ)..1, regF hc ρa τ t (r * u)
  have hL_sm : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => L z.1 z.2.1 z.2.2) := by
    have hint : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) =>
        ∫ u in (0 : ℝ)..1, regF hc ρa z.1 z.2.1 (z.2.2 * u)) := by
      have h1 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ =>
          regF hc ρa q.1.1 q.1.2.1 (q.1.2.2 * q.2)) := by
        have hf1 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1.1) :=
          (contDiff_fst : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1)).fst
        have hf2 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1.2.1) :=
          ((contDiff_fst : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1)).snd).fst
        have hf3 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1.2.2) :=
          ((contDiff_fst : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.1)).snd).snd
        have hs2 : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.2) :=
          (contDiff_snd : ContDiff ℝ ∞ (fun q : (ℝ × (ℝ × ℝ)) × ℝ => q.2))
        exact hreg_sm.comp (hf1.prodMk (hf2.prodMk (hf3.mul hs2)))
      exact Work.RPA3.contDiff_param_intervalIntegral ⊤
        (fun q : ℝ × (ℝ × ℝ) => fun u : ℝ => regF hc ρa q.1 q.2.1 (q.2.2 * u)) h1 0 1
    dsimp only [L]
    exact ((contDiff_snd : ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ) => z.2)).snd).mul hint
  have hL_even : ∀ τ t r, L τ t (-r) = L τ t r := by
    intro τ t r
    dsimp only [L]
    rcases eq_or_ne r 0 with hr | hr
    · rw [hr, neg_zero]
    · have hfun : (fun u : ℝ => regF hc ρa τ t ((-r) * u))
          = (fun u : ℝ => -regF hc ρa τ t (r * u)) := by
        funext u
        rw [show (-r) * u = -(r * u) by ring, hreg_odd]
      rw [hfun, intervalIntegral.integral_neg]
      ring
  have hL_per : ∀ τ t r, L τ (t + 2 * Real.pi) r = L τ t r := by
    intro τ t r
    dsimp only [L]
    rw [show (fun u : ℝ => regF hc ρa τ (t + 2 * Real.pi) (r * u))
        = (fun u : ℝ => regF hc ρa τ t (r * u)) from by
      funext u; exact hreg_per τ t (r * u)]
  -- the identity `L = a - a(·,0)` on the strip
  have hL_eq : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ r, 0 < r → r < ρa →
      L τ t r = a τ t r - a τ t 0 := by
    intro τ hτ t r hr0 hrρ
    have hrpi : r < Real.pi := lt_trans hrρ hρapi
    -- the substitution `r ∫_0^1 f (r u) du = ∫_0^r f`
    have hsub : r * ∫ u in (0 : ℝ)..1, regF hc ρa τ t (r * u)
        = ∫ s in (0 : ℝ)..r, regF hc ρa τ t s := by
      rw [intervalIntegral.integral_comp_mul_left (fun s : ℝ => regF hc ρa τ t s)
        (ne_of_gt hr0), mul_zero, mul_one]
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr0), one_mul]
    -- the fundamental theorem of calculus for the phase
    have hslice : ContDiffOn ℝ 1 (fun s : ℝ => a τ t s) (Set.Icc (0 : ℝ) r) := by
      have hg : ContDiffOn ℝ 1 (fun s : ℝ => (τ, (t, s))) (Set.Icc (0 : ℝ) r) := by
        apply ContDiff.contDiffOn; fun_prop
      have hmaps : Set.MapsTo (fun s : ℝ => (τ, (t, s))) (Set.Icc (0 : ℝ) r)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) :=
        fun s hs => ⟨hτ, trivial, ⟨hs.1, le_of_lt (lt_of_le_of_lt hs.2 hrpi)⟩⟩
      exact (ha.1.of_le (by simp)).comp hg hmaps
    have haeq : ∫ s in (0 : ℝ)..r, deriv (fun s : ℝ => a τ t s) s
        = ∫ s in (0 : ℝ)..r, regF hc ρa τ t s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with s hs hsI
      rw [Set.uIoc_of_le (le_of_lt hr0)] at hsI
      have hs0 : 0 < s := hsI.1
      have hsr : s ≤ r := hsI.2
      have hspi : s < Real.pi := lt_of_le_of_lt hsr hrpi
      rw [phaseDeriv_eq CI.c a ha hc hc_sm hc_half hτ ⟨hs0, hspi⟩
        (hne τ hτ t s (by rw [abs_of_pos hs0]; exact hspi)), regF_eq hc hc_sm ρa hτ]
      rw [abs_of_pos hs0]
      exact lt_of_le_of_lt hsr hrρ
    have hftc := intervalIntegral.integral_deriv_of_contDiffOn_Icc hslice (le_of_lt hr0)
    dsimp only [L]
    rw [hsub, ← haeq, hftc]
  -- the even `ρ`-chart of `L`
  obtain ⟨Ĝ, hĜ_sm, hĜ_val, _hĜ_per⟩ := evenChart L 16 hL_sm hL_even hL_per
  -- the `ρ`-chart of the "constant" part `a τ t 0`
  have ha0 : ContDiffOn ℝ 16 (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 0)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := by
    have hg : ContDiffOn ℝ 16 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, (0 : ℝ))))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) := by
      apply ContDiff.contDiffOn; fun_prop
    have hmaps : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.1, (0 : ℝ))))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Icc (0 : ℝ) Real.pi) :=
      fun z hz => ⟨hz.1, trivial, ⟨le_rfl, Real.pi_pos.le⟩⟩
    exact (ha.1.of_le (by simp)).comp hg hmaps
  refine ⟨Real.pi ^ 2 / 4, by positivity, fun τ t ρ => Ĝ τ t ρ + a τ t 0, ?_, ?_⟩
  · -- smoothness on the strip
    have hĜ : ContDiffOn ℝ 16 (fun z : ℝ × (ℝ × ℝ) => Ĝ z.1 z.2.1 z.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
      hĜ_sm.contDiffOn.mono (Set.subset_univ _)
    exact hĜ.add ha0
  · -- the value
    intro τ hτ t ρ hρ
    have hsqrt_lt : Real.sqrt ρ < Real.pi / 2 := by
      rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.pi / 2)]
      rw [show (Real.pi / 2) ^ 2 = Real.pi ^ 2 / 4 by ring]
      exact hρ.2
    have hrlt : Real.sqrt ρ < ρa := by
      rw [hρadef]; linarith [hsqrt_lt, Real.pi_pos]
    show Ĝ τ t ρ + a τ t 0 = a τ t (Real.sqrt ρ)
    rw [hĜ_val τ t ρ hρ.1.le,
      hL_eq τ hτ t (Real.sqrt ρ) (Real.sqrt_pos.mpr hρ.1) hrlt]
    ring

end Work.RPB.B5.C8
