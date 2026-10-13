/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T2SupF`: the pointwise sup bounds of order `≤ 2` for the coefficient `f`

The frozen statement (design `Submission/Work/FTS/ELL_H2_LEAD.md` §B2, the `T2S` input):

```
theorem t2SupF : ∃ C > 0, ∀ α f, 0 < α → α ≤ 1 → SmoothOpen f → HkMem α 4 f → CoefThMem 1 f →
  ∀ b a, a + b ≤ 2 → ∀ z θ, 0 < z → 0 < θ → θ < π/2 →
    |mixed b a f z θ| ≤ C * (Xn α f + CoefTh 1 f)
```

The constant `C` is **uniform in `α ∈ (0,1]`** — this is forced by the way `T2S` consumes it
(its right-hand side carries only one factor `1/√(γ-1)`).

## State of this file

* **`a ≥ 1` (all `b`): DONE** — `t2SupF_aPos`, proved `sorry`-free with the `α`-uniform
  constant of `flat_mixed_le 1` (the σ-gain).  The sup datum is `K = CoefTh 1 f`, extracted
  from `CoefThMem 1 f` through `supAbsO_le_coefTh`.

* **`a = 0`, `b ≤ 1`: DONE** — `t2SupF_b_le_one`, proved `sorry`-free, `α`-uniform.  Route:
  * the *angular average* bound `∫_θ (D_z^b f(z,θ))² dθ ≤ 3 · HkSq α 4 f` for **every** `z > 0`
    and `b ≤ 2` (`Work.FTS.TransportS.SupDzAux.sup_dz_avg_le`, proved) is the replacement for
    the missing decay hypothesis of the radial Hardy inequality;
  * a value `θ₀` of the middle half `[π/8, 3π/8]` at which the slice is at most `4/π` times its
    mean (`mid_min_le_avg`, below);
  * the `θ`-Lipschitz estimate `|D_z^b f(z,θ) - D_z^b f(z,θ₀)| ≤ CoefTh 1 f · |θ - θ₀|`, from
    Clairaut (`Work.Blocks.pth_DzIter_eqOn_Q0`) and `CoefThMem 1 f`
    (`t2SupF_pth_le_coefTh`), through the mean value theorem.
  No `(γ-1)^{-1}` occurs anywhere in this case.

* **`a = 0`, `b = 2`, `α ≥ 1/10`: DONE** — `t2SupF_b2_large`, proved `sorry`-free.  No new
  mathematics is needed: the proved pointwise bounds
  `Work.FTS.TransportS.sup_dz_le_hk` give `|D_z^2 f| ≤ C/√(γ-1) · Xn α f`, and for `α ≥ 1/10`
  the factor is `1/√(α/10) ≤ 10`.

* **`a = 0`, `b = 2`, `α < 1/10`: OPEN** — isolated as `t2SupF_b2_small`; this is the only
  remaining gap of the file.  The natural route is a one-dimensional weighted sup inequality
  for the slice `v = D_z^2 f(z,·)`, with the two inputs `∫_θ v² sin(2θ)^{-η} ≤ C HkSq`
  (weighted angular average, proved) and
  `∫_θ (v')² sin(2θ)^{2-γ} ≤ C HkSq` (`SupDzAux.sup_dz_ang_le`, proved), but that inequality is
  **FALSE** without a control of the angular oscillation of `v'`: a function equal to `1` on
  `[0, e^{-1/(γ-1)}]` decaying like `1 - log θ/L` afterwards has both integrals `→ 0` while
  `sup v² = 1` (found by the prover of `FTS/TransportS/SliceSupWeighted/sliceSup_eta_gam`,
  hence declared false).  In the product case `f = M(z)ψ(θ)` this profile has
  `∂_θ f = M ψ'` with `sup|ψ'| ≍ e^L/L` (`L = 1/(γ-1)`) *huge*, so `CoefTh 1 f` catches it and
  the `α`-uniform claim survives — but no general proof of that mechanism is known yet: the
  angular total-variation device of `NOTES_t2SupF.md` requires the exponent condition
  `2 - γ ≤ η`, i.e. exactly `α ≥ 1/10`, and the `θ`-Lipschitz-mass arguments need a pointwise
  Lipschitz bound on the slice `θ ↦ D_z^2 f(z,·)` (which `CoefThMem 1 f` does not supply: it
  bounds `∂_θ f`, `D_z ∂_θ f`, `D_θ ∂_θ f`, i.e. the `f`- and `D_z f`-level oscillations
  only).  See `NOTES_t2SupF.md` for the full record of the routes tried and the numerical
  sanity checks in the product class `f = M(z)ψ(θ)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.TransportS.sup_dz_le_hk

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The `a ≥ 1` case of `T2SupF`, with the `α`-uniform constant of `flat_mixed_le 1`.**

`|mixed b a f z θ| ≤ C₁ * (Xn α f + CoefTh 1 f)` for `1 ≤ a`, `a + b ≤ 2`: the σ-gain
`flat_mixed_le 1` gives `|mixed b a f| ≤ C₁ sin(2θ) · K` with `K` a bound on the constituents
of `CoefTh 1 f`, and `supAbsO_le_coefTh` (using the honesty hypothesis `CoefThMem 1 f`) turns
that into `K = CoefTh 1 f`. -/
theorem t2SupF_aPos :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → T2SF α f →
      ∀ b a : ℕ, 1 ≤ a → a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ|
          ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) := by
  obtain ⟨C1, hC1pos, hflat⟩ := flat_mixed_le 1
  refine ⟨C1, hC1pos, ?_⟩
  intro α f hα hα1 hsf b a ha hab z θ hz hθ hθ1
  have hKnn : 0 ≤ Work.FTS.VocabO.CoefTh 1 f := coefTh_nonneg 1 f
  have hbound : ∀ (b' i : ℕ), b' + i ≤ 1 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed b' i (Work.Spaces.pth f) z' θ'| ≤ Work.FTS.VocabO.CoefTh 1 f := by
    intro b' i hbi z' θ' hz' hθ' hθ'1
    obtain ⟨K, hK⟩ := hsf.coef b' i hbi
    have h1 : |Work.Spaces.mixed b' i (Work.Spaces.pth f) z' θ'|
        ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed b' i (Work.Spaces.pth f)) :=
      Work.FTS.H2.le_supAbsO hz' hθ' hθ'1
        (fun z'' θ'' hz'' hθ'' hθ''1 => hK z'' θ'' hz'' hθ'' hθ''1)
    exact le_trans h1 (supAbsO_le_coefTh (f := f) hbi)
  have h := hflat f hsf.smoothOpen (Work.FTS.VocabO.CoefTh 1 f) hKnn hbound a b ha hab
    z θ hz hθ hθ1
  have hsin : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hXnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  calc |Work.Spaces.mixed b a f z θ| ≤ C1 * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 1 f := h
    _ ≤ C1 * 1 * Work.FTS.VocabO.CoefTh 1 f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsin hC1pos.le) hKnn
    _ = C1 * Work.FTS.VocabO.CoefTh 1 f := by ring
    _ ≤ C1 * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hXnn) hC1pos.le

/-- **A pointwise bound on the constituents of `CoefTh 1 f`.**  Any `mixed b i (∂_θ f)` with
`b + i ≤ 1` is bounded on the open quadrant by `CoefTh 1 f` itself.  (`CoefThMem 1 f` is
needed only to know that the relevant `supAbsO` is not the junk value `0`.) -/
theorem t2SupF_pth_le_coefTh {α : ℝ} {f : Fn} (hsf : T2SF α f) {b i : ℕ} (hbi : b + i ≤ 1)
    {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ1 : θ < π / 2) :
    |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ| ≤ Work.FTS.VocabO.CoefTh 1 f := by
  obtain ⟨K, hK⟩ := hsf.coef b i hbi
  have h1 : |Work.Spaces.mixed b i (Work.Spaces.pth f) z θ|
      ≤ Work.FTS.H2.supAbsO (Work.Spaces.mixed b i (Work.Spaces.pth f)) :=
    Work.FTS.H2.le_supAbsO hz hθ hθ1
      (fun z' θ' hz' hθ' hθ'1 => hK z' θ' hz' hθ' hθ'1)
  exact le_trans h1 (supAbsO_le_coefTh (f := f) hbi)

/-- Over the middle half `[π/8, 3π/8]` of `Iθ`, some point has value at most `(4/π)` times
the integral over `Iθ`. -/
theorem mid_min_le_avg {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (π / 8) (3 * π / 8)))
    (hint : MeasureTheory.IntegrableOn φ Work.Spaces.Iθ)
    (hnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ φ θ) :
    ∃ θ₀ ∈ Set.Icc (π / 8) (3 * π / 8),
      φ θ₀ ≤ (4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
  have hle : π / 8 ≤ 3 * π / 8 := by linarith [Real.pi_pos]
  obtain ⟨θ₀, hθ₀, hmin⟩ :=
    (isCompact_Icc (a := π / 8) (b := 3 * π / 8)).exists_isMinOn
      ⟨π / 8, by simp only [Set.mem_Icc]; exact ⟨le_rfl, hle⟩⟩ hcont
  refine ⟨θ₀, hθ₀, ?_⟩
  have hsub : Set.Icc (π / 8) (3 * π / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, Real.pi_pos]⟩
  have hmeas : MeasurableSet (Set.Icc (π / 8) (3 * π / 8)) := measurableSet_Icc
  have hIccint : MeasureTheory.IntegrableOn φ (Set.Icc (π / 8) (3 * π / 8)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => φ θ₀)
      (Set.Icc (π / 8) (3 * π / 8)) :=
    integrableOn_const (μ := MeasureTheory.volume)
      (isCompact_Icc (a := π / 8) (b := 3 * π / 8)).measure_lt_top.ne (by simp)
  have hmono : ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ₀
      ≤ ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ :=
    setIntegral_mono_on hconst hIccint hmeas (fun θ hθ => hmin hθ)
  have hval : ∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ₀ = φ θ₀ * (π / 4) := by
    rw [setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : (0 : ℝ) ≤ 3 * π / 8 - π / 8)]
    ring
  have h2 : (∫ θ in Set.Icc (π / 8) (3 * π / 8), φ θ)
      ≤ ∫ θ in Work.Spaces.Iθ, φ θ := by
    rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) from rfl]
    exact MeasureTheory.setIntegral_mono_set hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hnn)
      (Filter.Eventually.of_forall (fun x hx => hsub hx))
  have h3 : φ θ₀ * (π / 4) ≤ ∫ θ in Work.Spaces.Iθ, φ θ := by
    rw [← hval]
    exact hmono.trans h2
  have h4 : φ θ₀ ≤ (∫ θ in Work.Spaces.Iθ, φ θ) / (π / 4) :=
    (le_div_iff₀ (by linarith [Real.pi_pos] : (0 : ℝ) < π / 4)).mpr (by linarith [h3])
  calc φ θ₀ ≤ (∫ θ in Work.Spaces.Iθ, φ θ) / (π / 4) := h4
    _ = (4 / Real.pi) * ∫ θ in Work.Spaces.Iθ, φ θ := by
        rw [div_eq_mul_inv, inv_div]
        ring

/-- **The `a = 0`, `b ≤ 1` case of `T2SupF`, with an `α`-uniform constant.**

`|D_z^b f(z,θ)| ≤ C (Xn α f + CoefTh 1 f)` for `b ≤ 1`, from the frozen hypotheses alone.
The proof is `θ`-average (`SupDzAux.sup_dz_avg_le`) plus `θ`-Lipschitz
(`CoefThMem 1 f` through `t2SupF_pth_le_coefTh`) plus the mean value theorem; no `(γ-1)^{-1}`
appears. -/
theorem t2SupF_b_le_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α ≤ 1 → T2SF α f →
      ∀ b : ℕ, b ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.DzIter b f z θ|
          ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) := by
  obtain ⟨CV, hCVpos, hV⟩ := Work.FTS.TransportS.SupDzAux.sup_dz_avg_le
  refine ⟨Real.sqrt (8 * CV / Real.pi) + Real.pi / Real.sqrt 2 + 1, by positivity, ?_⟩
  intro α f hα hα1 hsf b hb z θ hz hθ hθ1
  have hF : Work.FTS.EllipticEst.SmoothOpen f := hsf.smoothOpen
  have hmem : Work.Spaces.HkMem α 4 f := hsf.hk
  set Q : ℝ := Work.FTS.Nonlin.Xn α f with hQdef
  set K : ℝ := Work.FTS.VocabO.CoefTh 1 f with hKdef
  set C : ℝ := Real.sqrt (8 * CV / Real.pi) + Real.pi / Real.sqrt 2 + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hQnn : 0 ≤ Q := by rw [hQdef]; exact Work.Spaces.HkNorm_nonneg α 4 f
  have hKnn : 0 ≤ K := by rw [hKdef]; exact coefTh_nonneg 1 f
  have hQ2 : Q ^ 2 = Work.Spaces.HkSq α 4 f := by rw [hQdef]; exact Work.FTS.H2.HkNorm_sq α f
  -- the angular slice at `z` is integrable, being dominated by the `ℋ⁴`-integrand
  have hint : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.DzIter b f z σ) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2) ^ 2)
        ((hF.DzIter b).continuousOn.pow 2) hz
    · filter_upwards [Work.FTS.H2.ae_sin_two_pos] with σ hσ
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact Work.FTS.TransportS.SupDzAux.avgDzIter_sq_le α f hz hσ b (by omega)
  -- the angular average is bounded uniformly in `z`
  have hAvg : ∫ σ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z σ) ^ 2
      ≤ CV * Work.Spaces.HkSq α 4 f := hV α f b hα hα1 hF hmem (by omega) z hz
  -- a point of the middle half where the slice is at most `4/π` times its mean
  have hcontmid : ContinuousOn (fun σ => (Work.Spaces.DzIter b f z σ) ^ 2)
      (Set.Icc (π / 8) (3 * π / 8)) := by
    have hc : ContinuousOn (fun σ => Work.Spaces.DzIter b f z σ) (Set.Ioo (0 : ℝ) (π / 2)) :=
      ((hF.DzIter b).curry_θ hz).continuousOn
    refine (hc.mono ?_).pow 2
    intro σ hσ
    exact ⟨by linarith [hσ.1, Real.pi_pos], by linarith [hσ.2, Real.pi_pos]⟩
  obtain ⟨θ₀, hθ₀mem, hθ₀le⟩ := mid_min_le_avg hcontmid hint (fun σ _ => sq_nonneg _)
  have hθ₀I : θ₀ ∈ Work.Spaces.Iθ :=
    ⟨by linarith [hθ₀mem.1, Real.pi_pos], by linarith [hθ₀mem.2, Real.pi_pos]⟩
  -- the `θ`-Lipschitz estimate for the slice, on the interval between `θ` and `θ₀`
  have hsubu : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [h1], by linarith [h2, hθ₀mem.2, Real.pi_pos]⟩
    · exact ⟨by linarith [hθ₀mem.1, Real.pi_pos, h1], by linarith [h2]⟩
  have hdiff : ∀ x ∈ Set.uIcc θ θ₀,
      DifferentiableAt ℝ (fun σ => Work.Spaces.DzIter b f z σ) x := by
    have hc := ((hF.DzIter b).curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero
    intro x hx
    exact hc.differentiableAt (isOpen_Ioo.mem_nhds (hsubu hx))
  have hbd : ∀ x ∈ Set.uIcc θ θ₀,
      ‖deriv (fun σ => Work.Spaces.DzIter b f z σ) x‖ ≤ K := by
    intro x hx
    have hxI := hsubu hx
    have hpth : deriv (fun σ => Work.Spaces.DzIter b f z σ) x
        = Work.Spaces.pth (Work.Spaces.DzIter b f) z x := rfl
    have hcl : Work.Spaces.pth (Work.Spaces.DzIter b f) z x
        = Work.Spaces.DzIter b (Work.Spaces.pth f) z x :=
      Work.Blocks.pth_DzIter_eqOn_Q0 hF b
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hxI.1, hxI.2⟩)
    have hpt := t2SupF_pth_le_coefTh (α := α) hsf (b := b) (i := 0) (by omega)
      hz hxI.1 hxI.2
    rw [hpth, hcl, Real.norm_eq_abs, hKdef]
    simpa only [Work.Spaces.mixed_zero_right] using hpt
  have hmvt : |Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀| ≤ K * |θ - θ₀| := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun σ => Work.Spaces.DzIter b f z σ)
      (s := Set.uIcc θ θ₀) (C := K) hdiff hbd
      (convex_uIcc θ θ₀) Set.left_mem_uIcc Set.right_mem_uIcc
    simpa only [Real.norm_eq_abs, abs_sub_comm] using h
  have hπ2 : |θ - θ₀| ≤ π / 2 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hθ1.le, hθ₀I.1], by linarith [hθ₀I.2, hθ.le]⟩
  have hosc : (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
      ≤ K ^ 2 * (π / 2) ^ 2 := by
    have h1 := hmvt
    have h2 : K * |θ - θ₀| ≤ K * (π / 2) := mul_le_mul_of_nonneg_left hπ2 hKnn
    have h3 : |Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀| ≤ K * (π / 2) :=
      le_trans h1 h2
    have h4 : |Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀| ^ 2
        = (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2 := by
      rw [sq_abs]
    have h5 : (K * (π / 2)) ^ 2 = K ^ 2 * (π / 2) ^ 2 := by ring
    calc (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
        = |Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀| ^ 2 := h4.symm
      _ ≤ (K * (π / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = K ^ 2 * (π / 2) ^ 2 := h5
  have hmin : (Work.Spaces.DzIter b f z θ₀) ^ 2
      ≤ (4 / Real.pi) * (CV * Work.Spaces.HkSq α 4 f) :=
    le_trans hθ₀le (mul_le_mul_of_nonneg_left hAvg (by positivity))
  have hkey : (Work.Spaces.DzIter b f z θ) ^ 2
      ≤ K ^ 2 * (π / 2) ^ 2 * 2 + 2 * ((4 / Real.pi) * (CV * Work.Spaces.HkSq α 4 f)) := by
    have h1 : (Work.Spaces.DzIter b f z θ) ^ 2
        ≤ 2 * (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z θ₀) ^ 2
          + 2 * (Work.Spaces.DzIter b f z θ₀) ^ 2 := by
      nlinarith [sq_nonneg (Work.Spaces.DzIter b f z θ - 2 * Work.Spaces.DzIter b f z θ₀)]
    nlinarith [h1, hosc, hmin]
  -- the explicit `α`-uniform constant
  have hCsq1 : 8 * CV / Real.pi ≤ C ^ 2 := by
    have h0 : Real.sqrt (8 * CV / Real.pi) ≤ C := by
      rw [hCdef]
      linarith [Real.sqrt_nonneg (8 * CV / Real.pi),
        div_nonneg Real.pi_pos.le (Real.sqrt_nonneg 2)]
    have h1 : 0 ≤ Real.sqrt (8 * CV / Real.pi) := Real.sqrt_nonneg _
    have h2 : (Real.sqrt (8 * CV / Real.pi)) ^ 2 = 8 * CV / Real.pi :=
      Real.sq_sqrt (by positivity)
    have h3 : (Real.sqrt (8 * CV / Real.pi)) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ h1 h0 2
    rw [h2] at h3
    exact h3
  have hCsq2 : Real.pi ^ 2 / 2 ≤ C ^ 2 := by
    have h0 : Real.pi / Real.sqrt 2 ≤ C := by
      rw [hCdef]
      linarith [Real.sqrt_nonneg (8 * CV / Real.pi), Real.sqrt_nonneg 2, Real.pi_pos, hCVpos]
    have h1 : 0 ≤ Real.pi / Real.sqrt 2 := by positivity
    have h2 : (Real.pi / Real.sqrt 2) ^ 2 = Real.pi ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h3 : (Real.pi / Real.sqrt 2) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ h1 h0 2
    rw [h2] at h3
    exact h3
  have hfinal2 : (Work.Spaces.DzIter b f z θ) ^ 2 ≤ C ^ 2 * (Q + K) ^ 2 := by
    have hsq1 : K ^ 2 * (π / 2) ^ 2 * 2 = K ^ 2 * (Real.pi ^ 2 / 2) := by ring
    have hsq2 : 2 * ((4 / Real.pi) * (CV * Work.Spaces.HkSq α 4 f))
        = (8 * CV / Real.pi) * Q ^ 2 := by
      rw [hQ2]; ring
    rw [hsq1, hsq2] at hkey
    have h1 : K ^ 2 * (Real.pi ^ 2 / 2) ≤ C ^ 2 * K ^ 2 := by
      rw [mul_comm (K ^ 2) (Real.pi ^ 2 / 2)]
      exact mul_le_mul_of_nonneg_right hCsq2 (sq_nonneg K)
    have h2 : (8 * CV / Real.pi) * Q ^ 2 ≤ C ^ 2 * Q ^ 2 :=
      mul_le_mul_of_nonneg_right hCsq1 (sq_nonneg Q)
    have h3 : C ^ 2 * (Q + K) ^ 2
        = C ^ 2 * Q ^ 2 + C ^ 2 * K ^ 2 + 2 * (C ^ 2 * Q * K) := by ring
    have h4 : 0 ≤ 2 * (C ^ 2 * Q * K) := by positivity
    linarith [hkey, h1, h2, h3, h4]
  have hs : Real.sqrt (C ^ 2 * (Q + K) ^ 2) = C * (Q + K) := by
    rw [← mul_pow]
    exact Real.sqrt_sq (by positivity)
  have := Real.abs_le_sqrt hfinal2
  rw [hs] at this
  simpa only [hQdef, hKdef] using this

/-- **The `a = 0`, `b = 2` case of `T2SupF` for `α ≥ 1/10`.**

For `α ≥ 1/10` the factor `1/√(gam α - 1) = 1/√(α/10) ≤ 10` in the proved pointwise bounds
`Work.FTS.TransportS.sup_dz_le_hk` (`|D_z^b f| ≤ C/√(γ-1) · Xn α f`, `b ≤ 2`) is uniformly
bounded, so `|D_z²f| ≤ 10·C·Xn α f ≤ 10·C·(Xn α f + CoefTh 1 f)`.  No new mathematics is
needed here: the `α`-dependence of the paper's `SecondDerivativesBounded` is harmless as soon
as `γ - 1` stays away from `0`. -/
theorem t2SupF_b2_large :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 1 / 10 ≤ α → α ≤ 1 → T2SF α f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.DzIter 2 f z θ|
          ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) := by
  obtain ⟨C, hCpos, hsup⟩ := Work.FTS.TransportS.sup_dz_le_hk
  refine ⟨10 * C, by positivity, ?_⟩
  intro α f hα10 hα1 hsf z θ hz hθ hθ1
  have hα : 0 < α := by linarith
  have hγ : (1 : ℝ) / 100 ≤ Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hγpos : 0 < Work.Spaces.gam α - 1 := by linarith
  have hsqrt : (1 : ℝ) / 10 ≤ Real.sqrt (Work.Spaces.gam α - 1) := by
    have hγ' : ((1 : ℝ) / 10) ^ 2 ≤ Work.Spaces.gam α - 1 := by
      have : ((1 : ℝ) / 10) ^ 2 = 1 / 100 := by norm_num
      rw [this]; exact hγ
    calc (1 : ℝ) / 10 = Real.sqrt (((1 : ℝ) / 10) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_le_sqrt hγ'
  have hx : 0 < Real.sqrt (Work.Spaces.gam α - 1) := Real.sqrt_pos.mpr hγpos
  have hdiv : C / Real.sqrt (Work.Spaces.gam α - 1) ≤ 10 * C := by
    rw [div_le_iff₀ hx]
    calc C = 10 * C * (1 / 10) := by ring
      _ ≤ 10 * C * Real.sqrt (Work.Spaces.gam α - 1) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
  have hb := hsup α f hα hα1 hsf.smoothOpen hsf.hk 2 le_rfl z θ hz hθ hθ1
  have hXnn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hKnn : 0 ≤ Work.FTS.VocabO.CoefTh 1 f := coefTh_nonneg 1 f
  calc |Work.Spaces.DzIter 2 f z θ|
      ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := hb
    _ ≤ 10 * C * Work.FTS.Nonlin.Xn α f :=
        mul_le_mul_of_nonneg_right hdiv hXnn
    _ ≤ 10 * C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hKnn) (by positivity)

/-- **The `a = 0`, `b = 2` case of `T2SupF` for `α < 1/10`** — the remaining gap.

Here the factor `1/√(γ-1) = √(10/α)` of `sup_dz_le_hk` is unbounded, and the pointwise
hypotheses `CoefThMem 1 f` (which bound `∂_θf`, `D_z∂_θf`, `D_θ∂_θf` on the quadrant) have to
take over.  The statement is a proper sub-case of the frozen `T2SupF`; the analysis of the
routes tried so far is recorded in the module docstring of this file and in `NOTES_t2SupF.md`
(the angular total-variation device needs `2 - γ ≤ η`, i.e. exactly `α ≥ 1/10`, so it cannot
reach this range, and the θ-Lipschitz-mass arguments need a pointwise Lipschitz bound on the
slice `θ ↦ D_z²f(z,θ)`, which is not available from `CoefThMem 1 f`).

**Status 2026-10-12** (statement unchanged; still the only `sorry` of this file).  The frozen
hypotheses are not known to be sufficient for the attempted routes, and the statement is *not
known to be false*: every adversarial family checked (`θ`-log-profile, `θ`-bumps shrinking at
either endpoint, oscillatory radial profiles `φ(N log z)`) keeps
`|D_z²f| / (Xn α f + CoefTh 1 f)` below `0.005`, because the higher `ℋ⁴`-slots and the
`D_θ∂_θf`-slot of `CoefTh 1` penalise exactly the concentration a counterexample would need.
What *is* proved is the version with the honest Lipschitz datum:
`TransportS/sup_dz2_coef2.lean`, `T2S_coef2.lean`, `T2S_coef2_closed.lean`
(`T2SupF2_proof`, `T2S_coef2_final`, axiom-clean), and `T2S_coef2.lean` is the route the
level-six chapter's cone already uses.  See `NOTES_TransportS.md` §1a and `NOTES_t2SupF.md`. -/
theorem t2SupF_b2_small :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Fn), 0 < α → α < 1 / 10 → T2SF α f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.DzIter 2 f z θ|
          ≤ C * (Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f) := by
  sorry

/-! ## Weighted slot comparisons (ingredients of the angular total-variation device)

The two pointwise bounds below (Step 4 of the plan in `NOTES_t2SupF.md`) upgrade the pure-`z` and
the mixed `ℋ⁴`-slot summands to a general angular weight `sin(2θ)^{-c}`, which is what the angular
device `Work.FTS.TransportS.TvUniform.tv_uniform_bound` consumes. -/

/-- The pure-`z` slot with a general angular weight: for `c ≤ η`,
`(D_z^i f z θ)² · w(z)² · sin(2θ)^{-c} ≤ HkIntegrand α 4 f z θ`. -/
theorem dzIter_sq_w_rpow_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ c : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (hc : c ≤ Work.Spaces.eta) (i : ℕ) (hi : i ≤ 4) :
    (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-c) ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have h1 : (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ i hi
    have h2 : (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
      have hs2 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
          = Real.sin (2 * θ) ^ Work.Spaces.eta := by
        rw [sq, ← Real.rpow_add hsin,
          show Work.Spaces.eta / 2 + Work.Spaces.eta / 2 = Work.Spaces.eta by ring]
      rw [mul_pow, div_pow, hs2, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hsin)]
      ring
    rwa [h2] at h
  have h3 : (Real.sin (2 * θ)) ^ (-c) ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    have hs1 : Real.sin (2 * θ) ^ Work.Spaces.eta ≤ Real.sin (2 * θ) ^ c :=
      Real.rpow_le_rpow_of_exponent_ge hsin (Real.sin_le_one (2 * θ)) hc
    rw [Real.rpow_neg (le_of_lt hsin) c, Real.rpow_neg (le_of_lt hsin) Work.Spaces.eta,
      ← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hsin Work.Spaces.eta) hs1
  calc (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-c)
      ≤ (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := h1

/-- The mixed slot with a general angular weight: for `c ≤ γ`,
`(mixed j i f z θ)² · w(z)² · sin(2θ)^{-c} ≤ HkIntegrand α 4 f z θ`. -/
theorem mixed_sq_w_rpow_le_HkIntegrand (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ c : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (hc : c ≤ Work.Spaces.gam α) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-c) ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have h1 : (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij
    have h2 : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      have hw : Work.Spaces.Wt α z θ
          = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := rfl
      have hs2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
          = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [sq, ← Real.rpow_add hsin,
          show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2)
            = -(Work.Spaces.gam α) by ring]
      rw [hw, mul_pow, mul_pow, hs2]
      ring
    rwa [h2] at h
  have h3 : (Real.sin (2 * θ)) ^ (-c) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    have hs1 : Real.sin (2 * θ) ^ Work.Spaces.gam α ≤ Real.sin (2 * θ) ^ c :=
      Real.rpow_le_rpow_of_exponent_ge hsin (Real.sin_le_one (2 * θ)) hc
    rw [Real.rpow_neg (le_of_lt hsin) c, Real.rpow_neg (le_of_lt hsin) (Work.Spaces.gam α),
      ← one_div, ← one_div]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hsin (Work.Spaces.gam α)) hs1
  calc (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-c)
      ≤ (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ := h1

/-- **`T2SupF`.**  Assembled from the `a ≥ 1` case (`t2SupF_aPos`), the `a = 0`, `b ≤ 1` case
(`t2SupF_b_le_one`) and the two halves of the `a = 0`, `b = 2` case
(`t2SupF_b2_large` for `α ≥ 1/10`, `t2SupF_b2_small` for `α < 1/10`).  Only the last of these
is still open; see the module docstring and `NOTES_t2SupF.md`. -/
theorem t2SupF : Work.FTS.TransportS.T2SupF := by
  classical
  obtain ⟨C1, _hC1pos, h1⟩ := t2SupF_aPos
  obtain ⟨C0, _hC0pos, h0⟩ := t2SupF_b_le_one
  obtain ⟨C2, _hC2pos, h2⟩ := t2SupF_b2_large
  obtain ⟨C3, _hC3pos, h3⟩ := t2SupF_b2_small
  refine ⟨2 * (C1 + C0 + C2 + C3) + 1, by positivity, ?_⟩
  intro α f hα hα1 hsf b a hab z θ hz hθ hθ1
  have hWnn : 0 ≤ Work.FTS.Nonlin.Xn α f + Work.FTS.VocabO.CoefTh 1 f :=
    add_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (coefTh_nonneg 1 f)
  have hCa : C1 ≤ 2 * (C1 + C0 + C2 + C3) + 1 := by linarith
  have hCb : C0 ≤ 2 * (C1 + C0 + C2 + C3) + 1 := by linarith
  have hCc : C2 ≤ 2 * (C1 + C0 + C2 + C3) + 1 := by linarith
  have hCd : C3 ≤ 2 * (C1 + C0 + C2 + C3) + 1 := by linarith
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    by_cases hb1 : b ≤ 1
    · exact le_trans
        (by simpa only [Work.Spaces.mixed_zero_right] using
          h0 α f hα hα1 hsf b hb1 z θ hz hθ hθ1)
        (mul_le_mul_of_nonneg_right hCb hWnn)
    · have hb2 : b = 2 := by omega
      subst hb2
      by_cases hα10 : 1 / 10 ≤ α
      · exact le_trans
          (by simpa only [Work.Spaces.mixed_zero_right] using
            h2 α f hα10 hα1 hsf z θ hz hθ hθ1)
          (mul_le_mul_of_nonneg_right hCc hWnn)
      · exact le_trans
          (by simpa only [Work.Spaces.mixed_zero_right] using
            h3 α f hα (by linarith) hsf z θ hz hθ hθ1)
          (mul_le_mul_of_nonneg_right hCd hWnn)
  · exact le_trans (h1 α f hα hα1 hsf b a ha hab z θ hz hθ hθ1)
      (mul_le_mul_of_nonneg_right hCa hWnn)

end Work.FTS.TransportS
