/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.PARIMPL.Nm_mem_closure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.SplitPhase_normalForm` — the normal form of the split phase (L0)

This file proves the bundle `SplitPhase_normalForm` of the implosion-comparison design note
(`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.1, items L0.2–L0.5).  Given a parameter
normal form `P : Work.PARIMPL.ParNormal d` of a root-parabolic parameter `c₀` and the
antiholomorphic-symmetry statement `hswap` for the derivative of the second return map
`Ft c = (T_c)^[10]` (the second half of `Work.FlowerGlue2.SymmDeriv_tricorn`), it asserts:

* **L0.2** the multiplier of the normal form at its two split fixed points: for `σ = ±1`,
  `Ft c` has derivative `1 + 2·(σ a)·h(σ a)` at `m c + s c·(σ a)`;
* **L0.3** the germ values at `±a` are conjugate: `h c a = conj (h c (−a))` — this is the
  *split phase* symmetry, obtained from `hswap` and L0.2;
* **L0.4** the imaginary parts of the germ constants are small: `|Im τ_c| ≤ A λ_c²` and
  `|Im h₁_c| ≤ A λ_c`, with `τ_c = h c 0`, `λ_c = lam c`;
* **L0.5** the normalisation at the root parameter `h c₀ 0 = 1` and the phase blow-up
  `(π/λ_c)·‖h c 0 − 1‖ → 0` along the implosion side `Nm`.

The mathematical content is that the *only* way the phase `π/λ` can fail to be additively
corrected by `o(1)` is through a non-real `τ_c` of size `o(λ)`; the swap symmetry L0.3 supplies
exactly this, and L0.4–L0.5 turn it into the limit.

## Notation

`τ_c := P.h c 0`, `λ_c := P.lam c`, `a = P.a c = i·λ_c` on `Nm`, `m c`, `s c` the chart of the
normal form, `Ft c = (T_c)^[10] = (gtc c) ∘ (gtc c)`.
-/

open Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal Ft gtc)

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## L0.2 — the multiplier of the normal form at the split fixed points -/

/-- **L0.2.**  On the implosion side, at each of the two split fixed points `m c ± s c·a` of the
second return map, `Ft c` is differentiable with the multiplier `1 + 2·(σ a)·h(σ a)`.

The normal form identity `P.conj` holds on the (open) chart ball, and the point `σ a` (`σ = ±1`)
satisfies `‖σ a‖ = λ_c < r`, so `Ft c` coincides near the image point with the affine conjugate of
the model `ζ + (ζ² − a²)h(ζ)`; at `ζ = σ a` the quadratic factor vanishes and the difference
quotient of the model is `1 + (ζ + σ a)h(ζ)`, whose limit is `1 + 2(σ a)h(σ a)`. -/
theorem splitPhase_hasDerivAt (P : ParNormal d) {c : ℂ} (hc : c ∈ P.Nm) (hr : P.lam c < P.r)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    HasDerivAt (Ft c) (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c))
      (P.m c + P.s c * (σ * P.a c)) := by
  have hs : P.s c ≠ 0 := P.s_ne c hc.1
  have ha : P.a c = (P.lam c : ℂ) * Complex.I := P.a_of_mem_Nm hc
  have hσ_norm : ‖σ‖ = 1 := by rcases hσ with h | h <;> simp [h]
  have ha_norm : ‖P.a c‖ = P.lam c := by
    rw [ha, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos (P.lam_pos_of_mem_Nm hc)]
  have hζ_norm : ‖σ * P.a c‖ = P.lam c := by rw [norm_mul, hσ_norm, one_mul, ha_norm]
  have hζball : σ * P.a c ∈ ball (0 : ℂ) P.r := by
    rw [Metric.mem_ball, dist_zero_right, hζ_norm]; exact hr
  have hmem : (c, σ * P.a c) ∈ ball c₀ P.ρ₀ ×ˢ ball (0 : ℂ) P.r := ⟨hc.1, hζball⟩
  have hcont : ContinuousAt (P.h c) (σ * P.a c) := by
    have hU : ball c₀ P.ρ₀ ×ˢ ball (0 : ℂ) P.r ∈ 𝓝 (c, σ * P.a c) :=
      (isOpen_ball.prod isOpen_ball).mem_nhds hmem
    exact (P.cont_h.continuousAt hU).comp (continuousAt_const.prodMk continuousAt_id)
  have hfix : Work.Implosion.normalForm (P.a c) (P.h c) (σ * P.a c) = σ * P.a c := by
    rcases hσ with rfl | rfl
    · simpa using Work.Implosion.normalForm_fixed_left (P.a c) (P.h c)
    · simpa using Work.Implosion.normalForm_fixed_right (P.a c) (P.h c)
  have hsub : ∀ y : ℂ, Work.Implosion.normalForm (P.a c) (P.h c) y
      - Work.Implosion.normalForm (P.a c) (P.h c) (σ * P.a c)
      = (y - σ * P.a c) * (1 + (y + σ * P.a c) * P.h c y) := by
    intro y
    rw [hfix]
    rcases hσ with rfl | rfl
    · simpa using Work.Implosion.normalForm_sub_left (P.a c) (P.h c) y
    · simpa [neg_one_mul, sub_eq_add_neg, neg_neg] using
        Work.Implosion.normalForm_add_left (P.a c) (P.h c) y
  have hNF : HasDerivAt (Work.Implosion.normalForm (P.a c) (P.h c))
      (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c)) (σ * P.a c) := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hbase : Tendsto (fun y => 1 + (y + σ * P.a c) * P.h c y) (𝓝[≠] (σ * P.a c))
        (𝓝 (1 + (σ * P.a c + σ * P.a c) * P.h c (σ * P.a c))) := by
      have hR : ContinuousAt (fun y : ℂ => 1 + (y + σ * P.a c) * P.h c y) (σ * P.a c) :=
        continuousAt_const.add ((continuousAt_id.add continuousAt_const).mul hcont)
      exact hR.tendsto.mono_left inf_le_left
    have hgoal : 1 + (σ * P.a c + σ * P.a c) * P.h c (σ * P.a c)
        = 1 + 2 * (σ * P.a c) * P.h c (σ * P.a c) := by ring
    rw [hgoal] at hbase
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y - σ * P.a c ≠ 0 := sub_ne_zero.mpr hy
    simp only [slope_fun_def, vsub_eq_sub, smul_eq_mul]
    rw [hsub y, ← mul_assoc, inv_mul_cancel₀ hy', one_mul]
  have hinner : HasDerivAt (fun w : ℂ => (w - P.m c) * (P.s c)⁻¹) (P.s c)⁻¹
      (P.m c + P.s c * (σ * P.a c)) := by
    simpa using ((hasDerivAt_id (P.m c + P.s c * (σ * P.a c))).sub_const (P.m c)).mul_const
      (P.s c)⁻¹
  have hinner_val : (P.m c + P.s c * (σ * P.a c) - P.m c) * (P.s c)⁻¹ = σ * P.a c := by
    rw [add_sub_cancel_left, mul_right_comm, mul_inv_cancel₀ hs, one_mul]
  have houter : HasDerivAt
      (fun z : ℂ => P.m c + P.s c * Work.Implosion.normalForm (P.a c) (P.h c) z)
      (P.s c * (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c))) (σ * P.a c) := by
    have h0 := (hasDerivAt_const (σ * P.a c) (P.m c)).add (hNF.const_mul (P.s c))
    rw [zero_add] at h0
    exact h0
  have houter' : HasDerivAt
      (fun z : ℂ => P.m c + P.s c * Work.Implosion.normalForm (P.a c) (P.h c) z)
      (P.s c * (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c)))
      ((P.m c + P.s c * (σ * P.a c) - P.m c) * (P.s c)⁻¹) := by
    rw [hinner_val]; exact houter
  have hG : HasDerivAt (fun w : ℂ => P.m c + P.s c *
      Work.Implosion.normalForm (P.a c) (P.h c) ((w - P.m c) * (P.s c)⁻¹))
      (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c)) (P.m c + P.s c * (σ * P.a c)) := by
    have h := HasDerivAt.comp (P.m c + P.s c * (σ * P.a c)) houter' hinner
    have hd : P.s c * (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c)) * (P.s c)⁻¹
        = 1 + 2 * (σ * P.a c) * P.h c (σ * P.a c) := by
      rw [mul_right_comm, mul_inv_cancel₀ hs, one_mul]
    rw [hd] at h
    exact h
  have hEq : (Ft c) =ᶠ[𝓝 (P.m c + P.s c * (σ * P.a c))] (fun w : ℂ => P.m c + P.s c *
      Work.Implosion.normalForm (P.a c) (P.h c) ((w - P.m c) * (P.s c)⁻¹)) := by
    have hcont_inner : ContinuousAt (fun w : ℂ => (w - P.m c) * (P.s c)⁻¹)
        (P.m c + P.s c * (σ * P.a c)) := hinner.continuousAt
    have hball : (fun w : ℂ => (w - P.m c) * (P.s c)⁻¹) ⁻¹' ball (0 : ℂ) P.r
        ∈ 𝓝 (P.m c + P.s c * (σ * P.a c)) :=
      hcont_inner.preimage_mem_nhds (by rw [hinner_val]; exact isOpen_ball.mem_nhds hζball)
    filter_upwards [hball] with w hw
    have hzw : P.m c + P.s c * ((w - P.m c) * (P.s c)⁻¹) = w := by
      rw [show P.s c * ((w - P.m c) * (P.s c)⁻¹) = w - P.m c by
        rw [← mul_assoc, mul_right_comm, mul_inv_cancel₀ hs, one_mul]]
      ring
    have hc' := P.conj c hc.1 ((w - P.m c) * (P.s c)⁻¹) hw
    rw [hzw] at hc'
    exact hc'
  exact hG.congr_of_eventuallyEq hEq

/-! ## L0.3 — the germ values at the split fixed points are conjugate -/

/-- **L0.3.**  On the implosion side, `h c a = conj (h c (−a))`.  The antiholomorphic square root
`g c = (T_c)^[5]` swaps the two split points (`P.swap`), so `hswap` forces the multipliers
`1 + 2a·h(a)` and `1 − 2a·h(−a)` to be conjugate; as `conj a = −a` and `a ≠ 0`, this is exactly
the statement. -/
theorem splitPhase_h_split_conj (P : ParNormal d) {c : ℂ} (hc : c ∈ P.Nm) (hr : P.lam c < P.r)
    (hA : ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
      HasDerivAt (Ft c) (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c))
        (P.m c + P.s c * (σ * P.a c)))
    (hswap : ∀ (c p q : ℂ), gtc c p = q → gtc c q = p →
      deriv (Ft c) q = star (deriv (Ft c) p)) :
    P.h c (P.a c) = star (P.h c (-P.a c)) := by
  have ha : P.a c = (P.lam c : ℂ) * Complex.I := P.a_of_mem_Nm hc
  have ha_norm : ‖P.a c‖ = P.lam c := by
    rw [ha, norm_mul, Complex.norm_I, mul_one]; simp [abs_of_pos (P.lam_pos_of_mem_Nm hc)]
  have ha_ball : P.a c ∈ ball (0 : ℂ) P.r := by
    rw [Metric.mem_ball, dist_zero_right, ha_norm]; exact hr
  have ha_ne : P.a c ≠ 0 := by
    rw [ha]
    exact mul_ne_zero (by exact_mod_cast (ne_of_gt (P.lam_pos_of_mem_Nm hc))) Complex.I_ne_zero
  have hstar_a : star (P.a c) = -P.a c := by
    rw [ha]; simp [Complex.conj_ofReal, Complex.conj_I]
  have hp_deriv : deriv (Ft c) (P.m c + P.s c * P.a c) = 1 + 2 * P.a c * P.h c (P.a c) := by
    simpa using (hA 1 (Or.inl rfl)).deriv
  have hq_deriv : deriv (Ft c) (P.m c + P.s c * (-P.a c)) = 1 + 2 * (-P.a c) * P.h c (-P.a c) := by
    simpa using (hA (-1) (Or.inr rfl)).deriv
  have hpq : gtc c (P.m c + P.s c * P.a c) = P.m c + P.s c * (-P.a c) := by
    simpa [mul_neg, sub_eq_add_neg] using P.swap c hc.1 hc.2
  have hgg : ∀ y : ℂ, gtc c (gtc c y) = Ft c y := fun y => by
    rw [Work.PARIMPL.Ft_eq_g_comp]; rfl
  have hqp : gtc c (P.m c + P.s c * (-P.a c)) = P.m c + P.s c * P.a c := by
    rw [← hpq, hgg, P.conj c hc.1 (P.a c) ha_ball, Work.Implosion.normalForm_fixed_left]
  have hswapc := hswap c (P.m c + P.s c * P.a c) (P.m c + P.s c * (-P.a c)) hpq hqp
  rw [hp_deriv, hq_deriv] at hswapc
  have hstar_rhs : star (1 + 2 * P.a c * P.h c (P.a c))
      = 1 + 2 * (-P.a c) * star (P.h c (P.a c)) := by
    simp only [star_add, star_one, star_mul, star_ofNat, hstar_a]
    ring
  rw [hstar_rhs] at hswapc
  have h1 : 2 * (-P.a c) * P.h c (-P.a c) = 2 * (-P.a c) * star (P.h c (P.a c)) :=
    add_left_cancel hswapc
  have h2 : P.h c (-P.a c) = star (P.h c (P.a c)) :=
    mul_left_cancel₀ (mul_ne_zero (by norm_num) (neg_ne_zero.mpr ha_ne)) h1
  have h3 := congrArg star h2
  rw [star_star] at h3
  exact h3.symm

/-! ## L0.4 — the imaginary parts of the germ constants are `O(λ²)` and `O(λ)` -/

/-- **L0.4.**  Writing `h(±a) = τ ± h₁·a + e±` with `‖e±‖ ≤ A λ₂` (`ParBounds`), L0.3 gives
`2i·Im τ − 2λ·Im h₁ = conj e₋ − e₊`; the imaginary part bounds `|Im τ| ≤ Aλ²` and the real part
`|Im h₁| ≤ Aλ`. -/
theorem splitPhase_im_bounds (P : ParNormal d) {c : ℂ} (hc : c ∈ P.Nm) (hr : P.lam c < P.r)
    (hB : P.h c (P.a c) = star (P.h c (-P.a c))) :
    |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 ∧ |(P.h1 c).im| ≤ P.A * P.lam c := by
  have hb := P.bounds c hc.1
  have ha : P.a c = (P.lam c : ℂ) * Complex.I := P.a_of_mem_Nm hc
  have hlam_pos : 0 < P.lam c := P.lam_pos_of_mem_Nm hc
  have ha_norm : ‖P.a c‖ = P.lam c := by
    rw [ha, norm_mul, Complex.norm_I, mul_one]; simp [abs_of_pos hlam_pos]
  have hstar_a : star (P.a c) = -P.a c := by
    rw [ha]; simp [Complex.conj_ofReal, Complex.conj_I]
  have hconj : ∀ z : ℂ, z - star z = ((2 * z.im : ℝ) : ℂ) * Complex.I := fun z => Complex.sub_conj z
  set eplus : ℂ := P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c with heplus
  set eminus : ℂ := P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c) with heminus
  have hemp : ‖eminus‖ ≤ P.A * P.lam c ^ 2 := by
    rw [heminus]
    have h := hb.2.2.1 (-P.a c) (by rw [norm_neg, ha_norm]; exact hr)
    rwa [norm_neg, ha_norm] at h
  have hepp : ‖eplus‖ ≤ P.A * P.lam c ^ 2 := by
    rw [heplus]
    have h := hb.2.2.1 (P.a c) (by rw [ha_norm]; exact hr)
    rwa [ha_norm] at h
  have hDnorm : ‖star eminus - eplus‖ ≤ 2 * (P.A * P.lam c ^ 2) := by
    calc ‖star eminus - eplus‖ ≤ ‖star eminus‖ + ‖eplus‖ := norm_sub_le _ _
      _ = ‖eminus‖ + ‖eplus‖ := by rw [norm_star]
      _ ≤ P.A * P.lam c ^ 2 + P.A * P.lam c ^ 2 := add_le_add hemp hepp
      _ = 2 * (P.A * P.lam c ^ 2) := by ring
  have heq : (P.h c 0 - star (P.h c 0)) + (P.h1 c - star (P.h1 c)) * P.a c
      = star eminus - eplus := by
    have h1 : P.h c (P.a c) = P.h c 0 + P.h1 c * P.a c + eplus := by rw [heplus]; ring
    have h2 : P.h c (-P.a c) = P.h c 0 + P.h1 c * (-P.a c) + eminus := by rw [heminus]; ring
    have h3 : star (P.h c (-P.a c)) = star (P.h c 0) + star (P.h1 c) * P.a c + star eminus := by
      rw [h2]
      simp only [star_add, star_mul, star_neg, hstar_a]
      ring
    have hthis := hB
    rw [h1, h3] at hthis
    linear_combination hthis
  have him : (star eminus - eplus).im = 2 * (P.h c 0).im := by
    rw [← heq, hconj (P.h c 0), hconj (P.h1 c), ha]
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_I_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hre : (star eminus - eplus).re = -2 * (P.h1 c).im * P.lam c := by
    rw [← heq, hconj (P.h c 0), hconj (P.h1 c), ha]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  constructor
  · have h2 : |2 * (P.h c 0).im| ≤ 2 * (P.A * P.lam c ^ 2) := by
      rw [← him]
      calc |(star eminus - eplus).im| ≤ ‖star eminus - eplus‖ := Complex.abs_im_le_norm _
        _ ≤ 2 * (P.A * P.lam c ^ 2) := hDnorm
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h2
    linarith
  · have h2 : |2 * (P.h1 c).im * P.lam c| ≤ 2 * (P.A * P.lam c ^ 2) := by
      have hre' : 2 * (P.h1 c).im * P.lam c = -((star eminus - eplus).re) := by rw [hre]; ring
      rw [hre', abs_neg]
      calc |(star eminus - eplus).re| ≤ ‖star eminus - eplus‖ := Complex.abs_re_le_norm _
        _ ≤ 2 * (P.A * P.lam c ^ 2) := hDnorm
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hlam_pos] at h2
    nlinarith [hlam_pos]

/-! ## L0.5 — the normalisation at the root parameter and the phase blow-up -/

/-- **L0.5 (a).**  `τ_{c₀} = h c₀ 0 = 1`.  Along `Nm` the imaginary part of `τ` vanishes
(L0.4 and `λ → 0`), so `Im τ_{c₀} = 0`; with `‖τ_{c₀}‖ = 1` and `‖τ_{c₀} − 1‖ ≤ 1/2` this forces
`τ_{c₀} = 1`. -/
theorem splitPhase_tau_c0 (P : ParNormal d)
    (him : ∀ c ∈ P.Nm, P.lam c < P.r → |(P.h c 0).im| ≤ P.A * P.lam c ^ 2) :
    P.h c₀ 0 = 1 := by
  have hc₀ : c₀ ∈ ball c₀ P.ρ₀ := mem_ball_self P.hρ₀
  have hcl : c₀ ∈ closure P.Nm := Work.PARIMPL.Nm_mem_closure d P
  have hne : (𝓝[P.Nm] c₀).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  haveI : (𝓝[P.Nm] c₀).NeBot := hne
  have hlam : Tendsto P.lam (𝓝[P.Nm] c₀) (𝓝 0) := P.tendsto_lam c₀ P.a2₀ hc₀
  have hτ : Tendsto (fun c => P.h c 0) (𝓝[P.Nm] c₀) (𝓝 (P.h c₀ 0)) :=
    ((P.cont_τ.continuousAt (isOpen_ball.mem_nhds hc₀)).tendsto).mono_left inf_le_left
  have himτ : Tendsto (fun c => (P.h c 0).im) (𝓝[P.Nm] c₀) (𝓝 ((P.h c₀ 0).im)) :=
    (Complex.continuous_im.tendsto (P.h c₀ 0)).comp hτ
  have hr_ev : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c < P.r :=
    hlam.eventually (isOpen_Iio.mem_nhds P.hr)
  have hb : ∀ᶠ c in 𝓝[P.Nm] c₀, |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hr_ev] with c hc hcr
    exact him c hc hcr
  have hupper : Tendsto (fun c => P.A * P.lam c ^ 2) (𝓝[P.Nm] c₀) (𝓝 0) := by
    have h2 : Tendsto (fun c => P.lam c ^ 2) (𝓝[P.Nm] c₀) (𝓝 (0 : ℝ)) := by
      simpa using hlam.pow 2
    simpa using h2.const_mul P.A
  have hsqueeze : Tendsto (fun c => |(P.h c 0).im|) (𝓝[P.Nm] c₀) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Filter.Eventually.of_forall (fun c => abs_nonneg _)) hb
  have himτ2 : Tendsto (fun c => |(P.h c 0).im|) (𝓝[P.Nm] c₀) (𝓝 |(P.h c₀ 0).im|) :=
    himτ.abs
  have him0 : |(P.h c₀ 0).im| = 0 := (tendsto_nhds_unique hsqueeze himτ2).symm
  have him_zero : (P.h c₀ 0).im = 0 := abs_eq_zero.mp him0
  have hb₀ := P.bounds c₀ hc₀
  have hnorm : ‖P.h c₀ 0‖ = 1 := hb₀.2.1
  have hclose : ‖P.h c₀ 0 - 1‖ ≤ 1/2 := hb₀.2.2.2.2.2
  have hτre : P.h c₀ 0 = (((P.h c₀ 0).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him_zero]
  have habs : |(P.h c₀ 0).re| = 1 := by
    rw [hτre] at hnorm
    simpa using hnorm
  have hcl2 : |(P.h c₀ 0).re - 1| ≤ 1/2 := by
    have h := Complex.abs_re_le_norm (P.h c₀ 0 - 1)
    rw [Complex.sub_re, Complex.one_re] at h
    linarith
  have hre1 : (P.h c₀ 0).re = 1 := by
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
    · exact h
    · have := (abs_le.mp hcl2).1
      rw [h] at this; norm_num at this
  rw [hτre, hre1]; norm_num

/-- **L0.5 (b).**  `(π/λ_c)·‖τ_c − 1‖ → 0` along `Nm`.  From `‖τ_c‖ = 1` and `|Im τ_c| ≤ Aλ²`
one gets `‖τ_c − 1‖ ≤ |Im τ_c|·(1 + Aλ²)`, so `(π/λ_c)‖τ_c − 1‖ ≤ πAλ_c(1 + Aλ_c²) → 0`. -/
theorem splitPhase_tendsto_tau_phase (P : ParNormal d)
    (him : ∀ c ∈ P.Nm, P.lam c < P.r → |(P.h c 0).im| ≤ P.A * P.lam c ^ 2) :
    Tendsto (fun c => (Real.pi / P.lam c) * ‖P.h c 0 - 1‖) (𝓝[P.Nm] c₀) (𝓝 0) := by
  have hc₀ : c₀ ∈ ball c₀ P.ρ₀ := mem_ball_self P.hρ₀
  have hlam : Tendsto P.lam (𝓝[P.Nm] c₀) (𝓝 0) := P.tendsto_lam c₀ P.a2₀ hc₀
  have hr_ev : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c < P.r := hlam.eventually (isOpen_Iio.mem_nhds P.hr)
  have hpos_ev : ∀ᶠ c in 𝓝[P.Nm] c₀, 0 < P.lam c := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact P.lam_pos_of_mem_Nm hc
  have hb : ∀ᶠ c in 𝓝[P.Nm] c₀, (Real.pi / P.lam c) * ‖P.h c 0 - 1‖
      ≤ Real.pi * P.A * P.lam c * (1 + P.A * P.lam c ^ 2) := by
    filter_upwards [self_mem_nhdsWithin, hr_ev, hpos_ev] with c hc hcr hcp
    have hbc := P.bounds c hc.1
    have hnorm : ‖P.h c 0‖ = 1 := hbc.2.1
    have hclose : ‖P.h c 0 - 1‖ ≤ 1/2 := hbc.2.2.2.2.2
    have himc : |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 := him c hc hcr
    have hkey : ‖P.h c 0 - 1‖ ≤ |(P.h c 0).im| * (1 + P.A * P.lam c ^ 2) := by
      have hre_ge : 1/2 ≤ (P.h c 0).re := by
        have h := Complex.abs_re_le_norm (P.h c 0 - 1)
        rw [Complex.sub_re, Complex.one_re] at h
        have hab := abs_le.mp h
        linarith [hab.1, hclose]
      have hsq : ((P.h c 0).re)^2 + ((P.h c 0).im)^2 = 1 := by
        have h := Complex.normSq_apply (P.h c 0)
        rw [Complex.normSq_eq_norm_sq, hnorm, one_pow] at h
        nlinarith [h]
      have hle : 1 - (P.h c 0).re ≤ ((P.h c 0).im)^2 := by
        nlinarith [hsq, hre_ge, sq_nonneg (P.h c 0).im]
      have hre_le : (P.h c 0).re ≤ 1 := by nlinarith [hsq, hre_ge, sq_nonneg (P.h c 0).im]
      calc ‖P.h c 0 - 1‖ ≤ |(P.h c 0 - 1).re| + |(P.h c 0 - 1).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = |(P.h c 0).re - 1| + |(P.h c 0).im| := by
            simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
        _ = (1 - (P.h c 0).re) + |(P.h c 0).im| := by
            rw [abs_of_nonpos (by linarith), neg_sub]
        _ ≤ ((P.h c 0).im)^2 + |(P.h c 0).im| := by linarith [hle]
        _ = |(P.h c 0).im| * (|(P.h c 0).im| + 1) := by rw [← sq_abs]; ring
        _ ≤ |(P.h c 0).im| * (1 + P.A * P.lam c ^ 2) := by
            nlinarith [abs_nonneg (P.h c 0).im, himc]
    calc (Real.pi / P.lam c) * ‖P.h c 0 - 1‖
        ≤ (Real.pi / P.lam c) * (|(P.h c 0).im| * (1 + P.A * P.lam c ^ 2)) :=
          mul_le_mul_of_nonneg_left hkey (div_nonneg Real.pi_pos.le hcp.le)
      _ ≤ (Real.pi / P.lam c) * (P.A * P.lam c ^ 2 * (1 + P.A * P.lam c ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg Real.pi_pos.le hcp.le)
          exact mul_le_mul_of_nonneg_right himc (by nlinarith [P.hA, sq_nonneg (P.lam c)])
      _ = Real.pi * P.A * P.lam c * (1 + P.A * P.lam c ^ 2) := by
          field_simp
  have hupper : Tendsto (fun c => Real.pi * P.A * P.lam c * (1 + P.A * P.lam c ^ 2))
      (𝓝[P.Nm] c₀) (𝓝 0) := by
    have h2 : Tendsto (fun c => P.lam c ^ 2) (𝓝[P.Nm] c₀) (𝓝 (0 : ℝ)) := by
      simpa using hlam.pow 2
    have hF : Tendsto (fun c => 1 + P.A * P.lam c ^ 2) (𝓝[P.Nm] c₀) (𝓝 1) := by
      simpa using tendsto_const_nhds.add (h2.const_mul P.A)
    have hmul := (hlam.const_mul (Real.pi * P.A)).mul hF
    simpa using hmul
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ hb
  filter_upwards [hpos_ev] with c hcp
  exact mul_nonneg (div_nonneg Real.pi_pos.le hcp.le) (norm_nonneg _)

/-! ## The bundle -/

theorem SplitPhase_normalForm {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d)
    (hswap : ∀ (c p q : ℂ), Work.PARIMPL.gtc c p = q → Work.PARIMPL.gtc c q = p →
      deriv (Work.PARIMPL.Ft c) q = star (deriv (Work.PARIMPL.Ft c) p)) :
    (∀ c ∈ P.Nm, ∀ _hr : P.lam c < P.r, ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
      HasDerivAt (Work.PARIMPL.Ft c) (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c))
        (P.m c + P.s c * (σ * P.a c))) ∧
    (∀ c ∈ P.Nm, ∀ _hr : P.lam c < P.r, P.h c (P.a c) = star (P.h c (-P.a c))) ∧
    (∀ c ∈ P.Nm, ∀ _hr : P.lam c < P.r,
      |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 ∧ |(P.h1 c).im| ≤ P.A * P.lam c) ∧
    P.h c₀ 0 = 1 ∧
    Tendsto (fun c => (Real.pi / P.lam c) * ‖P.h c 0 - 1‖) (𝓝[P.Nm] c₀) (𝓝 0) := by
  have hA : ∀ c ∈ P.Nm, ∀ _hr : P.lam c < P.r, ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
      HasDerivAt (Work.PARIMPL.Ft c) (1 + 2 * (σ * P.a c) * P.h c (σ * P.a c))
        (P.m c + P.s c * (σ * P.a c)) :=
    fun c hc hr σ hσ => splitPhase_hasDerivAt P hc hr σ hσ
  have hB : ∀ c ∈ P.Nm, ∀ _hr : P.lam c < P.r, P.h c (P.a c) = star (P.h c (-P.a c)) :=
    fun c hc hr => splitPhase_h_split_conj P hc hr (hA c hc hr) hswap
  have him : ∀ c ∈ P.Nm, ∀ _hr : P.lam c < P.r,
      |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 ∧ |(P.h1 c).im| ≤ P.A * P.lam c :=
    fun c hc hr => splitPhase_im_bounds P hc hr (hB c hc hr)
  exact ⟨hA, hB, him, splitPhase_tau_c0 P (fun c hc hr => (him c hc hr).1),
    splitPhase_tendsto_tau_phase P (fun c hc hr => (him c hc hr).1)⟩

end

end Work.FlowerGlue2
