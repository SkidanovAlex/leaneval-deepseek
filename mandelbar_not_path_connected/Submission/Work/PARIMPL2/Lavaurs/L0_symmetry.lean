/-
Copyright: subproject `Submission/Work/PARIMPL2/Lavaurs/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.L0_symmetry` — level 0 of chain C

`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.1.  The four normalisation properties of a
parameter normal form `P : ParNormal d` on the **implosion side** `P.Nm = {a₂ < 0}` (where
`a c = i·λ_c`, `λ_c > 0`):

* **L0.3** the germ is conjugate-symmetric at the two repelling fixed points `±a c`,
  `h(a) = conj (h (−a))`;
* **L0.4** the imaginary parts of `τ_c = h c 0` and of `h₁ c` are of order `λ²` resp. `λ`,
  `|Im τ| ≤ A λ²`, `|Im h₁| ≤ A λ`;
* **L0.5** at the root parameter the rotation is trivial, `τ_{c₀} = h c₀ 0 = 1`, and along `Nm`
  the phase `π·‖τ_c − 1‖/λ_c` tends to `0` (i.e. `‖τ_c − 1‖ = o(λ)`).

## The mathematics

* L0.3.  On `Nm` the antiholomorphic square root `g c = (T_c)^[5]` of the second return map
  `Ft c = (T_c)^[10]` **swaps** the two split fixed points `m c ± s c·a c` (`ParNormal.swap`); the
  chart `conj` identity shows that both points are fixed by `Ft c`, and the chain rule for the
  conjugate-differentiable `g` (`Work.PARIMPL.ParSplit.deriv_conj_of_swap`) makes the two
  multipliers conjugate: `1 + 2 a h(a) = conj (1 − 2 a h(−a))`.  Since `conj a = −a ≠ 0`, this is
  `h(a) = conj (h (−a))`.  The multipliers are computed **with continuity of `h` only**: the node
  `ζ² − a²` factors as `(ζ ∓ a)·((ζ ± a)h(ζ))` and the vanishing factor kills the need for
  differentiability of the germ.
* L0.4.  `ParBounds` at `ζ = ±a` gives `h(±a) = τ ± h₁·a + e±` with `‖e±‖ ≤ A λ²`; the symmetry
  of L0.3 turns this into `2i·Im τ − 2λ·Im h₁ = conj e₋ − e₊`, whose imaginary part is
  `|Im τ| ≤ A λ²` and whose real part is `|Im h₁| ≤ A λ` (using `λ > 0`).
* L0.5.  `c₀ ∈ closure P.Nm` (`Work.PARIMPL.Nm_mem_closure`), `λ → 0` along `Nm`
  (`ParNormal.tendsto_lam`) and `τ` is continuous at `c₀` (`cont_τ`) give `Im τ_{c₀} = 0`; with
  `‖τ_{c₀}‖ = 1` and `‖τ_{c₀} − 1‖ ≤ 1/2` this pins `τ_{c₀} = 1`.  Finally `‖τ − 1‖ ≤ √2·|Im τ|`
  whenever `‖τ‖ = 1` and `‖τ − 1‖ ≤ 1/2`, hence `(π/λ)·‖τ − 1‖ ≤ √2πA·λ → 0`.

This lemma is the `hsym`/`him` input of the level-1 estimates of chain C. -/
import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

/-! ## Derivative of the normal form at its two fixed points, with continuity only -/

/-- Derivative of `ζ ↦ (ζ - b) * G ζ` at `b` when `G` is only **continuous** at `b`: the vanishing
factor `ζ - b` kills the differentiability requirement on `G`. -/
theorem hasDerivAt_sub_mul_of_continuousAt {G : ℂ → ℂ} {b : ℂ} (hG : ContinuousAt G b) :
    HasDerivAt (fun ζ : ℂ => (ζ - b) * G ζ) (G b) b := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hG.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
  have hyb : y - b ≠ 0 := sub_ne_zero.mpr hy
  simp only [slope, vsub_eq_sub, smul_eq_mul, sub_self, zero_mul, sub_zero]
  rw [← mul_assoc, inv_mul_cancel₀ hyb, one_mul]

/-- The multiplier of the local normal form `ζ + (ζ² − a²)h(ζ)` at its two fixed points `±a`,
using only the **continuity** of the germ `h` there. -/
theorem hasDerivAt_normalForm_pm {a : ℂ} {h : ℂ → ℂ} (ha : ContinuousAt h a)
    (hna : ContinuousAt h (-a)) :
    HasDerivAt (Work.Implosion.normalForm a h) (1 + 2 * a * h a) a ∧
    HasDerivAt (Work.Implosion.normalForm a h) (1 - 2 * a * h (-a)) (-a) := by
  constructor
  · have h1 : ContinuousAt (fun ζ : ℂ => ζ + a) a := continuousAt_id.add continuousAt_const
    have h2 : ContinuousAt (fun ζ : ℂ => (ζ + a) * h ζ) a := h1.mul ha
    have h3 : ContinuousAt (fun ζ : ℂ => 1 + (ζ + a) * h ζ) a := h2.const_add 1
    have hg := hasDerivAt_sub_mul_of_continuousAt h3
    have hval : (1 + (a + a) * h a : ℂ) = 1 + 2 * a * h a := by ring
    rw [hval] at hg
    have hfun : Work.Implosion.normalForm a h
        = fun ζ : ℂ => a + ((ζ - a) * (1 + (ζ + a) * h ζ)) := by
      funext ζ
      have hsub := Work.Implosion.normalForm_sub_left a h ζ
      linear_combination hsub
    rw [hfun]
    exact hg.const_add a
  · have h1 : ContinuousAt (fun ζ : ℂ => ζ - a) (-a) := continuousAt_id.sub continuousAt_const
    have h2 : ContinuousAt (fun ζ : ℂ => (ζ - a) * h ζ) (-a) := h1.mul hna
    have h3 : ContinuousAt (fun ζ : ℂ => 1 + (ζ - a) * h ζ) (-a) := h2.const_add 1
    have hg := hasDerivAt_sub_mul_of_continuousAt h3
    have hval : (1 + (-a - a) * h (-a) : ℂ) = 1 - 2 * a * h (-a) := by ring
    rw [hval] at hg
    have hfun : Work.Implosion.normalForm a h
        = fun ζ : ℂ => -a + ((ζ - -a) * (1 + (ζ - a) * h ζ)) := by
      funext ζ
      have hadd := Work.Implosion.normalForm_add_left a h ζ
      linear_combination hadd
    rw [hfun]
    exact hg.const_add (-a)

/-- The derivative of a map which is conjugated to a given `g` on the chart ball: if
`F (m + s·ζ) = m + s·g ζ` for `‖ζ‖ < r` and `b` lies in the chart ball, then
`deriv F (m + s·b) = deriv g b`. -/
theorem deriv_eq_of_chart {F : ℂ → ℂ} (hF : Differentiable ℂ F) {m s b : ℂ} (hs : s ≠ 0)
    {r : ℝ} {g : ℂ → ℂ} {g' : ℂ}
    (hid : ∀ ζ ∈ ball (0 : ℂ) r, F (m + s * ζ) = m + s * g ζ)
    (hb : b ∈ ball (0 : ℂ) r) (hg : HasDerivAt g g' b) :
    deriv F (m + s * b) = g' := by
  have heq : (fun ζ : ℂ => F (m + s * ζ)) =ᶠ[𝓝 b] (fun ζ : ℂ => m + s * g ζ) := by
    filter_upwards [isOpen_ball.mem_nhds hb] with ζ hz
    exact hid ζ hz
  have h1 : deriv (fun ζ : ℂ => F (m + s * ζ)) b = deriv (fun ζ : ℂ => m + s * g ζ) b :=
    Filter.EventuallyEq.deriv_eq heq
  have h2 : deriv (fun ζ : ℂ => F (m + s * ζ)) b = deriv F (m + s * b) * s := by
    have hlin : HasDerivAt (fun ζ : ℂ => m + s * ζ) s b := by
      simpa using ((hasDerivAt_id b).const_mul s).const_add m
    exact (HasDerivAt.comp b ((hF (m + s * b)).hasDerivAt) hlin).deriv
  have h3 : deriv (fun ζ : ℂ => m + s * g ζ) b = s * g' := by
    exact ((hg.const_mul s).const_add m).deriv
  rw [h2, h3] at h1
  exact mul_right_cancel₀ hs (h1.trans (mul_comm s g'))

/-! ## L0.3 — the conjugate symmetry of the germ at `±a` -/

/-- **L0.3.**  On the implosion side, at a parameter where the chart contains `±a c`
(`lam c < r`), the germ of the parameter normal form is conjugate-symmetric at the two
repelling fixed points: `h c (a c) = conj (h c (−a c))`. -/
theorem h_split_conj_aux {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d) :
    ∀ c ∈ P.Nm, P.lam c < P.r → P.h c (P.a c) = star (P.h c (-P.a c)) := by
  intro c hc hr
  have hc1 : c ∈ ball c₀ P.ρ₀ := hc.1
  have hc2 : P.a2 c < 0 := hc.2
  have hlam : 0 < P.lam c := P.lam_pos_of_mem_Nm hc
  have ha : P.a c = (P.lam c : ℂ) * Complex.I := P.a_of_mem_Nm hc
  have ha_norm : ‖P.a c‖ = P.lam c := by
    rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlam]
  have hpa : P.a c ∈ ball (0 : ℂ) P.r := by
    rw [mem_ball, dist_zero_right, ha_norm]; exact hr
  have hna : -P.a c ∈ ball (0 : ℂ) P.r := by
    rw [mem_ball, dist_zero_right, norm_neg, ha_norm]; exact hr
  have hmem : (c, P.a c) ∈ ball c₀ P.ρ₀ ×ˢ ball (0 : ℂ) P.r := ⟨hc1, hpa⟩
  have hmem' : (c, -P.a c) ∈ ball c₀ P.ρ₀ ×ˢ ball (0 : ℂ) P.r := ⟨hc1, hna⟩
  have hjoint : ContinuousAt (fun p : ℂ × ℂ => P.h p.1 p.2) (c, P.a c) :=
    P.cont_h.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)
  have hjoint' : ContinuousAt (fun p : ℂ × ℂ => P.h p.1 p.2) (c, -P.a c) :=
    P.cont_h.continuousAt ((isOpen_ball.prod isOpen_ball).mem_nhds hmem')
  have hcont1 : ContinuousAt (fun ζ : ℂ => P.h c ζ) (P.a c) := by
    have h := hjoint.comp (continuousAt_const.prodMk continuousAt_id)
    convert h using 1
    ext ζ; rfl
  have hcont2 : ContinuousAt (fun ζ : ℂ => P.h c ζ) (-P.a c) := by
    have h := hjoint'.comp (continuousAt_const.prodMk continuousAt_id)
    convert h using 1
    ext ζ; rfl
  have hFdiff : Differentiable ℂ (Work.EL.F c) := by
    show Differentiable ℂ ((Work.Landing.Tsq c)^[5])
    exact (by unfold Work.Landing.Tsq; fun_prop : Differentiable ℂ (Work.Landing.Tsq c)).iterate 5
  obtain ⟨hnc, hnc'⟩ := hasDerivAt_normalForm_pm (h := P.h c) hcont1 hcont2
  have hd1 : deriv (Work.EL.F c) (P.m c + P.s c * P.a c)
      = 1 + 2 * P.a c * P.h c (P.a c) :=
    deriv_eq_of_chart hFdiff (P.s_ne c hc1) (fun ζ hz => P.conj c hc1 ζ hz) hpa hnc
  have hd2 : deriv (Work.EL.F c) (P.m c + P.s c * (-P.a c))
      = 1 - 2 * P.a c * P.h c (-P.a c) :=
    deriv_eq_of_chart hFdiff (P.s_ne c hc1) (fun ζ hz => P.conj c hc1 ζ hz) hna hnc'
  have hswap1 : Work.PARIMPL.gtc c (P.m c + P.s c * P.a c) = P.m c + P.s c * (-P.a c) := by
    rw [P.swap c hc1 hc2]; ring
  have hfix1 : Work.PARIMPL.Ft c (P.m c + P.s c * P.a c) = P.m c + P.s c * P.a c := by
    rw [P.conj c hc1 (P.a c) hpa, Work.Implosion.normalForm_fixed_left]
  have hswap2 : Work.PARIMPL.gtc c (P.m c + P.s c * (-P.a c)) = P.m c + P.s c * P.a c := by
    rw [← hswap1]
    show (Work.PARIMPL.gtc c ∘ Work.PARIMPL.gtc c) (P.m c + P.s c * P.a c)
      = P.m c + P.s c * P.a c
    rw [← Work.PARIMPL.Ft_eq_g_comp]
    exact hfix1
  have hdc := Work.PARIMPL.ParSplit.deriv_conj_of_swap hswap1 hswap2
  rw [hd1, hd2] at hdc
  have hstar_a : star (P.a c) = -P.a c := by
    rw [ha]; simp
  have ha_ne : P.a c ≠ 0 := by
    rw [ha]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hne : (2 : ℂ) * P.a c ≠ 0 := mul_ne_zero (by norm_num) ha_ne
  have h2 : (2 : ℂ) * P.a c * P.h c (P.a c) = 2 * P.a c * star (P.h c (-P.a c)) := by
    have h := hdc
    simp only [star_sub, star_mul, star_one, hstar_a, star_ofNat] at h
    linear_combination h
  exact mul_left_cancel₀ hne h2

/-! ## L0.4 — the imaginary parts of `τ` and `h₁` -/

/-- **L0.4.**  From the conjugate symmetry of the germ at `±a` (L0.3) and the uniform bounds of
`ParBounds` at `ζ = ±a`, the imaginary parts of `h c 0 = τ c` and of `h1 c` are of order `λ²` and
`λ`: `|Im τ| ≤ A·λ²` and `|Im h1| ≤ A·λ`. -/
theorem im_tau_le_aux {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d)
    (hsym : ∀ c ∈ P.Nm, P.lam c < P.r → P.h c (P.a c) = star (P.h c (-P.a c))) :
    ∀ c ∈ P.Nm, P.lam c < P.r →
      |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 ∧ |(P.h1 c).im| ≤ P.A * P.lam c := by
  intro c hc hr
  have hc1 : c ∈ ball c₀ P.ρ₀ := hc.1
  have hlam : 0 < P.lam c := P.lam_pos_of_mem_Nm hc
  have ha : P.a c = (P.lam c : ℂ) * Complex.I := P.a_of_mem_Nm hc
  have ha_norm : ‖P.a c‖ = P.lam c := by
    rw [ha, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlam]
  have hstar_a : star (P.a c) = -P.a c := by rw [ha]; simp
  have hbnd := (P.bounds c hc1).2.2.1
  have hep : ‖P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c‖ ≤ P.A * P.lam c ^ 2 := by
    have h := hbnd (P.a c) (by rw [ha_norm]; exact hr)
    rwa [ha_norm] at h
  have hem : ‖P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c)‖ ≤ P.A * P.lam c ^ 2 := by
    have h := hbnd (-P.a c) (by rw [norm_neg, ha_norm]; exact hr)
    rw [norm_neg, ha_norm] at h
    exact h
  have hnorm : ‖star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
      - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)‖ ≤ 2 * (P.A * P.lam c ^ 2) := by
    calc ‖star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
          - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)‖
        ≤ ‖star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))‖
          + ‖P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c‖ := norm_sub_le _ _
      _ = ‖P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c)‖
          + ‖P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c‖ := by rw [norm_star]
      _ ≤ P.A * P.lam c ^ 2 + P.A * P.lam c ^ 2 := add_le_add hem hep
      _ = 2 * (P.A * P.lam c ^ 2) := by ring
  have hs := hsym c hc hr
  have hsub : star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
      - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)
      = (P.h c 0 - star (P.h c 0)) + (P.h1 c - star (P.h1 c)) * P.a c := by
    rw [hs]
    simp only [star_sub, star_mul, star_neg, hstar_a, neg_neg]
    ring
  have hIm0 : (P.h c 0 - star (P.h c 0)).im = 2 * (P.h c 0).im := by
    simp only [Complex.star_def, Complex.sub_im, Complex.conj_im]; ring
  have hRe0 : (P.h c 0 - star (P.h c 0)).re = 0 := by
    simp only [Complex.star_def, Complex.sub_re, Complex.conj_re]; ring
  have hIm1 : (P.h1 c - star (P.h1 c)).im = 2 * (P.h1 c).im := by
    simp only [Complex.star_def, Complex.sub_im, Complex.conj_im]; ring
  have hRe1 : (P.h1 c - star (P.h1 c)).re = 0 := by
    simp only [Complex.star_def, Complex.sub_re, Complex.conj_re]; ring
  have him : (star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
      - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)).im = 2 * (P.h c 0).im := by
    rw [hsub, Complex.add_im, Complex.mul_im, hRe1, hIm1, ha, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hIm0]
    ring
  have hre : (star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
      - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)).re
      = -(2 * P.lam c * (P.h1 c).im) := by
    rw [hsub, Complex.add_re, Complex.mul_re, hRe1, hIm1, ha, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hRe0]
    ring
  constructor
  · have h1 : |2 * (P.h c 0).im| ≤ 2 * (P.A * P.lam c ^ 2) := by
      calc |2 * (P.h c 0).im|
          = |(star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
              - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)).im| := by rw [him]
        _ ≤ ‖star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
              - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)‖ := Complex.abs_im_le_norm _
        _ ≤ 2 * (P.A * P.lam c ^ 2) := hnorm
    rw [abs_mul] at h1
    simp only [abs_two] at h1
    linarith
  · have h1 : |2 * P.lam c * (P.h1 c).im| ≤ 2 * (P.A * P.lam c ^ 2) := by
      calc |2 * P.lam c * (P.h1 c).im|
          = |-(2 * P.lam c * (P.h1 c).im)| := by rw [abs_neg]
        _ = |(star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
              - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)).re| := by rw [hre]
        _ ≤ ‖star (P.h c (-P.a c) - P.h c 0 - P.h1 c * (-P.a c))
              - (P.h c (P.a c) - P.h c 0 - P.h1 c * P.a c)‖ := Complex.abs_re_le_norm _
        _ ≤ 2 * (P.A * P.lam c ^ 2) := hnorm
    rw [abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
    have h2 : 2 * P.lam c * |(P.h1 c).im| ≤ 2 * P.lam c * (P.A * P.lam c) := by
      calc 2 * P.lam c * |(P.h1 c).im| ≤ 2 * (P.A * P.lam c ^ 2) := h1
        _ = 2 * P.lam c * (P.A * P.lam c) := by ring
    exact le_of_mul_le_mul_left h2 (by linarith)

/-! ## L0.5 — the rotation at the root parameter and its phase -/

/-- If `‖z‖ = 1`, `‖z − 1‖ ≤ 1/2` and `|Im z| ≤ t`, then `‖z − 1‖ ≤ √2·t`: the second hypothesis
gives `Re z ≥ 1/2`, hence `(Re z − 1)² ≤ (Im z)²` and `‖z − 1‖² = (Re z − 1)² + (Im z)² ≤ 2t²`. -/
theorem norm_sub_one_le_sqrt_two {z : ℂ} (hz : ‖z‖ = 1) (hz2 : ‖z - 1‖ ≤ 1/2) {t : ℝ}
    (ht : |z.im| ≤ t) : ‖z - 1‖ ≤ Real.sqrt 2 * t := by
  have hu : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have h4 : Complex.normSq (z - 1) ≤ 1/4 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz2, norm_nonneg (z - 1)]
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at h4
  simp only [Complex.one_re, Complex.one_im, sub_zero] at h4
  have hv : (z.re - 1) * (z.re - 1) + z.im * z.im ≤ 1/4 := h4
  have hu1 : 1/2 ≤ z.re := by
    have hsq : (z.re - 1) ^ 2 ≤ (1/2 : ℝ) ^ 2 := by nlinarith [hv]
    have h : |z.re - 1| ≤ 1/2 := by simpa using (sq_le_sq.mp hsq)
    linarith [(abs_le.mp h).1]
  have hu2 : z.re ≤ 1 := by
    have hsq : z.re ^ 2 ≤ (1 : ℝ) ^ 2 := by nlinarith [hu, sq_nonneg z.im]
    have h : |z.re| ≤ 1 := by simpa using (sq_le_sq.mp hsq)
    linarith [(abs_le.mp h).2]
  have hkey : (z.re - 1) * (z.re - 1) ≤ z.im * z.im := by
    have hfac : 2 * z.re * (z.re - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith [hu, hfac]
  have hnorm : ‖z - 1‖ ^ 2 = (z.re - 1) * (z.re - 1) + z.im * z.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
  have ht2 : z.im ^ 2 ≤ t ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  have hsq : ‖z - 1‖ ^ 2 ≤ (Real.sqrt 2 * t) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hnorm]
    nlinarith [hkey, ht2]
  calc ‖z - 1‖ = |‖z - 1‖| := (abs_of_nonneg (norm_nonneg _)).symm
    _ ≤ |Real.sqrt 2 * t| := sq_le_sq.mp hsq
    _ = Real.sqrt 2 * t :=
        abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_trans (abs_nonneg _) ht))

/-- **L0.5.**  At the root parameter the rotation constant is trivial, `h c₀ 0 = 1`, and the phase
`π·‖h c 0 − 1‖/λ` vanishes along the implosion side:
`(Real.pi / P.lam c) * ‖P.h c 0 - 1‖ → 0` in `𝓝[P.Nm] c₀`. -/
theorem tau_phase_aux {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d)
    (him : ∀ c ∈ P.Nm, P.lam c < P.r → |(P.h c 0).im| ≤ P.A * P.lam c ^ 2) :
    P.h c₀ 0 = 1 ∧
    Filter.Tendsto (fun c => (Real.pi / P.lam c) * ‖P.h c 0 - 1‖)
      (nhdsWithin c₀ P.Nm) (nhds 0) := by
  have hc0 : c₀ ∈ ball c₀ P.ρ₀ := by simpa using P.hρ₀
  have hneBot : (𝓝[P.Nm] c₀).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (Work.PARIMPL.Nm_mem_closure d P)
  have hlamlim : Tendsto P.lam (𝓝[P.Nm] c₀) (𝓝 0) := P.tendsto_lam c₀ P.a2₀ hc0
  have hsmall : ∀ᶠ c in 𝓝[P.Nm] c₀, P.lam c < P.r := hlamlim.eventually (Iio_mem_nhds P.hr)
  have hcont : Tendsto (fun c => (P.h c 0).im) (𝓝[P.Nm] c₀) (𝓝 ((P.h c₀ 0).im)) := by
    have h0 : ContinuousAt (fun c : ℂ => P.h c 0) c₀ :=
      P.cont_τ.continuousAt (isOpen_ball.mem_nhds hc0)
    exact ((Complex.continuous_im.continuousAt.comp h0).tendsto).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun c => (P.h c 0).im) (𝓝[P.Nm] c₀) (𝓝 0) := by
    have hg : Tendsto (fun c => P.A * P.lam c ^ 2) (𝓝[P.Nm] c₀) (𝓝 0) := by
      have h := (hlamlim.pow 2).const_mul P.A
      simpa using h
    have h1 : ∀ᶠ c in 𝓝[P.Nm] c₀, 0 ≤ |(P.h c 0).im| :=
      Eventually.of_forall fun c => abs_nonneg _
    have h2 : ∀ᶠ c in 𝓝[P.Nm] c₀, |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with c hc hlt
      exact him c hc hlt
    have h3 := squeeze_zero' h1 h2 hg
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using h3
  have him0 : (P.h c₀ 0).im = 0 := by
    haveI : (𝓝[P.Nm] c₀).NeBot := hneBot
    exact tendsto_nhds_unique hcont hzero
  have hb := P.bounds c₀ hc0
  have hz1 : ‖P.h c₀ 0‖ = 1 := hb.2.1
  have hz2 : ‖P.h c₀ 0 - 1‖ ≤ 1/2 := hb.2.2.2.2.2
  have hzreal : P.h c₀ 0 = (((P.h c₀ 0).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him0
  have hre_abs : |(P.h c₀ 0).re| = 1 := by
    have h := hz1
    rw [hzreal, Complex.norm_real] at h
    exact h
  have hre_near : |(P.h c₀ 0).re - 1| ≤ 1/2 := by
    have h := hz2
    rw [hzreal] at h
    have hcast : ((P.h c₀ 0).re : ℂ) - 1 = (((P.h c₀ 0).re - 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real] at h
    exact h
  have hre_one : (P.h c₀ 0).re = 1 := by
    have hsq : (P.h c₀ 0).re ^ 2 = 1 := by
      rw [← sq_abs, hre_abs]; norm_num
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · have := (abs_le.mp hre_near).1; linarith
  have hz_one : P.h c₀ 0 = 1 := by
    rw [hzreal, hre_one]; norm_num
  refine ⟨hz_one, ?_⟩
  have hglim : Tendsto (fun c => Real.sqrt 2 * Real.pi * P.A * P.lam c)
      (𝓝[P.Nm] c₀) (𝓝 0) := by
    have h := hlamlim.const_mul (Real.sqrt 2 * Real.pi * P.A)
    simpa using h
  have hgcongr : (fun c => (Real.pi / P.lam c) * (Real.sqrt 2 * (P.A * P.lam c ^ 2)))
      =ᶠ[𝓝[P.Nm] c₀] (fun c => Real.sqrt 2 * Real.pi * P.A * P.lam c) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hne : P.lam c ≠ 0 := ne_of_gt (P.lam_pos_of_mem_Nm hc)
    field_simp
  have hgtend : Tendsto (fun c => (Real.pi / P.lam c) * (Real.sqrt 2 * (P.A * P.lam c ^ 2)))
      (𝓝[P.Nm] c₀) (𝓝 0) := Filter.Tendsto.congr' hgcongr.symm hglim
  have h1 : ∀ᶠ c in 𝓝[P.Nm] c₀, 0 ≤ (Real.pi / P.lam c) * ‖P.h c 0 - 1‖ := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact mul_nonneg (div_nonneg Real.pi_pos.le (le_of_lt (P.lam_pos_of_mem_Nm hc)))
      (norm_nonneg _)
  have h2 : ∀ᶠ c in 𝓝[P.Nm] c₀,
      (Real.pi / P.lam c) * ‖P.h c 0 - 1‖
        ≤ (Real.pi / P.lam c) * (Real.sqrt 2 * (P.A * P.lam c ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with c hc hlt
    exact mul_le_mul_of_nonneg_left
      (norm_sub_one_le_sqrt_two (P.bounds c hc.1).2.1 (P.bounds c hc.1).2.2.2.2.2
        (him c hc hlt))
      (div_nonneg Real.pi_pos.le (le_of_lt (P.lam_pos_of_mem_Nm hc)))
  exact squeeze_zero' h1 h2 hgtend

/-! ## L0 — the four properties together -/

/-- **L0 (chain C, `NOTES_LEAD_mandelbar_implosion.md` §3.1).**  On the implosion side `Nm` of a
parameter normal form `P` of a root-parabolic parameter:

1. the germ is conjugate-symmetric at the two repelling fixed points `±a c` (L0.3);
2. the imaginary parts of `τ_c = h c 0` and of `h₁ c` are `O(λ²)` resp. `O(λ)` (L0.4);
3. at the root parameter `τ_{c₀} = h c₀ 0 = 1` and `π‖τ_c − 1‖/λ_c → 0` along `Nm ∋ c → c₀`
   (L0.5). -/
theorem L0_symmetry {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) (P : Work.PARIMPL.ParNormal d) :
    (∀ c ∈ P.Nm, P.lam c < P.r → P.h c (P.a c) = star (P.h c (-P.a c))) ∧
    (∀ c ∈ P.Nm, P.lam c < P.r →
      |(P.h c 0).im| ≤ P.A * P.lam c ^ 2 ∧ |(P.h1 c).im| ≤ P.A * P.lam c) ∧
    P.h c₀ 0 = 1 ∧
    Filter.Tendsto (fun c => (Real.pi / P.lam c) * ‖P.h c 0 - 1‖) (nhdsWithin c₀ P.Nm) (nhds 0) := by
  have hsym := h_split_conj_aux d P
  have him := im_tau_le_aux d P hsym
  obtain ⟨hz, hlim⟩ := tau_phase_aux d P (fun c hc hr => (him c hc hr).1)
  exact ⟨hsym, him, hz, hlim⟩

end Work.PARIMPL2.Lavaurs

end
