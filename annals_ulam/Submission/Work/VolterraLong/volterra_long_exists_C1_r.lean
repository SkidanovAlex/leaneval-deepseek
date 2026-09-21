import Mathlib
import Submission.Work.VolterraLong.volterra_long_exists_C1
import Submission.Work.OddCurveB.Engine.volterra_long_exists_ball

/-!
# `C¹` long-interval existence on a state ball of radius `r ≤ 1`

`Work.VolterraLong.volterra_long_exists_C1_r` is `Work.VolterraLong.volterra_long_exists_C1`
with every state-ball hypothesis (`hΘ_lip`, `hdiff`, `hGs_lip`, `hΘs_lip`, and the `ε`-closeness
hypotheses) taken on `Metric.closedBall (Z₀ s) r` for a fixed `r ∈ (0,1]` instead of the unit ball,
and with the `z`-derivative closeness of `G` to the linearisation `A` supplied in the `ε`-form

  `‖fderiv ℝ (fun w => G s w) z - A s‖ ≤ Cg * ‖z - Z₀ s‖ + ε`.

Both features are needed by the odd Ulam data, where the unit ball around the base state contains
states at which `z ↦ Godd n h s z` fails to be differentiable (see
`Submission/Work/OddCurveB/Engine/README.md`), while a smaller ball and a derivative bound with an
additive `ε` are available.

The proof reuses, rather than redoes, the radius-`1` `C¹` engine:

* existence on the radius-`r` ball is `Work.OddCurveB.Engine.volterra_long_exists_ball` (itself a
  dilation corollary of the radius-`1` fixed point, see
  `Submission/Work/OddCurveB/Engine/volterra_long_exists_ball.lean`); it needs differentiability of
  the base datum `G₀` at `Z₀`, which is extracted from `hA_spec` (an invertible `fderiv` forces
  differentiability) by `differentiableAt_of_fderiv_eq_equiv`;
* the derivative `V` of the solution is obtained from the linearised equation by
  `C1.solve_near_equiv`, whose constant here is `κ = (Cg * K1 + 1) * ε` because the derivative
  hypothesis carries the additive `ε`;
* the linearised datum is compared with the base datum by the radius-`r` version
  `data_diff_bound_r` of `C1.data_diff_bound`;
* the pointwise differentiability of the solution, with derivative `V`, is
  `deriv_from_solution_linearized`, the pointwise form of `deriv_from_equation_aux`;
* the solution is finally extended off `[a,b]` by `exists_extension_hasDerivAt`.
-/

noncomputable section

open Set Filter MeasureTheory
open Work.VolterraLong.C1
open scoped Topology Interval

namespace Work.VolterraLong

/-- If the `fderiv` of `f` at `x` is (the coercion of) an invertible continuous linear map, then
`f` is differentiable at `x` (`fderiv` is `0` at non-differentiable points, and an invertible
operator vanishes only on the zero space, where every function is differentiable). -/
lemma differentiableAt_of_fderiv_eq_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x : E} {e : E ≃L[ℝ] E}
    (h : fderiv ℝ f x = (e : E →L[ℝ] E)) : DifferentiableAt ℝ f x := by
  rcases subsingleton_or_nontrivial E with hs | hn
  · have hconst : f = fun _ => f x :=
      funext fun y => congrArg f (@Subsingleton.elim E hs y x)
    rw [hconst]
    exact differentiableAt_const (f x)
  · by_contra hnd
    have h0 : fderiv ℝ f x = 0 := fderiv_zero_of_not_differentiableAt hnd
    have he0 : (e : E →L[ℝ] E) = 0 := by rw [← h, h0]
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have h1 : (e : E →L[ℝ] E) (e.symm v) = v := e.apply_symm_apply v
    rw [he0, zero_apply] at h1
    exact hv h1.symm

theorem data_diff_bound_r {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r)
    {G0s Gs : ℝ → E → E} {Θ0 Θ0s Θ Θs : ℝ → ℝ → E → E} {Ξ0s Ξs : ℝ → E}
    {Z₀ Z : ℝ → E} {L LG L1 K1 ε : ℝ} (hε : 0 < ε) (hK1 : 0 ≤ K1)
    (hL : 0 ≤ L) (hLG : 0 ≤ LG) (hL1 : 0 ≤ L1)
    (hZ : ∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε) (hK1r : K1 * ε ≤ r)
    (hZ_cont : ContinuousOn Z (Set.Icc a b)) (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hΘs_cont : Continuous (fun p : ℝ × ℝ × E => Θs p.1 p.2.1 p.2.2))
    (hΘ0s_cont : Continuous (fun p : ℝ × ℝ × E => Θ0s p.1 p.2.1 p.2.2))
    (hGs_lip : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) r,
      ∀ z' ∈ Metric.closedBall (Z₀ s) r, ‖Gs s z - Gs s z'‖ ≤ LG * ‖z - z'‖)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) r,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) r, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hΘs_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) r,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) r, ‖Θs s σ z - Θs s σ z'‖ ≤ L1 * ‖z - z'‖)
    (hGs_c : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) r, dist (Gs s z) (G0s s z) < ε)
    (hΘ_c : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) r,
      dist (Θ s σ z) (Θ0 s σ z) < ε)
    (hΘs_c : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) r,
      dist (Θs s σ z) (Θ0s s σ z) < ε)
    (hΞs_c : ∀ s ∈ Set.Icc a b, dist (Ξs s) (Ξ0s s) < ε) :
    ∀ s ∈ Set.Icc a b, ‖(- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      - (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)‖
      ≤ ((1 + LG * K1) + (1 + L * K1) + (b - a + 1) * (1 + L1 * K1) + 1) * ε := by
  intro s hs
  have hsa : a ≤ s := hs.1
  have hsb : s ≤ b := hs.2
  -- ### distance facts from the perturbation hypothesis
  have hZ1 : ∀ σ ∈ Set.Icc a b, dist (Z σ) (Z₀ σ) ≤ r := by
    intro σ hσ
    have h := hZ σ hσ
    linarith
  have hZmem : ∀ σ ∈ Set.Icc a b, Z σ ∈ Metric.closedBall (Z₀ σ) r :=
    fun σ hσ => Metric.mem_closedBall.mpr (hZ1 σ hσ)
  have hZ₀mem : ∀ σ ∈ Set.Icc a b, Z₀ σ ∈ Metric.closedBall (Z₀ σ) r :=
    fun σ hσ => Metric.mem_closedBall.mpr (by rw [dist_self]; exact hr.le)
  have hZnorm : ∀ σ ∈ Set.Icc a b, ‖Z σ - Z₀ σ‖ ≤ K1 * ε := by
    intro σ hσ
    have h := hZ σ hσ
    rwa [dist_eq_norm] at h
  -- ### the smallness of each of the four differences
  have hG : ‖Gs s (Z s) - G0s s (Z₀ s)‖ ≤ (1 + LG * K1) * ε := by
    have hlip := hGs_lip s hs (Z s) (hZmem s hs) (Z₀ s) (hZ₀mem s hs)
    have hcl := hGs_c s hs (Z₀ s) (hZ₀mem s hs)
    rw [dist_eq_norm] at hcl
    have h2 : LG * ‖Z s - Z₀ s‖ ≤ LG * (K1 * ε) :=
      mul_le_mul_of_nonneg_left (hZnorm s hs) hLG
    have h1 : ‖Gs s (Z s) - G0s s (Z₀ s)‖ ≤ LG * ‖Z s - Z₀ s‖ + ε := by
      have ht := dist_triangle (Gs s (Z s)) (Gs s (Z₀ s)) (G0s s (Z₀ s))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      linarith
    have h3 : LG * (K1 * ε) + ε = (1 + LG * K1) * ε := by ring
    linarith
  have hΘb : ‖Θ s s (Z s) - Θ0 s s (Z₀ s)‖ ≤ (1 + L * K1) * ε := by
    have hlip := hΘ_lip s hs s hs (Z s) (hZmem s hs) (Z₀ s) (hZ₀mem s hs)
    have hcl := hΘ_c s hs s hs (Z₀ s) (hZ₀mem s hs)
    rw [dist_eq_norm] at hcl
    have h2 : L * ‖Z s - Z₀ s‖ ≤ L * (K1 * ε) :=
      mul_le_mul_of_nonneg_left (hZnorm s hs) hL
    have h1 : ‖Θ s s (Z s) - Θ0 s s (Z₀ s)‖ ≤ L * ‖Z s - Z₀ s‖ + ε := by
      have ht := dist_triangle (Θ s s (Z s)) (Θ s s (Z₀ s)) (Θ0 s s (Z₀ s))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      linarith
    have h3 : L * (K1 * ε) + ε = (1 + L * K1) * ε := by ring
    linarith
  have hΞb : ‖Ξs s - Ξ0s s‖ ≤ 1 * ε := by
    have h := hΞs_c s hs
    rw [dist_eq_norm] at h
    linarith
  -- ### pointwise bound for the integrand
  have hpoint : ∀ x ∈ Set.Icc s b,
      ‖Θs s x (Z x) - Θ0s s x (Z₀ x)‖ ≤ (1 + L1 * K1) * ε := by
    intro x hx
    have hxab : x ∈ Set.Icc a b := ⟨hsa.trans hx.1, hx.2⟩
    have hlip := hΘs_lip s hs x hxab (Z x) (hZmem x hxab) (Z₀ x) (hZ₀mem x hxab)
    have hcl := hΘs_c s hs x hxab (Z₀ x) (hZ₀mem x hxab)
    rw [dist_eq_norm] at hcl
    have h2 : L1 * ‖Z x - Z₀ x‖ ≤ L1 * (K1 * ε) :=
      mul_le_mul_of_nonneg_left (hZnorm x hxab) hL1
    have h1 : ‖Θs s x (Z x) - Θ0s s x (Z₀ x)‖ ≤ L1 * ‖Z x - Z₀ x‖ + ε := by
      have ht := dist_triangle (Θs s x (Z x)) (Θs s x (Z₀ x)) (Θ0s s x (Z₀ x))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      linarith
    have h3 : L1 * (K1 * ε) + ε = (1 + L1 * K1) * ε := by ring
    linarith
  -- ### continuity / integrability of the two integral kernels
  have hmapsZ : ContinuousOn (fun σ : ℝ => (s, σ, Z σ)) (Set.Icc s b) :=
    ContinuousOn.prodMk continuousOn_const
      (ContinuousOn.prodMk continuousOn_id
        (hZ_cont.mono (fun x hx => ⟨hsa.trans hx.1, hx.2⟩)))
  have hmapsZ₀ : ContinuousOn (fun σ : ℝ => (s, σ, Z₀ σ)) (Set.Icc s b) :=
    ContinuousOn.prodMk continuousOn_const
      (ContinuousOn.prodMk continuousOn_id
        (hZ₀_cont.mono (fun x hx => ⟨hsa.trans hx.1, hx.2⟩)))
  have hFcont : ContinuousOn (fun σ : ℝ => Θs s σ (Z σ)) (Set.Icc s b) :=
    hΘs_cont.continuousOn.comp hmapsZ (fun _ _ => Set.mem_univ _)
  have hF0cont : ContinuousOn (fun σ : ℝ => Θ0s s σ (Z₀ σ)) (Set.Icc s b) :=
    hΘ0s_cont.continuousOn.comp hmapsZ₀ (fun _ _ => Set.mem_univ _)
  have hFint : IntervalIntegrable (fun σ : ℝ => Θs s σ (Z σ)) MeasureTheory.volume s b :=
    hFcont.intervalIntegrable_of_Icc hsb
  have hF0int : IntervalIntegrable (fun σ : ℝ => Θ0s s σ (Z₀ σ)) MeasureTheory.volume s b :=
    hF0cont.intervalIntegrable_of_Icc hsb
  -- ### bound for the difference of the two integrals
  have hint : ‖(∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ))‖
      ≤ (b - a + 1) * (1 + L1 * K1) * ε := by
    rw [← intervalIntegral.integral_sub hFint hF0int]
    have hbound : ∀ x ∈ Set.uIoc s b, ‖Θs s x (Z x) - Θ0s s x (Z₀ x)‖ ≤ (1 + L1 * K1) * ε := by
      intro x hx
      rw [Set.uIoc_of_le hsb] at hx
      exact hpoint x (Set.Ioc_subset_Icc_self hx)
    have hni := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := b)
      (C := (1 + L1 * K1) * ε) hbound
    have habs : |b - s| = b - s := abs_of_nonneg (by linarith)
    rw [habs] at hni
    have hC : 0 ≤ (1 + L1 * K1) * ε := mul_nonneg (by linarith [hL1, hK1, mul_nonneg hL1 hK1]) (le_of_lt hε)
    have hbs : b - s ≤ b - a + 1 := by linarith
    have hmono := mul_le_mul_of_nonneg_left hbs hC
    have heq : ((1 + L1 * K1) * ε) * (b - a + 1) = (b - a + 1) * (1 + L1 * K1) * ε := by ring
    linarith
  have hb1 : ‖-(Gs s (Z s) - G0s s (Z₀ s))‖ ≤ (1 + LG * K1) * ε := by
    rw [norm_neg]; exact hG
  have hb2 : ‖-(Θ s s (Z s) - Θ0 s s (Z₀ s))‖ ≤ (1 + L * K1) * ε := by
    rw [norm_neg]; exact hΘb
  -- ### the four-term triangle inequality
  have htri : ∀ u1 u2 u3 u4 : E, ‖u1 + u2 + u3 + u4‖ ≤ ‖u1‖ + ‖u2‖ + ‖u3‖ + ‖u4‖ := by
    intro u1 u2 u3 u4
    have h1 : ‖u1 + u2 + u3 + u4‖ ≤ ‖u1 + u2 + u3‖ + ‖u4‖ := norm_add_le _ _
    have h2 : ‖u1 + u2 + u3‖ ≤ ‖u1 + u2‖ + ‖u3‖ := norm_add_le _ _
    have h3 : ‖u1 + u2‖ ≤ ‖u1‖ + ‖u2‖ := norm_add_le _ _
    linarith
  have htri_inst :
      ‖-(Gs s (Z s) - G0s s (Z₀ s)) + (-(Θ s s (Z s) - Θ0 s s (Z₀ s)))
        + ((∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ)))
        + (Ξs s - Ξ0s s)‖
      ≤ ‖-(Gs s (Z s) - G0s s (Z₀ s))‖ + ‖-(Θ s s (Z s) - Θ0 s s (Z₀ s))‖
        + ‖(∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ))‖
        + ‖Ξs s - Ξ0s s‖ :=
    htri (-(Gs s (Z s) - G0s s (Z₀ s))) (-(Θ s s (Z s) - Θ0 s s (Z₀ s)))
      ((∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ))) (Ξs s - Ξ0s s)
  have key : (- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      - (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)
      = -(Gs s (Z s) - G0s s (Z₀ s)) + (-(Θ s s (Z s) - Θ0 s s (Z₀ s)))
        + ((∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ)))
        + (Ξs s - Ξ0s s) := by abel
  rw [key]
  calc ‖-(Gs s (Z s) - G0s s (Z₀ s)) + (-(Θ s s (Z s) - Θ0 s s (Z₀ s)))
        + ((∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ)))
        + (Ξs s - Ξ0s s)‖
      ≤ ‖-(Gs s (Z s) - G0s s (Z₀ s))‖ + ‖-(Θ s s (Z s) - Θ0 s s (Z₀ s))‖
        + ‖(∫ σ in s..b, Θs s σ (Z σ)) - (∫ σ in s..b, Θ0s s σ (Z₀ σ))‖
        + ‖Ξs s - Ξ0s s‖ := htri_inst
    _ ≤ (1 + LG * K1) * ε + (1 + L * K1) * ε + (b - a + 1) * (1 + L1 * K1) * ε + 1 * ε := by
        linarith [hb1, hb2, hint, hΞb]
    _ = ((1 + LG * K1) + (1 + L * K1) + (b - a + 1) * (1 + L1 * K1) + 1) * ε := by ring



lemma deriv_from_solution_linearized {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → E → E} {Θ : ℝ → ℝ → E → E} {Ξ : ℝ → E} {Gs : ℝ → E → E}
    {Θs : ℝ → ℝ → E → E} {Ξs : ℝ → E} {Z V : ℝ → E} {A : ℝ → E ≃L[ℝ] E}
    {B κ : ℝ} (hB : 0 < B)
    (hAinv : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hZ : ContinuousOn Z (Set.Icc a b))
    (hκB : B * κ ≤ 1 / 2)
    (hsol : ∀ s ∈ Set.Icc a b, G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s)
    (hG : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ : Continuous Ξ)
    (hGs : ∀ s ∈ Set.Icc a b, ∀ z : E, HasDerivAt (fun u : ℝ => G u z) (Gs s z) s)
    (hGs_cont : Continuous (fun p : ℝ × E => Gs p.1 p.2))
    (hΘs : ∀ s ∈ Set.Icc a b, ∀ σ : ℝ, ∀ z : E, HasDerivAt (fun u : ℝ => Θ u σ z) (Θs s σ z) s)
    (hΘs_cont : Continuous (fun p : ℝ × ℝ × E => Θs p.1 p.2.1 p.2.2))
    (hΞs : ∀ s : ℝ, HasDerivAt Ξ (Ξs s) s) (hΞs_cont : Continuous Ξs)
    (hdiffZ : ∀ s ∈ Set.Icc a b, DifferentiableAt ℝ (fun w => G s w) (Z s))
    (hJκ : ∀ s ∈ Set.Icc a b,
      ‖fderiv ℝ (fun w => G s w) (Z s) - (A s : E →L[ℝ] E)‖ ≤ κ)
    (hV : ∀ s ∈ Set.Icc a b, fderiv ℝ (fun w => G s w) (Z s) (V s)
      = - Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s) :
    ∀ s ∈ Set.Icc a b, HasDerivWithinAt Z (V s) (Set.Icc a b) s := by
  intro s hs
  set J : E →L[ℝ] E := fderiv ℝ (fun w => G s w) (Z s) with hJdef
  set A₀ : E →L[ℝ] E := (A s : E →L[ℝ] E) with hA₀def
  have hJ : HasFDerivAt (fun w => G s w) J (Z s) := by
    rw [hJdef]; exact (hdiffZ s hs).hasFDerivAt
  have hlittle : (fun x => G s x - G s (Z s) - J (x - Z s)) =o[𝓝 (Z s)]
      (fun x => x - Z s) := hJ.isLittleO
  have hJA : ‖J - A₀‖ ≤ κ := by
    rw [hJdef, hA₀def]
    exact hJκ s hs
  -- the filter
  have hl_le : 𝓝[Set.Icc a b \ {s}] s ≤ 𝓝[{s}ᶜ] s :=
    nhdsWithin_mono s (fun x hx => hx.2)
  have hl_nhds : 𝓝[Set.Icc a b \ {s}] s ≤ 𝓝 s := le_trans hl_le nhdsWithin_le_nhds
  have hl_Icc : 𝓝[Set.Icc a b \ {s}] s ≤ 𝓝[Set.Icc a b] s :=
    nhdsWithin_mono s (fun x hx => hx.1)
  have hZtend : Tendsto Z (𝓝[Set.Icc a b \ {s}] s) (𝓝 (Z s)) :=
    (hZ.continuousWithinAt hs).tendsto.mono_left hl_Icc
  -- ## continuity helpers
  have huIcc_sub : ∀ {u : ℝ}, u ∈ Set.Icc a b → Set.uIcc s u ⊆ Set.Icc a b := by
    intro u hu
    have hs' : s ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hs
    have hu' : u ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hu
    have h := Set.uIcc_subset_uIcc hs' hu'
    rwa [Set.uIcc_of_le hab] at h
  have hcont_Θ_Z : ∀ (u : ℝ), u ∈ Set.Icc a b →
      ContinuousOn (fun σ : ℝ => Θ u σ (Z σ)) (Set.uIcc s u) := by
    intro u hu
    have h1 : ContinuousOn (fun σ : ℝ => (u, σ, Z σ)) (Set.uIcc s u) := by
      refine continuousOn_const.prodMk (continuousOn_id.prodMk ?_)
      exact hZ.comp continuousOn_id (fun σ hσ => huIcc_sub hu hσ)
    exact hΘ.comp_continuousOn h1
  have hcont_Θ_Icc : ∀ (u : ℝ), u ∈ Set.Icc a b →
      ContinuousOn (fun σ : ℝ => Θ u σ (Z σ)) (Set.Icc s b) := by
    intro u hu
    have h1 : ContinuousOn (fun σ : ℝ => (u, σ, Z σ)) (Set.Icc a b) := by
      refine continuousOn_const.prodMk (continuousOn_id.prodMk ?_)
      exact hZ.comp continuousOn_id (fun σ hσ => hσ)
    exact (hΘ.comp_continuousOn h1).mono (show Set.Icc s b ⊆ Set.Icc a b from
      Set.Icc_subset_Icc hs.1 (le_refl b))
  have hcont_Θs_Icc : ContinuousOn (fun σ : ℝ => Θs s σ (Z σ)) (Set.Icc s b) := by
    have h1 : ContinuousOn (fun σ : ℝ => (s, σ, Z σ)) (Set.Icc a b) := by
      refine continuousOn_const.prodMk (continuousOn_id.prodMk ?_)
      exact hZ.comp continuousOn_id (fun σ hσ => hσ)
    exact (hΘs_cont.comp_continuousOn h1).mono (show Set.Icc s b ⊆ Set.Icc a b from
      Set.Icc_subset_Icc hs.1 (le_refl b))
  have hcont_tuple_box : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2, Z p.2))
      (Set.Icc a b ×ˢ Set.Icc s b) := by
    refine continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk ?_)
    exact hZ.comp continuous_snd.continuousOn (fun p hp => ⟨le_trans hs.1 hp.2.1, hp.2.2⟩)
  have hcont_Θ_box : ContinuousOn (fun p : ℝ × ℝ => Θ p.1 p.2 (Z p.2))
      (Set.Icc a b ×ˢ Set.Icc s b) := hΘ.comp_continuousOn hcont_tuple_box
  have hcont_Θs_box : ContinuousOn (fun p : ℝ × ℝ => Θs p.1 p.2 (Z p.2))
      (Set.Icc a b ×ˢ Set.Icc s b) := hΘs_cont.comp_continuousOn hcont_tuple_box
  -- ## the algebraic identity
  have hkey : ∀ u ∈ Set.Icc a b, u ≠ s →
      J (slope Z s u - V s)
        = (((u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
          + (-((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
          + ((u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ)))
              - (∫ σ in s..b, Θs s σ (Z σ)))
          + (Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u))))
        - (u - s)⁻¹ • (G s (Z u) - G s (Z s) - J (Z u - Z s)) := by
    intro u hu hus
    have huI : u ∈ Set.Icc a b := hu
    have hi_Θu_su : IntervalIntegrable (fun σ : ℝ => Θ u σ (Z σ)) volume s u :=
      (hcont_Θ_Z u huI).intervalIntegrable
    have hi_Θu_us : IntervalIntegrable (fun σ : ℝ => Θ u σ (Z σ)) volume u s := hi_Θu_su.symm
    have hi_Θu_sb : IntervalIntegrable (fun σ : ℝ => Θ u σ (Z σ)) volume s b :=
      (hcont_Θ_Icc u huI).intervalIntegrable_of_Icc hs.2
    have hi_Θs_sb : IntervalIntegrable (fun σ : ℝ => Θ s σ (Z σ)) volume s b :=
      (hcont_Θ_Icc s hs).intervalIntegrable_of_Icc hs.2
    have hFTC : G u (Z u) - G s (Z u) = ∫ r in s..u, Gs r (Z u) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r => G r (Z u))
        (f' := fun r => Gs r (Z u))]
      · intro r hr
        exact hGs r (huIcc_sub huI hr) (Z u)
      · refine ContinuousOn.intervalIntegrable (u := fun r : ℝ => Gs r (Z u)) ?_
        have h1 : ContinuousOn (fun r : ℝ => (r, Z u)) (Set.uIcc s u) :=
          continuousOn_id.prodMk continuousOn_const
        exact hGs_cont.comp_continuousOn h1
    have hIntSplit : (∫ σ in u..b, Θ u σ (Z σ)) - (∫ σ in s..b, Θ s σ (Z σ))
        = -(∫ σ in s..u, Θ u σ (Z σ))
          + (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))) := by
      rw [intervalIntegral.integral_sub hi_Θu_sb hi_Θs_sb]
      rw [← intervalIntegral.integral_add_adjacent_intervals hi_Θu_us hi_Θu_sb]
      rw [intervalIntegral.integral_symm s u]
      module
    have hdiff : G u (Z u) - G s (Z s)
        = ((∫ σ in u..b, Θ u σ (Z σ)) - (∫ σ in s..b, Θ s σ (Z σ))) + (Ξ u - Ξ s) := by
      rw [hsol u huI, hsol s hs]; abel
    have hexp : (u - s)⁻¹ • (G u (Z u) - G s (Z s))
        = -(u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))
          + (u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ)))
          + (u - s)⁻¹ • (Ξ u - Ξ s) := by
      rw [hdiff, hIntSplit]
      module
    have hJslope : J (slope Z s u)
        = (u - s)⁻¹ • (G u (Z u) - G s (Z s))
          - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u))
          - (u - s)⁻¹ • (G s (Z u) - G s (Z s) - J (Z u - Z s)) := by
      rw [show slope Z s u = (u - s)⁻¹ • (Z u - Z s) from rfl, map_smul]
      have hJeq : J (Z u - Z s) = (G u (Z u) - G s (Z s)) - (∫ r in s..u, Gs r (Z u))
          - (G s (Z u) - G s (Z s) - J (Z u - Z s)) := by
        have h0 : J (Z u - Z s)
            = (G s (Z u) - G s (Z s)) - (G s (Z u) - G s (Z s) - J (Z u - Z s)) := by
          rw [sub_sub_cancel]
        rw [h0, ← hFTC]; module
      conv_lhs => rw [hJeq]
      module
    have hJv : J (V s) = - Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s := by
      rw [hJdef]; exact hV s hs
    rw [map_sub, hJslope, hJv, hexp]
    module
  -- ## the limit statements
  have T1 : Tendsto (fun u => (u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
      (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    have h : Tendsto (fun u => (u - s)⁻¹ • (Ξ u - Ξ s))
        (𝓝[Set.Icc a b \ {s}] s) (𝓝 (Ξs s)) := by
      have h1 := (hΞs s).tendsto_slope.mono_left hl_le
      have h2 : slope Ξ s = fun u => (u - s)⁻¹ • (Ξ u - Ξ s) := by
        funext u; simp [slope]
      rwa [h2] at h1
    simpa using h.sub_const (Ξs s)
  have hΦΘ : ContinuousWithinAt (fun p : ℝ × ℝ => Θ p.1 p.2 (Z p.2))
      (Set.Icc a b ×ˢ Set.Icc a b) (s, s) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (p.1, p.2, Z p.2))
        (Set.Icc a b ×ˢ Set.Icc a b) := by
      refine continuous_fst.continuousOn.prodMk (continuous_snd.continuousOn.prodMk ?_)
      exact hZ.comp continuous_snd.continuousOn (fun p hp => hp.2)
    exact (hΘ.comp_continuousOn h1).continuousWithinAt (by exact ⟨hs, hs⟩)
  have hΦGs : ContinuousWithinAt (fun p : ℝ × ℝ => Gs p.2 (Z p.1))
      (Set.Icc a b ×ˢ Set.Icc a b) (s, s) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (p.2, Z p.1)) (Set.Icc a b ×ˢ Set.Icc a b) :=
      continuous_snd.continuousOn.prodMk (hZ.comp continuous_fst.continuousOn (fun p hp => hp.1))
    exact (hGs_cont.comp_continuousOn h1).continuousWithinAt (by exact ⟨hs, hs⟩)
  have T2 : Tendsto (fun u => -((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
      (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    have h := interval_average_tendsto (f := fun u σ => Θ u σ (Z σ)) (s := s)
      (l := 𝓝[Set.Icc a b \ {s}] s) hl_le ?_ ?_
    · simpa using h.neg.add_const (Θ s s (Z s))
    · intro ε hεpos
      obtain ⟨δ, hδpos, hδprop⟩ := Metric.continuousWithinAt_iff.mp hΦΘ ε hεpos
      filter_upwards [self_mem_nhdsWithin, hl_nhds (Metric.ball_mem_nhds s hδpos)] with u huA huB
      intro σ hσ
      have hmem : (u, σ) ∈ Set.Icc a b ×ˢ Set.Icc a b := by
        refine ⟨huA.1, ?_⟩
        rcases le_total s u with h | h
        · rw [Set.uIcc_of_le h] at hσ; exact ⟨le_trans hs.1 hσ.1, le_trans hσ.2 huA.1.2⟩
        · rw [Set.uIcc_of_ge h] at hσ; exact ⟨le_trans huA.1.1 hσ.1, le_trans hσ.2 hs.2⟩
      exact hδprop hmem (lt_of_le_of_lt (dist_prod_pair_le hσ) huB)
    · filter_upwards [self_mem_nhdsWithin] with u huA
      exact (hcont_Θ_Z u huA.1).intervalIntegrable
  have T4 : Tendsto (fun u => Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u)))
      (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    have h := interval_average_tendsto (f := fun u r => Gs r (Z u)) (s := s)
      (l := 𝓝[Set.Icc a b \ {s}] s) hl_le ?_ ?_
    · simpa using h.const_sub (Gs s (Z s))
    · intro ε hεpos
      obtain ⟨δ, hδpos, hδprop⟩ := Metric.continuousWithinAt_iff.mp hΦGs ε hεpos
      filter_upwards [self_mem_nhdsWithin, hl_nhds (Metric.ball_mem_nhds s hδpos)] with u huA huB
      intro σ hσ
      have hmem : (u, σ) ∈ Set.Icc a b ×ˢ Set.Icc a b := by
        refine ⟨huA.1, ?_⟩
        rcases le_total s u with h | h
        · rw [Set.uIcc_of_le h] at hσ; exact ⟨le_trans hs.1 hσ.1, le_trans hσ.2 huA.1.2⟩
        · rw [Set.uIcc_of_ge h] at hσ; exact ⟨le_trans huA.1.1 hσ.1, le_trans hσ.2 hs.2⟩
      exact hδprop hmem (lt_of_le_of_lt (dist_prod_pair_le hσ) huB)
    · filter_upwards [self_mem_nhdsWithin] with u huA
      refine ContinuousOn.intervalIntegrable (u := fun r : ℝ => Gs r (Z u)) ?_
      have h1 : ContinuousOn (fun r : ℝ => (r, Z u)) (Set.uIcc s u) :=
        continuousOn_id.prodMk continuousOn_const
      exact hGs_cont.comp_continuousOn h1
  have T3 : Tendsto (fun u => (u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ)))
      - (∫ σ in s..b, Θs s σ (Z σ))) (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    have hder' : HasDerivWithinAt (fun x => ∫ t in s..b, Θ x t (Z t))
        (∫ t in s..b, Θs s t (Z t)) (Set.Icc a b) s :=
      param_interval_deriv (a := a) (b := b) (c := s) (d := b)
        hs.2 hs hcont_Θ_box hcont_Θs_box (fun x hx t ht => hΘs x hx t (Z t))
    have h2 : Tendsto (fun u => (u - s)⁻¹ •
        ((∫ t in s..b, Θ u t (Z t)) - (∫ t in s..b, Θ s t (Z t))))
        (𝓝[Set.Icc a b \ {s}] s) (𝓝 (∫ t in s..b, Θs s t (Z t))) := by
      refine ((hasDerivWithinAt_iff_tendsto_slope).mp hder').congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u huA
      simp [slope]
    have h3 : Tendsto (fun u => (u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))))
        (𝓝[Set.Icc a b \ {s}] s) (𝓝 (∫ σ in s..b, Θs s σ (Z σ))) := by
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u huA
      congr 1
      exact (intervalIntegral.integral_sub ((hcont_Θ_Icc u huA.1).intervalIntegrable_of_Icc hs.2)
        ((hcont_Θ_Icc s hs).intervalIntegrable_of_Icc hs.2)).symm
    simpa using h3.sub_const (∫ σ in s..b, Θs s σ (Z σ))
  -- ## combining the limits
  have hlim : Tendsto (fun u =>
      ((u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
      + (-((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
      + ((u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))) - (∫ σ in s..b, Θs s σ (Z σ)))
      + (Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u))))
      (𝓝[Set.Icc a b \ {s}] s) (𝓝 0) := by
    simpa using ((T1.add T2).add T3).add T4
  have htail : ∀ c > 0, ∀ᶠ u in 𝓝[Set.Icc a b \ {s}] s,
      ‖G s (Z u) - G s (Z s) - J (Z u - Z s)‖ ≤ c * ‖Z u - Z s‖ := by
    intro c hc
    have h1 : ∀ᶠ x in 𝓝 (Z s), ‖G s x - G s (Z s) - J (x - Z s)‖ ≤ c * ‖x - Z s‖ :=
      hlittle.def hc
    exact hZtend.eventually h1
  -- ## conclusion
  refine (hasDerivWithinAt_iff_tendsto_slope).mpr ?_
  rw [Metric.tendsto_nhds]
  intro η hη
  have hηB : 0 < η / (16 * B) := by positivity
  set c : ℝ := min (1 / (8 * B)) (η / (16 * B * (‖V s‖ + 1))) with hcdef
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hcB : B * c ≤ 1 / 8 := by
    have h1 : c ≤ 1 / (8 * B) := by rw [hcdef]; exact min_le_left _ _
    calc B * c ≤ B * (1 / (8 * B)) := mul_le_mul_of_nonneg_left h1 hB.le
      _ = 1 / 8 := by field_simp
  have hcV : c * ‖V s‖ ≤ η / (16 * B) := by
    have h1 : c ≤ η / (16 * B * (‖V s‖ + 1)) := by rw [hcdef]; exact min_le_right _ _
    have hVnn : 0 ≤ ‖V s‖ := norm_nonneg _
    have h2 : 0 < 16 * B * (‖V s‖ + 1) := by positivity
    have h3 : η * ‖V s‖ / (‖V s‖ + 1) ≤ η := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖V s‖ + 1)]
      nlinarith [hη.le, hVnn]
    have h4 : c * ‖V s‖ ≤ (η / (16 * B * (‖V s‖ + 1))) * ‖V s‖ :=
      mul_le_mul_of_nonneg_right h1 hVnn
    have h5 : (η / (16 * B * (‖V s‖ + 1))) * ‖V s‖ = (η * ‖V s‖ / (‖V s‖ + 1)) / (16 * B) := by
      field_simp
    rw [h5] at h4
    calc c * ‖V s‖ ≤ (η * ‖V s‖ / (‖V s‖ + 1)) / (16 * B) := h4
      _ ≤ η / (16 * B) := by
          apply div_le_div_of_nonneg_right h3 (by positivity)
  have hsmall : ∀ᶠ u in 𝓝[Set.Icc a b \ {s}] s, ‖((u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
      + (-((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
      + ((u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))) - (∫ σ in s..b, Θs s σ (Z σ)))
      + (Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u)))‖ ≤ η / (16 * B) := by
    have h1 : ∀ᶠ u in 𝓝[Set.Icc a b \ {s}] s, ‖((u - s)⁻¹ • (Ξ u - Ξ s) - Ξs s)
        + (-((u - s)⁻¹ • (∫ σ in s..u, Θ u σ (Z σ))) + Θ s s (Z s))
        + ((u - s)⁻¹ • (∫ σ in s..b, (Θ u σ (Z σ) - Θ s σ (Z σ))) - (∫ σ in s..b, Θs s σ (Z σ)))
        + (Gs s (Z s) - (u - s)⁻¹ • (∫ r in s..u, Gs r (Z u)))‖ < η / (16 * B) := by
      have h := (Metric.tendsto_nhds.mp hlim.norm) (η / (16 * B)) hηB
      filter_upwards [h] with u hu
      simpa using hu
    filter_upwards [h1] with u hu
    exact le_of_lt hu
  filter_upwards [hsmall, htail c hcpos, self_mem_nhdsWithin] with u hu1 hu2 hu3
  have huI : u ∈ Set.Icc a b := hu3.1
  have hkey' := hkey u huI (fun h => hu3.2 (by simpa [h]))
  have hgam : ‖(u - s)⁻¹ • (G s (Z u) - G s (Z s) - J (Z u - Z s))‖ ≤ c * ‖slope Z s u‖ := by
    rw [norm_smul, show slope Z s u = (u - s)⁻¹ • (Z u - Z s) from rfl, norm_smul]
    have h1 : ‖G s (Z u) - G s (Z s) - J (Z u - Z s)‖ ≤ c * ‖Z u - Z s‖ := hu2
    have h2 : 0 ≤ |(u - s)⁻¹| := abs_nonneg _
    calc |(u - s)⁻¹| * ‖G s (Z u) - G s (Z s) - J (Z u - Z s)‖
        ≤ |(u - s)⁻¹| * (c * ‖Z u - Z s‖) := mul_le_mul_of_nonneg_left h1 h2
      _ = c * (|(u - s)⁻¹| * ‖Z u - Z s‖) := by ring
  have hJb : ‖J (slope Z s u - V s)‖ ≤ η / (16 * B) + c * ‖slope Z s u‖ := by
    rw [hkey']
    exact le_trans (norm_sub_le _ _) (add_le_add hu1 hgam)
  have hVsplit : ‖slope Z s u‖ ≤ ‖slope Z s u - V s‖ + ‖V s‖ := by
    calc ‖slope Z s u‖ = ‖(slope Z s u - V s) + V s‖ := by abel_nf
      _ ≤ ‖slope Z s u - V s‖ + ‖V s‖ := norm_add_le _ _
  have h1 : ‖A₀ (slope Z s u - V s)‖ ≤ κ * ‖slope Z s u - V s‖
      + (η / (16 * B) + c * ‖slope Z s u‖) := by
    have hsplit : A₀ (slope Z s u - V s) = (A₀ - J) (slope Z s u - V s) + J (slope Z s u - V s) := by
      rw [ContinuousLinearMap.sub_apply]; abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ hJb)
    calc ‖(A₀ - J) (slope Z s u - V s)‖ ≤ ‖A₀ - J‖ * ‖slope Z s u - V s‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ κ * ‖slope Z s u - V s‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          simpa [norm_sub_rev] using hJA
  have h2 : ‖slope Z s u - V s‖ ≤ B * ‖A₀ (slope Z s u - V s)‖ := by
    have h1 := hAinv s hs
    calc ‖slope Z s u - V s‖ = ‖((A s).symm : E →L[ℝ] E) (A₀ (slope Z s u - V s))‖ := by
          rw [hA₀def]; simp
      _ ≤ B * ‖A₀ (slope Z s u - V s)‖ :=
          le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  have h3 : ‖slope Z s u - V s‖
      ≤ (B * κ + B * c) * ‖slope Z s u - V s‖ + B * (η / (16 * B) + c * ‖V s‖) := by
    have h2' := mul_le_mul_of_nonneg_left h1 hB.le
    have h4 : B * (κ * ‖slope Z s u - V s‖ + (η / (16 * B) + c * ‖slope Z s u‖))
        ≤ (B * κ + B * c) * ‖slope Z s u - V s‖ + B * (η / (16 * B) + c * ‖V s‖) := by
      have h5 : c * ‖slope Z s u‖ ≤ c * (‖slope Z s u - V s‖ + ‖V s‖) :=
        mul_le_mul_of_nonneg_left hVsplit hcpos.le
      nlinarith [h5, hcpos.le, hB.le, norm_nonneg (slope Z s u - V s), norm_nonneg (V s),
        mul_nonneg hB.le hcpos.le]
    linarith [h2, h2', h4]
  have h5 : (1 - B * κ - B * c) * ‖slope Z s u - V s‖ ≤ B * (η / (16 * B) + c * ‖V s‖) := by
    nlinarith [h3, hκB, hcB]
  have h6 : (1:ℝ) / 4 ≤ 1 - B * κ - B * c := by linarith [hκB, hcB]
  have h7 : ‖slope Z s u - V s‖ ≤ 4 * (B * (η / (16 * B) + c * ‖V s‖)) := by
    nlinarith [h5, h6, norm_nonneg (slope Z s u - V s)]
  calc dist (slope Z s u) (V s) = ‖slope Z s u - V s‖ := dist_eq_norm _ _
    _ ≤ 4 * (B * (η / (16 * B) + c * ‖V s‖)) := h7
    _ ≤ 4 * (B * (η / (16 * B) + η / (16 * B))) := by
        have h8 : B * (η / (16 * B) + c * ‖V s‖) ≤ B * (η / (16 * B) + η / (16 * B)) :=
          mul_le_mul_of_nonneg_left (by linarith [hcV]) hB.le
        linarith
    _ = η / 2 := by field_simp; ring
    _ < η := by linarith

theorem volterra_long_exists_C1_r {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b r : ℝ} (hab : a ≤ b) (hr : 0 < r) (hr1 : r ≤ 1)
    (A : ℝ → E ≃L[ℝ] E) (G0 G : ℝ → E → E) (Θ0 Θ : ℝ → ℝ → E → E) (Ξ0 Ξ : ℝ → E)
    (G0s Gs : ℝ → E → E) (Θ0s Θs : ℝ → ℝ → E → E) (Ξ0s Ξs : ℝ → E) (Z₀ Z₀s : ℝ → E)
    {B L Cg LG L1 : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (hCg : 0 ≤ Cg) (hLG : 0 ≤ LG) (hL1 : 0 ≤ L1)
    (hA_spec : ∀ s ∈ Set.Icc a b, (A s : E →L[ℝ] E) = fderiv ℝ (fun z => G0 s z) (Z₀ s))
    (hA_cont : ContinuousOn (fun s => ((A s).symm : E →L[ℝ] E)) (Set.Icc a b))
    (hAb : ∀ s ∈ Set.Icc a b, ‖((A s).symm : E →L[ℝ] E)‖ ≤ B)
    (hG_cont : Continuous (fun p : ℝ × E => G p.1 p.2))
    (hΘ_cont : Continuous (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2))
    (hΞ_cont : Continuous Ξ)
    (hZ₀_cont : ContinuousOn Z₀ (Set.Icc a b))
    (hZ₀s : ∀ s ∈ Set.Icc a b, HasDerivAt Z₀ (Z₀s s) s)
    (hZ₀s_cont : ContinuousOn Z₀s (Set.Icc a b))
    (hΘ0_cont : Continuous (fun p : ℝ × ℝ × E => Θ0 p.1 p.2.1 p.2.2))
    (hbase : ∀ s ∈ Set.Icc a b, G0 s (Z₀ s) = (∫ σ in s..b, Θ0 s σ (Z₀ σ)) + Ξ0 s)
    (hΘ_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) r,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) r, ‖Θ s σ z - Θ s σ z'‖ ≤ L * ‖z - z'‖)
    (hdiff : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) r,
      DifferentiableAt ℝ (fun w => G s w) z)
    (hGs : ∀ s ∈ Set.Icc a b, ∀ z : E, HasDerivAt (fun u : ℝ => G u z) (Gs s z) s)
    (hG0s : ∀ s ∈ Set.Icc a b, ∀ z : E, HasDerivAt (fun u : ℝ => G0 u z) (G0s s z) s)
    (hΘs : ∀ s ∈ Set.Icc a b, ∀ σ : ℝ, ∀ z : E, HasDerivAt (fun u : ℝ => Θ u σ z) (Θs s σ z) s)
    (hΘ0s : ∀ s ∈ Set.Icc a b, ∀ σ : ℝ, ∀ z : E,
      HasDerivAt (fun u : ℝ => Θ0 u σ z) (Θ0s s σ z) s)
    (hΞs : ∀ s : ℝ, HasDerivAt Ξ (Ξs s) s)
    (hΞ0s : ∀ s : ℝ, HasDerivAt Ξ0 (Ξ0s s) s)
    (hGs_cont : Continuous (fun p : ℝ × E => Gs p.1 p.2))
    (hG0s_cont : Continuous (fun p : ℝ × E => G0s p.1 p.2))
    (hΘs_cont : Continuous (fun p : ℝ × ℝ × E => Θs p.1 p.2.1 p.2.2))
    (hΘ0s_cont : Continuous (fun p : ℝ × ℝ × E => Θ0s p.1 p.2.1 p.2.2))
    (hΞs_cont : Continuous Ξs) (hΞ0s_cont : Continuous Ξ0s)
    (hGs_lip : ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) r,
      ∀ z' ∈ Metric.closedBall (Z₀ s) r, ‖Gs s z - Gs s z'‖ ≤ LG * ‖z - z'‖)
    (hΘs_lip : ∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) r,
      ∀ z' ∈ Metric.closedBall (Z₀ σ) r, ‖Θs s σ z - Θs s σ z'‖ ≤ L1 * ‖z - z'‖)
    (hbase_s : ∀ s ∈ Set.Icc a b, G0s s (Z₀ s) + (fderiv ℝ (fun z => G0 s z) (Z₀ s)) (Z₀s s)
      = - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s) :
    ∃ K1 K2 ε₀ : ℝ, 0 < K1 ∧ 0 < K2 ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∀ s ∈ Set.Icc a b, dist (Ξ s) (Ξ0 s) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) r, dist (G s z) (G0 s z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) r,
        dist (Θ s σ z) (Θ0 s σ z) < ε) →
      (∀ s ∈ Set.Icc a b, dist (Ξs s) (Ξ0s s) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) r, dist (Gs s z) (G0s s z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ σ ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ σ) r,
        dist (Θs s σ z) (Θ0s s σ z) < ε) →
      (∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (Z₀ s) r,
        ‖fderiv ℝ (fun w => G s w) z - (A s : E →L[ℝ] E)‖ ≤ Cg * ‖z - Z₀ s‖ + ε) →
      ∃ Z : ℝ → E, ContinuousOn Z (Set.Icc a b) ∧ Work.VolterraLong.SolvesOn a b G Θ Ξ Z ∧
        (∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε) ∧
        (∀ s ∈ Set.Icc a b, dist (deriv Z s) (Z₀s s) ≤ K2 * ε) := by
  classical
  have hG0_diff : ∀ s ∈ Set.Icc a b, DifferentiableAt ℝ (fun z => G0 s z) (Z₀ s) :=
    fun s hs => differentiableAt_of_fderiv_eq_equiv (f := fun z => G0 s z) (x := Z₀ s) (e := A s)
      (hA_spec s hs).symm
  set K1 : ℝ := 2 * B * (2 + (b - a)) * Real.exp ((4 * B * L + 1) * (b - a)) with hK1def
  have hK1pos : 0 < K1 := by
    rw [hK1def]
    have h1 : (0:ℝ) < 2 + (b - a) := by linarith
    positivity
  obtain ⟨S, hS⟩ : ∃ S : ℝ, ∀ s ∈ Set.Icc a b, ‖Z₀s s‖ ≤ S := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hZ₀s_cont
    exact ⟨max C 0, fun s hs => le_trans (hC s hs) (le_max_left C 0)⟩
  have hSnonneg : 0 ≤ S := le_trans (norm_nonneg _) (hS a (by simp [hab]))
  set M2 : ℝ := (1 + LG * K1) + (1 + L * K1) + (b - a + 1) * (1 + L1 * K1) + 1 with hM2def
  have hM2pos : 0 < M2 := by
    rw [hM2def]
    have h1 : 0 ≤ LG * K1 := mul_nonneg hLG hK1pos.le
    have h2 : 0 ≤ L * K1 := mul_nonneg hL hK1pos.le
    have h3 : 0 ≤ L1 * K1 := mul_nonneg hL1 hK1pos.le
    have h4 : 0 ≤ (b - a + 1) * (1 + L1 * K1) := by
      have h5 : (0:ℝ) ≤ b - a + 1 := by linarith
      positivity
    linarith
  set K2 : ℝ := 2 * B * ((Cg * K1 + 1) * S + M2) with hK2def
  have hK2pos : 0 < K2 := by
    rw [hK2def]
    have h2 : 0 ≤ Cg * K1 + 1 := by linarith [mul_nonneg hCg hK1pos.le]
    have h3 : 0 ≤ (Cg * K1 + 1) * S := mul_nonneg h2 hSnonneg
    positivity
  have hba : (0:ℝ) < 2 + (b - a) := by linarith
  set d2 : ℝ := r / (2 * B * (2 + (b - a)) * Real.exp ((4 * B * L + 1) * (b - a))) with hd2def
  set d3 : ℝ := r / (4 * B * (2 * r * B * Cg * (2 + (b - a)) *
    Real.exp ((4 * B * L + 1) * (b - a)) + 1)) with hd3def
  set d4 : ℝ := r / K1 with hd4def
  set d5 : ℝ := 1 / (1 + 2 * B * (Cg * K1 + 1)) with hd5def
  have hd2pos : 0 < d2 := by rw [hd2def]; positivity
  have hd3pos : 0 < d3 := by rw [hd3def]; positivity
  have hd4pos : 0 < d4 := by rw [hd4def]; positivity
  have hd5pos : 0 < d5 := by rw [hd5def]; positivity
  set ε₀ : ℝ := min 1 (min d2 (min d3 (min d4 d5))) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min one_pos (lt_min hd2pos (lt_min hd3pos (lt_min hd4pos hd5pos)))
  refine ⟨K1, K2, ε₀, hK1pos, hK2pos, hε₀pos, ?_⟩
  intro ε hε hεε₀ hΞc hGc hΘc hΞsc hGsc hΘsc hder
  have hε1 : ε < 1 := lt_of_lt_of_le hεε₀ (min_le_left _ _)
  have hε2 : ε < r / (2 * B * (2 + (b - a)) * Real.exp ((4 * B * L + 1) * (b - a))) := by
    have h := lt_of_lt_of_le hεε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
    rwa [hd2def] at h
  have hε3 : ε < r / (4 * B * (2 * r * B * Cg * (2 + (b - a)) *
      Real.exp ((4 * B * L + 1) * (b - a)) + 1)) := by
    have h := lt_of_lt_of_le hεε₀
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    rwa [hd3def] at h
  have hεd4 : ε < d4 := lt_of_lt_of_le hεε₀
    (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hεd5 : ε < d5 := lt_of_lt_of_le hεε₀
    (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hK1ε : K1 * ε ≤ r := by
    have h1 : K1 * ε < K1 * (r / K1) := by
      rw [hd4def] at hεd4
      exact mul_lt_mul_of_pos_left hεd4 hK1pos
    have h2 : K1 * (r / K1) = r := by field_simp
    linarith
  have hBκ : B * (Cg * K1 * ε + ε) ≤ 1 / 2 := by
    have hd : ε < 1 / (1 + 2 * B * (Cg * K1 + 1)) := by rw [← hd5def]; exact hεd5
    have hden : 0 < 1 + 2 * B * (Cg * K1 + 1) := by positivity
    have h1 : ε * (1 + 2 * B * (Cg * K1 + 1)) < 1 := by
      have h := (lt_div_iff₀ hden).mp hd
      linarith
    have h3 : 2 * B * (Cg * K1 + 1) * ε < 1 := by nlinarith [h1, hε.le]
    have h4 : Cg * K1 * ε + ε = (Cg * K1 + 1) * ε := by ring
    rw [h4]
    have h5 : B * ((Cg * K1 + 1) * ε) = (2 * B * (Cg * K1 + 1) * ε) / 2 := by ring
    rw [h5]
    linarith
  obtain ⟨Z, hZcont, hZsol, hZclose⟩ :=
    Work.OddCurveB.Engine.volterra_long_exists_ball hab r hr hr1 A G0 G Θ0 Θ Ξ0 Ξ Z₀
      hB hL hCg hG0_diff hA_spec hA_cont hAb hG_cont hΘ_cont hΞ_cont hZ₀_cont hΘ0_cont hbase
      hΘ_lip hdiff (2 + (b - a)) (Real.exp ((4 * B * L + 1) * (b - a))) rfl rfl
      hε hε1 hε2 hε3 hΞc hGc hΘc hder
  have hZclose' : ∀ s ∈ Set.Icc a b, dist (Z s) (Z₀ s) ≤ K1 * ε := by
    intro s hs
    simpa [hK1def] using hZclose s hs
  have hZs_mem : ∀ s ∈ Set.Icc a b, Z s ∈ Metric.closedBall (Z₀ s) r :=
    fun s hs => Metric.mem_closedBall.mpr (le_trans (hZclose' s hs) hK1ε)
  have hderJ : ∀ s ∈ Set.Icc a b,
      ‖fderiv ℝ (fun w => G s w) (Z s) - (A s : E →L[ℝ] E)‖ ≤ Cg * K1 * ε + ε := by
    intro s hs
    have h1 := hder s hs (Z s) (hZs_mem s hs)
    have h2 : ‖Z s - Z₀ s‖ ≤ K1 * ε := by
      have h3 := hZclose' s hs; rwa [dist_eq_norm] at h3
    have h4 : Cg * ‖Z s - Z₀ s‖ ≤ Cg * (K1 * ε) := mul_le_mul_of_nonneg_left h2 hCg
    linarith
  have hdiffZ : ∀ s ∈ Set.Icc a b, DifferentiableAt ℝ (fun w => G s w) (Z s) :=
    fun s hs => hdiff s hs (Z s) (hZs_mem s hs)
  have hδ : ∀ s ∈ Set.Icc a b,
      ‖(- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      - (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)‖
        ≤ M2 * ε := by
    intro s hs
    have hdata := data_diff_bound_r (hab := hab) (hr := hr) (hε := hε)
      (hK1 := le_of_lt hK1pos) (hL := hL) (hLG := hLG) (hL1 := hL1) (hZ := hZclose')
      (hK1r := hK1ε) (hZ_cont := hZcont) (hZ₀_cont := hZ₀_cont) (hΘs_cont := hΘs_cont)
      (hΘ0s_cont := hΘ0s_cont) (hGs_lip := hGs_lip) (hΘ_lip := hΘ_lip) (hΘs_lip := hΘs_lip)
      (hGs_c := hGsc) (hΘ_c := hΘc) (hΘs_c := hΘsc) (hΞs_c := hΞsc) s hs
    rwa [hM2def]
  have hexistsV : ∀ s ∈ Set.Icc a b, ∃ v : E,
      fderiv ℝ (fun w => G s w) (Z s) v
        = (- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      ∧ ‖v - Z₀s s‖ ≤ K2 * ε := by
    intro s hs
    have hbase' : (A s : E →L[ℝ] E) (Z₀s s)
        = (- G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s) := by
      have h := hbase_s s hs
      rw [← hA_spec s hs] at h
      have h2 : (A s : E →L[ℝ] E) (Z₀s s)
          = - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s - G0s s (Z₀ s) := by
        rw [← h]; abel
      rw [h2]; abel
    obtain ⟨v, hv1, hv2⟩ := solve_near_equiv (A := A s)
      (J := fderiv ℝ (fun w => G s w) (Z s))
      (B := B) (κ := Cg * K1 * ε + ε) (δ := M2 * ε)
      (R := - Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s)
      (R₀ := - G0s s (Z₀ s) - Θ0 s s (Z₀ s) + (∫ σ in s..b, Θ0s s σ (Z₀ σ)) + Ξ0s s)
      hB (hAb s hs) (hderJ s hs) hBκ hbase' (hδ s hs)
    refine ⟨v, hv1, le_trans hv2 ?_⟩
    rw [hK2def]
    have hb1 : (Cg * K1 * ε + ε) * ‖Z₀s s‖ ≤ ((Cg * K1 + 1) * S) * ε := by
      have h2 := hS s hs
      have h3 : Cg * K1 * ε + ε = (Cg * K1 + 1) * ε := by ring
      rw [h3]
      calc (Cg * K1 + 1) * ε * ‖Z₀s s‖ = ((Cg * K1 + 1) * ‖Z₀s s‖) * ε := by ring
        _ ≤ ((Cg * K1 + 1) * S) * ε := by
            refine mul_le_mul_of_nonneg_right ?_ hε.le
            exact mul_le_mul_of_nonneg_left h2 (by linarith [mul_nonneg hCg hK1pos.le])
    have hb2 : (Cg * K1 * ε + ε) * ‖Z₀s s‖ + M2 * ε
        ≤ ((Cg * K1 + 1) * S + M2) * ε := by linarith
    calc 2 * B * ((Cg * K1 * ε + ε) * ‖Z₀s s‖ + M2 * ε)
        ≤ 2 * B * (((Cg * K1 + 1) * S + M2) * ε) :=
          mul_le_mul_of_nonneg_left hb2 (by positivity)
      _ = 2 * B * ((Cg * K1 + 1) * S + M2) * ε := by ring
  let V : ℝ → E := fun s => if h : s ∈ Set.Icc a b then Classical.choose (hexistsV s h) else 0
  have hVeq : ∀ s ∈ Set.Icc a b, fderiv ℝ (fun w => G s w) (Z s) (V s)
      = (- Gs s (Z s) - Θ s s (Z s) + (∫ σ in s..b, Θs s σ (Z σ)) + Ξs s) := by
    intro s hs
    dsimp only [V]
    rw [dif_pos hs]
    exact (Classical.choose_spec (hexistsV s hs)).1
  have hVclose : ∀ s ∈ Set.Icc a b, dist (V s) (Z₀s s) ≤ K2 * ε := by
    intro s hs
    dsimp only [V]
    rw [dif_pos hs, dist_eq_norm]
    exact (Classical.choose_spec (hexistsV s hs)).2
  have hVderiv : ∀ s ∈ Set.Icc a b, HasDerivWithinAt Z (V s) (Set.Icc a b) s :=
    deriv_from_solution_linearized (hab := hab) (hB := hB) (hAinv := hAb) (hZ := hZcont)
      (hκB := hBκ) (hsol := hZsol) (hG := hG_cont) (hΘ := hΘ_cont) (hΞ := hΞ_cont)
      (hGs := hGs) (hGs_cont := hGs_cont) (hΘs := hΘs) (hΘs_cont := hΘs_cont)
      (hΞs := hΞs) (hΞs_cont := hΞs_cont) (hdiffZ := hdiffZ) (hJκ := hderJ) (hV := hVeq)
  obtain ⟨Z', hZ'eq, hZ'deriv⟩ := exists_extension_hasDerivAt hab hVderiv
  refine ⟨Z', ?_, ?_, ?_, ?_⟩
  · exact hZcont.congr (fun s hs => hZ'eq s hs)
  · intro s hs
    rw [hZ'eq s hs]
    have hcongr : (∫ σ in s..b, Θ s σ (Z' σ)) = (∫ σ in s..b, Θ s σ (Z σ)) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      have hx' : x ∈ Set.Icc a b := by
        have h1 : x ∈ Set.uIcc s b := hx
        rw [Set.uIcc_of_le hs.2] at h1
        exact ⟨le_trans hs.1 h1.1, h1.2⟩
      rw [hZ'eq x hx']
    rw [hcongr]
    exact hZsol s hs
  · intro s hs
    rw [hZ'eq s hs]
    exact hZclose' s hs
  · intro s hs
    have hderiv : deriv Z' s = V s := (hZ'deriv s hs).deriv
    rw [hderiv]
    exact hVclose s hs

end Work.VolterraLong
