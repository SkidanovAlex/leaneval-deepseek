import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.coordError_deriv_bound
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound
import Submission.Work.FatouCoord.Estimate.iterate_re_growth
import Submission.Work.FatouCoord.Estimate.summable_coordError

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Injectivity of the Fatou coordinate on a right half-plane

The Fatou coordinate of a parabolic germ, in the chart `w = -1/z`,

`fatouCoordW f (1 - a) w = approxCoord (1 - a) w + ∑' k, coordError f (1 - a) ((wMap f)^[k] w)`,

has derivative `1 + o(1)` as `Re w → +∞`.  In this file we deduce that `fatouCoordW f (1 - a)`
is injective on a right half-plane `{Re w > N}`.

The argument is the classical one.  Write `ψ = fatouCoordW f (1 - a)` and `G = ψ - id`.  On the
half-plane the series of defects may be differentiated term by term (locally uniformly): the
tool is `hasDerivAt_tsum_of_isPreconnected`, and the bounds for `deriv coordError` and for the
derivative of the iterates of `wMap` come from the `Estimate` files, together with the growth
`Re ((wMap f)^[k] w) ≥ N + k/2` of the orbit.  This gives

`‖deriv (ψ - id) w‖ ≤ |1 - a| / N + ∑' k, 4 B₁ M / (2N + k)^2 ≤ 1/4 + 1/4 = 1/2`

for `Re w > N`.  A mean value inequality on the convex half-plane then shows that `ψ - id` is
`1/2`-Lipschitz, whence `ψ` is injective: if `ψ w₁ = ψ w₂`, then
`‖w₁ - w₂‖ = ‖(ψ - id) w₁ - (ψ - id) w₂‖ ≤ (1/2)‖w₁ - w₂‖`.
-/

namespace Work.FatouCoord.Exist

open Work.FatouCoord
open scoped Topology
open Set Filter Metric Function

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-- The right half-plane `{w | N < Re w}` is convex over `ℝ`. -/
private lemma convex_re_gt (N : ℝ) : Convex ℝ {w : ℂ | N < w.re} := by
  have h : {w : ℂ | N < w.re} = Complex.reLm ⁻¹' (Set.Ioi N) := by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]
    rfl
  rw [h]
  exact (convex_Ioi N).linear_preimage Complex.reLm

/-- Elementary rewriting of a quotient with the substitution `w = (2N + n)/2`. -/
private lemma div_half_eq (B N : ℝ) (hN : 0 < N) (n : ℕ) :
    B / (N + (n : ℝ) / 2) ^ 2 = 4 * B / (2 * N + (n : ℝ)) ^ 2 := by
  have h1 : (0 : ℝ) < N + (n : ℝ) / 2 := by positivity
  have h2 : (0 : ℝ) < 2 * N + (n : ℝ) := by positivity
  field_simp
  ring

/-- **The derivative of the Fatou coordinate is close to `1`.**

For the parabolic germ described by `ParabolicBounds` there is `N > 1/r` such that on
`{Re w > N}` the Fatou coordinate in the chart is holomorphic and

`‖deriv (fatouCoordW f (1 - a)) w - 1‖ ≤ 1/2`.

Equivalently `G = fatouCoordW f (1 - a) - id` has derivative of norm at most `1/2` there. -/
private theorem deriv_close_aux (hb : ParabolicBounds f h a r A A') :
    ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ w : ℂ, N < w.re →
      DifferentiableAt ℂ (fatouCoordW f (1 - a)) w ∧
        ‖deriv (fatouCoordW f (1 - a)) w - 1‖ ≤ 1 / 2 := by
  obtain ⟨N₁, B₁, hN₁pos, hB₁, _hrN₁, hcErr⟩ := Estimate.coordError_deriv_bound hb
  obtain ⟨N₂, M, hN₂pos, _hrN₂, hM, hwMapD⟩ := Estimate.wMap_iterate_deriv_bound hb
  obtain ⟨N₄, hN₄pos, _hrN₄, hsumm⟩ := Estimate.summable_coordError hb
  set S : ℝ := 1 / r + 9 + N₁ + N₂ + N₄ + 2 * Estimate.Ksub A a + 16 * (B₁ * M)
      + 4 * ‖(1 : ℂ) - a‖ + 2 with hSdef
  set N : ℝ := max S 1 with hNdef
  have hSN : S ≤ N := le_max_left _ _
  have h1N : (1 : ℝ) ≤ N := le_max_right _ _
  have hBMnn : (0 : ℝ) ≤ B₁ * M := mul_nonneg hB₁ hM
  have h16BM : (0 : ℝ) ≤ 16 * (B₁ * M) := by linarith
  have h4a : (0 : ℝ) ≤ 4 * ‖(1 : ℂ) - a‖ := by positivity
  have hKsubnn : (0 : ℝ) ≤ Estimate.Ksub A a := Estimate.Ksub_nonneg hb.hA a
  have h2K : (0 : ℝ) ≤ 2 * Estimate.Ksub A a := by linarith
  have h1r : (0 : ℝ) < 1 / r := one_div_pos.mpr hb.hr
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one h1N
  have hhalf_nn : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) / 2 := fun k => by positivity
  have h9N : 1 / r + 9 < N := by
    have h : 1 / r + 9 < S := by rw [hSdef]; linarith
    linarith
  have hN₁N : N₁ < N := by
    have h : N₁ < S := by rw [hSdef]; linarith
    linarith
  have hN₂N : N₂ < N := by
    have h : N₂ < S := by rw [hSdef]; linarith
    linarith
  have hN₄N : N₄ < N := by
    have h : N₄ < S := by rw [hSdef]; linarith
    linarith
  have hrN : 1 / r < N := lt_trans (by linarith : 1 / r < 1 / r + 9) h9N
  have hN4 : (4 : ℝ) ≤ N := by
    have h : (4 : ℝ) < S := by rw [hSdef]; linarith
    linarith
  have hNK : 2 * Estimate.Ksub A a ≤ N := by
    have h : 2 * Estimate.Ksub A a ≤ S := by rw [hSdef]; linarith
    linarith
  have hN16BM : 16 * (B₁ * M) ≤ N := by
    have h : 16 * (B₁ * M) ≤ S := by rw [hSdef]; linarith
    linarith
  have hN4a : 4 * ‖(1 : ℂ) - a‖ ≤ N := by
    have h : 4 * ‖(1 : ℂ) - a‖ ≤ S := by rw [hSdef]; linarith
    linarith
  -- the region and its elementary properties
  have hUopen : IsOpen {z : ℂ | N < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {z : ℂ | N < z.re} := (convex_re_gt N).isPreconnected
  -- growth of the orbit along the region: `Re w` increases by `1/2` at every step
  have hgrowthU : ∀ y : ℂ, N < y.re → ∀ k : ℕ, N + (k : ℝ) / 2 ≤ ((wMap f)^[k] y).re :=
    fun y hy k => Estimate.orbit_re_growth_aux hb hN4 hrN hNK hy k
  -- the summands and their derivatives
  let g : ℕ → ℂ → ℂ := fun n z => coordError f (1 - a) ((wMap f)^[n] z)
  let g' : ℕ → ℂ → ℂ :=
    fun n z => deriv (coordError f (1 - a)) ((wMap f)^[n] z) * deriv ((wMap f)^[n]) z
  let u : ℕ → ℝ := fun n => 4 * (B₁ * M) / (2 * N + (n : ℝ)) ^ 2
  -- every summand is differentiable, with the announced derivative
  have hterm : ∀ (n : ℕ), ∀ y ∈ {z : ℂ | N < z.re}, HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have hyN : N < y.re := hy
    have hiterdiff : ∀ i < n, DifferentiableAt ℂ (wMap f) ((wMap f)^[i] y) := by
      intro i _
      have hre : N ≤ ((wMap f)^[i] y).re :=
        le_trans (by linarith [hhalf_nn i] : N ≤ N + (i : ℝ) / 2) (hgrowthU y hyN i)
      have h4norm : (4 : ℝ) ≤ ‖((wMap f)^[i] y)‖ :=
        le_trans hN4 (le_trans hre (Complex.re_le_norm _))
      have hrn : 1 / r < ‖((wMap f)^[i] y)‖ :=
        lt_of_lt_of_le (lt_of_lt_of_le hrN hre) (Complex.re_le_norm _)
      exact Estimate.differentiableAt_wMap hb hrn h4norm
    have hiter_hd : HasDerivAt ((wMap f)^[n]) (deriv ((wMap f)^[n]) y) y :=
      (Estimate.hasDerivAt_iterate n hiterdiff).differentiableAt.hasDerivAt
    have hcoord_hd : HasDerivAt (coordError f (1 - a))
        (deriv (coordError f (1 - a)) ((wMap f)^[n] y)) ((wMap f)^[n] y) := by
      have h9 : 1 / r + 9 < ((wMap f)^[n] y).re := by
        have h1 : N ≤ ((wMap f)^[n] y).re :=
          le_trans (by linarith [hhalf_nn n] : N ≤ N + (n : ℝ) / 2) (hgrowthU y hyN n)
        exact lt_of_lt_of_le h9N h1
      have hWslit : wMap f ((wMap f)^[n] y) ∈ Complex.slitPlane := by
        refine Or.inl ?_
        have h2 : N ≤ ((wMap f)^[n + 1] y).re := by
          refine le_trans (by linarith [hhalf_nn (n + 1)] : N ≤ N + ((n + 1 : ℕ) : ℝ) / 2) ?_
          exact hgrowthU y hyN (n + 1)
        rw [Function.iterate_succ_apply'] at h2
        linarith
      exact (Estimate.hasDerivAt_coordError hb h9 hWslit).differentiableAt.hasDerivAt
    have hcomp := hcoord_hd.comp y hiter_hd
    exact hcomp
  -- the uniform majorant of the derivatives
  have hg'le : ∀ (n : ℕ), ∀ y ∈ {z : ℂ | N < z.re}, ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hyN : N < y.re := hy
    have hre : N + (n : ℝ) / 2 ≤ ((wMap f)^[n] y).re := hgrowthU y hyN n
    have hng : N + (n : ℝ) / 2 ≤ ‖((wMap f)^[n] y)‖ := le_trans hre (Complex.re_le_norm _)
    have hNle : N ≤ ((wMap f)^[n] y).re :=
      le_trans (by linarith [hhalf_nn n] : N ≤ N + (n : ℝ) / 2) hre
    have hpos : 0 < N + (n : ℝ) / 2 := by linarith [hNpos, hhalf_nn n]
    have hc1 : ‖deriv (coordError f (1 - a)) ((wMap f)^[n] y)‖
        ≤ B₁ / ‖((wMap f)^[n] y)‖ ^ 2 := hcErr _ (lt_of_lt_of_le hN₁N hNle)
    have hc2 : ‖deriv ((wMap f)^[n]) y‖ ≤ M := hwMapD y (lt_trans hN₂N hyN) n
    have hdiv : B₁ / ‖((wMap f)^[n] y)‖ ^ 2 ≤ 4 * B₁ / (2 * N + (n : ℝ)) ^ 2 := by
      have h1 : B₁ / ‖((wMap f)^[n] y)‖ ^ 2 ≤ B₁ / (N + (n : ℝ) / 2) ^ 2 :=
        div_le_div_of_nonneg_left hB₁ (pow_pos hpos 2) (by nlinarith)
      rwa [div_half_eq B₁ N hNpos n] at h1
    have hdiv' : ‖deriv (coordError f (1 - a)) ((wMap f)^[n] y)‖
        ≤ 4 * B₁ / (2 * N + (n : ℝ)) ^ 2 := le_trans hc1 hdiv
    have h4 : (0 : ℝ) ≤ 4 * B₁ / (2 * N + (n : ℝ)) ^ 2 := by positivity
    calc ‖g' n y‖
        = ‖deriv (coordError f (1 - a)) ((wMap f)^[n] y)‖ * ‖deriv ((wMap f)^[n]) y‖ := by
          simp only [g', norm_mul]
      _ ≤ (4 * B₁ / (2 * N + (n : ℝ)) ^ 2) * M := mul_le_mul hdiv' hc2 (norm_nonneg _) h4
      _ = u n := by simp only [u]; ring
  -- summability of the majorant, with an explicit bound
  have hufin : ∀ k : ℕ, ∑ i ∈ Finset.range k, u i ≤ 4 * (B₁ * M) / N := by
    intro k
    have hnn : (0 : ℝ) ≤ 4 * (B₁ * M) := by linarith
    have hsplit : ∑ i ∈ Finset.range k, u i
        = 4 * (B₁ * M) * ∑ i ∈ Finset.range k, 1 / (2 * N + (i : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [u]; rw [mul_one_div]
    rw [hsplit]
    have hsmall : 1 / (2 * N) ^ 2 ≤ 1 / (2 * N) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h1N]
    have h2N : 1 / (2 * N) + 1 / (2 * N) = 1 / N := by
      field_simp
      ring
    have hsum2N : ∑ i ∈ Finset.range k, 1 / (2 * N + (i : ℝ)) ^ 2 ≤ 1 / N := by
      have h2 := Estimate.sum_range_inv_sq_le (2 * N) (by positivity) k
      linarith
    calc 4 * (B₁ * M) * ∑ i ∈ Finset.range k, 1 / (2 * N + (i : ℝ)) ^ 2
        ≤ 4 * (B₁ * M) * (1 / N) := mul_le_mul_of_nonneg_left hsum2N hnn
      _ = 4 * (B₁ * M) / N := by ring
  have hu_summ : Summable u := summable_of_sum_range_le (fun n => by positivity) hufin
  have hu_le : ∑' n, u n ≤ 4 * (B₁ * M) / N :=
    Real.tsum_le_of_sum_range_le (fun n => by positivity) hufin
  have hu_quarter : ∑' n, u n ≤ 1 / 4 := by
    have h : 4 * (B₁ * M) / N ≤ 1 / 4 := by
      rw [div_le_iff₀ hNpos]
      linarith
    linarith
  -- convergence of the series at the base point
  have hg0 : Summable (fun n : ℕ => g n (((N + 1 : ℝ) : ℂ))) := by
    have h : Summable
        (fun n : ℕ => ‖coordError f (1 - a) ((wMap f)^[n] (((N + 1 : ℝ) : ℂ)))‖) :=
      hsumm _ (by simp only [Complex.ofReal_re]; linarith)
    simpa [g] using h.of_norm
  refine ⟨N, hNpos, hrN, fun w hw => ?_⟩
  have hy₀mem : (((N + 1 : ℝ) : ℂ)) ∈ {z : ℂ | N < z.re} := by
    simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; linarith
  have htsum := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    (t := {z : ℂ | N < z.re}) (y₀ := ((N + 1 : ℝ) : ℂ))
    hu_summ hUopen hUconn hterm hg'le hy₀mem hg0 hw
  have happrox : HasDerivAt (approxCoord (1 - a)) (1 - (1 - a) / w) w :=
    Estimate.hasDerivAt_approxCoord (c := 1 - a) (Or.inl (lt_trans hNpos hw))
  have hψ := happrox.add htsum
  refine ⟨?_, ?_⟩
  · exact hψ.differentiableAt
  · have hderiv : deriv (fatouCoordW f (1 - a)) w = 1 - (1 - a) / w + ∑' n, g' n w := hψ.deriv
    rw [hderiv]
    have hD : (1 - (1 - a) / w + ∑' n, g' n w - 1) = ((∑' n, g' n w) - (1 - a) / w) := by ring
    rw [hD]
    have hsumm_norm : Summable (fun n : ℕ => ‖g' n w‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hg'le n w hw) hu_summ
    have hS : ‖∑' n, g' n w‖ ≤ 1 / 4 :=
      le_trans (norm_tsum_le_tsum_norm hsumm_norm)
        (le_trans (Summable.tsum_le_tsum (fun n => hg'le n w hw) hsumm_norm hu_summ) hu_quarter)
    have hwN : N ≤ ‖w‖ := le_trans hw.le (Complex.re_le_norm w)
    have hc : ‖(1 - a) / w‖ ≤ 1 / 4 := by
      rw [norm_div]
      have h2 : ‖1 - a‖ / ‖w‖ ≤ ‖1 - a‖ / N :=
        div_le_div_of_nonneg_left (norm_nonneg _) hNpos hwN
      have h3 : ‖1 - a‖ / N ≤ 1 / 4 := by
        rw [div_le_iff₀ hNpos]
        linarith
      linarith
    calc ‖(∑' n, g' n w) - (1 - a) / w‖
        ≤ ‖∑' n, g' n w‖ + ‖(1 - a) / w‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add hS hc
      _ = 1 / 2 := by norm_num

theorem fatouCoordW_injOn {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : ParabolicBounds f h a r A A') : ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ Set.InjOn (fatouCoordW f (1 - a)) {w : ℂ | N < w.re} := by
  obtain ⟨N, hNpos, hrN, hclose⟩ := deriv_close_aux hb
  refine ⟨N, hNpos, hrN, ?_⟩
  intro w₁ hw₁ w₂ hw₂ heq
  have hdiff : ∀ x ∈ {w : ℂ | N < w.re},
      DifferentiableAt ℂ (fun w => fatouCoordW f (1 - a) w - w) x := by
    intro x hx
    exact ((hclose x hx).1).sub differentiableAt_id
  have hbound : ∀ x ∈ {w : ℂ | N < w.re},
      ‖deriv (fun w => fatouCoordW f (1 - a) w - w) x‖ ≤ 1 / 2 := by
    intro x hx
    have hder : deriv (fun w => fatouCoordW f (1 - a) w - w) x
        = deriv (fatouCoordW f (1 - a)) x - 1 := by
      have h1 : (fun w => fatouCoordW f (1 - a) w - w)
          = (fun w => fatouCoordW f (1 - a) w) - id := by
        funext w; simp
      rw [h1, deriv_sub (hclose x hx).1 differentiableAt_id, deriv_id]
    rw [hder]
    exact (hclose x hx).2
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun w => fatouCoordW f (1 - a) w - w) (C := 1 / 2) hdiff hbound
    (convex_re_gt N) hw₁ hw₂
  have hval : (fatouCoordW f (1 - a) w₂ - w₂) - (fatouCoordW f (1 - a) w₁ - w₁) = w₁ - w₂ := by
    rw [heq]; ring
  rw [hval] at hmvt
  rw [norm_sub_rev w₂ w₁] at hmvt
  have hzero : ‖w₁ - w₂‖ = 0 := by
    nlinarith [hmvt, norm_nonneg (w₁ - w₂)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end

end Work.FatouCoord.Exist
