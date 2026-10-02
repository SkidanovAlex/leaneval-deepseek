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
# The derivative of the Fatou coordinate tends to `1` at `+∞`

For the parabolic germ `f z = z + z^2 h z` described by `ParabolicBounds`, the Fatou coordinate
in the chart `w = -1/z`,

`fatouCoordW f (1 - a) w = approxCoord (1 - a) w + ∑' k, coordError f (1 - a) ((wMap f)^[k] w)`,

has derivative tending to `1` as `Re w → +∞`.  Concretely we produce `N > 1/r` with

`‖deriv (fatouCoordW f (1 - a)) w - 1‖ ≤ 1/2` for every `w` with `Re w > N`.

The proof differentiates the defining series term by term on the half-plane `{Re w > N}` using
`hasDerivAt_tsum_of_isPreconnected`: the derivative of the `k`-th term is
`(deriv (coordError f (1-a)) (w_k)) * deriv ((wMap f)^[k]) w`, bounded by `B*M/(N+k/2)^2`
thanks to `coordError_deriv_bound`, `wMap_iterate_deriv_bound` and the orbit growth
`orbit_re_growth_aux`.  The majorant series is summable with sum `≤ 1/4`, and the derivative of
`approxCoord` contributes exactly `-(1-a)/w`, also of norm `≤ 1/4`.
-/

namespace Work.FatouCoord.Exist

open Work.FatouCoord

open scoped Topology

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-- The right half-plane `{w : ℂ | N < w.re}` is convex. -/
private lemma convex_re_gt (N : ℝ) : Convex ℝ {w : ℂ | N < w.re} := by
  have h : Convex ℝ (Complex.reLm ⁻¹' (Set.Ioi N)) := (convex_Ioi N).linear_preimage Complex.reLm
  convert h using 1
  ext z
  simp [Complex.reLm, Set.mem_Ioi]

/-- Elementary rewriting `X / (N + n/2)^2 = 4X / (2N + n)^2`. -/
private lemma div_half_sq (X N : ℝ) (hN : 0 < N) (n : ℕ) :
    X / (N + (n : ℝ) / 2) ^ 2 = 4 * X / (2 * N + (n : ℝ)) ^ 2 := by
  have h1 : (0 : ℝ) < N + (n : ℝ) / 2 := by positivity
  have h2 : (0 : ℝ) < 2 * N + (n : ℝ) := by positivity
  rw [div_eq_div_iff (pow_ne_zero 2 h1.ne') (pow_ne_zero 2 h2.ne')]
  ring

theorem fatouCoordW_deriv_close {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ N : ℝ, 0 < N ∧ 1 / r < N ∧ ∀ w : ℂ, N < w.re →
      ‖deriv (fatouCoordW f (1 - a)) w - 1‖ ≤ 1 / 2 := by
  obtain ⟨N₁, B, hN₁pos, hBnn, _hrN₁, hderr⟩ := Estimate.coordError_deriv_bound hb
  obtain ⟨N₂, M, hN₂pos, _hrN₂, hMnn, hditer⟩ := Estimate.wMap_iterate_deriv_bound hb
  obtain ⟨Ns, hNspos, _hrNs, hsumm⟩ := Estimate.summable_coordError hb
  -- nonnegativity facts used to extract the bounds on `N`
  have hKnn : (0 : ℝ) ≤ 2 * Estimate.Ksub A a := by
    have := Estimate.Ksub_nonneg (A := A) hb.hA a
    linarith
  have hBMnn : (0 : ℝ) ≤ B * M := mul_nonneg hBnn hMnn
  have h12BMnn : (0 : ℝ) ≤ 12 * (B * M) := by linarith
  have hann : (0 : ℝ) ≤ 4 * ‖(1 : ℂ) - a‖ := by positivity
  have h1rpos : (0 : ℝ) < 1 / r := one_div_pos.mpr hb.hr
  -- the level `N`
  set S : ℝ := 4 + (1 / r + 9) + 2 * Estimate.Ksub A a + N₁ + N₂ + Ns
      + 12 * (B * M) + 4 * ‖(1 : ℂ) - a‖ + 2 with hSdef
  set N : ℝ := max S 1 with hNdef
  have hSN : S ≤ N := le_max_left _ _
  have h1N : (1 : ℝ) ≤ N := le_max_right _ _
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one h1N
  have hN4 : (4 : ℝ) ≤ N := by
    have h : (4 : ℝ) ≤ S := by rw [hSdef]; linarith
    linarith
  have hNr : 1 / r < N := by
    have h : 1 / r + 9 ≤ S := by rw [hSdef]; linarith
    linarith
  have hNslit : 1 / r + 9 < N := by
    have h : 1 / r + 9 < S := by rw [hSdef]; linarith
    linarith
  have hNK : 2 * Estimate.Ksub A a ≤ N := by
    have h : 2 * Estimate.Ksub A a ≤ S := by rw [hSdef]; linarith
    linarith
  have hN₁N : N₁ < N := by
    have h : N₁ < S := by rw [hSdef]; linarith
    linarith
  have hN₂N : N₂ < N := by
    have h : N₂ < S := by rw [hSdef]; linarith
    linarith
  have hNsN : Ns < N := by
    have h : Ns < S := by rw [hSdef]; linarith
    linarith
  have hN12BM : 12 * (B * M) ≤ N := by
    have h : 12 * (B * M) ≤ S := by rw [hSdef]; linarith
    linarith
  have hN4a : 4 * ‖(1 : ℂ) - a‖ ≤ N := by
    have h : 4 * ‖(1 : ℂ) - a‖ ≤ S := by rw [hSdef]; linarith
    linarith
  refine ⟨N, hNpos, hNr, ?_⟩
  intro w hw
  -- the region and the orbit growth
  have hUopen : IsOpen {z : ℂ | N < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected {z : ℂ | N < z.re} := (convex_re_gt N).isPreconnected
  have hgrowthU : ∀ y : ℂ, N < y.re → ∀ k : ℕ, N + (k : ℝ) / 2 ≤ ((wMap f)^[k] y).re :=
    fun y hy k => Estimate.orbit_re_growth_aux hb hN4 hNr hNK hy k
  -- the summands
  let g : ℕ → ℂ → ℂ := fun n z => coordError f (1 - a) ((wMap f)^[n] z)
  let g' : ℕ → ℂ → ℂ :=
    fun n z => deriv (coordError f (1 - a)) ((wMap f)^[n] z) * deriv ((wMap f)^[n]) z
  let u : ℕ → ℝ := fun n => B * M / (N + (n : ℝ) / 2) ^ 2
  -- the chain rule for each summand
  have hterm : ∀ n : ℕ, ∀ y ∈ {z : ℂ | N < z.re}, HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have hyN : N < y.re := hy
    have hiterdiff : ∀ i < n, DifferentiableAt ℂ (wMap f) ((wMap f)^[i] y) := by
      intro i _
      have hre := hgrowthU y hyN i
      have hi2 : (0 : ℝ) ≤ (i : ℝ) / 2 := by positivity
      have hle : N ≤ ((wMap f)^[i] y).re := by linarith
      have hnorm : (4 : ℝ) ≤ ‖((wMap f)^[i] y)‖ :=
        le_trans hN4 (le_trans hle (Complex.re_le_norm _))
      have h1r : 1 / r < ‖((wMap f)^[i] y)‖ :=
        lt_of_lt_of_le hNr (le_trans hle (Complex.re_le_norm _))
      exact Estimate.differentiableAt_wMap hb h1r hnorm
    have hiter_hd : HasDerivAt ((wMap f)^[n]) (deriv ((wMap f)^[n]) y) y :=
      (Estimate.hasDerivAt_iterate n hiterdiff).differentiableAt.hasDerivAt
    have hcoord_hd : HasDerivAt (coordError f (1 - a))
        (deriv (coordError f (1 - a)) ((wMap f)^[n] y)) ((wMap f)^[n] y) := by
      have h9 : 1 / r + 9 < ((wMap f)^[n] y).re := by
        have h1 := hgrowthU y hyN n
        have h2 : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
        linarith
      have hWslit : wMap f ((wMap f)^[n] y) ∈ Complex.slitPlane := by
        refine Or.inl ?_
        have h2 := hgrowthU y hyN (n + 1)
        rw [Function.iterate_succ_apply'] at h2
        have h3 : (0 : ℝ) < N + (((n + 1 : ℕ)) : ℝ) / 2 := by positivity
        linarith
      exact (Estimate.hasDerivAt_coordError hb h9 hWslit).differentiableAt.hasDerivAt
    have hcomp := hcoord_hd.comp y hiter_hd
    rw [Function.comp_def] at hcomp
    simpa only [g, g'] using hcomp
  -- the uniform majorant
  have hgle : ∀ n : ℕ, ∀ y ∈ {z : ℂ | N < z.re}, ‖g' n y‖ ≤ u n := by
    intro n y hy
    have hyN : N < y.re := hy
    have hre := hgrowthU y hyN n
    have hn2 : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
    have hng : N + (n : ℝ) / 2 ≤ ‖((wMap f)^[n] y)‖ := le_trans hre (Complex.re_le_norm _)
    have hpos : 0 < N + (n : ℝ) / 2 := by linarith
    have hc1 : ‖deriv (coordError f (1 - a)) ((wMap f)^[n] y)‖ ≤ B / ‖((wMap f)^[n] y)‖ ^ 2 :=
      hderr _ (by linarith)
    have hc2 : ‖deriv ((wMap f)^[n]) y‖ ≤ M := hditer y (lt_trans hN₂N hyN) n
    have hdiv : B / ‖((wMap f)^[n] y)‖ ^ 2 ≤ B / (N + (n : ℝ) / 2) ^ 2 :=
      div_le_div_of_nonneg_left hBnn (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hng 2)
    calc ‖g' n y‖
        = ‖deriv (coordError f (1 - a)) ((wMap f)^[n] y)‖ * ‖deriv ((wMap f)^[n]) y‖ := by
          simp only [g', norm_mul]
      _ ≤ (B / (N + (n : ℝ) / 2) ^ 2) * M :=
          mul_le_mul (le_trans hc1 hdiv) hc2 (norm_nonneg _) (div_nonneg hBnn (sq_nonneg _))
      _ = u n := by simp only [u]; ring
  -- summability of the majorant and its sum
  have h4BMnn : (0 : ℝ) ≤ 4 * (B * M) := by linarith
  have hufin : ∀ k : ℕ, ∑ i ∈ Finset.range k, u i ≤ 3 * ((B * M) / N) := by
    intro k
    have h1 : ∑ i ∈ Finset.range k, u i
        = (4 * (B * M)) * ∑ i ∈ Finset.range k, 1 / (2 * N + (i : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [u]
      rw [div_half_sq (B * M) N hNpos i, mul_one_div]
    rw [h1]
    have h2 := Estimate.sum_range_inv_sq_le (2 * N) (by linarith : (0 : ℝ) < 2 * N) k
    have h3 : (4 * (B * M)) * (1 / (2 * N) ^ 2 + 1 / (2 * N))
        = (B * M) / N ^ 2 + 2 * ((B * M) / N) := by
      ring_nf
    have h4 : (B * M) / N ^ 2 ≤ (B * M) / N := by
      have hNle : N ≤ N ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left hBMnn hNpos hNle
    calc (4 * (B * M)) * ∑ i ∈ Finset.range k, 1 / (2 * N + (i : ℝ)) ^ 2
        ≤ (4 * (B * M)) * (1 / (2 * N) ^ 2 + 1 / (2 * N)) :=
          mul_le_mul_of_nonneg_left h2 h4BMnn
      _ = (B * M) / N ^ 2 + 2 * ((B * M) / N) := h3
      _ ≤ 3 * ((B * M) / N) := by linarith
  have hunn : ∀ n : ℕ, (0 : ℝ) ≤ u n :=
    fun n => div_nonneg hBMnn (sq_nonneg _)
  have hu_summ : Summable u := summable_of_sum_range_le hunn hufin
  have hu_le : ∑' n, u n ≤ 3 * ((B * M) / N) := Real.tsum_le_of_sum_range_le hunn hufin
  have hu_quarter : ∑' n, u n ≤ 1 / 4 := by
    have h : 3 * ((B * M) / N) ≤ 1 / 4 := by
      have h1 : 3 * ((B * M) / N) = 3 * (B * M) / N := by ring
      rw [h1, div_le_iff₀ hNpos]
      linarith [hN12BM]
    linarith
  -- summability at the base point
  have hy₀mem : (((N + 1 : ℝ) : ℂ)) ∈ {z : ℂ | N < z.re} := by
    simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
    linarith
  have hg0 : Summable (fun n : ℕ => g n (((N + 1 : ℝ) : ℂ))) := by
    have hx : Ns < (((N + 1 : ℝ) : ℂ)).re := by
      simp only [Complex.ofReal_re]
      linarith
    have h : Summable
        (fun n : ℕ => ‖coordError f (1 - a) ((wMap f)^[n] (((N + 1 : ℝ) : ℂ)))‖) := hsumm _ hx
    simpa [g] using h.of_norm
  -- differentiate the series term by term
  have htsum := hasDerivAt_tsum_of_isPreconnected (u := u) (g := g) (g' := g')
    (t := {z : ℂ | N < z.re}) (y₀ := ((N + 1 : ℝ) : ℂ))
    hu_summ hUopen hUconn hterm hgle hy₀mem hg0 hw
  have happrox : HasDerivAt (approxCoord (1 - a)) (1 - (1 - a) / w) w :=
    Estimate.hasDerivAt_approxCoord (Or.inl (lt_trans hNpos hw))
  have hψ := happrox.add htsum
  have hderiv : deriv (fatouCoordW f (1 - a)) w = (1 - (1 - a) / w) + ∑' n, g' n w := hψ.deriv
  rw [hderiv]
  have hD : (1 - (1 - a) / w + ∑' n, g' n w) - 1 = (∑' n, g' n w) - (1 - a) / w := by ring
  rw [hD]
  have hsumm_norm : Summable (fun n : ℕ => ‖g' n w‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => hgle n w hw) hu_summ
  have hS : ‖∑' n, g' n w‖ ≤ 1 / 4 :=
    le_trans (norm_tsum_le_tsum_norm hsumm_norm)
      (le_trans (Summable.tsum_le_tsum (fun n => hgle n w hw) hsumm_norm hu_summ) hu_quarter)
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

end

end Work.FatouCoord.Exist
