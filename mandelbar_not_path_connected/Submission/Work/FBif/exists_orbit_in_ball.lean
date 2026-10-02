/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif.exists_orbit_in_ball`

The orbit of a point near a period-`5` point `z₁` of `T_c` stays bounded — by any prescribed
`α ≥ escR c + 1` — during the first five iterates of the perturbation `perturb c q ε`, uniformly
for `z` in a fixed disc around `z₁` and for all small `ε > 0`.

The argument is a continuity/stability estimate and uses no dynamics of the perturbation:

* every point of the cycle of `z₁` has modulus at most the escape radius `escR c`
  (`Work.FBif.cyclePt_norm_le_escR`), so there is a disc `‖z - z₁‖ ≤ δ'` on which the
  *unperturbed* iterates `(T_c)^[k]`, `k ≤ 5`, stay strictly below a margin `β` with
  `escR c < β < α` (continuity of the finitely many maps `(T_c)^[k]`);
* on the ball of radius `M = α + 1` the map `q` is bounded by some `Q`, so for `ε < 1`
  the one-step error `‖f_ε u - T_c v‖ ≤ 2M‖u - v‖ + εQ` is `L`-Lipschitz up to the additive
  constant `εQ` with `L = 2M + 2Q`;
* the elementary orbit-stability estimate `Work.FBif.norm_iterate_sub_le` then gives
  `‖(f_ε^[k]) z‖ ≤ β + εQ · errB L k ≤ β + εQ · errB L 5 ≤ α` for `k ≤ 5`, provided `ε` is
  small enough that `εQ · errB L 5 ≤ α - β`.
-/
import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.escR_props

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Function
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The accumulated error factor -/

/-- `errB L k = 1 + L + ⋯ + L ^ (k-1)`: the accumulated error factor of the orbit-stability
estimate.  If the one-step error of a perturbed orbit obeys `e_{k+1} ≤ L * e_k + η`, then
`e_k ≤ η * errB L k`. -/
def errB (L : ℝ) : ℕ → ℝ
  | 0 => 0
  | (k + 1) => L * errB L k + 1

@[simp] theorem errB_zero (L : ℝ) : errB L 0 = 0 := rfl

@[simp] theorem errB_succ (L : ℝ) (k : ℕ) : errB L (k + 1) = L * errB L k + 1 := rfl

/-- The closed form of the accumulated error factor: `errB L k = ∑_{i<k} L^i`. -/
theorem errB_eq_sum (L : ℝ) (k : ℕ) : errB L k = ∑ i ∈ Finset.range k, L ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : L * (∑ i ∈ Finset.range k, L ^ i) = ∑ i ∈ Finset.range k, L ^ (i + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [errB_succ, ih, h, Finset.sum_range_succ', pow_zero]

theorem errB_nonneg {L : ℝ} (hL : 0 ≤ L) (k : ℕ) : 0 ≤ errB L k := by
  rw [errB_eq_sum]
  exact Finset.sum_nonneg (fun i _ => pow_nonneg hL i)

theorem errB_le_succ {L : ℝ} (hL : 0 ≤ L) (k : ℕ) : errB L k ≤ errB L (k + 1) := by
  have h : errB L (k + 1) = (∑ i ∈ Finset.range k, L ^ i) + L ^ k := by
    rw [errB_eq_sum, Finset.sum_range_succ]
  rw [h, errB_eq_sum]
  exact le_add_of_nonneg_right (pow_nonneg hL k)

theorem errB_mono {L : ℝ} (hL : 0 ≤ L) : Monotone (errB L) :=
  monotone_nat_of_le_succ (errB_le_succ hL)

/-! ## The orbit-stability estimate -/

/-- **Orbit stability.**  Let `f`, `g : ℂ → ℂ`, let `x` be a point whose `f`-orbit up to time
`5` stays in the ball of radius `ρ`, and suppose that on the ball of radius `M` the map `g`
approximates `f` in the mixed form `‖g u - f v‖ ≤ L ‖u - v‖ + η`.  If `ρ + η * errB L 5 ≤ M`,
then for every `k ≤ 5` the `g`-orbit of `x` stays within `ρ + η * errB L 5 ≤ M` and differs
from the `f`-orbit by at most `η * errB L k`. -/
theorem norm_iterate_sub_le {f g : ℂ → ℂ} {L η ρ M : ℝ} {x : ℂ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hM : ρ + η * errB L 5 ≤ M)
    (hmix : ∀ u v : ℂ, ‖u‖ ≤ M → ‖v‖ ≤ M → ‖g u - f v‖ ≤ L * ‖u - v‖ + η)
    (hmax : ∀ k : ℕ, k ≤ 5 → ‖(f^[k]) x‖ ≤ ρ) :
    ∀ k : ℕ, k ≤ 5 →
      ‖(g^[k]) x - (f^[k]) x‖ ≤ η * errB L k ∧ ‖(g^[k]) x‖ ≤ ρ + η * errB L k := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp, ?_⟩
    simpa using hmax 0 (by norm_num)
  | succ k ih =>
    intro hk
    have hk5 : k ≤ 5 := by omega
    obtain ⟨hd, hb⟩ := ih hk5
    have hmono : errB L k ≤ errB L 5 := errB_mono hL (by omega)
    have hη5 : 0 ≤ η * errB L 5 := mul_nonneg hη (errB_nonneg hL 5)
    have hgk : ‖(g^[k]) x‖ ≤ M := by
      have h1 : η * errB L k ≤ η * errB L 5 := mul_le_mul_of_nonneg_left hmono hη
      linarith
    have hfk : ‖(f^[k]) x‖ ≤ M := by linarith [hmax k hk5]
    have hkey : ‖(g^[k.succ]) x - (f^[k.succ]) x‖ ≤ η * errB L (k.succ) := by
      rw [Function.iterate_succ_apply' g k x, Function.iterate_succ_apply' f k x]
      calc ‖g ((g^[k]) x) - f ((f^[k]) x)‖
          ≤ L * ‖(g^[k]) x - (f^[k]) x‖ + η := hmix _ _ hgk hfk
        _ ≤ L * (η * errB L k) + η := by
              have := mul_le_mul_of_nonneg_left hd hL
              linarith
        _ = η * errB L (k.succ) := by rw [errB_succ]; ring
    refine ⟨hkey, ?_⟩
    calc ‖(g^[k.succ]) x‖ = ‖((g^[k.succ]) x - (f^[k.succ]) x) + (f^[k.succ]) x‖ := by ring_nf
      _ ≤ ‖(g^[k.succ]) x - (f^[k.succ]) x‖ + ‖(f^[k.succ]) x‖ := norm_add_le _ _
      _ ≤ η * errB L (k.succ) + ρ := by linarith [hmax (k + 1) hk]
      _ = ρ + η * errB L (k.succ) := by ring

/-! ## The orbit near the parabolic point -/

/-- For every `α` above the escape radius there is a disc around the period-`5` point `z₁` and a
threshold `ε₀ > 0` such that for `0 < ε < ε₀` the first five iterates of `perturb c q ε` of any
point of that disc have modulus at most `α`. -/
theorem exists_orbit_in_ball (c z₁ : ℂ) (hper : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁)
    {q : ℂ → ℂ} (hq : Continuous q) {α : ℝ} (hα : Work.FBif.escR c + 1 ≤ α) :
    ∃ δ' > 0, ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ z : ℂ, ‖z - z₁‖ ≤ δ' →
      ∀ k : ℕ, k ≤ 5 → ‖(Work.FBif.perturb c q ε)^[k] z‖ ≤ α := by
  have hTc : ∀ k : ℕ, Continuous ((Tantibar c)^[k]) := fun k => (continuous_tantibar c).iterate k
  have hcyc : ∀ k : ℕ, ‖(Tantibar c)^[k] z₁‖ ≤ escR c :=
    fun k => cyclePt_norm_le_escR c z₁ hper k
  -- a margin `β` strictly between `escR c` and `α`
  obtain ⟨β, hβesc, hβα⟩ : ∃ β : ℝ, escR c < β ∧ β < α :=
    ⟨(escR c + α) / 2, by linarith, by linarith⟩
  have hβpos : 0 < β := by linarith [one_le_escR c, hβesc]
  -- a disc around `z₁` in which the unperturbed orbit stays below `β` through time `5`
  have htube : ∀ᶠ w in 𝓝 z₁, ∀ k ∈ Finset.range 6, ‖(Tantibar c)^[k] w‖ < β := by
    rw [Filter.eventually_all_finset (Finset.range 6)]
    intro k _
    have hmem : Metric.ball (0 : ℂ) β ∈ 𝓝 ((Tantibar c)^[k] z₁) :=
      Metric.isOpen_ball.mem_nhds (by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (hcyc k) hβesc)
    have hpre := (hTc k).continuousAt.preimage_mem_nhds hmem
    filter_upwards [hpre] with x hx
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hx
    exact hx
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp htube
  have hδ' : ∀ w : ℂ, ‖w - z₁‖ ≤ δ₁ / 2 → ∀ k : ℕ, k ≤ 5 → ‖(Tantibar c)^[k] w‖ < β := by
    intro w hw k hk
    have h1 : w ∈ Metric.ball z₁ δ₁ := by
      rw [Metric.mem_ball, dist_eq_norm]; linarith
    exact hδ₁sub h1 k (Finset.mem_range.mpr (by omega))
  -- a bound `Q` for `q` on the ball of radius `M = α + 1`
  set M : ℝ := α + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; linarith
  have hβM : β < M := by rw [hMdef]; linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, ∀ u : ℂ, ‖u‖ ≤ M → ‖q u‖ ≤ Q := by
    obtain ⟨Q, hQ⟩ :=
      (isCompact_closedBall (0 : ℂ) M).exists_bound_of_continuousOn hq.continuousOn
    exact ⟨Q, fun u hu => hQ u (by rw [Metric.mem_closedBall, dist_zero_right]; exact hu)⟩
  have hQ0 : 0 ≤ Q := le_trans (norm_nonneg (q 0)) (hQ 0 (by simpa using hMpos.le))
  -- the stability constants
  set L : ℝ := 2 * M + 2 * Q with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith [hMpos.le, hQ0]
  have hL2M : 2 * M ≤ L := by rw [hLdef]; linarith [hQ0]
  set c₅ : ℝ := errB L 5 with hc₅def
  have hc₅0 : 0 ≤ c₅ := by rw [hc₅def]; exact errB_nonneg hL0 5
  refine ⟨δ₁ / 2, by linarith, min 1 ((α - β) / (1 + Q * c₅)), ?_, ?_⟩
  · refine lt_min one_pos (div_pos (by linarith) ?_)
    linarith [mul_nonneg hQ0 hc₅0]
  · intro ε hε hε₀ z hz k hk
    have hε1 : ε < 1 := lt_of_lt_of_le hε₀ (min_le_left _ _)
    have hεdiv : ε < (α - β) / (1 + Q * c₅) := lt_of_lt_of_le hε₀ (min_le_right _ _)
    have hden : 0 < 1 + Q * c₅ := by linarith [mul_nonneg hQ0 hc₅0]
    -- the threshold condition `ε * Q * c₅ < α - β`
    have hstep : ε * (Q * c₅) < α - β := by
      have h1 : ε * (1 + Q * c₅) < α - β := by
        have := mul_lt_mul_of_pos_right hεdiv hden
        rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at this
      have h2 : ε * (Q * c₅) ≤ ε * (1 + Q * c₅) :=
        mul_le_mul_of_nonneg_left (by linarith [mul_nonneg hQ0 hc₅0]) hε.le
      linarith
    have herr5 : ε * (Q * errB L 5) < α - β := by
      rw [hc₅def] at hstep
      exact hstep
    -- the mixed one-step estimate
    have hmix : ∀ u v : ℂ, ‖u‖ ≤ M → ‖v‖ ≤ M →
        ‖perturb c q ε u - (Tantibar c) v‖ ≤ L * ‖u - v‖ + ε * Q := by
      intro u v hu hv
      have hTuv : ‖Tantibar c u - Tantibar c v‖ ≤ 2 * M * ‖u - v‖ := by
        have hsq : Tantibar c u - Tantibar c v = (star u - star v) * (star u + star v) := by
          show (star u)^2 + c - ((star v)^2 + c) = _
          ring
        rw [hsq, norm_mul]
        have h1 : ‖star u - star v‖ = ‖u - v‖ := by rw [← star_sub, norm_star]
        have h2 : ‖star u + star v‖ ≤ ‖u‖ + ‖v‖ := by
          calc ‖star u + star v‖ ≤ ‖star u‖ + ‖star v‖ := norm_add_le _ _
            _ = ‖u‖ + ‖v‖ := by simp
        rw [h1]
        calc ‖u - v‖ * ‖star u + star v‖ ≤ ‖u - v‖ * (‖u‖ + ‖v‖) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ ≤ ‖u - v‖ * (2 * M) :=
              mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
          _ = 2 * M * ‖u - v‖ := by ring
      have hqu : ‖(ε : ℂ) * q u‖ ≤ ε * Q := by
        rw [norm_mul]
        have hεnorm : ‖((ε : ℝ) : ℂ)‖ = ε := by simp [abs_of_pos hε]
        rw [hεnorm]
        exact mul_le_mul_of_nonneg_left (hQ u hu) hε.le
      have hsplit : perturb c q ε u - Tantibar c v
          = (Tantibar c u - Tantibar c v) + (ε : ℂ) * q u := by
        rw [perturb_apply]; ring
      rw [hsplit]
      calc ‖(Tantibar c u - Tantibar c v) + (ε : ℂ) * q u‖
          ≤ ‖Tantibar c u - Tantibar c v‖ + ‖(ε : ℂ) * q u‖ := norm_add_le _ _
        _ ≤ 2 * M * ‖u - v‖ + ε * Q := add_le_add hTuv hqu
        _ ≤ L * ‖u - v‖ + ε * Q := by
              have h2 : 2 * M * ‖u - v‖ ≤ L * ‖u - v‖ :=
                mul_le_mul_of_nonneg_right hL2M (norm_nonneg _)
              linarith
    have hMQ : β + ε * Q * errB L 5 ≤ M := by
      have h1 : ε * Q * errB L 5 = ε * (Q * errB L 5) := by ring
      rw [h1]; linarith [hMdef]
    have hmax : ∀ j : ℕ, j ≤ 5 → ‖((Tantibar c)^[j]) z‖ ≤ β :=
      fun j hj => le_of_lt (hδ' z hz j hj)
    have hmain := norm_iterate_sub_le (f := Tantibar c) (g := perturb c q ε) (x := z)
      (L := L) (η := ε * Q) (ρ := β) (M := M) hL0 (mul_nonneg hε.le hQ0) hMQ hmix hmax
    obtain ⟨-, hb⟩ := hmain k hk
    calc ‖(perturb c q ε)^[k] z‖
        ≤ β + ε * Q * errB L k := hb
      _ ≤ β + ε * Q * errB L 5 := by
            have h2 : ε * Q * errB L k ≤ ε * Q * errB L 5 :=
              mul_le_mul_of_nonneg_left (errB_mono hL0 hk) (mul_nonneg hε.le hQ0)
            linarith
      _ ≤ α := by
            have h1 : ε * Q * errB L 5 = ε * (Q * errB L 5) := by ring
            linarith [herr5, h1]

end Work.FBif

end
