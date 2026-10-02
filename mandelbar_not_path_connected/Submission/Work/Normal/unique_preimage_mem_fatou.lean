import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.poly_unique_root_factorization
import Submission.Work.Normal.iterates_dist_le_of_contraction
import Submission.Work.Normal.isNormalFamily_of_tendsto_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Points that are their own unique preimage lie in the Fatou set

Let `f : ℂ → ℂ` be the evaluation map of a polynomial of degree `d ≥ 2` and let `y` be the unique
solution of `f z = y`.  Then `f y = y`, and the equation `f z = y` has the single root `y`; since
`f` has degree `d`, that root has multiplicity `d ≥ 2`, i.e. `f z - y = a (z - y) ^ d` for some
`a ≠ 0` (this is `Work.Normal.poly_unique_root_factorization`).  Consequently `y` is a
**superattracting** fixed point: on the disc of radius `ρ = min 1 (1 / (2 (‖a‖ + 1)))` around `y`
the map `f` contracts distances to `y` by the factor `1/2`, and therefore the iterates of `f`
converge locally uniformly to the constant `y` on the disc `ball y ρ`.  In particular the family of
iterates is normal there (every sequence of iterates is `f^[k n]`, and either `k` takes a value at
arbitrarily large indices or `k n → ∞`, so it has a locally uniformly convergent subsequence), and
`y` is a point of the Fatou set (using `Work.Normal.isNormalFamily_of_tendsto_iterate`).
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology

/-- For `0 ≤ x ≤ 1` and `1 ≤ n` we have `x ^ n ≤ x`. -/
private lemma pow_le_self_of_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    x ^ n ≤ x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ h0 h1) h0).trans_eq (one_mul x)

/-- If `f z - y = a * (z - y) ^ d` with `d ≥ 2`, then on the disc of radius
`min 1 (1 / (2 (‖a‖ + 1)))` around `y` the map `f` contracts the distance to `y` by the factor
`1 / 2`.  (The hypothesis `a ≠ 0` is not needed: when `a = 0` the map is constant `y` and the
statement is trivial.) -/
private lemma contraction_of_factorization {d : ℕ} (hd : 2 ≤ d) {f : ℂ → ℂ} {y a : ℂ}
    (hfa : ∀ z, f z - y = a * (z - y) ^ d) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, dist z y ≤ ρ → dist (f z) y ≤ (1 / 2) * dist z y := by
  refine ⟨min 1 (1 / (2 * (‖a‖ + 1))), lt_min one_pos (by positivity), ?_⟩
  intro z hz
  have hz1 : dist z y ≤ 1 := hz.trans (min_le_left _ _)
  have hz2 : dist z y ≤ 1 / (2 * (‖a‖ + 1)) := hz.trans (min_le_right _ _)
  have hdist : dist (f z) y = ‖a‖ * (dist z y) ^ d := by
    rw [Complex.dist_eq, hfa z, norm_mul, norm_pow, ← Complex.dist_eq]
  rw [hdist]
  have hpow : (dist z y) ^ (d - 1) ≤ dist z y :=
    pow_le_self_of_le_one dist_nonneg hz1 (by omega)
  have hhalf : ‖a‖ / (2 * (‖a‖ + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg a]
  have hkey : ‖a‖ * (dist z y) ^ (d - 1) ≤ 1 / 2 := by
    have h1 : ‖a‖ * (dist z y) ^ (d - 1) ≤ ‖a‖ * dist z y :=
      mul_le_mul_of_nonneg_left hpow (norm_nonneg a)
    have h2 : ‖a‖ * dist z y ≤ ‖a‖ * (1 / (2 * (‖a‖ + 1))) :=
      mul_le_mul_of_nonneg_left hz2 (norm_nonneg a)
    have h3 : ‖a‖ * (1 / (2 * (‖a‖ + 1))) = ‖a‖ / (2 * (‖a‖ + 1)) := by ring
    linarith
  have hpowd : (dist z y) ^ d = (dist z y) ^ (d - 1) * dist z y := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ]
  calc ‖a‖ * (dist z y) ^ d = ‖a‖ * (dist z y) ^ (d - 1) * dist z y := by
        rw [hpowd]; ring
    _ ≤ (1 / 2) * dist z y := mul_le_mul_of_nonneg_right hkey dist_nonneg

/-- If `f` contracts distances to `y` by the factor `1 / 2` on the closed disc of radius `ρ > 0`,
then the iterates of `f` converge locally uniformly to the constant `y` on the disc `ball y ρ`. -/
private lemma iterates_tendsto_of_contraction {f : ℂ → ℂ} {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hstep : ∀ z : ℂ, dist z y ≤ ρ → dist (f z) y ≤ (1 / 2) * dist z y) :
    TendstoLocallyUniformlyOn (fun n : ℕ => f^[n]) (fun _ : ℂ => y) Filter.atTop
      (Metric.ball y ρ) := by
  obtain hgeom := iterates_dist_le_of_contraction hρ hstep
  have hball : TendstoUniformlyOn (fun n : ℕ => f^[n]) (fun _ : ℂ => y) Filter.atTop
      (Metric.closedBall y ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * ρ) Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using h1.mul_const ρ
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
    refine Filter.eventually_atTop.2 ⟨N, fun n hn z hz => ?_⟩
    have hlt : (1 / 2 : ℝ) ^ n * ρ < ε := by
      have := hN n hn
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    have hzρ : dist z y ≤ ρ := Metric.mem_closedBall.1 hz
    calc dist y (f^[n] z) = dist (f^[n] z) y := dist_comm _ _
      _ ≤ (1 / 2) ^ n * dist z y := hgeom n z hzρ
      _ ≤ (1 / 2) ^ n * ρ := mul_le_mul_of_nonneg_left hzρ (by positivity)
      _ < ε := hlt
  exact (hball.tendstoLocallyUniformlyOn).mono Metric.ball_subset_closedBall

/-- If a point `y` is the unique preimage of itself under a polynomial map `f` of degree `d ≥ 2`,
then `y` belongs to the Fatou set of `f`: on a small disc around `y` the iterates converge locally
uniformly to the constant `y`. -/
theorem unique_preimage_mem_fatou {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) {y : ℂ} (h : ∀ z, f z = y ↔ z = y) :
    y ∈ FatouSet f := by
  obtain ⟨a, _ha, hfa⟩ := poly_unique_root_factorization hf h
  obtain ⟨ρ, hρ, hstep⟩ := contraction_of_factorization hd hfa
  refine fatouSet_of_mem_nhds (Metric.ball_mem_nhds y hρ) Metric.isOpen_ball ?_
  exact isNormalFamily_of_tendsto_iterate (iterates_tendsto_of_contraction hρ hstep)

end Work.Normal
