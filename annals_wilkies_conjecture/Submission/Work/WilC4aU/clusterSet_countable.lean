import Mathlib
import Submission.Work.WilC4aU.Defs
import Submission.Work.WilC4aU.cluster_estimate
import Submission.Work.WilC4aU.threshold_le_of_eps_mul

namespace Work.WilC4aU

open WilkiesDesign.CG.C4a (PBOne)

/-- **C4aU.Countable.**  Every cluster value of the ratio `f (2 x) / f x` is `2 ^ q` for a
rational `q`; hence the cluster-value set is countable.

Recall (`Submission/Work/WilC4aU/Defs.lean`, namespace `Work.WilC4aU`):
`ClusterSet Y = {lam | ∃ c : Fin k → ℝ, RatioCluster Y c lam}`,
`ZeroSect Y c = ∃ R, ∀ x y, R ≤ x → Fin.cons x (Fin.cons y c) ∈ Y → y = 0`,
`AsymSect Y c q a = a ≠ 0 ∧ ∀ ε > 0, ∃ R, ∀ x y, R ≤ x → Fin.cons x (Fin.cons y c) ∈ Y →
  |y / x ^ (q : ℝ) - a| < ε`,
and (`WilkiesDesign.CG.C4a`) `PBOne Y c ↔ ZeroSect Y c ∨ ∃ q a, AsymSect Y c q a`
(`Work.WilC4aU.pbOne_iff`).  Useful helper lemmas already proved in `Defs.lean`:
`Work.WilC4aU.unbounded_of_ratioCluster`, `Work.WilC4aU.not_zeroSect_of_unbounded`,
`Work.WilC4aU.sq_lt_sq_iff_ratio` (and it is safe to state/prove the inclusion
`ClusterSet Y ⊆ Set.range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ))` first and derive countability from
`Set.countable_range`).

Proof plan.  Let `lam ∈ ClusterSet Y`, witnessed by `c`.
* `¬ ZeroSect Y c`: by `unbounded_of_ratioCluster` (the cluster condition gives, for every `R`,
  points `(x,y,c) ∈ Y` with `x ≥ R` and `y ≠ 0`), use `not_zeroSect_of_unbounded`.
* Hence by `pbOne_iff` and `h1 c`, `∃ q a, AsymSect Y c q a`.
* Show `lam = 2 ^ q`.  Given `ε₁ > 0`, first fix `δ := min (|a|/2) (ε₁ * |a| / (8 * 2 ^ q)) > 0`
  and let `R` be the asymptotic threshold for error `δ` (note `2 ^ (q : ℝ) > 0`).
  Then apply `RatioCluster` with `ε := min (ε₁/2) (1 / (max R 1 + 1)) > 0`, obtaining
  `x, y, y'`, and convert the last condition with `sq_lt_sq_iff_ratio`:
  `|y' / y - lam| < ε ≤ ε₁/2`, and `x ≥ 1/ε ≥ max R 1 ≥ R`, `2 * x ≥ R`.
  From the asymptotic at `x` and `2 * x`:
  `|y - a * x ^ q| < δ * x ^ q` and `|y' - a * (2 * x) ^ q| < δ * (2 * x) ^ q`, while
  `(2 * x) ^ q = 2 ^ q * x ^ q` (`Real.mul_rpow`, `x > 0`) and `|y| ≥ (|a|/2) * x ^ q`.
  Hence `|y' / y - 2 ^ q| ≤ 4 * δ * 2 ^ q / |a| ≤ ε₁/2` and so
  `|lam - 2 ^ q| < ε₁`.  As `ε₁ > 0` is arbitrary, `lam = 2 ^ q`.
* Conclude countability from `lam ∈ Set.range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ))` and
  `Set.countable_range` (`Countable ℚ`). -/
theorem clusterSet_countable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (h1 : ∀ c : Fin k → ℝ, WilkiesDesign.CG.C4a.PBOne Y c) :
    (Work.WilC4aU.ClusterSet Y).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ)))
  rintro lam ⟨c, hcl⟩
  have hnz : ¬ ZeroSect Y c := not_zeroSect_of_unbounded (unbounded_of_ratioCluster hcl)
  rcases (pbOne_iff Y c).mp (h1 c) with hz | ⟨q, a, ha, hasym⟩
  · exact absurd hz hnz
  · refine ⟨q, ?_⟩
    have hmain : ∀ ε₁ > (0 : ℝ), |lam - (2 : ℝ) ^ (q : ℝ)| < ε₁ := by
      intro ε₁ hε₁
      have h2q : (0 : ℝ) < (2 : ℝ) ^ (q : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have hδ : 0 < min (|a| / 2) (ε₁ * |a| / (8 * (2 : ℝ) ^ (q : ℝ))) := by
        apply lt_min
        · exact half_pos (abs_pos.mpr ha)
        · exact div_pos (mul_pos hε₁ (abs_pos.mpr ha)) (by positivity)
      obtain ⟨R, hR⟩ := hasym _ hδ
      have hMpos : (0 : ℝ) < max R 1 + 1 := by
        have := le_max_right R 1; linarith
      have hεpos : 0 < min (ε₁ / 2) (1 / (max R 1 + 1)) :=
        lt_min (by linarith) (one_div_pos.mpr hMpos)
      obtain ⟨x, y, y', hεx, hxy, hy, hxy', hsq⟩ := hcl _ hεpos
      have hεle : min (ε₁ / 2) (1 / (max R 1 + 1)) ≤ 1 / (max R 1 + 1) := min_le_right _ _
      have hb := threshold_le_of_eps_mul hεpos hεle hεx
      have hRx : R ≤ x := hb.1
      have hx1 : 1 ≤ x := hb.2
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      have h2xR : R ≤ 2 * x := by linarith
      have hratio : |y' / y - lam| < ε₁ / 2 :=
        lt_of_lt_of_le ((sq_lt_sq_iff_ratio hy hεpos).mp hsq) (min_le_left _ _)
      exact cluster_estimate ha hε₁ hxpos (hR x y hRx hxy) (hR (2 * x) y' h2xR hxy') hratio
    have heq : lam = (2 : ℝ) ^ (q : ℝ) := by
      by_contra hne
      have hpos : 0 < |lam - (2 : ℝ) ^ (q : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hne)
      exact absurd (hmain _ hpos) (lt_irrefl _)
    exact heq.symm

end Work.WilC4aU
