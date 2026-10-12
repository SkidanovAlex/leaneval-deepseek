import ChallengeDeps
import Submission.Work.BoseFixB1S.meanFieldAbbrev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxSupport_count_eq` — the indicator count collapse

If `Φ` is supported (a.e. on `abox n ℓ`) inside the small box `B(u)`
(`mfSupp`), then the linear-in-`n` count form collapses:

`Σᵢ ∫_{Λᴺ} 1_{B(u)}(x_i) Φ(x)² dx = n ∫_{Λᴺ} Φ(x)² dx`.

Indeed `1_{B(u)}(x_i)·Φ(x)² = Φ(x)²` for a.e. `x` (`mfSupp` directly when
`Φ x ≠ 0`, and both sides vanish when `Φ x = 0`), so each of the `n`
integrands equals `mfI = ∫ Φ²`.
-/

namespace Work.BoseFixB1S

open MeasureTheory

theorem boxSupport_count_eq {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hsupp : Work.BoseFixB1S.mfSupp v μ n Φ u) :
    (∑ i : Fin n,
        ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator (fun _ => (1 : ℝ)) (x i)
            * (Φ x) ^ 2)
      = (n : ℝ) * Work.BoseFixB1S.mfI v μ n Φ := by
  -- Each of the `n` summands is `mfI v μ n Φ`: the indicator equals `1` on the
  -- support of `Φ` and both integrands vanish off it.
  have hterm : ∀ i : Fin n,
      (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u).indicator
                (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        = Work.BoseFixB1S.mfI v μ n Φ := by
    intro i
    rw [Work.BoseFixB1S.mfI]
    refine integral_congr_ae ?_
    refine hsupp.mono ?_
    intro x hx
    by_cases hmem : x i ∈ Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
    · simp [Set.indicator_of_mem hmem]
    · -- off the box, `mfSupp` forces `Φ x = 0`
      have hΦ : Φ x = 0 := by
        by_contra hc
        exact hmem (hx hc i)
      simp [Set.indicator_of_notMem hmem, hΦ]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end Work.BoseFixB1S
