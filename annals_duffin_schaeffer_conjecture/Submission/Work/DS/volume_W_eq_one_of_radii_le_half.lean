import Mathlib
import Submission.Work.DS.Bridge

/-!
# Full measure of `W ψ` when the radii are at most `1/2` and the series diverges

This is the transport step of Theorem 1: for `ψ : ℕ+ → ℝ≥0` with `ψ q / q ≤ 1/2` for
every `q`, divergence of the series `∑_{q ∈ ℕ+} ψ(q)·φ(q)/q` forces `W ψ` to have full
Lebesgue measure.

The proof composes three ingredients that already exist in the workspace:

* `Submission.DS.volume_W_eq_volume_E`: under the smallness hypothesis `ψ q / q ≤ 1/2`,
  the `[0,1]`-volume of `W ψ` equals the circle volume of `Eapprox ψ`;
* `Submission.duffin_schaeffer_mathlib`: Koukoulopoulos–Maynard, in the form
  `volume (addWellApproximable UnitAddCircle δ) = 1 ↔ ¬ Summable (n ↦ φ(n)·δ n)`,
  applied to `δ = radSeq ψ` (so that `φ(n)·δ n = φ(n)·ψ(n)/n` on `ℕ+`);
* the elementary identification of the two series, `Summable` over `ℕ` of
  `n ↦ φ(n)·radSeq ψ n` versus `Summable` over `ℕ+` of `q ↦ ψ(q)·φ(q)/q`
  (the term at `n = 0` vanishes, and the `ℕ+`-series is the `ℕ`-series with the
  terms reindexed by the bijection `n ↦ n + 1`).
-/

namespace Work.DS

open scoped Nat ENNReal NNReal MeasureTheory Topology

/-- The series `∑ₙ φ(n)·radSeq ψ n` (over `ℕ`) converges if and only if the series
`∑_{q ∈ ℕ+} ψ(q)·φ(q)/q` of the challenge statement converges. -/
private lemma summable_totient_radSeq_iff' (ψ : PNat → NNReal) :
    Summable (fun n : ℕ => (Nat.totient n : ℝ) * Submission.DS.radSeq ψ n) ↔
      Summable (fun q : PNat => (ψ q * (Nat.totient (q : ℕ) : NNReal)) / (q : NNReal)) := by
  let F : ℕ → ℝ := fun n => (Nat.totient n : ℝ) * Submission.DS.radSeq ψ n
  have hF0 : F 0 = 0 := by simp [F, Submission.DS.radSeq]
  -- `F` agrees with its indicator on `{n | 0 < n}` because `F 0 = 0`
  have hIndEq : ({n : ℕ | 0 < n}.indicator F) = F := by
    funext n
    by_cases hn : 0 < n
    · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | 0 < n} from hn)]
    · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | 0 < n} from hn)]
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst hn0
      exact hF0.symm
  -- reindex the sum over `ℕ` as a sum over the subtype `{n | 0 < n} = ℕ+`
  have hsub := summable_subtype_iff_indicator (s := {n : ℕ | 0 < n}) (f := F)
  have step1 : Summable (fun n : ℕ => F n) ↔ Summable (fun q : PNat => F (q : ℕ)) := by
    have h1 : Summable (fun n : ℕ => F n) ↔ Summable ({n : ℕ | 0 < n}.indicator F) := by
      rw [hIndEq]
    have h2 : Summable ({n : ℕ | 0 < n}.indicator F) ↔
        Summable (fun q : PNat => F (q : ℕ)) := hsub.symm
    exact h1.trans h2
  -- rewrite the integrand using `radSeq ψ q = ψ q / q`
  have step2 : (fun q : PNat => F (q : ℕ)) =
      (fun q : PNat =>
        (((ψ q * (Nat.totient (q : ℕ) : NNReal)) / (q : NNReal) : NNReal) : ℝ)) := by
    funext q
    simp only [F]
    rw [Submission.DS.radSeq_eq_coe]
    push_cast
    ring
  rw [step2] at step1
  exact step1.trans NNReal.summable_coe

theorem volume_W_eq_one_of_radii_le_half (ψ : PNat → NNReal)
    (hδ : ∀ q : PNat, ψ q / (q : NNReal) ≤ 1 / 2)
    (hdiv : ¬ Summable (fun q : PNat => (ψ q * (Nat.totient (q : ℕ) : NNReal)) / (q : NNReal))) :
    MeasureTheory.volume (Submission.DS.W ψ) = 1 := by
  have hV : MeasureTheory.volume (Submission.DS.W ψ) =
      MeasureTheory.volume (Submission.DS.Eapprox ψ) :=
    Submission.DS.volume_W_eq_volume_E ψ hδ
  rw [hV]
  refine (Submission.duffin_schaeffer_mathlib (Submission.DS.radSeq ψ)
    (Submission.DS.radSeq_nonneg ψ)).2 ?_
  exact fun h => hdiv ((summable_totient_radSeq_iff' ψ).mp h)

end Work.DS
