import Mathlib
import Submission.Work.WilC4aA.Defs

open Filter Set

namespace Work.WilC4aA

/-- **Factorization of an analytic function at `0`.**  If `t` is analytic at `0` with `t 0 = 0` and
strictly positive on a punctured right-neighbourhood of `0`, then there is an order `N ≥ 1` and an
analytic `u` with `u 0 > 0` (hence `u > 0` near `0` on the right) such that `t s = s ^ N * u s`
eventually on `0⁺`.

The order `N` is the order of vanishing `analyticOrderAt t 0`, and the leading coefficient `u 0` is
positive precisely because `t` is positive on the right. -/
theorem analytic_factor {t : ℝ → ℝ} (ht : AnalyticAt ℝ t 0) (ht0 : t 0 = 0)
    (hpos : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t s) :
    ∃ (N : ℕ) (u : ℝ → ℝ), 1 ≤ N ∧ AnalyticAt ℝ u 0 ∧ 0 < u 0 ∧
      (∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < u s) ∧
      t =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun s => s ^ N * u s) := by
  -- `t` does not vanish identically near `0`, since it is positive on the right.
  have hntop : analyticOrderAt t 0 ≠ ⊤ := by
    intro h
    have hz : ∀ᶠ z in nhdsWithin (0 : ℝ) (Set.Ioi 0), t z = 0 :=
      (analyticOrderAt_eq_top.mp h).filter_mono nhdsWithin_le_nhds
    obtain ⟨s, hs1, hs2⟩ := (hpos.and hz).exists
    rw [hs2] at hs1
    exact absurd hs1 (lt_irrefl 0)
  -- Factorization `t z = z ^ n • g z` with `g` analytic and `g 0 ≠ 0`.
  obtain ⟨g, hg, hg0, hfg⟩ := ht.analyticOrderAt_ne_top.mp hntop
  -- The order of vanishing is nonzero because `t 0 = 0`.
  have hne : analyticOrderAt t 0 ≠ 0 := ht.analyticOrderAt_ne_zero.mpr ht0
  have hn0 : analyticOrderNatAt t 0 ≠ 0 := by
    intro hn
    refine hne ?_
    have h1 : ((analyticOrderNatAt t 0 : ℕ) : ℕ∞) = analyticOrderAt t 0 :=
      Nat.cast_analyticOrderNatAt hntop
    rw [hn] at h1
    simpa using h1.symm
  have hn1 : 1 ≤ analyticOrderNatAt t 0 := Nat.one_le_iff_ne_zero.mpr hn0
  -- Restrict the factorization to the right-neighbourhood of `0`.
  have hf' : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      t s = s ^ analyticOrderNatAt t 0 * g s := by
    have h : t =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun z => (z - 0) ^ analyticOrderNatAt t 0 • g z) :=
      hfg.filter_mono nhdsWithin_le_nhds
    filter_upwards [h] with z hz
    simpa [sub_zero, smul_eq_mul] using hz
  -- `g` is positive on the right, because `s ^ n > 0` there.
  have hgpos_ev : ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < g s := by
    filter_upwards [hpos, hf', self_mem_nhdsWithin] with s hps hfe hs
    rw [hfe] at hps
    exact pos_of_mul_pos_right hps (le_of_lt (pow_pos hs _))
  -- Hence the leading coefficient `g 0` is nonnegative (continuity of `g` at `0`), and nonzero.
  have hge : 0 ≤ g 0 := by
    refine ge_of_tendsto (f := g) (x := nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_ ?_
    · exact hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hgpos_ev] with s hs using le_of_lt hs
  exact ⟨analyticOrderNatAt t 0, g, hn1, hg, lt_of_le_of_ne hge (Ne.symm hg0), hgpos_ev, hf'⟩

end Work.WilC4aA
