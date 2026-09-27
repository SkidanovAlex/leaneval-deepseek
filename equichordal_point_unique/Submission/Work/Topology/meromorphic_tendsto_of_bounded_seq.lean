import Mathlib

namespace Work.Topology

/-- A meromorphic function which is bounded along a sequence tending to the centre is analytic
there, and the limit along the punctured neighbourhood filter is the limit along the sequence.

Route: if the order of `f` at `0` were negative, `f` would tend to the cobounded filter
(`tendsto_cobounded_iff_meromorphicOrderAt_neg`), hence `‖f (t n)‖ → ∞`, contradicting the
convergence of `f (t n)`; so the order is nonnegative, `0` is not a pole, `f` extends analytically
to `0`, and its value there is the limit of `f (t n)`. -/
theorem meromorphic_tendsto_of_bounded_seq {f : ℂ → ℂ} {t : ℕ → ℂ} {B : ℂ}
    (hf : MeromorphicAt f 0) (ht : Filter.Tendsto t Filter.atTop (nhds 0))
    (ht0 : ∀ n, t n ≠ 0) (hfB : Filter.Tendsto (fun n => f (t n)) Filter.atTop (nhds B)) :
    Filter.Tendsto f (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (nhds B) := by
  -- The sequence is eventually in the punctured neighbourhood filter.
  have ht' : Filter.Tendsto t Filter.atTop (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ht, Filter.Eventually.of_forall (fun n => by simp [ht0 n])⟩
  -- The order at `0` is nonnegative: a negative order would send `f (t n)` to infinity.
  have hnonneg : 0 ≤ meromorphicOrderAt f 0 := by
    by_contra hneg
    have hneg : meromorphicOrderAt f 0 < 0 := not_le.mp hneg
    have hcob : Filter.Tendsto f (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (Bornology.cobounded ℂ) :=
      tendsto_cobounded_of_meromorphicOrderAt_neg hneg
    have h1 : Filter.Tendsto (fun n => ‖f (t n)‖) Filter.atTop Filter.atTop :=
      (tendsto_norm_atTop_iff_cobounded).2 (hcob.comp ht')
    have h2 : Filter.Tendsto (fun n => ‖f (t n)‖) Filter.atTop (nhds ‖B‖) := hfB.norm
    exact not_tendsto_atTop_of_tendsto_nhds h2 h1
  -- A nonnegative order gives a limit `c` along the punctured neighbourhood, and `c = B`
  -- by uniqueness against the sequence.
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf hnonneg
  have hct : Filter.Tendsto (fun n => f (t n)) Filter.atTop (nhds c) := hc.comp ht'
  rw [tendsto_nhds_unique hct hfB] at hc
  exact hc

end Work.Topology
