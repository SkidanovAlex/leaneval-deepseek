import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.ofatObstruction_edges
import Submission.Work.Drive.stripCrosscutAvoidingO_of_isClosed_finite_fibre
import Submission.Work.Drive.isClosed_OFatR
import Submission.Work.Drive.components_bounded_of_no_spreadQuad

/-!
# `E3` of the lead's `OFat ρ` design: the spread quadrisecant or the crosscut

This module assembles the `E3` gate of `Submission/Work/Drive/NOTES_LEAD_OFat.md` from its two
proved bricks:

* `E3b` — `Work.Drive.ofatObstruction_edges`: the closure of the obstruction set
  `A = OFatObstruction r ρ = OFatR r ρ ∪ TCset r` is bounded away from both edge lines of the strip;
* `E3c` — `Work.Drive.components_bounded_of_no_spreadQuad`: if `r` has no `δ`-spread quadrisecant
  (`δ = min ρ (min (2η) (2s/V))`) then the connected components of `A` are bounded in the first
  coordinate,
* plus `Work.Drive.isClosed_OFatR` (closedness of `OFatR r ρ`, `ρ > 0`) which, together with `E3b`,
  gives closedness of `A` (a limit point of `TCset` in the closure of `A` has strip coordinate in
  `[δ, period - δ]` with `δ > 0`, hence satisfies the *open* strip condition, so it lies in
  `TCset`).

The main statement `Work.Drive.crosscut_or_spreadQuad` is the disjunction consumed by the sweep
endgame (`E1`/`E4` of the lead's message): the knot either has a `δ`-spread quadrisecant, or the
strip carries a bottom–top crosscut avoiding `A`; a crosscut avoiding `TCset` in particular gives
the non-tangency (`hV`/`hntA`/`hntB`) of the sweep, and avoiding `OFatR r ρ` says that every
retained middle of a chord of the arc is *corner-local* (within `ρ` of an endpoint), which the
perpendicular-chamfer analysis (`E1`, `E2`, `G`) removes.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

open scoped unitInterval

/-- **The `E3` crosscut.**  A bottom–top crosscut of the period strip avoiding the obstruction set
`Work.Drive.OFatObstruction r ρ`. -/
def StripCrosscutAvoidingOFat (r : ℝ → Space) (ρ : ℝ) : Prop :=
  ∃ γ : C(I, ℝ × ℝ), (γ 0).2 = 0 ∧ (γ 1).2 = period ∧
    (∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → 0 < (γ t).2 ∧ (γ t).2 < period) ∧
    (∀ t : I, 0 < (t : ℝ) → (t : ℝ) < 1 → γ t ∉ OFatObstruction r ρ)

/-- **`OFatObstruction r ρ` is closed** (`ρ > 0`, no inflections).

`OFatR r ρ` is closed by `Work.Drive.isClosed_OFatR`.  For `TCset r` one observes that its
defining conditions are closed equalities *except* for the open strip condition `0 < q.2 < period`;
a limit point `q` of `TCset r` still satisfies the closed conditions, and since
`closure (OFatObstruction r ρ) ⊆ {z | δ ≤ z.2 ≤ period - δ}` with `δ > 0` (`E3b`,
`Work.Drive.ofatObstruction_edges`) it satisfies the strip condition strictly, so `q ∈ TCset r`. -/
theorem isClosed_OFatObstruction {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    {ρ : ℝ} (hρ : 0 < ρ) :
    IsClosed (OFatObstruction r ρ) := by
  have hcrosscont : Continuous fun p : Space × Space => cross3 p.1 p.2 := by
    have h := Commons.Analysis.Calculus.ContDiff.crossProduct (s := Set.univ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (u := fun p : Space × Space => p.1)
      (v := fun p : Space × Space => p.2) (by fun_prop) (by fun_prop)
    rw [contDiffOn_univ] at h
    exact h.continuous
  have hchord : Continuous fun q : ℝ × ℝ => r (q.1 + q.2) - r q.1 :=
    (hr.continuous.comp (continuous_fst.add continuous_snd)).sub (hr.continuous.comp continuous_fst)
  have hv1 : Continuous fun q : ℝ × ℝ => velocity r q.1 :=
    (hr.smooth.continuous_deriv le_top).comp continuous_fst
  have hv2 : Continuous fun q : ℝ × ℝ => velocity r (q.1 + q.2) :=
    (hr.smooth.continuous_deriv le_top).comp (continuous_fst.add continuous_snd)
  have hC1 : IsClosed {q : ℝ × ℝ |
      cross3 (r (q.1 + q.2) - r q.1) (velocity r q.1) = 0} :=
    isClosed_eq (hcrosscont.comp (hchord.prodMk hv1)) continuous_const
  have hC2 : IsClosed {q : ℝ × ℝ |
      cross3 (r (q.1 + q.2) - r q.1) (velocity r (q.1 + q.2)) = 0} :=
    isClosed_eq (hcrosscont.comp (hchord.prodMk hv2)) continuous_const
  have hC : IsClosed {q : ℝ × ℝ |
      cross3 (r (q.1 + q.2) - r q.1) (velocity r q.1) = 0 ∨
      cross3 (r (q.1 + q.2) - r q.1) (velocity r (q.1 + q.2)) = 0} := hC1.union hC2
  have hTC : IsClosed (TCset r) := by
    rw [← closure_subset_iff_isClosed]
    intro q hq
    have hsub : TCset r ⊆ OFatObstruction r ρ := fun z hz => Or.inr hz
    have hmem : q ∈ closure (OFatObstruction r ρ) := closure_mono hsub hq
    obtain ⟨δ, hδpos, hbound⟩ := ofatObstruction_edges hr hinfl hρ
    obtain ⟨hb1, hb2⟩ := hbound q hmem
    refine ⟨by linarith, by linarith, ?_⟩
    exact (closure_minimal (fun z hz => hz.2.2) hC) hq
  have hfin : IsClosed (OFatR r ρ ∪ TCset r) := (isClosed_OFatR hr hρ).union hTC
  exact hfin

/-- **`E3` of the lead's `OFat ρ` design.**  Either `r` has a `δ`-spread quadrisecant
(`δ = min ρ (min (2η) (2s/V))`), or the period strip carries a bottom–top crosscut avoiding the
obstruction set `OFatObstruction r ρ`.

The proof is the dichotomy of `Work.Drive.components_bounded_of_no_spreadQuad` (`E3c`) together with
`Work.Drive.ofatObstruction_edges` (`E3b`) and the strip-crosscut theorem
`Work.Drive.exists_crosscut_period`. -/
theorem crosscut_or_spreadQuad {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t])
    (htc : TangentChordGP r)
    {ρ t₀ η s V : ℝ} (hρ : 0 < ρ) (hη : 0 < η) (hηP : 2 * η < period)
    (hslab : ∀ u : ℝ, FatMiddle r ρ u → ∀ k : ℤ,
      η < |u - (t₀ + (k : ℝ) * period)|)
    (hs : 0 < s) (hV : 0 < V)
    (hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r a - knotMap r b‖)
    (hlip : ∀ a b : KnotParam, ‖knotMap r a - knotMap r b‖ ≤ V * dist a b) :
    (∃ a b z w : ℝ, SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w ∧
      IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
      IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (w : KnotParam)) ∨
    StripCrosscutAvoidingOFat r ρ := by
  by_cases hspread : ∃ a b z w : ℝ, SpreadQuad (min ρ (min (2 * η) (2 * s / V))) a b z w ∧
      IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
      IsMiddleOnChord r (a : KnotParam) (b : KnotParam) (w : KnotParam)
  · exact Or.inl hspread
  · refine Or.inr ?_
    have hbdd := components_bounded_of_no_spreadQuad hr hρ hη hηP hslab hs hV hsep hlip htc hinfl
      (fun a b z w hδ hmid => hspread ⟨a, b, z, w, hδ, hmid.1, hmid.2⟩)
    obtain ⟨δ, hδpos, hbound⟩ := ofatObstruction_edges hr hinfl hρ
    have hstrip : OFatObstruction r ρ ⊆ {z : ℝ × ℝ | 0 < z.2 ∧ z.2 < period} := by
      intro q hq
      rcases hq with h | h
      · exact ⟨(mem_OFatR_iff.mp h).1, (mem_OFatR_iff.mp h).2.1⟩
      · exact ⟨(mem_TCset_iff.mp h).1, (mem_TCset_iff.mp h).2.1⟩
    have haway : Disjoint (closure (OFatObstruction r ρ))
        {z : ℝ × ℝ | z.2 ≤ 0 ∨ period ≤ z.2} := by
      rw [Set.disjoint_left]
      intro q hq hq'
      obtain ⟨hb1, hb2⟩ := hbound q hq
      rcases hq' with h | h <;> linarith
    obtain ⟨γ, h0, h1, hint⟩ :=
      exists_crosscut_period (isClosed_OFatObstruction hr hinfl hρ) hstrip haway hbdd
    exact ⟨γ, h0, h1, (fun t ht0 ht1 => ⟨(hint t ht0 ht1).1, (hint t ht0 ht1).2.1⟩),
      (fun t ht0 ht1 => (hint t ht0 ht1).2.2)⟩

end Work.Drive
