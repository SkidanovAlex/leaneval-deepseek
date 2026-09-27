import Mathlib
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.segfunHdist

/-!
# Area L — a local isometry is uniformly isometric onto the whole geodesic segment

`uniformLocal` is the compactness step of the local-isometry argument: if `F : ℍⁿ → ℍⁿ` is a
*local* isometry in the sense that at every point `z` there is a radius `ρ z > 0` on which `F`
preserves `hdist`, then along the unit-speed geodesic segment `segfun u v : [0, hdist u v] → ℍⁿ`
the preservation is *uniform*: there is `δ > 0` such that every pair of parameters `s, s'` of the
segment with `|s - s'| < δ` satisfies `hdist (F (segfun u v s)) (F (segfun u v s')) = |s - s'|`.

The proof is a Lebesgue-number argument.  At each point `t` of the (compact) parameter interval
`[0, hdist u v]` the local-isometry radius `ρ (segfun u v t)` gives an open interval
`(t - ρ, t + ρ)` of parameters on which `F` is isometric with centre `t`.  These intervals cover
`[0, hdist u v]`, and `lebesgue_number_lemma_of_metric` produces `δ > 0` such that the `δ`-ball
around any parameter lies in one of them.  Two parameters within `δ` therefore share a centre `t`,
and `hseg` converts the membership `|s - t| < ρ` into `hdist (segfun u v t) (segfun u v s) < ρ`,
which is exactly the hypothesis of the local isometry at `t`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem uniformLocal {n : ℕ} (F : E n → E n) (u v : E n) (huv : u ≠ v)
    (hloc : ∀ z, ∃ ρ > 0, ∀ x y, hdist z x < ρ → hdist z y < ρ → hdist (F x) (F y) = hdist x y)
    (htri : ∀ x y z : E n, hdist x z ≤ hdist x y + hdist y z)
    (hseg : ∀ s s' : ℝ, s ∈ Set.Icc 0 (hdist u v) → s' ∈ Set.Icc 0 (hdist u v) →
      hdist (segfun u v s) (segfun u v s') = |s - s'|) :
    ∃ δ > 0, ∀ s s' : ℝ, s ∈ Set.Icc 0 (hdist u v) → s' ∈ Set.Icc 0 (hdist u v) →
      |s - s'| < δ → hdist (F (segfun u v s)) (F (segfun u v s')) = |s - s'| := by
  classical
  -- the local isometry radii, chosen at every point
  choose ρ hρpos hρ using hloc
  -- if the parameter interval is empty (`hdist u v < 0`) the claim is vacuous
  rcases lt_or_ge (hdist u v) 0 with hL | hL
  · refine ⟨1, one_pos, fun s s' hs hs' _ => ?_⟩
    exact absurd hs.1 (by linarith [hs.2, hL])
  · -- the open intervals `(t - ρ, t + ρ)`, indexed by the parameters `t` of the segment,
    -- cover the compact parameter interval
    have hcopen : ∀ t : Set.Icc 0 (hdist u v),
        IsOpen (Set.Ioo ((t:ℝ) - ρ (segfun u v (t:ℝ))) ((t:ℝ) + ρ (segfun u v (t:ℝ)))) :=
      fun t => isOpen_Ioo
    have hcover : Set.Icc 0 (hdist u v) ⊆
        ⋃ t : Set.Icc 0 (hdist u v),
          Set.Ioo ((t:ℝ) - ρ (segfun u v (t:ℝ))) ((t:ℝ) + ρ (segfun u v (t:ℝ))) := by
      intro x hx
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      exact Set.mem_Ioo.mpr
        ⟨by linarith [hρpos (segfun u v x)], by linarith [hρpos (segfun u v x)]⟩
    -- Lebesgue number of the cover
    obtain ⟨δ, hδpos, hδ⟩ :=
      lebesgue_number_lemma_of_metric (s := Set.Icc 0 (hdist u v)) isCompact_Icc hcopen hcover
    refine ⟨δ, hδpos, ?_⟩
    intro s s' hs hs' hss'
    -- both parameters lie in one interval of the cover
    obtain ⟨i, hi⟩ := hδ s hs
    have hsball : s ∈ Metric.ball s δ := Metric.mem_ball_self hδpos
    have hs'ball : s' ∈ Metric.ball s δ := by
      rw [Metric.mem_ball, dist_comm, Real.dist_eq]
      exact hss'
    have h1 : s ∈ Set.Ioo ((i:ℝ) - ρ (segfun u v (i:ℝ)))
        ((i:ℝ) + ρ (segfun u v (i:ℝ))) := hi hsball
    have h2 : s' ∈ Set.Ioo ((i:ℝ) - ρ (segfun u v (i:ℝ)))
        ((i:ℝ) + ρ (segfun u v (i:ℝ))) := hi hs'ball
    rw [Set.mem_Ioo] at h1 h2
    -- membership is the distance bound needed by the local isometry at `segfun u v i`
    have hd1 : hdist (segfun u v (i:ℝ)) (segfun u v s) < ρ (segfun u v (i:ℝ)) := by
      rw [hseg (i:ℝ) s i.2 hs, abs_sub_comm, abs_lt]
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hd2 : hdist (segfun u v (i:ℝ)) (segfun u v s') < ρ (segfun u v (i:ℝ)) := by
      rw [hseg (i:ℝ) s' i.2 hs', abs_sub_comm, abs_lt]
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    rw [hρ (segfun u v (i:ℝ)) (segfun u v s) (segfun u v s') hd1 hd2, hseg s s' hs hs']

end Work.Mostow
