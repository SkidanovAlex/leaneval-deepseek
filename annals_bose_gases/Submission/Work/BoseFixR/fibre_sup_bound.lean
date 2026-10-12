import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBox.q3kinDiagCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.fibre_sup_bound`

Uniform bound of a continuous `(m+1)`-body state on the image of the *sliding* insertion map
`(z, r) ↦ kcInsN m i (z, r)`, with `z` ranging over the one-particle centred cube `acube ℓ`
and `r` over the `m`-particle centred box `abox m ℓ`.

The argument is compactness: the insertion of a cube point into a box point is a box point
of the `(m+1)`-particle box `abox (m+1) ℓ` (coordinatewise, `kc_insN_apply_same` /
`kc_insN_apply_succ`), and `abox (m+1) ℓ` is compact (`abox_compact`), so `|Φ|` is bounded
there by `IsCompact.exists_bound_of_continuousOn`.
-/

namespace Work.BoseFixR

set_option autoImplicit false

/-- Inserting a cube point `z` at slot `i` of an `m`-particle box point `r` yields an
`(m+1)`-particle box point: coordinate `i` is `z`, and every other coordinate is a
coordinate of `r`. -/
private lemma kcInsN_mem_abox {m : ℕ} {ℓ : ℝ} (i : Fin (m + 1))
    {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ Submission.BoseGases.acube ℓ)
    {r : Fin m → EuclideanSpace ℝ (Fin 3)} (hr : r ∈ Submission.BoseGases.abox m ℓ) :
    Submission.BoseGases.kcInsN m i (z, r) ∈ Submission.BoseGases.abox (m + 1) ℓ := by
  rw [Submission.BoseGases.mem_abox_iff]
  intro j
  by_cases hj : j = i
  · have hcoord : (Submission.BoseGases.kcInsN m i (z, r)) j = z := by
      rw [hj]
      exact Submission.BoseGases.kc_insN_apply_same m i z r
    rw [hcoord]
    exact hz
  · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hj
    have hcoord : (Submission.BoseGases.kcInsN m i (z, r)) j = r j' := by
      rw [← hj']
      exact Submission.BoseGases.kc_insN_apply_succ m i z r j'
    rw [hcoord]
    exact (Submission.BoseGases.mem_abox_iff m ℓ r).mp hr j'

theorem fibre_sup_bound {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Submission.BoseGases.abox m ℓ,
      ∀ z ∈ Submission.BoseGases.acube ℓ,
        |Φ (Submission.BoseGases.kcInsN m i (z, r))| ≤ M := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (m + 1) hℓ).exists_bound_of_continuousOn
    hΦ.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr z hz
  have hb := hC _ (kcInsN_mem_abox i hz hr)
  rw [Real.norm_eq_abs] at hb
  exact le_trans hb (le_max_left _ _)

end Work.BoseFixR
