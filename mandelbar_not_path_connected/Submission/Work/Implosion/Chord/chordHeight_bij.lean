import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Geometry
import Submission.Work.Implosion.Chord

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Chord

/-- On the open unit interval the chord height is `artanh t / λ`; since `artanh` maps
`(-1,1)` bijectively onto `ℝ` and division by `λ > 0` is a strictly increasing bijection
of `ℝ`, this exhibits `chordHeight λ` as an order isomorphism `(-1,1) ≃ ℝ`. -/
theorem chordHeight_bij (lam : ℝ) (hlam : 0 < lam) :
    StrictMonoOn (chordHeight lam) (Set.Ioo (-1 : ℝ) 1)
      ∧ Set.SurjOn (chordHeight lam) (Set.Ioo (-1 : ℝ) 1) Set.univ := by
  have hch : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, chordHeight lam t = Real.artanh t / lam := by
    intro t ht
    have hI : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [chordHeight, Real.artanh_eq_half_log hI]
    ring
  constructor
  · intro x hx y hy hxy
    rw [hch x hx, hch y hy]
    exact div_lt_div_of_pos_right (Real.artanh_lt_artanh hx.1 hy.2 hxy) hlam
  · intro y _
    obtain ⟨t, ht, htval⟩ := Real.artanh_surjOn (Set.mem_univ (lam * y))
    refine ⟨t, ht, ?_⟩
    rw [hch t ht, htval]
    exact mul_div_cancel_left₀ y (ne_of_gt hlam)

end Work.Implosion.Chord
