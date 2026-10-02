import Mathlib
import Submission.Work.ELTop.PolyCurve.image_cycParam
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-! ## The orientation of the root wake `W₀`

`Work.EL.InArc x a b` is the open counterclockwise arc `(a,b)` on `ℝ/ℤ`, measured by
`Int.fract`.  The two root-portrait angles are `alpha1 = 371/1023` and `alpha2 = 404/1023`, whose
cyclic difference is `11/341`.

The lemma `InArc_W0_orientation` says: if `u` and `v` are each congruent modulo `1` to one of
the two root angles, and *every* point of the arc `(alpha1, alpha2)` lies in the arc `(u, v)`,
then `u ≡ alpha1` and `v ≡ alpha2`.  In other words, the only way for the root wake `W₀` to be
contained in an arc `(u,v)` spanned by root angles is that `(u,v)` has the orientation
`alpha1 → alpha2`.

The proof tests the inclusion at the midpoint `775/2046 = (alpha1+alpha2)/2` of the arc and
inspects the four possible orientations; only `(alpha1, alpha2)` survives. -/

/-- `Int.fract (11/682) = 11/682`. -/
private lemma fract_eq_11_682 : Int.fract ((11:ℝ)/682) = 11/682 := by
  rw [Int.fract_eq_self]; norm_num

/-- `Int.fract (11/341) = 11/341`. -/
private lemma fract_eq_11_341 : Int.fract ((11:ℝ)/341) = 11/341 := by
  rw [Int.fract_eq_self]; norm_num

/-- `Int.fract (-(11/682)) = 671/682`. -/
private lemma fract_neg_11_682 : Int.fract (-(11/682 : ℝ)) = 671/682 := by
  rw [Int.fract_neg (by rw [fract_eq_11_682]; norm_num), fract_eq_11_682]; norm_num

/-- `Int.fract (-(11/341)) = 330/341`. -/
private lemma fract_neg_11_341 : Int.fract (-(11/341 : ℝ)) = 330/341 := by
  rw [Int.fract_neg (by rw [fract_eq_11_341]; norm_num), fract_eq_11_341]; norm_num

/-- The midpoint `775/2046` of the root arc `(alpha1, alpha2)` lies in it. -/
private lemma inArc_th0 : Work.EL.InArc ((775:ℝ)/2046) Work.EL.alpha1 Work.EL.alpha2 := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : (775:ℝ)/2046 - Work.EL.alpha1 = 11/682 := by unfold Work.EL.alpha1; norm_num
  have h2 : Work.EL.alpha2 - Work.EL.alpha1 = 11/341 := by
    unfold Work.EL.alpha1 Work.EL.alpha2; norm_num
  rw [h1, h2, fract_eq_11_682, fract_eq_11_341]
  norm_num

theorem InArc_W0_orientation {u v : ℝ}
    (hu : ∃ m : ℤ, u = Work.EL.alpha1 + m ∨ u = Work.EL.alpha2 + m)
    (hv : ∃ m : ℤ, v = Work.EL.alpha1 + m ∨ v = Work.EL.alpha2 + m)
    (hW : ∀ θ : ℝ, Work.EL.InArc θ Work.EL.alpha1 Work.EL.alpha2 → Work.EL.InArc θ u v) :
    (∃ m : ℤ, u = Work.EL.alpha1 + m) ∧ (∃ m : ℤ, v = Work.EL.alpha2 + m) := by
  have hArc := inArc_th0
  have hWuv := (hW ((775:ℝ)/2046) hArc).2
  -- Determine `u`: it cannot be congruent to `alpha2` modulo `1`.
  have hu1 : ∃ m : ℤ, u = Work.EL.alpha1 + m := by
    rcases hu with ⟨m, hm | hm⟩
    · exact ⟨m, hm⟩
    · exfalso
      rcases hv with ⟨m', hm' | hm'⟩
      · have hf : Int.fract ((775:ℝ)/2046 - u) = 671/682 := by
          rw [hm]
          rw [show (775:ℝ)/2046 - (Work.EL.alpha2 + (m:ℝ)) = (-(11/682):ℝ) - (m:ℝ) by
                unfold Work.EL.alpha2; ring]
          rw [Int.fract_sub_intCast, fract_neg_11_682]
        have ha : Work.EL.arcLen u v = 330/341 := by
          unfold Work.EL.arcLen
          rw [hm, hm']
          rw [show (Work.EL.alpha1 + (m':ℝ)) - (Work.EL.alpha2 + (m:ℝ)) =
                (Work.EL.alpha1 - Work.EL.alpha2) + ((m'-m : ℤ):ℝ) by push_cast; ring]
          rw [Int.fract_add_intCast]
          rw [show Work.EL.alpha1 - Work.EL.alpha2 = (-(11/341):ℝ) by
                unfold Work.EL.alpha1 Work.EL.alpha2; norm_num]
          rw [fract_neg_11_341]
        rw [hf, ha] at hWuv
        norm_num at hWuv
      · have hf : Int.fract ((775:ℝ)/2046 - u) = 671/682 := by
          rw [hm]
          rw [show (775:ℝ)/2046 - (Work.EL.alpha2 + (m:ℝ)) = (-(11/682):ℝ) - (m:ℝ) by
                unfold Work.EL.alpha2; ring]
          rw [Int.fract_sub_intCast, fract_neg_11_682]
        have ha : Work.EL.arcLen u v = 0 := by
          unfold Work.EL.arcLen
          rw [hm, hm']
          rw [show (Work.EL.alpha2 + (m':ℝ)) - (Work.EL.alpha2 + (m:ℝ)) = ((m'-m : ℤ):ℝ) by
                push_cast; ring]
          exact Int.fract_eq_zero_iff.mpr ⟨m' - m, rfl⟩
        rw [hf, ha] at hWuv
        norm_num at hWuv
  refine ⟨hu1, ?_⟩
  -- Now `u ≡ alpha1`; determine `v`: it cannot be congruent to `alpha1` modulo `1`.
  rcases hu1 with ⟨m, hm⟩
  rcases hv with ⟨m', hm' | hm'⟩
  · exfalso
    have hf : Int.fract ((775:ℝ)/2046 - u) = 11/682 := by
      rw [hm]
      rw [show (775:ℝ)/2046 - (Work.EL.alpha1 + (m:ℝ)) = (11/682:ℝ) - (m:ℝ) by
            unfold Work.EL.alpha1; ring]
      rw [Int.fract_sub_intCast, fract_eq_11_682]
    have ha : Work.EL.arcLen u v = 0 := by
      unfold Work.EL.arcLen
      rw [hm, hm']
      rw [show (Work.EL.alpha1 + (m':ℝ)) - (Work.EL.alpha1 + (m:ℝ)) = ((m'-m : ℤ):ℝ) by
            push_cast; ring]
      exact Int.fract_eq_zero_iff.mpr ⟨m' - m, rfl⟩
    rw [hf, ha] at hWuv
    norm_num at hWuv
  · exact ⟨m', hm'⟩

end Work.ELAssembly
