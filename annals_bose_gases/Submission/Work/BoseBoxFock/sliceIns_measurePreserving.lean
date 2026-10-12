import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sliceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sliceIns_measurePreserving`

The coordinate insertion `Φ ((y,u),x'') = insertCoord2 p y u x''` of `sliceDefs`, regarded as a
measurable equivalence `sliceIns p hp` between `(E3 × E3) × (ι → E3)` and `Fin n → E3`
(`ι = {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}`), **preserves the product of the box measures**:
the source measure `(boxMeas ℓ × boxMeas ℓ) × Measure.pi (fun _ : ι => boxMeas ℓ)` is pushed
forward to `Measure.pi (fun _ : Fin n => boxMeas ℓ)`.

The mathematical content is the π-system computation on coordinate boxes
`Set.pi Set.univ s` (`s : Fin n → Set E3`): under the insertion this rectangle pulls back to

`(s p.1 ×ˢ s p.2) ×ˢ (Set.pi Set.univ fun i : ι => s i.1)`

(`sliceIns_preimage_pi`, proved from the three coordinate evaluations of the insertion), and the
`Measure.pi`-of-a-product formula (`Measure.pi_pi`, `Measure.prod_prod`) together with the
weight factorisation `prod_slice` of `sliceDefs` match the two sides.  Since both measures are
σ-finite (`Restrict.sigmaFinite`, `Measure.pi`), equality on this generating π-system suffices
(`Measure.pi_eq`).

`sorry`-free.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Coordinate evaluations of the insertion -/

lemma sliceInsFun_apply_fst {n : ℕ} (p : Fin n × Fin n)
    (w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :
    sliceInsFun p w p.1 = w.1.1 := by
  show insertCoord2 p w.1.1 w.1.2 w.2 p.1 = w.1.1
  exact insertCoord2_apply_fst p w

lemma sliceInsFun_apply_snd {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) :
    sliceInsFun p w p.2 = w.1.2 := by
  show insertCoord2 p w.1.1 w.1.2 w.2 p.2 = w.1.2
  exact insertCoord2_apply_snd p hp w

lemma sliceInsFun_apply_rest {n : ℕ} (p : Fin n × Fin n)
    (w : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))
    (i : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2}) :
    sliceInsFun p w i.1 = w.2 i := by
  show insertCoord2 p w.1.1 w.1.2 w.2 i.1 = w.2 i
  exact insertCoord2_apply_rest p w i

/-! ## The pull-back of a coordinate box -/

/-- The preimage of a coordinate box `Set.pi Set.univ s` under the insertion is the product of
the two special coordinates with the box on the remaining coordinates. -/
lemma sliceIns_preimage_pi {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (s : Fin n → Set E3) :
    (sliceInsFun p) ⁻¹' (Set.pi Set.univ s)
      = (s p.1 ×ˢ s p.2) ×ˢ
          (Set.pi Set.univ (fun i : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => s i.1)) := by
  ext w
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
  constructor
  · intro h
    exact ⟨⟨by simpa only [sliceInsFun_apply_fst p w] using h p.1,
            by simpa only [sliceInsFun_apply_snd p hp w] using h p.2⟩,
           fun i => by simpa only [sliceInsFun_apply_rest p w i] using h i.1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩ k
    by_cases hk : k = p.1
    · subst hk; simpa only [sliceInsFun_apply_fst p w] using h1
    · by_cases hk' : k = p.2
      · subst hk'; simpa only [sliceInsFun_apply_snd p hp w] using h2
      · simpa only [sliceInsFun_apply_rest p w ⟨k, hk, hk'⟩] using h3 ⟨k, hk, hk'⟩

/-! ## The insertion preserves the box measure -/

theorem sliceIns_measurePreserving {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) :
    MeasureTheory.MeasurePreserving
      (⇑(Work.BoseBoxFock.sliceIns p hp))
      (((Work.BoseBoxFock.boxMeas ℓ).prod (Work.BoseBoxFock.boxMeas ℓ)).prod
        (MeasureTheory.Measure.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} =>
          Work.BoseBoxFock.boxMeas ℓ)))
      (MeasureTheory.Measure.pi (fun _ : Fin n => Work.BoseBoxFock.boxMeas ℓ)) := by
  refine ⟨(sliceIns p hp).measurable, ?_⟩
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (sliceIns p hp).measurable (MeasurableSet.univ_pi hs)]
  rw [show (⇑(sliceIns p hp)) ⁻¹' Set.pi Set.univ s
      = (s p.1 ×ˢ s p.2) ×ˢ (Set.pi Set.univ fun i : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => s i.1)
      from sliceIns_preimage_pi p hp s]
  rw [Measure.prod_prod, Measure.prod_prod, Measure.pi_pi]
  rw [prod_slice p hp (fun k : Fin n => boxMeas ℓ (s k))]

end Work.BoseBoxFock
