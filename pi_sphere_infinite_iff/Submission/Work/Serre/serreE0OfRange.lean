import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE0Range

/-!
# E0 from its range form

`Work.Serre.SerreE0` follows from `Work.Serre.SerreE0Range` (**proved**, file `serreE0Range.lean`)
together with the single degree-`0` statement that the augmentation `H₀(X;ℚ) → H₀(*;ℚ)` is an
isomorphism for connected `X`.  In degrees `> 0` both sides of the augmentation are zero objects,
so *any* map between them is an isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-- In `ModuleCat ℚ`, a morphism whose source and target are subsingleton modules is an
isomorphism (both are then nonempty subsingletons, so the map is bijective). -/
theorem isIso_of_subsingleton_module {M N : ModuleCat ℚ} (hM : Subsingleton (↥M))
    (hN : Subsingleton (↥N)) (f : M ⟶ N) : IsIso f := by
  haveI := hM
  haveI := hN
  refine IsIso.mk ⟨(0 : N ⟶ M), ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _
  · apply ModuleCat.hom_ext
    ext y
    exact Subsingleton.elim _ _

/-- **E0 from the range form and the `H₀` computation.** -/
theorem serreE0OfRange : SerreE0OfRange := by
  intro hRange hZero X _ x₀ hwc n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hZero X x₀ (hwc 0)
  · have hZ : RatVanishingBelow X (n + 1) := hRange X x₀ n (fun i _ => hwc i)
    have hX : IsZero (ratH (TopCat.of X) n) := hZ n hn (Nat.lt_succ_self n)
    have hP : IsZero (ratH (TopCat.of PUnit) n) :=
      Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of PUnit) n hn
    exact isIso_of_subsingleton_module (subsingleton_of_isZero hX) (subsingleton_of_isZero hP) _

/-- **E0** (from `serreE0Range` and the `H₀` statement of the previous lemma). -/
theorem serreE0_of_range (hZero : ∀ (X : Type) [TopologicalSpace X] (x₀ : X),
    Subsingleton (HomotopyGroup (Fin 0) X x₀) → IsIso (ratHomologyMap (toPoint X) 0)) :
    SerreE0 :=
  serreE0OfRange serreE0Range hZero

end

end Work.Serre
