import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.StemsB.AToolsR
import Submission.Work.Serre.bijAssembly
import Submission.Work.Serre.mvDeltaCupMixed

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

theorem bijective_mixedCup_of_openCover {X : Type} [TopologicalSpace X] (A : Set X)
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (n₀ K : ℕ) (U₀ : Work.Thom.RelCoh ℚ n₀ X A)
    (hlocU : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥U =>
      (Work.Thom.mixedCupC ℚ {y : ↥U | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, X))
          {y : ↥U | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocV : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥V =>
      (Work.Thom.mixedCupC ℚ {y : ↥V | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, X))
          {y : ↥V | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀)))
    (hlocUV : ∀ m : ℕ, m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(U ∩ V) =>
      (Work.Thom.mixedCupC ℚ {y : ↥(U ∩ V) | (y : X) ∈ A} m n₀) x
        ((Work.Thom.relCohMap (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(U ∩ V), X))
          {y : ↥(U ∩ V) | (y : X) ∈ A} A (fun _ hy => hy) ℚ n₀).hom U₀))) :
    ∀ m : ℕ, 1 ≤ m → m + n₀ ≤ K → Function.Bijective (fun x : Work.Thom.Coh ℚ m X =>
      (Work.Thom.mixedCupC ℚ A m n₀) x U₀) :=
  bijective_mixedCup_of_openCover_aux A U V hU hV hcov n₀ K U₀ hlocU hlocV hlocUV
    (fun m => mvDeltaCupMixed (TopCat.of X) A U V hU hV hcov n₀ U₀ m)

end Work.Serre
