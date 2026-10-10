import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.GlobalCFT.Idele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Ideles

open NK.GlobalCFT
open scoped NumberField

/-- A number field has at least one infinite (archimedean) place: any complex embedding of `K`
gives one. -/
theorem infinitePlace_nonempty (K : Type*) [Field K] [NumberField K] :
    Nonempty (NumberField.InfinitePlace K) := inferInstance

/-- The completion map `K → K_w` at an infinite place is injective (it factors through the
injective embedding `K →+* ℂ` associated with `w`). -/
theorem algebraMap_completion_injective {K : Type*} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) :
    Function.Injective (algebraMap K w.Completion) := by
  intro a b hab
  have h := congrArg (NumberField.InfinitePlace.Completion.extensionEmbedding w) hab
  simp only [NumberField.InfinitePlace.Completion.algebraMap_apply,
    NumberField.InfinitePlace.Completion.extensionEmbedding_coe] at h
  exact RingHom.injective w.embedding h

/-- **The diagonal embedding `Kˣ → 𝕀 K` is injective.**  If two units of `K` have the same image
in the idèle group, then they agree in `K_wˣ` for any (equivalently every) archimedean place `w`.
The completion map `K → K_w` is injective, hence the two units agree in `Kˣ`. -/
theorem globalCFT_principalIdele_injective {K : Type*} [Field K] [NumberField K] :
    Function.Injective (NK.GlobalCFT.Idele.principalIdele K) := by
  intro x y h
  obtain ⟨w⟩ := (infinitePlace_nonempty K)
  have h1 := congrArg (fun z : Idele K => Idele.eval (Place.ofInfinite w) z) h
  rw [Idele.eval_apply, Idele.principalIdele_apply, Idele.eval_apply,
    Idele.principalIdele_apply] at h1
  exact Units.ext (algebraMap_completion_injective w (congrArg Units.val h1))

end NK.GlobalCFT.Ideles
