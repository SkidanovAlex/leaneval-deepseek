import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.NumberField.Basic
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
import Submission.Work.SSGRoute.TatePoitouRoute.exists_shapiro_c
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IntermediateField

namespace Work.SSGRoute.Sha2Lib

/-- **`L` is generated over `K` by the `k`-conjugates of `MM ∩ L`.**

Let `k ⊆ K ⊆ L ⊆ Ω` with `k ⊆ K` finite Galois, `L/K` an intermediate field, `↥L` a number
field which is Galois over `k`, and `MM ⊆ L` a finite extension of `k` whose normal closure in
`Ω` is (the image of) `L` (`hNc`).  Then `L` is the compositum of the image of `K` and of the
`k`-conjugates of the copy `MM ∩ L` of `MM` inside `L`:

`K · ∏_{τ ∈ Gal(L/k)} τ(MM) = L`.

This is the "`hgenL`" generation hypothesis used to feed `inertia_eq_bot_of_finset_sup`: since
`L` is the normal closure of `MM`, it is generated over `k` by the images of all `k`-embeddings
of `MM`, and (normality of `L/k`) each of those images is a conjugate of `MM ∩ L` inside `L`. -/
theorem normalClosureEqTop {k K Ω : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (MM : IntermediateField k Ω) [FiniteDimensional k ↥MM]
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hMM : MM ≤ L.restrictScalars k)
    (hNc : L.restrictScalars k = IntermediateField.normalClosure k ↥MM Ω)
    [IsScalarTower k ↥L Ω] :
    ((IsScalarTower.toAlgHom k K ↥L).fieldRange ⊔
        ⨆ τ : ↥L ≃ₐ[k] ↥L,
          (MM.comap (IsScalarTower.toAlgHom k ↥L Ω)).map (τ : ↥L →ₐ[k] ↥L)) = ⊤ := by
  classical
  haveI hNormL : Normal k ↥L := IsGalois.to_normal
  -- The inclusion `L ⊆ Ω` and the copy `M = MM ∩ L` of `MM` inside `L`.
  let val : ↥L →ₐ[k] Ω := IsScalarTower.toAlgHom k ↥L Ω
  let M : IntermediateField k ↥L := MM.comap val
  let A : IntermediateField k ↥L := (IsScalarTower.toAlgHom k K ↥L).fieldRange
  let B : IntermediateField k ↥L := ⨆ τ : ↥L ≃ₐ[k] ↥L, M.map (τ : ↥L →ₐ[k] ↥L)
  -- `B` is the normal closure of `M` computed inside the normal extension `↥L/k`.
  have hBnc : B = IntermediateField.normalClosure k ↥M ↥L :=
    (IntermediateField.normalClosure_def'' (F := k) (K := M) (L := ↥L)).symm
  -- `L` is the sup of the images of the `k`-embeddings of `MM`.
  have hNc' : L.restrictScalars k = ⨆ f : ↥MM →ₐ[k] Ω, f.fieldRange := by
    rw [hNc]
    exact normalClosure_def k ↥MM Ω
  -- Every such image lies in `A ⊔ B`.
  have hle : L.restrictScalars k ≤ (A ⊔ B).map val := by
    rw [hNc']
    refine iSup_le fun f => ?_
    have hfL : f.fieldRange ≤ L.restrictScalars k := by
      rw [hNc]
      exact AlgHom.fieldRange_le_normalClosure f
    -- `f` corestricted to `L`.
    let g : ↥MM →ₐ[k] ↥L :=
      f.codRestrict (L.restrictScalars k).toSubalgebra fun x => hfL ⟨x, rfl⟩
    -- the canonical identification of `MM` with its copy `M` inside `L`
    let e : ↥M →ₐ[k] ↥MM := (val.comp M.val).codRestrict MM.toSubalgebra fun m => m.2
    have he_surj : Function.Surjective e := by
      rintro ⟨y, hy⟩
      refine ⟨⟨⟨y, hMM hy⟩, ?_⟩, ?_⟩
      · exact hy
      · exact Subtype.ext rfl
    -- `e` is onto, so it does not change the image of `g`
    have hfr : (g.comp e).fieldRange = g.fieldRange := by
      apply le_antisymm
      · rintro y ⟨m, rfl⟩
        exact ⟨e m, rfl⟩
      · rintro y ⟨x, rfl⟩
        obtain ⟨m, hm⟩ := he_surj x
        exact ⟨m, congrArg g hm⟩
    have hgB : g.fieldRange ≤ B := by
      rw [← hfr, hBnc]
      exact AlgHom.fieldRange_le_normalClosure (g.comp e)
    have hfg : val.comp g = f := by
      ext x
      rfl
    calc f.fieldRange = (g.fieldRange).map val := by
          rw [AlgHom.map_fieldRange g val, hfg]
      _ ≤ B.map val := IntermediateField.map_mono val hgB
      _ ≤ (A ⊔ B).map val := IntermediateField.map_mono val le_sup_right
  -- Conversely the image lies in `L`, and `map val` is injective, so `A ⊔ B = ⊤`.
  have hmain : A ⊔ B = ⊤ := by
    refine IntermediateField.map_injective val ?_
    refine le_antisymm (IntermediateField.map_mono val le_top) ?_
    refine le_trans ?_ hle
    rintro x ⟨y, -, rfl⟩
    exact y.2
  exact hmain

end Work.SSGRoute.Sha2Lib
