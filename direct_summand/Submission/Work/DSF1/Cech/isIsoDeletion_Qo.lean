import Mathlib
import Submission.Work.DSF1.Cech.CechQo
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.isIsoDeletion_Qi

/-!
# The "unit case" of the Čech complex after localizing at a single open

Let `U : ι → X.Opens` be a family of opens of a scheme `X`, `i₀ : ι` an index and `V ≤ U i₀`
an open contained in the `i₀`-th member.  For any presheaf of modules `P` we consider the
presheaf `Qo P V` given by `W ↦ P (W ⊓ V)` (`Work.DSF1.Cech.Qo`).

Inserting the index `i₀` into a simplex does not change the open `Eobj U n x ⊓ V`, because
`Eobj U (n+1) (insIdx U i₀ n x) = Eobj U n x ⊓ U i₀` (`Eobj_insIdx`) and `V ≤ U i₀`; likewise
`⊤ ⊓ V = U i₀ ⊓ V`.  Hence `Qo P V` inverts all cofaces inserting `i₀`, i.e. it satisfies
`IsIsoDeletion U (Qo P V) i₀`, and the unit case (`Work.DSF1.Cech.UnitCase`) applies to the
Čech complex of `Qo P V` along `U`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {X : Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u}

/-- A map of `Qo P V` coming from a map `f : W ⟶ W'` of opens is an isomorphism as soon as `f`
becomes an equality after intersecting with `V`. -/
lemma isIso_Qo_map (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat S) (V : X.Opens)
    {W W' : X.Opensᵒᵖ} (f : W ⟶ W') (h : W'.unop ⊓ V = W.unop ⊓ V) :
    IsIso ((Qo P V).map f) := by
  have hf : (Qo P V).map f =
      P.map (homOfLE (inf_le_inf_right V f.unop.le)).op := rfl
  rw [hf]
  have hg : IsIso (homOfLE (inf_le_inf_right V f.unop.le)) :=
    homOfLE_isIso_of_eq _ h
  have hg' : IsIso ((homOfLE (inf_le_inf_right V f.unop.le)).op) := (isIso_op_iff _).mpr hg
  exact @Functor.map_isIso _ _ _ _ _ _ P _ hg'

/-- **The unit case after localizing at `V ≤ U i₀`.**  The presheaf `W ↦ P (W ⊓ V)` inverts
the cofaces of the Čech nerve which insert the index `i₀`. -/
theorem isIsoDeletion_Qo {U : ι → X.Opens} {P : X.Opensᵒᵖ ⥤ ModuleCat S} {i₀ : ι} {V : X.Opens}
    (hV : V ≤ U i₀) :
    Work.DSF1.Cech.IsIsoDeletion U (Work.DSF1.Cech.Qo P V) i₀ := by
  refine ⟨?_, ?_⟩
  · refine isIso_Qo_map U P V (homOfLE (le_top : U i₀ ≤ ⊤)).op ?_
    show U i₀ ⊓ V = ⊤ ⊓ V
    rw [inf_eq_right.mpr hV, top_inf_eq]
  · intro n x
    refine isIso_Qo_map U P V (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op ?_
    have hf : Eobj U n (((E U).map (SimplexCategory.δ 0).op).f (insIdx U i₀ n x)) = Eobj U n x :=
      congrArg (Eobj U n) (cech_map_delta0_f U i₀ n x)
    have h : Eobj U (n+1) (insIdx U i₀ n x) ⊓ V =
        Eobj U n (((E U).map (SimplexCategory.δ 0).op).f (insIdx U i₀ n x)) ⊓ V := by
      rw [Eobj_insIdx U i₀ n x, hf, inf_assoc, inf_eq_right.mpr hV]
    exact h

end Work.DSF1.Cech
