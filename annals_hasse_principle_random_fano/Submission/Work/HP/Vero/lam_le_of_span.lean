import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic

/-!
# Extracting short successive-minima vectors from a spanning family

If the realifications of a family `v : κ → ℤ^ι` of lattice vectors of norm `≤ B` span (over `ℝ`)
the same space as the realification of the lattice `L ⊆ ℤ^ι`, then `lam L (rk L) ≤ B`: a finite
spanning family with `dim = rk L` contains `rk L` real-linearly independent members, which are
automatically `ℤ`-independent.
-/
set_option autoImplicit false
noncomputable section
open Finset
namespace Work.HP.Vero

/-- Real linear independence of realified integer vectors implies `ℤ`-linear independence. -/
lemma linInd_of_realify {ι : Type*} [Fintype ι] {κ : Type*} {w : κ → (ι → ℤ)}
    (h : LinearIndependent ℝ (fun i => intCastPi (w i))) : LinearIndependent ℤ w := by
  have h' : LinearIndependent ℝ (fun i => algebraMap ℤ ℝ ∘ w i) := h
  exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := w)).mp h'

theorem lam_le_of_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) {κ : Type*} [Fintype κ]
    (v : κ → ι → ℤ) (hv : ∀ i, v i ∈ L)
    (hspan : Submodule.span ℝ (Set.range (fun i => intCastPi (v i)))
              = Submodule.span ℝ (↑(L.map intCastPi) : Set (ι → ℝ)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i, eNorm (v i) ≤ B) :
    lam L (rk L) ≤ B := by
  classical
  set f : κ → (ι → ℝ) := fun i => intCastPi (v i) with hf
  have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = rk L := by
    rw [hf, hspan, Submodule.map_coe, finrank_span_image_intCastPi]
    rfl
  obtain ⟨κ', a, ha_inj, ha_span, ha_li⟩ := exists_linearIndependent' (K := ℝ) f
  haveI : Fintype κ' := Fintype.ofInjective a ha_inj
  have hcard : Fintype.card κ' = rk L := by
    rw [← finrank_span_eq_card ha_li, ha_span, hdim]
  let e := Fintype.equivFin κ'
  let idx : Fin (rk L) → κ' := fun j => e.symm (Fin.cast hcard.symm j)
  have hidx_inj : Function.Injective idx := by
    intro j j' h
    exact Fin.cast_injective hcard.symm (e.symm.injective h)
  have hreal : LinearIndependent ℝ (fun j : Fin (rk L) => intCastPi (v (a (idx j)))) := by
    have h1 : LinearIndependent ℝ (fun j : Fin (rk L) => f (a (idx j))) :=
      ha_li.comp idx hidx_inj
    simpa only [hf] using h1
  refine csInf_le (bddBelow_lamSet L (rk L)) ?_
  exact ⟨hB0, fun j => v (a (idx j)), fun j => hv _, linInd_of_realify hreal, fun j => hB _⟩

end Work.HP.Vero
