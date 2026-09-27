import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLC7.isPlaqueAlgebra_smulMS
import Submission.Work.EKLComp.atom_comap

/-!
# Transport of plaque algebras and shapes along a `U`-translation

Elementary facts used in the proof of the local left quasi-invariance of a system of leafwise
measures (`Work.EKLRelCross.leftQuasiInv`), where the `condexp` field of `IsLeafwise` is applied
to a plaque algebra `(Z, m)` and to its translate under the point transformation `y ↦ u • y`,
`u ∈ U`.
-/

open scoped MeasureTheory

set_option linter.unusedVariables false

namespace Work.EKLRelCross

open Work.EKLContract

/-- `atom m` is constant on its atoms. -/
theorem atom_eq_of_mem_atom {m : MeasurableSpace X3} {x y : X3} (hy : y ∈ atom m x) :
    atom m y = atom m x := by
  have hy' : ∀ s : Set X3, MeasurableSet[m] s → x ∈ s → y ∈ s := by
    intro s hs hxs
    rw [atom, Set.mem_sInter] at hy
    exact hy s ⟨hs, hxs⟩
  have hx' : ∀ s : Set X3, MeasurableSet[m] s → y ∈ s → x ∈ s := by
    intro s hs hys
    by_contra hxs
    exact hy' sᶜ hs.compl hxs hys
  refine le_antisymm ?_ ?_
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, hy' s hs.1 hs.2⟩
  · intro z hz
    rw [atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, hx' s hs.1 hs.2⟩

/-- **Plaque algebras pull back along a `U`-translation** (this is
`Work.EKLC7.isPlaqueAlgebra_smulMS` at `u⁻¹`, unwound). -/
theorem isPlaqueAlgebra_comap_smul {U : Subgroup SL3} {u : SL3} (hu : u ∈ U) {Z : Set X3}
    {m : MeasurableSpace X3} (hpla : IsPlaqueAlgebra U Z m) :
    IsPlaqueAlgebra U ((fun x : X3 => u • x) ⁻¹' Z)
      (MeasurableSpace.comap (fun x : X3 => u • x) m) := by
  have h := Work.EKLC7.isPlaqueAlgebra_smulMS (U := U) (u := u⁻¹) (U.inv_mem hu) hpla
  have hcarrier : Work.EKLC7.smulSt u⁻¹ Z = (fun x : X3 => u • x) ⁻¹' Z := by
    ext y
    rw [Work.EKLC7.smulSt_mem, Set.mem_preimage, inv_inv]
  have hms : Work.EKLC7.smulMS u⁻¹ m = MeasurableSpace.comap (fun x : X3 => u • x) m := by
    rw [Work.EKLC7.smulMS, inv_inv]
  rwa [hcarrier, hms] at h

/-- **The shape at the translated point.**  If `u • x` lies in the atom of `m` at `x`, the shape
at `u • x` is the right translate by `u⁻¹` of the shape at `x`. -/
theorem shape_smul_right {U : Subgroup SL3} {u : SL3} (hu : u ∈ U) {m : MeasurableSpace X3}
    {x : X3} (hatom : u • x ∈ atom m x) :
    shape m U (u • x) = (fun g : SL3 => g * u⁻¹) '' shape m U x := by
  have hatomeq : atom m (u • x) = atom m x := atom_eq_of_mem_atom hatom
  ext g
  rw [shape, Set.mem_ofPred_eq, shape, Set.mem_image]
  constructor
  · rintro ⟨hgU, hgatom⟩
    refine ⟨g * u, ⟨U.mul_mem hgU hu, ?_⟩, by group⟩
    have hx : (g * u) • x = g • (u • x) := by rw [mul_smul]
    rw [hx, ← hatomeq]
    exact hgatom
  · rintro ⟨h, ⟨hhU, hhatom⟩, rfl⟩
    refine ⟨U.mul_mem hhU (U.inv_mem hu), ?_⟩
    have hx : (h * u⁻¹) • (u • x) = h • x := by rw [mul_smul, inv_smul_smul]
    rw [hx, hatomeq]
    exact hhatom

end Work.EKLRelCross
