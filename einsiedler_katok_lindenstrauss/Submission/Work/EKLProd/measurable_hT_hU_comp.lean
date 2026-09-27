import Mathlib
import Submission.Work.EKLProd.prodPlaqueAux
import Submission.Work.EKLProd.ProdFlowerDefs

/-!
# Measurability of the coordinates of the decomposition `H = T · U`

The chosen `T`- and `U`-coordinates `hT T U`, `hU T U` of `ProdPlaqueDefs` are defined by a
`Classical.choice`, so measurability is not automatic.  On `H = T·U` however they coincide with
the *continuous* coordinates `tCoord`, `uCoord` of `prodPlaqueAux` (built from the open mapping
theorem for the locally compact group `H`), hence composing them with any measurable
`f : X₃ → H` is measurable. -/

open MeasureTheory Topology
open Work.EKLContract

namespace Work.EKLProd

theorem measurable_hT_hU_comp {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    {f : Work.EKLContract.X3 → Work.EKLContract.SL3} (hf : Measurable f)
    (hfH : ∀ x : Work.EKLContract.X3, f x ∈ (H : Set Work.EKLContract.SL3)) :
    Measurable (fun x : Work.EKLContract.X3 => Work.EKLProd.hT T U (f x)) ∧
      Measurable (fun x : Work.EKLContract.X3 => Work.EKLProd.hU T U (f x)) := by
  classical
  let F : Work.EKLContract.X3 → ↥H := fun x => ⟨f x, hfH x⟩
  have hF : Measurable F := Measurable.subtype_mk hf
  have htcm : Measurable (tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc) :=
    (tCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc).measurable
  have hucm : Measurable (uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc) :=
    (uCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc).measurable
  -- the chosen coordinates agree with the continuous `tCoord`, `uCoord` on `H`
  have hbridgeT : ∀ x, hT T U (f x) =
      ((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc (F x)) : SL3) := by
    intro x
    have hex : ∃ a ∈ T, ∃ b ∈ U, f x = a * b := hcop (f x) (hfH x)
    have hdec : hT T U (f x) * hU T U (f x) = f x := hT_mul_hU hex
    have h1 := (eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc (F x)
      (hT_mem hex) (hU_mem hex) hdec.symm).1
    exact (congrArg Subtype.val h1).symm
  have hbridgeU : ∀ x, hU T U (f x) =
      ((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc (F x)) : SL3) := by
    intro x
    have hex : ∃ a ∈ T, ∃ b ∈ U, f x = a * b := hcop (f x) (hfH x)
    have hdec : hT T U (f x) * hU T U (f x) = f x := hT_mul_hU hex
    have h2 := (eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc (F x)
      (hT_mem hex) (hU_mem hex) hdec.symm).2
    exact (congrArg Subtype.val h2).symm
  constructor
  · have heq : (fun x : Work.EKLContract.X3 => Work.EKLProd.hT T U (f x)) =
        fun x => ((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc (F x)) : SL3) :=
      funext hbridgeT
    rw [heq]
    exact continuous_subtype_val.measurable.comp (htcm.comp hF)
  · have heq : (fun x : Work.EKLContract.X3 => Work.EKLProd.hU T U (f x)) =
        fun x => ((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc (F x)) : SL3) :=
      funext hbridgeU
    rw [heq]
    exact continuous_subtype_val.measurable.comp (hucm.comp hF)

end Work.EKLProd
