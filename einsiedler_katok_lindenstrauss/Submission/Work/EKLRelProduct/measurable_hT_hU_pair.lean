import Mathlib
import Submission.Work.EKLProd.measurable_hT_hU_comp
import Submission.Work.EKLProd.prodPlaqueAux

/-!
# Measurability of the pair of product coordinates `(hT, hU)` on `SL₃(ℝ)`

The chosen decomposition coordinates `hT T U`, `hU T U` of `EKLProd/ProdPlaqueDefs` are
`Classical.choice`-based.  Nevertheless the *pair* `w ↦ (hT T U w, hU T U w)` is measurable on
all of `SL₃(ℝ)`:

* on the closed subgroup `H = T·U ≤ SL₃(ℝ)` the pair coincides with the continuous coordinate
  maps `tCoord`, `uCoord` of `EKLProd/prodPlaqueAux` (this is the content of
  `hT_eq_tCoord` / `hU_eq_uCoord`, already used in `EKLProd/measurable_hT_hU_comp`);
* off `H` there is no `T`-`U` decomposition at all (`hT_eq_one_of_not_mem` /
  `hU_eq_one_of_not_mem`), so both coordinates take the junk value `1`.

Since `H` is closed, hence Borel, the piecewise description is measurable.
-/

open Work.EKLContract Work.EKLProd

namespace Work.EKLRelProduct

/-! ## The junk value off `H` -/

/-- `w ∉ H` admits no decomposition over `T, U ≤ H`, so `hT` is the junk value `1`. -/
theorem hT_eq_one_of_not_mem {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H) {w : SL3} (hw : w ∉ H) :
    Work.EKLProd.hT T U w = 1 := by
  have h : ¬ (∃ p : SL3 × SL3, p.1 ∈ T ∧ p.2 ∈ U ∧ p.1 * p.2 = w) := by
    rintro ⟨p, hp1, hp2, hpw⟩
    exact hw (hpw ▸ H.mul_mem (hTH hp1) (hUH hp2))
  simp only [Work.EKLProd.hT, Work.EKLProd.decompose, dif_neg h]

/-- `w ∉ H` admits no decomposition over `T, U ≤ H`, so `hU` is the junk value `1`. -/
theorem hU_eq_one_of_not_mem {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H) {w : SL3} (hw : w ∉ H) :
    Work.EKLProd.hU T U w = 1 := by
  have h : ¬ (∃ p : SL3 × SL3, p.1 ∈ T ∧ p.2 ∈ U ∧ p.1 * p.2 = w) := by
    rintro ⟨p, hp1, hp2, hpw⟩
    exact hw (hpw ▸ H.mul_mem (hTH hp1) (hUH hp2))
  simp only [Work.EKLProd.hU, Work.EKLProd.decompose, dif_neg h]

/-! ## The chosen coordinates on `H` are the continuous ones -/

/-- On `H` the chosen `T`-coordinate is the continuous `tCoord`. -/
theorem hT_eq_tCoord {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (a : ↥H) :
    Work.EKLProd.hT T U (a : SL3)
      = ((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc a : ↥T) : SL3) := by
  have hex : ∃ t ∈ T, ∃ u ∈ U, (a : SL3) = t * u := hcop a a.2
  have hdec : Work.EKLProd.hT T U (a : SL3) * Work.EKLProd.hU T U (a : SL3) = (a : SL3) :=
    hT_mul_hU hex
  have h1 := (eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc a
    (hT_mem hex) (hU_mem hex) hdec.symm).1
  exact (congrArg Subtype.val h1).symm

/-- On `H` the chosen `U`-coordinate is the continuous `uCoord`. -/
theorem hU_eq_uCoord {H T U : Subgroup SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set SL3)) (hTc : IsClosed (T : Set SL3)) (hUc : IsClosed (U : Set SL3))
    (a : ↥H) :
    Work.EKLProd.hU T U (a : SL3)
      = ((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc a : ↥U) : SL3) := by
  have hex : ∃ t ∈ T, ∃ u ∈ U, (a : SL3) = t * u := hcop a a.2
  have hdec : Work.EKLProd.hT T U (a : SL3) * Work.EKLProd.hU T U (a : SL3) = (a : SL3) :=
    hT_mul_hU hex
  have h1 := (eq_coords_of hTH hUH hnorm hcop hdisj hHc hTc hUc a
    (hT_mem hex) (hU_mem hex) hdec.symm).2
  exact (congrArg Subtype.val h1).symm

/-! ## Measurability of the two coordinates and of the pair -/

theorem measurable_hT_hU_pair {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3)) :
    Measurable (fun w : Work.EKLContract.SL3 =>
      (Work.EKLProd.hT T U w, Work.EKLProd.hU T U w)) := by
  have hHmeas : MeasurableSet (H : Set SL3) := hHc.measurableSet
  have hTmeas : Measurable (fun w : SL3 => Work.EKLProd.hT T U w) := by
    refine measurable_of_restrict_of_restrict_compl
      (f := fun w : SL3 => Work.EKLProd.hT T U w) (s := (H : Set SL3)) hHmeas ?_ ?_
    · have heq : ((H : Set SL3).domRestrict (fun w : SL3 => Work.EKLProd.hT T U w)) =
          fun a : ↥H => ((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc a : ↥T) : SL3) := by
        funext a
        exact hT_eq_tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc a
      rw [heq]
      exact continuous_subtype_val.measurable.comp
        ((tCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc).measurable)
    · have heq : (fun a : ↥((H : Set SL3)ᶜ) => Work.EKLProd.hT T U (a : SL3)) =
          fun _ => (1 : SL3) := by
        funext a
        exact hT_eq_one_of_not_mem hTH hUH a.2
      have : Measurable (fun a : ↥((H : Set SL3)ᶜ) => Work.EKLProd.hT T U (a : SL3)) := by
        rw [heq]; exact measurable_const
      exact this
  have hUmeas : Measurable (fun w : SL3 => Work.EKLProd.hU T U w) := by
    refine measurable_of_restrict_of_restrict_compl
      (f := fun w : SL3 => Work.EKLProd.hU T U w) (s := (H : Set SL3)) hHmeas ?_ ?_
    · have heq : ((H : Set SL3).domRestrict (fun w : SL3 => Work.EKLProd.hU T U w)) =
          fun a : ↥H => ((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc a : ↥U) : SL3) := by
        funext a
        exact hU_eq_uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc a
      rw [heq]
      exact continuous_subtype_val.measurable.comp
        ((uCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc).measurable)
    · have heq : (fun a : ↥((H : Set SL3)ᶜ) => Work.EKLProd.hU T U (a : SL3)) =
          fun _ => (1 : SL3) := by
        funext a
        exact hU_eq_one_of_not_mem hTH hUH a.2
      have : Measurable (fun a : ↥((H : Set SL3)ᶜ) => Work.EKLProd.hU T U (a : SL3)) := by
        rw [heq]; exact measurable_const
      exact this
  exact Measurable.prod hTmeas hUmeas

end Work.EKLRelProduct
