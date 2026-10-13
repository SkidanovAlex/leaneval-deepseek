import Mathlib

namespace Work.WilC2

/-- If `I` is preconnected in `ℝ`, contains `u`, and does not contain a point `w > u`,
then `I` lies strictly below `w`. -/
theorem preconnected_subset_Iio {I : Set ℝ} (hI : IsPreconnected I) {u w : ℝ}
    (hu : u ∈ I) (huw : u < w) (hw : w ∉ I) : I ⊆ Set.Iio w := by
  intro x hx
  rw [Set.mem_Iio]
  by_contra hxw
  rw [not_lt] at hxw
  exact hw ((hI.ordConnected.out hu hx) ⟨le_of_lt huw, hxw⟩)

theorem exists_cut_mem {s : Finset (Set ℝ)} (hpre : ∀ I ∈ s, IsPreconnected I)
    {u v w : ℝ} (hu : u ∈ ⋃₀ (s : Set (Set ℝ))) (hv : v ∈ ⋃₀ (s : Set (Set ℝ)))
    (huw : u < w) (hwv : w < v) (hw : w ∉ ⋃₀ (s : Set (Set ℝ))) :
    ∃ I ∈ s, u < (sSup I + sInf {x ∈ ⋃₀ (s : Set (Set ℝ)) | sSup I < x}) / 2 ∧
      (sSup I + sInf {x ∈ ⋃₀ (s : Set (Set ℝ)) | sSup I < x}) / 2 < v := by
  classical
  set U : Set ℝ := ⋃₀ (s : Set (Set ℝ)) with hUdef
  -- a member of `s` containing `u` (necessarily contained in `(-∞, w)`)
  obtain ⟨I₀, hI₀s, hI₀u⟩ := Set.mem_sUnion.mp hu
  have hwI₀ : w ∉ I₀ := fun h => hw (Set.mem_sUnion.mpr ⟨I₀, hI₀s, h⟩)
  have hI₀sub : I₀ ⊆ Set.Iio w := preconnected_subset_Iio (hpre I₀ hI₀s) hI₀u huw hwI₀
  have hI₀mem : I₀ ∈ s.filter (fun J => J ⊆ Set.Iio w ∧ J.Nonempty) :=
    Finset.mem_filter.mpr ⟨hI₀s, hI₀sub, ⟨u, hI₀u⟩⟩
  -- `I` maximises `sSup` among the nonempty members below `w`
  obtain ⟨I, hImem, hImax⟩ := Finset.exists_max_image
    (s.filter (fun J => J ⊆ Set.Iio w ∧ J.Nonempty)) (fun J => sSup J) ⟨I₀, hI₀mem⟩
  obtain ⟨hIs, hIsub, hIne⟩ := Finset.mem_filter.mp hImem
  have hσw : sSup I ≤ w := csSup_le hIne (fun b hb => le_of_lt (Set.mem_Iio.mp (hIsub hb)))
  have hσv : sSup I < v := lt_of_le_of_lt hσw hwv
  have hvS : v ∈ {x ∈ U | sSup I < x} := ⟨hv, hσv⟩
  have hSne : ({x ∈ U | sSup I < x} : Set ℝ).Nonempty := ⟨v, hvS⟩
  have hτv : sInf {x ∈ U | sSup I < x} ≤ v :=
    csInf_le ⟨sSup I, fun y hy => le_of_lt hy.2⟩ hvS
  refine ⟨I, hIs, ?_, by linarith⟩
  rcases lt_or_ge u (sSup I) with hcase | hcase
  · -- `u < sSup I` : both branches are easy
    have hτge : sSup I ≤ sInf {x ∈ U | sSup I < x} :=
      le_csInf hSne (fun y hy => le_of_lt hy.2)
    linarith
  · -- `u = sSup I` : the infimum of the points of `U` above `sSup I` is `≥ w`
    have hu_le : u ≤ sSup I := by
      have hle : sSup I₀ ≤ sSup I := hImax I₀ hI₀mem
      have hbdd : BddAbove I₀ := ⟨w, fun y hy => le_of_lt (Set.mem_Iio.mp (hI₀sub hy))⟩
      exact le_trans (le_csSup hbdd hI₀u) hle
    have hB : sSup I = u := le_antisymm hcase hu_le
    -- no point of `U` lies strictly between `u` and `w`
    have hno : ∀ x ∈ U, u < x → x < w → False := by
      intro x hxU hux hxw
      obtain ⟨J, hJs, hxJ⟩ := Set.mem_sUnion.mp hxU
      have hJw : w ∉ J := fun h => hw (Set.mem_sUnion.mpr ⟨J, hJs, h⟩)
      have hJsub : J ⊆ Set.Iio w := preconnected_subset_Iio (hpre J hJs) hxJ hxw hJw
      have hJmem : J ∈ s.filter (fun K => K ⊆ Set.Iio w ∧ K.Nonempty) :=
        Finset.mem_filter.mpr ⟨hJs, hJsub, ⟨x, hxJ⟩⟩
      have hle : sSup J ≤ sSup I := hImax J hJmem
      have hbddJ : BddAbove J := ⟨w, fun y hy => le_of_lt (Set.mem_Iio.mp (hJsub hy))⟩
      have hxle : x ≤ sSup J := le_csSup hbddJ hxJ
      have : x ≤ u := by rw [← hB]; exact le_trans hxle hle
      linarith
    have hτw : w ≤ sInf {x ∈ U | sSup I < x} :=
      le_csInf hSne (fun y hy => by
        by_contra hcon
        rw [not_le] at hcon
        exact hno y hy.1 (by rw [← hB]; exact hy.2) hcon)
    linarith

end Work.WilC2
