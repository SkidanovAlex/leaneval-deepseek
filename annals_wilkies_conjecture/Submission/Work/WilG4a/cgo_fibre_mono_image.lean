import Mathlib
import Submission.Work.WilG4a.LipChartsDefs

namespace Work.WilG4a

/-- The image of an open interval under a function that is continuous on it and strictly
monotone (in either direction) is the open interval between the infimum and the supremum of
the image, provided the image is bounded. -/
lemma image_Ioo_eq_Ioo_csInf_csSup {g : ℝ → ℝ} {a b : ℝ}
    (hne : (Set.Ioo a b).Nonempty) (hcont : ContinuousOn g (Set.Ioo a b))
    (hmono : StrictMonoOn g (Set.Ioo a b) ∨ StrictAntiOn g (Set.Ioo a b))
    (hbl : BddBelow (g '' Set.Ioo a b)) (hba : BddAbove (g '' Set.Ioo a b)) :
    g '' Set.Ioo a b = Set.Ioo (sInf (g '' Set.Ioo a b)) (sSup (g '' Set.Ioo a b)) := by
  have hTne : (g '' Set.Ioo a b).Nonempty := hne.image g
  have hconn : IsConnected (g '' Set.Ioo a b) :=
    ⟨hTne, (isPreconnected_Ioo (a := a) (b := b)).image g hcont⟩
  refine subset_antisymm ?_ (hconn.Ioo_csInf_csSup_subset hbl hba)
  rintro s ⟨t, ht, rfl⟩
  have hta : a < t := ht.1
  have htb : t < b := ht.2
  have ht1 : (a + t) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have ht2 : (t + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hlt1 : (a + t) / 2 < t := by linarith
  have hlt2 : t < (t + b) / 2 := by linarith
  refine ⟨?_, ?_⟩
  · rcases hmono with hm | hm
    · exact lt_of_le_of_lt (csInf_le hbl (Set.mem_image_of_mem g ht1)) (hm ht1 ht hlt1)
    · exact lt_of_le_of_lt (csInf_le hbl (Set.mem_image_of_mem g ht2)) (hm ht ht2 hlt2)
  · rcases hmono with hm | hm
    · exact lt_of_lt_of_le (hm ht ht2 hlt2) (le_csSup hba (Set.mem_image_of_mem g ht2))
    · exact lt_of_lt_of_le (hm ht1 ht hlt1) (le_csSup hba (Set.mem_image_of_mem g ht1))

theorem cgo_fibre_mono_image {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p+1) → ℝ)) (l : Fin p → ℝ) {a b : ℝ}
    (hκ : κ ⊆ Work.WilG4a.strip p) (hfib : Work.WilG4a.fibre κ l = Set.Ioo a b)
    (hne : (Work.WilG4a.fibre κ l).Nonempty)
    (hdiff : ∀ y ∈ Work.WilG4a.fibre κ l, DifferentiableAt ℝ (f l) y)
    (hmono : (∀ y ∈ Work.WilG4a.fibre κ l, 0 < deriv (f l) y) ∨
      (∀ y ∈ Work.WilG4a.fibre κ l, deriv (f l) y < 0))
    (hinto : ∀ x ∈ Work.WilG4a.I, f l x ∈ Work.WilG4a.I) :
    (StrictMonoOn (f l) (Work.WilG4a.fibre κ l) ∨ StrictAntiOn (f l) (Work.WilG4a.fibre κ l)) ∧
    Work.WilG4a.imgFibre κ f l = Set.Ioo (Work.WilG4a.Aend κ f l) (Work.WilG4a.Bend κ f l) ∧
    Work.WilG4a.Aend κ f l < Work.WilG4a.Bend κ f l ∧
    0 ≤ Work.WilG4a.Aend κ f l ∧ Work.WilG4a.Bend κ f l ≤ 1 ∧
    (∀ y ∈ Work.WilG4a.fibre κ l, Work.WilG4a.Aend κ f l < f l y ∧ f l y < Work.WilG4a.Bend κ f l) := by
  have hneIoo : (Set.Ioo a b).Nonempty := by rwa [← hfib]
  have hdiffOn : DifferentiableOn ℝ (f l) (Set.Ioo a b) := fun y hy =>
    (hdiff y (by rwa [hfib])).differentiableWithinAt
  have hcont : ContinuousOn (f l) (Set.Ioo a b) := hdiffOn.continuousOn
  have hmonoOn : StrictMonoOn (f l) (Set.Ioo a b) ∨ StrictAntiOn (f l) (Set.Ioo a b) := by
    rcases hmono with h | h
    · left
      refine strictMonoOn_of_deriv_pos (convex_Ioo a b) hcont ?_
      intro x hx
      rw [interior_Ioo] at hx
      exact h x (by rwa [hfib])
    · right
      refine strictAntiOn_of_deriv_neg (convex_Ioo a b) hcont ?_
      intro x hx
      rw [interior_Ioo] at hx
      exact h x (by rwa [hfib])
  have hsubI' : (f l) '' Set.Ioo a b ⊆ I := by
    rintro s ⟨y, hy, rfl⟩
    have hyfib : y ∈ fibre κ l := by rwa [hfib]
    have hyI : y ∈ I := by
      have h1 : Fin.snoc l y ∈ strip p := hκ hyfib
      simpa [strip] using h1
    exact hinto y hyI
  have hbl : BddBelow ((f l) '' Set.Ioo a b) := ⟨0, fun s hs => le_of_lt (hsubI' hs).1⟩
  have hba : BddAbove ((f l) '' Set.Ioo a b) := ⟨1, fun s hs => le_of_lt (hsubI' hs).2⟩
  have himg : (f l) '' Set.Ioo a b =
      Set.Ioo (sInf ((f l) '' Set.Ioo a b)) (sSup ((f l) '' Set.Ioo a b)) :=
    image_Ioo_eq_Ioo_csInf_csSup hneIoo hcont hmonoOn hbl hba
  have himgFibre_eq : imgFibre κ f l = (f l) '' Set.Ioo a b := by
    rw [← hfib]
    ext s
    simp [imgFibre, fibre]
  have hsubI : imgFibre κ f l ⊆ I := by
    rw [himgFibre_eq]; exact hsubI'
  have himg' : imgFibre κ f l =
      Set.Ioo (sInf (imgFibre κ f l)) (sSup (imgFibre κ f l)) := by
    have h1 : (f l) '' Set.Ioo a b =
        Set.Ioo (sInf (imgFibre κ f l)) (sSup (imgFibre κ f l)) := by
      rw [himg, himgFibre_eq]
    exact himgFibre_eq.trans h1
  have hnonempty_img : (imgFibre κ f l).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    exact ⟨f l y, y, hy, rfl⟩
  have hAB : Aend κ f l < Bend κ f l := by
    obtain ⟨s, hs⟩ := hnonempty_img
    have hs' : s ∈ Set.Ioo (sInf (imgFibre κ f l)) (sSup (imgFibre κ f l)) := by
      rw [← himg']; exact hs
    simpa [Aend, Bend] using lt_trans hs'.1 hs'.2
  have hA0 : 0 ≤ Aend κ f l := by
    show 0 ≤ sInf (imgFibre κ f l)
    exact le_csInf hnonempty_img (fun b hb => le_of_lt (hsubI hb).1)
  have hB1 : Bend κ f l ≤ 1 := by
    show sSup (imgFibre κ f l) ≤ 1
    exact csSup_le hnonempty_img (fun b hb => le_of_lt (hsubI hb).2)
  have hmem' : ∀ y ∈ fibre κ l, Aend κ f l < f l y ∧ f l y < Bend κ f l := by
    intro y hy
    have hyimg : f l y ∈ imgFibre κ f l := ⟨y, hy, rfl⟩
    have h1 : f l y ∈ Set.Ioo (sInf (imgFibre κ f l)) (sSup (imgFibre κ f l)) := by
      rw [← himg']; exact hyimg
    simpa [Aend, Bend] using h1
  refine ⟨?_, ?_, hAB, hA0, hB1, hmem'⟩
  · rcases hmonoOn with hm | hm
    · exact Or.inl (hm.mono (fun y hy => hfib ▸ hy))
    · exact Or.inr (hm.mono (fun y hy => hfib ▸ hy))
  · simpa [Aend, Bend] using himg'

end Work.WilG4a
