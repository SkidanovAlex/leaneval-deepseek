import Mathlib
import Submission.Work.Peluse.Prop36SW.GenDefs

namespace Work.Prop36SW

open Work.Peluse.UControl

theorem dirFamG_bound {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} (p : ι → P → ℤ)
    (a : P) (b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ) (M₁' H S : ℕ) (C : ℝ)
    (hb : b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1))
    (hp : ∀ s : Work.Peluse.UControl.Slot ι (fun _ => 1), |(p s.1 a : ℝ)| ≤ C)
    (hcard : Fintype.card ι ≤ S) :
    ∀ (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ)
      (j : Fin (Fintype.card (Work.Peluse.UControl.FamIdx kω))),
      ∀ z ∈ Work.Peluse.Prop36SW.pDirFamG p M₁' a b
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j),
        |(z : ℝ)| ≤ (M₁' : ℝ) * ((S : ℝ) * (C * ((H : ℝ) + 1))) := by
  intro kω j z hz
  rw [Work.Peluse.Prop36SW.pDirFamG, Work.Peluse.Prop36SW.pDirG,
      Work.Peluse.arithIcc] at hz
  rw [Finset.mem_image] at hz
  obtain ⟨n, hn, rfl⟩ := hz
  rw [Finset.mem_Icc] at hn
  obtain ⟨hn1, hnL⟩ := hn
  set ω : Finset (Slot ι (fun _ => 1)) := ((Fintype.equivFin (FamIdx kω)).symm j).1.1 with hω
  have hne : ω.Nonempty := ((Fintype.equivFin (FamIdx kω)).symm j).1.2
  obtain ⟨s0, hs0⟩ := hne
  have hC : 0 ≤ C := le_trans (abs_nonneg (p s0.1 a : ℝ)) (hp s0)
  have hmem2 : ∀ x : Slot ι (fun _ => 1), b x ∈ Finset.Ioo (-(↑(H + 1) : ℤ)) (↑(H + 1) : ℤ) := by
    have hmem := hb
    rwa [Work.Peluse.UControl.paramBox, Fintype.mem_piFinset] at hmem
  have hbs0 : ∀ s : Slot ι (fun _ => 1), |(b s : ℝ)| ≤ (H : ℝ) + 1 := by
    intro s
    have h2 := hmem2 s
    rw [Finset.mem_Ioo] at h2
    obtain ⟨h1, h2⟩ := h2
    have h1' : ((-((H : ℤ) + 1)) : ℤ) ≤ b s := le_of_lt h1
    have h2' : b s ≤ ((H : ℤ) + 1) := le_of_lt h2
    rw [abs_le]
    exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
  have hterm : ∀ s ∈ ω, |(p s.1 a : ℝ) * (b s : ℝ)| ≤ C * ((H : ℝ) + 1) := by
    intro s hs
    calc |(p s.1 a : ℝ) * (b s : ℝ)| = |(p s.1 a : ℝ)| * |(b s : ℝ)| := abs_mul _ _
      _ ≤ C * ((H : ℝ) + 1) := mul_le_mul (hp s) (hbs0 s) (abs_nonneg _) hC
  have hbnd : |(∑ s ∈ ω, (p s.1 a : ℝ) * (b s : ℝ))| ≤ (S : ℝ) * (C * ((H : ℝ) + 1)) := by
    have hright : (0:ℝ) ≤ C * ((H : ℝ) + 1) := mul_nonneg hC (by positivity)
    calc |∑ s ∈ ω, (p s.1 a : ℝ) * (b s : ℝ)|
        ≤ ∑ s ∈ ω, |(p s.1 a : ℝ) * (b s : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ ω, C * ((H : ℝ) + 1) := Finset.sum_le_sum hterm
      _ = (ω.card : ℝ) * (C * ((H : ℝ) + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S : ℝ) * (C * ((H : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right _ hright
          have h1 : (ω.card : ℝ) ≤ (Fintype.card (Slot ι (fun _ => 1)) : ℝ) := by
            exact_mod_cast Finset.card_le_univ ω
          have h2 : Fintype.card (Slot ι (fun _ => 1)) = Fintype.card ι := by
            simp [Slot, Fintype.card_sigma]
          rw [h2] at h1
          exact h1.trans (by exact_mod_cast hcard)
  have hcast : (((∑ s ∈ ω, p s.1 a * b s) * (n : ℤ) : ℤ) : ℝ)
      = (∑ s ∈ ω, (p s.1 a : ℝ) * (b s : ℝ)) * (n : ℝ) := by
    rw [Int.cast_mul, Int.cast_sum]; push_cast; ring_nf
  rw [hcast, abs_mul]
  have hnR : (n : ℝ) ≤ (M₁' : ℝ) := by exact_mod_cast hnL
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ))]
  calc (|∑ s ∈ ω, (p s.1 a : ℝ) * (b s : ℝ)|) * (n : ℝ)
      ≤ ((S : ℝ) * (C * ((H : ℝ) + 1))) * (M₁' : ℝ) :=
        mul_le_mul hbnd hnR (by positivity) (by positivity)
    _ = (M₁' : ℝ) * ((S : ℝ) * (C * ((H : ℝ) + 1))) := by ring_nf

end Work.Prop36SW
