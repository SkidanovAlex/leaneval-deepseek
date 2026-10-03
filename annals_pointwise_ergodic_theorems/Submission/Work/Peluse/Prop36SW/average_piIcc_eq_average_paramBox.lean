import Mathlib
import Submission.Work.Peluse.UControl.peluseLadder

namespace Work.Peluse.Prop36SW

/-- **The `k = 1` parameter box is the closed `H`-box.**

When every slot has multiplicity `1`, the slot type `Slot ι (fun _ => 1) = Σ i : ι, Fin 1` is a
copy of `ι` (the second component is a subsingleton), and the parameter box
`paramBox (k := fun _ => 1) (H+1) = ∏_{Slot ι 1} Ioo (-(H+1)) (H+1)` is a copy of the ordinary
product box `∏_{i : ι} Icc (-H) H`.  Indeed `Ioo (-(H+1)) (H+1) = Icc (-H) H` in `ℤ`, and the
bijection is `s ↦ (fun t => s t.1)`.

Hence the average of any `Ψ` over the closed box `∏_{i : ι} Icc (-H) H` (pulled back along
`s ↦ Ψ (fun t => s t.1)`) equals its average over `paramBox (k := fun _ => 1) (H+1)`.  This is the
matching of the §5 chain's state box (`LState`, which averages over `paramBox` with slot
multiplicity `1`) with the plain box of the state's parameters. -/
theorem average_piIcc_eq_average_paramBox {ι : Type} [Fintype ι] [DecidableEq ι] (H : ℕ)
    (Ψ : (Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ) → ℝ) :
    ((Fintype.piFinset (fun _ : ι => Finset.Icc (-(H : ℤ)) (H : ℤ))).card : ℝ)⁻¹ *
        ∑ s ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (-(H : ℤ)) (H : ℤ)), Ψ (fun t => s t.1)
      = ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1)).card : ℝ)⁻¹ *
        ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1), Ψ b := by
  classical
  -- `Ioo (-(H+1)) (H+1) = Icc (-H) H` in `ℤ`
  have hIoo : (Finset.Ioo (-(((H + 1 : ℕ)) : ℤ)) (((H + 1 : ℕ)) : ℤ) : Finset ℤ)
      = Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  -- so `paramBox` is the product box over the slots of the closed box
  have hboxIcc : Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1)
      = Fintype.piFinset (fun _ : Work.Peluse.UControl.Slot ι (fun _ => 1) =>
          Finset.Icc (-(H : ℤ)) (H : ℤ)) := by
    rw [Work.Peluse.UControl.paramBox]
    congr 1
    funext t
    exact hIoo
  -- and reindexing the slots by `ι` (second component is a subsingleton) identifies it with `S`
  have hbox : Fintype.piFinset (fun _ : Work.Peluse.UControl.Slot ι (fun _ => 1) =>
        Finset.Icc (-(H : ℤ)) (H : ℤ))
      = (Fintype.piFinset (fun _ : ι => Finset.Icc (-(H : ℤ)) (H : ℤ))).image
          (fun s t => s t.1) := by
    ext b
    simp only [Fintype.mem_piFinset, Finset.mem_image]
    constructor
    · intro hb
      refine ⟨fun i => b ⟨i, 0⟩, fun i => hb ⟨i, 0⟩, ?_⟩
      funext t
      have ht : (⟨t.1, (0 : Fin 1)⟩ : Work.Peluse.UControl.Slot ι (fun _ => 1)) = t :=
        Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _))
      show b ⟨t.1, (0 : Fin 1)⟩ = b t
      rw [ht]
    · rintro ⟨s, hs, rfl⟩ t
      exact hs t.1
  have hinj : Set.InjOn (fun s : ι → ℤ =>
      fun t : Work.Peluse.UControl.Slot ι (fun _ => 1) => s t.1)
      ↑(Fintype.piFinset (fun _ : ι => Finset.Icc (-(H : ℤ)) (H : ℤ))) := by
    intro s _ s' _ h
    funext i
    have := congrFun h (⟨i, (0 : Fin 1)⟩ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    simpa using this
  have hsum : ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1), Ψ b
      = ∑ s ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (-(H : ℤ)) (H : ℤ)),
          Ψ (fun t => s t.1) := by
    rw [hboxIcc, hbox, Finset.sum_image hinj]
  have hcard : (Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) (H + 1)).card
      = (Fintype.piFinset (fun _ : ι => Finset.Icc (-(H : ℤ)) (H : ℤ))).card := by
    rw [hboxIcc, hbox, Finset.card_image_of_injOn hinj]
  rw [hsum, hcard]

end Work.Peluse.Prop36SW
