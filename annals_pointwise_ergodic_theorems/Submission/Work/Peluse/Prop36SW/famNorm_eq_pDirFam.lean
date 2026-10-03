import Mathlib
import Submission.Work.Peluse.Prop36SW.pDir_eq_dir_gen
import Submission.Work.Peluse.Prop36SW.pDirEqDir

namespace Work.Peluse.Prop36SW

/-- **Reindexing the direction family of a box *norm* (not just its power) along an equivalence.**

`boxNorm t Q S f` is the `2^t`-th root of `boxNormPow t Q S f`, so an equality of the powers at
*equal* cardinalities transfers to the norms themselves.  This is the `boxNorm`-level companion of
`Work.Peluse.Prop36SW.boxNormPow_family_equiv`. -/
lemma boxNorm_family_equiv {ι ι' : Type} [Fintype ι] [Fintype ι'] (φ : ι ≃ ι')
    (Q : ι → Finset ℤ) (e : ι ≃ Fin (Fintype.card ι)) (e' : ι' ≃ Fin (Fintype.card ι'))
    (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNorm (Fintype.card ι) (fun i => Q (e.symm i)) S f
      = Work.Peluse.boxNorm (Fintype.card ι') (fun i => Q (φ.symm (e'.symm i))) S f := by
  have hcard : Fintype.card ι = Fintype.card ι' := Fintype.card_congr φ
  simp only [Work.Peluse.boxNorm]
  rw [boxNormPow_family_equiv φ Q e e' hcard S f, hcard]

/-- **Peluse's `famNorm` at the peeled level is the ladder's `pDirFam`.**

`D.famNorm`-shaped box norm at the level `ℓ+1` — the directions `D.dir d c (ℓ+1) w (padUpdate D ℓ al
s)`, `w ∈ I_{ℓ+1}`, evaluated on the parameter family obtained from `al : D.Idx (ℓ+1)` and the new
level-`(ℓ+1)` parameters `s` — is the same box norm with the ladder's index type
`FamIdx (k := fun _ : D.S (ℓ+1) => 1) (fun _ => 1)` and the ladder's direction family `pDirFam` built
from the level-`ℓ` slot coefficients `(d - ℓ)·dir d c ℓ (par ℓ t) (pad (ℓ+1) al)`.

Both sides have the same number of directions (`FamIdx` at multiplicity one is the nonempty subsets
of the slots, i.e. `I_{ℓ+1}`), and the two direction families agree pointwise by the identity
`pDir_eq_dir_gen` (which is `sumSlotDir_gen` read through `pDir`); the transfer between the two
enumerations is `boxNormPow_family_equiv` (via `boxNorm_family_equiv`). -/
theorem famNorm_eq_pDirFam (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (ℓ : ℕ) (H N : ℕ) (f : ℤ → ℂ)
    (al : D.Idx (ℓ + 1)) (s : D.S (ℓ + 1) → ℤ) :
    Work.Peluse.boxNorm (Fintype.card (D.I (ℓ + 1)))
        (fun i => Work.Peluse.arithIcc (D.dir d c (ℓ + 1) ((Fintype.equivFin (D.I (ℓ + 1))).symm i)
            (Work.Peluse.padUpdate D ℓ al s)) H) (Work.Peluse.symIcc N) f
      = Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx (k := fun _ : D.S (ℓ + 1) => 1)
            (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => 1)))
          (fun i => Work.Peluse.UControl.pDirFam (p := fun (t : D.S (ℓ + 1)) (_ : Fin 0 → ℤ) =>
              ((d : ℤ) - (ℓ : ℤ)) * D.dir d c ℓ (D.par ℓ t) (D.pad (ℓ + 1) al))
            H (fun _ => (0 : ℤ)) (fun t => s t.1)
            ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (k := fun _ : D.S (ℓ + 1) => 1)
              (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => 1))).symm i)) (Work.Peluse.symIcc N) f := by
  classical
  obtain ⟨e, he⟩ := Work.Peluse.Prop36SW.pDir_eq_dir_gen D d c ℓ al s H
  have hmain := boxNorm_family_equiv
    (φ := (Equiv.sigmaUnique (Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1))
        (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => Fin 1)).trans e)
    (Q := fun j : Work.Peluse.UControl.FamIdx (k := fun _ : D.S (ℓ + 1) => 1)
        (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => 1) =>
        Work.Peluse.UControl.pDirFam (p := fun (t : D.S (ℓ + 1)) (_ : Fin 0 → ℤ) =>
            ((d : ℤ) - (ℓ : ℤ)) * D.dir d c ℓ (D.par ℓ t) (D.pad (ℓ + 1) al))
          H (fun _ => (0 : ℤ)) (fun t => s t.1) j)
    (e := Fintype.equivFin _) (e' := Fintype.equivFin _) (S := Work.Peluse.symIcc N) (f := f)
  have hfun : (fun i : Fin (Fintype.card (D.I (ℓ + 1))) =>
        (fun j : Work.Peluse.UControl.FamIdx (k := fun _ : D.S (ℓ + 1) => 1)
          (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => 1) =>
          Work.Peluse.UControl.pDirFam (p := fun (t : D.S (ℓ + 1)) (_ : Fin 0 → ℤ) =>
              ((d : ℤ) - (ℓ : ℤ)) * D.dir d c ℓ (D.par ℓ t) (D.pad (ℓ + 1) al))
            H (fun _ => (0 : ℤ)) (fun t => s t.1) j)
          (((Equiv.sigmaUnique (Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1))
              (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => Fin 1)).trans e).symm
            ((Fintype.equivFin (D.I (ℓ + 1))).symm i)))
      = (fun i => Work.Peluse.arithIcc (D.dir d c (ℓ + 1) ((Fintype.equivFin (D.I (ℓ + 1))).symm i)
            (Work.Peluse.padUpdate D ℓ al s)) H) := by
    funext i
    show Work.Peluse.UControl.pDir (p := fun (t : D.S (ℓ + 1)) (_ : Fin 0 → ℤ) =>
              ((d : ℤ) - (ℓ : ℤ)) * D.dir d c ℓ (D.par ℓ t) (D.pad (ℓ + 1) al))
          H (fun _ => (0 : ℤ)) (fun t => s t.1)
          (((Equiv.sigmaUnique (Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1))
              (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => Fin 1)).trans e).symm
            ((Fintype.equivFin (D.I (ℓ + 1))).symm i)).1
        = Work.Peluse.arithIcc (D.dir d c (ℓ + 1) ((Fintype.equivFin (D.I (ℓ + 1))).symm i)
            (Work.Peluse.padUpdate D ℓ al s)) H
    rw [he _]
    congr 1
    have h1 : (((Equiv.sigmaUnique (Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1))
              (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => Fin 1)).trans e).symm
            ((Fintype.equivFin (D.I (ℓ + 1))).symm i))
        = (Equiv.sigmaUnique (Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1))
              (fun _ : Work.Peluse.UControl.SlotSet (D.S (ℓ + 1)) (fun _ => 1) => Fin 1)).symm
            (e.symm ((Fintype.equivFin (D.I (ℓ + 1))).symm i)) := rfl
    rw [h1, Equiv.sigmaUnique_symm_apply, Equiv.apply_symm_apply]
    rfl
  rw [hfun] at hmain
  exact hmain.symm

end Work.Peluse.Prop36SW
