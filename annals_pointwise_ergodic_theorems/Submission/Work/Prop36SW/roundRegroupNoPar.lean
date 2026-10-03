import Mathlib
import Submission.Work.Peluse.Prop36SW.roundRegroup

namespace Work.Prop36SW

/-- **The round's regrouping step without the surjectivity hypothesis on `D.par`.**

`Work.Peluse.Prop36SW.roundRegroup` states the same conclusion under the extra hypothesis
`hpar : ∀ i : D.I (n + 1), ∃ s : D.S (n + 2), D.par (n + 1) s = i`.  That hypothesis is *not*
used anywhere in its proof: the regrouping identity `roundRegroup_avg` (the equality of the
averaged box-norm powers over `Abox D (n+2) H` and over the double average
`Abox D (n+1) H × paramBox`) holds for every `IdxDatum`, and the passage from the box-norm power
to the box norm is pointwise (`boxNormPow_le_boxNorm'`).  So the conclusion holds with `hpar`
dropped; only the statement is repeated here. -/
theorem roundRegroupNoPar (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (n : ℕ)
    (Λ M₁ M₂ H N : ℕ) (hH : M₂ = H + 1) (f : ℤ → ℂ) (γ γw : ℝ)
    (t : D.S (n + 2) → ℕ)
    (hL : 1 ≤ Work.Peluse.Prop36SW.peelL M₁ M₂ γw) (hγ : 0 < γ)
    (hf1 : ∀ x : ℤ, ‖f x‖ ≤ 1) (hfs : Work.Peluse.SupportIn f N)
    (h : γ ≤ ((Work.Peluse.Prop36SW.Abox D (n + 2) H).card : ℝ)⁻¹ *
        ∑ a ∈ Work.Peluse.Prop36SW.Abox D (n + 2) H,
          Work.Peluse.boxNormPow (Fintype.card (Sigma (fun s : D.S (n + 2) => Fin (t s))))
            (fun i => Work.Peluse.arithIcc
              (Work.Peluse.Prop36SW.pFlat D d c (n + 1) Λ
                ((Fintype.equivFin (Sigma (fun s : D.S (n + 2) => Fin (t s)))).symm i).1 a)
              (Work.Peluse.Prop36SW.peelL M₁ M₂ γw)) (Work.Peluse.symIcc N) f) :
    γ ≤ ((Work.Peluse.Prop36SW.Abox D (n + 1) H).card : ℝ)⁻¹ *
        ((Work.Peluse.UControl.paramBox (k := fun _ : D.S (n + 1) => 1) M₂).card : ℝ)⁻¹ *
        ∑ a'' ∈ Work.Peluse.Prop36SW.Abox D (n + 1) H,
          ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : D.S (n + 1) => 1) M₂,
          Work.Peluse.boxNorm (Fintype.card (Work.Peluse.UControl.FamIdx
              (Work.Peluse.Prop36SW.regroupKω D (n + 1) t)))
            (fun i => Work.Peluse.Prop36SW.pDirFamG
              (Work.Peluse.Prop36SW.pFlat D d c n (Λ * (d - (n + 1)))) (Work.Peluse.Prop36SW.peelL M₁ M₂ γw)
              a'' b
              ((Fintype.equivFin (Work.Peluse.UControl.FamIdx
                (Work.Peluse.Prop36SW.regroupKω D (n + 1) t))).symm i))
            (Work.Peluse.symIcc N) f
:= by
  refine le_trans h ?_
  rw [Work.Peluse.Prop36SW.roundRegroup_avg D d c n Λ M₁ M₂ H N hH f γw t]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum (fun a'' _ => Finset.sum_le_sum (fun b _ => ?_))
  exact Work.Peluse.Prop36SW.boxNormPow_le_boxNorm' hf1 (Work.Peluse.Prop36SW.SupportIn.symIcc hfs)

end Work.Prop36SW
