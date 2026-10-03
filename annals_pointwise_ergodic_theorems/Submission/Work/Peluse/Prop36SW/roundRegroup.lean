import Mathlib
import Submission.Work.Peluse.Prop36SW.regroupDefs
import Submission.Work.Peluse.Prop36SW.sigmaFiberBoxNorm

set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-! ## The round's regrouping step (session 8)

The round `n+1 → n` of the §5 chain must reindex the box-norm family indexed by the slots
`Σ s : D.S (n+2), Fin (t s)` onto the family `FamIdx (regroupKω D (n+1) t)`: the slot `s` is
grouped into the parent `parSet D (n+1) s`, and the direction of the group is the sum of the
level-`n` directions over the parent (`dir_step_eq_sum`).  The averaged quantities are the same
because the flat box `Abox D (n+2) H` splits as `Abox D (n+1) H` times the ladder's parameter box
(`parBox_succ_average` + `average_piIcc_eq_average_paramBox`).
-/

/-- **The regrouping identity at one box point.**  For a lower parameter `a''` of the new state and
a level-`(n+1)` parameter `b` on the canonical slots, the hypothesis family of the state at slot
level `n+1` equals the conclusion family of the state at slot level `n`. -/
theorem roundFamily_eq (D : IdxDatum) (d : ℕ) (c : ℤ) (n Λ M₁ M₂ H N : ℕ) (γw : ℝ)
    (t : D.S (n + 2) → ℕ) (a'' : Fin (nD D (n + 1)) → ℤ) (ha'' : a'' ∈ Abox D (n + 1) H)
    (b : Slot (D.S (n + 1)) (fun _ => 1) → ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow (Fintype.card (Σ s : D.S (n + 2), Fin (t s)))
        (fun i => Work.Peluse.arithIcc
          ((Λ : ℤ) * ((d : ℤ) - ((n + 1 : ℕ) : ℤ)) *
            D.dir d c (n + 1) (D.par (n + 1)
              ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1)
            (padUpdate D n (decD D (n + 1) a'') (fun x => b (slotOf x))))
          (peelL M₁ M₂ γw)) (Work.Peluse.symIcc N) f
      = Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t)))
        (fun i => pDirFamG (pFlat D d c n (Λ * (d - (n + 1)))) (peelL M₁ M₂ γw) a'' b
          ((Fintype.equivFin (FamIdx (regroupKω D (n + 1) t))).symm i))
        (Work.Peluse.symIcc N) f := by
  classical
  obtain ⟨al, _hal, hal_eq⟩ := mem_Abox_iff.mp ha''
  have hdec : decD D (n + 1) a'' = al := by rw [← hal_eq, decD_encD]
  rw [hdec]
  set G : SlotSet (D.S (n + 1)) (fun _ => 1) → Finset ℤ := fun ω =>
    Work.Peluse.arithIcc
      (∑ s ∈ ω.1, pFlat D d c n (Λ * (d - (n + 1))) s.1 (encD D (n + 1) al) * b s)
      (peelL M₁ M₂ γw) with hG
  have hL : Work.Peluse.boxNormPow (Fintype.card (Σ s : D.S (n + 2), Fin (t s)))
        (fun i => Work.Peluse.arithIcc
          ((Λ : ℤ) * ((d : ℤ) - ((n + 1 : ℕ) : ℤ)) *
            D.dir d c (n + 1) (D.par (n + 1)
              ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1)
            (padUpdate D n al (fun x => b (slotOf x))))
          (peelL M₁ M₂ γw)) (Work.Peluse.symIcc N) f
      = Work.Peluse.boxNormPow (Fintype.card (Σ s : D.S (n + 2), Fin (t s)))
          (fun i => G (parSet D (n + 1)
            ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1))
          (Work.Peluse.symIcc N) f := by
    refine congrArg (fun F : Fin (Fintype.card (Σ s : D.S (n + 2), Fin (t s))) → Finset ℤ =>
      Work.Peluse.boxNormPow (Fintype.card (Σ s : D.S (n + 2), Fin (t s))) F
        (Work.Peluse.symIcc N) f) ?_
    funext i
    rw [hG]
    refine congrArg (fun z : ℤ => Work.Peluse.arithIcc z (peelL M₁ M₂ γw)) ?_
    rw [dir_step_eq_sum D d c n Λ al b
      ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1]
    show (∑ s' ∈ (D.par (n + 1)
          ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1).1,
        pFlat D d c n (Λ * (d - (n + 1))) s' (encD D (n + 1) al) * b (slotOf s'))
      = ∑ s ∈ ((parSet D (n + 1)
          ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1)).1,
        pFlat D d c n (Λ * (d - (n + 1))) s.1 (encD D (n + 1) al) * b s
    rw [show ((parSet D (n + 1)
            ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1)).1
          = ((D.par (n + 1)
              ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1)).1.image
              (fun x => slotOf x) from rfl]
    rw [sum_image_slotOf]
  rw [hL]
  rw [sigmaFiberBoxNorm (g := parSet D (n + 1)) (k := t) (k' := regroupKω D (n + 1) t)
      (regroupKω_eq_fiber_sum D (n + 1) t) G (Work.Peluse.symIcc N) f]
  refine congrArg (fun F : Fin (Fintype.card (FamIdx (regroupKω D (n + 1) t))) → Finset ℤ =>
    Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t))) F
      (Work.Peluse.symIcc N) f) ?_
  funext i
  rw [hG, hal_eq]
  rfl

/-- **The regrouping of the averaged box norms.**  The average of the hypothesis's box-norm powers
over the flat box `Abox D (n+2) H` equals the double average of the conclusion's box-norm powers
over `Abox D (n+1) H` and the ladder's parameter box. -/
theorem roundRegroup_avg (D : IdxDatum) (d : ℕ) (c : ℤ) (n Λ M₁ M₂ H N : ℕ)
    (hH : M₂ = H + 1) (f : ℤ → ℂ) (γw : ℝ) (t : D.S (n + 2) → ℕ) :
    ((Abox D (n + 2) H).card : ℝ)⁻¹ *
        ∑ a ∈ Abox D (n + 2) H,
          Work.Peluse.boxNormPow (Fintype.card (Σ s : D.S (n + 2), Fin (t s)))
            (fun i => Work.Peluse.arithIcc
              (pFlat D d c (n + 1) Λ
                ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1 a)
              (peelL M₁ M₂ γw)) (Work.Peluse.symIcc N) f
      = ((Abox D (n + 1) H).card : ℝ)⁻¹ *
        ((paramBox (k := fun _ : D.S (n + 1) => 1) M₂).card : ℝ)⁻¹ *
        ∑ a'' ∈ Abox D (n + 1) H, ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) M₂,
          Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t)))
            (fun i => pDirFamG (pFlat D d c n (Λ * (d - (n + 1)))) (peelL M₁ M₂ γw) a'' b
              ((Fintype.equivFin (FamIdx (regroupKω D (n + 1) t))).symm i))
            (Work.Peluse.symIcc N) f := by
  classical
  set Φ : ((j' : ℕ) → D.S j' → ℤ) → ℝ := fun A =>
    Work.Peluse.boxNormPow (Fintype.card (Σ s : D.S (n + 2), Fin (t s)))
      (fun i => Work.Peluse.arithIcc
        ((Λ : ℤ) * ((d : ℤ) - ((n + 1 : ℕ) : ℤ)) *
          D.dir d c (n + 1) (D.par (n + 1)
            ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1) A)
        (peelL M₁ M₂ γw)) (Work.Peluse.symIcc N) f with hΦ
  have key6 : ∀ a'' ∈ Abox D (n + 1) H, ∀ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
      Φ (padUpdate D n (decD D (n + 1) a'') (fun x => b (slotOf x)))
        = Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t)))
            (fun i => pDirFamG (pFlat D d c n (Λ * (d - (n + 1)))) (peelL M₁ M₂ γw) a'' b
              ((Fintype.equivFin (FamIdx (regroupKω D (n + 1) t))).symm i))
            (Work.Peluse.symIcc N) f := by
    intro a'' ha'' b _
    rw [hΦ]
    exact roundFamily_eq D d c n Λ M₁ M₂ H N γw t a'' ha'' b f
  have hstep1 : ((Abox D (n + 2) H).card : ℝ)⁻¹ *
        ∑ a ∈ Abox D (n + 2) H,
          Work.Peluse.boxNormPow (Fintype.card (Σ s : D.S (n + 2), Fin (t s)))
            (fun i => Work.Peluse.arithIcc
              (pFlat D d c (n + 1) Λ
                ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1 a)
              (peelL M₁ M₂ γw)) (Work.Peluse.symIcc N) f
      = ((Abox D (n + 2) H).card : ℝ)⁻¹ *
          ∑ a ∈ Abox D (n + 2) H, Φ (D.pad (n + 2) (decD D (n + 2) a)) := by
    rw [show (∑ a ∈ Abox D (n + 2) H,
            Work.Peluse.boxNormPow (Fintype.card (Σ s : D.S (n + 2), Fin (t s)))
              (fun i => Work.Peluse.arithIcc
                (pFlat D d c (n + 1) Λ
                  ((Fintype.equivFin (Σ s : D.S (n + 2), Fin (t s))).symm i).1 a)
                (peelL M₁ M₂ γw)) (Work.Peluse.symIcc N) f)
          = ∑ a ∈ Abox D (n + 2) H, Φ (D.pad (n + 2) (decD D (n + 2) a)) from
        Finset.sum_congr rfl (fun a _ => by rw [hΦ]; rfl)]
  have hstep2 := average_Abox_eq_average_parBox D (n + 2) H (fun a => Φ (D.pad (n + 2) a))
  have hstep3 := parBox_succ_average D n H Φ
  have hstep4 := (average_Abox_eq_average_parBox D (n + 1) H
    (fun al => ((Fintype.piFinset (fun _ : D.S (n + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ))).card : ℝ)⁻¹ *
      ∑ s ∈ Fintype.piFinset (fun _ : D.S (n + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ)),
        Φ (padUpdate D n al s))).symm
  have hstep5 : ((Abox D (n + 1) H).card : ℝ)⁻¹ *
          ∑ a'' ∈ Abox D (n + 1) H,
            ((Fintype.piFinset (fun _ : D.S (n + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ))).card : ℝ)⁻¹ *
              ∑ s ∈ Fintype.piFinset (fun _ : D.S (n + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ)),
                Φ (padUpdate D n (decD D (n + 1) a'') s)
      = ((Abox D (n + 1) H).card : ℝ)⁻¹ *
          ∑ a'' ∈ Abox D (n + 1) H,
            ((paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
              ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Φ (padUpdate D n (decD D (n + 1) a'') (fun x => b (slotOf x))) := by
    rw [show (∑ a'' ∈ Abox D (n + 1) H,
            ((Fintype.piFinset (fun _ : D.S (n + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ))).card : ℝ)⁻¹ *
              ∑ s ∈ Fintype.piFinset (fun _ : D.S (n + 1) => Finset.Icc (-(H : ℤ)) (H : ℤ)),
                Φ (padUpdate D n (decD D (n + 1) a'') s))
          = ∑ a'' ∈ Abox D (n + 1) H,
            ((paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
              ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Φ (padUpdate D n (decD D (n + 1) a'') (fun x => b (slotOf x))) from
        Finset.sum_congr rfl (fun a'' _ => avg_piIcc_eq_avg_paramBox (ι := D.S (n + 1)) H
          (fun b => Φ (padUpdate D n (decD D (n + 1) a'') b)))]
  have hstep6 : ((Abox D (n + 1) H).card : ℝ)⁻¹ *
          ∑ a'' ∈ Abox D (n + 1) H,
            ((paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
              ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Φ (padUpdate D n (decD D (n + 1) a'') (fun x => b (slotOf x)))
      = ((Abox D (n + 1) H).card : ℝ)⁻¹ *
          ∑ a'' ∈ Abox D (n + 1) H,
            ((paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
              ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t)))
                  (fun i => pDirFamG (pFlat D d c n (Λ * (d - (n + 1)))) (peelL M₁ M₂ γw)
                    a'' b ((Fintype.equivFin (FamIdx (regroupKω D (n + 1) t))).symm i))
                  (Work.Peluse.symIcc N) f := by
    rw [show (∑ a'' ∈ Abox D (n + 1) H,
            ((paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
              ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Φ (padUpdate D n (decD D (n + 1) a'') (fun x => b (slotOf x))))
          = ∑ a'' ∈ Abox D (n + 1) H,
            ((paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
              ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t)))
                  (fun i => pDirFamG (pFlat D d c n (Λ * (d - (n + 1)))) (peelL M₁ M₂ γw)
                    a'' b ((Fintype.equivFin (FamIdx (regroupKω D (n + 1) t))).symm i))
                  (Work.Peluse.symIcc N) f from
        Finset.sum_congr rfl (fun a'' ha'' => by
          rw [show (∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Φ (padUpdate D n (decD D (n + 1) a'') (fun x => b (slotOf x))))
              = ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t)))
                  (fun i => pDirFamG (pFlat D d c n (Λ * (d - (n + 1)))) (peelL M₁ M₂ γw)
                    a'' b ((Fintype.equivFin (FamIdx (regroupKω D (n + 1) t))).symm i))
                  (Work.Peluse.symIcc N) f from
            Finset.sum_congr rfl (fun b hb => key6 a'' ha'' b hb)])]
  have hfinal : ((Abox D (n + 1) H).card : ℝ)⁻¹ *
          ∑ a'' ∈ Abox D (n + 1) H,
            ((paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
              ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
                Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t)))
                  (fun i => pDirFamG (pFlat D d c n (Λ * (d - (n + 1)))) (peelL M₁ M₂ γw)
                    a'' b ((Fintype.equivFin (FamIdx (regroupKω D (n + 1) t))).symm i))
                  (Work.Peluse.symIcc N) f
      = ((Abox D (n + 1) H).card : ℝ)⁻¹ *
        ((paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1)).card : ℝ)⁻¹ *
        ∑ a'' ∈ Abox D (n + 1) H, ∑ b ∈ paramBox (k := fun _ : D.S (n + 1) => 1) (H + 1),
          Work.Peluse.boxNormPow (Fintype.card (FamIdx (regroupKω D (n + 1) t)))
            (fun i => pDirFamG (pFlat D d c n (Λ * (d - (n + 1)))) (peelL M₁ M₂ γw) a'' b
              ((Fintype.equivFin (FamIdx (regroupKω D (n + 1) t))).symm i))
            (Work.Peluse.symIcc N) f := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a'' _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [mul_assoc]
  rw [hstep1, hstep2, hstep3, hstep4, hstep5, hstep6, hfinal, hH]

theorem roundRegroup (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (n : ℕ)
    (Λ M₁ M₂ H N : ℕ) (hH : M₂ = H + 1) (f : ℤ → ℂ) (γ γw : ℝ)
    (t : D.S (n + 2) → ℕ)
    (hpar : ∀ i : D.I (n + 1), ∃ s : D.S (n + 2), D.par (n + 1) s = i)
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
            (Work.Peluse.symIcc N) f := by
  refine le_trans h ?_
  rw [roundRegroup_avg D d c n Λ M₁ M₂ H N hH f γw t]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum (fun a'' _ => Finset.sum_le_sum (fun b _ => ?_))
  exact boxNormPow_le_boxNorm' hf1 (SupportIn.symIcc hfs)

end

end Work.Peluse.Prop36SW
