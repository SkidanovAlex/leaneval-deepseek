import Mathlib
import Submission.Work.DSEQ0.AugAbSetup
import Submission.Work.DSF1.Sheaf.cechTrivAll_local

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators
set_option backward.isDefEq.respectTransparency false
universe u

/-- The boundary case of the second extra-codegeneracy identity for the
`AddCommGrpCat`-valued Čech complex: `δ₁ ≫ kAb 0 = kTopAb ≫ coaugAb`, the `AddCommGrpCat`
analogue of `Work.DSF1.Cech.KTopSq`.  This is the missing ingredient of the chain-homotopy
identity `homotopy_zeroAb` in degree `0`. -/
lemma KTopSqAbAux {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {i₀ : ι}
    (h : Work.DSEQ0.IsIsoDelAbTop U Q i₀) :
    Work.DSF1.Sheaf.deltaXAb U Q 0 (1 : Fin 2) ≫ Work.DSF1.Sheaf.kAb U Q h.2 0 =
      Work.DSEQ0.kTopAb U Q h ≫ Work.DSEQ0.coaugAb X U Q := by
  apply Limits.Pi.hom_ext
  intro x
  conv_lhs => erw [Category.assoc, Work.DSF1.Sheaf.kAb_comp_π]
  conv_lhs => erw [← Category.assoc, Work.DSF1.Sheaf.cech_delta_comp_πAb U Q 0 (1 : Fin 2)
      (Work.DSF1.Cech.insIdx U i₀ 0 x)]
  conv_rhs => erw [Category.assoc]
  conv_rhs => erw [show coaugAb X U Q ≫
      Limits.Pi.π (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z))) x =
      Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op from
        Limits.Pi.lift_comp_π _ _]
  have hf1 : ((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
      (Work.DSF1.Cech.insIdx U i₀ 0 x) = (fun _ : Fin 1 => i₀) := by
    show (Limits.FormalCoproduct.mapPower (Limits.FormalCoproduct.mk ι U)
        (SimplexCategory.δ (1 : Fin 2)).toOrderHom.toFun).f (Fin.cons i₀ x) = _
    funext a
    simp only [Limits.FormalCoproduct.mapPower, SimplexCategory.δ]
    fin_cases a
    simp
  have h0 : Work.DSF1.Cech.Eobj U 0
      (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
        (Work.DSF1.Cech.insIdx U i₀ 0 x))
      = Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) :=
    congrArg (Work.DSF1.Cech.Eobj U 0) hf1
  have hδE : Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
          (Work.DSF1.Cech.insIdx U i₀ 0 x)) ≤ ⊤)).op
      ≫ Q.map ((eqToHom h0.symm).op)
      = Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op := by
    rw [← Q.map_comp]
    congr 1
  haveI : IsIso (Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
          (Work.DSF1.Cech.insIdx U i₀ 0 x)) ≤ ⊤)).op) := by
    rw [h0]
    exact h.1
  haveI : IsIso (Q.map (homOfLE (le_top :
      Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := h.1
  haveI : IsIso (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ
      (Work.DSF1.Cech.insIdx U i₀ 0 x)).op) := h.2 0 x
  haveI : IsIso (coaugAb X U Q ≫ Limits.Pi.π
      (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z))) (fun _ : Fin 1 => i₀)) :=
    isIso_coaugAb_π U Q i₀ h
  have hπ : Limits.Pi.π (fun v : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 v)))
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
          (Work.DSF1.Cech.insIdx U i₀ 0 x))
      ≫ Q.map ((eqToHom h0.symm).op)
      = Limits.Pi.π (fun v : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 v)))
        (fun _ : Fin 1 => i₀) := by
    rw [show Q.map ((eqToHom h0.symm).op) = eqToHom (by simp only [hf1]) from by
      rw [eqToHom_op, eqToHom_map]]
    exact Limits.Pi.π_comp_eqToHom _ hf1
  have hA : Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
          (Work.DSF1.Cech.insIdx U i₀ 0 x)) ≤ ⊤)).op
      ≫ Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ
          (Work.DSF1.Cech.insIdx U i₀ 0 x)).op
      = Q.map (homOfLE (le_top :
          Work.DSF1.Cech.Eobj U 1 (Work.DSF1.Cech.insIdx U i₀ 0 x) ≤ ⊤)).op := by
    rw [← Q.map_comp]
    congr 1
  have hB : Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op
      ≫ Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ
          (Work.DSF1.Cech.insIdx U i₀ 0 x)).op
      = Q.map (homOfLE (le_top :
          Work.DSF1.Cech.Eobj U 1 (Work.DSF1.Cech.insIdx U i₀ 0 x) ≤ ⊤)).op := by
    rw [← Q.map_comp]
    congr 1
  have hγ : Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ
        (Work.DSF1.Cech.insIdx U i₀ 0 x)).op
      = inv (Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
            (Work.DSF1.Cech.insIdx U i₀ 0 x)) ≤ ⊤)).op)
        ≫ Q.map (homOfLE (le_top :
            Work.DSF1.Cech.Eobj U 1 (Work.DSF1.Cech.insIdx U i₀ 0 x) ≤ ⊤)).op := by
    rw [← hA, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hβ : Q.map (homOfLE (le_top :
        Work.DSF1.Cech.Eobj U 1 (Work.DSF1.Cech.insIdx U i₀ 0 x) ≤ ⊤)).op
      ≫ inv (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ
          (Work.DSF1.Cech.insIdx U i₀ 0 x)).op)
      = Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op := by
    rw [← hB, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hγinv : Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ
        (Work.DSF1.Cech.insIdx U i₀ 0 x)).op
      ≫ inv (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ
          (Work.DSF1.Cech.insIdx U i₀ 0 x)).op)
      = inv (Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
            (Work.DSF1.Cech.insIdx U i₀ 0 x)) ≤ ⊤)).op)
        ≫ Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op := by
    rw [hγ, Category.assoc, hβ]
  have h1 : inv (Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
          (Work.DSF1.Cech.insIdx U i₀ 0 x)) ≤ ⊤)).op)
      ≫ Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op
      = Q.map ((eqToHom h0.symm).op) := by
    rw [← hδE, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hinv : inv (Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
          (Work.DSF1.Cech.insIdx U i₀ 0 x)) ≤ ⊤)).op)
      = Q.map ((eqToHom h0.symm).op)
        ≫ inv (Q.map (homOfLE (le_top :
            Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := by
    rw [← h1, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hinvε : inv (coaugAb X U Q ≫ Limits.Pi.π
        (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
        (fun _ : Fin 1 => i₀))
      = inv (Q.map (homOfLE (le_top :
          Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := by
    have hε : coaugAb X U Q ≫ Limits.Pi.π
        (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
        (fun _ : Fin 1 => i₀)
        = Q.map (homOfLE (le_top :
            Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op :=
      Limits.Pi.lift_comp_π _ _
    have h2 : (coaugAb X U Q ≫ Limits.Pi.π
        (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
        (fun _ : Fin 1 => i₀))
        ≫ inv (Q.map (homOfLE (le_top :
            Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op)
        = 𝟙 (Q.obj (op ⊤)) := by
      rw [hε, IsIso.hom_inv_id]
    calc inv (coaugAb X U Q ≫ Limits.Pi.π
          (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
          (fun _ : Fin 1 => i₀))
        = inv (coaugAb X U Q ≫ Limits.Pi.π
            (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
            (fun _ : Fin 1 => i₀)) ≫ 𝟙 (Q.obj (op ⊤)) := (Category.comp_id _).symm
      _ = inv (coaugAb X U Q ≫ Limits.Pi.π
            (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
            (fun _ : Fin 1 => i₀))
          ≫ ((coaugAb X U Q ≫ Limits.Pi.π
              (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
              (fun _ : Fin 1 => i₀))
            ≫ inv (Q.map (homOfLE (le_top :
                Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op)) := by rw [h2]
      _ = (inv (coaugAb X U Q ≫ Limits.Pi.π
              (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
              (fun _ : Fin 1 => i₀))
          ≫ (coaugAb X U Q ≫ Limits.Pi.π
              (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
              (fun _ : Fin 1 => i₀)))
          ≫ inv (Q.map (homOfLE (le_top :
              Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 (Q.obj (op (Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀)))) ≫
            inv (Q.map (homOfLE (le_top :
              Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := by
        rw [IsIso.inv_hom_id]
      _ = inv (Q.map (homOfLE (le_top :
            Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) := Category.id_comp _
  calc ((Limits.Pi.π (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
            (Work.DSF1.Cech.insIdx U i₀ 0 x)))
          ≫ Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ
            (Work.DSF1.Cech.insIdx U i₀ 0 x)).op)
        ≫ inv (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ
            (Work.DSF1.Cech.insIdx U i₀ 0 x)).op)
      = Limits.Pi.π (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
            (Work.DSF1.Cech.insIdx U i₀ 0 x))
          ≫ (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).φ
              (Work.DSF1.Cech.insIdx U i₀ 0 x)).op
            ≫ inv (Q.map (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (0 : Fin 2)).op).φ
              (Work.DSF1.Cech.insIdx U i₀ 0 x)).op)) := Category.assoc _ _ _
      _ = Limits.Pi.π (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
            (Work.DSF1.Cech.insIdx U i₀ 0 x))
          ≫ (inv (Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0
              (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
                (Work.DSF1.Cech.insIdx U i₀ 0 x)) ≤ ⊤)).op)
            ≫ Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op) := by
        rw [hγinv]
      _ = Limits.Pi.π (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
            (Work.DSF1.Cech.insIdx U i₀ 0 x))
          ≫ ((Q.map ((eqToHom h0.symm).op)
            ≫ inv (Q.map (homOfLE (le_top :
                Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op))
            ≫ Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op) := by
        rw [hinv]
      _ = ((Limits.Pi.π (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
            (((Work.DSF1.Cech.E U).map (SimplexCategory.δ (1 : Fin 2)).op).f
              (Work.DSF1.Cech.insIdx U i₀ 0 x))
            ≫ Q.map ((eqToHom h0.symm).op))
            ≫ inv (Q.map (homOfLE (le_top :
                Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op))
          ≫ Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op := by
        simp only [Category.assoc]
      _ = (Limits.Pi.π (fun z : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 z)))
            (fun _ : Fin 1 => i₀)
            ≫ inv (Q.map (homOfLE (le_top :
                Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op))
          ≫ Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op := by
        erw [hπ]
      _ = kTopAb U Q h ≫ Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 x ≤ ⊤)).op := by
        erw [kTopAb, asIso_inv, hinvε]

/-- The chain-homotopy identity in degree `0` of the augmented Čech complex with coefficients
in a presheaf `Q` of abelian groups, in the "unit case" `Work.DSEQ0.IsIsoDelAbTop U Q i₀`
(the coface maps of the Čech nerve inserting `i₀` are inverted by `Q`, and so is the
restriction `Q(⊤) ⟶ Q (U i₀)`).  It is the degree-`0` companion of
`Work.DSF1.Sheaf.homotopy_succAb`, with `Work.DSEQ0.kTopAb` playing the role of the contracting
homotopy in degree `0`.  The proof is a copy of `Work.DSF1.Cech.KTopSq` and
`Work.DSF1.Cech.homotopy_zero` with `ModuleCat S` replaced by `AddCommGrpCat`. -/
lemma homotopy_zeroAb {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {i₀ : ι}
    (h : Work.DSEQ0.IsIsoDelAbTop U Q i₀) :
    Work.DSEQ0.kTopAb U Q h ≫ Work.DSEQ0.coaugAb X U Q +
      ((CategoryTheory.cechComplexFunctor U).obj Q).d 0 1 ≫
        Work.DSF1.Sheaf.kAb U Q h.2 0 =
      𝟙 (((CategoryTheory.cechComplexFunctor U).obj Q).X 0) := by
  rw [Work.DSF1.Sheaf.d_eq_sum_deltaAb U Q 0]
  rw [Fin.sum_univ_two]
  rw [Fin.val_zero, pow_zero, one_zsmul]
  rw [show ((-1 : ℤ) ^ (((1 : Fin 2) : ℕ))) = -1 from by norm_num]
  rw [neg_one_zsmul]
  rw [Preadditive.add_comp, Preadditive.neg_comp]
  rw [Work.DSF1.Sheaf.delta0_comp_kAb_dX U Q h.2 0, KTopSqAbAux U Q h]
  abel

end Work.DSEQ0
