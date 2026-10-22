/-
AREA RESOL — the projection onto the `k`-th column of the cut total complex is a chain map.

For a cochain complex `B` of light condensed abelian groups and an integer `k`,
`Zero.totCut k B` is the total complex of the columns `q ≥ k` of the resolution bicomplex
(`Zero.totCpx` with the predicate `q ≥ k`), and `Zero.colCpx k B` is the `k`-th column alone,
re-indexed so that its resolution degree `0` sits in cochain degree `k`
(see `RESOL/ZeroCut.lean`).

This file proves that the degreewise projection `Zero.colProjFam k B n` (which is the
`Sigma.desc` sending the summand of the `k`-th column to the corresponding object of `colCpx`
and all other summands to `0`) is compatible with the differentials, i.e. that it is a chain map
`Zero.totCut k B ⟶ Zero.colCpx k B`. This is the `g`-part of the column filtration
`0 → totCut (k+1) B → totCut k B → colCpx k B → 0` whose exactness is used by the induction
proving that the augmentation `R B ⟶ B` of the resolution is a quasi-isomorphism.

Route. Both sides of the identity are morphisms out of the coproduct `(totCut k B).X i`, so it
suffices to test them on the summands `Sigma.ι x` (`Sigma.hom_ext`). Writing the differential as
`totDc = Sigma.desc (totVpart + totHpart)` (`Zero.totDc_apply`, `Preadditive.add_comp`):

* if the column of `x` is not `k`, then both `totVpart ... x` and `totHpart ... x` are `0` after
  projection, because `colProjFam` vanishes on the summands sitting in a column different from
  `k` (`Zero.totVpart_colProj_eq_zero`, `Zero.totHpart_colProj_eq_zero`);
* if the column of `x` is `k`, then `x` is the canonical index `colSectIdx k i` (a subtype
  equality, using `x.2.1 : x.1.2 + x.1.1 = i`), and the vertical part of the differential is the
  differential of the `k`-th column, while the horizontal part dies after projection
  (`Zero.totVpart_colProj_eq`, `Zero.totHpart_colProj_eq`); finally the comparison morphism
  `eqToHom (Zero.totFam_eq_colCpx ...)` is the identity because its two sides are defeq.

The file sets the `backward.isDefEq.respectTransparency` options (as the other files of the
AREA RESOL do) so that the `rfl`-level identities between the many abbreviations and
re-indexings involved are seen by the elaborator.
-/
import Mathlib
import Submission.Work.RESOL.ZeroCut

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Work.RESOL

/-- Two `eqToHom`s of the same equation are equal (proof irrelevance). -/
lemma eqToHom_proof_irrel {C : Type*} [Category C] {A B : C} (h h' : A = B) :
    eqToHom h = eqToHom h' := by
  rw [Subsingleton.elim h h']

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M)) (B : Cpx)

/-- At the canonical index `colSectIdx k n` of the `k`-th column, the vertical part of the
differential of `totCut k B` followed by the projection onto the `k`-th column is the
differential of the `k`-th column (`colCpx k B`, in degrees `n` and `n+1`). -/
lemma totVpart_colProj_eq (k : ℤ) (n : ℤ) :
    totVpart F π hπ (geP k) B n (colSectIdx k n) ≫ colProjFam F π hπ k B (n+1)
      = ((Rco F π hπ).obj (B.X k)).d (n - k) ((n + 1) - k) := by
  have hι : (Sigma.ι (totFam F π hπ (geP k) B (n+1)) (totVIdx (colSectIdx k n)))
        ≫ colProjFam F π hπ k B (n+1)
      = eqToHom (congr_arg (((Rco F π hπ).obj (B.X k)).X)
          ((ComplexShape.up ℤ).next_eq
            ((ComplexShape.up_Rel ℤ (n - k) ((n - k) + 1)).mpr rfl)
            ((ComplexShape.up_Rel ℤ (n - k) ((n + 1) - k)).mpr (by omega)))) := by
    rw [colProjFam_ι, dite_eq_left (show (totVIdx (colSectIdx k n)).1.1 = k from rfl)]
  exact (Category.assoc
      (((Rco F π hπ).obj (B.X (colSectIdx k n).1.1)).d (colSectIdx k n).1.2
        ((colSectIdx k n).1.2 + 1))
      (Sigma.ι (totFam F π hπ (geP k) B (n+1)) (totVIdx (colSectIdx k n)))
      (colProjFam F π hπ k B (n+1))).trans
    ((congrArg (fun t => (((Rco F π hπ).obj (B.X (colSectIdx k n).1.1)).d
        (colSectIdx k n).1.2 ((colSectIdx k n).1.2 + 1)) ≫ t) hι).trans
      (HomologicalComplex.d_comp_eqToHom ((Rco F π hπ).obj (B.X k))
        ((ComplexShape.up_Rel ℤ (n-k) ((n+1)-k)).mpr (by omega))
        ((ComplexShape.up_Rel ℤ (n-k) ((n-k)+1)).mpr (by omega))))

/-- At the canonical index `colSectIdx k n` of the `k`-th column, the horizontal part of the
differential of `totCut k B` vanishes after projection onto the `k`-th column (it lands in the
column `k+1`). -/
lemma totHpart_colProj_eq (k : ℤ) (n : ℤ) :
    totHpart F π hπ (geP k) (geP_step k) B n (colSectIdx k n)
      ≫ colProjFam F π hπ k B (n+1) = 0 := by
  rw [totHpart]
  rw [Linear.units_smul_comp]
  rw [Category.assoc]
  rw [colProjFam_ι]
  rw [dite_eq_right (show ¬ ((totHIdx (geP_step k) (colSectIdx k n)).1.1 = k) from by
    show ¬ ((k : ℤ) + 1 = k); omega)]
  simp

/-- The vertical part of the differential of a summand whose column is not `k` vanishes after
projection onto the `k`-th column. -/
lemma totVpart_colProj_eq_zero (k : ℤ) (n : ℤ) (x : TotIdx (geP k) n) (h : ¬ x.1.1 = k) :
    totVpart F π hπ (geP k) B n x ≫ colProjFam F π hπ k B (n+1) = 0 := by
  have hι : (Sigma.ι (totFam F π hπ (geP k) B (n+1)) (totVIdx x))
      ≫ colProjFam F π hπ k B (n+1) = 0 := by
    rw [colProjFam_ι, dite_eq_right (show ¬ ((totVIdx x).1.1 = k) from h)]
  calc totVpart F π hπ (geP k) B n x ≫ colProjFam F π hπ k B (n+1)
      = (((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
          ≫ Sigma.ι (totFam F π hπ (geP k) B (n+1)) (totVIdx x))
          ≫ colProjFam F π hπ k B (n+1) := rfl
    _ = ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1)
          ≫ (Sigma.ι (totFam F π hπ (geP k) B (n+1)) (totVIdx x)
              ≫ colProjFam F π hπ k B (n+1)) := Category.assoc _ _ _
    _ = ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1) ≫ 0 :=
        congrArg (fun t => ((Rco F π hπ).obj (B.X x.1.1)).d x.1.2 (x.1.2 + 1) ≫ t) hι
    _ = 0 := comp_zero

/-- The horizontal part of the differential of a summand vanishes after projection onto the
`k`-th column: it lands in the column `x.1.1 + 1`, which is different from `k` because
`x.1.1 ≥ k` (the columns of `totCut k B` start at `k`). -/
lemma totHpart_colProj_eq_zero (k : ℤ) (n : ℤ) (x : TotIdx (geP k) n) :
    totHpart F π hπ (geP k) (geP_step k) B n x ≫ colProjFam F π hπ k B (n+1) = 0 := by
  rw [totHpart]
  rw [Linear.units_smul_comp]
  rw [Category.assoc]
  rw [colProjFam_ι]
  rw [dite_eq_right (show ¬ ((totHIdx (geP_step k) x).1.1 = k) from by
    show ¬ ((x.1.1 : ℤ) + 1 = k); omega)]
  simp

end Zero

/-- The projection onto the `k`-th column of the cut total complex is a chain map, i.e. it
commutes with the differentials: this is the `g`-part of the column filtration short exact
sequence `0 → totCut (k+1) B → totCut k B → colCpx k B → 0`. -/
theorem zCutColProjComm (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M)) (k : ℤ) (B : Work.RESOL.Cpx) :
    ∀ (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j),
      CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.colProjFam F π hπ k B i)
          ((Work.RESOL.Zero.colCpx F π hπ k B).d i j)
        = CategoryTheory.CategoryStruct.comp ((Work.RESOL.Zero.totCut F π hπ k B).d i j)
            (Work.RESOL.Zero.colProjFam F π hπ k B j) := by
  intro i j hij
  have hj : i + 1 = j := (ComplexShape.up_Rel ℤ i j).mp hij
  subst hj
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, Zero.colProjFam_ι]
  rw [Zero.totCut_d_eq, ← Category.assoc, Zero.totDc_apply]
  rw [Preadditive.add_comp]
  split_ifs with h
  · -- the summand `x` sits in the `k`-th column: it is the canonical index
    have hx : x = Zero.colSectIdx k i := by
      apply Subtype.ext
      apply Prod.ext
      · simpa [Zero.colSectIdx] using h
      · show x.1.2 = i - k
        have := x.2.1
        omega
    subst hx
    -- the comparison of the summand with the `k`-th column is the identity
    have hcol : eqToHom (Zero.totFam_eq_colCpx F π hπ B (Zero.colSectIdx k i) h)
        = 𝟙 ((Zero.colCpx F π hπ k B).X i) := by
      rw [show Zero.totFam_eq_colCpx F π hπ B (Zero.colSectIdx k i) h = rfl from
        Subsingleton.elim _ _]
      rw [eqToHom_refl]
      rfl
    have hd : eqToHom (Zero.totFam_eq_colCpx F π hπ B (Zero.colSectIdx k i) h)
          ≫ (Zero.colCpx F π hπ k B).d i (i + 1)
        = ((Zero.Rco F π hπ).obj (B.X k)).d (i - k) ((i + 1) - k) :=
      (congrArg (fun t => t ≫ (Zero.colCpx F π hπ k B).d i (i + 1)) hcol).trans
        ((Category.id_comp _).trans (Zero.colCpx_d F π hπ k B i (i + 1)))
    rw [Zero.totVpart_colProj_eq, Zero.totHpart_colProj_eq, add_zero]
    exact hd
  · -- the summand `x` sits in a column different from `k`: both parts die
    rw [Zero.totVpart_colProj_eq_zero F π hπ B k i x h,
      Zero.totHpart_colProj_eq_zero F π hπ B k i x, add_zero, zero_comp]

end Work.RESOL
