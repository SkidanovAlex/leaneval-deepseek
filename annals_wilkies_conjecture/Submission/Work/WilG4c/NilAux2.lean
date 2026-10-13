/-
  WilG4c / `NilAux2` — the realisation of the pointwise-fibre-continuity shape.

  `ZpShape p n` is a shape in `ℝ^{Nc+1}` (`Nc = p + (n+1)`) built from two `mem`-atoms (the
  graph of `f`, used for the free point and for the point `(l, y', v')`) and the four positivity
  gadgets `ε > 0`, `δ > 0`, `δ² > Σ (y'-u)²`, `ε² > (v'-v)²`.  This file

  * proves, layer by layer, that the `OShape.realize` of each sub-shape is the corresponding
    named set (`InnerSet`, `VeSet`, `BallSet`, `YSet`, `DeltaSet`, `DeltaExSet`, `EpsSet`,
    `EpsExSet`, `ContSet`), and hence `(ZpShape p n).realize = ZpShapeSet p n f`;
  * unwinds `ContSet` into the honest ε-δ formulation (`ContSet_mem`), which is the only place
    where the mathematical content of the gadgets is used;
  * deduces `(ZpShape p n).realize (ZpData p n f D) = ZpSet p n f`.

  The whole file is written in *term mode* whenever a definitionally-equal `Data` has to be
  transported: `OShape.Data` is a semireducible recursive definition, so `rw`/`simp only`
  (implicit transparency) cannot unify `d : σ.Data` with `τ.Data` for definitionally equal
  `σ, τ`, while `exact`/`have … := rfl` (default transparency) can.
-/
import Mathlib
import Submission.Work.WilG4c.SliceNilDefs
import Submission.Work.WilG4c.NilAux1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Membership forms of the `OShape.realize` equations -/

theorem realize_and_mem {n : ℕ} (s t : OShape n) (d : (OShape.and s t).Data) (x : Fin n → ℝ) :
    x ∈ (OShape.and s t).realize d ↔ x ∈ s.realize d.1 ∧ x ∈ t.realize d.2 := Iff.rfl

theorem realize_neg_mem {n : ℕ} (s : OShape n) (d : (OShape.neg s).Data) (x : Fin n → ℝ) :
    x ∈ (OShape.neg s).realize d ↔ x ∉ s.realize d := Iff.rfl

theorem realize_ex_mem {n : ℕ} (s : OShape (n + 1)) (d : (OShape.ex s).Data) (x : Fin n → ℝ) :
    x ∈ (OShape.ex s).realize d ↔ ∃ t : ℝ, Fin.snoc x t ∈ s.realize d := Iff.rfl

theorem realize_mem_mem {n m : ℕ} (ι : Fin m → Fin n) (d : Set (Fin m → ℝ) × ℕ) (x : Fin n → ℝ) :
    x ∈ (OShape.mem n m ι).realize d ↔ x ∘ ι ∈ d.1 := Iff.rfl

theorem realize_poly_mem {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ (OShape.poly n).realize P ↔ MvPolynomial.eval x P = 0 := Iff.rfl

theorem posEx_realize_mem' {m : ℕ} (Q : MvPolynomial (Fin m) ℝ) (x : Fin m → ℝ) :
    x ∈ (OShape.ex (OShape.poly (m + 1))).realize (posAtom Q) ↔ 0 < MvPolynomial.eval x Q := by
  exact (Set.ext_iff.mp (posEx_realize Q) x).trans (by simp only [Set.mem_ofPred_eq])

/-! ## 2. The intermediate sets, one per shape layer -/

/-- The `v'`-block: the point `(l,y',v')` lies on the graph and `(v'-v)² < ε²`. -/
def InnerSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Kz p n + 2) → ℝ) :=
  {u | (u ∘ iotaVp p n) ∈ famGraph f ∧ 0 < MvPolynomial.eval u (PD p n)}

/-- `∃ v'`: the value of the family at `(l, y')`. -/
def VeSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Kz p n + 1) → ℝ) :=
  {u | ∃ t : ℝ, Fin.snoc u t ∈ InnerSet p n f}

/-- The ball implication `δ² - Σ(y'-u)² > 0 → (…)`. -/
def BallSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Kz p n) → ℝ) :=
  {x | ¬ ∃ t : ℝ, Fin.snoc x t ∈ ({y : Fin (Kz p n + 1) → ℝ |
      MvPolynomial.eval y (posAtom (Pball p n)) = 0} ∩ (VeSet p n f)ᶜ)}

/-- `∀ y'`. -/
def YSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n + 5) → ℝ) :=
  {x | ∀ w : Fin (n + 1) → ℝ, Work.WilG0.snocIt (Nc p n + 5) (n + 1) x w ∈ BallSet p n f}

/-- `δ > 0 ∧ ∀ y'`. -/
def DeltaSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n + 5) → ℝ) :=
  {x | MvPolynomial.eval x (posAtom (Pdel p n)) = 0} ∩ YSet p n f

/-- `∃ δ, δ > 0 ∧ ∀ y'`. -/
def DeltaExSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n + 3) → ℝ) :=
  {x | ∃ t : ℝ, Fin.snoc x t ∈ {y : Fin (Nc p n + 4) → ℝ |
      ∃ s : ℝ, Fin.snoc y s ∈ DeltaSet p n f}}

/-- `ε > 0 ∧ ¬ ∃ δ (…)`. -/
def EpsSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n + 3) → ℝ) :=
  {x | MvPolynomial.eval x (posAtom (Peps p n)) = 0} ∩ (DeltaExSet p n f)ᶜ

/-- `∃ ε, ε > 0 ∧ ¬ ∃ δ (…)`. -/
def EpsExSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n + 2) → ℝ) :=
  {x | ∃ t : ℝ, Fin.snoc x t ∈ EpsSet p n f}

/-- `∀ ε > 0, ∃ δ > 0, ∀ y' (…)`. -/
def ContSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : Set (Fin (Nc p n + 1) → ℝ) :=
  {z | ¬ ∃ t : ℝ, Fin.snoc z t ∈ EpsExSet p n f}

/-- The set realised by `ZpShape p n`. -/
def ZpShapeSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    Set (Fin (Nc p n + 1) → ℝ) :=
  {z | z ∘ id ∈ famGraph f} ∩ ContSet p n f

/-! ## 3. The realisation lemmas, one per layer -/

theorem zpInner_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpInner p n).realize (zpInnerData p n f D) = InnerSet p n f := by
  ext u
  refine (realize_and_mem (OShape.mem (Kz p n + 2) (Ng p n) (iotaVp p n))
      (OShape.ex (OShape.poly (Kz p n + 3))) (zpInnerData p n f D) u).trans ?_
  refine (and_congr (realize_mem_mem (iotaVp p n) (famGraph f, D) u)
      (posEx_realize_mem' (PD p n) u)).trans ?_
  simp only [InnerSet, Set.mem_ofPred_eq]

theorem zpVexists_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpVexists p n).realize (zpVexistsData p n f D) = VeSet p n f := by
  ext u
  refine (realize_ex_mem (zpInner p n) (zpVexistsData p n f D) u).trans ?_
  simp only [VeSet, Set.mem_ofPred_eq]
  exact exists_congr fun t => by
    rw [show (zpInner p n).realize (zpVexistsData p n f D) = InnerSet p n f from
      zpInner_realize p n f D]

theorem zpBallImp_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpBallImp p n).realize (zpBallImpData p n f D) = BallSet p n f := by
  ext x
  refine (realize_neg_mem (OShape.ex (OShape.and (OShape.poly (Kz p n + 1))
      (OShape.neg (zpVexists p n)))) (zpBallImpData p n f D) x).trans ?_
  refine not_congr ?_
  refine (realize_ex_mem (OShape.and (OShape.poly (Kz p n + 1)) (OShape.neg (zpVexists p n)))
      (zpBallImpData p n f D) x).trans ?_
  simp only [BallSet, VeSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  refine exists_congr fun t => ?_
  refine (realize_and_mem (OShape.poly (Kz p n + 1)) (OShape.neg (zpVexists p n))
      (zpBallImpData p n f D) (Fin.snoc x t)).trans ?_
  refine (and_congr (realize_poly_mem (posAtom (Pball p n)) (Fin.snoc x t))
      (realize_neg_mem (zpVexists p n) (zpVexistsData p n f D) (Fin.snoc x t))).trans ?_
  refine and_congr Iff.rfl (not_congr ?_)
  rw [show (zpVexists p n).realize (zpVexistsData p n f D) = VeSet p n f from
    zpVexists_realize p n f D]
  simp only [VeSet, Set.mem_ofPred_eq]

theorem zpYBlock_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpYBlock p n).realize (zpYBlockData p n f D) = YSet p n f := by
  ext x
  refine (Set.ext_iff.mp (forallIter_realize (Nc p n + 5) (n + 1) (zpBallImp p n)
    (zpBallImpData p n f D)) x).trans ?_
  simp only [YSet, Set.mem_ofPred_eq]
  exact forall_congr' fun w => by
    rw [show (zpBallImp p n).realize (zpBallImpData p n f D) = BallSet p n f from
      zpBallImp_realize p n f D]

theorem zpDelta_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpDelta p n).realize (zpDeltaData p n f D) = DeltaSet p n f := by
  ext x
  refine (realize_and_mem (OShape.poly (Nc p n + 5)) (zpYBlock p n)
      (zpDeltaData p n f D) x).trans ?_
  refine (and_congr (realize_poly_mem (posAtom (Pdel p n)) x) Iff.rfl).trans ?_
  simp only [DeltaSet, YSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  refine and_congr Iff.rfl ?_
  rw [show (zpYBlock p n).realize (zpDeltaData p n f D).2 = YSet p n f from
    zpYBlock_realize p n f D]
  simp only [YSet, Set.mem_ofPred_eq]

theorem zpDeltaEx_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpDeltaEx p n).realize (zpDeltaExData p n f D) = DeltaExSet p n f := by
  ext x
  refine (realize_ex_mem (OShape.ex (zpDelta p n)) (zpDeltaExData p n f D) x).trans ?_
  simp only [DeltaExSet, Set.mem_ofPred_eq]
  refine exists_congr fun t => ?_
  refine (realize_ex_mem (zpDelta p n) (zpDeltaData p n f D) (Fin.snoc x t)).trans ?_
  refine exists_congr fun s => ?_
  rw [show (zpDelta p n).realize (zpDeltaData p n f D) = DeltaSet p n f from
    zpDelta_realize p n f D]

theorem zpEps_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpEps p n).realize (zpEpsData p n f D) = EpsSet p n f := by
  ext x
  refine (realize_and_mem (OShape.poly (Nc p n + 3)) (OShape.neg (zpDeltaEx p n))
      (zpEpsData p n f D) x).trans ?_
  refine (and_congr (realize_poly_mem (posAtom (Peps p n)) x)
      (realize_neg_mem (zpDeltaEx p n) (zpDeltaExData p n f D) x)).trans ?_
  simp only [EpsSet, DeltaExSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  refine and_congr Iff.rfl (not_congr ?_)
  rw [show (zpDeltaEx p n).realize (zpDeltaExData p n f D) = DeltaExSet p n f from
    zpDeltaEx_realize p n f D]
  simp only [DeltaExSet, Set.mem_ofPred_eq]

theorem zpEpsEx_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpEpsEx p n).realize (zpEpsData p n f D) = EpsExSet p n f := by
  ext x
  refine (realize_ex_mem (zpEps p n) (zpEpsData p n f D) x).trans ?_
  simp only [EpsExSet, Set.mem_ofPred_eq]
  exact exists_congr fun t => by
    rw [show (zpEps p n).realize (zpEpsData p n f D) = EpsSet p n f from
      zpEps_realize p n f D]

theorem zpCont_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (zpCont p n).realize (zpEpsData p n f D) = ContSet p n f := by
  ext z
  refine Iff.trans (realize_neg_mem (OShape.ex (zpEpsEx p n)) (zpEpsData p n f D) z) ?_
  refine Iff.trans (not_congr (realize_ex_mem (zpEpsEx p n) (zpEpsData p n f D) z)) ?_
  rw [show (zpEpsEx p n).realize (zpEpsData p n f D) = EpsExSet p n f from
    zpEpsEx_realize p n f D]
  rw [show ContSet p n f = {z : Fin (Nc p n + 1) → ℝ | ¬ ∃ t : ℝ,
    Fin.snoc z t ∈ EpsExSet p n f} from rfl]
  simp only [Set.mem_ofPred_eq]

theorem ZpShape_realize_stage (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (ZpShape p n).realize (ZpData p n f D) = ZpShapeSet p n f := by
  ext z
  refine (realize_and_mem (OShape.mem (Nc p n + 1) (Ng p n) id) (zpCont p n)
      (ZpData p n f D) z).trans ?_
  refine (and_congr (realize_mem_mem id (famGraph f, D) z) Iff.rfl).trans ?_
  simp only [ZpShapeSet, ContSet, Function.comp_id, Set.mem_ofPred_eq, Set.mem_inter_iff]
  refine and_congr Iff.rfl ?_
  rw [show (zpCont p n).realize (ZpData p n f D).2 = ContSet p n f from
    zpCont_realize p n f D]
  rw [show ContSet p n f = {z : Fin (Nc p n + 1) → ℝ | ¬ ∃ t : ℝ,
    Fin.snoc z t ∈ EpsExSet p n f} from rfl]
  simp only [Set.mem_ofPred_eq]

/-! ## 4. Unwinding `ContSet`

After unfolding the ten set definitions the membership `z ∈ ContSet p n f` is a nested
`∃`/`¬∃` formula.  The four gadget conversions (`exists_sq_mul_sub_one`,
`not_exists_sq_gadget`, `exists_sq_gadget_pos`, `not_exists_sq_gadget_const`,
`exists_eq_and_pos`) together with the four evaluation lemmas (`eval_posAtom_Peps`,
`eval_chain_Pdel`, `eval_chain_Pball`, `eval_chain_PD`) and the graph reduction
(`famGraph_chain_iotaVp`) identify it with the honest ε-δ formulation. -/

theorem ContSet_mem (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (z : Fin (Nc p n + 1) → ℝ) :
    z ∈ ContSet p n f ↔ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ w : Fin (n + 1) → ℝ,
      (∑ j : Fin (n + 1), (w j - cubePt (Fin.init z) j) ^ 2) < δ ^ 2 →
      (f (parPt (Fin.init z)) w - z (Fin.last (Nc p n))) ^ 2 < ε ^ 2 := by
  have hpar : parPt (Fin.init z) = fun i : Fin p => z ⟨(i : ℕ), by simp only [Nc]; omega⟩ :=
    parPt_init_eq p n z
  have hcube : cubePt (Fin.init z) =
      fun j : Fin (n + 1) => z ⟨p + (j : ℕ), by simp only [Nc]; omega⟩ :=
    cubePt_init_eq p n z
  have hlast : z (Fin.last (Nc p n)) = z ⟨Nc p n, by simp only [Nc]; omega⟩ :=
    congrArg z (Fin.ext rfl)
  rw [hpar, hcube, hlast]
  simp only [ContSet, EpsExSet, EpsSet, DeltaExSet, DeltaSet, YSet, BallSet, VeSet, InnerSet,
    Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  simp only [eval_posAtom_Peps, eval_chain_Pdel, eval_chain_Pball, eval_chain_PD,
    famGraph_chain_iotaVp]
  simp only [not_exists_sq_gadget]
  simp only [exists_sq_gadget_pos]
  simp only [not_exists_sq_gadget_const]
  simp only [exists_eq_and_pos]
  simp only [sub_pos]

theorem z_last_eq (p n : ℕ) (z : Fin (Nc p n + 1) → ℝ) :
    z (Fin.last (Nc p n)) = z ⟨Nc p n, by simp only [Nc]; omega⟩ :=
  congrArg z (Fin.ext rfl)

theorem ZpShapeSet_eq_ZpSet (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    ZpShapeSet p n f = ZpSet p n f := by
  ext z
  rw [show ZpShapeSet p n f = ({z : Fin (Nc p n + 1) → ℝ | z ∘ id ∈ famGraph f}) ∩
    ContSet p n f from rfl]
  rw [show ZpSet p n f = {z : Fin (Nc p n + 1) → ℝ | z ∈ famGraph f ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y' : Fin (n + 1) → ℝ,
        (∑ j : Fin (n + 1), (y' j - cubePt (Fin.init z) j) ^ 2) < δ ^ 2 →
        (f (parPt (Fin.init z)) y' - z (Fin.last (Nc p n))) ^ 2 < ε ^ 2} from rfl]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.comp_id, ContSet_mem]

theorem ZpShape_realize (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (D : ℕ) :
    (ZpShape p n).realize (ZpData p n f D) = ZpSet p n f := by
  rw [ZpShape_realize_stage p n f D, ZpShapeSet_eq_ZpSet p n f]

end Work.WilkG4c
