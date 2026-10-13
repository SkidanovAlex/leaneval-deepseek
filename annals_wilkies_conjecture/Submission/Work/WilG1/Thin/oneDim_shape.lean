/-
  WilG1 / Thin / oneDim_shape

  The `OShape` formula calculus instantiated for the four one-sided oscillation predicates
  `RHi`, `RLo`, `LHi`, `LLo` used in the proof of `oneDim_thin`.

  The seven coordinates of the block are `(x, δ, y, v, u, t, s)`: `v` is the value of the
  graph at `x`, `u` the value at `y`, `t` the witness for the position of `y` relative to
  `(x, δ)` (the condition `(y-x)(δ-(y-x)) > 0`, i.e. `0 < ±(y-x) < δ`), and `s` the witness
  for the shift inequality.  The shape itself is `∀δ > 0, ∃(y,v,u,t,s): block`.
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG0.Main

set_option autoImplicit false
noncomputable section

open Classical Filter Topology
open scoped Topology

namespace Work.WilG1.Thin

open WilkiesDesign WilkiesConjecture Work.WilG1 WilkiesDesign.CG

lemma liftR_inter (A B : Set ℝ) : liftR (A ∩ B) = liftR A ∩ liftR B := by
  ext z; simp [liftR, Set.mem_inter_iff]

/-! ## Coordinates -/

/-- coordinate `0`: `x`. -/
def cX : Fin 7 := Fin.castAdd 5 (Fin.castSucc (0 : Fin 1))
/-- coordinate `1`: `δ`. -/
def cD : Fin 7 := Fin.castAdd 5 (Fin.last 1)
/-- coordinate `2`: `y`. -/
def cY : Fin 7 := Fin.natAdd 2 (0 : Fin 5)
/-- coordinate `3`: the value `v` of the graph at `x`. -/
def cV : Fin 7 := Fin.natAdd 2 (1 : Fin 5)
/-- coordinate `4`: the value `u` of the graph at `y`. -/
def cU : Fin 7 := Fin.natAdd 2 (2 : Fin 5)
/-- coordinate `5`: the position witness `t`. -/
def cT : Fin 7 := Fin.natAdd 2 (3 : Fin 5)
/-- coordinate `6`: the shift witness `s`. -/
def cS : Fin 7 := Fin.natAdd 2 (4 : Fin 5)

/-- The pair `(x, v)`. -/
def stA : Fin 2 → Fin 7 := fun j => if j = 0 then cX else cV
/-- The pair `(y, u)`. -/
def stB : Fin 2 → Fin 7 := fun j => if j = 0 then cY else cU

def xp : MvPolynomial (Fin 7) ℝ := MvPolynomial.X cX
def dp : MvPolynomial (Fin 7) ℝ := MvPolynomial.X cD
def yp : MvPolynomial (Fin 7) ℝ := MvPolynomial.X cY
def vp : MvPolynomial (Fin 7) ℝ := MvPolynomial.X cV
def up : MvPolynomial (Fin 7) ℝ := MvPolynomial.X cU
def tp : MvPolynomial (Fin 7) ℝ := MvPolynomial.X cT
def sph : MvPolynomial (Fin 7) ℝ := MvPolynomial.X cS

/-- `0 < y - x < δ`, via the witness `t`. -/
def PRp : MvPolynomial (Fin 7) ℝ :=
  tp ^ 2 * ((yp - xp) * (dp - (yp - xp))) - 1

/-- `0 < x - y < δ`, via the witness `t`. -/
def PLp : MvPolynomial (Fin 7) ℝ :=
  tp ^ 2 * ((xp - yp) * (dp - (xp - yp))) - 1

/-- `q (y - x) < u - v`, via the witness `s`. -/
def PS1p (q : ℝ) : MvPolynomial (Fin 7) ℝ :=
  sph ^ 2 * ((up - vp) - MvPolynomial.C q * (yp - xp)) - 1

/-- `u - v < q (y - x)`, via the witness `s`. -/
def PS2p (q : ℝ) : MvPolynomial (Fin 7) ℝ :=
  sph ^ 2 * (MvPolynomial.C q * (yp - xp) - (up - vp)) - 1

/-- `r ^ 2 δ - 1 = 0`, solvable in `r` iff `δ > 0`. -/
def sPol : MvPolynomial (Fin 3) ℝ := MvPolynomial.X 2 ^ 2 * MvPolynomial.X 1 - 1

/-- `δ > 0`, with an existential witness. -/
def sPos : OShape 2 := OShape.ex (OShape.poly 3)

/-- The block of the formula: two graph memberships and two polynomial equations. -/
def sBlk : OShape 7 :=
  OShape.and (OShape.and (OShape.and (OShape.mem 7 2 stA) (OShape.mem 7 2 stB))
    (OShape.poly 7)) (OShape.poly 7)

/-- Eliminate the five witnesses `y, v, u, t, s`. -/
def sBody : OShape 2 :=
  OShape.ex (OShape.ex (OShape.ex (OShape.ex (OShape.ex sBlk))))

/-- `¬∃δ, δ > 0 ∧ ¬Body`, i.e. `∀δ > 0, Body`. -/
def sShp : OShape 1 := OShape.neg (OShape.ex (OShape.and sPos (OShape.neg sBody)))

/-- The data of the shape. -/
def sData (X : Set (Fin 2 → ℝ)) (D : ℕ) (P1' P2' : MvPolynomial (Fin 7) ℝ) : sShp.Data :=
  (sPol, (((X, D), (X, D)), P1'), P2')

/-- The predicate realised by the block. -/
def sIn (X : Set (Fin 2 → ℝ)) (P1' P2' : MvPolynomial (Fin 7) ℝ) (w : Fin 1 → ℝ)
    (δ : ℝ) : Prop :=
  ∃ r : Fin 5 → ℝ,
    let z := Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r
    (z ∘ stA) ∈ X ∧ (z ∘ stB) ∈ X ∧
      MvPolynomial.eval z P1' = 0 ∧ MvPolynomial.eval z P2' = 0

/-- An explicit witness tuple. -/
def mk5 (a b c d e : ℝ) : Fin 5 → ℝ := ![a, b, c, d, e]

/-! ## Elementary readings -/

@[simp] theorem mk5_zero (a b c d e : ℝ) : mk5 a b c d e 0 = a := by simp [mk5]
@[simp] theorem mk5_one (a b c d e : ℝ) : mk5 a b c d e 1 = b := by simp [mk5]
@[simp] theorem mk5_two (a b c d e : ℝ) : mk5 a b c d e 2 = c := by simp [mk5]
@[simp] theorem mk5_three (a b c d e : ℝ) : mk5 a b c d e 3 = d := by simp [mk5]
@[simp] theorem mk5_four (a b c d e : ℝ) : mk5 a b c d e 4 = e := by simp [mk5]

@[simp] theorem snoc2_one (w : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc w t : Fin 2 → ℝ) 1 = t := by
  rw [show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]

@[simp] theorem snoc3_one (w : Fin 2 → ℝ) (t : ℝ) : (Fin.snoc w t : Fin 3 → ℝ) 1 = w 1 := by
  rw [show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) from Fin.ext rfl, Fin.snoc_castSucc]

@[simp] theorem snoc3_two (w : Fin 2 → ℝ) (t : ℝ) : (Fin.snoc w t : Fin 3 → ℝ) 2 = t := by
  rw [show (2 : Fin 3) = Fin.last 2 from Fin.ext rfl, Fin.snoc_last]

@[simp] theorem stA_zero : stA 0 = cX := rfl
@[simp] theorem stA_one : stA 1 = cV := rfl
@[simp] theorem stB_zero : stB 0 = cY := rfl
@[simp] theorem stB_one : stB 1 = cU := rfl
@[simp] theorem stA_last : stA (Fin.last 1) = cV := stA_one
@[simp] theorem stA_castSucc : stA (Fin.castSucc (0 : Fin 1)) = cX := stA_zero
@[simp] theorem stB_last : stB (Fin.last 1) = cU := stB_one
@[simp] theorem stB_castSucc : stB (Fin.castSucc (0 : Fin 1)) = cY := stB_zero

theorem read_x (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) cX = w 0 := by
  rw [cX, Work.WilG0.snocIt_castAdd, Fin.snoc_castSucc]

theorem read_d (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) cD = δ := by
  rw [cD, Work.WilG0.snocIt_castAdd, Fin.snoc_last]

theorem read_y (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) cY = r 0 :=
  Work.WilG0.snocIt_natAdd 2 5 (Fin.snoc w δ) r 0

theorem read_v (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) cV = r 1 :=
  Work.WilG0.snocIt_natAdd 2 5 (Fin.snoc w δ) r 1

theorem read_u (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) cU = r 2 :=
  Work.WilG0.snocIt_natAdd 2 5 (Fin.snoc w δ) r 2

theorem read_t (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) cT = r 3 :=
  Work.WilG0.snocIt_natAdd 2 5 (Fin.snoc w δ) r 3

theorem read_s (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) cS = r 4 :=
  Work.WilG0.snocIt_natAdd 2 5 (Fin.snoc w δ) r 4

theorem eval_PRp (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    MvPolynomial.eval (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) PRp
      = (r 3) ^ 2 * ((r 0 - w 0) * (δ - (r 0 - w 0))) - 1 := by
  simp only [PRp, xp, dp, yp, tp, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_X, map_one, read_x, read_d, read_y, read_t]

theorem eval_PLp (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    MvPolynomial.eval (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) PLp
      = (r 3) ^ 2 * ((w 0 - r 0) * (δ - (w 0 - r 0))) - 1 := by
  simp only [PLp, xp, dp, yp, tp, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_X, map_one, read_x, read_d, read_y, read_t]

theorem eval_PS1p (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) (q : ℝ) :
    MvPolynomial.eval (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) (PS1p q)
      = (r 4) ^ 2 * ((r 2 - r 1) - q * (r 0 - w 0)) - 1 := by
  simp only [PS1p, xp, yp, vp, up, sph, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_C, map_one, read_x, read_y,
    read_v, read_u, read_s]

theorem eval_PS2p (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) (q : ℝ) :
    MvPolynomial.eval (Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) (PS2p q)
      = (r 4) ^ 2 * (q * (r 0 - w 0) - (r 2 - r 1)) - 1 := by
  simp only [PS2p, xp, yp, vp, up, sph, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_X, MvPolynomial.eval_C, map_one, read_x, read_y,
    read_v, read_u, read_s]

theorem graphA_iff (g : ℝ → ℝ) (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    ((Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) ∘ stA) ∈
        graphOf (fun x : Fin 1 → ℝ => g (x 0)) ↔ r 1 = g (w 0) := by
  rw [graphOf, Set.mem_ofPred_eq]
  simp only [Function.comp_apply, stA_last, stA_castSucc, Fin.init, read_x, read_v]

theorem graphB_iff (g : ℝ → ℝ) (w : Fin 1 → ℝ) (δ : ℝ) (r : Fin 5 → ℝ) :
    ((Work.WilG0.snocIt 2 5 (Fin.snoc w δ) r) ∘ stB) ∈
        graphOf (fun x : Fin 1 → ℝ => g (x 0)) ↔ r 2 = g (r 0) := by
  rw [graphOf, Set.mem_ofPred_eq]
  simp only [Function.comp_apply, stB_last, stB_castSucc, Fin.init, read_y, read_u]

/-! ## Realising the shape -/

theorem sPos_realize : sPos.realize sPol = {w : Fin 2 → ℝ | 0 < w 1} := by
  ext w
  simp only [sPos, OShape.realize, projLast, Set.mem_ofPred_eq, sPol, MvPolynomial.eval_sub,
    MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_X, map_one,
    snoc3_one, snoc3_two]
  constructor
  · rintro ⟨t, ht⟩
    nlinarith [sq_nonneg t]
  · intro h
    refine ⟨(Real.sqrt (w 1))⁻¹, ?_⟩
    have hs : Real.sqrt (w 1) ^ 2 = w 1 := Real.sq_sqrt (le_of_lt h)
    have hne : w 1 ≠ 0 := ne_of_gt h
    rw [inv_pow, hs, inv_mul_cancel₀ hne]
    norm_num

theorem sBlk_realize (X : Set (Fin 2 → ℝ)) (D : ℕ) (P1' P2' : MvPolynomial (Fin 7) ℝ) :
    sBlk.realize ((((X, D), (X, D)), P1'), P2') =
      {z : Fin 7 → ℝ | z ∘ stA ∈ X ∧ z ∘ stB ∈ X ∧
        MvPolynomial.eval z P1' = 0 ∧ MvPolynomial.eval z P2' = 0} := by
  ext z
  simp only [sBlk, OShape.realize, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

theorem sShp_realize (X : Set (Fin 2 → ℝ)) (D : ℕ) (P1' P2' : MvPolynomial (Fin 7) ℝ) :
    sShp.realize (sData X D P1' P2') =
      {w : Fin 1 → ℝ | ∀ δ : ℝ, 0 < δ → sIn X P1' P2' w δ} := by
  have hbody : sBody.realize ((((X, D), (X, D)), P1'), P2')
      = Work.WilG0.projLastIter 2 5 (sBlk.realize ((((X, D), (X, D)), P1'), P2')) := rfl
  ext w
  simp only [sShp, sData, sIn, OShape.realize, sPos_realize, hbody, sBlk_realize,
    Work.WilG0.projLastIter_eq, projLast, Set.mem_ofPred_eq, Set.mem_compl_iff,
    Set.mem_inter_iff, snoc2_one]
  constructor
  · intro h δ hδ
    by_contra hc
    exact h ⟨δ, hδ, hc⟩
  · rintro h ⟨δ, hδ, hc⟩
    exact hc (h δ hδ)

end Work.WilG1.Thin
