import Mathlib
import Submission.Work.WilG0.Main
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace Work.WilG1.Thin

open WilkiesDesign WilkiesDesign.CG

/-!
# `infderiv_mem`

Given `g : ℝ → ℝ` whose graph is an `Ω`-set of format `F` and degree `D`, the set

  `infDeriv g s = {x | ∀ M > 1, ∃ δ > 0, ∀ y ≠ x, |y-x| < δ → M < s * (g y - g x)/(y - x)}`

is an `Ω`-set of format `F + 1000` and degree `1000 * (D + 1)`.

The proof compiles the defining first-order formula into an `OShape` (`G0`'s Ω-formula
calculus, `Work.WilG0.realize_mem_Omega`) and then evaluates the shape.
-/

/-! ## 1. The positivity / sublevel gadgets

`PosShape n` realised by `PosData P` is `{0 < P}`: the extra coordinate `t` solves
`P * t ^ 2 = 1`. `SubShape n` is its complement, i.e. `{P ≤ 0}`. -/

/-- `∃ t, P * t^2 - 1 = 0` in `n+1` coordinates; over the first `n` coordinates this is `0 < P`. -/
def PosShape (n : ℕ) : OShape n := OShape.ex (OShape.poly (n + 1))

/-- The polynomial data of `PosShape n P`. -/
def PosData {n : ℕ} (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.rename Fin.castSucc P * MvPolynomial.X (Fin.last n) ^ 2 - 1

/-- The complement of `PosShape n P`, i.e. the sublevel set `{P ≤ 0}`. -/
def SubShape (n : ℕ) : OShape n := OShape.neg (PosShape n)

theorem eval_PosData {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (z : Fin n → ℝ) (t : ℝ) :
    MvPolynomial.eval (Fin.snoc z t) (PosData P) = MvPolynomial.eval z P * t ^ 2 - 1 := by
  have h1 : (Fin.snoc z t : Fin (n + 1) → ℝ) ∘ Fin.castSucc = z := by
    funext i
    exact Fin.snoc_castSucc (α := fun _ => ℝ) t z i
  have h2 : (MvPolynomial.eval (Fin.snoc z t)) (1 : MvPolynomial (Fin (n + 1)) ℝ) = 1 := by
    rw [← MvPolynomial.C_1, MvPolynomial.eval_C]
  simp only [PosData, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_pow, MvPolynomial.eval_rename, MvPolynomial.eval_X, h1, h2,
    Fin.snoc_last]

theorem PosShape_realize {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (PosShape n).realize (PosData P) = {z : Fin n → ℝ | 0 < MvPolynomial.eval z P} := by
  ext z
  simp only [PosShape, OShape.realize, projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    rw [eval_PosData] at ht
    nlinarith [sq_nonneg t]
  · intro h
    refine ⟨1 / Real.sqrt (MvPolynomial.eval z P), ?_⟩
    rw [eval_PosData]
    have hP : 0 < MvPolynomial.eval z P := h
    have hs : Real.sqrt (MvPolynomial.eval z P) ^ 2 = MvPolynomial.eval z P :=
      Real.sq_sqrt (le_of_lt hP)
    have hne : MvPolynomial.eval z P ≠ 0 := ne_of_gt hP
    rw [div_pow, one_pow, hs, one_div, mul_inv_cancel₀ hne, sub_self]

theorem SubShape_realize {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (SubShape n).realize (PosData P) = {z : Fin n → ℝ | MvPolynomial.eval z P ≤ 0} := by
  ext z
  simp only [SubShape, OShape.realize, Set.mem_compl_iff, Set.mem_ofPred_eq]
  rw [PosShape_realize]
  simp

/-! ## 2. The coordinates of the ambient space `Fin 7 → ℝ = (x, M, δ, y, vx, vy, t)` -/

/-- The substitution picking `(x, vx)` out of the seven coordinates. -/
def iotax : Fin 2 → Fin 7 := ![0, 4]

/-- The substitution picking `(y, vy)` out of the seven coordinates. -/
def iotay : Fin 2 → Fin 7 := ![3, 5]

@[simp] theorem iotax_zero : iotax 0 = (0 : Fin 7) := rfl
@[simp] theorem iotax_one : iotax 1 = (4 : Fin 7) := rfl
@[simp] theorem iotay_zero : iotay 0 = (3 : Fin 7) := rfl
@[simp] theorem iotay_one : iotay 1 = (5 : Fin 7) := rfl

/-- `M * (y - x)^2 - s * (vy - vx) * (y - x)`; negative exactly when the difference quotient
at `x` in direction `y` exceeds `M / s`. -/
def Pinf (s : ℝ) : MvPolynomial (Fin 7) ℝ :=
  MvPolynomial.X 1 * (MvPolynomial.X 3 - MvPolynomial.X 0) ^ 2 -
    MvPolynomial.C s * (MvPolynomial.X 5 - MvPolynomial.X 4) * (MvPolynomial.X 3 - MvPolynomial.X 0)

/-! ## 3. The shape -/

/-- The innermost atom: the two graph memberships and the strict inequality. -/
def Big7 : OShape 7 :=
  OShape.and (OShape.and (OShape.mem 7 2 iotax) (OShape.mem 7 2 iotay)) (PosShape 7)

/-- Eliminate the witnesses `vx, vy, t`. -/
def Body4 : OShape 4 := OShape.ex (OShape.ex (OShape.ex Big7))

/-- `z 2 ≤ z 3 - z 0` or `z 3 - z 0 ≤ -z 2`, i.e. `|z 3 - z 0| ≥ z 2`. -/
def AbsSh4 : OShape 4 := OShape.or (SubShape 4) (SubShape 4)

/-- The body of the `∀ y` condition. -/
def Full4 : OShape 4 := OShape.or (OShape.or (OShape.poly 4) AbsSh4) Body4

/-- `∀ y, Body`, i.e. `¬∃ y, ¬Body`. -/
def ForallY3 : OShape 3 := OShape.neg (OShape.ex (OShape.neg Full4))

/-- `0 < δ` on the coordinates `(x, M, δ)`. -/
def Posδ3 : OShape 3 := PosShape 3

/-- `0 < δ ∧ ∀ y, Body`. -/
def S3 : OShape 3 := OShape.and Posδ3 ForallY3

/-- `∃ δ, 0 < δ ∧ Body`. -/
def E2 : OShape 2 := OShape.ex S3

/-- `M ≤ 1` on the coordinates `(x, M)`. -/
def Mle1_2 : OShape 2 := SubShape 2

/-- `M ≤ 1 ∨ ∃ δ, …`. -/
def S2 : OShape 2 := OShape.or Mle1_2 E2

/-- The shape of the infinite-derivative set. -/
def FullShape : OShape 1 := OShape.neg (OShape.ex (OShape.neg S2))

/-! ## 4. The data -/

/-- `z 2 - (z 3 - z 0)`, i.e. `z 2 ≤ z 3 - z 0` iff `≤ 0`. -/
def PA : MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.X 2 - (MvPolynomial.X 3 - MvPolynomial.X 0)

/-- `z 3 - z 0 + z 2`, i.e. `z 3 - z 0 ≤ -z 2` iff `≤ 0`. -/
def PB : MvPolynomial (Fin 4) ℝ :=
  MvPolynomial.X 3 - MvPolynomial.X 0 + MvPolynomial.X 2

def dataMle : Mle1_2.Data := PosData (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℝ)

def dataPosδ : Posδ3.Data := PosData (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ)

def dataPoly4 : (OShape.poly 4).Data :=
  (MvPolynomial.X 3 - MvPolynomial.X 0 : MvPolynomial (Fin 4) ℝ)

def dataAbs : AbsSh4.Data := (PosData PA, PosData PB)

def dataBig (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) : Big7.Data :=
  (((G, D), (G, D)), PosData (-(Pinf s)))

def dataFull4 (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) : Full4.Data :=
  ((dataPoly4, dataAbs), dataBig G D s)

def dataForallY3 (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) : ForallY3.Data :=
  dataFull4 G D s

def dataS3 (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) : S3.Data :=
  (dataPosδ, dataForallY3 G D s)

def dataE2 (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) : E2.Data := dataS3 G D s

def fullData (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) : FullShape.Data :=
  (dataMle, dataE2 G D s)

/-! ## 5. Coordinate evaluations of `snocIt 4 3` and of iterated `Fin.snoc` -/

@[simp] theorem snocIt4_0 (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    Work.WilG0.snocIt 4 3 z w 0 = z 0 := by
  rw [show (0 : Fin 7) = Fin.castAdd 3 (0 : Fin 4) from Fin.ext rfl, Work.WilG0.snocIt_castAdd]
@[simp] theorem snocIt4_1 (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    Work.WilG0.snocIt 4 3 z w 1 = z 1 := by
  rw [show (1 : Fin 7) = Fin.castAdd 3 (1 : Fin 4) from Fin.ext rfl, Work.WilG0.snocIt_castAdd]
@[simp] theorem snocIt4_2 (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    Work.WilG0.snocIt 4 3 z w 2 = z 2 := by
  rw [show (2 : Fin 7) = Fin.castAdd 3 (2 : Fin 4) from Fin.ext rfl, Work.WilG0.snocIt_castAdd]
@[simp] theorem snocIt4_3 (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    Work.WilG0.snocIt 4 3 z w 3 = z 3 := by
  rw [show (3 : Fin 7) = Fin.castAdd 3 (3 : Fin 4) from Fin.ext rfl, Work.WilG0.snocIt_castAdd]
@[simp] theorem snocIt4_4 (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    Work.WilG0.snocIt 4 3 z w 4 = w 0 := by
  rw [show (4 : Fin 7) = Fin.natAdd 4 (0 : Fin 3) from Fin.ext rfl, Work.WilG0.snocIt_natAdd]
@[simp] theorem snocIt4_5 (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    Work.WilG0.snocIt 4 3 z w 5 = w 1 := by
  rw [show (5 : Fin 7) = Fin.natAdd 4 (1 : Fin 3) from Fin.ext rfl, Work.WilG0.snocIt_natAdd]
@[simp] theorem snocIt4_6 (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    Work.WilG0.snocIt 4 3 z w 6 = w 2 := by
  rw [show (6 : Fin 7) = Fin.natAdd 4 (2 : Fin 3) from Fin.ext rfl, Work.WilG0.snocIt_natAdd]

@[simp] theorem snoc2_zero (z : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 2 → ℝ) 0 = z 0 := by
  rw [show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from Fin.ext rfl, Fin.snoc_castSucc]
@[simp] theorem snoc2_one (z : Fin 1 → ℝ) (t : ℝ) : (Fin.snoc z t : Fin 2 → ℝ) 1 = t := by
  rw [show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]
@[simp] theorem snoc3_zero (u : Fin 2 → ℝ) (t : ℝ) : (Fin.snoc u t : Fin 3 → ℝ) 0 = u 0 := by
  rw [show (0 : Fin 3) = Fin.castSucc (0 : Fin 2) from Fin.ext rfl, Fin.snoc_castSucc]
@[simp] theorem snoc3_one (u : Fin 2 → ℝ) (t : ℝ) : (Fin.snoc u t : Fin 3 → ℝ) 1 = u 1 := by
  rw [show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) from Fin.ext rfl, Fin.snoc_castSucc]
@[simp] theorem snoc3_two (u : Fin 2 → ℝ) (t : ℝ) : (Fin.snoc u t : Fin 3 → ℝ) 2 = t := by
  rw [show (2 : Fin 3) = Fin.last 2 from Fin.ext rfl, Fin.snoc_last]
@[simp] theorem snoc4_zero (z : Fin 1 → ℝ) (M δ y : ℝ) :
    (Fin.snoc (Fin.snoc (Fin.snoc z M) δ) y : Fin 4 → ℝ) 0 = z 0 := by
  rw [show (0 : Fin 4) = Fin.castSucc (0 : Fin 3) from Fin.ext rfl, Fin.snoc_castSucc,
    show (0 : Fin 3) = Fin.castSucc (0 : Fin 2) from Fin.ext rfl, Fin.snoc_castSucc,
    show (0 : Fin 2) = Fin.castSucc (0 : Fin 1) from Fin.ext rfl, Fin.snoc_castSucc]
@[simp] theorem snoc4_one (z : Fin 1 → ℝ) (M δ y : ℝ) :
    (Fin.snoc (Fin.snoc (Fin.snoc z M) δ) y : Fin 4 → ℝ) 1 = M := by
  rw [show (1 : Fin 4) = Fin.castSucc (1 : Fin 3) from Fin.ext rfl, Fin.snoc_castSucc,
    show (1 : Fin 3) = Fin.castSucc (1 : Fin 2) from Fin.ext rfl, Fin.snoc_castSucc,
    show (1 : Fin 2) = Fin.last 1 from Fin.ext rfl, Fin.snoc_last]
@[simp] theorem snoc4_two (z : Fin 1 → ℝ) (M δ y : ℝ) :
    (Fin.snoc (Fin.snoc (Fin.snoc z M) δ) y : Fin 4 → ℝ) 2 = δ := by
  rw [show (2 : Fin 4) = Fin.castSucc (2 : Fin 3) from Fin.ext rfl, Fin.snoc_castSucc,
    show (2 : Fin 3) = Fin.last 2 from Fin.ext rfl, Fin.snoc_last]
@[simp] theorem snoc4_three (z : Fin 1 → ℝ) (M δ y : ℝ) :
    (Fin.snoc (Fin.snoc (Fin.snoc z M) δ) y : Fin 4 → ℝ) 3 = y := by
  rw [show (3 : Fin 4) = Fin.last 3 from Fin.ext rfl, Fin.snoc_last]

theorem comp_iotax_snocIt (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    (Work.WilG0.snocIt 4 3 z w) ∘ iotax = ![z 0, w 0] := by
  funext j
  fin_cases j <;> simp [iotax]

theorem comp_iotay_snocIt (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    (Work.WilG0.snocIt 4 3 z w) ∘ iotay = ![z 3, w 1] := by
  funext j
  fin_cases j <;> simp [iotay]

theorem eval_Pinf_snocIt (s : ℝ) (z : Fin 4 → ℝ) (w : Fin 3 → ℝ) :
    MvPolynomial.eval (Work.WilG0.snocIt 4 3 z w) (Pinf s)
      = z 1 * (z 3 - z 0) ^ 2 - s * (w 1 - w 0) * (z 3 - z 0) := by
  simp only [Pinf, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, MvPolynomial.eval_C, snocIt4_0, snocIt4_1, snocIt4_3,
    snocIt4_4, snocIt4_5]
  try ring
  try ring_nf

/-! ## 6. Total-degree bounds for the data polynomials -/

theorem td_PosData_le {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (PosData P).totalDegree ≤ P.totalDegree + 3 := by
  have hX : (MvPolynomial.X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 1 :=
    Work.WilG5.td_X_le _
  have hsq : ((MvPolynomial.X (Fin.last n)) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 2 := by
    rw [pow_two]
    exact Work.WilG5.td_sq_le hX
  have hren : (MvPolynomial.rename Fin.castSucc P : MvPolynomial (Fin (n + 1)) ℝ).totalDegree
      ≤ P.totalDegree := MvPolynomial.totalDegree_rename_le Fin.castSucc P
  have hmul : ((MvPolynomial.rename Fin.castSucc P) * (MvPolynomial.X (Fin.last n)) ^ 2 :
      MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ P.totalDegree + 2 := by
    have := Work.WilG5.td_mul_le (MvPolynomial.rename Fin.castSucc P : MvPolynomial (Fin (n + 1)) ℝ)
      ((MvPolynomial.X (Fin.last n)) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ)
    omega
  have hone : (1 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree ≤ 0 := by
    rw [MvPolynomial.totalDegree_one]
  simp only [PosData]
  refine le_trans (Work.WilG5.td_sub_le
    ((MvPolynomial.rename Fin.castSucc P) * (MvPolynomial.X (Fin.last n)) ^ 2 :
      MvPolynomial (Fin (n + 1)) ℝ) (1 : MvPolynomial (Fin (n + 1)) ℝ)) (max_le ?_ ?_)
  · omega
  · omega

theorem td_Pinf_le (s : ℝ) : (Pinf s).totalDegree ≤ 3 := by
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h1 : (MvPolynomial.X 1 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h3 : (MvPolynomial.X 3 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h4 : (MvPolynomial.X 4 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h5 : (MvPolynomial.X 5 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h30 : (MvPolynomial.X 3 - MvPolynomial.X 0 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 :=
    le_trans (Work.WilG5.td_sub_le _ _) (max_le h3 h0)
  have h30sq : ((MvPolynomial.X 3 - MvPolynomial.X 0) ^ 2 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
    rw [pow_two]
    exact Work.WilG5.td_sq_le h30
  have h54 : (MvPolynomial.X 5 - MvPolynomial.X 4 : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 :=
    le_trans (Work.WilG5.td_sub_le _ _) (max_le h5 h4)
  have hA : (MvPolynomial.X 1 * (MvPolynomial.X 3 - MvPolynomial.X 0) ^ 2 :
      MvPolynomial (Fin 7) ℝ).totalDegree ≤ 3 := by
    have := Work.WilG5.td_mul_le (MvPolynomial.X 1 : MvPolynomial (Fin 7) ℝ)
      ((MvPolynomial.X 3 - MvPolynomial.X 0) ^ 2)
    omega
  have hB1 : (MvPolynomial.C s * (MvPolynomial.X 5 - MvPolynomial.X 4) :
      MvPolynomial (Fin 7) ℝ).totalDegree ≤ 1 := by
    have hc : (MvPolynomial.C s : MvPolynomial (Fin 7) ℝ).totalDegree ≤ 0 := Work.WilG5.td_C_le s
    have := Work.WilG5.td_mul_le (MvPolynomial.C s : MvPolynomial (Fin 7) ℝ)
      (MvPolynomial.X 5 - MvPolynomial.X 4)
    omega
  have hB : (MvPolynomial.C s * (MvPolynomial.X 5 - MvPolynomial.X 4) * (MvPolynomial.X 3 - MvPolynomial.X 0) :
      MvPolynomial (Fin 7) ℝ).totalDegree ≤ 2 := by
    have := Work.WilG5.td_mul_le
      (MvPolynomial.C s * (MvPolynomial.X 5 - MvPolynomial.X 4) : MvPolynomial (Fin 7) ℝ)
      (MvPolynomial.X 3 - MvPolynomial.X 0)
    omega
  simp only [Pinf]
  refine le_trans (Work.WilG5.td_sub_le
    (MvPolynomial.X 1 * (MvPolynomial.X 3 - MvPolynomial.X 0) ^ 2 : MvPolynomial (Fin 7) ℝ)
    (MvPolynomial.C s * (MvPolynomial.X 5 - MvPolynomial.X 4) * (MvPolynomial.X 3 - MvPolynomial.X 0)))
    (max_le ?_ ?_)
  · omega
  · omega

theorem td_neg_le {N : ℕ} (p : MvPolynomial (Fin N) ℝ) : (-p).totalDegree ≤ p.totalDegree := by
  have h : (-p) = (MvPolynomial.C (-1) * p : MvPolynomial (Fin N) ℝ) := by
    rw [MvPolynomial.C_neg, MvPolynomial.C_1, neg_one_mul]
  rw [h]
  have hc : (MvPolynomial.C (-1) : MvPolynomial (Fin N) ℝ).totalDegree ≤ 0 := Work.WilG5.td_C_le (-1)
  have := Work.WilG5.td_mul_le (MvPolynomial.C (-1) : MvPolynomial (Fin N) ℝ) p
  omega

theorem td_negPinf_le (s : ℝ) : (-(Pinf s)).totalDegree ≤ 3 := by
  have := td_neg_le (Pinf s)
  have := td_Pinf_le s
  omega

theorem td_PA_le : PA.totalDegree ≤ 1 := by
  have h2 : (MvPolynomial.X 2 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h3 : (MvPolynomial.X 3 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h30 : (MvPolynomial.X 3 - MvPolynomial.X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    le_trans (Work.WilG5.td_sub_le _ _) (max_le h3 h0)
  simp only [PA]
  refine le_trans (Work.WilG5.td_sub_le (MvPolynomial.X 2 : MvPolynomial (Fin 4) ℝ)
    (MvPolynomial.X 3 - MvPolynomial.X 0)) (max_le ?_ ?_)
  · omega
  · omega

theorem td_PB_le : PB.totalDegree ≤ 1 := by
  have h2 : (MvPolynomial.X 2 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h3 : (MvPolynomial.X 3 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
  have h30 : (MvPolynomial.X 3 - MvPolynomial.X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    le_trans (Work.WilG5.td_sub_le _ _) (max_le h3 h0)
  simp only [PB]
  refine le_trans (MvPolynomial.totalDegree_add
    (MvPolynomial.X 3 - MvPolynomial.X 0 : MvPolynomial (Fin 4) ℝ) (MvPolynomial.X 2)) (max_le ?_ ?_)
  · omega
  · omega

/-! ## 7. Realisation of the sub-shapes -/

theorem Big7_realize (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) :
    Big7.realize (dataBig G D s) =
      {z : Fin 7 → ℝ | z ∘ iotax ∈ G ∧ z ∘ iotay ∈ G ∧
        0 < MvPolynomial.eval z (-(Pinf s))} := by
  ext z
  simp only [Big7, OShape.realize, dataBig, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [PosShape_realize]
  tauto

/-- The key algebraic equivalence: `y ≠ x` and the difference quotient exceeds `M / s` iff
`M (y-x)^2 - s (g y - g x)(y - x) < 0`. -/
theorem body_iff (g : ℝ → ℝ) (s M x y : ℝ) :
    (M * (y - x) ^ 2 - s * (g y - g x) * (y - x) < 0) ↔
      y ≠ x ∧ M < s * Work.WilG1.dq g x y := by
  rcases eq_or_ne y x with hxy | hxy
  · subst hxy
    simp
  · have hxy' : y - x ≠ 0 := sub_ne_zero.mpr hxy
    have hB : (0 : ℝ) < (y - x) ^ 2 := sq_pos_of_ne_zero hxy'
    have key : s * Work.WilG1.dq g x y = s * (g y - g x) * (y - x) / (y - x) ^ 2 := by
      rw [Work.WilG1.dq]
      field_simp
      try ring
    rw [key, lt_div_iff₀ hB]
    constructor
    · intro h
      exact ⟨hxy, by linarith⟩
    · rintro ⟨-, h⟩
      linarith

theorem Body4_realize (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) (g : ℝ → ℝ)
    (hG : ∀ w : Fin 2 → ℝ, w ∈ G ↔ w 1 = g (w 0)) :
    Body4.realize (dataBig G D s) =
      {z : Fin 4 → ℝ | z 3 ≠ z 0 ∧ z 1 < s * Work.WilG1.dq g (z 0) (z 3)} := by
  have hbody : Body4.realize (dataBig G D s)
      = Work.WilG0.projLastIter 4 3 (Big7.realize (dataBig G D s)) := rfl
  rw [hbody, Work.WilG0.projLastIter_eq, Big7_realize]
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hx, hy, hz⟩
    rw [comp_iotax_snocIt] at hx
    rw [comp_iotay_snocIt] at hy
    rw [hG] at hx hy
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    rw [MvPolynomial.eval_neg, eval_Pinf_snocIt] at hz
    rw [hx, hy] at hz
    exact (body_iff g s (z 1) (z 0) (z 3)).mp (by linarith)
  · rintro ⟨hne, hM⟩
    refine ⟨![g (z 0), g (z 3), 0], ?_, ?_, ?_⟩
    · rw [comp_iotax_snocIt, hG]
      simp
    · rw [comp_iotay_snocIt, hG]
      simp
    · rw [MvPolynomial.eval_neg, eval_Pinf_snocIt]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have := (body_iff g s (z 1) (z 0) (z 3)).mpr ⟨hne, hM⟩
      linarith

theorem AbsSh4_realize :
    AbsSh4.realize dataAbs = {z : Fin 4 → ℝ | z 2 ≤ |z 3 - z 0|} := by
  have h : (SubShape 4).realize (PosData PA) ∪ (SubShape 4).realize (PosData PB)
      = {z : Fin 4 → ℝ | z 2 ≤ |z 3 - z 0|} := by
    rw [SubShape_realize, SubShape_realize]
    ext z
    simp only [Set.mem_union, Set.mem_ofPred_eq, PA, PB, MvPolynomial.eval_sub,
      MvPolynomial.eval_add, MvPolynomial.eval_X]
    rw [le_abs]
    constructor
    · rintro (h | h)
      · left; linarith
      · right; linarith
    · rintro (h | h)
      · left; linarith
      · right; linarith
  exact h

theorem Full4_realize (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) (g : ℝ → ℝ)
    (hG : ∀ w : Fin 2 → ℝ, w ∈ G ↔ w 1 = g (w 0)) :
    Full4.realize (dataFull4 G D s) =
      {z : Fin 4 → ℝ | z 3 = z 0 ∨ z 2 ≤ |z 3 - z 0| ∨
        (z 3 ≠ z 0 ∧ z 1 < s * Work.WilG1.dq g (z 0) (z 3))} := by
  have hp : (OShape.poly 4).realize dataPoly4 = {z : Fin 4 → ℝ | z 3 = z 0} := by
    ext z
    simp only [OShape.realize, dataPoly4, Set.mem_ofPred_eq, MvPolynomial.eval_sub,
      MvPolynomial.eval_X]
    constructor <;> intro h <;> linarith
  have hmain : Full4.realize (dataFull4 G D s)
      = (OShape.or (OShape.poly 4) AbsSh4).realize (dataPoly4, dataAbs)
        ∪ Body4.realize (dataBig G D s) := rfl
  rw [hmain, Body4_realize G D s g hG]
  have h1 : (OShape.or (OShape.poly 4) AbsSh4).realize (dataPoly4, dataAbs)
      = {z : Fin 4 → ℝ | z 3 = z 0} ∪ {z : Fin 4 → ℝ | z 2 ≤ |z 3 - z 0|} := by
    show (OShape.poly 4).realize dataPoly4 ∪ AbsSh4.realize dataAbs = _
    rw [hp, AbsSh4_realize]
  rw [h1]
  ext z
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  tauto

theorem ForallY3_realize (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) :
    ForallY3.realize (dataForallY3 G D s) =
      {w : Fin 3 → ℝ | ∀ y : ℝ, Fin.snoc w y ∈ Full4.realize (dataFull4 G D s)} := by
  ext w
  simp only [ForallY3, dataForallY3, OShape.realize, projLast, Set.mem_ofPred_eq,
    Set.mem_compl_iff]
  constructor
  · intro h y
    by_contra hc
    exact h ⟨y, hc⟩
  · rintro h ⟨y, hy⟩
    exact hy (h y)

theorem Posδ3_realize : Posδ3.realize dataPosδ = {w : Fin 3 → ℝ | 0 < w 2} := by
  have h : (PosShape 3).realize (PosData (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ))
      = {w : Fin 3 → ℝ | 0 < w 2} := by
    rw [PosShape_realize]
    ext w
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X]
  exact h

theorem S3_realize (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) :
    S3.realize (dataS3 G D s) =
      {w : Fin 3 → ℝ | 0 < w 2 ∧
        ∀ y : ℝ, Fin.snoc w y ∈ Full4.realize (dataFull4 G D s)} := by
  have hmain : S3.realize (dataS3 G D s)
      = Posδ3.realize dataPosδ ∩ ForallY3.realize (dataForallY3 G D s) := rfl
  rw [hmain, Posδ3_realize, ForallY3_realize]
  ext w
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]

theorem E2_realize (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) :
    E2.realize (dataE2 G D s) =
      {u : Fin 2 → ℝ | ∃ δ : ℝ, 0 < δ ∧
        ∀ y : ℝ, Fin.snoc (Fin.snoc u δ) y ∈ Full4.realize (dataFull4 G D s)} := by
  have hmain : E2.realize (dataE2 G D s)
      = projLast (S3.realize (dataS3 G D s)) := rfl
  rw [hmain, S3_realize]
  ext u
  simp only [projLast, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, h⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨δ, hδ, h⟩

theorem eval_X1_sub_one (u : Fin 2 → ℝ) :
    MvPolynomial.eval u (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℝ) = u 1 - 1 := by
  have h2 : (MvPolynomial.eval u) (1 : MvPolynomial (Fin 2) ℝ) = 1 := by
    rw [← MvPolynomial.C_1, MvPolynomial.eval_C]
  rw [MvPolynomial.eval_sub, MvPolynomial.eval_X, h2]

theorem Mle1_2_realize :
    Mle1_2.realize dataMle = {u : Fin 2 → ℝ | u 1 ≤ 1} := by
  have h : (SubShape 2).realize (PosData (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℝ))
      = {u : Fin 2 → ℝ | u 1 ≤ 1} := by
    rw [SubShape_realize]
    ext u
    simp only [Set.mem_ofPred_eq]
    rw [eval_X1_sub_one u]
    constructor <;> intro h <;> linarith
  exact h

/-! ## 8. The realisation of the whole shape -/

theorem FullShape_realize (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) (g : ℝ → ℝ)
    (hG : ∀ w : Fin 2 → ℝ, w ∈ G ↔ w 1 = g (w 0)) :
    FullShape.realize (fullData G D s) = Work.WilG1.liftR (Work.WilG1.infDeriv g s) := by
  have hOuter : FullShape.realize (fullData G D s)
      = {z : Fin 1 → ℝ | ∀ M : ℝ, Fin.snoc z M ∈ (S2).realize (fullData G D s)} := by
    ext z
    simp only [FullShape, OShape.realize, projLast, Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · intro h M
      by_contra hc
      exact h ⟨M, hc⟩
    · rintro h ⟨M, hM⟩
      exact hM (h M)
  rw [hOuter]
  have hS2 : (S2).realize (fullData G D s)
      = Mle1_2.realize dataMle ∪ (E2).realize (dataE2 G D s) := rfl
  ext z
  simp only [Set.mem_ofPred_eq, Work.WilG1.liftR, Work.WilG1.infDeriv]
  rw [hS2]
  simp only [Set.mem_union, Set.mem_ofPred_eq, Mle1_2_realize, E2_realize, snoc2_one]
  constructor
  · intro h M hM
    rcases h M with h1 | ⟨δ, hδ, hy⟩
    · exact absurd h1 (not_le.mpr hM)
    · refine ⟨δ, hδ, fun y hyne hlt => ?_⟩
      have hy' := hy y
      rw [Full4_realize G D s g hG, Set.mem_ofPred_eq,
        snoc4_zero, snoc4_one, snoc4_two, snoc4_three] at hy'
      rcases hy' with h' | h' | ⟨_, hq⟩
      · exact absurd h' hyne
      · exact absurd hlt (not_lt.mpr h')
      · exact hq
  · intro h M
    by_cases hM : M ≤ 1
    · exact Or.inl hM
    · have h1M : 1 < M := not_le.mp hM
      obtain ⟨δ, hδ, hy⟩ := h M h1M
      refine Or.inr ⟨δ, hδ, fun y => ?_⟩
      rw [Full4_realize G D s g hG, Set.mem_ofPred_eq,
        snoc4_zero, snoc4_one, snoc4_two, snoc4_three]
      by_cases hyx : y = z 0
      · exact Or.inl hyx
      · by_cases hle : δ ≤ |y - z 0|
        · exact Or.inr (Or.inl hle)
        · exact Or.inr (Or.inr ⟨hyx, hy y hyx (not_le.mp hle)⟩)

/-! ## 9. Goodness and the bounds -/

theorem fullShape_good (S : SOMin) (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) {F : ℕ}
    (hG : G ∈ S.Ω F D 2) : FullShape.Good S F (fullData G D s) := by
  simp only [FullShape, S2, E2, S3, Posδ3, ForallY3, Full4, AbsSh4, Body4, Big7, Mle1_2,
    SubShape, PosShape, fullData, dataE2, dataS3, dataForallY3, dataFull4, dataBig,
    dataMle, dataPosδ, dataPoly4, dataAbs, OShape.Good, and_true, true_and,
    Prod.fst, Prod.snd]
  tauto

theorem oFmt_FullShape_le (F : ℕ) : Work.WilG0.oFmt F FullShape ≤ F + 1000 := by
  simp only [FullShape, S2, E2, S3, Posδ3, ForallY3, Full4, AbsSh4, Body4, Big7, Mle1_2,
    SubShape, PosShape, Work.WilG0.oFmt]
  omega

theorem deg_fullData_le (G : Set (Fin 2 → ℝ)) (D : ℕ) (s : ℝ) :
    FullShape.deg (fullData G D s) ≤
      (Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D := by
  have hpoly : (Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D = 1000 * (D + 1) := by
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  rw [hpoly]
  have h1 : (PosData (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℝ)).totalDegree ≤ 4 := by
    have hX : (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
      have a1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
      have a0 : (1 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 0 := by
        rw [MvPolynomial.totalDegree_one]
      refine le_trans (Work.WilG5.td_sub_le (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)
        (1 : MvPolynomial (Fin 2) ℝ)) (max_le ?_ ?_)
      · omega
      · omega
    have := td_PosData_le (MvPolynomial.X 1 - 1 : MvPolynomial (Fin 2) ℝ)
    omega
  have h2 : (PosData (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ)).totalDegree ≤ 4 := by
    have hX : (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := Work.WilG5.td_X_le _
    have := td_PosData_le (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℝ)
    omega
  have h3 : (MvPolynomial.X 3 - MvPolynomial.X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    le_trans (Work.WilG5.td_sub_le _ _)
      (max_le (Work.WilG5.td_X_le (3 : Fin 4)) (Work.WilG5.td_X_le (0 : Fin 4)))
  have h4 : (PosData PA).totalDegree ≤ 4 := by
    have := td_PosData_le PA
    have := td_PA_le
    omega
  have h5 : (PosData PB).totalDegree ≤ 4 := by
    have := td_PosData_le PB
    have := td_PB_le
    omega
  have h6 : (PosData (-(Pinf s))).totalDegree ≤ 6 := by
    have := td_PosData_le (-(Pinf s))
    have := td_negPinf_le s
    omega
  simp only [FullShape, S2, E2, S3, Posδ3, ForallY3, Full4, AbsSh4, Body4, Big7, Mle1_2,
    SubShape, PosShape, fullData, dataE2, dataS3, dataForallY3, dataFull4, dataBig,
    dataMle, dataPosδ, dataPoly4, dataAbs, OShape.deg, Prod.fst, Prod.snd]
  omega

/-! ## 10. The target theorem -/

theorem infderiv_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (s : ℝ) :
    Work.WilG1.liftR (Work.WilG1.infDeriv g s) ∈
      S.Ω (F + 1000) ((Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D) 1 := by
  set G : Set (Fin 2 → ℝ) := WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) with hGdef
  have hG : ∀ w : Fin 2 → ℝ, w ∈ G ↔ w 1 = g (w 0) := by
    intro w
    have h1 : w (Fin.last 1) = w 1 := by
      rw [show (Fin.last 1 : Fin 2) = 1 from Fin.ext rfl]
    have h2 : (fun x : Fin 1 → ℝ => g (x 0)) (Fin.init w) = g (w 0) := by
      show g ((Fin.init w) 0) = g (w 0)
      congr 1
    simp only [hGdef, WilkiesDesign.graphOf, Set.mem_ofPred_eq, h1, h2]
  have hgd : G ∈ S.Ω F D 2 := by rw [hGdef]; exact hg
  have hd : FullShape.Good S F (fullData G D s) := fullShape_good S G D s hgd
  have hmem := Work.WilG0.realize_mem_Omega S FullShape F (fullData G D s) hd
  rw [FullShape_realize G D s g hG] at hmem
  exact Work.WilG5.mem_mono hmem (F + 1000)
    ((Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D)
    (oFmt_FullShape_le F) (deg_fullData_le G D s)

end Work.WilG1.Thin
