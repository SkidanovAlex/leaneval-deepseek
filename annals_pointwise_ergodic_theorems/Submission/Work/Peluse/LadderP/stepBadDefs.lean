import Mathlib
import Submission.Work.Peluse.LadderP.stepPState
import Submission.Work.Peluse.Concat.gcdBoxBadCount

/-!
# Definitions and elementary lemmas for the exceptional-set count of the ladder step

This file contains the vocabulary of `Work.Peluse.LadderP.stepBadCount`:

* `patZ` — a sign pattern as a `{0,1}`-valued integer vector;
* `stepLin` — the linear form `a + b_ω` attached to a pattern `ω`, in the reduced coordinates
  `(A,B,m,a)` where `A,B` are the head parts of `h,h'`, `m = h'_{last}` and `a` is the averaged
  parameter; it satisfies `a + b_ω = a - m - 1 + ω·(A-B)`;
* `badBox` — the two-dimensional box of integer pairs with a large gcd, whose cardinality is
  bounded by `Concat.gcdBoxBadCount`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- A sign pattern as a `{0,1}`-valued integer vector. -/
def patZ {j : ℕ} (ω : Fin j → Bool) : Fin j → ℤ := fun i => if ω i then 1 else 0

/-- The linear form `a + b_ω` attached to the pattern `ω`, in the reduced coordinates `(A,B,m,a)`:
`stepLin ω A B m a = (a:ℤ) - (m:ℤ) - 1 + ω·(A - B)`. -/
def stepLin {j M₁ : ℕ} (ω : Fin j → Bool) (A B : Fin j → Fin M₁) (m a : ℕ) : ℤ :=
  (a : ℤ) - (m : ℤ) - 1 + Concat.dotZ ω (fun i => (A i : ℤ) - (B i : ℤ))

lemma dotZ_eq_sum_patZ {j : ℕ} (ω : Fin j → Bool) (u : Fin j → ℤ) :
    Concat.dotZ ω u = ∑ i, patZ ω i * u i := by
  simp only [Concat.dotZ, patZ]
  exact Finset.sum_congr rfl (fun i _ => by by_cases hi : ω i <;> simp [hi])

/-- In the original coordinates, `a + (step shift of `ω`)` is the reduced linear form. -/
lemma add_stepShift_eq_stepLin {j M₁ : ℕ} (h h' : Fin (j+1) → Fin M₁) (ω : Fin j → Bool)
    (a : ℕ) :
    (a : ℤ) + stepShift h h' ω
      = stepLin ω (headPart h) (headPart h') (h' (Fin.last j)) a := by
  have hfun : Concat.tupSub (headPart h) (headPart h')
      = fun i => (headPart h i : ℤ) - (headPart h' i : ℤ) := by
    funext i
    simp only [Concat.tupSub]
    ring
  rw [stepLin, stepShift, hfun]
  ring

/-- The difference of two linear forms sees only the difference `A - B`. -/
lemma stepLin_sub {j M₁ : ℕ} (ω ω' : Fin j → Bool) (A B : Fin j → Fin M₁) (m a : ℕ) :
    stepLin ω' A B m a - stepLin ω A B m a
      = ∑ i, (patZ ω' i - patZ ω i) * ((A i : ℤ) - (B i : ℤ)) := by
  rw [stepLin, stepLin, dotZ_eq_sum_patZ, dotZ_eq_sum_patZ]
  have h1 : (a : ℤ) - (m : ℤ) - 1 + ∑ i, patZ ω' i * ((A i : ℤ) - (B i : ℤ))
      - ((a : ℤ) - (m : ℤ) - 1 + ∑ i, patZ ω i * ((A i : ℤ) - (B i : ℤ)))
      = (∑ i, patZ ω' i * ((A i : ℤ) - (B i : ℤ)))
        - (∑ i, patZ ω i * ((A i : ℤ) - (B i : ℤ))) := by ring
  rw [h1, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The two-dimensional box of pairs with coordinate gcd exceeding `Q`. -/
def badBox (D : ℕ) (Q : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(D : ℤ)) (D : ℤ) ×ˢ Finset.Icc (-(D : ℤ)) (D : ℤ)).filter
    (fun z => Q < ((Int.gcd z.1 z.2 : ℕ) : ℝ))

lemma badBox_card_le {D : ℕ} (hD : 1 ≤ D) {Q : ℝ} (hQ : 1 ≤ Q) :
    ((badBox D Q).card : ℝ) ≤ 36 * (D : ℝ) ^ 2 / Q :=
  Concat.gcdBoxBadCount (M := D) hD hQ

/-- The reduced linear form is bounded by `(j+1) * M₁` on the relevant range. -/
lemma stepLin_abs_le {j M₁ : ℕ} (ω : Fin j → Bool) (A B : Fin j → Fin M₁) (m a : ℕ)
    (ha1 : 1 ≤ a) (ha2 : a ≤ M₁) (hm : m < M₁) :
    |stepLin ω A B m a| ≤ ((j + 1) * M₁ : ℤ) := by
  have ham : |(a : ℤ) - (m : ℤ) - 1| ≤ (M₁ : ℤ) - 1 := by
    have h1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha1
    have h2 : (a : ℤ) ≤ (M₁ : ℤ) := by exact_mod_cast ha2
    have h3 : (0 : ℤ) ≤ (m : ℤ) := by positivity
    have h4 : (m : ℤ) ≤ (M₁ : ℤ) - 1 := by
      have h : (m : ℤ) < (M₁ : ℤ) := by exact_mod_cast hm
      omega
    rw [abs_le]
    constructor <;> omega
  have hAB : ∀ i : Fin j, |((A i : ℤ) - (B i : ℤ))| ≤ (M₁ : ℤ) - 1 := by
    intro i
    have hA : (A i : ℤ) ≤ (M₁ : ℤ) - 1 := by
      have h : (A i : ℤ) < (M₁ : ℤ) := by exact_mod_cast (A i).isLt
      omega
    have hB : (B i : ℤ) ≤ (M₁ : ℤ) - 1 := by
      have h : (B i : ℤ) < (M₁ : ℤ) := by exact_mod_cast (B i).isLt
      omega
    have hA0 : (0 : ℤ) ≤ (A i : ℤ) := by positivity
    have hB0 : (0 : ℤ) ≤ (B i : ℤ) := by positivity
    rw [abs_le]
    constructor <;> omega
  have hM0 : (0 : ℤ) ≤ (M₁ : ℤ) - 1 := by
    have h : (1 : ℤ) ≤ (M₁ : ℤ) := by exact_mod_cast (by omega : 1 ≤ M₁)
    omega
  have hS : |Concat.dotZ ω (fun i => (A i : ℤ) - (B i : ℤ))| ≤ (j : ℤ) * ((M₁ : ℤ) - 1) := by
    calc |Concat.dotZ ω (fun i => (A i : ℤ) - (B i : ℤ))|
        = |∑ i : Fin j, (if ω i then ((A i : ℤ) - (B i : ℤ)) else 0)| := rfl
      _ ≤ ∑ i : Fin j, |(if ω i then ((A i : ℤ) - (B i : ℤ)) else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin j, ((M₁ : ℤ) - 1) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          by_cases hi : ω i
          · rw [if_pos hi]; exact hAB i
          · rw [if_neg hi, abs_zero]; exact hM0
      _ = (j : ℤ) * ((M₁ : ℤ) - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [stepLin]
  calc |(a : ℤ) - (m : ℤ) - 1 + Concat.dotZ ω (fun i => (A i : ℤ) - (B i : ℤ))|
      ≤ |(a : ℤ) - (m : ℤ) - 1|
        + |Concat.dotZ ω (fun i => (A i : ℤ) - (B i : ℤ))| := abs_add_le _ _
    _ ≤ ((M₁ : ℤ) - 1) + (j : ℤ) * ((M₁ : ℤ) - 1) := add_le_add ham hS
    _ = ((j : ℤ) + 1) * ((M₁ : ℤ) - 1) := by ring
    _ ≤ ((j : ℤ) + 1) * (M₁ : ℤ) := by
        have hj : (0 : ℤ) ≤ (j : ℤ) + 1 := by positivity
        nlinarith
    _ = (((j + 1) * M₁ : ℕ) : ℤ) := by push_cast; ring

/-- The reduced coordinates `(A,r,B,m,a)` of a triple `(h,h',a)`: the head part and the last
coordinate of `h` (namely `A`,`r`), those of `h'` (namely `B`,`m`), and the index `a` of the
averaged parameter `a+1`. -/
structure RedIdx (j M₁ : ℕ) where
  A : Fin j → Fin M₁
  r : Fin M₁
  B : Fin j → Fin M₁
  m : Fin M₁
  a : Fin M₁
deriving DecidableEq

/-- The equivalence with the product form. -/
def redIdxEquiv (j M₁ : ℕ) :
    RedIdx j M₁ ≃ (((Fin j → Fin M₁) × Fin M₁) × ((Fin j → Fin M₁) × Fin M₁)) × Fin M₁ where
  toFun t := (((t.A, t.r), (t.B, t.m)), t.a)
  invFun s := ⟨s.1.1.1, s.1.1.2, s.1.2.1, s.1.2.2, s.2⟩
  left_inv t := by cases t; rfl
  right_inv s := by obtain ⟨⟨⟨A, r⟩, ⟨B, m⟩⟩, a⟩ := s; rfl

instance (j M₁ : ℕ) : Fintype (RedIdx j M₁) :=
  Fintype.ofEquiv _ (redIdxEquiv j M₁).symm

/-- The pair of linear forms attached to a pair of patterns, in the reduced coordinates. -/
def redPair {j M₁ : ℕ} (ω ω' : Fin j → Bool) (t : RedIdx j M₁) : ℤ × ℤ :=
  (stepLin ω t.A t.B t.m ((t.a : ℕ) + 1), stepLin ω' t.A t.B t.m ((t.a : ℕ) + 1))


/-- Extensionality for the reduced coordinates. -/
@[ext] theorem RedIdx.ext' {j M₁ : ℕ} {x y : RedIdx j M₁} (hA : x.A = y.A) (hr : x.r = y.r)
    (hB : x.B = y.B) (hm : x.m = y.m) (ha : x.a = y.a) : x = y := by
  cases x; cases y; simp_all

/-- The reduced linear form is injective in the parameter. -/
lemma stepLin_inj {j M₁ : ℕ} (ω : Fin j → Bool) (A B : Fin j → Fin M₁) (m : ℕ)
    {a a' : ℕ} (h : stepLin ω A B m a = stepLin ω A B m a') : a = a' := by
  simp only [stepLin] at h
  have : ((a : ℤ)) = ((a' : ℤ)) := by linarith
  omega

/-- The aggregate linear form of a repacked tuple is the reduced linear form of the corresponding
reduced coordinates. -/
lemma stepShift_snoc_eq {j M₁ : ℕ} (y : RedIdx j M₁) (ω : Fin j → Bool) :
    (((y.a : ℕ) + 1 : ℤ) + stepShift (Fin.snoc y.A y.r) (Fin.snoc y.B y.m) ω)
      = stepLin ω y.A y.B (y.m : ℕ) ((y.a : ℕ) + 1) := by
  have h := add_stepShift_eq_stepLin (Fin.snoc y.A y.r) (Fin.snoc y.B y.m) ω ((y.a : ℕ) + 1)
  push_cast at h
  rw [h]
  have e1 : headPart (Fin.snoc y.A y.r) = y.A := by
    funext i; simp [headPart, Fin.snoc_castSucc]
  have e2 : headPart (Fin.snoc y.B y.m) = y.B := by
    funext i; simp [headPart, Fin.snoc_castSucc]
  rw [e1, e2]
  simp only [Fin.snoc_last]


/-- `headPart` is `Fin.init`. -/
lemma headPart_eq_init {j M₁ : ℕ} (h : Fin (j+1) → Fin M₁) : headPart h = Fin.init h := rfl


end

end Work.Peluse.LadderP
