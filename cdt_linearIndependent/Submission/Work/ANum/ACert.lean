import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.ANum.PsiAEncl
import Submission.Work.ANum.CSqrt
import Submission.Work.ANum.Log

/-! # Area ANum — the arc certificate for the rearrangement-integral bound (definitions)

This module collects the *computable data* of the per-arc certificate for conjunct 2 of
`Submission.CDTPlan.ANumerics` (the bound `rearrInt … ≤ 112/10`).

Design (see `Submission/Work/ANum/STATUS.md`): partition the three circles
`|z| = 1/10⁴`, `|z| = 283/500`, `|z| = 1` into `N k` arcs; for each arc compute

* a *point* enclosure of `psiA (c k · rot t_j)` at the arc's left endpoint `t_j = j/N`,
* a *arc* enclosure of `psiA (c k · rot t)` for `t` in the arc,

and bound `circleLog (phiAfam k) t` by `[value at t_j] + [derivative bound]·(arc width)`,
falling back to the ball bound `h_log_bound` on the (few) arcs containing a critical point of
one of the five contour stages.

All definitions here are *computable* (primitive recursion / integer arithmetic) so that the
kernel can evaluate them; the soundness lemmas live in sibling modules.
-/

namespace Work.ANum

open Submission.CDTPlan Complex

/-- The interval `[⌊p·SC/q⌋, ⌈p·SC/q⌉]` (outer enclosure of the rational `p/q`). -/
def ratIv (p : ℤ) (q : ℕ) : Iv :=
  ⟨Int.ediv (p * SC) (q : ℤ), -Int.ediv (-(p * SC)) (q : ℤ)⟩

lemma m2r_int (n : ℤ) : m2r n = (n : ℝ) / (SC : ℝ) := rfl

lemma m2r_mul_int (a b : ℤ) : m2r (a * b) = (a : ℝ) * m2r b := by
  simp only [m2r]
  push_cast
  field_simp

theorem mem_ratIv {p : ℤ} {q : ℕ} (hq : 0 < q) : (ratIv p q).Mem ((p : ℝ) / q) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have key : ∀ a : ℤ, m2r (Int.ediv a (q : ℤ)) * (q : ℝ) ≤ m2r a := by
    intro a
    have h : Int.ediv a (q : ℤ) * (q : ℤ) ≤ a := Int.ediv_mul_le a hqZ
    have h2 : m2r (Int.ediv a (q : ℤ) * (q : ℤ)) ≤ m2r a := m2r_le h
    have hm : m2r (Int.ediv a (q : ℤ) * (q : ℤ))
        = (m2r (Int.ediv a (q : ℤ))) * (q : ℝ) := by
      rw [m2r_mul_int]
      simp only [m2r]
      push_cast
      ring
    rwa [hm] at h2
  have hp : m2r (p * SC) = (p : ℝ) := by
    rw [m2r_mul_int, m2r_SC, mul_one]
  have hnp : m2r (-(p * SC)) = -(p : ℝ) := by rw [m2r_neg, hp]
  constructor
  · show m2r (Int.ediv (p * SC) (q : ℤ)) ≤ (p : ℝ) / (q : ℝ)
    rw [le_div_iff₀ hqR]
    rw [← hp]
    exact key (p * SC)
  · show (p : ℝ) / (q : ℝ) ≤ m2r (-Int.ediv (-(p * SC)) (q : ℤ))
    rw [div_le_iff₀ hqR, m2r_neg]
    have h := key (-(p * SC))
    rw [hnp] at h
    nlinarith [h]

end Work.ANum

/-! ## The numerical data of the arc certificate -/

namespace Work.ANum

open Submission.CDTPlan Complex

/-- The pre-scaling `s = 491/500` of the Theorem-A contour. -/
def S491 : CD := cst (ratIv 491 500)

/-- The four stage rotations `rot tⱼ` (`t = (2033/25000, 2927/25000, 453/12500, -1971/25000)`). -/
def RW1 : CD := ⟨⟨936604608, 936604609⟩, ⟨525065054, 525065055⟩⟩
def RW2 : CD := ⟨⟨796077079, 796077080⟩, ⟨720543397, 720543398⟩⟩
def RW3 : CD := ⟨⟨1046025941, 1046025942⟩, ⟨242386540, 242386541⟩⟩
def RW4 : CD := ⟨⟨944672293, 944672294⟩, ⟨-510407448, -510407447⟩⟩

/-- The slit constants `A = (1+r)²`, `B = 2(1-6r+r²)`, `E = 2(r-1)²`, `C = 1+r`, `G = 8r`. -/
def cA1 : Iv := ratIv 361 100
def cB1 : Iv := ratIv (-359) 50
def cE1 : Iv := ratIv 1 50
def cC1 : Iv := ratIv 19 10
def cG1 : Iv := ratIv 36 5
def cA2 : Iv := ratIv 1008016 390625
def cB2 : Iv := ratIv (-1773968) 390625
def cE2 : Iv := ratIv 121032 390625
def cC2 : Iv := ratIv 1004 625
def cG2 : Iv := ratIv 3032 625
def cA3 : Iv := ratIv 3697929 1562500
def cB3 : Iv := ratIv (-3032071) 781250
def cE3 : Iv := ratIv 332929 781250
def cC3 : Iv := ratIv 1923 1250
def cG3 : Iv := ratIv 2692 625
def cA4 : Iv := ratIv 305795169 100000000
def cB4 : Iv := ratIv (-293164831) 50000000
def cE4 : Iv := ratIv 6315169 50000000
def cC4 : Iv := ratIv 17487 10000
def cG4 : Iv := ratIv 7487 1250

/-- The lune constants (`c = 36/5`): `B = 1+c²`, `C2 = 16c²`, `Dc = 2(c²-1)`, `RC = -4/5`. -/
def cBl : Iv := ratIv 1321 25
def cC2l : Iv := ratIv 20736 25
def cDcl : Iv := ratIv 2542 25
def cRC : Iv := ratIv (-4) 5

/-- The rectangle enclosure of the whole contour, with the constants substituted. -/
def psiAEnclA (D : CD) : CD :=
  psiAEncl S491 RW1 RW2 RW3 RW4
    cA1 cB1 cE1 cC1 cG1 cA2 cB2 cE2 cC2 cG2 cA3 cB3 cE3 cC3 cG3 cA4 cB4 cE4 cC4 cG4
    cBl cC2l cDcl cRC D

/-! ## The arc partition -/

/-- `rotPowAux fuel acc b e`: binary exponentiation of the rectangle `b` with accumulator `acc`,
using `fuel` steps (enough when `e < 2^fuel`). -/
def rotPowAux : ℕ → CD → CD → ℕ → CD
  | 0, acc, _, _ => acc
  | (k + 1), acc, b, e =>
      if e = 0 then acc
      else rotPowAux k (if e % 2 = 1 then acc.mul b else acc) (b.mul b) (e / 2)

/-- An enclosure of `w^n` for `n < 2^14` (binary exponentiation from a rectangle `W ∋ w`). -/
def rotPow2 (W : CD) (n : ℕ) : CD := rotPowAux 14 ONE W n

/-- The enclosure of `rot (1/4096)` (the step of the arc partition):
`cos(2π/4096) ≈ 1073740560.5/SC`, `sin(2π/4096) ≈ 1647098.8/SC`. -/
def W4096 : CD := ⟨⟨1073740560, 1073740561⟩, ⟨1647098, 1647099⟩⟩

/-! ## The per-arc boxes -/

/-- The partition size (all three circles). -/
def NARC : ℕ := 4096

/-- A bound for `2π/NARC` at scale `SC`. -/
def RHOARC : ℤ := 1647100

/-- The scaling `c k` of the three maps `φ_A(c_k·z)`. -/
def cK : Fin 3 → Iv := ![ratIv 1 10000, ratIv 283 500, ratIv 1 1]

/-- The rectangle enclosing `rot t` for `t` in the `j`-th arc. -/
def arcBox (j : ℕ) : CD := (rotPow2 W4096 j).mul (sqAround SC 0 RHOARC)

/-- The rectangle enclosing `c k · rot t` for `t` in the `j`-th arc. -/
def inArc (k : Fin 3) (j : ℕ) : CD := (cst (cK k)).mul (arcBox j)

/-- The rectangle enclosing `c k · rot (j/NARC)` (the arc's left endpoint). -/
def inPt (k : Fin 3) (j : ℕ) : CD := (cst (cK k)).mul (rotPow2 W4096 j)

/-- The `psiA`-image rectangle of the `j`-th arc of the `k`-th circle. -/
def qArc (k : Fin 3) (j : ℕ) : CD := psiAEnclA (inArc k j)

/-- The `psiA`-image rectangle of the arc's left endpoint. -/
def qPt (k : Fin 3) (j : ℕ) : CD := psiAEnclA (inPt k j)



end Work.ANum
