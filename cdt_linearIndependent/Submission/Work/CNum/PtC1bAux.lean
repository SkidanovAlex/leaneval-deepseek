import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.ExpISpec
import Submission.Work.CNum.MemIvS
import Submission.Work.CNum.CpxSound

/-!
# `Work.CNum.PtC1bAux`

Named pieces of the fourth-arc point certificate `ptC1b k = (3/4)·W1 k (-1)`
(`k ≤ 1024`), plus the two certified numerical facts about the radicand interval that
`MemIvS` needs.

For `k` in the fourth arc (`780 ≤ k ≤ 1024`) the point `ptC1b k` is meant to enclose
`ψ_C(e^{i·2πk/1024})`, where `E = expI k` encloses `e^{i·kπ/1024} = e^{iθ_k/2}`
(`θ_k = 2πk/1024`).  The named intervals are

* `cT1b k = (expI k).re² - (expI k).im²`, enclosing `cos θ_k`
  (since `cos(x/2)² - sin(x/2)² = cos x`);
* `X1b k = 2A·(cT1b k - γ)`, enclosing `2A(cos θ_k - γ) = PR θ_k ²`;
* `P1b k = IvS (X1b k)`, enclosing `PR θ_k = √(2A(cos θ_k - γ))`;
* `Q1b k = 2(1+c²)·(expI k).im`, enclosing `QR θ_k = 2(1+c²) sin(θ_k/2)`;
* `W1b k = -( ((-P1b k) + i·Q1b k)·(1/dR)·(expI k) )`, enclosing `Wfun (e^{iθ_k})`.

The two numerical lemmas `X1b_lo_nonneg` and `X1b_hi_lt` are kernel `decide` computations
over the 245 values `780 ≤ k ≤ 1024`; they are the side conditions of `MemIvS`
(`0 ≤ X1b k` for the interval square root, and `X1b k < 2^40` for the binary-search range).
-/

namespace Work.CNum

open Work.ANum

/-- `cos θ_k` interval (`θ_k = 2πk/1024`). -/
def cT1b (k : ℕ) : Iv := Iv.sub (Iv.sq (expI k).re) (Iv.sq (expI k).im)

/-- `2A(cos θ_k - γ)` interval. -/
def X1b (k : ℕ) : Iv := IvM (ratIv 791282 10000) (Iv.sub (cT1b k) (ratIv 27559 395641))

/-- `√(2A(cos θ_k - γ))` interval. -/
def P1b (k : ℕ) : Iv := IvS (X1b k)

/-- `2(1+c²) sin(θ_k/2)` interval. -/
def Q1b (k : ℕ) : Iv := IvM (ratIv 629 50) (expI k).im

/-- The fourth-arc point `W1 k (-1)` with its intermediate intervals named. -/
def W1b (k : ℕ) : Cpx :=
  Cpx.neg (Cpx.mul (Cpx.mulr ⟨Iv.neg (P1b k), Q1b k⟩ (ratIv 50 429)) (expI k))

theorem W1b_eq (k : ℕ) : W1 k (-1) = W1b k := rfl

theorem ptC1b_eq (k : ℕ) : ptC1b k = Cpx.mulr (W1b k) (ratIv 3 4) := rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all : ∀ k ∈ Finset.Icc 780 1024, 0 ≤ (X1b k).lo := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem X1b_hi_all : ∀ k ∈ Finset.Icc 780 1024,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide

/-- The radicand interval is nonnegative on the fourth arc. -/
theorem X1b_lo_nonneg {k : ℕ} (h1 : 780 ≤ k) (h2 : k ≤ 1024) : 0 ≤ (X1b k).lo :=
  X1b_lo_nonneg_all k (Finset.mem_Icc.mpr ⟨h1, h2⟩)

/-- The radicand interval stays below the `2^70` binary-search range of `isqrt`. -/
theorem X1b_hi_lt {k : ℕ} (h1 : 780 ≤ k) (h2 : k ≤ 1024) :
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 :=
  X1b_hi_all k (Finset.mem_Icc.mpr ⟨h1, h2⟩)

end Work.CNum
