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

set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p0 : ∀ k ∈ Finset.Icc 780 795, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p1 : ∀ k ∈ Finset.Icc 796 811, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p2 : ∀ k ∈ Finset.Icc 812 827, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p3 : ∀ k ∈ Finset.Icc 828 843, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p4 : ∀ k ∈ Finset.Icc 844 859, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p5 : ∀ k ∈ Finset.Icc 860 875, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p6 : ∀ k ∈ Finset.Icc 876 891, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p7 : ∀ k ∈ Finset.Icc 892 907, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p8 : ∀ k ∈ Finset.Icc 908 923, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p9 : ∀ k ∈ Finset.Icc 924 939, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p10 : ∀ k ∈ Finset.Icc 940 955, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p11 : ∀ k ∈ Finset.Icc 956 971, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p12 : ∀ k ∈ Finset.Icc 972 987, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p13 : ∀ k ∈ Finset.Icc 988 1003, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p14 : ∀ k ∈ Finset.Icc 1004 1019, 0 ≤ (X1b k).lo := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_lo_nonneg_all_p15 : ∀ k ∈ Finset.Icc 1020 1024, 0 ≤ (X1b k).lo := by decide +kernel
theorem X1b_lo_nonneg_all : ∀ k ∈ Finset.Icc 780 1024, 0 ≤ (X1b k).lo := by
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  by_cases h0 : k ≤ 795
  · exact X1b_lo_nonneg_all_p0 k (Finset.mem_Icc.mpr ⟨by omega, h0⟩)
  by_cases h1 : k ≤ 811
  · exact X1b_lo_nonneg_all_p1 k (Finset.mem_Icc.mpr ⟨by omega, h1⟩)
  by_cases h2 : k ≤ 827
  · exact X1b_lo_nonneg_all_p2 k (Finset.mem_Icc.mpr ⟨by omega, h2⟩)
  by_cases h3 : k ≤ 843
  · exact X1b_lo_nonneg_all_p3 k (Finset.mem_Icc.mpr ⟨by omega, h3⟩)
  by_cases h4 : k ≤ 859
  · exact X1b_lo_nonneg_all_p4 k (Finset.mem_Icc.mpr ⟨by omega, h4⟩)
  by_cases h5 : k ≤ 875
  · exact X1b_lo_nonneg_all_p5 k (Finset.mem_Icc.mpr ⟨by omega, h5⟩)
  by_cases h6 : k ≤ 891
  · exact X1b_lo_nonneg_all_p6 k (Finset.mem_Icc.mpr ⟨by omega, h6⟩)
  by_cases h7 : k ≤ 907
  · exact X1b_lo_nonneg_all_p7 k (Finset.mem_Icc.mpr ⟨by omega, h7⟩)
  by_cases h8 : k ≤ 923
  · exact X1b_lo_nonneg_all_p8 k (Finset.mem_Icc.mpr ⟨by omega, h8⟩)
  by_cases h9 : k ≤ 939
  · exact X1b_lo_nonneg_all_p9 k (Finset.mem_Icc.mpr ⟨by omega, h9⟩)
  by_cases h10 : k ≤ 955
  · exact X1b_lo_nonneg_all_p10 k (Finset.mem_Icc.mpr ⟨by omega, h10⟩)
  by_cases h11 : k ≤ 971
  · exact X1b_lo_nonneg_all_p11 k (Finset.mem_Icc.mpr ⟨by omega, h11⟩)
  by_cases h12 : k ≤ 987
  · exact X1b_lo_nonneg_all_p12 k (Finset.mem_Icc.mpr ⟨by omega, h12⟩)
  by_cases h13 : k ≤ 1003
  · exact X1b_lo_nonneg_all_p13 k (Finset.mem_Icc.mpr ⟨by omega, h13⟩)
  by_cases h14 : k ≤ 1019
  · exact X1b_lo_nonneg_all_p14 k (Finset.mem_Icc.mpr ⟨by omega, h14⟩)
  exact X1b_lo_nonneg_all_p15 k (Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩)

set_option maxRecDepth 100000 in
theorem X1b_hi_all_p0 : ∀ k ∈ Finset.Icc 780 795,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p1 : ∀ k ∈ Finset.Icc 796 811,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p2 : ∀ k ∈ Finset.Icc 812 827,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p3 : ∀ k ∈ Finset.Icc 828 843,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p4 : ∀ k ∈ Finset.Icc 844 859,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p5 : ∀ k ∈ Finset.Icc 860 875,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p6 : ∀ k ∈ Finset.Icc 876 891,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p7 : ∀ k ∈ Finset.Icc 892 907,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p8 : ∀ k ∈ Finset.Icc 908 923,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p9 : ∀ k ∈ Finset.Icc 924 939,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p10 : ∀ k ∈ Finset.Icc 940 955,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p11 : ∀ k ∈ Finset.Icc 956 971,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p12 : ∀ k ∈ Finset.Icc 972 987,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p13 : ∀ k ∈ Finset.Icc 988 1003,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p14 : ∀ k ∈ Finset.Icc 1004 1019,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
set_option maxRecDepth 100000 in
theorem X1b_hi_all_p15 : ∀ k ∈ Finset.Icc 1020 1024,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by decide +kernel
theorem X1b_hi_all : ∀ k ∈ Finset.Icc 780 1024,
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 := by
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  by_cases h0 : k ≤ 795
  · exact X1b_hi_all_p0 k (Finset.mem_Icc.mpr ⟨by omega, h0⟩)
  by_cases h1 : k ≤ 811
  · exact X1b_hi_all_p1 k (Finset.mem_Icc.mpr ⟨by omega, h1⟩)
  by_cases h2 : k ≤ 827
  · exact X1b_hi_all_p2 k (Finset.mem_Icc.mpr ⟨by omega, h2⟩)
  by_cases h3 : k ≤ 843
  · exact X1b_hi_all_p3 k (Finset.mem_Icc.mpr ⟨by omega, h3⟩)
  by_cases h4 : k ≤ 859
  · exact X1b_hi_all_p4 k (Finset.mem_Icc.mpr ⟨by omega, h4⟩)
  by_cases h5 : k ≤ 875
  · exact X1b_hi_all_p5 k (Finset.mem_Icc.mpr ⟨by omega, h5⟩)
  by_cases h6 : k ≤ 891
  · exact X1b_hi_all_p6 k (Finset.mem_Icc.mpr ⟨by omega, h6⟩)
  by_cases h7 : k ≤ 907
  · exact X1b_hi_all_p7 k (Finset.mem_Icc.mpr ⟨by omega, h7⟩)
  by_cases h8 : k ≤ 923
  · exact X1b_hi_all_p8 k (Finset.mem_Icc.mpr ⟨by omega, h8⟩)
  by_cases h9 : k ≤ 939
  · exact X1b_hi_all_p9 k (Finset.mem_Icc.mpr ⟨by omega, h9⟩)
  by_cases h10 : k ≤ 955
  · exact X1b_hi_all_p10 k (Finset.mem_Icc.mpr ⟨by omega, h10⟩)
  by_cases h11 : k ≤ 971
  · exact X1b_hi_all_p11 k (Finset.mem_Icc.mpr ⟨by omega, h11⟩)
  by_cases h12 : k ≤ 987
  · exact X1b_hi_all_p12 k (Finset.mem_Icc.mpr ⟨by omega, h12⟩)
  by_cases h13 : k ≤ 1003
  · exact X1b_hi_all_p13 k (Finset.mem_Icc.mpr ⟨by omega, h13⟩)
  by_cases h14 : k ≤ 1019
  · exact X1b_hi_all_p14 k (Finset.mem_Icc.mpr ⟨by omega, h14⟩)
  exact X1b_hi_all_p15 k (Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩)

/-- The radicand interval is nonnegative on the fourth arc. -/
theorem X1b_lo_nonneg {k : ℕ} (h1 : 780 ≤ k) (h2 : k ≤ 1024) : 0 ≤ (X1b k).lo :=
  X1b_lo_nonneg_all k (Finset.mem_Icc.mpr ⟨h1, h2⟩)

/-- The radicand interval stays below the `2^70` binary-search range of `isqrt`. -/
theorem X1b_hi_lt {k : ℕ} (h1 : 780 ≤ k) (h2 : k ≤ 1024) :
    (X1b k).hi.toNat * SC.toNat < 2 ^ 70 :=
  X1b_hi_all k (Finset.mem_Icc.mpr ⟨h1, h2⟩)

end Work.CNum
