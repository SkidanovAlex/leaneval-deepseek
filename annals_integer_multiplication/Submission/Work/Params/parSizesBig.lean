import Mathlib
import Submission.Work.Params.defs
import Submission.Work.Params.basic
import Submission.Work.Params.tsfacts
import Submission.Work.Params.uparfacts
import Submission.Work.Params.QallPowNr

/-!
# `Work.Params.parSizesBig`

For every `n` with `65755586 ≤ n.size` (the "big `n`" regime of the `Params` area — the size
threshold reached by `n₁ = 2^{2^40·8d}`, see `n1SizeBig`) every parameter of paper §5.1 has binary
length at most `n.size + 4`:

* `b = ⌈log₂ n⌉ ≤ n.size` and `p = 6b`;
* `α = ⌈(12d²b)^{1/4}⌉ = √√(12d²b-1) + 1`;
* `k_T = ⌈log₂ ((4n+b-1)/b)⌉ ≤ n.size + 3`, `T = 2^{k_T}`, `k_r = ⌈k_T/d⌉ ≤ k_T`, `r = 2^{k_r}`;
* `d' = d·k_r - k_T < d`, `L = ⌊(2d-1)r/(4d)⌋ + 1 ≤ r + 1`;
* `u₀ < L + F·Q ≤ (r+1) + 2^{n.size+2}` (the last bound is `QallPowNr`).

Every claim is proved in the form `X < 2 ^ (n.size + 4)` via `Nat.size_le`, so the kernel never has
to evaluate a concrete huge power.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-! ## Elementary lemmas on `Nat.size`, roots and powers of two -/

/-- `(sqrt a).size ≤ a.size / 2 + 1`: a square root roughly halves the binary length. -/
theorem sqrt_size_le (a : ℕ) : (Nat.sqrt a).size ≤ a.size / 2 + 1 := by
  rw [Nat.size_le, Nat.sqrt_lt]
  have hle : a.size ≤ 2 * (a.size / 2 + 1) := by
    have h := Nat.div_add_mod a.size 2
    omega
  have h1 : a < 2 ^ a.size := Nat.lt_size_self a
  have h2 : (2 : ℕ) ^ a.size ≤ 2 ^ (2 * (a.size / 2 + 1)) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h3 : (2 : ℕ) ^ (2 * (a.size / 2 + 1))
      = 2 ^ (a.size / 2 + 1) * 2 ^ (a.size / 2 + 1) := by
    have hexp : 2 * (a.size / 2 + 1) = (a.size / 2 + 1) + (a.size / 2 + 1) := by ring
    rw [hexp, pow_add]
  rw [h3] at h2
  exact lt_of_lt_of_le h1 h2

/-- `(a * b).size ≤ a.size + b.size`. -/
theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  rw [Nat.size_le]
  calc a * b < 2 ^ a.size * 2 ^ b.size := Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)
    _ = 2 ^ (a.size + b.size) := (pow_add 2 a.size b.size).symm

/-- `(a + 1).size ≤ a.size + 1`. -/
theorem size_succ_le (a : ℕ) : (a + 1).size ≤ a.size + 1 := by
  rw [Nat.size_le]
  exact lt_of_le_of_lt (Nat.succ_le_of_lt (Nat.lt_size_self a))
    (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- `8 * 2 ^ e = 2 ^ (e + 3)`. -/
theorem eight_mul_two_pow_eq (e : ℕ) : 8 * (2 : ℕ) ^ e = 2 ^ (e + 3) := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
  rw [show 3 + e = e + 3 by omega]

/-- `4 * 2 ^ e = 2 ^ (e + 2)`. -/
theorem four_mul_two_pow_eq (e : ℕ) : 4 * (2 : ℕ) ^ e = 2 ^ (e + 2) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
  rw [show 2 + e = e + 2 by omega]

/-- `2 ^ e + 1 < 2 ^ k` when `e ≥ 1` and `e + 1 ≤ k`. -/
theorem two_pow_add_one_lt_of {e k : ℕ} (h : e + 1 ≤ k) (he : 1 ≤ e) :
    (2 : ℕ) ^ e + 1 < 2 ^ k := by
  have h2 : 2 ≤ (2 : ℕ) ^ e := by
    have h := Nat.pow_le_pow_right (by norm_num : 0 < 2) he
    simpa using h
  have h1 : (2 : ℕ) ^ e + 1 < 2 ^ (e + 1) := by
    rw [pow_succ]
    omega
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h)

/-- The `α` bound: `α = √√(12d²b-1) + 1 < 2 ^ (n.size + 4)` for `65755586 ≤ n.size`. -/
theorem apar_lt_pow (n : ℕ) (hsz : 65755586 ≤ n.size) :
    HvdH.apar n < 2 ^ (n.size + 4) := by
  have hn : n < 2 ^ n.size := (Nat.size_le).mp le_rfl
  have hNs : n.size < 2 ^ n.size := Nat.lt_two_pow_self (n := n.size)
  have hb : HvdH.bpar n ≤ n.size := by
    rw [HvdH.bpar, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    exact le_of_lt hn
  have hA : 12 * HvdH.D ^ 2 ≤ 2 ^ 26 := by norm_num [HvdH.D]
  -- `x := 12 d² b - 1 < 2 ^ (n.size + 26)`
  have hx : 12 * HvdH.D ^ 2 * HvdH.bpar n - 1 < 2 ^ (n.size + 26) := by
    have h1 : 12 * HvdH.D ^ 2 * HvdH.bpar n ≤ 2 ^ 26 * n.size := by
      calc 12 * HvdH.D ^ 2 * HvdH.bpar n ≤ 2 ^ 26 * HvdH.bpar n := Nat.mul_le_mul_right _ hA
        _ ≤ 2 ^ 26 * n.size := Nat.mul_le_mul_left _ hb
    have h2 : (2 : ℕ) ^ 26 * n.size < 2 ^ (n.size + 26) := by
      calc (2 : ℕ) ^ 26 * n.size < 2 ^ 26 * 2 ^ n.size :=
            Nat.mul_lt_mul_of_pos_left hNs (by norm_num)
        _ = 2 ^ (26 + n.size) := (pow_add 2 26 n.size).symm
        _ = 2 ^ (n.size + 26) := by rw [show 26 + n.size = n.size + 26 by omega]
    omega
  -- `√x < 2 ^ ((n.size+26)/2 + 1)`
  have hsq1 : Nat.sqrt (12 * HvdH.D ^ 2 * HvdH.bpar n - 1)
      < 2 ^ ((n.size + 26) / 2 + 1) := by
    rw [Nat.sqrt_lt]
    have h2 : n.size + 26 < 2 * ((n.size + 26) / 2 + 1) := by
      have h := (Nat.div_lt_iff_lt_mul (x := n.size + 26) (y := (n.size + 26) / 2 + 1)
        (by norm_num : 0 < 2)).mp (Nat.lt_succ_self _)
      omega
    calc 12 * HvdH.D ^ 2 * HvdH.bpar n - 1 < 2 ^ (n.size + 26) := hx
      _ ≤ 2 ^ (2 * ((n.size + 26) / 2 + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ ((n.size + 26) / 2 + 1) * 2 ^ ((n.size + 26) / 2 + 1) := by
          have hexp : 2 * ((n.size + 26) / 2 + 1)
              = ((n.size + 26) / 2 + 1) + ((n.size + 26) / 2 + 1) := by ring
          rw [hexp, pow_add]
  -- `√√x < 2 ^ B` with `B := ((n.size+26)/2 + 1)/2 + 1`
  have hsq2 : Nat.sqrt (Nat.sqrt (12 * HvdH.D ^ 2 * HvdH.bpar n - 1))
      < 2 ^ (((n.size + 26) / 2 + 1) / 2 + 1) := by
    rw [Nat.sqrt_lt]
    have h2 : (n.size + 26) / 2 + 1
        < 2 * (((n.size + 26) / 2 + 1) / 2 + 1) := by
      have h := (Nat.div_lt_iff_lt_mul (x := (n.size + 26) / 2 + 1)
        (y := ((n.size + 26) / 2 + 1) / 2 + 1) (by norm_num : 0 < 2)).mp (Nat.lt_succ_self _)
      omega
    calc Nat.sqrt (12 * HvdH.D ^ 2 * HvdH.bpar n - 1) < 2 ^ ((n.size + 26) / 2 + 1) := hsq1
      _ ≤ 2 ^ (2 * (((n.size + 26) / 2 + 1) / 2 + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ (((n.size + 26) / 2 + 1) / 2 + 1) * 2 ^ (((n.size + 26) / 2 + 1) / 2 + 1) := by
          have hexp : 2 * (((n.size + 26) / 2 + 1) / 2 + 1)
              = (((n.size + 26) / 2 + 1) / 2 + 1) + (((n.size + 26) / 2 + 1) / 2 + 1) := by ring
          rw [hexp, pow_add]
  -- `B + 1 ≤ n.size + 4`
  have hB : ((n.size + 26) / 2 + 1) / 2 + 1 + 1 ≤ n.size + 4 := by
    have h1 : (n.size + 26) / 2 ≤ 2 * (n.size + 2) := by
      have h := Nat.div_le_self (n.size + 26) 2
      omega
    have h2 : ((n.size + 26) / 2 + 1) / 2 ≤ n.size + 2 := by
      rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : 0 < 2)]
      omega
    omega
  rw [HvdH.apar]
  have h3 : 2 ^ (((n.size + 26) / 2 + 1) / 2 + 1) + 1
      < 2 ^ ((((n.size + 26) / 2 + 1) / 2 + 1) + 1) := by
    rw [pow_succ]
    have hp : 1 ≤ (2 : ℕ) ^ (((n.size + 26) / 2 + 1) / 2 + 1) := Nat.one_le_two_pow
    omega
  have h4 : (2 : ℕ) ^ ((((n.size + 26) / 2 + 1) / 2 + 1) + 1) ≤ 2 ^ (n.size + 4) :=
    Nat.pow_le_pow_right (by norm_num) hB
  omega

/-! ## The size bounds -/

/-- **Sizes of the parameters of paper §5.1.**  In the regime `65755586 ≤ n.size` all ten
parameters `b, p, α, k_T, T, k_r, r, d', L, u₀` have binary length at most `n.size + 4`. -/
theorem parSizesBig (n : ℕ) (hsz : 65755586 ≤ n.size) :
    (HvdH.bpar n).size ≤ n.size + 4 ∧
    (HvdH.ppar n).size ≤ n.size + 4 ∧
    (HvdH.apar n).size ≤ n.size + 4 ∧
    (HvdH.kTpar n).size ≤ n.size + 4 ∧
    (HvdH.Tpar n).size ≤ n.size + 4 ∧
    (Work.Params.krpar n).size ≤ n.size + 4 ∧
    (HvdH.rpar n).size ≤ n.size + 4 ∧
    (Work.Params.dpar n).size ≤ n.size + 4 ∧
    (Work.Params.Lpar n).size ≤ n.size + 4 ∧
    (Work.Params.upar n).size ≤ n.size + 4 := by
  have hn : n < 2 ^ n.size := (Nat.size_le).mp le_rfl
  have hNs : n.size < 2 ^ n.size := Nat.lt_two_pow_self (n := n.size)
  have hn2 : 2 ≤ n := by
    have h : (2 : ℕ) ^ 1 ≤ n := Nat.lt_size.mp (by omega : 1 < n.size)
    simpa using h
  have hn1 : 1 < n := by omega
  have hns_le_n : n.size ≤ n := (Nat.size_le).mpr (Nat.lt_two_pow_self (n := n))
  have hD : HvdH.D = 1729 := rfl
  have hb : HvdH.bpar n ≤ n.size := by
    rw [HvdH.bpar, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    exact le_of_lt hn
  have hbpos : 0 < HvdH.bpar n := by
    rw [HvdH.bpar]
    exact Nat.clog_pos (by norm_num : 1 < 2) hn1
  -- `k_T ≤ n.size + 3`
  have hkT : HvdH.kTpar n ≤ n.size + 3 := by
    rw [HvdH.kTpar, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    have h4 : (4 * n + HvdH.bpar n - 1) / HvdH.bpar n ≤ 4 * n + n.size := by
      calc (4 * n + HvdH.bpar n - 1) / HvdH.bpar n ≤ 4 * n + HvdH.bpar n - 1 :=
            Nat.div_le_self _ _
        _ ≤ 4 * n + HvdH.bpar n := Nat.sub_le _ _
        _ ≤ 4 * n + n.size := by omega
    have h5 : 4 * n + n.size < 8 * 2 ^ n.size := by
      have h6 : 4 * n + n.size < 4 * 2 ^ n.size + 2 ^ n.size := by omega
      have h7 : 4 * 2 ^ n.size + 2 ^ n.size = 5 * 2 ^ n.size := by ring
      have h8 : 5 * 2 ^ n.size ≤ 8 * 2 ^ n.size := Nat.mul_le_mul_right _ (by norm_num)
      omega
    have h9 : 8 * 2 ^ n.size = 2 ^ (n.size + 3) := eight_mul_two_pow_eq _
    omega
  -- `1 ≤ k_T` and `k_r ≤ k_T`
  have hm2 : 2 ≤ (4 * n + HvdH.bpar n - 1) / HvdH.bpar n := by
    rw [Nat.le_div_iff_mul_le hbpos]
    omega
  have hkT1 : 1 ≤ HvdH.kTpar n := by
    rw [HvdH.kTpar]
    exact Nat.clog_pos (by norm_num : 1 < 2) (by omega)
  have hkr : Work.Params.krpar n ≤ HvdH.kTpar n := by
    unfold Work.Params.krpar
    rw [Nat.div_le_iff_le_mul (by norm_num [HvdH.D] : 0 < HvdH.D)]
    rw [hD]
    omega
  have hkrle : Work.Params.krpar n ≤ n.size + 3 := le_trans hkr hkT
  -- `L ≤ r + 1` and `r ≤ 2 ^ (n.size+3)`
  have hr : HvdH.rpar n ≤ 2 ^ (n.size + 3) := by
    rw [HvdH.rpar]
    exact Nat.pow_le_pow_right (by norm_num) hkrle
  have hLr : Work.Params.Lpar n ≤ HvdH.rpar n + 1 := by
    unfold Work.Params.Lpar
    have hdiv : HvdH.rpar n * (2 * HvdH.D - 1) / (4 * HvdH.D) ≤ HvdH.rpar n := by
      rw [Nat.div_le_iff_le_mul_add_pred (by norm_num [HvdH.D] : 0 < 4 * HvdH.D)]
      rw [hD]
      omega
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `b`
    rw [Nat.size_le]
    have h3 : (2 : ℕ) ^ n.size ≤ 2 ^ (n.size + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · -- `p = 6b`
    rw [Nat.size_le, HvdH.ppar]
    have h6 : 6 * HvdH.bpar n ≤ 6 * n.size := Nat.mul_le_mul_left 6 hb
    have h7 : 6 * n.size < 8 * 2 ^ n.size := by
      have h8 : 6 * n.size < 6 * 2 ^ n.size := Nat.mul_lt_mul_of_pos_left hNs (by norm_num)
      have h9 : 6 * 2 ^ n.size ≤ 8 * 2 ^ n.size := Nat.mul_le_mul_right _ (by norm_num)
      omega
    have h10 : 8 * 2 ^ n.size = 2 ^ (n.size + 3) := eight_mul_two_pow_eq _
    have h11 : (2 : ℕ) ^ (n.size + 3) < 2 ^ (n.size + 4) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · -- `α`
    exact Nat.size_le.mpr (apar_lt_pow n hsz)
  · -- `k_T`
    rw [Nat.size_le]
    have h11 : n.size + 3 < 2 ^ (n.size + 3) := Nat.lt_two_pow_self (n := _)
    have h12 : (2 : ℕ) ^ (n.size + 3) ≤ 2 ^ (n.size + 4) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · -- `T = 2 ^ k_T`
    rw [HvdH.Tpar, Nat.size_pow]
    omega
  · -- `k_r`
    rw [Nat.size_le]
    have h11 : n.size + 3 < 2 ^ (n.size + 3) := Nat.lt_two_pow_self (n := _)
    have h12 : (2 : ℕ) ^ (n.size + 3) ≤ 2 ^ (n.size + 4) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · -- `r = 2 ^ k_r`
    rw [HvdH.rpar, Nat.size_pow]
    have h := hkrle
    unfold Work.Params.krpar at h
    omega
  · -- `d' = d k_r - k_T`
    rw [Nat.size_le]
    have hdpar : Work.Params.dpar n ≤ HvdH.D := by
      unfold Work.Params.dpar Work.Params.krpar
      rw [hD]
      have hdiv := Nat.div_add_mod (HvdH.kTpar n + 1729 - 1) 1729
      omega
    have h14 : Work.Params.dpar n ≤ 1729 := hD ▸ hdpar
    have h15 : (1729 : ℕ) < 2 ^ (n.size + 4) := by
      have h16 : (2 : ℕ) ^ 11 ≤ 2 ^ (n.size + 4) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h17 : (1729 : ℕ) < 2 ^ 11 := by norm_num
      omega
    omega
  · -- `L`
    rw [Nat.size_le]
    have hL : Work.Params.Lpar n ≤ 2 ^ (n.size + 3) + 1 := by omega
    have h18 : (2 : ℕ) ^ (n.size + 3) + 1 < 2 ^ (n.size + 4) :=
      two_pow_add_one_lt_of (e := n.size + 3) (k := n.size + 4) (by omega) (by omega)
    omega
  · -- `u₀`
    rw [Nat.size_le]
    have hup : Work.Params.upar n < Work.Params.Lpar n + Work.Params.Ffac * Work.Params.Qall :=
      (uparfacts n).2.1
    have hFQ : Work.Params.Ffac * Work.Params.Qall ≤ 2 ^ (n.size + 2) := QallPowNr n hsz
    have h2k : (2 : ℕ) ^ (n.size + 3) = 2 * 2 ^ (n.size + 2) := by
      rw [show n.size + 3 = (n.size + 2) + 1 by omega, pow_succ']
    have hLb : Work.Params.Lpar n ≤ 2 * 2 ^ (n.size + 2) + 1 := by
      have hL : Work.Params.Lpar n ≤ 2 ^ (n.size + 3) + 1 := by omega
      omega
    have h4k : (2 : ℕ) ^ (n.size + 4) = 4 * 2 ^ (n.size + 2) := by
      rw [show n.size + 4 = (n.size + 2) + 2 by omega, ← four_mul_two_pow_eq]
    rw [h4k]
    have hpos : 1 ≤ (2 : ℕ) ^ (n.size + 2) := Nat.one_le_two_pow
    omega

end Work.Params
