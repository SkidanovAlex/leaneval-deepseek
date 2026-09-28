import Mathlib
import Submission.Work.HP.Sig2.VeroMon

/-!
# `ν_{d,n}` is injective on rays

If `ν_{d,n}(x) = λ · ν_{d,n}(y)` for some `λ ≠ 0` and `y ≠ 0`, then `x = μ · y` for some `μ`.

The proof uses the two monomial probes of `Submission.Work.HP.Sig2.VeroMon`:

* `diagMon d n j` gives `x j ^ d = λ · y j ^ d`, which in particular shows `x j ≠ 0`
  whenever `y j ≠ 0`;
* `pairMon d n j i` gives `x j ^ (d-1) · x i = λ · (y j ^ (d-1) · y i)`.

Multiplying the second by `y j`, using the first and cancelling `x j ^ (d-1)` yields
`x i · y j = x j · y i` for every `i`, i.e. `x i = (x j / y j) · y i`.
-/

set_option autoImplicit false

namespace Work.HP.Sig2

open Work.HP

theorem veronese_proportional {K : Type*} [Field K] (d n : ℕ) (hd : 1 ≤ d)
    (x y : Fin (n + 1) → K) (hy : y ≠ 0) {lam : K} (hlam : lam ≠ 0)
    (h : ∀ m : Mon d n, veronese d n x m = lam * veronese d n y m) :
    ∃ mu : K, x = mu • y := by
  -- a coordinate `j` with `y j ≠ 0`
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), y j ≠ 0 := by
    simpa using Function.ne_iff.mp hy
  refine ⟨x j / y j, ?_⟩
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  -- the diagonal probe: `x j ^ d = lam * y j ^ d`
  have hdiag : x j ^ d = lam * y j ^ d := by
    have hh := h (diagMon d n j)
    rwa [veronese_diag, veronese_diag] at hh
  -- in particular `x j ≠ 0`
  have hxj : x j ≠ 0 := by
    intro h0
    have hz : x j ^ d = 0 := by rw [h0]; exact zero_pow (by omega)
    rw [hdiag] at hz
    exact (mul_ne_zero hlam (pow_ne_zero d hj)) hz
  by_cases hij : i = j
  · rw [hij, div_mul_cancel₀ (x j) hj]
  · have hji : j ≠ i := fun hh => hij hh.symm
    -- the mixed probe
    have hpair : x j ^ (d - 1) * x i = lam * (y j ^ (d - 1) * y i) := by
      have hh := h (pairMon d n j i hji hd)
      rwa [veronese_pair d n j i hji hd x, veronese_pair d n j i hji hd y] at hh
    have hxy : x i * y j = x j * y i := by
      have hy_pow : y j ^ (d - 1) * y j = y j ^ d := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      have hx_pow : x j ^ (d - 1) * x j = x j ^ d := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      have key : x j ^ (d - 1) * (x i * y j) = x j ^ (d - 1) * (x j * y i) := by
        calc
          x j ^ (d - 1) * (x i * y j)
              = (x j ^ (d - 1) * x i) * y j := by ring
          _ = (lam * (y j ^ (d - 1) * y i)) * y j := by rw [hpair]
          _ = lam * (y j ^ (d - 1) * y j) * y i := by ring
          _ = lam * (y j ^ d) * y i := by rw [hy_pow]
          _ = (lam * y j ^ d) * y i := by ring
          _ = x j ^ d * y i := by rw [hdiag]
          _ = (x j ^ (d - 1) * x j) * y i := by rw [hx_pow]
          _ = x j ^ (d - 1) * (x j * y i) := by ring
      exact mul_left_cancel₀ (pow_ne_zero (d - 1) hxj) key
    field_simp
    exact hxy

end Work.HP.Sig2
