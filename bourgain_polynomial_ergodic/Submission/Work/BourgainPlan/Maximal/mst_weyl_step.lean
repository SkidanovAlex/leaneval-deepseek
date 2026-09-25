import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_scalar_defs
import Submission.Work.BourgainPlan.Maximal.polyWeylKernel_minorArcDecay
import Submission.Work.BourgainPlan.Maximal.mst_bracket_rpow
import Submission.Work.BourgainPlan.Maximal.mst_absorb_logloss

namespace Work.BourgainPlan.Maximal

open Finset

set_option autoImplicit false

/-!
# The polylog Weyl step of the minor-arc bound (MST §4.1, the regime `q ≥ n^γ`)

This file contains the reduction of the *classical Weyl inequality with polylogarithmic loss*
(`MSTWeylBound`, `Maximal/mst_scalar_defs.lean`) to the form consumed by the minor-arc analysis:
for every `α > 0`, if the Dirichlet approximation `a/q` of the scaled frequency `c·θ`
(`c = P.leadingCoeff`) has a denominator `q ≥ n^γ` with `γ = (α + c_W + 1)·2^{d-1}` large, and `q` is
still below the trivial bound `2 n^{-γ} 2^{nd}`, then the Weyl kernel `m_{2^n}(θ)` decays
polylogarithmically, `‖m_{2^n}(θ)‖ ≤ C (n+1)^{-α}`.

The two purely arithmetical ingredients are `mst_bracket_rpow` (the Weyl bracket
`1/q + 1/N + 1/N^{d-1} + q/N^d ≤ 5 n^{-γ}` at `N = 2^n`, raised to the Weyl exponent `σ = 2^{1-d}`)
and `mst_absorb_logloss` (the polylogarithmic loss `(1+log N)^{c_W}` absorbed by `n^{-γσ}` once
`γσ ≥ α + c_W + 1`).
-/

/-- The sum in the definition of the Weyl kernel `polyWeylKernel` is the Weyl sum in the shape used
by `MSTWeylBound` (there the polynomial is evaluated at `M + x` with `M = 0`, and the phase is
written `↑(2π f(x)) * I` instead of `2π I * ↑(f x)`). -/
lemma mst_weyl_sum_eq (θ : ℝ) (P : Polynomial ℤ) (N : ℕ) :
    (∑ x ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I *
      (((Polynomial.eval (x : ℝ) (Polynomial.C θ * toRealPoly P)) : ℝ) : ℂ)))
      = ∑ x ∈ Finset.range N, Complex.exp
          ((↑(2 * Real.pi * (Polynomial.C θ * toRealPoly P).eval ((0 : ℤ) + (x : ℝ))) : ℂ)
            * Complex.I) := by
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  push_cast
  ring_nf

/-- **Weyl's inequality in the normalized form used by the minor-arc analysis.**

For an integer polynomial `P` of degree `d ≥ 2` and every `a/q` with `gcd a q = 1` within `1/q²` of
the leading coefficient times `θ`, the Weyl kernel at the scale `N` is bounded by
`C_W (1 + log N)^{c_W}` times the `σ = 2^{1-d}`-th power of the classical bracket
`1/q + 1/N + 1/N^{d-1} + q/N^d` — i.e. `MSTWeylBound` applied to the real polynomial
`C θ * toRealPoly P` (of degree `d`, leading coefficient `θ · c`). -/
lemma mst_weyl_kernel_bound (hW : MSTWeylBound) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ (CW cW : ℝ), 0 < CW ∧ 0 < cW ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℤ) (q : ℕ), 1 ≤ q →
      Int.gcd a (q:ℤ) = 1 → ∀ θ : ℝ, θ ≠ 0 →
      |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2 →
      ‖polyWeylKernel P N θ‖ ≤ CW * (1 + Real.log (N:ℝ))^cW *
        (1/(q:ℝ) + 1/(N:ℝ) + 1/(N:ℝ)^(P.natDegree-1) + (q:ℝ)/(N:ℝ)^(P.natDegree))^((2:ℝ)^(1-(P.natDegree:ℝ))) := by
  obtain ⟨CW, cW, hCW, hcW, hWmain⟩ := hW P.natDegree hd
  refine ⟨CW, cW, hCW, hcW, ?_⟩
  intro N hN a q hq hg θ hθ hθapp
  have hqZ : (1:ℤ) ≤ (q:ℤ) := by exact_mod_cast hq
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  set f : Polynomial ℝ := Polynomial.C θ * toRealPoly P with hf
  have hfdeg : f.natDegree = P.natDegree := by
    rw [hf, Polynomial.natDegree_C_mul hθ, natDegree_toRealPoly]
  have hlead : f.leadingCoeff = θ * (P.leadingCoeff : ℝ) := by
    rw [hf]; exact leadingCoeff_C_toRealPoly P θ hθ
  have happ : |f.leadingCoeff - (a:ℝ)/(q:ℝ)| ≤ 1/(q:ℝ)^2 := by
    rw [hlead, mul_comm]; exact hθapp
  have hWe := hWmain 0 N a (q:ℤ) f hN hqZ hg hfdeg happ
  have hnorm : ‖polyWeylKernel P N θ‖
      = (N:ℝ)⁻¹ * ‖∑ x ∈ Finset.range N, Complex.exp ((↑(2 * Real.pi *
            f.eval ((0 : ℤ) + (x : ℝ))) : ℂ) * Complex.I)‖ := by
    rw [polyWeylKernel_eq_eval_toRealPoly P N θ, mst_weyl_sum_eq θ P N, hf]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc ‖polyWeylKernel P N θ‖
      = (N:ℝ)⁻¹ * ‖∑ x ∈ Finset.range N, Complex.exp ((↑(2 * Real.pi *
            f.eval ((0 : ℤ) + (x : ℝ))) : ℂ) * Complex.I)‖ := hnorm
    _ ≤ (N:ℝ)⁻¹ * (CW * (1 + Real.log (N:ℝ))^cW * (N:ℝ) *
          (1/(q:ℝ) + 1/(N:ℝ) + 1/(N:ℝ)^(P.natDegree-1) + (q:ℝ)/(N:ℝ)^(P.natDegree))^((2:ℝ)^(1-(P.natDegree:ℝ)))) :=
        mul_le_mul_of_nonneg_left hWe (by positivity)
    _ = CW * (1 + Real.log (N:ℝ))^cW *
          (1/(q:ℝ) + 1/(N:ℝ) + 1/(N:ℝ)^(P.natDegree-1) + (q:ℝ)/(N:ℝ)^(P.natDegree))^((2:ℝ)^(1-(P.natDegree:ℝ))) := by
        rw [show (N:ℝ)⁻¹ * (CW * (1 + Real.log (N:ℝ))^cW * (N:ℝ) *
              (1/(q:ℝ) + 1/(N:ℝ) + 1/(N:ℝ)^(P.natDegree-1) + (q:ℝ)/(N:ℝ)^(P.natDegree))^((2:ℝ)^(1-(P.natDegree:ℝ))))
            = CW * (1 + Real.log (N:ℝ))^cW *
              (1/(q:ℝ) + 1/(N:ℝ) + 1/(N:ℝ)^(P.natDegree-1) + (q:ℝ)/(N:ℝ)^(P.natDegree))^((2:ℝ)^(1-(P.natDegree:ℝ))) from by
          field_simp]

/-- **The polylog Weyl regime of the minor-arc bound** (MST §4.1, the case `q ≥ n^γ`). `Work.BourgainPlan.Maximal.MSTWeylBound` (`Maximal/mst_scalar_defs.lean`, in its current form) supplies the classical Weyl inequality with polylogarithmic loss: for each degree `k ≥ 2` there are `C_W, c_W > 0` with `‖Σ_{x<N} e(f(M+x))‖ ≤ C_W (1 + log N)^{c_W} N (1/q + 1/N + 1/N^{k-1} + q/N^k)^{2^{1-k}}` whenever `gcd a q = 1`, `f.natDegree = k` and `|f.leadingCoeff − a/q| ≤ 1/q²`. Hence for every `α > 0` there is a *large* `γ > 0` (of size `(α + c_W + 1)·2^{d-1}`), such that whenever the Dirichlet approximation `|cθ − a/q| ≤ 1/q²` of the scaled frequency `c θ = P.leadingCoeff · θ` has denominator above the threshold `n^γ` and `q ≤ 2 n^{-γ} 2^{n d}`, the Weyl kernel decays: `‖m_{2^n}(θ)‖ ≤ C (n+1)^{-α}`.

Proof: unfold `polyWeylKernel` with `polyWeylKernel_eq_eval_toRealPoly` (`Maximal/polyWeylKernel_minorArcDecay.lean`), apply `hW` at `k := P.natDegree` with `M := 0`, `f := Polynomial.C θ * toRealPoly P` (whose `natDegree` is `P.natDegree` because `θ ≠ 0` and `P ≠ 0`, and whose leading coefficient is `θ · c`); the bracket is `≤ 5 n^{-γ}` since `1/q ≤ n^{-γ}`, `1/N ≤ n^{-γ}`, `1/N^{d-1} ≤ 1/N` and `q/N^d ≤ 2n^{-γ}`; with `σ := 2^{1-d}` this gives `‖m‖ ≤ C_W 5^σ (1+log 2)^{c_W} (1+log2)^{c_W} n^{c_W - γσ}`, and `γ σ ≥ α + c_W + 1` absorbs the polylog loss. -/
theorem mst_weyl_step (hW : Work.BourgainPlan.Maximal.MSTWeylBound) (P : Polynomial ℤ)
    (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff) {α : ℝ} (hα : 0 < α) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₁ : ℕ,
      ∀ n : ℕ, N₁ ≤ n → ∀ (a : ℤ) (q : ℕ),
      1 ≤ q → (n : ℝ) ^ γ ≤ (q : ℝ) →
      (q : ℝ) ≤ 2 * (n : ℝ) ^ (-γ) * (2 : ℝ) ^ ((n : ℝ) * (P.natDegree : ℝ)) →
      (2 : ℝ) ^ (-(n : ℝ)) ≤ (n : ℝ) ^ (-γ) →
      Int.gcd a (q : ℤ) = 1 → ∀ θ : ℝ, θ ≠ 0 →
      |(P.leadingCoeff : ℝ) * θ - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      ‖Work.BourgainPlan.Maximal.polyWeylKernel P (2 ^ n) θ‖ ≤ C * ((n : ℝ) + 1) ^ (-α) := by
  obtain ⟨CW, cW, hCW, hcW, hWb⟩ := mst_weyl_kernel_bound hW P hd
  -- the Weyl exponent `σ = 2^{1-d}` and the threshold `γ = (α + c_W + 1)·2^{d-1}`
  set σ : ℝ := (2:ℝ) ^ (1 - (P.natDegree:ℝ)) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  set γ : ℝ := (α + cW + 1) * (2:ℝ) ^ ((P.natDegree:ℝ) - 1) with hγdef
  have hγpos : 0 < γ := by
    rw [hγdef]
    have h2 : 0 < (2:ℝ) ^ ((P.natDegree:ℝ) - 1) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  have hγσ : α + cW + 1 ≤ γ * σ := by
    rw [hγdef, hσdef, mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      show ((P.natDegree:ℝ) - 1) + (1 - (P.natDegree:ℝ)) = 0 by ring, Real.rpow_zero, mul_one]
  set C : ℝ := CW * 5^σ * ((1 + Real.log 2) * 2)^cW * 2^α with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h5 : 0 < (5:ℝ)^σ := Real.rpow_pos_of_pos (by norm_num) _
    have hlog2 : 0 < (1 + Real.log 2) * 2 := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
    have hl : 0 < ((1 + Real.log 2) * 2)^cW := Real.rpow_pos_of_pos hlog2 _
    have h2a : 0 < (2:ℝ)^α := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  refine ⟨γ, hγpos, C, hCpos, 1, ?_⟩
  intro n hn a q hq1 hqγ hqN hNγ hgcd θ hθ hθapp
  have hn1 : 1 ≤ n := hn
  have hN2 : (((2:ℕ)^n : ℕ) : ℝ) = (2:ℝ)^n := by push_cast; norm_num
  have hstep : ‖polyWeylKernel P (2^n) θ‖ ≤
      CW * (1 + Real.log (((2:ℕ)^n : ℕ) : ℝ))^cW *
        (1/(q:ℝ) + 1/(((2:ℕ)^n : ℕ) : ℝ) + 1/((((2:ℕ)^n : ℕ) : ℝ))^(P.natDegree-1)
          + (q:ℝ)/((((2:ℕ)^n : ℕ) : ℝ))^(P.natDegree))^σ := by
    exact hWb (2^n) Nat.one_le_two_pow a q hq1 hgcd θ hθ hθapp
  rw [hN2] at hstep
  have hlognn : 0 ≤ Real.log ((2:ℝ)^n) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_two_pow)
  have hnonneg : 0 ≤ CW * (1 + Real.log ((2:ℝ)^n))^cW :=
    mul_nonneg hCW.le (Real.rpow_nonneg (by linarith) _)
  have hnonneg2 : 0 ≤ CW * 5^σ :=
    mul_nonneg hCW.le (Real.rpow_nonneg (by norm_num) _)
  have hbr := mst_bracket_rpow P.natDegree hd γ σ hσpos n q hn1 hq1 hqγ hqN hNγ
  have habs := mst_absorb_logloss α cW γ σ hα hcW hγσ n hn1
  calc ‖polyWeylKernel P (2^n) θ‖
      ≤ CW * (1 + Real.log ((2:ℝ)^n))^cW *
          (1/(q:ℝ) + 1/(2:ℝ)^n + 1/((2:ℝ)^n)^(P.natDegree-1) + (q:ℝ)/((2:ℝ)^n)^(P.natDegree))^σ := hstep
    _ ≤ CW * (1 + Real.log ((2:ℝ)^n))^cW * (5^σ * (n:ℝ)^(-(γ*σ))) :=
        mul_le_mul_of_nonneg_left hbr hnonneg
    _ = CW * 5^σ * ((1 + Real.log ((2:ℝ)^n))^cW * (n:ℝ)^(-(γ*σ))) := by ring
    _ ≤ CW * 5^σ * (((1 + Real.log 2) * 2)^cW * 2^α * ((n:ℝ)+1)^(-α)) :=
        mul_le_mul_of_nonneg_left habs hnonneg2
    _ = C * ((n:ℝ)+1)^(-α) := by rw [hCdef]; ring

end Work.BourgainPlan.Maximal
