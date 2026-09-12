import Mathlib
import Submission.ArcFamily
import Submission.S5_defs
import Submission.Consts
import Submission.F_cor42_full
import Submission.TrigObservation

/-! Section 5, Lemmas 5.4 & 5.5 of the paper (choosing the sign colouring `ε`):

Assume the quadrant family `F` and a colouring `α` with `|ê_r(α)| ≤ 1` for all
`r < n`.  We construct `ε : Fin n → {±1}` such that

    |s_o(θ) − ŝ(θ)| ≤ 75·√n    for every θ ∈ [0, π/2],

where `s_o(θ) = Σ_r ε_r sin((2r+1)θ)` and `ŝ(θ) = Σ_r ê_r sin((2r+1)θ)`.

SETUP (paper §5): let `M := 64n` and sample points `θ_k := (2k−1)π/(4M)`,
`k = 1..M`; every `θ ∈ [0,π/2]` is within `δ0 := π/(4M) = 2^(-8)·π/n` of some
`θ_k`.  For each `k` and each `ℓ = 0..L−1` with `L := 2n+1`, define the
constraint vector `v_{(k,ℓ)}` by `(v_{(k,ℓ)})_j := (d^ℓ/dθ^ℓ) sin((2j+1)θ)|_{θ=θ_k}`
(`j < n`).  Then, with `f := s_o − ŝ`,

    f^(ℓ)(θ_k) = ⟨ε − ê, v_{(k,ℓ)}⟩.

Apply Corollary 4.2 (`Discrepancy.cor42_full`) with dimension `n`, `x0 := ê`
(in `[-1,1]^n` by the hypothesis), constants `c_{(k,ℓ)} := 14·√((11+ℓ)·ln 2)`.
The hypothesis holds because

    Σ_k Σ_ℓ exp(−c²/196) = M · Σ_ℓ 2^(-(11+ℓ)) ≤ M·2^(-10) = n/16 .

Hence for each (k,ℓ) with ℓ ≤ L−1:

    |f^(ℓ)(θ_k)| ≤ (69 + 2ℓ)·√n·(2n)^ℓ .

TAYLOR STEP: for θ within δ0 of θ_k, Taylor's theorem with Lagrange remainder
(order L−1; remainder controlled by `|f^(L)| ≤ 2n·(2n)^L` times `δ0^L/L!`, which
is `≤ √n`) gives

    |f(θ)| ≤ Σ_{ℓ<L} |f^(ℓ)(θ_k)|·δ0^ℓ/ℓ! + √n
          ≤ √n·( Σ_{ℓ=0}^{∞} (69+2ℓ)·(2n·δ0)^ℓ/ℓ! ) + √n
          ≤ √n·( (69 + 2a)·e^a ) + √n ,    a := 2n·δ0 = π/128 .

Numerics (import `Submission.Consts`): `π ≤ 22/7`, and for `0 ≤ a < 1`,
`e^a ≤ 1/(1−a)`.  With `a ≤ (22/7)/128` you get `(69 + 2a)·e^a + 1 ≤ 75`.
All bounds are uniform in `θ`, so the conclusion follows by covering
`[0,π/2]` with the discs around the `θ_k`.  You will need the derivative
identity `d^ℓ/dθ^ℓ sin((2j+1)θ) = (2j+1)^ℓ·sin((2j+1)θ + ℓπ/2)` (or a
`|·| ≤ (2j+1)^ℓ` bound only), `iteratedDeriv` API, and the finite-index
encoding of pairs `(k,ℓ)` as `Fin (M·L)`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

namespace Submission
namespace S5

/-- Number of sample points `M := 64n`. -/
def M (n : ℕ) : ℕ := 64 * n
/-- Number of derivative orders: `L := 2n+1`. -/
def L (n : ℕ) : ℕ := 2 * n + 1
/-- Sampling radius `δ0 = π/(4M)`. -/
def delta0 (n : ℕ) : ℝ := Real.pi / (4 * (M n : ℝ))
/-- Sample point `θ_k = (2k+1)·π/(4M)`. -/
def theta (n : ℕ) (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * Real.pi / (4 * (M n : ℝ))
/-- Constraint vector for `(k, ℓ)`: `i ↦ (d^ℓ/dθ^ℓ) sin((2i+1)θ)` at `θ_k`. -/
def dvec (n : ℕ) (ℓ k : ℕ) : Fin n → ℝ :=
  fun i => iteratedDeriv ℓ (fun θ : ℝ => oddSin i.1 θ) (theta n k)

/-- |iteratedDeriv ℓ sin x| ≤ 1. -/
lemma abs_iteratedDeriv_sin_le (ℓ : ℕ) (x : ℝ) : |iteratedDeriv ℓ Real.sin x| ≤ 1 := by
  rcases Nat.even_or_odd ℓ with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm, ← two_mul]
    rw [Real.iteratedDeriv_even_sin]
    simp
    exact Real.abs_sin_le_one x
  · rw [hm]
    rw [Real.iteratedDeriv_odd_sin]
    simp
    exact Real.abs_cos_le_one x

/-- `|iteratedDeriv ℓ (sin ∘ (c·)) x| ≤ c^ℓ` for `0 ≤ c`. -/
lemma abs_iteratedDeriv_sin_mul_le (ℓ : ℕ) {c : ℝ} (hc0 : 0 ≤ c) (x : ℝ) :
    |iteratedDeriv ℓ (fun θ : ℝ => Real.sin (c * θ)) x| ≤ c ^ ℓ := by
  have hc : ContDiff ℝ (↑ℓ : WithTop ℕ∞) Real.sin := Real.contDiff_sin
  have h := iteratedDeriv_comp_const_mul (f := Real.sin) (c := c) hc
  calc
    |iteratedDeriv ℓ (fun θ : ℝ => Real.sin (c * θ)) x|
        = |c ^ ℓ * iteratedDeriv ℓ Real.sin (c * x)| := by rw [h]
    _ = |c| ^ ℓ * |iteratedDeriv ℓ Real.sin (c * x)| := by rw [abs_mul, abs_pow]
    _ ≤ |c| ^ ℓ * 1 := mul_le_mul_of_nonneg_left (abs_iteratedDeriv_sin_le ℓ (c * x)) (pow_nonneg (abs_nonneg c) ℓ)
    _ = c ^ ℓ := by
      rw [mul_one]
      rw [abs_of_nonneg hc0]

lemma freq_nonneg (r : ℕ) : 0 ≤ freq r := by
  dsimp [freq]
  positivity

lemma freq_le_two_n {n : ℕ} (i : Fin n) : freq i.1 ≤ 2 * (n : ℝ) := by
  dsimp [freq]
  have hi : (i.1 : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt i.2
  have hc : ((i.1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hi
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le i.1) i.2)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]
    norm_num
  calc
    2 * (i.1 : ℝ) + 1 ≤ 2 * ((n - 1 : ℕ) : ℝ) + 1 := by nlinarith [hc]
    _ = 2 * (n : ℝ) - 1 := by rw [hcast]; ring
    _ ≤ 2 * (n : ℝ) := by linarith

/-- `supAbs` of the constraint vector is bounded by `(2n)^ℓ`. -/
lemma supAbs_dvec_le (n ℓ k : ℕ) (hn : 0 < n) :
    Discrepancy.supAbs (dvec n ℓ k) ≤ (2 * (n : ℝ)) ^ ℓ := by
  refine Discrepancy.supAbs_le_of_forall (dvec n ℓ k) ?hM ?hM0
  · intro i
    dsimp [dvec]
    calc
      |iteratedDeriv ℓ (fun θ : ℝ => oddSin i.1 θ) (theta n k)|
          ≤ (freq i.1) ^ ℓ := by
              simpa [oddSin] using abs_iteratedDeriv_sin_mul_le ℓ (hc0 := freq_nonneg i.1) (x := theta n k)
      _ ≤ (2 * (n : ℝ)) ^ ℓ := by
              exact pow_le_pow_left₀ (freq_nonneg i.1) (freq_le_two_n i) ℓ
  · exact pow_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)) ℓ

/-- A coloured sine sum difference function: `f(θ) = Σ_i (u_i − v_i)·sin((2i+1)θ)`. -/
def diffFun (n : ℕ) (u v : Fin n → ℝ) : ℝ → ℝ :=
  fun θ => ∑ i : Fin n, (u i - v i) * oddSin i.1 θ

/-- A single odd sine is `C^∞`. -/
@[fun_prop]
lemma contDiff_oddSin_r (m : ℕ) (r : ℕ) : ContDiff ℝ (m : WithTop ℕ∞) (fun θ : ℝ => oddSin r θ) := by
  dsimp [oddSin]
  fun_prop

/-- The diff function is `C^∞`. -/
lemma contDiff_diffFun {n m : ℕ} (u v : Fin n → ℝ) : ContDiff ℝ (m : WithTop ℕ∞) (diffFun n u v) := by
  unfold diffFun
  apply ContDiff.sum
  intro i hi
  fun_prop

/-- Iterated derivative of `diffFun` (linearity through the sum). -/
lemma iteratedDeriv_diffFun (n ℓ : ℕ) (u v : Fin n → ℝ) (θ0 : ℝ) :
    iteratedDeriv ℓ (diffFun n u v) θ0 =
      ∑ i : Fin n, (u i - v i) * iteratedDeriv ℓ (fun θ : ℝ => oddSin i.1 θ) θ0 := by
  unfold diffFun
  rw [iteratedDeriv_fun_sum (f := fun i : Fin n => fun θ : ℝ => (u i - v i) * oddSin i.1 θ) (I := Finset.univ)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedDeriv_const_mul_field (c := u i - v i) (f := fun θ : ℝ => oddSin i.1 θ)]
  · intro i hi
    fun_prop

/-- Reindex `sHat` over `Fin n`. -/
lemma sHat_eq_sum_fin (n N : ℕ) (K : ℝ) (F : Family.Quad n N) (α : Fin N → ℝ) (θ : ℝ) :
    sHat n N K F α θ = ∑ i : Fin n, ehat n N K F α i.1 * oddSin i.1 θ := by
  rw [sHat]
  symm
  exact Fin.sum_univ_eq_sum_range (fun r : ℕ => ehat n N K F α r * oddSin r θ) n

/-- The diff function with `v = ê`-coefficients is `s_o − ŝ`. -/
lemma diffFun_eq_sOdd_sub_sHat (n N : ℕ) (K : ℝ) (F : Family.Quad n N)
    (ε : Fin n → ℝ) (α : Fin N → ℝ) (θ : ℝ) :
    diffFun n ε (fun i => ehat n N K F α i.1) θ = sOdd n ε θ - sHat n N K F α θ := by
  unfold diffFun sOdd
  rw [sHat_eq_sum_fin]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sub_mul]

/-- Taylor's theorem with Lagrange remainder, in terms of global iterated
derivatives.  Order `m`; remainder involves the `(m+1)`-st derivative. -/
lemma taylor_bound {f : ℝ → ℝ} {x x0 : ℝ} {m : ℕ} (B : ℝ) (hx : x0 ≠ x)
    (hf : ∀ k : ℕ, ContDiff ℝ (k : WithTop ℕ∞) f)
    (hB : ∀ y ∈ Set.uIcc x0 x, |iteratedDeriv (m + 1) f y| ≤ B) :
    |f x - ∑ ℓ ∈ Finset.range (m + 1),
        (iteratedDeriv ℓ f x0) * (x - x0) ^ ℓ / (ℓ.factorial : ℝ)|
      ≤ B * |x - x0| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv (n := m) hx ((hf (m + 1)).contDiffOn) with ⟨x', hx'i, hrem⟩
  have hx'cc : x' ∈ Set.uIcc x0 x := by
    rw [Set.uIcc, Set.mem_Icc]
    rw [Set.uIoo, Set.mem_Ioo] at hx'i
    exact ⟨le_of_lt hx'i.1, le_of_lt hx'i.2⟩
  have htay : taylorWithinEval f m (Set.uIcc x0 x) x0 x =
      ∑ ℓ ∈ Finset.range (m + 1), (iteratedDeriv ℓ f x0) * (x - x0) ^ ℓ / (ℓ.factorial : ℝ) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro ℓ hℓmem
    have hid : iteratedDerivWithin ℓ f (Set.uIcc x0 x) x0 = iteratedDeriv ℓ f x0 := by
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx) ((hf ℓ).contDiffAt) (by simp)
    rw [hid]
    simp [smul_eq_mul]
    ring
  calc
    |f x - ∑ ℓ ∈ Finset.range (m + 1),
        (iteratedDeriv ℓ f x0) * (x - x0) ^ ℓ / (ℓ.factorial : ℝ)|
        = |f x - taylorWithinEval f m (Set.uIcc x0 x) x0 x| := by rw [htay]
    _ = |iteratedDeriv (m + 1) f x' * (x - x0) ^ (m + 1) / ((m + 1).factorial : ℝ)| := by rw [hrem]
    _ ≤ B * |x - x0| ^ (m + 1) / ((m + 1).factorial : ℝ) := by
      have hBx' : |iteratedDeriv (m + 1) f x'| ≤ B := hB x' hx'cc
      have hfac : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
      have hfac0 : (0 : ℝ) ≤ ((m + 1).factorial : ℝ) := le_of_lt hfac
      have hP : 0 ≤ |x - x0| ^ (m + 1) := by positivity
      have hmm : |iteratedDeriv (m + 1) f x'| * |x - x0| ^ (m + 1) ≤ B * |x - x0| ^ (m + 1) :=
        mul_le_mul_of_nonneg_right hBx' hP
      rw [abs_div, abs_mul, abs_pow]
      rw [abs_of_nonneg hfac0]
      exact div_le_div_of_nonneg_right hmm hfac0

/-- Numerical bound used in the Taylor step: `(69 + 2a)·e^a + 1 ≤ 75` for
`a ≤ (22/7)/128`. -/
lemma taylor_numeric (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ (22 / 7 : ℝ) / 128) :
    (69 + 2 * a) * Real.exp a + 1 ≤ 75 := by
  have hlt : a < 1 := by
    have h1 : (22 / 7 : ℝ) / 128 < 1 := by norm_num
    linarith
  have hpos : 0 < 1 - a := by linarith
  have hmain : (69 + 2 * a) / (1 - a) ≤ 74 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  calc
    (69 + 2 * a) * Real.exp a + 1 ≤ (69 + 2 * a) * (1 / (1 - a)) + 1 := by
      have hc : 0 ≤ 69 + 2 * a := by positivity
      have hb : (69 + 2 * a) * Real.exp a ≤ (69 + 2 * a) * (1 / (1 - a)) :=
        mul_le_mul_of_nonneg_left (Submission.Consts.exp_le_inv_sub_one ha0 hlt) hc
      linarith
    _ = (69 + 2 * a) / (1 - a) + 1 := by ring
    _ ≤ 75 := by linarith

/-- Partial sums of the exponential series are bounded by `exp`. -/
lemma exp_partial_le (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (∑ ℓ ∈ Finset.range m, x ^ ℓ / (ℓ.factorial : ℝ)) ≤ Real.exp x := by
  simpa using Real.sum_le_exp_of_nonneg hx m

/-- `Σ_{ℓ<m+1} ℓ·x^ℓ/ℓ! = x·Σ_{ℓ<m} x^ℓ/ℓ!`. -/
lemma sum_weighted_eq (x : ℝ) (m : ℕ) :
    (∑ ℓ ∈ Finset.range (m + 1), (ℓ : ℝ) * x ^ ℓ / (ℓ.factorial : ℝ)) =
      x * (∑ ℓ ∈ Finset.range m, x ^ ℓ / (ℓ.factorial : ℝ)) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ]
      have hterm : ((m + 1 : ℕ) : ℝ) * x ^ (m + 1) / ((m + 1).factorial : ℝ) =
          x * (x ^ m / (m.factorial : ℝ)) := by
        have hf2 : ((m + 1 : ℕ).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          norm_num
        have hc1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hc2 : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
        calc
          ((m + 1 : ℕ) : ℝ) * x ^ (m + 1) / ((m + 1).factorial : ℝ)
              = x ^ (m + 1) / (m.factorial : ℝ) := by
                  rw [hf2]
                  field_simp [hc1, hc2]
          _ = x * (x ^ m / (m.factorial : ℝ)) := by
                  rw [pow_succ]
                  ring
      rw [hterm]
      ring

/-- `Σ_{ℓ<m+1}(69 + 2ℓ)x^ℓ/ℓ! ≤ (69 + 2x)e^x` for `0 ≤ x`. -/
lemma partial_weighted_le_exp (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    (∑ ℓ ∈ Finset.range (m + 1), (69 + 2 * (ℓ : ℝ)) * x ^ ℓ / (ℓ.factorial : ℝ))
      ≤ (69 + 2 * x) * Real.exp x := by
  have hsplit :
      (∑ ℓ ∈ Finset.range (m + 1), (69 + 2 * (ℓ : ℝ)) * x ^ ℓ / (ℓ.factorial : ℝ))
        = 69 * (∑ ℓ ∈ Finset.range (m + 1), x ^ ℓ / (ℓ.factorial : ℝ))
          + 2 * (∑ ℓ ∈ Finset.range (m + 1), (ℓ : ℝ) * x ^ ℓ / (ℓ.factorial : ℝ)) := by
    calc
      (∑ ℓ ∈ Finset.range (m + 1), (69 + 2 * (ℓ : ℝ)) * x ^ ℓ / (ℓ.factorial : ℝ))
          = ∑ ℓ ∈ Finset.range (m + 1), (69 * (x ^ ℓ / (ℓ.factorial : ℝ)) +
              2 * ((ℓ : ℝ) * x ^ ℓ / (ℓ.factorial : ℝ))) := by
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            ring
      _ = (∑ ℓ ∈ Finset.range (m + 1), 69 * (x ^ ℓ / (ℓ.factorial : ℝ))) +
          (∑ ℓ ∈ Finset.range (m + 1), 2 * ((ℓ : ℝ) * x ^ ℓ / (ℓ.factorial : ℝ))) := by
            rw [Finset.sum_add_distrib]
      _ = 69 * (∑ ℓ ∈ Finset.range (m + 1), x ^ ℓ / (ℓ.factorial : ℝ))
          + 2 * (∑ ℓ ∈ Finset.range (m + 1), (ℓ : ℝ) * x ^ ℓ / (ℓ.factorial : ℝ)) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h2 : (∑ ℓ ∈ Finset.range (m + 1), (ℓ : ℝ) * x ^ ℓ / (ℓ.factorial : ℝ)) ≤ x * Real.exp x := by
    rw [sum_weighted_eq x m]
    exact mul_le_mul_of_nonneg_left (exp_partial_le x hx m) hx
  calc
    (∑ ℓ ∈ Finset.range (m + 1), (69 + 2 * (ℓ : ℝ)) * x ^ ℓ / (ℓ.factorial : ℝ))
        = 69 * (∑ ℓ ∈ Finset.range (m + 1), x ^ ℓ / (ℓ.factorial : ℝ))
          + 2 * (∑ ℓ ∈ Finset.range (m + 1), (ℓ : ℝ) * x ^ ℓ / (ℓ.factorial : ℝ)) := hsplit
    _ ≤ 69 * Real.exp x + 2 * (x * Real.exp x) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (exp_partial_le x hx (m + 1)) (by norm_num))
        (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = (69 + 2 * x) * Real.exp x := by ring

/-- `14√((11+ℓ)·ln 2) ≤ 39 + 2ℓ`. -/
lemma c_bound (ℓ : ℕ) :
    14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2) ≤ 39 + 2 * (ℓ : ℝ) := by
  have hl70 : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := Submission.Consts.log_two_le_70
    have hnorm : (70 : ℝ) / 100 = (7 : ℝ) / 10 := by norm_num
    rwa [hnorm] at h
  have hsqrt : Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2) ≤
      Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * (7 / 10 : ℝ)) := by
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hl70
      (by positivity : 0 ≤ (11 : ℝ) + (ℓ : ℝ)))
  have hnon : 0 ≤ 14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2) := by positivity
  have hnon2 : 0 ≤ 39 + 2 * (ℓ : ℝ) := by positivity
  have hsq : (14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * (7 / 10 : ℝ))) ^ 2 ≤ (39 + 2 * (ℓ : ℝ)) ^ 2 := by
    have hnn : 0 ≤ ((11 : ℝ) + (ℓ : ℝ)) * (7 / 10 : ℝ) := by positivity
    rw [mul_pow, Real.sq_sqrt hnn]
    nlinarith [sq_nonneg (ℓ : ℝ)]
  have hsq1 : (14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2)) ^ 2 ≤
      (14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * (7 / 10 : ℝ))) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ 14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2))
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num : 0 ≤ (14 : ℝ))) 2
  exact Discrepancy.le_of_sq_le_sq hnon hnon2 (le_trans hsq1 hsq)

/-- The constant `c_{(k,ℓ)} + 30 ≤ 69 + 2ℓ` used in the discrepancy bound. -/
lemma coeff_c_le (ℓ : ℕ) :
    14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2) + 30 ≤ 69 + 2 * (ℓ : ℝ) := by
  have h := c_bound ℓ
  linarith

/-- `exp (−c²/196) = (1/2)^(11+ℓ)` where `c = 14√((11+ℓ)ln2)`. -/
lemma exp_term_eq (ℓ : ℕ) :
    Real.exp (-((14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2)) ^ 2) / 196)
      = (1 / 2 : ℝ) ^ (11 + ℓ) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hnon : 0 ≤ ((11 : ℝ) + (ℓ : ℝ)) * Real.log 2 := by positivity
  have hcalc : (14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2)) ^ 2 =
      196 * (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2) := by
    rw [mul_pow, Real.sq_sqrt hnon]
    norm_num
  have hsq : -((14 * Real.sqrt (((11 : ℝ) + (ℓ : ℝ)) * Real.log 2)) ^ 2) / 196 =
      -(((11 : ℝ) + (ℓ : ℝ)) * Real.log 2) := by
    rw [hcalc]
    field_simp
  rw [hsq]
  have h11 : (11 : ℝ) = ((11 : ℕ) : ℝ) := by norm_num
  rw [h11, ← Nat.cast_add]
  rw [Real.exp_neg]
  rw [Real.exp_nat_mul (Real.log 2) (11 + ℓ)]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← inv_pow (a := (2 : ℝ)) (n := 11 + ℓ)]
  norm_num

/-- `Σ_{i < m} (1/2)^i = 2 − 2·(1/2)^m`. -/
lemma sum_half_eq (m : ℕ) :
    (∑ i ∈ Finset.range m, ((1 : ℝ) / 2) ^ i) = 2 - 2 * ((1 : ℝ) / 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : ((1 : ℝ) / 2) ^ m = 2 * ((1 : ℝ) / 2) ^ (m + 1) := by
        rw [pow_succ]
        norm_num
        ring
      rw [hp]
      ring

/-- `Σ_{i < m} (1/2)^i ≤ 2`. -/
lemma sum_half_le_two (m : ℕ) :
    (∑ i ∈ Finset.range m, ((1 : ℝ) / 2) ^ i) ≤ 2 := by
  rw [sum_half_eq]
  have h1 : 0 ≤ 2 * ((1 : ℝ) / 2) ^ m := by positivity
  linarith

/-- `Σ_{i=0}^{L n − 1} (1/2)^(11+i) ≤ (1/2)^10`. -/
lemma sum_half_11_le (n : ℕ) :
    (∑ i ∈ Finset.range (L n), ((1 : ℝ) / 2) ^ (11 + i)) ≤ ((1 : ℝ) / 2) ^ 10 := by
  calc
    (∑ i ∈ Finset.range (L n), ((1 : ℝ) / 2) ^ (11 + i))
        = ∑ i ∈ Finset.range (L n), ((1 : ℝ) / 2) ^ 11 * ((1 : ℝ) / 2) ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [pow_add]
    _ = ((1 : ℝ) / 2) ^ 11 * (∑ i ∈ Finset.range (L n), ((1 : ℝ) / 2) ^ i) := by
          rw [Finset.mul_sum]
    _ ≤ ((1 : ℝ) / 2) ^ 11 * 2 := by
          exact mul_le_mul_of_nonneg_left (sum_half_le_two (L n)) (by positivity)
    _ = ((1 : ℝ) / 2) ^ 10 := by norm_num [pow_succ]

/-- Corollary 4.2 with an arbitrary finite index type (sums over `ι`). -/
lemma cor42_indexed {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin n → ℝ)) (x0 : Fin n → ℝ)
    (hx0 : ∀ i : Fin n, x0 i ∈ Set.Icc (-1) 1) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hsum : (∑ j : ι, Real.exp (-(c j) ^ 2 / 196)) ≤ (n : ℝ) / 16) :
    ∃ x : Fin n → ℝ, (∀ i : Fin n, x i = -1 ∨ x i = 1) ∧
      (∀ j : ι, |Discrepancy.dot (fun i => x i - x0 i) (v j)|
        ≤ (c j + 30) * Real.sqrt (n : ℝ) * Discrepancy.supAbs (v j)) := by
  classical
  let m : ℕ := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let vv : Fin m → Fin n → ℝ := fun j => v (e.symm j)
  let cc : Fin m → ℝ := fun j => c (e.symm j)
  have hc0 : ∀ j : Fin m, 0 ≤ cc j := by
    intro j
    dsimp [cc]
    exact hc (e.symm j)
  have hsum' : (∑ j : Fin m, Real.exp (-(cc j) ^ 2 / 196)) ≤ (n : ℝ) / 16 := by
    calc
      (∑ j : Fin m, Real.exp (-(cc j) ^ 2 / 196))
          = ∑ i : ι, Real.exp (-(c i) ^ 2 / 196) := by
              dsimp [cc]
              exact Equiv.sum_comp e.symm (fun i : ι => Real.exp (-(c i) ^ 2 / 196))
      _ ≤ (n : ℝ) / 16 := hsum
  rcases Discrepancy.cor42_full n m vv x0 hx0 cc hc0 hsum' with ⟨x, hx1, hx2⟩
  refine ⟨x, hx1, ?_⟩
  intro j
  have hj := hx2 (e j)
  simpa [vv, cc] using hj

/-- The discrepancy hypothesis: `Σ_{(k,ℓ)} exp(−c²/196) ≤ n/16` with
`c = 14√((11+ℓ)·ln 2)`. -/
lemma cor42_sum_hyp (n : ℕ) :
    (∑ j : Fin (M n) × Fin (L n),
       Real.exp (-((14 * Real.sqrt (((11 : ℝ) + j.2.1) * Real.log 2)) ^ 2) / 196))
      ≤ (n : ℝ) / 16 := by
  have hM0r : 0 ≤ (M n : ℝ) := by positivity
  calc
    (∑ j : Fin (M n) × Fin (L n),
       Real.exp (-((14 * Real.sqrt (((11 : ℝ) + j.2.1) * Real.log 2)) ^ 2) / 196))
        = ∑ j : Fin (M n) × Fin (L n), ((1 : ℝ) / 2) ^ (11 + j.2.1) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact exp_term_eq j.2.1
    _ = (M n : ℝ) * (∑ ℓ : Fin (L n), ((1 : ℝ) / 2) ^ (11 + ℓ.1)) := by
            rw [Fintype.sum_prod_type]
            simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M n : ℝ) * ((1 : ℝ) / 2) ^ 10 := by
          have hL : (∑ ℓ : Fin (L n), ((1 : ℝ) / 2) ^ (11 + ℓ.1)) ≤ ((1 : ℝ) / 2) ^ 10 := by
            calc
              (∑ ℓ : Fin (L n), ((1 : ℝ) / 2) ^ (11 + ℓ.1))
                  = ∑ i ∈ Finset.range (L n), ((1 : ℝ) / 2) ^ (11 + i) := by
                      exact Fin.sum_univ_eq_sum_range (fun i : ℕ => ((1 : ℝ) / 2) ^ (11 + i)) (L n)
              _ ≤ ((1 : ℝ) / 2) ^ 10 := sum_half_11_le n
          exact mul_le_mul_of_nonneg_left hL hM0r
    _ ≤ (n : ℝ) / 16 := by
          have hE : (M n : ℝ) * ((1 : ℝ) / 2) ^ 10 = (n : ℝ) / 16 := by
            dsimp [M]
            norm_num
            ring_nf
          rw [hE]

/-- Crude global bound on iterated derivatives of a ±1-coefficient
difference function: `|iteratedDeriv ℓ (diffFun n u v) x| ≤ 2n·(2n)^ℓ`. -/
lemma high_deriv_bound {n : ℕ} (u v : Fin n → ℝ)
    (hu1 : ∀ i, |u i| ≤ 1) (hv1 : ∀ i, |v i| ≤ 1) (ℓ : ℕ) (x : ℝ) :
    |iteratedDeriv ℓ (diffFun n u v) x| ≤ 2 * (n : ℝ) * (2 * (n : ℝ)) ^ ℓ := by
  have hsum := iteratedDeriv_diffFun n ℓ u v x
  rw [hsum]
  calc
    |∑ i : Fin n, (u i - v i) * iteratedDeriv ℓ (fun θ : ℝ => oddSin i.1 θ) x|
        ≤ ∑ i : Fin n, |(u i - v i) * iteratedDeriv ℓ (fun θ : ℝ => oddSin i.1 θ) x| := by
            simpa using (Finset.abs_sum_le_sum_abs (fun i : Fin n => (u i - v i) * iteratedDeriv ℓ (fun θ : ℝ => oddSin i.1 θ) x) (Finset.univ : Finset (Fin n)))
    _ ≤ ∑ i : Fin n, 2 * (2 * (n : ℝ)) ^ ℓ := by
            apply Finset.sum_le_sum
            intro i hi
            calc
              |(u i - v i) * iteratedDeriv ℓ (fun θ : ℝ => oddSin i.1 θ) x|
                  ≤ |u i - v i| * (freq i.1) ^ ℓ := by
                      rw [abs_mul]
                      exact mul_le_mul_of_nonneg_left (by simpa [oddSin] using abs_iteratedDeriv_sin_mul_le ℓ (hc0 := freq_nonneg i.1) x) (abs_nonneg (u i - v i))
              _ ≤ 2 * (2 * (n : ℝ)) ^ ℓ := by
                      have hc : |u i - v i| ≤ 2 := by
                        have h1 : |u i| ≤ 1 := hu1 i
                        have h2 : |v i| ≤ 1 := hv1 i
                        have habs : |u i - v i| ≤ |u i| + |v i| := by
                          simpa [sub_eq_add_neg, abs_neg] using (abs_add_le (u i) (-(v i)))
                        linarith
                      have hw : (freq i.1) ^ ℓ ≤ (2 * (n : ℝ)) ^ ℓ := pow_le_pow_left₀ (freq_nonneg i.1) (freq_le_two_n i) ℓ
                      calc
                        |u i - v i| * (freq i.1) ^ ℓ ≤ 2 * (freq i.1) ^ ℓ := by
                              exact mul_le_mul_of_nonneg_right hc (pow_nonneg (freq_nonneg i.1) ℓ)
                        _ ≤ 2 * (2 * (n : ℝ)) ^ ℓ := by
                              exact mul_le_mul_of_nonneg_left hw (by norm_num)
    _ = 2 * (n : ℝ) * (2 * (n : ℝ)) ^ ℓ := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring

/-- |a·b/c| ≤ A·B/c from |a| ≤ A, |b| ≤ B, A ≥ 0, c > 0. -/
lemma abs_div_le (a b c : ℝ) (A B : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hA : 0 ≤ A) (hc : 0 < c) : |a * b / c| ≤ A * B / c := by
  have hB : 0 ≤ B := le_trans (abs_nonneg b) hb
  have h1 : |a * b / c| ≤ |a| * |b| / c := by
    rw [abs_div, abs_mul]
    rw [abs_of_nonneg hc.le]
  have h2 : |a| * |b| ≤ A * B := by
    calc |a| * |b| ≤ A * |b| := mul_le_mul_of_nonneg_right ha (abs_nonneg b)
      _ ≤ A * B := mul_le_mul_of_nonneg_left hb hA
  exact le_trans h1 (div_le_div_of_nonneg_right h2 hc.le)

/-- Bound one Taylor term using the derivative bound at the sample point. -/
lemma taylor_term_le {n : ℕ} (f : ℝ → ℝ) (θ θk δ0 a : ℝ) (ℓ : ℕ)
    (hder : |iteratedDeriv ℓ f θk|
      ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * (2 * (n : ℝ)) ^ ℓ)
    (hd : |θ - θk| ≤ δ0) (ha : a = 2 * (n : ℝ) * δ0) :
    |(iteratedDeriv ℓ f θk) * (θ - θk) ^ ℓ / (ℓ.factorial : ℝ)|
      ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * a ^ ℓ / (ℓ.factorial : ℝ) := by
  have hcpos : (0 : ℝ) < (ℓ.factorial : ℝ) := by exact_mod_cast (Nat.factorial_pos ℓ)
  have hA0 : 0 ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) := by positivity
  have hEq : (2 * (n : ℝ)) ^ ℓ * δ0 ^ ℓ = a ^ ℓ := by
    rw [ha]
    rw [← mul_pow]
  have hpow : |(θ - θk) ^ ℓ| ≤ δ0 ^ ℓ := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hd ℓ
  calc
    |(iteratedDeriv ℓ f θk) * (θ - θk) ^ ℓ / (ℓ.factorial : ℝ)|
        ≤ ((69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * (2 * (n : ℝ)) ^ ℓ) * δ0 ^ ℓ / (ℓ.factorial : ℝ) := by
            exact abs_div_le (iteratedDeriv ℓ f θk) ((θ - θk) ^ ℓ) (ℓ.factorial : ℝ)
              ((69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * (2 * (n : ℝ)) ^ ℓ) (δ0 ^ ℓ) hder hpow
              (by positivity) hcpos
    _ = (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * ((2 * (n : ℝ)) ^ ℓ * δ0 ^ ℓ) / (ℓ.factorial : ℝ) := by ring
    _ = (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * a ^ ℓ / (ℓ.factorial : ℝ) := by rw [hEq]

/-- The Taylor remainder is absorbed by the next term of the exponential
series (order `2n+1`). -/
lemma rem_tail_le {n : ℕ} (_hn1 : 1 ≤ n) (θ θk δ0 a : ℝ)
    (hd : |θ - θk| ≤ δ0) (hδnn : 0 ≤ δ0) (ha : a = 2 * (n : ℝ) * δ0)
    (hcoeff : 2 * (n : ℝ) ≤ (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * Real.sqrt (n : ℝ)) :
    (2 * (n : ℝ)) * (2 * (n : ℝ)) ^ (2 * n + 1) * |θ - θk| ^ (2 * n + 1) /
        ((2 * n + 1).factorial : ℝ)
      ≤ (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * Real.sqrt (n : ℝ) * a ^ (2 * n + 1) /
        ((2 * n + 1).factorial : ℝ) := by
  have h2n0 : 0 ≤ 2 * (n : ℝ) := by
    have hz : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    nlinarith
  have hfacpos : (0 : ℝ) < ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos (2 * n + 1))
  have hEq : (2 * (n : ℝ)) ^ (2 * n + 1) * |θ - θk| ^ (2 * n + 1) =
      (2 * (n : ℝ) * |θ - θk|) ^ (2 * n + 1) := by
    rw [← mul_pow]
  have hd2 : 2 * (n : ℝ) * |θ - θk| ≤ a := by
    rw [ha]
    exact mul_le_mul_of_nonneg_left hd h2n0
  have hnn : 0 ≤ 2 * (n : ℝ) * |θ - θk| := mul_nonneg h2n0 (abs_nonneg _)
  have hpow : (2 * (n : ℝ) * |θ - θk|) ^ (2 * n + 1) ≤ a ^ (2 * n + 1) :=
    pow_le_pow_left₀ hnn hd2 (2 * n + 1)
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg h2n0 hδnn
  have hae0 : 0 ≤ a ^ (2 * n + 1) := pow_nonneg ha0 (2 * n + 1)
  have hcoeff2 : 2 * (n : ℝ) * a ^ (2 * n + 1) ≤
      (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * Real.sqrt (n : ℝ) * a ^ (2 * n + 1) := by
    have hm := mul_le_mul_of_nonneg_right hcoeff hae0
    simpa [mul_assoc] using hm
  calc
    (2 * (n : ℝ)) * (2 * (n : ℝ)) ^ (2 * n + 1) * |θ - θk| ^ (2 * n + 1) /
        ((2 * n + 1).factorial : ℝ)
        = (2 * (n : ℝ)) * ((2 * (n : ℝ)) ^ (2 * n + 1) * |θ - θk| ^ (2 * n + 1)) /
            ((2 * n + 1).factorial : ℝ) := by ring
    _ = (2 * (n : ℝ)) * (2 * (n : ℝ) * |θ - θk|) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by rw [hEq]
    _ ≤ (2 * (n : ℝ)) * a ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow h2n0) hfacpos.le
    _ ≤ (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * Real.sqrt (n : ℝ) * a ^ (2 * n + 1) /
        ((2 * n + 1).factorial : ℝ) := by
        exact div_le_div_of_nonneg_right hcoeff2 hfacpos.le

/-- The Taylor polynomial of order `2n` is bounded by the weighted exponential
partial sum. -/
lemma taylor_poly_bound_le {n : ℕ} (f : ℝ → ℝ) (θ θk δ0 a : ℝ)
    (ha : a = 2 * (n : ℝ) * δ0)
    (hder : ∀ ℓ : ℕ, ℓ < L n →
        |iteratedDeriv ℓ f θk|
          ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * (2 * (n : ℝ)) ^ ℓ)
    (hd : |θ - θk| ≤ δ0) :
    |∑ ℓ ∈ Finset.range (2 * n + 1), (iteratedDeriv ℓ f θk) * (θ - θk) ^ ℓ / (ℓ.factorial : ℝ)|
      ≤ Real.sqrt (n : ℝ) * (∑ ℓ ∈ Finset.range (2 * n + 1), (69 + 2 * (ℓ : ℝ)) * a ^ ℓ / (ℓ.factorial : ℝ)) := by
  have htermb : ∀ ℓ : ℕ, ℓ ∈ Finset.range (2 * n + 1) →
      |(iteratedDeriv ℓ f θk) * (θ - θk) ^ ℓ / (ℓ.factorial : ℝ)|
        ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * a ^ ℓ / (ℓ.factorial : ℝ) := by
    intro ℓ hℓ
    have hℓL : ℓ < L n := by
      dsimp [L]
      exact Finset.mem_range.mp hℓ
    exact taylor_term_le (f := f) (θ := θ) (θk := θk) (δ0 := δ0) (a := a) ℓ (hder ℓ hℓL) hd ha
  calc
    |∑ ℓ ∈ Finset.range (2 * n + 1), (iteratedDeriv ℓ f θk) * (θ - θk) ^ ℓ / (ℓ.factorial : ℝ)|
        ≤ ∑ ℓ ∈ Finset.range (2 * n + 1),
            |(iteratedDeriv ℓ f θk) * (θ - θk) ^ ℓ / (ℓ.factorial : ℝ)| := by
              exact Finset.abs_sum_le_sum_abs (fun ℓ : ℕ => (iteratedDeriv ℓ f θk) * (θ - θk) ^ ℓ / (ℓ.factorial : ℝ)) (Finset.range (2 * n + 1))
    _ ≤ ∑ ℓ ∈ Finset.range (2 * n + 1), (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * a ^ ℓ / (ℓ.factorial : ℝ) := by
              exact Finset.sum_le_sum (fun ℓ hℓ => htermb ℓ hℓ)
    _ = ∑ ℓ ∈ Finset.range (2 * n + 1),
          Real.sqrt (n : ℝ) * ((69 + 2 * (ℓ : ℝ)) * a ^ ℓ / (ℓ.factorial : ℝ)) := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              ring
    _ = Real.sqrt (n : ℝ) * (∑ ℓ ∈ Finset.range (2 * n + 1), (69 + 2 * (ℓ : ℝ)) * a ^ ℓ / (ℓ.factorial : ℝ)) := by
              rw [Finset.mul_sum]

/-- `δ0 ≥ 0` for `1 ≤ n`. -/
lemma delta0_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ delta0 n := by
  dsimp [delta0]
  have hMn : (0 : ℝ) < (M n : ℝ) := by
    dsimp [M]
    exact_mod_cast (by omega : 0 < 64 * n)
  have hden : (0 : ℝ) < 4 * (M n : ℝ) := mul_pos (by norm_num) hMn
  exact div_nonneg Real.pi_pos.le hden.le

/-- `2n·δ0 ≤ 2n·δ0` normal form: `a ≤ (22/7)/128`. -/
lemma a_le {n : ℕ} (hn : 1 ≤ n) : 2 * (n : ℝ) * delta0 n ≤ (22 / 7 : ℝ) / 128 := by
  dsimp [delta0, M]
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn0r : (n : ℝ) ≠ 0 := ne_of_gt hpos
  have hπ : Real.pi ≤ 22 / 7 := Submission.Consts.pi_le_22_div_7
  have h64 : ((64 * n : ℕ) : ℝ) = 64 * (n : ℝ) := by
    rw [Nat.cast_mul]
    norm_num
  have hcalc : 2 * (n : ℝ) * (Real.pi / (4 * ((64 * n : ℕ) : ℝ))) = Real.pi / 128 := by
    rw [h64]
    field_simp [hn0r]
    ring
  rw [hcalc]
  exact div_le_div_of_nonneg_right hπ (by norm_num : (0 : ℝ) ≤ 128)

/-- `(1 : ℝ) ≤ √n` for `1 ≤ n`. -/
lemma one_le_sqrt_n {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq := Real.sqrt_le_sqrt hnR
  simpa using hsq

/-- coefficient needed to absorb the remainder: `2n ≤ (69+2(2n+1))·√n`. -/
lemma two_n_le_coeff {n : ℕ} (hn : 1 ≤ n) :
    2 * (n : ℝ) ≤ (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * Real.sqrt (n : ℝ) := by
  have h1n := one_le_sqrt_n hn
  have hlin : 2 * (n : ℝ) ≤ 69 + 2 * (((2 * n + 1 : ℕ) : ℝ)) := by
    push_cast
    nlinarith
  have hpos2 : 0 ≤ 69 + 2 * (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  have hmul : (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * 1 ≤ (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_left h1n hpos2
  nlinarith

/-- If `a ≤ x ≤ b` and `m` is the midpoint with `δ = (b−a)/2`, then `|x−m| ≤ δ`. -/
lemma abs_sub_le_of_mem_Icc_mid {a b m x δ : ℝ} (hax : a ≤ x) (hxb : x ≤ b)
    (hm : m = (a + b) / 2) (hδ : δ = (b - a) / 2) : |x - m| ≤ δ := by
  have h1 : x - m ≤ δ := by
    rw [hm, hδ]
    nlinarith
  have h2 : m - x ≤ δ := by
    rw [hm, hδ]
    nlinarith
  rw [abs_le]
  constructor
  · linarith
  · exact h1

/-- Every `θ ∈ [0, π/2]` is within `δ0` of some sample point `θ_k`. -/
lemma cover (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
    ∃ k : Fin (M n), |θ - theta n k.1| ≤ delta0 n := by
  classical
  have hMn_pos : 0 < M n := by
    dsimp [M]
    omega
  have hM0 : (0 : ℝ) < (M n : ℝ) := by exact_mod_cast hMn_pos
  have hMn_one : 1 ≤ M n := by
    dsimp [M]
    omega
  have hθlo : 0 ≤ θ := hθ.1
  have hθhi : θ ≤ Real.pi / 2 := hθ.2
  let p : ℕ → Prop := fun k => k < M n ∧ θ ≤ (k + 1) * Real.pi / (2 * (M n : ℝ))
  have hp_nonempty : ∃ k, p k := by
    refine ⟨M n - 1, ?_, ?_⟩
    · omega
    · have hcast : ((M n - 1 : ℕ) : ℝ) = (M n : ℝ) - 1 := by
        rw [Nat.cast_sub hMn_one]
        norm_num
      have hEq : ((M n - 1 : ℕ) : ℝ) + 1 = (M n : ℝ) := by rw [hcast]; ring
      have hEq2 : (M n : ℝ) * Real.pi / (2 * (M n : ℝ)) = Real.pi / 2 := by
        have hden : (2 * (M n : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast (ne_of_gt hMn_pos))
        field_simp [hden]
      rw [hEq, hEq2]
      exact hθhi
  let k0 : ℕ := Nat.find hp_nonempty
  have hk0p : p k0 := Nat.find_spec hp_nonempty
  have hk0M : k0 < M n := hk0p.1
  have hk0hi : θ ≤ (k0 + 1) * Real.pi / (2 * (M n : ℝ)) := hk0p.2
  have hk0lo : k0 * Real.pi / (2 * (M n : ℝ)) ≤ θ := by
    by_cases hk0 : k0 = 0
    · have hkR : (k0 : ℝ) = 0 := by exact_mod_cast hk0
      rw [hkR]
      simpa using hθlo
    · have hnot : ¬ p (k0 - 1) := by
        intro h
        have hmin := Nat.find_min' hp_nonempty h
        omega
      have hcase : k0 * Real.pi / (2 * (M n : ℝ)) < θ := by
        by_contra h
        apply hnot
        constructor
        · omega
        · have hkge1 : 1 ≤ k0 := by omega
          have hcast : ((k0 - 1 : ℕ) : ℝ) = (k0 : ℝ) - 1 := by
            rw [Nat.cast_sub hkge1]
            norm_num
          have hEq : ((k0 - 1 : ℕ) : ℝ) + 1 = (k0 : ℝ) := by rw [hcast]; ring
          rw [hEq]
          exact le_of_not_gt h
      exact le_of_lt hcase
  refine ⟨⟨k0, hk0M⟩, ?_⟩
  have hax : (k0 : ℝ) * Real.pi / (2 * (M n : ℝ)) ≤ θ := hk0lo
  have hkadd : ((k0 + 1 : ℕ) : ℝ) = (k0 : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have hxb : θ ≤ ((k0 + 1 : ℕ) : ℝ) * Real.pi / (2 * (M n : ℝ)) := by
    rw [hkadd]
    exact hk0hi
  have hm : theta n k0 = ((k0 : ℝ) * Real.pi / (2 * (M n : ℝ)) +
      ((k0 + 1 : ℕ) : ℝ) * Real.pi / (2 * (M n : ℝ))) / 2 := by
    dsimp [theta]
    rw [hkadd]
    ring
  have hδ : delta0 n = ((((k0 + 1 : ℕ) : ℝ) * Real.pi / (2 * (M n : ℝ))) -
      (k0 : ℝ) * Real.pi / (2 * (M n : ℝ))) / 2 := by
    dsimp [delta0]
    rw [hkadd]
    ring
  exact abs_sub_le_of_mem_Icc_mid hax hxb hm hδ

theorem choose_eps (n N : ℕ) (hn : 2 ≤ n) (K : ℝ) (F : Family.Quad n N)
    (α : Fin N → ℝ) (hα : IsColoring α)
    (hehat : ∀ r : Fin n, |ehat n N K F α r.1| ≤ 1) :
    ∃ ε : Fin n → ℝ, IsColoring ε ∧
      ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) →
        |sOdd n ε θ - sHat n N K F α θ| ≤ 75 * Real.sqrt (n : ℝ) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn0 : 0 < n := by omega
  let x0 : Fin n → ℝ := fun i => ehat n N K F α i.1
  have hx0 : ∀ i : Fin n, x0 i ∈ Set.Icc (-1) 1 := by
    intro i
    have h : |x0 i| ≤ 1 := by simpa [x0] using hehat i
    exact abs_le.mp h
  let vv : (Fin (M n) × Fin (L n)) → Fin n → ℝ := fun j => dvec n j.2.1 j.1.1
  let cc : (Fin (M n) × Fin (L n)) → ℝ := fun j => 14 * Real.sqrt (((11 : ℝ) + j.2.1) * Real.log 2)
  have hc0 : ∀ j : Fin (M n) × Fin (L n), 0 ≤ cc j := by
    intro j
    dsimp [cc]
    exact mul_nonneg (by norm_num : 0 ≤ (14 : ℝ)) (Real.sqrt_nonneg _)
  have hsum0 : (∑ j : Fin (M n) × Fin (L n), Real.exp (-(cc j) ^ 2 / 196)) ≤ (n : ℝ) / 16 := by
    dsimp [cc]
    exact cor42_sum_hyp n
  rcases cor42_indexed (n := n) (ι := Fin (M n) × Fin (L n)) vv x0 hx0 cc hc0 hsum0 with ⟨ε, hε1, hε2⟩
  have hεcol : IsColoring ε := by
    intro i
    rcases hε1 i with h | h
    · exact Or.inr h
    · exact Or.inl h
  refine ⟨ε, hεcol, ?_⟩
  let f : ℝ → ℝ := diffFun n ε x0
  have hfC : ∀ k : ℕ, ContDiff ℝ (k : WithTop ℕ∞) f := by
    intro k
    dsimp [f]
    exact contDiff_diffFun (u := ε) (v := x0)
  have hx0b : ∀ i : Fin n, |x0 i| ≤ 1 := by
    intro i
    exact abs_le.mpr (hx0 i)
  have hε1b : ∀ i : Fin n, |ε i| ≤ 1 := by
    intro i
    rcases hε1 i with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hbd : ∀ y : ℝ, |iteratedDeriv (2 * n + 1) f y| ≤ 2 * (n : ℝ) * (2 * (n : ℝ)) ^ (2 * n + 1) := by
    intro y
    dsimp [f]
    exact high_deriv_bound (u := ε) (v := x0) hε1b hx0b (2 * n + 1) y
  have hbnd : ∀ (k : Fin (M n)) (ℓ : ℕ), ℓ < L n →
      |iteratedDeriv ℓ f (theta n k.1)|
        ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * (2 * (n : ℝ)) ^ ℓ := by
    intro k ℓ hℓ
    have hid : iteratedDeriv ℓ f (theta n k.1) =
        Discrepancy.dot (fun i => ε i - x0 i) (dvec n ℓ k.1) := by
      dsimp [f]
      rw [iteratedDeriv_diffFun]
      rfl
    have h1 := hε2 (k, ⟨ℓ, hℓ⟩)
    have hsup : Discrepancy.supAbs (dvec n ℓ k.1) ≤ (2 * (n : ℝ)) ^ ℓ :=
      supAbs_dvec_le n ℓ k.1 hn0
    have hc : cc (k, ⟨ℓ, hℓ⟩) + 30 ≤ 69 + 2 * (ℓ : ℝ) := by
      dsimp [cc]
      exact coeff_c_le ℓ
    calc
      |iteratedDeriv ℓ f (theta n k.1)|
          = |Discrepancy.dot (fun i => ε i - x0 i) (dvec n ℓ k.1)| := by rw [hid]
      _ ≤ (cc (k, ⟨ℓ, hℓ⟩) + 30) * Real.sqrt (n : ℝ) * Discrepancy.supAbs (dvec n ℓ k.1) := by
          simpa [vv] using h1
      _ ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * Discrepancy.supAbs (dvec n ℓ k.1) := by
          have hpos : 0 ≤ Real.sqrt (n : ℝ) * Discrepancy.supAbs (dvec n ℓ k.1) := by
            exact mul_nonneg (Real.sqrt_nonneg _) (Discrepancy.supAbs_nonneg _)
          have hm := mul_le_mul_of_nonneg_right hc hpos
          simpa [mul_assoc] using hm
      _ ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) * (2 * (n : ℝ)) ^ ℓ := by
          have h2 : 0 ≤ (69 + 2 * (ℓ : ℝ)) * Real.sqrt (n : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_left hsup h2
  intro θ hθ
  rcases cover n hn1 θ hθ with ⟨k, hkdist⟩
  have hd0 : |θ - theta n k.1| ≤ delta0 n := hkdist
  have hδnn : 0 ≤ delta0 n := delta0_nonneg hn1
  by_cases hxk : θ = theta n k.1
  · have hb := hbnd k 0 (by dsimp [L]; omega)
    have hid0 : iteratedDeriv 0 f (theta n k.1) = f (theta n k.1) := by simp
    have hfθ : |f θ| ≤ 69 * Real.sqrt (n : ℝ) := by
      rw [hxk]
      have hb0 : |f (theta n k.1)| ≤ 69 * Real.sqrt (n : ℝ) := by
        have hb' : |iteratedDeriv 0 f (theta n k.1)| ≤ 69 * Real.sqrt (n : ℝ) * 1 := by
          simpa [hid0] using hb
        simpa using hb'
      exact hb0
    have hgoal : |f θ| ≤ 75 * Real.sqrt (n : ℝ) := by
      calc
        |f θ| ≤ 69 * Real.sqrt (n : ℝ) := hfθ
        _ ≤ 75 * Real.sqrt (n : ℝ) := by
          have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
          nlinarith
    have hconn : f θ = sOdd n ε θ - sHat n N K F α θ := by
      dsimp [f]
      exact diffFun_eq_sOdd_sub_sHat n N K F ε α θ
    simpa [hconn] using hgoal
  · let a : ℝ := 2 * (n : ℝ) * delta0 n
    have ha : a = 2 * (n : ℝ) * delta0 n := rfl
    have ha0 : 0 ≤ a := by
      rw [ha]
      exact mul_nonneg (by nlinarith) hδnn
    have ha_le : a ≤ (22 / 7 : ℝ) / 128 := by
      dsimp [a]
      exact a_le hn1
    have hkt : theta n k.1 ≠ θ := Ne.symm hxk
    have ht := taylor_bound (f := f) (x := θ) (x0 := theta n k.1) (m := 2 * n)
      (B := 2 * (n : ℝ) * (2 * (n : ℝ)) ^ (2 * n + 1)) hkt hfC (by intro y hy; exact hbd y)
    let T : ℝ := ∑ ℓ ∈ Finset.range (2 * n + 1),
        (iteratedDeriv ℓ f (theta n k.1)) * (θ - theta n k.1) ^ ℓ / (ℓ.factorial : ℝ)
    have hTrem : |f θ - T| ≤ (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * Real.sqrt (n : ℝ) * a ^ (2 * n + 1) /
        ((2 * n + 1).factorial : ℝ) := by
      have hts : |f θ - T| ≤ (2 * (n : ℝ)) * (2 * (n : ℝ)) ^ (2 * n + 1) * |θ - theta n k.1| ^ (2 * n + 1) /
          ((2 * n + 1).factorial : ℝ) := by
        simpa [T] using ht
      exact le_trans hts (rem_tail_le (n := n) hn1 θ (theta n k.1) (delta0 n) a hd0 hδnn ha (two_n_le_coeff hn1))
    have hT := taylor_poly_bound_le (f := f) (θ := θ) (θk := theta n k.1) (δ0 := delta0 n) (a := a) ha
      (fun ℓ hℓ => hbnd k ℓ hℓ) hd0
    have htri : |f θ| ≤ |f θ - T| + |T| := by
      calc
        |f θ| = |(f θ - T) + T| := by congr 1; ring
        _ ≤ |f θ - T| + |T| := abs_add_le _ _
    have hmain : |f θ| ≤ Real.sqrt (n : ℝ) * ((69 + 2 * a) * Real.exp a) := by
      calc
        |f θ| ≤ |f θ - T| + |T| := htri
        _ ≤ (69 + 2 * (((2 * n + 1 : ℕ) : ℝ))) * Real.sqrt (n : ℝ) * a ^ (2 * n + 1) /
            ((2 * n + 1).factorial : ℝ)
            + Real.sqrt (n : ℝ) * (∑ ℓ ∈ Finset.range (2 * n + 1), (69 + 2 * (ℓ : ℝ)) * a ^ ℓ / (ℓ.factorial : ℝ)) := by
              exact add_le_add hTrem hT
        _ = Real.sqrt (n : ℝ) * (∑ ℓ ∈ Finset.range (2 * n + 2), (69 + 2 * (ℓ : ℝ)) * a ^ ℓ / (ℓ.factorial : ℝ)) := by
              have hsplit := Finset.sum_range_succ (fun ℓ : ℕ => (69 + 2 * (ℓ : ℝ)) * a ^ ℓ / (ℓ.factorial : ℝ)) (2 * n + 1)
              rw [hsplit]
              ring
        _ ≤ Real.sqrt (n : ℝ) * ((69 + 2 * a) * Real.exp a) := by
              have hpw := partial_weighted_le_exp a ha0 (2 * n + 1)
              exact mul_le_mul_of_nonneg_left hpw (Real.sqrt_nonneg _)
    have hfinal : |f θ| ≤ 75 * Real.sqrt (n : ℝ) := by
      calc
        |f θ| ≤ Real.sqrt (n : ℝ) * ((69 + 2 * a) * Real.exp a) := hmain
        _ = (69 + 2 * a) * Real.exp a * Real.sqrt (n : ℝ) := by ring
        _ ≤ 74 * Real.sqrt (n : ℝ) := by
              have hnum := taylor_numeric a ha0 ha_le
              have h74 : (69 + 2 * a) * Real.exp a ≤ 74 := by linarith
              exact mul_le_mul_of_nonneg_right h74 (Real.sqrt_nonneg _)
        _ ≤ 75 * Real.sqrt (n : ℝ) := by
              have hs : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
              nlinarith
    have hconn : f θ = sOdd n ε θ - sHat n N K F α θ := by
      dsimp [f]
      exact diffFun_eq_sOdd_sub_sHat n N K F ε α θ
    simpa [hconn] using hfinal

end S5

end Submission
