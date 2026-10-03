/-
# `Submission.Work.FITop4.Red5.window_setup` — the window ladder of the round-5 reduction

The outer `m`-sum of `BformPiTau` is split into

* the *small-`m`* region `1 ≤ m ≤ M₀`, handled by `BformPiTauSmall_le2`; here
  `M₀ = ⌊ϑx/N⌋ + 2` is chosen so that `M₀ N > ϑx` (the `Params.hMN` field) and `2N ≤ M₀`;
* the *dyadic* windows `(M_j, 2M_j]`, `M_j = 2^j M₀` (`j < JJ`), where `JJ` is the least exponent
  with `2^JJ M₀ > M_top`, hence `2^{JJ-1} M₀ ≤ M_top`, so that every dyadic window satisfies
  `M_j · 2N ≤ x` (the `Params.hMNx` field);
* the *top* window `(M_top, 2M_top]`, `M_top = ⌊x/(2N)⌋`, which covers the remaining range
  `(M_top, ⌊x/N⌋]` and *does* satisfy `M_top · 2N ≤ x`.

-/
import Mathlib
import Submission.Work.FITop4.Red5.Vocab

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The start of the top window: `⌊x/(2N)⌋` (the largest `M` with `M · 2N ≤ x`). -/
def MtopN (x N : ℕ) : ℕ := x / (2 * N)

/-- `⌊ϑx/N⌋`, the top of the small-`m` region. -/
def YsN (x N : ℕ) : ℕ := Nat.floor (varthetaOf x Asave * (x : ℝ) / (N : ℝ))

/-- The small-`m` cutoff `M₀ = ⌊ϑx/N⌋ + 2`. -/
def M0N (x N : ℕ) : ℕ := YsN x N + 2

/-- `∃ j, b < 2^j a` for `a > 0` (the Archimedean property of `2^j`). -/
lemma exists_two_pow_mul_gt (a b : ℕ) (ha : 0 < a) : ∃ j : ℕ, b < 2 ^ j * a := by
  refine ⟨b, ?_⟩
  have ha1 : 1 ≤ a := ha
  calc b < 2 ^ b := Nat.lt_two_pow_self
    _ = 2 ^ b * 1 := (mul_one _).symm
    _ ≤ 2 ^ b * a := Nat.mul_le_mul_left _ ha1

lemma M0N_pos (x N : ℕ) : 0 < M0N x N := by unfold M0N; omega

lemma exJJ (x N : ℕ) : ∃ j : ℕ, MtopN x N < 2 ^ j * M0N x N :=
  exists_two_pow_mul_gt (M0N x N) (MtopN x N) (M0N_pos x N)

/-- The number of dyadic windows: the least `JJ` with `2^JJ M₀ > M_top`. -/
def JJN (x N : ℕ) : ℕ := Nat.find (exJJ x N)

lemma MtopN_lt_two_pow_JJN (x N : ℕ) :
    MtopN x N < 2 ^ (JJN x N) * M0N x N := by
  unfold JJN; exact Nat.find_spec (exJJ x N)

lemma two_pow_pred_JJN_mul_le_MtopN {x N : ℕ} (h : 1 ≤ JJN x N) :
    2 ^ (JJN x N - 1) * M0N x N ≤ MtopN x N := by
  have hdef : JJN x N = Nat.find (exJJ x N) := rfl
  rw [hdef] at h ⊢
  exact le_of_not_gt (Nat.find_min (exJJ x N)
    (by omega : Nat.find (exJJ x N) - 1 < Nat.find (exJJ x N)))

/-- The `j`-th dyadic window start. -/
def MjN (x N j : ℕ) : ℕ := 2 ^ j * M0N x N

lemma M0N_ge_two (x N : ℕ) : 2 ≤ M0N x N := by unfold M0N; omega

/-- `M₀ N > ϑx` (the `Params.hMN` field for every window of the ladder). -/
lemma vartheta_mul_lt_M0N_mul (x N : ℕ) (h : 0 < N) :
    varthetaOf x Asave * (x : ℝ) < (M0N x N : ℝ) * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast h
  have hfloor : varthetaOf x Asave * (x : ℝ) / (N : ℝ) < ((YsN x N : ℕ) : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (varthetaOf x Asave * (x : ℝ) / (N : ℝ))
    simpa [YsN] using this
  have h1 : varthetaOf x Asave * (x : ℝ) < (((YsN x N : ℕ) : ℝ) + 1) * (N : ℝ) := by
    have h2 := (div_lt_iff₀ hNpos).mp hfloor
    linarith
  have h3 : (((YsN x N : ℕ) : ℝ) + 1) * (N : ℝ) ≤ (((YsN x N : ℕ) : ℝ) + 2) * (N : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt hNpos); linarith
  have hM0 : ((M0N x N : ℕ) : ℝ) = ((YsN x N : ℕ) : ℝ) + 2 := by
    unfold M0N; push_cast; ring
  rw [hM0]
  linarith

/-! ## The inner summand of `BformPiTau` -/

/-- The inner `m`-summand of `BformPiTau`. -/
def Iterm (x N Pz : ℕ) (C τ : ℝ) (m : ℕ) : ℝ :=
  |∑ n ∈ Finset.Icc 1 (2 * N),
    (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
      then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
        * Work.FITop.atilFIa (m * n) else 0)|

lemma BformPiTau_eq_sum_Iterm (x N Pz : ℕ) (C τ : ℝ) :
    BformPiTau x N Pz C τ = ∑ m ∈ Finset.Icc 1 x, Iterm x N Pz C τ m := rfl

lemma Iterm_nonneg (x N Pz : ℕ) (C τ : ℝ) (m : ℕ) : 0 ≤ Iterm x N Pz C τ m :=
  abs_nonneg _

/-- `I_m = 0` once `m (N+1) > x`: every admissible `n` satisfies `n > N`, so `m n ≥ m (N+1) > x`. -/
lemma Iterm_eq_zero_of_lt (x N Pz : ℕ) (C τ : ℝ) {m : ℕ} (h : x < m * (N + 1)) :
    Iterm x N Pz C τ m = 0 := by
  rw [Iterm]
  refine abs_eq_zero.mpr (Finset.sum_eq_zero (fun n hn => ?_))
  rw [Finset.mem_Icc] at hn
  by_cases hc : N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
  · rw [if_pos hc]
    obtain ⟨hNn, hmn, -⟩ := hc
    have hmono : m * (N + 1) ≤ m * n := Nat.mul_le_mul_left m (by omega)
    omega
  · rw [if_neg hc]

lemma Iterm_eq_zero_of_gt_x (x N Pz : ℕ) (C τ : ℝ) {m : ℕ} (h : x < m) :
    Iterm x N Pz C τ m = 0 := by
  refine Iterm_eq_zero_of_lt x N Pz C τ ?_
  have hmle : m ≤ m * (N + 1) := by
    calc m = m * 1 := (mul_one m).symm
      _ ≤ m * (N + 1) := Nat.mul_le_mul_left m (by omega)
  omega


/-! ## The right-hand sides of the `T2`/`T3` window estimates -/

/-- The right-hand side of the `T2` window estimate: the coprimality part `(5.10)` plus the
`θ`-small shell part. -/
def T2RHS (x N Mn Pz : ℕ) (θ : ℝ) : ℝ :=
  (((Mn : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((5 : ℝ) / 4))
    + (Pz : ℝ)⁻¹ * ((Mn : ℝ) ^ ((3 : ℝ) / 4) * (N : ℝ) ^ ((3 : ℝ) / 4))
    + θ * (((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4))) * (Real.log (x : ℝ)) ^ (100 : ℕ)

/-- The right-hand side of the `T3` (radial-defect) window estimate. -/
def T3RHS (x N Mn : ℕ) (θ : ℝ) : ℝ :=
  θ * (((Mn : ℝ) * (N : ℝ)) ^ ((3 : ℝ) / 4)) * (Real.log (x : ℝ)) ^ (100 : ℕ)


/-- The `j`-th window scale of the ladder: `2^j M₀` for `j < JJ`, and the top window `M_top` for
`j = JJ`.  The index `j` runs over `Fin (JJ+1)`. -/
def MnOf (x N j : ℕ) : ℕ := if j < JJN x N then 2 ^ j * M0N x N else MtopN x N

lemma MnOf_of_lt {x N j : ℕ} (h : j < JJN x N) : MnOf x N j = 2 ^ j * M0N x N := by
  rw [MnOf, if_pos h]

lemma MnOf_of_not_lt {x N j : ℕ} (h : ¬ j < JJN x N) : MnOf x N j = MtopN x N := by
  rw [MnOf, if_neg h]


end
end Work.FITop4.Red5
