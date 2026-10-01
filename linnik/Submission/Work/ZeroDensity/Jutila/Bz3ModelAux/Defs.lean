/-
# Vocabulary for the continuous-model evaluation `Bz3ModelEval`

`Work.ZeroDensity.Jutila.s3cont z N` (`Bz3Defs.lean`) is the continuous model of the `S₃` main
term: the triple sum over `q ≤ N/z`, `r, t ≤ N/(q z)` of

  `[r ⟂ t]·μ(r)μ(t)·s3c(rt)·(N/(qrt))·((log((N/(qrt))·t/z) − 1)(log((N/(qrt))·r/z) − 1) + 1)`,

with `s3c(c) = ζ(2)^{-1}∏_{p | c} p/(p+1)`.  For squarefree coprime `r, t` one has
`s3c(rt)·(N/(qrt)) = ζ(2)^{-1}·(N/q)·(1/κ(r))·(1/κ(t))` (`Bz3Defs.s3c_mul_eq_of_coprime`), and
`log((N/(qrt))·t/z) = log(Q_q/r)`, `log((N/(qrt))·r/z) = log(Q_q/t)` where `Q_q = N/(q z)`;
this is the *decoupled* shape in which the inner `r`-summation becomes an instance of the
Mertens-type input `KappaMertensInput` (Graham (11),(12); An, arXiv:2206.10104, Lemmas 11ing/12ing).

The definitions below fix that vocabulary:

* `Qq z N q = N/(q z)` (as a real number), `Bq z N q = ⌊N/(q z)⌋` (the truncation limit);
* `Dq B Q` is the decoupled inner double sum (weights `μ(r)μ(t)/(κ(r)κ(t))`, indicator `[r ⟂ t]`);
* `Gq B Q = Σ_{t ≤ B} μ(t)(log(Q/t) − 1)/t` is the single sum left after the `r`-summation has been
  replaced by its Mertens mean value `ζ(2)·κ(t)/t`, whose value is `1 + O(log^{-2})`
  by `Work.LinnikAreas.Density4.BzHard.mertens_log_weighted_one`.
-/
import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

namespace Work.ZeroDensity.Jutila.Bz3ModelAux

open Finset

noncomputable section

/-- `Qq z N q = N/(q z)` as a real number (the real summation limit of the `q`-th inner sums). -/
def Qq (z N q : ℕ) : ℝ := (N : ℝ) / ((q : ℝ) * (z : ℝ))

/-- `Bq z N q = ⌊N/(q z)⌋`, the truncation limit of the `q`-th inner sums. -/
def Bq (z N q : ℕ) : ℕ := N / (q * z)

/-- The decoupled `q`-th inner double sum of the continuous model `s3cont`:
`Σ_{r,t ≤ B} [r ⟂ t]·μ(r)μ(t)/(κ(r)κ(t))·((log(Q/r) − 1)(log(Q/t) − 1) + 1)`. -/
def Dq (B : ℕ) (Q : ℝ) : ℝ :=
  ∑ r ∈ Icc 1 B, ∑ t ∈ Icc 1 B,
    (if Nat.Coprime r t then
        (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
      (((1 / Work.ZeroDensity.Jutila.kap r) * (1 / Work.ZeroDensity.Jutila.kap t)) *
        ((Real.log (Q / (r : ℝ)) - 1) * (Real.log (Q / (t : ℝ)) - 1) + 1))

/-- The single Möbius sum left after the inner `r`-summation of `Dq`:
`Σ_{t ≤ B} μ(t)·(log(Q/t) − 1)/t`. -/
def Gq (B : ℕ) (Q : ℝ) : ℝ :=
  ∑ t ∈ Icc 1 B, (ArithmeticFunction.moebius t : ℝ) * (Real.log (Q / (t : ℝ)) - 1) / (t : ℝ)

/-- `Bq z N q ≤ Qq z N q`: the truncation limit is at most the real limit. -/
lemma Bq_le_Qq (z N q : ℕ) : (Bq z N q : ℝ) ≤ Qq z N q := by
  unfold Bq Qq
  rw [← Nat.cast_mul]
  exact Nat.cast_div_le (α := ℝ)

/-- `Qq z N q < Bq z N q + 1`: the truncation limit is the floor of `N/(qz)`. -/
lemma Qq_lt_Bq_succ (z N q : ℕ) : Qq z N q < (Bq z N q : ℝ) + 1 := by
  unfold Bq Qq
  rcases Nat.eq_zero_or_pos (q * z) with h | h
  · have h0 : ((q : ℝ) * (z : ℝ)) = 0 := by rw [← Nat.cast_mul, h]; simp
    rw [h0, h, Nat.div_zero]
    norm_num
  · have h1 : N < (N / (q * z) + 1) * (q * z) :=
      (Nat.div_lt_iff_lt_mul h).mp (Nat.lt_succ_self _)
    have h2 : (N : ℝ) < (((N / (q * z) : ℕ) : ℝ) + 1) * ((q : ℝ) * (z : ℝ)) := by
      have h2' := Nat.cast_lt (α := ℝ).mpr h1
      push_cast at h2'
      exact h2'
    have hm : (0 : ℝ) < (q : ℝ) * (z : ℝ) := by
      rw [← Nat.cast_mul]
      exact_mod_cast h
    rw [div_lt_iff₀ hm]
    exact h2

/-- `Qq z N q ≤ 2·Bq z N q` as soon as `Bq z N q ≥ 1` (the hypothesis `Q ≤ 2B` of the
per-`q` estimates, automatically satisfied in the application). -/
lemma Qq_le_two_Bq (z N q : ℕ) (h : 1 ≤ Bq z N q) : Qq z N q ≤ 2 * (Bq z N q : ℝ) := by
  have h1 := Qq_lt_Bq_succ z N q
  have h2 : (1 : ℝ) ≤ (Bq z N q : ℝ) := by exact_mod_cast h
  linarith

/-- `Bq z N q ≥ 1` for `q ≤ N/z`. -/
lemma Bq_pos {z N q : ℕ} (hq : 1 ≤ q) (hz : 1 ≤ z) (hqz : q ≤ N / z) : 1 ≤ Bq z N q := by
  unfold Bq
  rw [Nat.le_div_iff_mul_le (by positivity : 0 < q * z)]
  have h : q * z ≤ N := by
    rw [← Nat.le_div_iff_mul_le (by omega : 0 < z)]
    exact hqz
  calc 1 * (q * z) = q * z := one_mul _
    _ ≤ N := h

/-- `Qq z N q > 0` for `q ≥ 1`, `z ≥ 1`, `N ≥ 1`. -/
lemma Qq_pos {z N q : ℕ} (hq : 1 ≤ q) (hz : 1 ≤ z) (hN : 1 ≤ N) : 0 < Qq z N q := by
  unfold Qq
  have h1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h2 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have h3 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  positivity

end

end Work.ZeroDensity.Jutila.Bz3ModelAux
