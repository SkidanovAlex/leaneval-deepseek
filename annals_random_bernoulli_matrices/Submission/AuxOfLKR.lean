/-
`aux_single_vector`: the per-row small-ball estimate of Tikhomirov
(Lemma l:aux single vector, arXiv:1812.09016), assembled end-to-end from the
eq-aux estimate (`eq_aux`, RogozinBridge, unconditional via the Commons LKR
(`Commons.Probability.Levy.rogozin_measurable`)) through the row bridge
(`row_smallBall_of_cf`, AuxSingleVector) into the tensorization lemma
(`aux_single_vector`, AuxSingleVector).

Conclusion (integer-parameter form): there is a `γ > 0` depending only on `p` such that for every
`ε > 0`, every `n ≥ 2`, every shift `s`, every unit vector `x` and every
integer `r` with `0 < r ≤ n−1` and `ε·(n−1) ≤ r`,

    P{ ‖(B + s·1_{n−1}1_nᵀ)·x‖₂² ≤ γ²·ε·n }
        ≤ ( e·(n−1)/r )^r · (1−p)^((n−1)−r),

where `B` is the (n−1)×n Bernoulli(p) family.  This is exactly the
per-net-point estimate needed by Proposition l:compress.

Bookkeeping: the eq-aux radius `r₀` (uniform in n, from LKR) gives the row
small-ball bound at scale `r₀`; with `γ := r₀/4` and row scale
`η := γ·√(n/(n−1))` we have `η ≤ r₀` for all `n ≥ 2`, and
`η²·ε·(n−1) = γ²·ε·n`.
-/
import Mathlib
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Bernoulli
import Submission.AuxSingleVector
import Submission.RogozinBridge
import ChallengeDeps

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Submission.AuxOfLKR

noncomputable section

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval
open scoped ENNReal BigOperators

universe u

/-- Lemma l:aux single vector (integer-parameter form), from the unconditional
eq aux (`RogozinBridge.eq_aux`, backed by the Commons LKR theorem). -/
theorem aux_single_vector {p : I} (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ (ε : ℝ), 0 < ε → ∀ (n : ℕ), 2 ≤ n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P]
        (B : Fin (n - 1) → Fin n → Ω → ℝ)
        (hBmeas : ∀ k : Fin (n - 1), ∀ j : Fin n, Measurable (B k j))
        (hBind : ProbabilityTheory.iIndepFun (fun kj : Fin (n - 1) × Fin n => B kj.1 kj.2) P)
        (hBlaw : ∀ k : Fin (n - 1), ∀ j : Fin n, HasLaw (B k j) (bernoulliMeasure 1 0 p) P)
        (s : ℝ) {x : Fin n → ℝ} (hx : (∑ j : Fin n, (x j) ^ 2) = 1),
        ∀ (r : ℕ), 0 < r → r ≤ n - 1 → ε * ((n - 1 : ℕ) : ℝ) ≤ (r : ℝ) →
          P.real {ω : Ω |
            (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) ≤
              γ ^ 2 * ε * (n : ℝ)} ≤
            (Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (r : ℝ)) ^ r *
              (1 - (p : ℝ)) ^ ((n - 1) - r) := by
  classical
  rcases (Submission.RogozinBridge.eq_aux hp₀ hp₁) with ⟨r₀, hr₀, hEq0⟩
  let γ : ℝ := r₀ / 4
  have hγ : 0 < γ := by
    dsimp [γ]
    positivity
  refine ⟨γ, hγ, ?_⟩
  intro ε hε0 n hn2 Ω mΩ P hP B hBmeas hBind hBlaw s x hx r hr0 hrm hεr
  let η : ℝ := γ * Real.sqrt ((n : ℝ) / ((n - 1 : ℕ) : ℝ))
  have hdenpos : 0 < ((n - 1 : ℕ) : ℝ) := by
    have h1 : 1 ≤ n - 1 := by omega
    exact_mod_cast (Nat.succ_le_iff.mp h1)
  have hdenne : ((n - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hdenpos
  have hη0 : 0 ≤ η := by
    dsimp [η]
    exact mul_nonneg (le_of_lt hγ) (Real.sqrt_nonneg _)
  have hfrac : (n : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ 4 := by
    have hmain : (n : ℝ) ≤ 4 * ((n - 1 : ℕ) : ℝ) := by
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hcast]
      have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      nlinarith
    exact (div_le_iff₀ hdenpos).2 hmain
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
  have hηR : η ≤ r₀ := by
    dsimp [η, γ]
    have hs4 : Real.sqrt ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ 2 := by
      calc
        Real.sqrt ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ Real.sqrt (4 : ℝ) := Real.sqrt_le_sqrt hfrac
        _ = 2 := by norm_num
    have hle1 : r₀ / 4 * Real.sqrt ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ r₀ / 4 * 2 := by
      exact mul_le_mul_of_nonneg_left hs4 (by positivity)
    calc
      r₀ / 4 * Real.sqrt ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤ r₀ / 4 * 2 := hle1
      _ = r₀ / 2 := by ring
      _ ≤ r₀ := by linarith [hr₀]
  -- per-row eq-aux bound at scale r₀, for every row k
  have hrow₀ : ∀ (k : Fin (n - 1)) (l : ℝ),
      P.real {ω : Ω | |(∑ j : Fin n, B k j ω * x j) - l| ≤ r₀} ≤ (1 - (p : ℝ)) := by
    intro k l
    have hrow_indep : ProbabilityTheory.iIndepFun (fun j : Fin n => B k j) P := by
      have hg : Function.Injective (fun j : Fin n => (k, j)) := by
        intro a b h
        exact congrArg Prod.snd h
      exact ProbabilityTheory.iIndepFun.precomp (f := (fun kj : Fin (n - 1) × Fin n => B kj.1 kj.2)) hg hBind
    have hrow_law : ∀ j : Fin n, HasLaw (B k j) (bernoulliMeasure 1 0 p) P := fun j => hBlaw k j
    have hrow_meas : ∀ j : Fin n, Measurable (B k j) := fun j => hBmeas k j
    exact hEq0 (n := n) (Ω := Ω) P (b := fun j : Fin n => fun ω : Ω => B k j ω)
      (hb_meas := hrow_meas) (hb_indep := hrow_indep) (hb_law := hrow_law)
      (x := x) hx l
  -- per-row small-ball bound at the smaller scale η (absorbing the shift s)
  have hsmall : ∀ k : Fin (n - 1),
      P.real {ω : Ω | |(∑ j : Fin n, (B k j ω + s) * x j)| ≤ η} ≤ (1 - (p : ℝ)) := by
    exact Submission.AuxSingleVector.row_smallBall_of_cf (p := p) hp₁ P (B := B) (x := x) (s := s)
      (R := r₀) (η := η) hηR hrow₀
  have hmain := Submission.AuxSingleVector.aux_single_vector (p := p) hp₀ hp₁
    (n := n) (Ω := Ω) P (B := B) (hBmeas := hBmeas) (hBind := hBind)
    (x := x) hx (s := s) (η := η) hη0 (ε := ε) hε0 (r := r) hr0 hrm hεr hsmall
  -- scale identity: η²·ε·(n−1) = γ²·ε·n
  have hs : (Real.sqrt ((n : ℝ) / ((n - 1 : ℕ) : ℝ))) ^ 2 = (n : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    exact Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) / ((n - 1 : ℕ) : ℝ))
  have hscale : η ^ 2 * ε * ((n - 1 : ℕ) : ℝ) = γ ^ 2 * ε * (n : ℝ) := by
    dsimp [η]
    calc
      (γ * Real.sqrt ((n : ℝ) / ((n - 1 : ℕ) : ℝ))) ^ 2 * ε * ((n - 1 : ℕ) : ℝ)
          = γ ^ 2 * (((n : ℝ) / ((n - 1 : ℕ) : ℝ)) * ε * ((n - 1 : ℕ) : ℝ)) := by
              rw [mul_pow, hs]
              ring
      _ = γ ^ 2 * ε * (n : ℝ) := by
            field_simp [hdenne]
  have hset : {ω : Ω |
      (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) ≤
        η ^ 2 * ε * ((n - 1 : ℕ) : ℝ)}
      = {ω : Ω |
      (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) ≤
        γ ^ 2 * ε * (n : ℝ)} := by
    ext ω
    change (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) ≤ η ^ 2 * ε * ((n - 1 : ℕ) : ℝ)
        ↔ (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) ≤ γ ^ 2 * ε * (n : ℝ)
    rw [hscale]
  have hfin : P.real {ω : Ω |
      (∑ k : Fin (n - 1), ((∑ j : Fin n, (B k j ω + s) * x j)) ^ 2) ≤
        γ ^ 2 * ε * (n : ℝ)} ≤
      (Real.exp 1 * ((n - 1 : ℕ) : ℝ) / (r : ℝ)) ^ r * (1 - (p : ℝ)) ^ ((n - 1) - r) := by
    rw [← hset]
    exact hmain
  exact hfin

end

end Submission.AuxOfLKR
