import Mathlib
import Submission.ArcFamily
import Submission.S5_defs
import Submission.S5_chooseAlpha
import Submission.S5_chooseEps
import Submission.S5_sHat
import Submission.TrigObservation
import Submission.Consts

/-! Section 5, Theorem 2.4 of the paper (the odd sine polynomial), assembled
from `choose_alpha` (Lemma 5.3), `choose_eps` (Lemmas 5.4–5.5), and the
bounds on `ŝ` (`S5_sHat`).

Fix `K := 160`, a quadrant family `F` with `N ≤ n/2^41`, `n ≥ 2^16`.  We show
that there is an odd sine polynomial `s_o(θ) = Σ_{r<n} ε_r sin((2r+1)θ)`
(`ε_r ∈ {±1}`) such that

    |s_o(θ)| ≥ 10·√n    for every θ ∈ [0,π/2] ∩ ⋃F
    |s_o(θ)| ≤ 2^12·√n  for every θ ∈ ℝ .

Assembly: `choose_alpha` gives `α` with `|ê_r(α)| ≤ 1`; `choose_eps` then
gives `ε` with `|s_o(θ) − ŝ(θ)| ≤ 75√n` on `[0,π/2]`; `S5_sHat.sHat_lower`
gives `|ŝ(θ)| ≥ (3/5)·K·√n = 96√n` on `⋃F`, hence
`|s_o(θ)| ≥ 96√n − 75√n = 21√n ≥ 10√n`; `S5_sHat.sHat_upper` gives
`|ŝ(θ)| ≤ 8K√n = 1280√n`, hence `|s_o| ≤ 1355√n ≤ 2^12√n` on `[0,π/2]`.

The global bound on all of `ℝ` follows from the symmetries of an odd sine
sum: `s_o(π−θ) = s_o(θ)`, `s_o(π+θ) = −s_o(θ)`, `s_o(−θ) = −s_o(θ)`,
`s_o(θ + 2π) = s_o(θ)` (see `Submission.Trig.sin_odd_mul_pi_sub/add`), so
every `θ` is `π±θ`-or-periodicity related to a point of `[0,π/2]` with the
same `|s_o|`. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

namespace Submission
namespace S5

/-- Numerical: `(3/5)·160 − 75 = 21 ≥ 10` and `8·160 + 75 ≤ 2^12`. -/
lemma constants_ok : (3 / 5 : ℝ) * 160 - 75 ≥ 10 ∧ 8 * 160 + 75 ≤ 2 ^ 12 := by
  norm_num

/-! ## Pointwise symmetry of the odd sine terms -/

private lemma oddSin_pi_sub (r : ℕ) (θ : ℝ) : oddSin r (Real.pi - θ) = oddSin r θ := by
  unfold oddSin freq
  have hcast : (((2 * r + 1 : ℕ) : ℝ)) = (2 * (r : ℝ) + 1) := by norm_num
  have h := Trig.sin_odd_mul_pi_sub (2 * r + 1) (by exact ⟨r, rfl⟩) θ
  rw [← hcast]
  exact h

private lemma oddSin_pi_add (r : ℕ) (θ : ℝ) : oddSin r (Real.pi + θ) = -oddSin r θ := by
  unfold oddSin freq
  have hcast : (((2 * r + 1 : ℕ) : ℝ)) = (2 * (r : ℝ) + 1) := by norm_num
  have h := Trig.sin_odd_mul_pi_add (2 * r + 1) (by exact ⟨r, rfl⟩) θ
  rw [← hcast]
  exact h

private lemma oddSin_neg (r : ℕ) (θ : ℝ) : oddSin r (-θ) = -oddSin r θ := by
  unfold oddSin freq
  rw [mul_neg, Real.sin_neg]

private lemma oddSin_periodic (r : ℕ) (θ : ℝ) : oddSin r (θ + 2 * Real.pi) = oddSin r θ := by
  unfold oddSin freq
  have hcast : (((2 * r + 1 : ℕ) : ℝ)) = (2 * (r : ℝ) + 1) := by norm_num
  have h := Trig.sin_odd_add_two_pi (2 * r + 1) θ
  rw [← hcast]
  exact h

/-- The odd sine polynomial is `|·|`-symmetric enough to extend quadrant bounds
to all of `ℝ`: for odd positions only.  Formal statement: applying any of the
maps `θ ↦ π±θ, −θ, θ+2π` preserves `|Σ_i ε_i sin((2i+1)θ)|`.  We give the
exact identities for `sOdd`. -/
lemma sOdd_pi_sub (n : ℕ) (ε : Fin n → ℝ) (θ : ℝ) :
    sOdd n ε (Real.pi - θ) = sOdd n ε θ := by
  simp [sOdd, oddSin_pi_sub]

lemma sOdd_pi_add (n : ℕ) (ε : Fin n → ℝ) (θ : ℝ) :
    sOdd n ε (Real.pi + θ) = -sOdd n ε θ := by
  simp [sOdd, oddSin_pi_add, Finset.sum_neg_distrib]

lemma sOdd_neg (n : ℕ) (ε : Fin n → ℝ) (θ : ℝ) :
    sOdd n ε (-θ) = -sOdd n ε θ := by
  simp [sOdd, oddSin_neg, Finset.sum_neg_distrib]

lemma sOdd_periodic (n : ℕ) (ε : Fin n → ℝ) (θ : ℝ) :
    sOdd n ε (θ + 2 * Real.pi) = sOdd n ε θ := by
  simp [sOdd, oddSin_periodic]

/-- `sOdd` is periodic with period `k·2π` for every integer `k`. -/
private lemma sOdd_int_mul_two_pi (n : ℕ) (ε : Fin n → ℝ) (k : ℤ) (θ : ℝ) :
    sOdd n ε (θ + (k : ℝ) * (2 * Real.pi)) = sOdd n ε θ := by
  have hper : Function.Periodic (fun θ : ℝ => sOdd n ε θ) (2 * Real.pi) := sOdd_periodic n ε
  simpa using hper.int_mul k θ

/-- Reduce an arbitrary real argument to `[0, 2π)` (periodicity). -/
private lemma sOdd_period_reduce (n : ℕ) (ε : Fin n → ℝ) (θ : ℝ) :
    ∃ φ : ℝ, φ ∈ Set.Ico 0 (2 * Real.pi) ∧ |sOdd n ε θ| = |sOdd n ε φ| := by
  let a := θ / (2 * Real.pi)
  let q : ℤ := Int.floor a
  let φ : ℝ := Int.fract a * (2 * Real.pi)
  have h2pi : (0 : ℝ) < 2 * Real.pi := by nlinarith [Real.pi_pos]
  refine ⟨φ, ?mem, ?eq⟩
  · have hf0 : 0 ≤ Int.fract a := Int.fract_nonneg a
    have hf1 : Int.fract a < 1 := Int.fract_lt_one a
    constructor
    · dsimp [φ]
      exact mul_nonneg hf0 (by nlinarith)
    · dsimp [φ]
      simpa using (mul_lt_mul_of_pos_right hf1 h2pi)
  · have hφ : φ + (q : ℝ) * (2 * Real.pi) = θ := by
      dsimp [φ, q, a]
      rw [Int.fract]
      field_simp [ne_of_gt h2pi]
      ring
    have hval : sOdd n ε θ = sOdd n ε φ := by
      rw [← hφ]
      exact sOdd_int_mul_two_pi n ε q φ
    rw [hval]

/-- Every real `θ` is equivalent (by `θ ↦ π±θ`, `θ ↦ −θ`, and periodicity) to
a point in `[0, π/2]` with the same `|sOdd|`-value. -/
lemma reduce_to_quadrant (n : ℕ) (ε : Fin n → ℝ) (θ : ℝ) :
    ∃ θ0 : ℝ, θ0 ∈ Set.Icc 0 (Real.pi / 2) ∧ |sOdd n ε θ| = |sOdd n ε θ0| := by
  rcases sOdd_period_reduce n ε θ with ⟨φ, hφmem, hφeq⟩
  rcases hφmem with ⟨hφ0, hφlt⟩
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  by_cases hA : φ ≤ Real.pi / 2
  · refine ⟨φ, ⟨hφ0, hA⟩, hφeq⟩
  · have hφA : Real.pi / 2 < φ := lt_of_not_ge hA
    by_cases hB : φ ≤ Real.pi
    · refine ⟨Real.pi - φ, ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · rw [hφeq]
        have h := sOdd_pi_sub n ε φ
        rw [← h]
    · have hφB : Real.pi < φ := lt_of_not_ge hB
      by_cases hC : φ ≤ 3 * Real.pi / 2
      · refine ⟨φ - Real.pi, ⟨?_, ?_⟩, ?_⟩
        · linarith
        · linarith
        · rw [hφeq]
          have h := sOdd_pi_add n ε (φ - Real.pi)
          have hφ' : Real.pi + (φ - Real.pi) = φ := by ring
          rw [hφ'] at h
          rw [h, abs_neg]
      · have hφC : 3 * Real.pi / 2 < φ := lt_of_not_ge hC
        refine ⟨2 * Real.pi - φ, ⟨?_, ?_⟩, ?_⟩
        · linarith
        · linarith
        · rw [hφeq]
          have h1 : sOdd n ε φ = sOdd n ε (-(2 * Real.pi - φ) + 2 * Real.pi) := by
            congr 1
            ring
          rw [h1]
          have hper : sOdd n ε (-(2 * Real.pi - φ) + 2 * Real.pi) =
              sOdd n ε (-(2 * Real.pi - φ)) := sOdd_periodic n ε (-(2 * Real.pi - φ))
          rw [hper]
          have hneg : sOdd n ε (-(2 * Real.pi - φ)) = -sOdd n ε (2 * Real.pi - φ) :=
            sOdd_neg n ε (2 * Real.pi - φ)
          rw [hneg, abs_neg]

/-- Theorem 2.4 (paper), quadrant + global form. -/
theorem theorem_sine (n N : ℕ) (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    (hN : (N : ℝ) ≤ (n : ℝ) / 2 ^ 41) :
    ∃ ε : Fin n → ℝ, IsColoring ε ∧
      (∃ α : Fin N → ℝ, IsColoring α ∧ (∀ r : Fin n, |ehat n N 160 F α r.1| ≤ 1)) ∧
      (∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) → θ ∈ F.union →
        10 * Real.sqrt (n : ℝ) ≤ |sOdd n ε θ|) ∧
      (∀ θ : ℝ, |sOdd n ε θ| ≤ 2 ^ 12 * Real.sqrt (n : ℝ)) := by
  classical
  have hn2 : 2 ≤ n := by
    exact le_trans (by norm_num : (2 : ℕ) ≤ 2 ^ 16) hn
  have hK0 : (0 : ℝ) ≤ 160 := by norm_num
  rcases choose_alpha n N (160 : ℝ) F hK0 (le_rfl : (160 : ℝ) ≤ 160) hN with ⟨α, hαcol, hαehat⟩
  rcases choose_eps n N hn2 (160 : ℝ) F α hαcol hαehat with ⟨ε, hεcol, hεclose⟩
  have hsq : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg (n : ℝ)
  have hlow_quad : ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) → θ ∈ F.union →
      10 * Real.sqrt (n : ℝ) ≤ |sOdd n ε θ| := by
    intro θ hθ hθF
    have hlowhat := sHat_lower n N hn (160 : ℝ) hK0 F α hαcol θ hθ hθF
    have hclose := hεclose θ hθ
    have htri : |sHat n N (160 : ℝ) F α θ| ≤
        |sOdd n ε θ - sHat n N (160 : ℝ) F α θ| + |sOdd n ε θ| := by
      calc
        |sHat n N (160 : ℝ) F α θ|
            = |(sHat n N (160 : ℝ) F α θ - sOdd n ε θ) + sOdd n ε θ| := by congr 1; ring
        _ ≤ |sHat n N (160 : ℝ) F α θ - sOdd n ε θ| + |sOdd n ε θ| := abs_add_le _ _
        _ = |sOdd n ε θ - sHat n N (160 : ℝ) F α θ| + |sOdd n ε θ| := by rw [abs_sub_comm]
    nlinarith [hlowhat, hclose, htri, hsq, constants_ok.1]
  have hup_quad : ∀ θ : ℝ, θ ∈ Set.Icc 0 (Real.pi / 2) →
      |sOdd n ε θ| ≤ 2 ^ 12 * Real.sqrt (n : ℝ) := by
    intro θ hθ
    have huphat := sHat_upper n N hn (160 : ℝ) hK0 F α hαcol θ hθ
    have hclose := hεclose θ hθ
    have htri : |sOdd n ε θ| ≤ |sOdd n ε θ - sHat n N (160 : ℝ) F α θ| +
        |sHat n N (160 : ℝ) F α θ| := by
      calc
        |sOdd n ε θ| = |(sOdd n ε θ - sHat n N (160 : ℝ) F α θ) + sHat n N (160 : ℝ) F α θ| := by
          congr 1
          ring
        _ ≤ |sOdd n ε θ - sHat n N (160 : ℝ) F α θ| + |sHat n N (160 : ℝ) F α θ| := abs_add_le _ _
    nlinarith [huphat, hclose, htri, hsq, constants_ok.2]
  refine ⟨ε, hεcol, ⟨α, hαcol, hαehat⟩, hlow_quad, ?_⟩
  intro θ
  rcases reduce_to_quadrant n ε θ with ⟨θ0, hθ0mem, hθ0eq⟩
  rw [hθ0eq]
  exact hup_quad θ0 hθ0mem

end S5
end Submission
