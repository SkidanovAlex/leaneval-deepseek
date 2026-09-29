import Mathlib
import Submission.Work.TMC14Core.RatRot
import Submission.Work.TMC14Core.Chambers
import Submission.Work.TMC14Core.chamCoef_norm
import Submission.Work.TMC14Core.disc_im_eq_zero

/-!
# TMC14Core: every energy `E` with `‖Δ(E)‖ ≤ 2 + 2λ^q` is a Bloch eigenvalue

For coprime `p`, `q ≥ 1`, `λ > 0` and a real energy `E` whose *discriminant* value
`Δ(E) = (disc p q lam).eval E` lies in the disk of radius `2 + 2λ^q`, there are a phase
`θ` and a quasi-momentum `k` with

`(blochMat p q lam θ k).charpoly.eval E = 0`,

i.e. `E` is an eigenvalue of the periodic Bloch matrix at the pair `(θ,k)`.

Chambers' formula (`blochMat_chambers`) gives

`det(E - blochMat θ k) = Δ(E) + 2(-λ)^q(-1)^{p(q-1)} cos(2πqθ) - 2 cos(2πk)`

with the middle coefficient real of modulus `2λ^q`, so it suffices to solve

`2λ^q cos(2πqθ) + 2 cos(2πk) = Δ(E)`

for real `θ`, `k`.  The left hand side sweeps the whole interval `[-(2+2λ^q), 2+2λ^q]`
(split `Δ(E) = s + (Δ(E) - s)` with `|s| ≤ 2` and `|Δ(E) - s| ≤ 2λ^q`, then absorb
the two pieces in the `k` and the `θ` variable respectively); the hypothesis on `Δ(E)`
is exactly the statement that `Δ(E)` lies in that interval.

The two elementary existence statements are `exists_two_cos_eq_of_abs_le_two`
(delegated, module `Submission.Work.TMC14Core.exists_two_cos_eq_of_abs_le_two`) and
`exists_chamCoef_mul_cos` (delegated, module
`Submission.Work.TMC14Core.exists_chamCoef_mul_cos`); they are reproduced here privately
so that this file is self-contained and does not depend on their build order.
-/

namespace Work.TMC14Core

noncomputable section

/-! ## Elementary existence statements -/

/-- `k ↦ 2 cos(2πk)` maps `ℝ` onto `[-2,2]`. -/
private theorem exists_two_cos_eq_of_abs_le_two_aux (s : ℝ) (hs : |s| ≤ 2) :
    ∃ k : ℝ, 2 * Real.cos (2 * Real.pi * k) = s := by
  have hs' : s / 2 ∈ Set.range Real.cos := by
    rw [Real.range_cos, Set.mem_Icc]
    have h2 : |s / 2| ≤ 1 := by
      rw [abs_div, abs_two, div_le_one (by norm_num : (0:ℝ) < 2)]
      exact hs
    exact abs_le.mp h2
  obtain ⟨x, hx⟩ := hs'
  refine ⟨x / (2 * Real.pi), ?_⟩
  have harg : 2 * Real.pi * (x / (2 * Real.pi)) = x := by field_simp
  rw [harg, hx]
  ring

/-- `chamCoef p q lam = 2(-λ)^q(-1)^{p(q-1)}` is the coercion of a real number. -/
private theorem chamCoef_eq_ofReal (p : ℤ) (q : ℕ) (lam : ℝ) :
    chamCoef p q lam = ((2 * (-lam) ^ q * (-1 : ℝ) ^ (p * ((q : ℤ) - 1)) : ℝ) : ℂ) := by
  rw [chamCoef]
  push_cast
  ring

/-- For `q ≥ 1`, `λ > 0` and `|c| ≤ 2λ^q` there is a phase `θ` with
`chamCoef p q lam * cos(2πqθ) = c`. -/
private theorem exists_chamCoef_mul_cos_aux (p : ℤ) (q : ℕ) (lam : ℝ) (hq : 1 ≤ q)
    (hlam : 0 < lam) (c : ℝ) (hc : |c| ≤ 2 * lam ^ q) :
    ∃ θ : ℝ, chamCoef p q lam * ((Real.cos (2 * Real.pi * (q : ℝ) * θ) : ℝ) : ℂ) = (c : ℂ) := by
  set γ : ℝ := 2 * (-lam) ^ q * (-1 : ℝ) ^ (p * ((q : ℤ) - 1)) with hγ
  have hcr : chamCoef p q lam = ((γ : ℝ) : ℂ) := by
    rw [hγ]; exact chamCoef_eq_ofReal p q lam
  have h1 : |(-1 : ℝ) ^ (p * ((q : ℤ) - 1))| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  have h2 : |(-lam) ^ q| = lam ^ q := by
    rw [abs_pow, abs_neg, abs_of_pos hlam]
  have habs : |γ| = 2 * lam ^ q := by
    rw [hγ, abs_mul, abs_mul, h1, h2, mul_one, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hγpos : 0 < |γ| := by rw [habs]; positivity
  have hγne : γ ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    have := pow_pos hlam q
    linarith
  have ht1 : |c / γ| ≤ 1 := by
    rw [abs_div, div_le_one hγpos, habs]
    exact hc
  have htmem : c / γ ∈ Set.range Real.cos := by
    rw [Real.range_cos, Set.mem_Icc]; exact abs_le.mp ht1
  obtain ⟨x, hx⟩ := htmem
  refine ⟨x / (2 * Real.pi * (q : ℝ)), ?_⟩
  have harg : 2 * Real.pi * (q : ℝ) * (x / (2 * Real.pi * (q : ℝ))) = x := by
    field_simp
  rw [harg, hx, hcr, ← Complex.ofReal_mul, Complex.ofReal_inj]
  field_simp

/-! ## The main reduction -/

theorem existsBlochMatCharpolyRoot (p : ℤ) (q : ℕ) (lam : ℝ) (hq : 1 ≤ q)
    (hpq : Nat.Coprime p.natAbs q) (hlam : 0 < lam) (E : ℝ)
    (hU : ‖(Work.TMC14Core.disc p q lam).eval (E : ℂ)‖ ≤ 2 + 2 * lam ^ q) :
    ∃ θ k : ℝ, (Work.TMC14Core.blochMat p q lam θ k).charpoly.eval (E : ℂ) = 0 := by
  -- `Δ(E)` is a real number.
  set c : ℝ := ((disc p q lam).eval (E : ℂ)).re with hcdef
  have hc : (disc p q lam).eval (E : ℂ) = (c : ℂ) := by
    apply Complex.ext
    · simp [hcdef]
    · simpa [hcdef] using disc_im_eq_zero p q lam E
  have hcle : |c| ≤ 2 + 2 * lam ^ q := by
    rw [hc] at hU
    simpa [RCLike.norm_ofReal] using hU
  -- Split `Δ(E) = s + (Δ(E) - s)` with `|s| ≤ 2` and `|Δ(E) - s| ≤ 2λ^q`.
  obtain ⟨s, hs2, hsc⟩ : ∃ s : ℝ, |s| ≤ 2 ∧ |s - c| ≤ 2 * lam ^ q := by
    refine ⟨min 2 (max (-2) c), ?_, ?_⟩
    · rw [abs_le]
      exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
    · have hle : 0 < 2 * lam ^ q := by positivity
      rcases lt_or_ge c 2 with hc2 | hc2
      · rcases lt_or_ge c (-2) with hc3 | hc3
        · have hs : min 2 (max (-2) c) = -2 := by
            rw [min_eq_right (max_le (by norm_num) (le_of_lt hc2)), max_eq_left (le_of_lt hc3)]
          rw [hs, abs_of_nonneg (by linarith : (0:ℝ) ≤ -2 - c)]
          rw [abs_of_neg (by linarith : c < 0)] at hcle
          linarith
        · have hs : min 2 (max (-2) c) = c := by
            rw [max_eq_right hc3, min_eq_right (le_of_lt hc2)]
          rw [hs, sub_self, abs_zero]; linarith
      · have hs : min 2 (max (-2) c) = 2 := by
          rw [max_eq_right (by linarith : (-2:ℝ) ≤ c), min_eq_left hc2]
        rw [hs, abs_of_nonpos (by linarith : 2 - c ≤ 0)]
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ c)] at hcle
        linarith
  -- Absorb `s` in the quasi-momentum and `Δ(E) - s` in the phase.
  obtain ⟨k, hk⟩ := exists_two_cos_eq_of_abs_le_two_aux s hs2
  obtain ⟨θ, hθ⟩ := exists_chamCoef_mul_cos_aux p q lam hq hlam (s - c) hsc
  refine ⟨θ, k, ?_⟩
  rw [Matrix.eval_charpoly]
  rw [show Matrix.scalar (Fin q) (E : ℂ) = (E : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ) from by
    ext i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases h : i = j <;> simp [h]]
  rw [blochMat_chambers p q lam θ k (E : ℂ) hpq hq, hc, hθ]
  have hk' : (2 : ℂ) * ((Real.cos (2 * Real.pi * k) : ℝ) : ℂ) = (s : ℂ) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hk
    push_cast at h
    simpa using h
  rw [hk']
  push_cast
  ring

end

end Work.TMC14Core
