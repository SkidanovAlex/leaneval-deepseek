import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP2.mon_lip
import Submission.Work.HP.HP2.sum_abs_le_sqrt_card_mul
import Submission.Work.HP.tau_basic

namespace Work.HP.HP2

open Finset

/-! ## Lipschitz bound for degree-`d` forms on the unit ball

The single ingredient is the monomial bound `Work.HP.HP2.mon_lip` at `R = 1`, summed over the
monomial basis with Cauchy--Schwarz in both the coefficient vector `a` and the displacement
`u - v`.
-/

lemma eNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v := Real.sqrt_nonneg _

/-- Per-monomial Lipschitz bound on the unit ball: with `‖u‖, ‖v‖ ≤ 1`,
`|ν(u)_m - ν(v)_m| ≤ d · Σᵢ |uᵢ - vᵢ|`.  This is `Work.HP.HP2.mon_lip` with `s = univ`, `R = 1`
and `μ = m.1`; the factor `Σᵢ μᵢ` is `d` because `m` is a degree-`d` exponent vector. -/
lemma veronese_lip_unit (d n : ℕ) (m : Mon d n) (u v : Fin (n + 1) → ℝ)
    (hu : rNorm u ≤ 1) (hv : rNorm v ≤ 1) :
    |veronese d n u m - veronese d n v m| ≤ (d : ℝ) * ∑ i, |u i - v i| := by
  have hu' : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), |u i| ≤ (1 : ℝ) :=
    fun i _ => le_trans (abs_apply_le_rNorm u i) hu
  have hv' : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))), |v i| ≤ (1 : ℝ) :=
    fun i _ => le_trans (abs_apply_le_rNorm v i) hv
  have h := mon_lip (Finset.univ : Finset (Fin (n + 1))) u v (fun i => (m.1 i : ℕ)) 1
    le_rfl hu' hv'
  have hsum : ((∑ i ∈ (Finset.univ : Finset (Fin (n + 1))), (m.1 i : ℕ)) : ℝ) = (d : ℝ) := by
    exact_mod_cast m.2
  rw [hsum, one_pow, mul_one] at h
  simpa only [veronese] using h

/-- Lipschitz bound for the form `Q(x) = formEvalR d n (toR a) x` on the unit ball of `ℝ^{n+1}`.
Route: expand `Q(u) = Σ_μ (a_μ) * u^μ` and apply `Work.HP.HP2.mon_lip` with `s = univ`, `R = 1`,
`μ = fun i => (m.1 i : ℕ)`, giving `|ν(u)_m - ν(v)_m| ≤ d * Σ_i |u_i - v_i|` (the factor `Σ_i μ_i`
is `d` by `m.2`); `|u_i| ≤ 1` follows from `Work.HP.abs_apply_le_rNorm`. Then use
`Σ_μ |a_μ| ≤ √(Fintype.card (Mon d n)) * eNorm a` and `Σ_i |u_i - v_i| ≤ √(n+1) * rNorm (u - v)`
(both Cauchy–Schwarz). -/
theorem cone_lip (d n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Mon d n → ℤ) (u v : Fin (n + 1) → ℝ),
      rNorm u ≤ 1 → rNorm v ≤ 1 →
      |formEvalR d n (toR a) u - formEvalR d n (toR a) v| ≤ C * eNorm a * rNorm (u - v) := by
  refine ⟨max 1 (Real.sqrt (Fintype.card (Mon d n)) * (d : ℝ) * Real.sqrt (n + 1)),
    lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro a u v hu hv
  set S : ℝ := ∑ i : Fin (n + 1), |u i - v i| with hSdef
  set T : ℝ := ∑ m : Mon d n, |(a m : ℝ)| with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; exact Finset.sum_nonneg fun m _ => abs_nonneg _
  have hS0 : 0 ≤ S := by rw [hSdef]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
  have hA0 : 0 ≤ Real.sqrt (Fintype.card (Mon d n)) * eNorm a :=
    mul_nonneg (Real.sqrt_nonneg _) (eNorm_nonneg' a)
  -- (1) expand the difference over the monomial basis
  have hsub : formEvalR d n (toR a) u - formEvalR d n (toR a) v
      = ∑ m : Mon d n, (a m : ℝ) * (veronese d n u m - veronese d n v m) := by
    rw [formEvalR, formEvalR, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [toR]
    ring
  -- (2) term-by-term Lipschitz bound, with `Σ_i μ_i = d`
  have hmon : ∀ m : Mon d n,
      |veronese d n u m - veronese d n v m| ≤ (d : ℝ) * S := by
    intro m
    rw [hSdef]
    exact veronese_lip_unit d n m u v hu hv
  have hstep : |formEvalR d n (toR a) u - formEvalR d n (toR a) v| ≤ T * ((d : ℝ) * S) := by
    rw [hsub]
    calc |∑ m : Mon d n, (a m : ℝ) * (veronese d n u m - veronese d n v m)|
        ≤ ∑ m : Mon d n, |(a m : ℝ) * (veronese d n u m - veronese d n v m)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ m : Mon d n, |(a m : ℝ)| * |veronese d n u m - veronese d n v m| := by
          exact Finset.sum_congr rfl fun m _ => abs_mul _ _
      _ ≤ ∑ m : Mon d n, |(a m : ℝ)| * ((d : ℝ) * S) :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hmon m) (abs_nonneg _)
      _ = T * ((d : ℝ) * S) := by rw [hTdef, Finset.sum_mul]
  -- (3) Cauchy--Schwarz for the coefficients
  have hcs_a : T ≤ Real.sqrt (Fintype.card (Mon d n)) * eNorm a := by
    rw [hTdef]
    have h := sum_abs_le_sqrt_card_mul (toR a)
    have hcoef : (∑ i, |toR a i|) = ∑ m : Mon d n, |(a m : ℝ)| :=
      Finset.sum_congr rfl fun m _ => by simp [toR]
    rw [hcoef] at h
    rwa [show rNorm (toR a) = eNorm a from rfl] at h
  -- (4) Cauchy--Schwarz for the displacement
  have hcs_S : S ≤ Real.sqrt (n + 1) * rNorm (u - v) := by
    rw [hSdef]
    have h := sum_abs_le_sqrt_card_mul (u - v)
    have hcard : ((Fintype.card (Fin (n + 1)) : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
    rw [hcard] at h
    simpa [Pi.sub_apply] using h
  -- (5) assemble
  have hbound : T * ((d : ℝ) * S) ≤
      (Real.sqrt (Fintype.card (Mon d n)) * (d : ℝ) * Real.sqrt (n + 1)) * eNorm a
        * rNorm (u - v) := by
    have hS' : (d : ℝ) * S ≤ (d : ℝ) * (Real.sqrt (n + 1) * rNorm (u - v)) :=
      mul_le_mul_of_nonneg_left hcs_S (Nat.cast_nonneg d)
    have hS0' : 0 ≤ (d : ℝ) * S := mul_nonneg (Nat.cast_nonneg d) hS0
    have hprod := mul_le_mul hcs_a hS' hS0' hA0
    calc T * ((d : ℝ) * S)
          ≤ (Real.sqrt (Fintype.card (Mon d n)) * eNorm a)
              * ((d : ℝ) * (Real.sqrt (n + 1) * rNorm (u - v))) := hprod
        _ = (Real.sqrt (Fintype.card (Mon d n)) * (d : ℝ) * Real.sqrt (n + 1)) * eNorm a
              * rNorm (u - v) := by ring
  calc |formEvalR d n (toR a) u - formEvalR d n (toR a) v|
      ≤ (Real.sqrt (Fintype.card (Mon d n)) * (d : ℝ) * Real.sqrt (n + 1)) * eNorm a
          * rNorm (u - v) := le_trans hstep hbound
    _ ≤ max 1 (Real.sqrt (Fintype.card (Mon d n)) * (d : ℝ) * Real.sqrt (n + 1)) * eNorm a
          * rNorm (u - v) := by
        apply mul_le_mul_of_nonneg_right _ (rNorm_nonneg _)
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (eNorm_nonneg' a)

end Work.HP.HP2
