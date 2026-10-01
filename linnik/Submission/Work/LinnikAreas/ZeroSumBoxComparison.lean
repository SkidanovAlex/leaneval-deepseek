import Mathlib
import Submission.Work.LinnikAreas.CIDeps
import Submission.Work.LinnikAreas.norm_Hk_le
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall
import Submission.Work.LinnikAreas.norm_tsum_sub_finsum_indicator_le
import Submission.Work.LinnikAreas.summable_zeroMult_norm_mul
import Submission.Work.LinnikAreas.finite_inBox_zeroMult

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators Classical

noncomputable section

/-- **Comparison of the full zero sum with the box sum (Heath-Brown §13).**

For a non-principal character `χ` of level `q` and `R > 0`, the ball-restricted zero sums

`ρ ↦ Σ_{‖u‖ ≤ ρ} ord_Λ(u) · Hk(11/2, 3/10, (1-u) log q)`

(where `Λ = completedLFunction χ.primitiveCharacter`) converge as `ρ → ∞` to a limit `Z` (the
full zero sum, absolutely convergent), and the distance of this limit to the box sum
`boxSum q (11/2) (3/10) R χ` is at most the mass `farSum q (11/2) (3/10) R χ` of the zeros
outside the box. -/
theorem ZeroSumBoxComparison {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    [NeZero χ.conductor] {R : ℝ} (hR : 0 < R) :
    ∃ Z : ℂ,
      (Filter.Tendsto (fun ρ : ℝ => ∑ᶠ u : ℂ,
          ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 ρ)) u : ℤ) : ℂ) *
            Work.LinnikContract.Hk (11/2) (3/10) ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ))))
        Filter.atTop (nhds Z))
      ∧ ‖Z - Work.LinnikContract.boxSum q (11/2) (3/10) R χ‖
          ≤ Work.LinnikAreas.farSum q (11/2) (3/10) R χ := by
  classical
  -- `q ≥ 2`, so `log q > 0`
  have hq : 2 ≤ q := by
    have hc1 : χ.conductor ≠ 1 := fun h => hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h)
    have hc0 : χ.conductor ≠ 0 := DirichletCharacter.conductor_ne_zero χ
    have hdvd : χ.conductor ∣ q := DirichletCharacter.conductor_dvd_level χ
    have h2 : 2 ≤ χ.conductor := by omega
    have hle : χ.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) hdvd
    omega
  have hlogq : 0 < Real.log (q : ℝ) := by
    apply Real.log_pos
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  -- the primitive character inducing `χ` is non-principal
  have hχprim_ne : χ.primitiveCharacter ≠ 1 := by
    intro h
    have h1 : DirichletCharacter.conductor χ.primitiveCharacter = 1 := by
      rw [h, DirichletCharacter.conductor_one]
    have h2 : χ.conductor = 1 := by
      rw [← (DirichletCharacter.isPrimitive_def (χ := χ.primitiveCharacter)).mp
        χ.primitiveCharacter_isPrimitive]
      exact h1
    exact hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h2)
  set Φ : ℂ → ℂ := fun u => Work.LinnikContract.Hk (11/2) (3/10)
      ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)) with hΦdef
  set κ : ℂ → ℂ := fun u =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℂ) with hκdef
  have hΛdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter) :=
    DirichletCharacter.differentiable_completedLFunction hχprim_ne
  have hdivuniv : ∀ u : ℂ, MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter) Set.univ u
      = (analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℤ) :=
    fun u => Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast
      (fun z _ => hΛdiff.analyticAt z) (Set.mem_univ u)
  have hApos : 0 < 16 / (Real.log (q : ℝ)) ^ 2 := div_pos (by norm_num) (pow_pos hlogq 2)
  -- the inverse-square decay of the kernel on the critical strip
  have hΦbound : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ →
      ‖Φ u‖ ≤ (16 / (Real.log (q : ℝ)) ^ 2) / ‖u‖ ^ 2 := by
    intro u h1 h2 h3
    rw [hΦdef]
    exact norm_Hk_le (by norm_num) (by norm_num) hlogq h1 h2 h3
  -- summability of the full zero sum
  have hsumm_div : Summable (fun u : ℂ =>
      (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        Set.univ) u : ℤ) : ℂ) * Φ u) :=
    (Commons.NumberTheory.DirichletCharacter.divisorSum_summable_and_tendsto
      (χ.primitiveCharacter) hχprim_ne χ.primitiveCharacter_isPrimitive
      (Φ := Φ) (A := 16 / (Real.log (q : ℝ)) ^ 2) hApos hΦbound).1
  -- the ball sums converge to the full zero sum
  have hball0 := tendsto_finsum_divisor_closedBall (χ.primitiveCharacter) hχprim_ne hsumm_div
  -- absolute summability of the full zero sum
  have hsumm_abs : Summable (fun u : ℂ => ‖κ u * Φ u‖) := by
    have h := summable_zeroMult_norm_mul (χ.primitiveCharacter) hχprim_ne
      χ.primitiveCharacter_isPrimitive (Φ := Φ) (A := 16 / (Real.log (q : ℝ)) ^ 2) hApos hΦbound
    refine h.congr (fun u => ?_)
    rw [hκdef]
    simp
  -- finiteness of the box part
  have hboxfin : Function.HasFiniteSupport
      (fun u : ℂ => if Work.LinnikContract.InBox q R u then κ u * Φ u else 0) := by
    have hset := finite_inBox_zeroMult χ hχ (R := R) hR
    refine hset.subset ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_cases hIn : Work.LinnikContract.InBox q R u
    · rw [if_pos hIn] at hu
      refine ⟨hIn, ?_⟩
      have hk : κ u ≠ 0 := fun h0 => hu (by rw [h0, zero_mul])
      intro hz
      apply hk
      rw [hκdef]
      simpa [Work.LinnikContract.zeroMult] using hz
    · rw [if_neg hIn] at hu
      exact absurd rfl hu
  -- the triangle inequality for the tail
  have hkey := norm_tsum_sub_finsum_indicator_le (κ := κ) (Φ := Φ)
      (S := fun u => Work.LinnikContract.InBox q R u) hsumm_abs hboxfin
  -- identify `boxSum` and `farSum` with the corresponding summand
  have hbox_eq : Work.LinnikContract.boxSum q (11/2) (3/10) R χ
      = ∑ᶠ u : ℂ, if Work.LinnikContract.InBox q R u then κ u * Φ u else 0 := by
    unfold Work.LinnikContract.boxSum
    refine finsum_congr (fun u => ?_)
    by_cases hIn : Work.LinnikContract.InBox q R u
    · rw [if_pos hIn, if_pos hIn, hκdef, hΦdef]
      simp [Work.LinnikContract.zeroMult]
    · rw [if_neg hIn, if_neg hIn]
  have hfar_eq : Work.LinnikAreas.farSum q (11/2) (3/10) R χ
      = ∑' u : ℂ, if Work.LinnikContract.InBox q R u then 0 else ‖κ u * Φ u‖ := by
    unfold Work.LinnikAreas.farSum
    refine tsum_congr (fun u => ?_)
    by_cases hIn : Work.LinnikContract.InBox q R u
    · rw [if_pos hIn, if_pos hIn]
    · rw [if_neg hIn, if_neg hIn, hκdef, hΦdef]
      simp [Work.LinnikContract.zeroMult]
  refine ⟨∑' u : ℂ, κ u * Φ u, ?_, ?_⟩
  · have hlim : (∑' u : ℂ, (((MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ.primitiveCharacter) Set.univ) u : ℤ) : ℂ) * Φ u)
        = ∑' u : ℂ, κ u * Φ u := by
      refine tsum_congr (fun u => ?_)
      rw [hdivuniv u, hκdef]
      norm_cast
    rw [hlim] at hball0
    simpa [hΦdef] using hball0
  · rw [hbox_eq, hfar_eq]
    exact hkey

end

end Work.LinnikAreas
