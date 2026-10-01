import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count
import Submission.Work.LinnikAreas.A5.LFunction_disc_zeroCount

open DirichletCharacter

namespace Work.ZeroFreeTables.P9

/-- For a *primitive* character `χ` of level `q`, the multiplicity `zeroMult χ u` — defined as
the vanishing order of the completed L-function of the primitive character inducing `χ` —
coincides with the vanishing order of the completed L-function of `χ` itself: for primitive `χ`
the induced primitive character is `χ` itself, up to the canonical change of level
`χ.conductor = q`, and `completedLFunction` is insensitive to that change of level. -/
private theorem zeroMult_eq_analyticOrderNatAt_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (u : ℂ) :
    Work.LinnikContract.zeroMult χ u =
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u := by
  have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc : χ.conductor = q := hprim
  -- `completedLFunction` is insensitive to the level of a character
  have key : ∀ {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) (ψ : DirichletCharacter ℂ n) (s : ℂ),
      DirichletCharacter.completedLFunction (N := n) ψ s =
        DirichletCharacter.completedLFunction (N := m) (changeLevel (dvd_of_eq h) ψ) s := by
    intro n m _ _ h ψ s
    cases h
    rw [Subsingleton.elim (dvd_of_eq rfl) (dvd_refl n), changeLevel_self]
  have hχψ : changeLevel (dvd_of_eq hc) χ.primitiveCharacter = χ := by
    rw [Subsingleton.elim (dvd_of_eq hc) χ.conductor_dvd_level, changeLevel_primitiveCharacter]
  have hfun : (DirichletCharacter.completedLFunction (N := χ.conductor) χ.primitiveCharacter)
      = (DirichletCharacter.completedLFunction χ) := by
    funext s
    rw [key hc χ.primitiveCharacter s, hχψ]
  unfold Work.LinnikContract.zeroMult
  exact congrArg (fun f : ℂ → ℂ => analyticOrderNatAt f u) hfun

theorem zeroSum_invSq_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
        ≤ C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by
  -- Uniform (in `χ`, `N`) zero count of `Λ(·,χ) = completedLFunction χ` in an arbitrary disk.
  obtain ⟨c, hcpos, hc⟩ := Work.LinnikAreas.A5.ball_zeroCount_uniformL_A5
  -- The dyadic inverse-square estimate turns a ball count into a bound for the Poisson-kernel
  -- zero sum, with counting parameter `q = log N`.
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.ownRepelNW.orderSum_invSq_bound_of_count hcpos.le
  refine ⟨C, hCpos, fun s => ?_⟩
  have hlogN : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast NeZero.one_le
    exact Real.log_nonneg hN1
  have hΛan : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    fun z _ => (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  -- finite-set bounds for the kernel attached to `completedLFunction χ`
  have hfin : ∀ S : Finset ℂ,
      ∑ u ∈ S, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2))
        ≤ C * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := by
    intro S
    refine hC (DirichletCharacter.completedLFunction χ) hΛan (Real.log (N : ℝ)) hlogN ?_ s S
    intro a ρ hρ
    exact hc χ hχ hprim a ρ hρ
  -- rewrite `zeroMult` as the vanishing order of `Λ(·,χ)`
  have hcongr : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
      = ∑' u : ℂ, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2)) :=
    tsum_congr (fun u => by rw [zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u])
  rw [hcongr]
  have hnn : ∀ u : ℂ, (0 : ℝ) ≤
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2)) := by
    intro u
    have h1 : (0 : ℝ) ≤ 1 / (1 + ‖s - u‖ ^ 2) := by positivity
    positivity
  have hsumm : Summable (fun u : ℂ =>
      (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
        (1 / (1 + ‖s - u‖ ^ 2))) := summable_of_sum_le hnn hfin
  calc (∑' u : ℂ, (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) u : ℝ) *
          (1 / (1 + ‖s - u‖ ^ 2)))
      ≤ C * (Real.log (2 + ‖s‖) + Real.log (N : ℝ) + 2) := hsumm.tsum_le_of_sum_le hfin
    _ = C * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := by ring

end Work.ZeroFreeTables.P9
