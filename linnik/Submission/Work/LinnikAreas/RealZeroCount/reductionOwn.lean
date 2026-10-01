import Mathlib
import Submission.Work.LinnikAreas.RealZeroCount.Defs
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas.ReductionOwn

/-- Fallback (owned) proof of the real-zero count reduction: the multiplicity-weighted number of
real zeros with `λ ≤ t` is at most `3δ` times the divisor-weighted Hadamard kernel sum over the
unit ball, `δ = t / log q`. -/
theorem realZeroCountFinsum_le' {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {t : ℝ} (ht : 0 < t) :
    Work.LinnikAreas.realZeroCountFinsum q χ t
      ≤ 3 * (t / Real.log (q : ℝ))
        * Work.LinnikAreas.divisorKernelFinsum q χ (1 + 2 * (t / Real.log (q : ℝ))) := by
  classical
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter ≠ 1 := by
    intro h1
    exact hχ (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1,
      DirichletCharacter.changeLevel_one χ.conductor_dvd_level])
  have hψprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  set δ : ℝ := t / Real.log (q : ℝ) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos ht hlogq
  set σ₁ : ℝ := 1 + 2 * δ with hσdef
  have hσ1 : 1 ≤ σ₁ := by rw [hσdef]; linarith
  set f : ℝ → ℝ := fun β : ℝ => if Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
      Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t
    then (Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) else 0 with hfdef
  set DK : ℂ → ℝ := fun u : ℂ => (((MeromorphicOn.divisor
      (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0 : ℂ) 1)) u : ℤ) : ℝ) * Work.LinnikAreas.realKernel σ₁ u
    with hDKdef
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (Metric.closedBall (0 : ℂ) 1) := fun z _ =>
    (DirichletCharacter.differentiable_completedLFunction hψ).analyticAt z
  -- the box in which the counted zeros lie is finite
  have hBoxfin : ({u : ℂ | Work.LinnikContract.zeroMult χ u ≠ 0 ∧ 1 - δ ≤ u.re ∧ u.re ≤ 1 ∧
      |u.im| ≤ 1} : Set ℂ).Finite := boxMaxZeroAux.finite_zeroMult_box χ (1 - δ) 1
  have hstrip : ∀ β : ℝ, Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
      Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t → (0 : ℝ) < β ∧ β < 1 ∧ 1 - β ≤ δ := by
    intro β hc
    obtain ⟨hzm, hlam⟩ := hc
    obtain ⟨hβ0, hβ1, -⟩ := OtherCharRepel.zeroMultStripPos hq hχ hzm
    have hβ0' : (0 : ℝ) < β := by simpa using hβ0
    have hβ1' : β < 1 := by simpa using hβ1
    have hlam' : (1 - β) * Real.log (q : ℝ) ≤ t := by
      simpa [Work.LinnikContract.lamOf] using hlam
    have h1βδ : 1 - β ≤ δ := by
      rw [hδdef]; exact (le_div_iff₀ hlogq).mpr hlam'
    exact ⟨hβ0', hβ1', h1βδ⟩
  have hsub : Function.support f ⊆ Complex.re '' {u : ℂ | Work.LinnikContract.zeroMult χ u ≠ 0 ∧
      1 - δ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 1} := by
    intro β hβ
    rw [Function.mem_support] at hβ
    have hc : Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
        Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t := by
      by_contra h
      exact hβ (by rw [hfdef]; exact if_neg h)
    obtain ⟨hβ0, hβ1, hδ1⟩ := hstrip β hc
    refine ⟨(β : ℂ), ⟨hc.1, ?_, ?_, ?_⟩, ?_⟩
    · simp only [Complex.ofReal_re]; linarith
    · simp only [Complex.ofReal_re]; linarith
    · simp
    · simp
  have hsuppfin : (Function.support f).Finite := hBoxfin.image Complex.re |>.subset hsub
  -- pointwise preparation on the support
  have hprep : ∀ β ∈ hsuppfin.toFinset,
      Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧ f β =
        (Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) ∧
      DK (β : ℂ) = (Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) * realKernel σ₁ (β : ℂ) := by
    intro β hβS
    have hβsupp : f β ≠ 0 := Function.mem_support.mp ((hsuppfin.mem_toFinset).mp hβS)
    have hc : Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
        Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t := by
      by_contra h
      exact hβsupp (by rw [hfdef]; exact if_neg h)
    refine ⟨hc.1, by rw [hfdef]; exact if_pos hc, ?_⟩
    obtain ⟨hβ0, hβ1, -⟩ := hstrip β hc
    have hmemB : (β : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hβ0]
      linarith
    have hdivβ : (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction
        χ.primitiveCharacter) (Metric.closedBall (0 : ℂ) 1)) ((β : ℂ)) : ℤ) : ℝ) =
        (Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) := by
      rw [Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmemB]
      simp [Work.LinnikContract.zeroMult]
    simp only [hDKdef]
    rw [hdivβ]
  -- the kernel is at least `1/(3δ)` on the counted zeros
  have hker : ∀ β : ℝ, (0 : ℝ) < β → β < 1 → 1 - β ≤ δ → 1 / (3 * δ) ≤ realKernel σ₁ (β : ℂ) := by
    intro β hβ0 hβ1 h1βδ
    rw [Work.LinnikAreas.realKernel_ofReal]
    have hpos : 0 < σ₁ - β := by rw [hσdef]; linarith
    have hle : σ₁ - β ≤ 3 * δ := by rw [hσdef]; linarith
    have h1 : 1 / (3 * δ) ≤ 1 / (σ₁ - β) := one_div_le_one_div_of_le hpos hle
    have h2 : 0 ≤ 1 / (1 + β) := by
      apply div_nonneg one_pos.le; linarith
    linarith
  -- pointwise bound
  have hpoint : ∀ β ∈ hsuppfin.toFinset, f β ≤ 3 * δ * DK (β : ℂ) := by
    intro β hβS
    obtain ⟨hzm, hfβ, hDKβ⟩ := hprep β hβS
    have hc : Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
        Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t := by
      by_contra h
      exact (Function.mem_support.mp ((hsuppfin.mem_toFinset).mp hβS)) (by rw [hfdef]; exact if_neg h)
    obtain ⟨hβ0, hβ1, hδ1⟩ := hstrip β hc
    have hkey := mul_le_mul_of_nonneg_left (hker β hβ0 hβ1 hδ1)
      (Nat.cast_nonneg (Work.LinnikContract.zeroMult χ ((β : ℂ))))
    calc f β = (Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) := hfβ
      _ = 3 * δ * ((Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) * (1 / (3 * δ))) := by
            field_simp
      _ ≤ 3 * δ * ((Work.LinnikContract.zeroMult χ ((β : ℂ)) : ℝ) * realKernel σ₁ (β : ℂ)) := by
            apply mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 3 * δ * DK (β : ℂ) := by rw [hDKβ]
  -- nonnegativity of the divisor summand, and finiteness of its support
  have hDnn : ∀ u : ℂ, 0 ≤ DK u := by
    intro u
    by_cases hu0 : MeromorphicOn.divisor (DirichletCharacter.completedLFunction
        χ.primitiveCharacter) (Metric.closedBall (0 : ℂ) 1) u = 0
    · simp [hDKdef, hu0]
    · have huB : u ∈ Metric.closedBall (0 : ℂ) 1 := by
        by_contra h
        exact hu0 (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h)
      have hdivu : MeromorphicOn.divisor (DirichletCharacter.completedLFunction
          χ.primitiveCharacter) (Metric.closedBall (0 : ℂ) 1) u =
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) u : ℤ) :=
        Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han huB
      have hord : analyticOrderNatAt (DirichletCharacter.completedLFunction
          χ.primitiveCharacter) u ≠ 0 := by
        intro h0
        exact hu0 (by rw [hdivu, h0]; rfl)
      have hzero : DirichletCharacter.completedLFunction χ.primitiveCharacter u = 0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
      have hstripu := Commons.NumberTheory.Linnik.completedL_zero_strip
        χ.primitiveCharacter hψ hψprim hzero
      have hdnn : (0 : ℝ) ≤ ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction
          χ.primitiveCharacter) (Metric.closedBall (0 : ℂ) 1) u : ℤ) : ℝ) := by
        rw [hdivu]
        simp
      have hKnn : 0 ≤ realKernel σ₁ u := by
        rw [realKernel]
        have h1 : 0 < σ₁ - u.re := by linarith [hstripu.2, hσ1]
        have h2 : 0 < 1 + u.re := by linarith [hstripu.1]
        have hd1 : 0 < (σ₁ - u.re) ^ 2 + u.im ^ 2 := by
          nlinarith [sq_nonneg u.im, mul_pos h1 h1]
        have hd2 : 0 < (1 + u.re) ^ 2 + u.im ^ 2 := by
          nlinarith [sq_nonneg u.im, mul_pos h2 h2]
        exact add_nonneg (div_nonneg h1.le hd1.le) (div_nonneg h2.le hd2.le)
      simp only [hDKdef]
      exact mul_nonneg hdnn hKnn
  have hDKfin : (Function.support DK).Finite := by
    refine (MeromorphicOn.divisor_support_finite_of_subset
      (f := DirichletCharacter.completedLFunction χ.primitiveCharacter)
      (U := Metric.closedBall (0 : ℂ) 1) (V := Metric.closedBall (0 : ℂ) 1)
      han.meromorphicOn (isCompact_closedBall (0 : ℂ) 1) (le_refl _)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h0
    exact hu (by simp [hDKdef, h0])
  -- assemble
  have hsumle : ∑ᶠ β : ℝ, f β ≤ 3 * δ * ∑ᶠ u : ℂ, DK u := by
    rw [finsum_eq_sum_of_support_subset f (s := hsuppfin.toFinset)
      (by rw [Set.Finite.coe_toFinset])]
    have h1 : ∑ β ∈ hsuppfin.toFinset, f β ≤ ∑ β ∈ hsuppfin.toFinset, 3 * δ * DK (β : ℂ) :=
      Finset.sum_le_sum hpoint
    have h2 : ∑ β ∈ hsuppfin.toFinset, 3 * δ * DK (β : ℂ)
        = 3 * δ * ∑ β ∈ hsuppfin.toFinset, DK (β : ℂ) := by
      rw [Finset.mul_sum]
    have hinj : Set.InjOn (fun β : ℝ => (β : ℂ)) (↑hsuppfin.toFinset) := by
      intro x _ y _ hxy
      exact Complex.ofReal_injective hxy
    have h3 : ∑ u ∈ hsuppfin.toFinset.image (fun β : ℝ => (β : ℂ)), DK u
        = ∑ β ∈ hsuppfin.toFinset, DK (β : ℂ) := Finset.sum_image hinj
    have h4 : ∑ u ∈ hsuppfin.toFinset.image (fun β : ℝ => (β : ℂ)), DK u
        ≤ ∑ u ∈ hDKfin.toFinset, DK u := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro u hu
        rw [hDKfin.mem_toFinset, Function.mem_support]
        obtain ⟨β, hβS, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨hzm, -, hDKβ⟩ := hprep β hβS
        have hc : Work.LinnikContract.zeroMult χ ((β : ℂ)) ≠ 0 ∧
            Work.LinnikContract.lamOf q ((β : ℂ)) ≤ t := by
          by_contra h
          exact (Function.mem_support.mp ((hsuppfin.mem_toFinset).mp hβS))
            (by rw [hfdef]; exact if_neg h)
        obtain ⟨hβ0, hβ1, hδ1⟩ := hstrip β hc
        have hkpos : 0 < realKernel σ₁ (β : ℂ) :=
          lt_of_lt_of_le (by positivity) (hker β hβ0 hβ1 hδ1)
        rw [hDKβ]
        exact mul_ne_zero (by exact_mod_cast hzm) (ne_of_gt hkpos)
      · intro u _ _
        exact hDnn u
    have h5 : ∑ u ∈ hDKfin.toFinset, DK u = ∑ᶠ u : ℂ, DK u :=
      (finsum_eq_sum_of_support_subset DK (s := hDKfin.toFinset)
        (by rw [Set.Finite.coe_toFinset])).symm
    have hδnn : 0 ≤ 3 * δ := by linarith
    calc ∑ β ∈ hsuppfin.toFinset, f β
        ≤ 3 * δ * (∑ β ∈ hsuppfin.toFinset, DK (β : ℂ)) := by rw [← h2]; exact h1
      _ ≤ 3 * δ * (∑ u ∈ hDKfin.toFinset, DK u) :=
            mul_le_mul_of_nonneg_left (by rw [← h3]; exact h4) hδnn
      _ = 3 * δ * (∑ᶠ u : ℂ, DK u) := by rw [h5]
  have hfeq : Work.LinnikAreas.realZeroCountFinsum q χ t = ∑ᶠ β : ℝ, f β := by
    rw [Work.LinnikAreas.realZeroCountFinsum]
  have hgoal : Work.LinnikAreas.realZeroCountFinsum q χ t
      ≤ 3 * δ * Work.LinnikAreas.divisorKernelFinsum q χ σ₁ := by
    rw [hfeq]
    refine le_trans hsumle ?_
    have h6 : ∑ᶠ u : ℂ, DK u = ∑ᶠ u : ℂ, (((MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall (0 : ℂ) 1)) u : ℤ) : ℝ) * realKernel σ₁ u :=
      finsum_congr (fun u => by rw [hDKdef])
    rw [h6, Work.LinnikAreas.divisorKernelFinsum]
  simpa only [hδdef, hσdef] using hgoal

end Work.LinnikAreas.ReductionOwn
