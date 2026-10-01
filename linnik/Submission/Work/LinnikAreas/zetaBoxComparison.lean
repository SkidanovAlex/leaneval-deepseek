import Mathlib
import Submission.Work.LinnikAreas.ZetaPrincipalDefs
import Submission.Work.LinnikAreas.ZetaDev
import Submission.Work.LinnikAreas.norm_tsum_sub_finsum_indicator_le
import Submission.Work.LinnikAreas.zetaZeroSumInvSq
import Submission.Work.LinnikAreas.zetaOrder_eq_xiF
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
import Submission.Work.LinnikAreas.finite_inBox_xiF
import Submission.Work.LinnikAreas.zetaZeroSum_summable_of_count

open DirichletCharacter Complex Filter Metric
open scoped BigOperators Classical Topology
noncomputable section

namespace Work.LinnikAreas

theorem zetaBoxComparison :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q], ∀ R : ℝ, 1 ≤ R →
      ∃ Z : ℂ,
        (Filter.Tendsto (fun ρ : ℝ => Work.LinnikAreas.zetaBallSum q ρ) Filter.atTop (nhds Z)) ∧
        ‖Z + (3/10 : ℝ)^2 - Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q)‖
          ≤ Work.LinnikAreas.farSumP q R + C * (q : ℝ) ^ (-(49:ℝ)/10) := by
  refine ⟨100, by norm_num, ?_⟩
  intro q hq _ R hR
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  -- `zeroMult` of the principal character coincides with `zetaMult`
  have hcoef : ∀ u : ℂ, zetaMult u = Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) u := by
    intro u
    show analyticOrderNatAt Commons.NumberTheory.Zeta.XiPF.xiF u = _
    rw [zetaDev_zeroMult_one_eq, zetaOrder_eq_xiF]
  -- summability of the `Hk`-weighted zero sum
  have hBsumm : Summable (fun u : ℂ => (zetaMult u : ℂ) * zetaHk q u) := by
    obtain ⟨C₀, -, hcount⟩ := zetaZeroSumInvSq
    exact zetaZeroSum_summable_of_count q hq (C := C₀) hcount
  -- the two sums agree off the poles `0`, `1`
  have hAB : ∀ u : ℂ, u ≠ 0 → u ≠ 1 → zetaA q u = zetaB q u := by
    intro u hu0 hu1
    simp only [zetaA_apply, zetaB_apply]
    have hκ : ((MeromorphicOn.divisor completedRiemannZeta Set.univ u : ℤ) : ℂ) = (zetaMult u : ℂ) := by
      have hana : AnalyticAt ℂ completedRiemannZeta u := by
        have hU : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} :=
          (isOpen_compl_singleton (x := (0:ℂ))).inter (isOpen_compl_singleton (x := (1:ℂ)))
        have hd : DifferentiableOn ℂ completedRiemannZeta {z : ℂ | z ≠ 0 ∧ z ≠ 1} :=
          fun z hz => (differentiableAt_completedZeta hz.1 hz.2).differentiableWithinAt
        exact hd.analyticOnNhd hU u ⟨hu0, hu1⟩
      have hdiv : MeromorphicOn.divisor completedRiemannZeta Set.univ u
          = (analyticOrderNatAt completedRiemannZeta u : ℤ) := by
        rw [MeromorphicOn.divisor_apply meromorphicOn_completedRiemannZeta (Set.mem_univ u),
          hana.meromorphicOrderAt_eq]
        rcases eq_or_ne (analyticOrderAt completedRiemannZeta u) ⊤ with h | h
        · rw [h]; simp [analyticOrderNatAt, h]
        · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
          have h2 : analyticOrderNatAt completedRiemannZeta u = n := by
            rw [analyticOrderNatAt, ← hn]; simp
          rw [h2, ← hn]; simp
      have hdiv' : MeromorphicOn.divisor completedRiemannZeta Set.univ u = (zetaMult u : ℤ) := by
        rw [hdiv]
        exact congrArg (fun n : ℕ => (n : ℤ)) (zetaOrder_eq_xiF u)
      rw [hdiv']
      exact Int.cast_natCast (zetaMult u)
    have hΦ : zetaTent q u = zetaHk q u := by
      rw [zetaTent_apply, zetaHk_apply]
      exact (Hk_eq_tentK (z := (1 - u) * (Real.log (q : ℝ) : ℂ)) (by
        refine mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu1)) ?_
        exact Complex.ofReal_ne_zero.mpr hlogq.ne')).symm
    rw [hκ, hΦ]
  have hDfin : Function.HasFiniteSupport (fun u : ℂ => zetaA q u - zetaB q u) := by
    refine (Set.Finite.insert 0 (Set.finite_singleton 1)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hcon
    push_neg at hcon
    exact hu (by rw [hAB u hcon.1 hcon.2, sub_self])
  have hsummD : Summable (fun u : ℂ => zetaA q u - zetaB q u) := summable_of_hasFiniteSupport hDfin
  have hsummA : Summable (zetaA q) := by
    have h : Summable (fun u : ℂ => zetaB q u + (zetaA q u - zetaB q u)) := hBsumm.add hsummD
    exact h.congr (fun u => by ring)
  have hZeq : (∑' u : ℂ, zetaA q u) = (∑' u : ℂ, zetaB q u) + (∑' u : ℂ, (zetaA q u - zetaB q u)) := by
    rw [← Summable.tsum_add hBsumm hsummD]
    exact tsum_congr (fun u => by ring)
  have hsubsupp : Function.support (fun u : ℂ => zetaA q u - zetaB q u) ⊆ ({0, 1} : Finset ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hcon
    push_neg at hcon
    exact hu (by rw [hAB u hcon.1 hcon.2, sub_self])
  have hDval : (∑' u : ℂ, (zetaA q u - zetaB q u))
      = (zetaA q 0 - zetaB q 0) + (zetaA q 1 - zetaB q 1) := by
    rw [tsum_eq_finsum (f := fun u : ℂ => zetaA q u - zetaB q u)
        (L := SummationFilter.unconditional ℂ) hDfin,
      finsum_eq_sum_of_support_subset _ hsubsupp]
    rw [Finset.sum_insert (show (0:ℂ) ∉ ({(1:ℂ)} : Finset ℂ) by simp), Finset.sum_singleton]
  have hz0 : zetaMult 0 = 0 := by
    have h : analyticOrderAt Commons.NumberTheory.Zeta.XiPF.xiF 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr Commons.NumberTheory.Zeta.XiPF.xiF_zero_ne)
    simp [zetaMult, analyticOrderNatAt, h]
  have hz1 : zetaMult 1 = 0 := by
    have hne : Commons.NumberTheory.Zeta.XiPF.xiF 1 ≠ 0 := by
      rw [show Commons.NumberTheory.Zeta.XiPF.xiF 1 = (1/2 : ℂ) by
        rw [Commons.NumberTheory.Zeta.XiPF.xiF]; norm_num]
      norm_num
    have h : analyticOrderAt Commons.NumberTheory.Zeta.XiPF.xiF 1 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hne)
    simp [zetaMult, analyticOrderNatAt, h]
  have ht0 : zetaTent q 0 = zetaHk q 0 := by
    rw [zetaTent_apply, zetaHk_apply,
      show (1 - 0 : ℂ) * (Real.log (q : ℝ) : ℂ) = (Real.log (q : ℝ) : ℂ) by ring]
    exact (Hk_eq_tentK (z := (Real.log (q : ℝ) : ℂ))
      (Complex.ofReal_ne_zero.mpr hlogq.ne')).symm
  have ht1 : zetaTent q 1 = (3/10 : ℝ)^2 := by
    rw [zetaTent_apply, show (1 - 1 : ℂ) * (Real.log (q : ℝ) : ℂ) = 0 by ring,
      tentK_zero (11/2) (3/10)]
  have hA0 : zetaA q 0 - zetaB q 0 = - zetaHk q 0 := by
    rw [zetaA_apply, zetaB_apply, divisor_univ_completedRiemannZeta_zero, hz0, ht0]
    simp only [zetaHk_apply, sub_zero, one_mul]
    ring_nf
  have hA1 : zetaA q 1 - zetaB q 1 = - (3/10 : ℝ)^2 := by
    rw [zetaA_apply, zetaB_apply, divisor_univ_completedRiemannZeta_one, hz1, ht1]
    ring_nf
  have hbox : (∑ᶠ u : ℂ, if Work.LinnikContract.InBox q R u then zetaB q u else 0)
      = Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q) := by
    simp only [Work.LinnikContract.boxSum]
    refine finsum_congr (fun u => ?_)
    simp only [zetaB_apply, zetaHk_apply]
    by_cases hIn : Work.LinnikContract.InBox q R u
    · rw [if_pos hIn, if_pos hIn]
      congr 1
      exact congrArg (fun n : ℕ => (n : ℂ)) (hcoef u)
    · rw [if_neg hIn, if_neg hIn]
  have hfarP : (∑' u : ℂ, if Work.LinnikContract.InBox q R u then 0 else ‖zetaB q u‖)
      = Work.LinnikAreas.farSumP q R := by
    simp only [Work.LinnikAreas.farSumP]
    refine tsum_congr (fun u => ?_)
    simp only [zetaB_apply, zetaHk_apply]
    by_cases hIn : Work.LinnikContract.InBox q R u
    · rw [if_pos hIn, if_pos hIn]
    · rw [if_neg hIn, if_neg hIn]
      rw [norm_mul, Complex.norm_natCast, hcoef u]
  have hfin : Function.HasFiniteSupport
      (fun u : ℂ => if Work.LinnikContract.InBox q R u then zetaB q u else 0) := by
    refine (finite_inBox_xiF q hq hRpos).subset ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_cases hIn : Work.LinnikContract.InBox q R u
    · rw [if_pos hIn] at hu
      refine ⟨hIn, ?_⟩
      intro hz
      exact hu (by rw [zetaB_apply, show zetaMult u = 0 from hz]; simp)
    · rw [if_neg hIn] at hu
      exact absurd rfl hu
  have hab : Summable (fun u : ℂ => ‖zetaB q u * 1‖) := by simpa using hBsumm.norm
  have hfin' : Function.HasFiniteSupport
      (fun u : ℂ => if Work.LinnikContract.InBox q R u then zetaB q u * 1 else 0) := by
    simpa using hfin
  have hfar : ‖(∑' u : ℂ, zetaB q u)
        - Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q)‖
      ≤ Work.LinnikAreas.farSumP q R := by
    have h := norm_tsum_sub_finsum_indicator_le (κ := zetaB q) (Φ := fun _ : ℂ => (1:ℂ))
      (S := fun u : ℂ => Work.LinnikContract.InBox q R u) hab hfin'
    simp only [mul_one] at h
    rw [hbox, hfarP] at h
    exact h
  refine ⟨∑' u : ℂ, zetaA q u, ?_, ?_⟩
  · have hsummA' : Summable (fun u : ℂ =>
        ((MeromorphicOn.divisor completedRiemannZeta Set.univ u : ℤ) : ℂ) * zetaTent q u) :=
      hsummA
    have ht := tendsto_finsum_divisor_closedBall_mero (f := completedRiemannZeta)
      meromorphicOn_completedRiemannZeta (Φ := zetaTent q) hsummA'
    simpa only [zetaBallSum] using ht
  · have hkey : (∑' u : ℂ, zetaA q u) + (3/10 : ℝ)^2
          - Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q)
        = ((∑' u : ℂ, zetaB q u)
            - Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q))
          - zetaHk q 0 := by
      rw [hZeq, hDval, hA0, hA1]
      ring_nf
    rw [hkey]
    calc ‖((∑' u : ℂ, zetaB q u)
            - Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q))
          - zetaHk q 0‖
        ≤ ‖(∑' u : ℂ, zetaB q u)
            - Work.LinnikContract.boxSum q (11/2) (3/10) R (1 : DirichletCharacter ℂ q)‖
            + ‖zetaHk q 0‖ := norm_sub_le _ _
      _ ≤ Work.LinnikAreas.farSumP q R + 100 * (q : ℝ) ^ (-(49:ℝ)/10) := by
          refine add_le_add hfar ?_
          simpa only [zetaHk_apply, sub_zero, one_mul] using norm_Hk_logq_le q hq

end Work.LinnikAreas
