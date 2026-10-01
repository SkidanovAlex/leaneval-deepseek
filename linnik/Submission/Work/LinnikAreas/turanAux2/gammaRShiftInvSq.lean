import Mathlib
import Submission.Work.LinnikAreas.TuranOther.orderInvGammaR_eq_indicator
import Submission.Work.LinnikAreas.turanAux2.gammaROrderShift
import Submission.Work.LinnikAreas.turanAux2.invSqShiftSeriesLe

namespace Work.LinnikAreas.turanAux2

open Complex

/-- The comparison series `∑ 1/(3/2 + 2n)^2` converges (a shifted `p`-series with `p = 2`). -/
lemma summable_invSq_two_shift : Summable (fun n : ℕ => (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)
  have hbase : Summable (fun n : ℕ => (1:ℝ)/(((n+1 : ℕ):ℝ))^2) :=
    h.comp_injective Nat.succ_injective
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2 := fun n => by positivity
  have hle : ∀ n : ℕ, (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2 ≤ (1:ℝ)/(((n+1 : ℕ):ℝ))^2 := by
    intro n
    apply one_div_le_one_div_of_le
    · positivity
    · have h1 : ((n:ℝ)+1) ≤ (3/2:ℝ) + 2*(n:ℝ) := by
        have h0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      have h2 : (0:ℝ) ≤ (n:ℝ)+1 := by positivity
      have h3 := pow_le_pow_left₀ h2 h1 2
      push_cast
      linarith [h3]
  exact Summable.of_nonneg_of_le hnn hle hbase

/-- The map `n ↦ -(a + 2n)` is injective. -/
lemma phi_injective (a : ℕ) : Function.Injective (fun n : ℕ => -(((a + 2*n:ℕ):ℂ))) := by
  intro m n h
  have h1 : (((a + 2*m:ℕ):ℂ)) = (((a+2*n:ℕ):ℂ)) := neg_inj.mp h
  have h2 : (a + 2*m : ℕ) = (a + 2*n : ℕ) := by exact_mod_cast h1
  omega

theorem gammaRShiftInvSq :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ) (w : ℂ), (3 / 2 : ℝ) ≤ w.re →
      Summable (fun u : ℂ =>
          (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u : ℝ) / ‖w - u‖ ^ 2) ∧
        (∑' u : ℂ,
          (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a : ℂ)))⁻¹) u : ℝ) / ‖w - u‖ ^ 2)
          ≤ C := by
  classical
  refine ⟨∑' n : ℕ, (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2 + 1, ?_, ?_⟩
  · -- positivity of the constant
    have hg := summable_invSq_two_shift
    have h0 : (1:ℝ)/((3/2:ℝ)+2*((0:ℕ):ℝ))^2 ≤ ∑' n : ℕ, (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2 :=
      hg.le_tsum 0 (fun j hj => by positivity)
    have h00 : (1:ℝ)/((3/2:ℝ)+2*((0:ℕ):ℝ))^2 = 4/9 := by norm_num
    linarith
  · intro a w hw
    have hg : Summable (fun n : ℕ => (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2) := summable_invSq_two_shift
    obtain ⟨-, hptw, -⟩ := invSqShiftSeriesLe a w hw
    -- the zero set of `(Γ_ℝ(·+a))⁻¹` is `{-(a+2n)}`
    let phi : ℕ → ℂ := fun n => -(((a + 2*n:ℕ):ℂ))
    have hinj : Function.Injective phi := phi_injective a
    have hone : ∀ n : ℕ,
        analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) (phi n) = 1 := by
      intro n
      rw [gammaROrderShift a (phi n)]
      exact Set.indicator_of_mem (show phi n ∈ Set.range phi from ⟨n, rfl⟩) (fun _ => (1:ℕ))
    -- pointwise domination of the reindexed series by the comparison series
    have hpt : ∀ n : ℕ,
        (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) (phi n) : ℝ)/‖w - phi n‖^2
          ≤ (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2 := by
      intro n
      rw [hone n, Nat.cast_one]
      exact hptw n
    have hcomp : Summable (fun n : ℕ =>
        (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) (phi n) : ℝ)/‖w - phi n‖^2) :=
      Summable.of_nonneg_of_le
        (g := fun n => (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) (phi n) : ℝ)/‖w - phi n‖^2)
        (f := fun n : ℕ => (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2)
        (fun n => by positivity) hpt hg
    -- the summand vanishes off `Set.range phi`
    have hsupp : ∀ u : ℂ, u ∉ Set.range phi →
        (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) u : ℝ)/‖w-u‖^2 = 0 := by
      intro u hu
      have hzero : analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) u = 0 := by
        rw [gammaROrderShift a u, Set.indicator_of_notMem hu]
      simp [hzero]
    have hsumm : Summable (fun u : ℂ =>
        (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) u : ℝ)/‖w-u‖^2) :=
      (Function.Injective.summable_iff hinj hsupp).mp hcomp
    refine ⟨hsumm, ?_⟩
    have hs' : Function.support (fun u : ℂ =>
        (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) u : ℝ)/‖w-u‖^2) ⊆ Set.range phi := by
      intro u hu
      by_contra h
      exact hu (hsupp u h)
    have htsum_eq : (∑' u : ℂ,
        (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) u : ℝ)/‖w-u‖^2)
        = ∑' n : ℕ, (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) (phi n) : ℝ)/‖w - phi n‖^2 :=
      (Function.Injective.tsum_eq hinj hs').symm
    rw [htsum_eq]
    calc ∑' n : ℕ, (analyticOrderNatAt (fun z : ℂ => (Complex.Gammaℝ (z + (a:ℂ)))⁻¹) (phi n) : ℝ)/‖w - phi n‖^2
        ≤ ∑' n : ℕ, (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2 := Summable.tsum_le_tsum hpt hcomp hg
      _ ≤ ∑' n : ℕ, (1:ℝ)/((3/2:ℝ)+2*(n:ℝ))^2 + 1 := by linarith

end Work.LinnikAreas.turanAux2
