import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseB7.Estimates
import Submission.Work.BoseB7.bp_cauchy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped BigOperators

namespace Work.BoseFixR

/-- Linearity of the Fock form in its first argument, for a finite linear
combination `∑_{i ∈ s} c_i • u_i`. -/
private lemma bp_sum_smul_left {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (F : Work.BoseB7.FockData Mode) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (u : ι → F.H) (f : F.H) :
    F.bp (∑ i ∈ s, c i • u i) f = ∑ i ∈ s, c i * F.bp (u i) f := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-- **Triangle inequality / Cauchy–Schwarz for the Fock form against a linear
combination**: the sesquilinear form `⟨·,·⟩ = F.bp` is positive semidefinite, so
`g ↦ √(F.bp g g)` behaves like a seminorm.  Hence for `g = ∑_{i ∈ s} c_i • u_i`,

  `|⟨g, f⟩| ≤ (∑_{i ∈ s} |c_i| √⟨u_i, u_i⟩) · √⟨f, f⟩`.

The proof is the classical one: Cauchy–Schwarz gives `|⟨g, f⟩| ≤ ‖g‖·‖f‖`, and
the expansion `⟨g, g⟩ = ∑_i c_i ⟨u_i, g⟩` together with Cauchy–Schwarz on each
term gives `⟨g, g⟩ ≤ (∑_i |c_i| √⟨u_i, u_i⟩) · √⟨g, g⟩`, i.e. `‖g‖ ≤
∑_i |c_i| √⟨u_i, u_i⟩`. -/
theorem absBpSumSmulLe {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (u : ι → F.H) (f : F.H) :
    |F.bp (∑ i ∈ s, c i • u i) f|
      ≤ (∑ i ∈ s, |c i| * Real.sqrt (F.bp (u i) (u i))) * Real.sqrt (F.normSq f) := by
  set S : ℝ := ∑ i ∈ s, |c i| * Real.sqrt (F.bp (u i) (u i)) with hS
  set T : ℝ := F.bp (∑ i ∈ s, c i • u i) (∑ i ∈ s, c i • u i) with hT
  have hSnonneg : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  -- Cauchy–Schwarz on the pair `(∑ c_i • u_i, f)`
  have hcs := Work.BoseB7.bp_cauchy_abs F (∑ i ∈ s, c i • u i) f
  rw [← hT] at hcs
  -- the seminorm bound `√T ≤ S`
  have hT_le : T ≤ S * Real.sqrt T := by
    have hexp : T = ∑ i ∈ s, c i * F.bp (u i) (∑ j ∈ s, c j • u j) := by
      rw [hT]; exact bp_sum_smul_left F s c u _
    calc T = ∑ i ∈ s, c i * F.bp (u i) (∑ j ∈ s, c j • u j) := hexp
      _ ≤ |∑ i ∈ s, c i * F.bp (u i) (∑ j ∈ s, c j • u j)| := le_abs_self _
      _ ≤ ∑ i ∈ s, |c i * F.bp (u i) (∑ j ∈ s, c j • u j)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ s, |c i| * |F.bp (u i) (∑ j ∈ s, c j • u j)| := by
            apply Finset.sum_congr rfl; intro i hi; rw [abs_mul]
      _ ≤ ∑ i ∈ s, |c i| * (Real.sqrt (F.bp (u i) (u i)) * Real.sqrt T) := by
            apply Finset.sum_le_sum; intro i hi
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            have h := Work.BoseB7.bp_cauchy_abs F (u i) (∑ j ∈ s, c j • u j)
            rwa [← hT] at h
      _ = S * Real.sqrt T := by
            rw [hS, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro i hi; ring
  have hts : Real.sqrt T ≤ S := by
    have hT0 : 0 ≤ T := by rw [hT]; exact F.bp_nonneg _
    have e : (Real.sqrt T)^2 = T := Real.sq_sqrt hT0
    have h1 : (Real.sqrt T)^2 ≤ S * Real.sqrt T := by linarith
    have h2 : Real.sqrt T * (Real.sqrt T - S) ≤ 0 := by nlinarith [h1]
    rcases mul_nonpos_iff.mp h2 with ⟨h, _⟩ | ⟨_, h⟩
    · have := Real.sqrt_nonneg T; linarith
    · linarith
  calc |F.bp (∑ i ∈ s, c i • u i) f| ≤ Real.sqrt T * Real.sqrt (F.bp f f) := hcs
    _ ≤ S * Real.sqrt (F.bp f f) := mul_le_mul_of_nonneg_right hts (Real.sqrt_nonneg _)
    _ = S * Real.sqrt (F.normSq f) := by rw [Work.BoseB7.FockData.normSq]

end Work.BoseFixR
