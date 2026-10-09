import Mathlib
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.shafarevich_existence
import Submission.Work.SSGRoute.no_two_torsion_fixingSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # `Work.SSGRoute.step4_x_exists`, proved through Shafarevich's existence theorem

`Work.SSGRoute.step4_x_exists` (`Submission/Work/SSGRoute/step4_x_exists.lean`) produces, from the
coker-side data `D` and the datum `y` (SW's Second Shrinking), a class `x` satisfying the clauses of
Shafarevich's Existence Theorem (SW Theorem 13) for `y`.

Its statement is *exactly* the conclusion of `Work.SSGRoute.shafarevich_existence` with
`k := ℚ`, `Ω := ℚ̄`, `Λ := D.Λ`, `E := E p (K ≃ₐ[ℚ] K) n i j`, `S := D.S`, `sec := D.sec` — clause by
clause (the "split" clause of `step4_x_exists` and of `shafarevich_existence` carry the same
hypothesis `IsSplitIn ℚ K A`, under which the sums agree).  The proof below is therefore a single
instantiation; the `y` = 0 approach in the sibling file (which needs the corestriction of `y` to
vanish on *every* place of `S` splitting in `K`, a statement that is *not* available from
`Step4YData` at the places of `Tnew`) is bypassed.

This module imports only `Step4CokerData`, `shafarevich_existence` and
`no_two_torsion_fixingSubgroup`, so it builds independently of the Step-4 lane. -/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **`step4_x_exists`, through `SSGRoute.shafarevich_existence`.** -/
theorem step4_x_exists_proved (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) (D : Work.SSGRoute.Step4CokerData p K n i j)
    (y : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j)
    (hY : Work.SSGRoute.Step4YData p K n i j D y) :
    ∃ x : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j,
      SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) ⊤ x ∧
      SSGRoute.IsLocConstOn ⊤ x ∧
      (∀ A ∈ D.S, SSGRoute.IsSplitIn ℚ K A →
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A)
          (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((D.sec s)⁻¹ * δ * D.sec s))) ∧
      (∀ A ∈ D.S, ¬ SSGRoute.IsSplitIn ℚ K A →
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x) ∧
      (∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (Subgroup.zpowers c) x) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
        (∀ A ∈ D.S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ D.Λ B →
        ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
        (∀ A ∈ D.S, ¬ SSGRoute.IsConjPlace ℚ A B) →
        ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
          (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ SSGRoute.decomp ℚ B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ B ⊓ V) x) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hμ' := hμ
  -- a primitive `p`-th root of unity in `K`, obtained from the primitive `p^{i+1}`-st one
  obtain ⟨ζ, hζK, hζi⟩ := hμ
  have hdiv : p ^ i ∣ p ^ (i + 1) := by
    rw [pow_succ]; exact dvd_mul_right _ _
  have hζ : IsPrimitiveRoot (ζ ^ (p ^ i)) p := by
    have h := hζi.pow_of_dvd (p := p ^ i) (pow_ne_zero _ hp0) hdiv
    have hk : p ^ (i + 1) / p ^ i = p := by
      rw [pow_succ]
      exact Nat.mul_div_right p (pow_pos (Nat.pos_of_ne_zero hp0) i)
    rwa [hk] at h
  have hζK' : ζ ^ (p ^ i) ∈ K := pow_mem hζK (p ^ i)
  haveI hGalK : IsGalois ℚ K := IsGalois.mk
  haveI hΛfd : FiniteDimensional ℚ D.Λ := D.fdΛ
  haveI hΛgal : IsGalois ℚ D.Λ := D.galΛ
  haveI hEfin : Finite (E p (K ≃ₐ[ℚ] K) n i j) :=
    Work.CohomologicalShrinking.flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) n i j
  haveI hSMCE := Work.CohomologicalShrinking.instSMulCommClassRefinedQuotient
    (G := K ≃ₐ[ℚ] K) (P := Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) n) p i j
  -- `G_ℚ` has no involution fixing `K` (it is totally imaginary of level `(i,j)`, `i ≥ 1`),
  -- so `y` kills the involutions of `G_K`
  have hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0 := by
    intro c hc hc2
    rw [no_two_torsion_fixingSubgroup p K i (le_trans hj hji) hμ' c hc2 hc]
    have h := hY.1 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  exact Work.SSGRoute.shafarevich_existence (p := p) (k := ℚ) (Ω := SSGRoute.QBar)
    (K := K) (Λ := D.Λ) (hKΛ := D.hKΛ) (ζ := ζ ^ (p ^ i)) (hζ := hζ) (hζK := hζK')
    (E := E p (K ≃ₐ[ℚ] K) n i j) (S := D.S) (hSfin := D.hSfin) (hSdisj := D.hSdisj)
    (hSram := D.hSram) (y := y) (hy := hY.1) (hyc := hY.2.1) (hyS := hY.2.2.1)
    (hyT := hY.2.2.2.1) (hy0 := hY.2.2.2.2.1) (hyinf := hyinf) (sec := D.sec)
    (hsec := D.hsec)

end Work.SSGRoute
