import Mathlib
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.OffAxis.Defs

namespace Work.ZeroFreeTables.OffAxis

open scoped Classical BigOperators

/-- A finite sum of nonnegative values over an arbitrary `Finset` is at most the `finsum`
(which sums over the support of `f`).  Used to compare the "number of distinct zeros in `S`"
with the multiplicity-weighted zero count. -/
lemma finset_sum_le_finsum_of_nonneg {α : Type*} {f : α → ℝ} (hnn : ∀ x, 0 ≤ f x)
    (hfin : Function.HasFiniteSupport f) (s : Finset α) :
    ∑ x ∈ s, f x ≤ ∑ᶠ x, f x := by
  classical
  have hsub : Function.support f ⊆ ↑hfin.toFinset := by
    intro x hx
    exact (Set.Finite.mem_toFinset hfin).mpr hx
  rw [finsum_eq_finsetSum_of_support_subset f hsub]
  have h1 : ∑ x ∈ s, f x ≤ ∑ x ∈ s ∪ hfin.toFinset, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun i _ _ => hnn i)
  have h2 : ∑ x ∈ s ∪ hfin.toFinset, f x = ∑ x ∈ hfin.toFinset, f x := by
    symm
    refine Finset.sum_subset Finset.subset_union_right (fun x hx hxnot => ?_)
    exact Function.notMem_support.mp (fun hc => hxnot ((Set.Finite.mem_toFinset hfin).mpr hc))
  linarith

theorem card_le_famCount {q : ℕ} [NeZero q] (σ T : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ∃ χ : DirichletCharacter ℂ q,
      Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T) :
    (S.card : ℝ) ≤ Work.ZeroDensity.famCount q σ T := by
  classical
  let g : DirichletCharacter ℂ q → ℂ → ℝ :=
    fun χ u => if σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T
      then (Work.LinnikContract.zeroMult χ u : ℝ) else 0
  have hg_nonneg : ∀ χ u, 0 ≤ g χ u := by
    intro χ u
    simp only [g]
    split_ifs <;> simp
  have hg_supp : ∀ χ, Function.HasFiniteSupport (g χ) := by
    intro χ
    refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ T).subset ?_
    intro u hu
    simp only [Function.mem_support, g] at hu
    have hc : σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T := by
      by_contra hcon
      exact hu (if_neg hcon)
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := by
      have hz : (Work.LinnikContract.zeroMult χ u : ℝ) ≠ 0 := by
        rwa [if_pos hc] at hu
      exact_mod_cast hz
    exact ⟨hzm, hc.1, hc.2.1, hc.2.2⟩
  have hP1 : ∀ χ : DirichletCharacter ℂ q, ∑ u ∈ S, g χ u ≤ ∑ᶠ u, g χ u :=
    fun χ => finset_sum_le_finsum_of_nonneg (hg_nonneg χ) (hg_supp χ) S
  have hP2 : ∀ u ∈ S, (1 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ q, g χ u := by
    intro u hu
    obtain ⟨χ, hzm, hσ, hre, him⟩ := hS u hu
    have hval : g χ u = (Work.LinnikContract.zeroMult χ u : ℝ) := by
      simp only [g]
      rw [if_pos ⟨hσ, hre, him⟩]
    have hge1 : (1 : ℝ) ≤ g χ u := by
      rw [hval]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzm
    exact hge1.trans (Finset.single_le_sum (fun i _ => hg_nonneg i u) (Finset.mem_univ χ))
  have hmain : (S.card : ℝ) ≤ ∑ χ : DirichletCharacter ℂ q, ∑ᶠ u, g χ u := by
    calc (S.card : ℝ) = ∑ u ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ u ∈ S, ∑ χ : DirichletCharacter ℂ q, g χ u := Finset.sum_le_sum hP2
      _ = ∑ χ : DirichletCharacter ℂ q, ∑ u ∈ S, g χ u := Finset.sum_comm
      _ ≤ ∑ χ : DirichletCharacter ℂ q, ∑ᶠ u, g χ u :=
          Finset.sum_le_sum (fun χ _ => hP1 χ)
  simpa only [g, Work.ZeroDensity.famCount, Work.ZeroDensity.zCount,
    Work.LinnikAreas.zeroCountIn] using hmain

end Work.ZeroFreeTables.OffAxis
