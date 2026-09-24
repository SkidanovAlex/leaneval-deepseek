import Mathlib
import Submission.Work.ChenPlan.LinearSieve.FrameworkR
import Submission.Work.ChenPlan.LinearSieve.Abel.abel_sum_le
import Submission.Work.ChenPlan.LinearSieve.RIMain.abel_pointwise_defs
import Submission.Work.ChenPlan.LinearSieve.RI.tail_bound

namespace Work.ChenPlan.LinearSieve.RIMain.aux

open Finset
open scoped BigOperators

set_option autoImplicit false

theorem sum_nu_VfR_eq_range {A : BoundingSieve} {w Z : ℝ} {Φ : ℝ → ℝ} :
    (∑ p ∈ Work.ChenPlan.LinearSieve.RIMain.pSet A w Z,
        A.nu p * Work.ChenPlan.LinearSieve.VfR A (p : ℝ) * Φ (p : ℝ))
      = Work.ChenPlan.LinearSieve.VfR A Z *
        ∑ k ∈ Finset.range (Work.ChenPlan.LinearSieve.RIMain.pSet A w Z).card,
          (Work.ChenPlan.LinearSieve.RIMain.Vnorm A Z
              (Work.ChenPlan.LinearSieve.RIMain.vEnum A w Z k)
            - Work.ChenPlan.LinearSieve.RIMain.Vnorm A Z
              (Work.ChenPlan.LinearSieve.RIMain.vEnum A w Z (k + 1)))
          * Φ (Work.ChenPlan.LinearSieve.RIMain.vEnum A w Z k) := by
  classical
  let S : Finset ℕ := Work.ChenPlan.LinearSieve.RIMain.pSet A w Z
  have hSsub : ∀ p ∈ S, p ∈ A.prodPrimes.primeFactors :=
    fun p hp => (Work.ChenPlan.LinearSieve.RIMain.mem_pSet.mp hp).1
  have hSw : ∀ p ∈ S, w ≤ (p : ℝ) :=
    fun p hp => (Work.ChenPlan.LinearSieve.RIMain.mem_pSet.mp hp).2.1
  have hSZ : ∀ p ∈ S, (p : ℝ) < Z :=
    fun p hp => (Work.ChenPlan.LinearSieve.RIMain.mem_pSet.mp hp).2.2
  have hSZle : ∀ p ∈ S, (p : ℝ) ≤ Z := fun p hp => le_of_lt (hSZ p hp)
  have hPmono : Monotone (Abel.enumExt S Z) := Abel.enumExt_mono hSZle
  have hE_leZ : ∀ k, Abel.enumExt S Z k ≤ Z := Abel.enumExt_le_Z hSZ
  have hVZne : VfR A Z ≠ 0 := ne_of_gt (VfR_pos A Z)
  let e : Fin S.card → ℕ := fun i => (((S.orderIsoOfFin rfl) i : ↥S) : ℕ)
  have hE_apply : ∀ i : Fin S.card, Abel.enumExt S Z (i : ℕ) = ((e i : ℕ) : ℝ) :=
    fun i => Abel.enumExt_apply i.isLt
  -- The pointwise identity: the k-th jump of `VfR` times `VfR Z` is `ν p_k · VfR p_k`.
  have hterm : ∀ i : Fin S.card,
      A.nu (e i) * VfR A ((e i : ℕ) : ℝ) * Φ ((e i : ℕ) : ℝ)
        = VfR A Z * ((Vnorm A Z (Abel.enumExt S Z (i : ℕ))
              - Vnorm A Z (Abel.enumExt S Z ((i : ℕ) + 1)))
            * Φ (Abel.enumExt S Z (i : ℕ))) := by
    intro i
    have hle : Abel.enumExt S Z (i : ℕ) ≤ Abel.enumExt S Z ((i : ℕ) + 1) :=
      hPmono (Nat.le_succ _)
    have hdiff := Work.ChenPlan.LinearSieve.RI.sum_nu_VfR_eq A hle
    have hfil : A.prodPrimes.primeFactors.filter
        (fun q : ℕ => Abel.enumExt S Z (i : ℕ) ≤ (q : ℝ)
          ∧ (q : ℝ) < Abel.enumExt S Z ((i : ℕ) + 1)) = {e i} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hqT, hpq, hqlt⟩
        rw [hE_apply i] at hpq
        have hviS : e i ∈ S := ((S.orderIsoOfFin rfl) i).2
        have hqS : q ∈ S := Work.ChenPlan.LinearSieve.RIMain.mem_pSet.mpr
          ⟨hqT, le_trans (hSw _ hviS) hpq, lt_of_lt_of_le hqlt (hE_leZ ((i : ℕ) + 1))⟩
        have h1 : q ≤ e i := Abel.enumExt_le_enum i hqS hqlt
        exact le_antisymm h1 (by exact_mod_cast hpq)
      · intro hq
        subst hq
        refine ⟨hSsub _ ((S.orderIsoOfFin rfl) i).2, ?_, ?_⟩
        · rw [hE_apply i]
        · exact Abel.enumExt_lt_succ hSZ i
    have hVsub : VfR A (Abel.enumExt S Z (i : ℕ)) - VfR A (Abel.enumExt S Z ((i : ℕ) + 1))
        = A.nu (e i) * VfR A ((e i : ℕ) : ℝ) := by
      rw [← hdiff, hfil, Finset.sum_singleton]
    have hVsub' : VfR A ((e i : ℕ) : ℝ) - VfR A (Abel.enumExt S Z ((i : ℕ) + 1))
        = A.nu (e i) * VfR A ((e i : ℕ) : ℝ) := by
      have h := hVsub
      rw [hE_apply i] at h
      exact h
    rw [hE_apply i, Vnorm, Vnorm, ← sub_div, hVsub']
    field_simp
  -- Reindex the sieve sum by the increasing enumeration.
  let g₀ : ℕ → ℝ := fun p => A.nu p * VfR A (p : ℝ) * Φ (p : ℝ)
  let ff : ℕ → ℝ := fun k => (Vnorm A Z (Abel.enumExt S Z k)
      - Vnorm A Z (Abel.enumExt S Z (k + 1))) * Φ (Abel.enumExt S Z k)
  change (∑ p ∈ S, g₀ p) = VfR A Z * ∑ k ∈ Finset.range S.card, ff k
  have h2 : (∑ p : ↥S, g₀ (p : ℕ)) = ∑ i : Fin S.card, g₀ (e i) :=
    (Equiv.sum_comp (S.orderIsoOfFin rfl).toEquiv (fun p : ↥S => g₀ (p : ℕ))).symm
  have h3 : (∑ i : Fin S.card, g₀ (e i)) = ∑ i : Fin S.card, VfR A Z * ff (i : ℕ) :=
    Finset.sum_congr rfl (fun i _ => hterm i)
  have h4 : (∑ i : Fin S.card, VfR A Z * ff (i : ℕ))
      = VfR A Z * ∑ i : Fin S.card, ff (i : ℕ) := by
    rw [Finset.mul_sum]
  have h5 : (∑ i : Fin S.card, ff (i : ℕ)) = ∑ k ∈ Finset.range S.card, ff k :=
    Fin.sum_univ_eq_sum_range ff S.card
  rw [← Finset.sum_coe_sort S g₀, h2, h3, h4, h5]

end Work.ChenPlan.LinearSieve.RIMain.aux
