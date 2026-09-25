import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2
import Submission.Work.BourgainPlan.IonescuWainger.indicator_sigmaStrataFinset_incl_excl
import Submission.Work.BourgainPlan.IonescuWainger.sigmaStrataQ_sum_ne_zero

open Finset MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-! ## Elementary torsion-subgroup calculus on the circle

The strata `Σ_A = sigmaStrataFinset A` live inside the torsion subgroups `Σ_{⊆ B} = 𝕋[Q_B]`
(`sigmaSubAFinset B`).  For the counting argument of Tao's `ortho-apply`(ii) we need to know that a
point of a stratum is *detected* by the co-atoms of `S`, exactly as in the `ZMod` picture of
`cluster_strata_l2_bound.lean`. -/

/-- A point of `Σ_{⊆ B}` is killed by `Q_B`. -/
lemma nsmul_QA_eq_zero_of_mem_sigmaSubAFinset {B : Finset ℕ} (h2 : ∀ q ∈ B, 2 ≤ q)
    {x : Circle} (hx : x ∈ sigmaSubAFinset B) : (QA B) • x = 0 :=
  (addOrderOf_dvd_iff_nsmul_eq_zero).mp
    ((mem_sigmaSubAFinset_iff_dvd_addOrderOf h2 x).mp hx)

/-- A point killed by `Q_B` lies in `Σ_{⊆ B}`. -/
lemma mem_sigmaSubAFinset_of_nsmul_eq_zero {B : Finset ℕ} (h2 : ∀ q ∈ B, 2 ≤ q)
    {x : Circle} (hx : (QA B) • x = 0) : x ∈ sigmaSubAFinset B :=
  (mem_sigmaSubAFinset_iff_dvd_addOrderOf h2 x).mpr
    ((addOrderOf_dvd_iff_nsmul_eq_zero).mpr hx)

/-- `Σ_{⊆ B}` is a subgroup: it is closed under subtraction. -/
lemma sub_mem_sigmaSubAFinset {B : Finset ℕ} (h2 : ∀ q ∈ B, 2 ≤ q)
    {x y : Circle} (hx : x ∈ sigmaSubAFinset B) (hy : y ∈ sigmaSubAFinset B) :
    x - y ∈ sigmaSubAFinset B :=
  mem_sigmaSubAFinset_of_nsmul_eq_zero h2 (by
    rw [smul_sub, nsmul_QA_eq_zero_of_mem_sigmaSubAFinset h2 hx,
      nsmul_QA_eq_zero_of_mem_sigmaSubAFinset h2 hy, sub_zero])

/-- **A stratum point is detected by its co-atoms.**  If `q ∈ A ⊆ S` and `x ∈ Σ_A`, then
`x ∉ 𝕋[Q_{S ∖ {q}}]`.

Indeed `x ∈ 𝕋[Q_A]`, so if also `x ∈ 𝕋[Q_{S∖{q}}]` then the additive order of `x` divides
`gcd (Q_A) (Q_{S∖{q}}) = Q_{A ∩ (S∖{q})} = Q_{A∖{q}}`, contradicting the stratum condition for the
proper subset `A ∖ {q} ⊊ A`. -/
lemma strata_nsmul_sdiff_ne_zero {S A : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ r ∈ S, p ≠ r → Nat.Coprime p r)
    (hA : A ⊆ S) {x : Circle} (hx : x ∈ sigmaStrataFinset A) {q : ℕ} (hq : q ∈ A) :
    (QA (S \ {q})) • x ≠ 0 := by
  intro h0
  have hxA : x ∈ sigmaSubAFinset A := (mem_sigmaStrataFinset.mp hx).1
  have h2A : ∀ r ∈ A, 2 ≤ r := fun r hr => h2 r (hA hr)
  have hd1 : addOrderOf x ∣ QA A := (mem_sigmaSubAFinset_iff_dvd_addOrderOf h2A x).mp hxA
  have hd2 : addOrderOf x ∣ QA (S \ {q}) := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr h0
  have hgcd : Nat.gcd (QA A) (QA (S \ {q})) = QA (A ∩ (S \ {q})) :=
    gcd_QA_inter_of_coprime
      (fun p hp r hr hpr => hS p (hA hp) r (Finset.mem_sdiff.mp hr).1 hpr)
  have hB : A ∩ (S \ {q}) = A \ {q} := by
    ext r
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨hrA, -, hrq⟩; exact ⟨hrA, hrq⟩
    · rintro ⟨hrA, hrq⟩; exact ⟨hrA, hA hrA, hrq⟩
  have hd3 : addOrderOf x ∣ QA (A \ {q}) := by
    have h := Nat.dvd_gcd hd1 hd2
    rwa [hgcd, hB] at h
  have hAne : A \ {q} ≠ A := by
    intro h
    have h1 : q ∈ A \ {q} := by rw [h]; exact hq
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_singleton_self q)
  have hsub : x ∈ sigmaSubAFinset (A \ {q}) :=
    (mem_sigmaSubAFinset_iff_dvd_addOrderOf
      (fun r hr => h2 r (hA (Finset.mem_sdiff.mp hr).1)) x).mpr hd3
  exact not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset Finset.sdiff_subset hAne hsub hx

/-- **The strata add**: for disjoint `A₀, A₁ ⊆ S`, `Σ_{A₀} + Σ_{A₁} ⊆ Σ_{A₀ ∪ A₁}`. -/
theorem circle_strata_add_mem {S A₀ A₁ : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ r ∈ S, p ≠ r → Nat.Coprime p r)
    (hA₀ : A₀ ⊆ S) (hA₁ : A₁ ⊆ S) (hdisj : Disjoint A₀ A₁)
    {x y : Circle} (hx : x ∈ sigmaStrataFinset A₀) (hy : y ∈ sigmaStrataFinset A₁) :
    x + y ∈ sigmaStrataFinset (A₀ ∪ A₁) := by
  rw [mem_sigmaStrataFinset]
  have hxA : x ∈ sigmaSubAFinset A₀ := (mem_sigmaStrataFinset.mp hx).1
  have hyA : y ∈ sigmaSubAFinset A₁ := (mem_sigmaStrataFinset.mp hy).1
  have h2U : ∀ q ∈ A₀ ∪ A₁, 2 ≤ q := fun q hq =>
    (Finset.mem_union.mp hq).elim (fun h => h2 q (hA₀ h)) (fun h => h2 q (hA₁ h))
  constructor
  · rw [mem_sigmaSubAFinset_iff_dvd_addOrderOf h2U (x + y), QA_union hdisj]
    refine (addOrderOf_dvd_iff_nsmul_eq_zero).mpr ?_
    have hx0 : (QA A₀) • x = 0 := nsmul_QA_eq_zero_of_mem_sigmaSubAFinset
      (fun q hq => h2 q (hA₀ hq)) hxA
    have hy0 : (QA A₁) • y = 0 := nsmul_QA_eq_zero_of_mem_sigmaSubAFinset
      (fun q hq => h2 q (hA₁ hq)) hyA
    calc (QA A₀ * QA A₁) • (x + y)
        = (QA A₀ * QA A₁) • x + (QA A₀ * QA A₁) • y := smul_add _ _ _
      _ = QA A₁ • (QA A₀ • x) + QA A₀ • (QA A₁ • y) := by
          rw [← smul_smul (QA A₀) (QA A₁) x, smul_comm (QA A₀) (QA A₁) x,
            ← smul_smul (QA A₀) (QA A₁) y]
      _ = 0 := by rw [hx0, hy0, smul_zero, smul_zero, add_zero]
  · intro B hB hxyB
    rw [Finset.mem_erase, Finset.mem_powerset] at hB
    obtain ⟨hBne, hBsub⟩ := hB
    obtain ⟨q, hqmem, hqnotB⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hBsub, hBne⟩)
    have hBsub' : B ⊆ S \ {q} := by
      intro r hr
      rw [Finset.mem_sdiff]
      refine ⟨(Finset.mem_union.mp (hBsub hr)).elim (fun h => hA₀ h) (fun h => hA₁ h), ?_⟩
      intro hrq
      exact hqnotB ((Finset.mem_singleton.mp hrq) ▸ hr)
    have h2Ss : ∀ r ∈ S \ {q}, 2 ≤ r := fun r hr => h2 r (Finset.mem_sdiff.mp hr).1
    have hxyS : x + y ∈ sigmaSubAFinset (S \ {q}) :=
      mem_sigmaSubAFinset_of_subset hBsub' h2Ss hxyB
    rcases Finset.mem_union.mp hqmem with hq0 | hq1
    · have hysub : A₁ ⊆ S \ {q} := by
        intro r hr
        rw [Finset.mem_sdiff]
        refine ⟨hA₁ hr, ?_⟩
        intro hrq
        exact Finset.disjoint_left.mp hdisj hq0 ((Finset.mem_singleton.mp hrq) ▸ hr)
      have hyS : y ∈ sigmaSubAFinset (S \ {q}) :=
        mem_sigmaSubAFinset_of_subset hysub h2Ss hyA
      have hxS : x ∈ sigmaSubAFinset (S \ {q}) := by
        have h := sub_mem_sigmaSubAFinset h2Ss hxyS hyS
        rwa [add_sub_cancel_right] at h
      exact strata_nsmul_sdiff_ne_zero h2 hS hA₀ hx hq0
        (nsmul_QA_eq_zero_of_mem_sigmaSubAFinset h2Ss hxS)
    · have hxsub : A₀ ⊆ S \ {q} := by
        intro r hr
        rw [Finset.mem_sdiff]
        refine ⟨hA₀ hr, ?_⟩
        intro hrq
        exact Finset.disjoint_left.mp hdisj hr ((Finset.mem_singleton.mp hrq) ▸ hq1)
      have hxS : x ∈ sigmaSubAFinset (S \ {q}) :=
        mem_sigmaSubAFinset_of_subset hxsub h2Ss hxA
      have hyS : y ∈ sigmaSubAFinset (S \ {q}) := by
        have h := sub_mem_sigmaSubAFinset h2Ss hxyS hxS
        rwa [add_sub_cancel_left] at h
      exact strata_nsmul_sdiff_ne_zero h2 hS hA₁ hy hq1
        (nsmul_QA_eq_zero_of_mem_sigmaSubAFinset h2Ss hyS)

/-- **The strata are disjoint**: a point of the circle lies in at most one stratum `Σ_A`, `A ⊆ S`. -/
theorem circle_strata_disjoint {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ r ∈ S, p ≠ r → Nat.Coprime p r)
    (hA : A ⊆ S) (hB : B ⊆ S) {x : Circle}
    (hxA : x ∈ sigmaStrataFinset A) (hxB : x ∈ sigmaStrataFinset B) : A = B := by
  by_contra hne
  have h2A : ∀ q ∈ A, 2 ≤ q := fun q hq => h2 q (hA hq)
  have h2B : ∀ q ∈ B, 2 ≤ q := fun q hq => h2 q (hB hq)
  have hdA : addOrderOf x ∣ QA A :=
    (mem_sigmaSubAFinset_iff_dvd_addOrderOf h2A x).mp (mem_sigmaStrataFinset.mp hxA).1
  have hdB : addOrderOf x ∣ QA B :=
    (mem_sigmaSubAFinset_iff_dvd_addOrderOf h2B x).mp (mem_sigmaStrataFinset.mp hxB).1
  have hd : addOrderOf x ∣ QA (A ∩ B) := by
    rw [← gcd_QA_inter_of_coprime (fun p hp q hq hpq => hS p (hA hp) q (hB hq) hpq)]
    exact Nat.dvd_gcd hdA hdB
  have hsub : x ∈ sigmaSubAFinset (A ∩ B) :=
    (mem_sigmaSubAFinset_iff_dvd_addOrderOf
      (fun q hq => h2 q (hA (Finset.mem_inter.mp hq).1)) x).mpr hd
  by_cases hAB : A ⊆ B
  · have hne' : A ∩ B ≠ B := by rw [Finset.inter_eq_left.mpr hAB]; exact hne
    exact not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset Finset.inter_subset_right hne' hsub hxB
  · have hne' : A ∩ B ≠ A := fun h => hAB (Finset.inter_eq_left.mp h)
    exact not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset Finset.inter_subset_left hne' hsub hxA

/-- **Uniqueness of the decomposition `Σ_{A₀} ⊕ Σ_{A₁}`.**  For disjoint `A₀, A₁ ⊆ S`, the sum
`α + γ` with `α ∈ Σ_{A₁}`, `γ ∈ Σ_{A₀}` determines `α` and `γ`. -/
lemma circle_strata_decomp_unique {S A₀ A₁ : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ r ∈ S, p ≠ r → Nat.Coprime p r)
    (hA₀ : A₀ ⊆ S) (hA₁ : A₁ ⊆ S) (hdisj : Disjoint A₀ A₁)
    {α α' γ γ' : Circle} (hα : α ∈ sigmaStrataFinset A₁) (hα' : α' ∈ sigmaStrataFinset A₁)
    (hγ : γ ∈ sigmaStrataFinset A₀) (hγ' : γ' ∈ sigmaStrataFinset A₀)
    (h : α + γ = α' + γ') : α = α' ∧ γ = γ' := by
  have h2A₀ : ∀ q ∈ A₀, 2 ≤ q := fun q hq => h2 q (hA₀ hq)
  have h2A₁ : ∀ q ∈ A₁, 2 ≤ q := fun q hq => h2 q (hA₁ hq)
  have hαS : α ∈ sigmaSubAFinset A₁ := (mem_sigmaStrataFinset.mp hα).1
  have hαS' : α' ∈ sigmaSubAFinset A₁ := (mem_sigmaStrataFinset.mp hα').1
  have hγS : γ ∈ sigmaSubAFinset A₀ := (mem_sigmaStrataFinset.mp hγ).1
  have hγS' : γ' ∈ sigmaSubAFinset A₀ := (mem_sigmaStrataFinset.mp hγ').1
  have hdα : addOrderOf (α - α') ∣ QA A₁ := by
    refine (addOrderOf_dvd_iff_nsmul_eq_zero).mpr ?_
    rw [smul_sub, nsmul_QA_eq_zero_of_mem_sigmaSubAFinset h2A₁ hαS,
      nsmul_QA_eq_zero_of_mem_sigmaSubAFinset h2A₁ hαS', sub_zero]
  have hdγ : addOrderOf (γ' - γ) ∣ QA A₀ := by
    refine (addOrderOf_dvd_iff_nsmul_eq_zero).mpr ?_
    rw [smul_sub, nsmul_QA_eq_zero_of_mem_sigmaSubAFinset h2A₀ hγS',
      nsmul_QA_eq_zero_of_mem_sigmaSubAFinset h2A₀ hγS, sub_zero]
  have heq : α - α' = γ' - γ := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm γ' α']
    exact h
  have hdγ' : addOrderOf (α - α') ∣ QA A₀ := by rw [heq]; exact hdγ
  have hinter : A₀ ∩ A₁ = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
  have hd : addOrderOf (α - α') ∣ QA (A₀ ∩ A₁) := by
    rw [← gcd_QA_inter_of_coprime (fun p hp q hq hpq => hS p (hA₀ hp) q (hA₁ hq) hpq)]
    exact Nat.dvd_gcd hdγ' hdα
  have hd1 : addOrderOf (α - α') ∣ 1 := by
    rw [hinter] at hd
    simpa [QA] using hd
  have hzero : α - α' = 0 := by
    have h := (addOrderOf_dvd_iff_nsmul_eq_zero).mp hd1
    simpa using h
  refine ⟨sub_eq_zero.mp hzero, ?_⟩
  rw [sub_eq_zero.mp hzero] at h
  exact add_left_cancel h

/-- **The co-atoms of a pair of the strata index set lie in `Σ_{≤ k}`.**  For `(A₀, α)` in
`strataCompPairSet S k` and `γ ∈ Σ_{A₀}`, the point `γ + α` is a point of the torsion subgroup
`𝕋[Q_B]` for some `B ⊆ S` with `B.card ≤ k`. -/
lemma exists_arcPt_of_strataPairSet {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) {k : ℕ}
    {p : Finset ℕ × Circle} (hp : p ∈ strataCompPairSet S k) {γ : Circle}
    (hγ : γ ∈ sigmaStrataFinset p.1) :
    ∃ (B : Finset ℕ) (b : ℤ), B ⊆ S ∧ B.card ≤ k ∧ γ + p.2 = arcPt (QA B) b := by
  classical
  obtain ⟨hp1S, hp1k, hp2mem⟩ := mem_strataCompPairSet.mp hp
  obtain ⟨A₁, hA₁mem, hp2A₁⟩ := mem_strataCompFinset.mp hp2mem
  rw [Finset.mem_filter, Finset.mem_powerset] at hA₁mem
  obtain ⟨hA₁sub, hA₁card⟩ := hA₁mem
  have hA₁S : A₁ ⊆ S := hA₁sub.trans (Finset.sdiff_subset)
  have hdisj : Disjoint p.1 A₁ := Finset.disjoint_left.mpr fun q hq hq₁ =>
    (Finset.mem_sdiff.mp (hA₁sub hq₁)).2 hq
  have hmem : γ + p.2 ∈ sigmaStrataFinset (p.1 ∪ A₁) :=
    circle_strata_add_mem h2 hS hp1S hA₁S hdisj hγ hp2A₁
  have hcard : (p.1 ∪ A₁).card ≤ k := by
    rw [Finset.card_union_of_disjoint hdisj]; omega
  have h2U : ∀ q ∈ p.1 ∪ A₁, 2 ≤ q := fun q hq =>
    (Finset.mem_union.mp hq).elim (fun h => h2 q (hp1S h)) (fun h => h2 q (hA₁S h))
  have hsub : γ + p.2 ∈ sigmaSubAFinset (p.1 ∪ A₁) := (mem_sigmaStrataFinset.mp hmem).1
  have hz : (QA (p.1 ∪ A₁) : ℤ) • (γ + p.2) = 0 :=
    (mem_sigmaSubAFinset_iff_zsmul_eq_zero h2U (γ + p.2)).mp hsub
  obtain ⟨b, hb⟩ := exists_arcPt_of_zsmul_eq_zero (QA_ne_zero_of_two_le h2U) hz
  exact ⟨p.1 ∪ A₁, b, Finset.union_subset hp1S hA₁S, hcard, hb⟩

/-! ## Tao's `2 ^ k` counting bound for the strata index set -/

/-- **The strata pairs that decompose a fixed point share a common denominator set.**  If
`strataCompPairSetFilter S k β` is nonempty then there is `B ⊆ S` with `B.card ≤ k` such that every
pair `(A₀, α)` of the filtered set has `A₀ ⊆ B`. -/
lemma exists_common_strata {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (β : Circle) :
    ∃ B : Finset ℕ, B.card ≤ k ∧ ∀ p ∈ strataCompPairSetFilter S k β, p.1 ⊆ B := by
  classical
  by_cases hne : (strataCompPairSetFilter S k β).Nonempty
  · obtain ⟨p₀, hp₀⟩ := hne
    obtain ⟨A₀, α₀⟩ := p₀
    obtain ⟨hp₀pair, hβ₀⟩ := mem_strataCompPairSetFilter.mp hp₀
    obtain ⟨hA₀sub, hA₀card, hα₀comp⟩ := mem_strataCompPairSet.mp hp₀pair
    obtain ⟨A₁, hA₁mem, hα₀A₁⟩ := mem_strataCompFinset.mp hα₀comp
    rw [Finset.mem_filter, Finset.mem_powerset] at hA₁mem
    obtain ⟨hA₁sub, hA₁card⟩ := hA₁mem
    have hA₁S : A₁ ⊆ S := hA₁sub.trans (Finset.sdiff_subset)
    have hdisj₀ : Disjoint A₀ A₁ := Finset.disjoint_left.mpr fun q hq hq₁ =>
      (Finset.mem_sdiff.mp (hA₁sub hq₁)).2 hq
    have hB₀ : β ∈ sigmaStrataFinset (A₀ ∪ A₁) := by
      have h := circle_strata_add_mem h2 hS hA₀sub hA₁S hdisj₀ hβ₀ hα₀A₁
      rwa [sub_add_cancel] at h
    have hBcard : (A₀ ∪ A₁).card ≤ k := by
      rw [Finset.card_union_of_disjoint hdisj₀]; omega
    refine ⟨A₀ ∪ A₁, hBcard, ?_⟩
    intro p hp
    obtain ⟨A, γ⟩ := p
    obtain ⟨hppair, hβγ⟩ := mem_strataCompPairSetFilter.mp hp
    obtain ⟨hAsub, hAcard, hγcomp⟩ := mem_strataCompPairSet.mp hppair
    obtain ⟨A₂, hA₂mem, hγA₂⟩ := mem_strataCompFinset.mp hγcomp
    rw [Finset.mem_filter, Finset.mem_powerset] at hA₂mem
    obtain ⟨hA₂sub, hA₂card⟩ := hA₂mem
    have hA₂S : A₂ ⊆ S := hA₂sub.trans (Finset.sdiff_subset)
    have hdisj : Disjoint A A₂ := Finset.disjoint_left.mpr fun q hq hq₂ =>
      (Finset.mem_sdiff.mp (hA₂sub hq₂)).2 hq
    have hβA : β ∈ sigmaStrataFinset (A ∪ A₂) := by
      have h := circle_strata_add_mem h2 hS hAsub hA₂S hdisj hβγ hγA₂
      rwa [sub_add_cancel] at h
    have heq : A ∪ A₂ = A₀ ∪ A₁ :=
      circle_strata_disjoint h2 hS (Finset.union_subset hAsub hA₂S)
        (Finset.union_subset hA₀sub hA₁S) hβA hB₀
    intro q hq
    rw [← heq]
    exact Finset.mem_union_left _ hq
  · refine ⟨∅, by simp, ?_⟩
    intro p hp
    rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hp
    exact absurd hp (Finset.notMem_empty p)

/-- **The first projection is injective on `strataCompPairSetFilter`**: two admissible pairs `(A₀, α)`
and `(A₀, γ)` sharing their first component share their second one too. -/
lemma fst_injOn_strata {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (β : Circle) :
    Set.InjOn Prod.fst (strataCompPairSetFilter S k β : Set (Finset ℕ × Circle)) := by
  classical
  intro p hp q hq hpq
  obtain ⟨A, α⟩ := p
  obtain ⟨B, γ⟩ := q
  have hAB : A = B := hpq
  subst hAB
  have hp_pair : (A, α) ∈ strataCompPairSet S k := (mem_strataCompPairSetFilter.mp hp).1
  have hβA : β - α ∈ sigmaStrataFinset A := (mem_strataCompPairSetFilter.mp hp).2
  obtain ⟨hAsub, hAcard, hαunion⟩ := mem_strataCompPairSet.mp hp_pair
  obtain ⟨A₂, hA₂mem, hαA₂⟩ := mem_strataCompFinset.mp hαunion
  rw [Finset.mem_filter, Finset.mem_powerset] at hA₂mem
  obtain ⟨hA₂sub, hA₂card⟩ := hA₂mem
  have hA₂S : A₂ ⊆ S := hA₂sub.trans (Finset.sdiff_subset)
  have hdisjA₂ : Disjoint A A₂ := Finset.disjoint_left.mpr fun r hr hr₂ =>
    (Finset.mem_sdiff.mp (hA₂sub hr₂)).2 hr
  have hβu : β ∈ sigmaStrataFinset (A ∪ A₂) := by
    have h := circle_strata_add_mem h2 hS hAsub hA₂S hdisjA₂ hβA hαA₂
    rwa [sub_add_cancel] at h
  have hq_pair : (A, γ) ∈ strataCompPairSet S k := (mem_strataCompPairSetFilter.mp hq).1
  have hβγ : β - γ ∈ sigmaStrataFinset A := (mem_strataCompPairSetFilter.mp hq).2
  obtain ⟨hAsub', hAcard', hγunion⟩ := mem_strataCompPairSet.mp hq_pair
  obtain ⟨A₂', hA₂'mem, hγA₂'⟩ := mem_strataCompFinset.mp hγunion
  rw [Finset.mem_filter, Finset.mem_powerset] at hA₂'mem
  obtain ⟨hA₂'sub, hA₂'card⟩ := hA₂'mem
  have hA₂'S : A₂' ⊆ S := hA₂'sub.trans (Finset.sdiff_subset)
  have hdisjA₂' : Disjoint A A₂' := Finset.disjoint_left.mpr fun r hr hr₂ =>
    (Finset.mem_sdiff.mp (hA₂'sub hr₂)).2 hr
  have hβu' : β ∈ sigmaStrataFinset (A ∪ A₂') := by
    have h := circle_strata_add_mem h2 hS hAsub' hA₂'S hdisjA₂' hβγ hγA₂'
    rwa [sub_add_cancel] at h
  have heqU : A ∪ A₂ = A ∪ A₂' :=
    circle_strata_disjoint h2 hS (Finset.union_subset hAsub hA₂S)
      (Finset.union_subset hAsub' hA₂'S) hβu hβu'
  have hA₂eq : A₂ = A₂' := by
    have e1 : A₂ = (A ∪ A₂) \ A := by
      ext r
      rw [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun hr => ⟨Or.inr hr, fun hrA => Finset.disjoint_left.mp hdisjA₂ hrA hr⟩,
        fun h => h.1.elim (fun hrA => absurd hrA h.2) id⟩
    have e2 : A₂' = (A ∪ A₂') \ A := by
      ext r
      rw [Finset.mem_sdiff, Finset.mem_union]
      exact ⟨fun hr => ⟨Or.inr hr, fun hrA => Finset.disjoint_left.mp hdisjA₂' hrA hr⟩,
        fun h => h.1.elim (fun hrA => absurd hrA h.2) id⟩
    rw [e1, e2, heqU]
  have huniq := circle_strata_decomp_unique h2 hS hAsub hA₂S hdisjA₂ hαA₂
    (by rw [hA₂eq]; exact hγA₂') hβA hβγ (by
      rw [add_comm α (β - α), sub_add_cancel, add_comm γ (β - γ), sub_add_cancel])
  exact Prod.ext rfl (by simpa using huniq.1)

/-- **Tao's `2 ^ k` counting bound for the strata index set.**  For a fixed point `β` of the circle,
at most `2 ^ k` pairs `(A₀, α)` with `A₀ ⊆ S`, `A₀.card ≤ k`, `α ∈ Σ_{(A₀)}` satisfy
`β - α ∈ Σ_{A₀}`. -/
theorem strataCompPairSetFilter_card_le_aux {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (β : Circle) :
    (strataCompPairSetFilter S k β).card ≤ 2 ^ k := by
  classical
  obtain ⟨B, hBcard, hBsub⟩ := exists_common_strata h2 hS k β
  have hinj := fst_injOn_strata h2 hS k β
  have hmain : (strataCompPairSetFilter S k β).card ≤ B.powerset.card :=
    Finset.card_le_card_of_injOn Prod.fst
      (fun p hp => Finset.mem_powerset.mpr (hBsub p hp))
      (fun p hp q hq hpq => hinj hp hq hpq)
  calc (strataCompPairSetFilter S k β).card ≤ B.powerset.card := hmain
    _ = 2 ^ B.card := Finset.card_powerset B
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hBcard

/-- **The `2^k` counting bound for the arcs of the strata square function.**  If `2ε` is smaller
than the separation `1/qmax^{2k}` of the arc points of `Σ_{≤k}`, then at each point `ξ` of the
circle at most `2^k` of the pairs `(A₀, α)` of `strataCompPairSet S k` can have
`(α + Σ_{A₀})` meeting the ball of radius `ε` around `ξ`. -/
theorem strataPairSet_card_le {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) {k qmax : ℕ}
    (hmax : ∀ q ∈ S, q ≤ qmax) (hqmax : 1 ≤ qmax) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : 2 * ε < 1 / (qmax : ℝ) ^ (2 * k)) (ξ : Circle) :
    (((strataCompPairSet S k).filter (fun p => ∃ γ ∈ sigmaStrataFinset p.1,
        ‖ξ - (γ + p.2)‖ ≤ ε)).card) ≤ 2 ^ k := by
  classical
  set T := (strataCompPairSet S k).filter (fun p => ∃ γ ∈ sigmaStrataFinset p.1,
      ‖ξ - (γ + p.2)‖ ≤ ε) with hT
  rcases T.eq_empty_or_nonempty with hem | ⟨p₀, hp₀⟩
  · rw [hem, Finset.card_empty]
    exact Nat.zero_le _
  · obtain ⟨hp₀s, γ₀, hγ₀, hγ₀le⟩ := Finset.mem_filter.mp hp₀
    refine le_trans (Finset.card_le_card ?_)
      (strataCompPairSetFilter_card_le_aux h2 hS k (γ₀ + p₀.2))
    intro p hp
    obtain ⟨hps, γ, hγ, hle⟩ := Finset.mem_filter.mp hp
    rw [mem_strataCompPairSetFilter]
    refine ⟨hps, ?_⟩
    have hβ : γ + p.2 = γ₀ + p₀.2 := by
      by_contra hne
      obtain ⟨B, b, hB, hkB, hBeq⟩ := exists_arcPt_of_strataPairSet h2 hS hps hγ
      obtain ⟨B', b', hB', hkB', hB'eq⟩ := exists_arcPt_of_strataPairSet h2 hS hp₀s hγ₀
      have hne' : arcPt (QA B) b ≠ arcPt (QA B') b' := fun hc =>
        hne (by rw [hBeq, hc, ← hB'eq])
      have hsep := sigmaLe_separation h2 hS hB hB' hkB hkB' hmax hne'
      rw [← hBeq, ← hB'eq] at hsep
      have htri : ‖(γ + p.2) - (γ₀ + p₀.2)‖ ≤ 2 * ε := by
        calc ‖(γ + p.2) - (γ₀ + p₀.2)‖
            = ‖(ξ - (γ₀ + p₀.2)) - (ξ - (γ + p.2))‖ := by abel
          _ ≤ ‖ξ - (γ₀ + p₀.2)‖ + ‖ξ - (γ + p.2)‖ := norm_sub_le _ _
          _ ≤ 2 * ε := by linarith
      exact absurd hsep (not_le.mpr (lt_of_le_of_lt htri hsmall))
    rw [← hβ, add_sub_cancel_right]
    exact hγ


/-- The `p = 2` endpoint of Tao's `ortho-apply`(ii) in the strata convention: for a bump `φ` supported in the ball of radius `ε` and bounded by `M`, with `2ε` smaller than the separation `1/qmax^{2k}` of the arc points of `Σ_{≤k}`, the square function of the modulated multipliers over the strata index set obeys the Plancherel/Bessel bound `Σ_{(A₀,α)} ‖Op_{φ;α+Σ_{A₀}}f‖²_{ℓ²} ≤ M² 2^k ‖f‖²_{ℓ²}`, where `(A₀,α)` runs over `strataCompPairSet S k` (i.e. `A₀ ⊆ S`, `A₀.card ≤ k`, `α ∈ Σ_{(A₀)} = strataCompFinset S k A₀`) and the operator is `opArc φ hφ (arcShift (sigmaStrataFinset A₀) α)`, i.e. the multiplier with symbol `Σ_{γ ∈ α + Σ_{A₀}} φ(· − γ)` (Tao's strata `Σ_{A₀}`, not the exact-denominator set).  It is exactly `opArc_l2_endpoint` with `sigmaAFinset`/`sigmaCompPairSet` replaced by `sigmaStrataFinset`/`strataCompPairSet`. -/
theorem opArc_l2_endpoint_strata {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) {k qmax : ℕ}
    (hmax : ∀ q ∈ S, q ≤ qmax) (hqmax : 1 ≤ qmax) {ε : ℝ} (hε : 0 ≤ ε)
    (hsmall : 2 * ε < 1 / (qmax : ℝ) ^ (2 * k))
    (φ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hφ : MeasureTheory.MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) {M : ℝ}
    (hM : 0 ≤ M) (hφbd : ∀ ξ, ‖φ ξ‖ ≤ M) (hφsupp : ∀ ξ, ε < ‖ξ‖ → φ ξ = 0)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    ∑ p ∈ Work.BourgainPlan.IonescuWainger.strataCompPairSet S k, ∑' n : ℤ,
        ‖Work.BourgainPlan.IonescuWainger.opArc φ hφ
          (Work.BourgainPlan.IonescuWainger.arcShift
            (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset p.1) p.2) f hf n‖ ^ 2
      ≤ M ^ 2 * (2 ^ k : ℝ) * ∑' n : ℤ, ‖f n‖ ^ 2 := by
  classical
  have hsep : ∀ p ∈ Work.BourgainPlan.IonescuWainger.strataCompPairSet S k,
      ∀ β ∈ Work.BourgainPlan.IonescuWainger.arcShift
          (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset p.1) p.2,
      ∀ β' ∈ Work.BourgainPlan.IonescuWainger.arcShift
          (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset p.1) p.2,
        β ≠ β' → 1 / (qmax : ℝ) ^ (2 * k) ≤ ‖β - β'‖ := by
    intro p hp β hβ β' hβ' hne
    rw [mem_arcShift] at hβ hβ'
    obtain ⟨γ, hγ, rfl⟩ := hβ
    obtain ⟨γ', hγ', rfl⟩ := hβ'
    obtain ⟨B, b, hB, hkB, hBeq⟩ := exists_arcPt_of_strataPairSet h2 hS hp hγ
    obtain ⟨B', b', hB', hkB', hB'eq⟩ := exists_arcPt_of_strataPairSet h2 hS hp hγ'
    have hne' : arcPt (QA B) b ≠ arcPt (QA B') b' := fun hc =>
      hne (by rw [hBeq, hc, ← hB'eq])
    have hsep' := sigmaLe_separation h2 hS hB hB' hkB hkB' hmax hne'
    rwa [← hBeq, ← hB'eq] at hsep'
  have hbd : ∀ p ∈ Work.BourgainPlan.IonescuWainger.strataCompPairSet S k,
      ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      ‖(arcSymbolLp φ hφ (arcShift (sigmaStrataFinset p.1) p.2) : Circle → ℂ) ξ‖ ≤ M := by
    intro p hp
    filter_upwards [arcSymbolLp_coeFn φ hφ (arcShift (sigmaStrataFinset p.1) p.2)] with ξ hξ
    rw [hξ]
    exact norm_arcSymbol_le hφbd hφsupp (hsep p hp) hsmall ξ
  have hcnt : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)),
      (((strataCompPairSet S k).filter (fun p =>
        (arcSymbolLp φ hφ (arcShift (sigmaStrataFinset p.1) p.2) : Circle → ℂ) ξ ≠ 0)).card : ℝ)
        ≤ (2 ^ k : ℝ) := by
    have hall : ∀ᵐ ξ ∂(AddCircle.haarAddCircle (T := 1)), ∀ p ∈ strataCompPairSet S k,
        (arcSymbolLp φ hφ (arcShift (sigmaStrataFinset p.1) p.2) : Circle → ℂ) ξ
          = arcSymbol φ (arcShift (sigmaStrataFinset p.1) p.2) ξ := by
      refine Filter.Eventually.mono (Filter.eventually_all.mpr fun p : ↥(strataCompPairSet S k) =>
        arcSymbolLp_coeFn φ hφ (arcShift (sigmaStrataFinset p.1.1) p.1.2)) ?_
      intro ξ hξ p hp
      exact hξ ⟨p, hp⟩
    filter_upwards [hall] with ξ hξ
    have hsub : (strataCompPairSet S k).filter (fun p =>
          (arcSymbolLp φ hφ (arcShift (sigmaStrataFinset p.1) p.2) : Circle → ℂ) ξ ≠ 0)
        ⊆ (strataCompPairSet S k).filter (fun p => ∃ γ ∈ sigmaStrataFinset p.1,
            ‖ξ - (γ + p.2)‖ ≤ ε) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      rw [Finset.mem_filter]
      refine ⟨hp1, ?_⟩
      rw [hξ p hp1, arcSymbol_apply] at hp2
      obtain ⟨β, hβ, hβne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp2
      rw [mem_arcShift] at hβ
      obtain ⟨γ, hγ, rfl⟩ := hβ
      refine ⟨γ, hγ, ?_⟩
      by_contra hlt
      exact hβne (hφsupp _ (not_le.mp hlt))
    calc (((strataCompPairSet S k).filter (fun p =>
            (arcSymbolLp φ hφ (arcShift (sigmaStrataFinset p.1) p.2) : Circle → ℂ) ξ ≠ 0)).card : ℝ)
        ≤ (((strataCompPairSet S k).filter (fun p => ∃ γ ∈ sigmaStrataFinset p.1,
            ‖ξ - (γ + p.2)‖ ≤ ε)).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ (2 : ℝ) ^ k := by
          refine le_trans (Nat.cast_le.mpr (strataPairSet_card_le h2 hS hmax hqmax hε hsmall ξ)) ?_
          push_cast
          exact le_rfl
  exact sum_opMul_l2_le_finset (N := (2 ^ k : ℝ)) (strataCompPairSet S k)
    (fun p => arcSymbolLp φ hφ (arcShift (sigmaStrataFinset p.1) p.2)) hM (by positivity) hbd hcnt f hf

end

end Work.BourgainPlan.IonescuWainger
