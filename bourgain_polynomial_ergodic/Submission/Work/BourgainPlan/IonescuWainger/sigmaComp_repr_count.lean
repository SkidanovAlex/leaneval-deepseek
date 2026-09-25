import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcSep
import Submission.Work.BourgainPlan.IonescuWainger.sigmaA_add_mem
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Two closure properties of the torsion arcs `Σ_{⊆ A}` -/

/-- `Σ_{⊆ A}` is closed under multiplication by integers. -/
private lemma zsmul_mem_sigmaSubA {A : Finset ℕ} {x : Circle} (hx : x ∈ sigmaSubA A)
    (n : ℤ) : n • x ∈ sigmaSubA A := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨n * a, ?_⟩
  rw [arcPt, zsmul_arcPt]
  congr 1
  push_cast
  ring

/-- `Σ_{⊆ A}` is closed under negation. -/
private lemma neg_mem_sigmaSubA {A : Finset ℕ} {x : Circle} (hx : x ∈ sigmaSubA A) :
    -x ∈ sigmaSubA A := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨-a, by rw [arcPt_neg]⟩

/-- **Exact additivity of the denominator.**  If `A₀, A₁ ⊆ S` are disjoint and `x ∈ Σ_{A₀}`,
`y ∈ Σ_{A₁}` have exact denominators `Q_{A₀}`, `Q_{A₁}`, then the sum `x + y` has exact order
`Q_{A₀} Q_{A₁} = Q_{A₀ ∪ A₁}`: any `n` with `n • (x + y) = 0` is a multiple of `Q_{A₀} Q_{A₁}`.

Indeed `n • x = -(n • y)` lies in `Σ_{⊆ A₀} ∩ Σ_{⊆ A₁} = {0}` (the torsion subgroups are coprime),
so `Q_{A₀} ∣ n` and `Q_{A₁} ∣ n`, and `Q_{A₀}`, `Q_{A₁}` are coprime. -/
private lemma dvd_of_zsmul_add_eq_zero {S A₀ A₁ : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) (hA₁ : A₁ ⊆ S) (hdisj : Disjoint A₀ A₁)
    {x y : Circle} (hx : x ∈ sigmaA A₀) (hy : y ∈ sigmaA A₁) {n : ℕ}
    (hn : (n : ℤ) • (x + y) = 0) : QA A₀ * QA A₁ ∣ n := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hQ0 : QA A₀ ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA₀ hq)
  have hQ1 : QA A₁ ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA₁ hq)
  have hdisj' : ∀ q ∈ A₀, q ∉ A₁ := fun q hq => Finset.disjoint_left.mp hdisj hq
  have hcop : Nat.Coprime (QA A₀) (QA A₁) :=
    coprime_QA_of_disjoint fun q hq q' hq' => by
      rcases eq_or_ne q q' with he | hne
      · subst he; exact absurd hq' (hdisj' q hq)
      · exact hS q (hA₀ hq) q' (hA₁ hq') hne
  rw [smul_add] at hn
  have hnx : (n : ℤ) • arcPt (QA A₀) a = -((n : ℤ) • arcPt (QA A₁) b) :=
    eq_neg_of_add_eq_zero_left hn
  have hmem₁ : (n : ℤ) • arcPt (QA A₀) a ∈ sigmaSubA A₀ :=
    zsmul_mem_sigmaSubA (sigmaA_subset_sigmaSubA A₀ ⟨a, ha, rfl⟩) n
  have hmem₂ : (n : ℤ) • arcPt (QA A₀) a ∈ sigmaSubA A₁ := by
    rw [hnx]
    exact neg_mem_sigmaSubA (zsmul_mem_sigmaSubA (sigmaA_subset_sigmaSubA A₁ ⟨b, hb, rfl⟩) n)
  have hzero : (n : ℤ) • arcPt (QA A₀) a = 0 :=
    eq_zero_of_mem_sigmaSubA_inter h2 hA₀ hA₁ hcop hmem₁ hmem₂
  have hdvd₀ : QA A₀ ∣ n := dvd_of_zsmul_arcPt_eq_zero hQ0 ha hzero
  have hny : (n : ℤ) • arcPt (QA A₁) b = -((n : ℤ) • arcPt (QA A₀) a) := by
    rw [hnx, neg_neg]
  have hzero' : (n : ℤ) • arcPt (QA A₁) b = 0 := by rw [hny, hzero, neg_zero]
  have hdvd₁ : QA A₁ ∣ n := dvd_of_zsmul_arcPt_eq_zero hQ1 hb hzero'
  exact hcop.mul_dvd_of_dvd_of_dvd hdvd₀ hdvd₁

/-- **The exact denominator of a decomposition is determined by the point.**
If `x₀ + x₁ = y₀ + y₁` with `x₀ ∈ Σ_A`, `x₁ ∈ Σ_B`, `y₀ ∈ Σ_C`, `y₁ ∈ Σ_D` for pairwise disjoint
`A, B` resp. `C, D` inside the pairwise coprime set `S`, then `A ∪ B = C ∪ D`.

Indeed both sides of the equality `x₀ + x₁ = y₀ + y₁ = β` have exact order `Q_{A ∪ B}` resp.
`Q_{C ∪ D}` (`dvd_of_zsmul_add_eq_zero`, in both directions), so `Q_{A∪B} = Q_{C∪D}`, and `Q` is
injective on subsets of `S` (`QA_injective`). -/
private lemma sigmaUnion_unique {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A B C D : Finset ℕ} (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S) (hD : D ⊆ S)
    (hdAB : Disjoint A B) (hdCD : Disjoint C D)
    {x₀ x₁ y₀ y₁ : Circle} (hx₀ : x₀ ∈ sigmaA A) (hx₁ : x₁ ∈ sigmaA B)
    (hy₀ : y₀ ∈ sigmaA C) (hy₁ : y₁ ∈ sigmaA D)
    (heq : x₀ + x₁ = y₀ + y₁) : A ∪ B = C ∪ D := by
  have hC0 : (QA C : ℤ) • y₀ = 0 :=
    sigmaSubA_zsmul_eq_zero (fun q hq => h2 q (hC hq)) (sigmaA_subset_sigmaSubA C hy₀)
  have hD1 : (QA D : ℤ) • y₁ = 0 :=
    sigmaSubA_zsmul_eq_zero (fun q hq => h2 q (hD hq)) (sigmaA_subset_sigmaSubA D hy₁)
  have hA0 : (QA A : ℤ) • x₀ = 0 :=
    sigmaSubA_zsmul_eq_zero (fun q hq => h2 q (hA hq)) (sigmaA_subset_sigmaSubA A hx₀)
  have hB1 : (QA B : ℤ) • x₁ = 0 :=
    sigmaSubA_zsmul_eq_zero (fun q hq => h2 q (hB hq)) (sigmaA_subset_sigmaSubA B hx₁)
  have hxzero : ((QA A * QA B : ℕ) : ℤ) • (x₀ + x₁) = 0 := by
    have step : ((QA A * QA B : ℕ) : ℤ) = (QA B : ℤ) * (QA A : ℤ) := by
      rw [Nat.cast_mul, mul_comm]
    rw [step, mul_zsmul, smul_add, hA0, zero_add, smul_comm, hB1, smul_zero]
  have hyzero : ((QA C * QA D : ℕ) : ℤ) • (y₀ + y₁) = 0 := by
    have step : ((QA C * QA D : ℕ) : ℤ) = (QA D : ℤ) * (QA C : ℤ) := by
      rw [Nat.cast_mul, mul_comm]
    rw [step, mul_zsmul, smul_add, hC0, zero_add, smul_comm, hD1, smul_zero]
  have h1 : QA A * QA B ∣ QA C * QA D :=
    dvd_of_zsmul_add_eq_zero h2 hS hA hB hdAB hx₀ hx₁ (by rw [heq]; exact hyzero)
  have h2' : QA C * QA D ∣ QA A * QA B :=
    dvd_of_zsmul_add_eq_zero h2 hS hC hD hdCD hy₀ hy₁ (by rw [← heq]; exact hxzero)
  have hQeq : QA (A ∪ B) = QA (C ∪ D) := by
    rw [QA_union hdAB, QA_union hdCD]
    exact Nat.dvd_antisymm h1 h2'
  exact QA_injective h2 hS (Finset.union_subset hA hB) (Finset.union_subset hC hD) hQeq

/-- **Tao's `2^k` counting bound for the decompositions `β = α₀ + α`, `α₀ ∈ Σ_{A₀}`, `α ∈ Σ_{(A₀)}`.**

Let `S` be a finite set of pairwise coprime integers `≥ 2`, and let `β` be any point of the circle
`𝕋 = ℝ/ℤ`.  Then the number of sets `A₀ ⊆ S` with `A₀.card ≤ k` for which `β` admits a decomposition
`β = α₀ + α` with `α₀ ∈ Σ_{A₀}` (points of *exact* denominator `Q_{A₀}`) and `α ∈ Σ_{(A₀)}` (the
complementary arc `Σ_{(A₀)} = ⋃_{A₁ ⊆ S \\ A₀, A₁.card ≤ k - A₀.card} Σ_{A₁}`) is at most `2^k`;
`sigmaCompDecompSet S k β` (in `ArcSep.lean`) is that set of admissible `A₀`.

This is the counting fact used in the proof of Tao's Theorem `ortho-apply`(i)
(arXiv:2008.05066, §4). -/
theorem sigmaComp_repr_count {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (β : Circle) :
    (sigmaCompDecompSet S k β).card ≤ 2 ^ k := by
  classical
  by_cases hne : (sigmaCompDecompSet S k β).Nonempty
  · obtain ⟨A₀, hA₀mem⟩ := hne
    -- unpack the membership of `A₀`
    have hA₀mem' := hA₀mem
    simp only [sigmaCompDecompSet, Finset.mem_filter, Finset.mem_powerset] at hA₀mem'
    obtain ⟨⟨hA₀sub, hA₀card⟩, α, hαmem, hα₀mem⟩ := hA₀mem'
    -- unpack the complementary arc `Σ_{(A₀)}`
    rw [sigmaComp] at hαmem
    simp only [Set.mem_iUnion] at hαmem
    obtain ⟨A₁, hA₁mem, hα₁mem⟩ := hαmem
    rw [Finset.mem_filter, Finset.mem_powerset] at hA₁mem
    obtain ⟨hA₁sub, hA₁card⟩ := hA₁mem
    have hA₁S : A₁ ⊆ S := hA₁sub.trans (Finset.sdiff_subset)
    have hdisj : Disjoint A₀ A₁ :=
      Finset.disjoint_left.mpr fun q hq₀ hq₁ => (Finset.mem_sdiff.mp (hA₁sub hq₁)).2 hq₀
    have hBcard : (A₀ ∪ A₁).card ≤ k := by
      rw [Finset.card_union_of_disjoint hdisj]
      omega
    -- every admissible `A₀'` satisfies `A₀' ⊆ A₀ ∪ A₁`
    have hsub : sigmaCompDecompSet S k β ⊆ (A₀ ∪ A₁).powerset := by
      intro A₀' hA₀'mem
      rw [Finset.mem_powerset]
      have hA₀'mem' := hA₀'mem
      simp only [sigmaCompDecompSet, Finset.mem_filter, Finset.mem_powerset] at hA₀'mem'
      obtain ⟨⟨hA₀'sub, -⟩, α', hα'mem, hα₀'mem⟩ := hA₀'mem'
      rw [sigmaComp] at hα'mem
      simp only [Set.mem_iUnion] at hα'mem
      obtain ⟨A₁', hA₁'mem, hα₁'mem⟩ := hα'mem
      rw [Finset.mem_filter, Finset.mem_powerset] at hA₁'mem
      obtain ⟨hA₁'sub, -⟩ := hA₁'mem
      have hA₁'S : A₁' ⊆ S := hA₁'sub.trans Finset.sdiff_subset
      have hdisj' : Disjoint A₀' A₁' :=
        Finset.disjoint_left.mpr fun q hq₀ hq₁ => (Finset.mem_sdiff.mp (hA₁'sub hq₁)).2 hq₀
      have heq : (β - α') + α' = (β - α) + α := by rw [sub_add_cancel, sub_add_cancel]
      have hunion : A₀' ∪ A₁' = A₀ ∪ A₁ :=
        sigmaUnion_unique h2 hS hA₀'sub hA₁'S hA₀sub hA₁S hdisj' hdisj
          hα₀'mem hα₁'mem hα₀mem hα₁mem heq
      intro q hq
      rw [← hunion]
      exact Finset.mem_union_left _ hq
    calc (sigmaCompDecompSet S k β).card ≤ ((A₀ ∪ A₁).powerset).card := Finset.card_le_card hsub
      _ = 2 ^ (A₀ ∪ A₁).card := Finset.card_powerset _
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hBcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

end Work.BourgainPlan.IonescuWainger
