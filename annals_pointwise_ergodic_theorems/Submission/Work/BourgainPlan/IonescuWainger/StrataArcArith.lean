import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.indicator_sigmaStrataFinset_incl_excl
import Submission.Work.BourgainPlan.IonescuWainger.sigmaA_petal_sum_shift_perturbed_ne_zero
import Submission.Work.BourgainPlan.IonescuWainger.sigmaStrataQ_petal_sum_ne_zero

/-!
# The circle-side arithmetic of Tao's strata `Σ_A` (nonce and petal separation)

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4,
Lemma `ortho`(ii)/(iii).

This file ports the two arithmetic inputs of the band-limited lane
(`sigmaA_nonce_sum_perturbed_ne_zero`, `sigmaA_petal_sum_shift_perturbed_ne_zero`, both stated for
the *exact denominator* sets `sigmaAFinset`/`sigmaA`) to Tao's **strata**
`Σ_A = sigmaStrataFinset A = 𝕋[Q_A] \ ⋃_{B ⊊ A} 𝕋[Q_B]`, which is the convention in which the
major-arc system is a partition of `Σ_{≤k}` (and hence the convention of `ortho_apply_upper` and of
the target `ortho_apply_lower_strata`).

The only difference from the exact-denominator statements is that a stratum point `α` is *not*
assumed to have exact denominator `Q_A`: all that is used is that `α ∈ 𝕋[Q_A]` (so `Q_A • α = 0`)
and that `α` does not lie in any strictly smaller subgroup `𝕋[Q_B]`, `B ⊊ A`.

* `sigmaStrata_nonce_sum_norm_ge` / `sigmaStrata_nonce_sum_perturbed_ne_zero`: the signed sum of
  points of the strata of a family carrying a *nonce* is bounded below by `1/∏_i Q_{A i}`, hence
  cannot be destroyed by perturbations `θ_i` of size `≤ ε < 1/((#ι)·∏_i Q_{A i})`.
* `sigmaStrata_petal_sum_shift_norm_ge` / `sigmaStrata_petal_sum_shift_perturbed_ne_zero`: the same
  for the difference of two petal sums with a common core shift, for pairwise disjoint petals.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Elementary facts about the strata and the torsion subgroups -/

/-- **Tao's stratum `Σ_A` is contained in the torsion subgroup `Σ_{⊆ A} = 𝕋[Q_A]`** (as subsets of
the circle). -/
theorem coe_sigmaStrataFinset_subset_sigmaSubA (A : Finset ℕ) :
    ((sigmaStrataFinset A : Finset Circle) : Set Circle) ⊆ sigmaSubA A := by
  intro β hβ
  have hβ' : β ∈ sigmaSubAFinset A :=
    sigmaStrataFinset_subset_sigmaSubAFinset A (Finset.mem_coe.mp hβ)
  rw [sigmaSubAFinset, Finset.mem_image] at hβ'
  obtain ⟨a, -, rfl⟩ := hβ'
  exact ⟨(a : ℤ), rfl⟩

/-- **A point of the circle killed by both `Q_A` and `Q_B` lies in `Σ_{⊆ A ∩ B}`**, for
`A, B ⊆ S` with `S` pairwise coprime: the additive order divides `gcd (Q_A) (Q_B) = Q_{A ∩ B}`. -/
theorem sigmaSubAFinset_inter_mem' {S A B : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (hA : A ⊆ S) (hB : B ⊆ S)
    {β : Circle} (hβA : β ∈ sigmaSubAFinset A) (hβB : β ∈ sigmaSubAFinset B) :
    β ∈ sigmaSubAFinset (A ∩ B) := by
  have h2AB : ∀ q ∈ A ∩ B, 2 ≤ q := fun q hq => h2 q (hA (Finset.mem_inter.mp hq).1)
  rw [mem_sigmaSubAFinset_iff_dvd_addOrderOf h2AB β,
    ← gcd_QA_inter_of_coprime (fun p hp q hq hpq => hS p (hA hp) q (hB hq) hpq)]
  exact Nat.dvd_gcd
    ((mem_sigmaSubAFinset_iff_dvd_addOrderOf (fun q hq => h2 q (hA hq)) β).mp hβA)
    ((mem_sigmaSubAFinset_iff_dvd_addOrderOf (fun q hq => h2 q (hB hq)) β).mp hβB)

/-! ## The nonce lemma for the strata -/

/-- **Quantitative denominator orthogonality for the strata** (Tao's `ortho`(ii), arithmetic core,
strata form).  For a family `A : ι → Finset ℕ` of subsets of a pairwise coprime `S` carrying a
nonce, and points `α i` of the strata `Σ_{A i}`, the signed sum `Σ_i sgn_i • α_i` is at distance at
least `1/∏_i Q_{A i}` from `0` in the circle.

Proof: if the sum vanished, multiplying it by `Q_{A₀}` (`A₀` = the union of all the `A i`, `i ≠ j`,
where the nonce `q ∈ A j` sits) kills every term but the `j`-th; so `α j ∈ 𝕋[Q_{A₀}]`, and with
`α j ∈ 𝕋[Q_{A j}]` this puts `α j ∈ 𝕋[Q_{A j ∩ A₀}]` with `A j ∩ A₀ ⊊ A j` (since `q ∈ A j \ A₀`),
contradicting the stratum condition. -/
theorem sigmaStrata_nonce_sum_norm_ge {ι : Type*} [Fintype ι] {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : ι → Finset ℕ} (hA : ∀ i, A i ⊆ S)
    {sgn : ι → ℤ} (hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1)
    {α : ι → Circle} (hα : ∀ i, α i ∈ (sigmaStrataFinset (A i) : Set Circle))
    (hnonce : ∃ j : ι, ∃ q ∈ A j, ∀ i, i ≠ j → q ∉ A i) :
    1 / ((∏ i, QA (A i) : ℕ) : ℝ) ≤ ‖∑ i, sgn i • α i‖ := by
  classical
  have h2' : ∀ i, ∀ q ∈ A i, 2 ≤ q := fun i q hq => h2 q (hA i hq)
  have hsubA : ∀ i, α i ∈ sigmaSubA (A i) := fun i =>
    coe_sigmaStrataFinset_subset_sigmaSubA _ (hα i)
  have hsub : ∀ i, α i ∈ sigmaSubAFinset (A i) := fun i =>
    sigmaStrataFinset_subset_sigmaSubAFinset _ (Finset.mem_coe.mp (hα i))
  have hkill : ∀ i, (QA (A i) : ℤ) • α i = 0 := fun i =>
    (mem_sigmaSubAFinset_iff_zsmul_eq_zero (h2' i) (α i)).mp (hsub i)
  -- the signed sum does not vanish
  have hne : (∑ i, sgn i • α i) ≠ 0 := by
    intro hzero
    obtain ⟨j, q₀, hq₀, huniq⟩ := hnonce
    set A₀ : Finset ℕ := Finset.univ.biUnion (fun i : ι => if i = j then ∅ else A i) with hA₀def
    have hA₀sub : A₀ ⊆ S := by
      intro x hx
      rw [hA₀def, Finset.mem_biUnion] at hx
      obtain ⟨i, -, hxi⟩ := hx
      by_cases hi : i = j
      · rw [if_pos hi] at hxi; exact absurd hxi (Finset.notMem_empty x)
      · rw [if_neg hi] at hxi; exact hA i hxi
    have hq₀A₀ : q₀ ∉ A₀ := by
      intro hx
      rw [hA₀def, Finset.mem_biUnion] at hx
      obtain ⟨i, -, hxi⟩ := hx
      by_cases hi : i = j
      · rw [if_pos hi] at hxi; exact Finset.notMem_empty q₀ hxi
      · rw [if_neg hi] at hxi; exact absurd hxi (huniq i hi)
    have hAjsub : ∀ i, i ≠ j → A i ⊆ A₀ := by
      intro i hi x hx
      rw [hA₀def, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, by rw [if_neg hi]; exact hx⟩
    have h2A₀ : ∀ q ∈ A₀, 2 ≤ q := fun q hq => h2 q (hA₀sub hq)
    -- multiplying the vanishing sum by `Q_{A₀}` kills every term but the `j`-th
    have hkillA₀ : ∀ i, i ≠ j → QA A₀ • α i = 0 := by
      intro i hi
      obtain ⟨m, hm⟩ := QA_dvd_of_subset (hAjsub i hi)
      have h : QA (A i) • α i = 0 := by
        rw [← natCast_zsmul]; exact hkill i
      calc QA A₀ • α i = (QA (A i) * m) • α i := by rw [hm]
        _ = m • (QA (A i) • α i) := mul_nsmul (α i) (QA (A i)) m
        _ = 0 := by rw [h, nsmul_zero]
    have hkillj : (QA A₀ : ℤ) • α j = 0 := by
      have h0 : (QA A₀ : ℤ) • (∑ i, sgn i • α i) = 0 := by rw [hzero, smul_zero]
      rw [Finset.smul_sum] at h0
      have hother : ∀ i, i ≠ j → (QA A₀ : ℤ) • (sgn i • α i) = 0 := by
        intro i hi
        have h1 : (QA A₀ : ℤ) • α i = 0 := by rw [natCast_zsmul]; exact hkillA₀ i hi
        rw [smul_comm (QA A₀ : ℤ) (sgn i) (α i), h1, smul_zero]
      rw [Finset.sum_eq_single j (fun i _ hi => hother i hi)
        (fun hj => absurd (Finset.mem_univ j) hj)] at h0
      rcases hsgn j with h | h
      · rwa [h, one_smul] at h0
      · rw [h, neg_one_smul, smul_neg] at h0
        exact neg_eq_zero.mp h0
    -- `α j` lies in the strictly smaller torsion subgroup `𝕋[Q_{A j ∩ A₀}]`
    have hαA₀ : α j ∈ sigmaSubAFinset A₀ :=
      (mem_sigmaSubAFinset_iff_zsmul_eq_zero h2A₀ (α j)).mpr hkillj
    have hinter : α j ∈ sigmaSubAFinset (A j ∩ A₀) :=
      sigmaSubAFinset_inter_mem' h2 hS (hA j) hA₀sub (hsub j) hαA₀
    have hne' : A j ∩ A₀ ≠ A j := by
      intro heq
      have hq : q₀ ∈ A j ∩ A₀ := by rw [heq]; exact hq₀
      exact hq₀A₀ (Finset.mem_inter.mp hq).2
    exact not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset Finset.inter_subset_left hne' hinter
      (Finset.mem_coe.mp (hα j))
  -- quantitative separation: the sum is a non-zero point of denominator `∏_i Q_{A i}`
  have hQ1 : ∀ i, 1 ≤ QA (A i) := fun i => one_le_QA (h2' i)
  have hQne : ∀ i, QA (A i) ≠ 0 := fun i => QA_ne_zero_of_two_le (h2' i)
  choose a ha using fun i => exists_arcPt_of_zsmul_eq_zero (hQne i) (hkill i)
  have hsum_eq : (∑ i, sgn i • α i)
      = arcPt (∏ i, QA (A i)) (∑ i, sgn i * a i * (((∏ j, QA (A j)) / QA (A i) : ℕ) : ℤ)) := by
    rw [show (∑ i, sgn i • α i) = ∑ i, sgn i • arcPt (QA (A i)) (a i) from
      Finset.sum_congr rfl (fun i _ => by rw [ha i])]
    exact sum_smul_arcPt_eq_arcPt hQ1 a sgn
  rw [hsum_eq]
  exact norm_arcPt_ge (Finset.one_le_prod₀ (fun i _ => hQ1 i)) (by rw [hsum_eq] at hne; exact hne)

/-- **The `ε`-perturbed nonce lemma for the strata** (Tao's `ortho`(ii) as used).  Perturbing the
stratum points by real numbers `θ_i` with `|θ_i| ≤ ε` cannot create a vanishing signed sum, as long
as `#ι · ε < 1/∏_i Q_{A i}` — the perturbation is smaller than the separation supplied by
`sigmaStrata_nonce_sum_norm_ge`. -/
theorem sigmaStrata_nonce_sum_perturbed_ne_zero {ι : Type*} [Fintype ι] {S : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : ι → Finset ℕ} (hA : ∀ i, A i ⊆ S)
    {sgn : ι → ℤ} (hsgn : ∀ i, sgn i = 1 ∨ sgn i = -1)
    {α : ι → Circle} (hα : ∀ i, α i ∈ (sigmaStrataFinset (A i) : Set Circle))
    (hnonce : ∃ j : ι, ∃ q ∈ A j, ∀ i, i ≠ j → q ∉ A i)
    {θ : ι → ℝ} {ε : ℝ} (hθ : ∀ i, |θ i| ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) * ε < 1 / ((∏ i, QA (A i) : ℕ) : ℝ)) :
    (∑ i, sgn i • (α i + (θ i : Circle))) ≠ 0 := by
  have hbase : 1 / ((∏ i, QA (A i) : ℕ) : ℝ) ≤ ‖∑ i, sgn i • α i‖ :=
    sigmaStrata_nonce_sum_norm_ge h2 hS hA hsgn hα hnonce
  have hsplit : (∑ i, sgn i • (α i + (θ i : Circle)))
      = (∑ i, sgn i • α i) + ∑ i, sgn i • (θ i : Circle) := by
    rw [Finset.sum_congr rfl (fun i _ => smul_add (sgn i) _ _), Finset.sum_add_distrib]
  have hnorm : ‖∑ i, sgn i • (θ i : Circle)‖ ≤ (Fintype.card ι : ℝ) * ε := by
    calc ‖∑ i, sgn i • (θ i : Circle)‖ ≤ ∑ i, ‖sgn i • (θ i : Circle)‖ := norm_sum_le _ _
      _ = ∑ i, ‖(θ i : Circle)‖ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rcases hsgn i with h | h <;> simp [h]
      _ ≤ ∑ i, |θ i| := Finset.sum_le_sum fun i _ => norm_circle_coe_le_abs (θ i)
      _ ≤ ∑ i, ε := Finset.sum_le_sum fun i _ => hθ i
      _ = (Fintype.card ι : ℝ) * ε := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  intro hzero
  have hsum0 : (∑ i, sgn i • α i) + ∑ i, sgn i • (θ i : Circle) = 0 := by
    rw [← hsplit]; exact hzero
  have hle : ‖(∑ i, sgn i • α i)‖
      ≤ ‖(∑ i, sgn i • α i) + ∑ i, sgn i • (θ i : Circle)‖
        + ‖∑ i, sgn i • (θ i : Circle)‖ := by
    have h := norm_add_le ((∑ i, sgn i • α i) + ∑ i, sgn i • (θ i : Circle))
      (-(∑ i, sgn i • (θ i : Circle)))
    rw [norm_neg] at h
    have h2' : ((∑ i, sgn i • α i) + ∑ i, sgn i • (θ i : Circle))
        + -(∑ i, sgn i • (θ i : Circle)) = ∑ i, sgn i • α i := by abel
    rwa [h2'] at h
  rw [hsum0, norm_zero, zero_add] at hle
  linarith [hbase, hnorm, hle, hsmall]

/-! ## The petal lemma (with core shift) for the strata -/

/-- **Quantitative petal separation with a core shift, for the strata.**  Let `S` be a finite set of
pairwise coprime integers `≥ 2`, `A₀ ⊆ S` a core, `P : ι → Finset ℕ` pairwise disjoint petals
disjoint from `A₀`.  If `α i, β i ∈ Σ_{P i}` and `γ i, δ i ∈ Σ_{A₀}` are stratum points and
`α j ≠ β j` for some `j`, then

`1/(Q_{A₀} · ∏_i Q_{P i}) ≤ ‖Σ_i (γ i + α i) − Σ_i (δ i + β i)‖`.

Proof: multiply by `M = Q_{A₀} · ∏_{i ≠ j} Q_{P i}`, which kills every term except the `j`-th petal
difference; `M` is coprime to `Q_{P j}` and therefore acts injectively on `𝕋[Q_{P j}]`, so
`M • (α j − β j) ≠ 0`, a contradiction. -/
theorem sigmaStrata_petal_sum_shift_norm_ge {ι : Type*} [Fintype ι] {S A₀ : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : ι → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {α β : ι → Circle} (hα : ∀ i, α i ∈ (sigmaStrataFinset (P i) : Set Circle))
    (hβ : ∀ i, β i ∈ (sigmaStrataFinset (P i) : Set Circle))
    (hne : ∃ i, α i ≠ β i)
    {γ δ : ι → Circle} (hγ : ∀ i, γ i ∈ (sigmaStrataFinset A₀ : Set Circle))
    (hδ : ∀ i, δ i ∈ (sigmaStrataFinset A₀ : Set Circle)) :
    1 / ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) ≤
      ‖(∑ i, (γ i + α i)) - (∑ i, (δ i + β i))‖ := by
  classical
  obtain ⟨j, hnej⟩ := hne
  have hA₀2 : ∀ q ∈ A₀, 2 ≤ q := fun q hq => h2 q (hA₀ hq)
  have hP2 : ∀ i, ∀ q ∈ P i, 2 ≤ q := fun i q hq => h2 q (hP i hq)
  have hQA₀1 : 1 ≤ QA A₀ := one_le_QA hA₀2
  have hQAi1 : ∀ i, 1 ≤ QA (P i) := fun i => one_le_QA (hP2 i)
  set Q : ℕ := QA A₀ * ∏ i, QA (P i) with hQ
  have hQ1 : 1 ≤ Q := by
    rw [hQ]
    exact one_le_mul hQA₀1 (Finset.one_le_prod₀ fun i _ => hQAi1 i)
  have hdvd₀ : QA A₀ ∣ Q := by rw [hQ]; exact dvd_mul_right _ _
  have hdvdP : ∀ i, QA (P i) ∣ Q := by
    intro i
    rw [hQ]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  -- torsion-subgroup memberships
  have hsubα : ∀ i, α i ∈ sigmaSubA (P i) := fun i =>
    coe_sigmaStrataFinset_subset_sigmaSubA _ (hα i)
  have hsubβ : ∀ i, β i ∈ sigmaSubA (P i) := fun i =>
    coe_sigmaStrataFinset_subset_sigmaSubA _ (hβ i)
  have hsubγ : ∀ i, γ i ∈ sigmaSubA A₀ := fun i =>
    coe_sigmaStrataFinset_subset_sigmaSubA _ (hγ i)
  have hsubδ : ∀ i, δ i ∈ sigmaSubA A₀ := fun i =>
    coe_sigmaStrataFinset_subset_sigmaSubA _ (hδ i)
  have hkillα : ∀ i, (QA (P i) : ℤ) • α i = 0 := fun i =>
    (mem_sigmaSubAFinset_iff_zsmul_eq_zero (hP2 i) (α i)).mp
      (sigmaStrataFinset_subset_sigmaSubAFinset _ (Finset.mem_coe.mp (hα i)))
  have hkillβ : ∀ i, (QA (P i) : ℤ) • β i = 0 := fun i =>
    (mem_sigmaSubAFinset_iff_zsmul_eq_zero (hP2 i) (β i)).mp
      (sigmaStrataFinset_subset_sigmaSubAFinset _ (Finset.mem_coe.mp (hβ i)))
  have hkillγ : ∀ i, (QA A₀ : ℤ) • γ i = 0 := fun i =>
    (mem_sigmaSubAFinset_iff_zsmul_eq_zero hA₀2 (γ i)).mp
      (sigmaStrataFinset_subset_sigmaSubAFinset _ (Finset.mem_coe.mp (hγ i)))
  have hkillδ : ∀ i, (QA A₀ : ℤ) • δ i = 0 := fun i =>
    (mem_sigmaSubAFinset_iff_zsmul_eq_zero hA₀2 (δ i)).mp
      (sigmaStrataFinset_subset_sigmaSubAFinset _ (Finset.mem_coe.mp (hδ i)))
  -- representations as arc points
  choose a hαeq using fun i =>
    exists_arcPt_of_zsmul_eq_zero (QA_ne_zero_of_two_le (hP2 i)) (hkillα i)
  choose b hβeq using fun i =>
    exists_arcPt_of_zsmul_eq_zero (QA_ne_zero_of_two_le (hP2 i)) (hkillβ i)
  choose c hγeq using fun i =>
    exists_arcPt_of_zsmul_eq_zero (QA_ne_zero_of_two_le hA₀2) (hkillγ i)
  choose d hδeq using fun i =>
    exists_arcPt_of_zsmul_eq_zero (QA_ne_zero_of_two_le hA₀2) (hkillδ i)
  -- the sum, split into the core part and the petal part
  have hsplit : (∑ i, (γ i + α i)) - (∑ i, (δ i + β i))
      = (∑ i, (γ i - δ i)) + (∑ i, (α i - β i)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  have hrep₁ : (∑ i, (γ i - δ i)) = arcPt Q (∑ i, (c i - d i) * (((Q / QA A₀ : ℕ)) : ℤ)) := by
    have h1 : (∑ i, (γ i - δ i)) = ∑ i, arcPt (QA A₀) (c i - d i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hγeq i, hδeq i, arcPt_sub_same]
    rw [h1]
    exact sum_arcPt_commonDenom (fun _ => hQA₀1) hQ1 (fun _ => hdvd₀) _
  have hrep₂ : (∑ i, (α i - β i)) = arcPt Q (∑ i, (a i - b i) * (((Q / QA (P i) : ℕ)) : ℤ)) := by
    have h1 : (∑ i, (α i - β i)) = ∑ i, arcPt (QA (P i)) (a i - b i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hαeq i, hβeq i, arcPt_sub_same]
    rw [h1]
    exact sum_arcPt_commonDenom hQAi1 hQ1 hdvdP _
  have hrep : (∑ i, (γ i + α i)) - (∑ i, (δ i + β i))
      = arcPt Q ((∑ i, (c i - d i) * (((Q / QA A₀ : ℕ)) : ℤ))
          + (∑ i, (a i - b i) * (((Q / QA (P i) : ℕ)) : ℤ))) := by
    rw [hsplit, hrep₁, hrep₂, arcPt_add]
  -- the sum is non-zero: multiply by the denominators of all terms except the `j`-th petal
  have hWne : (∑ i, (γ i + α i)) - (∑ i, (δ i + β i)) ≠ 0 := by
    obtain ⟨M, hM⟩ : ∃ M : ℕ, M = QA A₀ * (∏ i ∈ Finset.univ.erase j, QA (P i)) := ⟨_, rfl⟩
    have hdvdM₀ : QA A₀ ∣ M := by rw [hM]; exact dvd_mul_right _ _
    have hdvdMi : ∀ i, i ≠ j → QA (P i) ∣ M := by
      intro i hij
      rw [hM]
      exact dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)) _
    have hkill₀ : ∀ {x : Circle}, x ∈ sigmaSubA A₀ → (M : ℤ) • x = 0 := fun hx =>
      zsmul_eq_zero_of_dvd_QA (fun q hq => by have := hA₀2 q hq; omega) hdvdM₀ hx
    have hkillP : ∀ i, i ≠ j → ∀ {x : Circle}, x ∈ sigmaSubA (P i) → (M : ℤ) • x = 0 :=
      fun i hij x hx =>
        zsmul_eq_zero_of_dvd_QA (fun q hq => by have := hP2 i q hq; omega) (hdvdMi i hij) hx
    intro hW
    have h1 : (M : ℤ) • ((∑ i, (γ i + α i)) - (∑ i, (δ i + β i))) = 0 := by rw [hW, smul_zero]
    rw [smul_sub, Finset.smul_sum, Finset.smul_sum] at h1
    have hsumA : (∑ i, (M : ℤ) • (γ i + α i)) = (M : ℤ) • (γ j + α j) := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_) (fun hj => absurd (Finset.mem_univ j) hj)
      rw [smul_add, hkill₀ (hsubγ i), hkillP i hij (hsubα i), add_zero]
    have hsumB : (∑ i, (M : ℤ) • (δ i + β i)) = (M : ℤ) • (δ j + β j) := by
      refine Finset.sum_eq_single j (fun i _ hij => ?_) (fun hj => absurd (Finset.mem_univ j) hj)
      rw [smul_add, hkill₀ (hsubδ i), hkillP i hij (hsubβ i), add_zero]
    have h2M : (M : ℤ) • (α j - β j) = 0 := by
      rw [hsumA, hsumB, smul_add, smul_add, hkill₀ (hsubγ j), hkill₀ (hsubδ j),
        zero_add, zero_add] at h1
      rwa [← smul_sub] at h1
    have hcopM : Nat.Coprime M (QA (P j)) := by
      rw [hM]
      refine Nat.Coprime.mul_left ?_ ?_
      · exact coprime_QA_of_pairwise (A := A₀) (B := P j) hS hA₀ (hP j) (hdisjA j)
      · exact Nat.Coprime.prod_left fun i hi =>
          coprime_QA_of_pairwise (A := P i) (B := P j) hS (hP i) (hP j)
            (hdisjP i j (Finset.mem_erase.mp hi).1)
    have hnonzero : (M : ℤ) • (α j - β j) ≠ 0 := by
      rw [smul_sub]
      exact sub_ne_zero.mpr
        (zsmul_ne_of_ne_of_mem_sigmaSubA (A := P j) (fun q hq => by have := hP2 j q hq; omega)
          hcopM (hsubα j) (hsubβ j) hnej)
    exact hnonzero h2M
  -- conclusion: the sum is a non-zero point of denominator dividing `Q`
  rw [hrep]
  refine norm_arcPt_ge hQ1 ?_
  rw [← hrep]
  exact hWne

/-- **The `ε`-perturbed petal non-vanishing with a core shift, for the strata** — the arithmetic
verification of Tao's `ortho`(iii) in the presence of the core `Σ_{⊆ A₀}`, for Tao's strata. -/
theorem sigmaStrata_petal_sum_shift_perturbed_ne_zero {ι : Type*} [Fintype ι] {S A₀ : Finset ℕ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) {P : ι → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisjP : ∀ i j : ι, i ≠ j → Disjoint (P i) (P j))
    (hdisjA : ∀ i, Disjoint A₀ (P i))
    {α β : ι → Circle} (hα : ∀ i, α i ∈ (sigmaStrataFinset (P i) : Set Circle))
    (hβ : ∀ i, β i ∈ (sigmaStrataFinset (P i) : Set Circle))
    (hne : ∃ i, α i ≠ β i)
    {γ δ : ι → Circle} (hγ : ∀ i, γ i ∈ (sigmaStrataFinset A₀ : Set Circle))
    (hδ : ∀ i, δ i ∈ (sigmaStrataFinset A₀ : Set Circle))
    {θ θ' : ι → ℝ} {ε : ℝ} (hθ : ∀ i, |θ i| ≤ ε) (hθ' : ∀ i, |θ' i| ≤ ε)
    (hsmall : 2 * (Fintype.card ι : ℝ) * ε * ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) < 1) :
    (∑ i, ((γ i + α i + (θ i : Circle)) - (δ i + β i + (θ' i : Circle)))) ≠ 0 := by
  have hQpos : (0 : ℝ) < ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) := by
    have h1 : 1 ≤ QA A₀ * ∏ i, QA (P i) :=
      one_le_mul (one_le_QA fun q hq => h2 q (hA₀ hq))
        (Finset.one_le_prod₀ fun i _ => one_le_QA fun q hq => h2 q (hP i hq))
    exact_mod_cast (by omega : 0 < QA A₀ * ∏ i, QA (P i))
  have hbase : 1 / ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) ≤
      ‖(∑ i, (γ i + α i)) - (∑ i, (δ i + β i))‖ :=
    sigmaStrata_petal_sum_shift_norm_ge h2 hS hA₀ hP hdisjP hdisjA hα hβ hne hγ hδ
  have hsmall' : 2 * (Fintype.card ι : ℝ) * ε <
      1 / ((QA A₀ * (∏ i, QA (P i)) : ℕ) : ℝ) := by
    rw [lt_div_iff₀ hQpos]
    exact hsmall
  have hsplit : (∑ i, ((γ i + α i + (θ i : Circle)) - (δ i + β i + (θ' i : Circle))))
      = ((∑ i, (γ i + α i)) - (∑ i, (δ i + β i)))
        + ∑ i, ((θ i : Circle) - (θ' i : Circle)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  have hnorm : ‖∑ i, ((θ i : Circle) - (θ' i : Circle))‖ ≤ 2 * (Fintype.card ι : ℝ) * ε := by
    calc ‖∑ i, ((θ i : Circle) - (θ' i : Circle))‖
        ≤ ∑ i, ‖(θ i : Circle) - (θ' i : Circle)‖ := norm_sum_le _ _
      _ ≤ ∑ i, (|θ i| + |θ' i|) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc ‖(θ i : Circle) - (θ' i : Circle)‖
                ≤ ‖(θ i : Circle)‖ + ‖(θ' i : Circle)‖ := norm_sub_le _ _
              _ ≤ |θ i| + |θ' i| := add_le_add (norm_circle_coe_le_abs _)
                    (norm_circle_coe_le_abs _)
      _ ≤ ∑ _i : ι, (ε + ε) := Finset.sum_le_sum fun i _ => add_le_add (hθ i) (hθ' i)
      _ = 2 * (Fintype.card ι : ℝ) * ε := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
  intro hzero
  have hsum0 : ((∑ i, (γ i + α i)) - (∑ i, (δ i + β i)))
      + ∑ i, ((θ i : Circle) - (θ' i : Circle)) = 0 := by
    rw [← hsplit]; exact hzero
  have hle : ‖(∑ i, (γ i + α i)) - (∑ i, (δ i + β i))‖
      ≤ ‖((∑ i, (γ i + α i)) - (∑ i, (δ i + β i)))
          + ∑ i, ((θ i : Circle) - (θ' i : Circle))‖
        + ‖∑ i, ((θ i : Circle) - (θ' i : Circle))‖ := by
    have h := norm_add_le
      (((∑ i, (γ i + α i)) - (∑ i, (δ i + β i))) + ∑ i, ((θ i : Circle) - (θ' i : Circle)))
      (-(∑ i, ((θ i : Circle) - (θ' i : Circle))))
    rw [norm_neg] at h
    have h2' : (((∑ i, (γ i + α i)) - (∑ i, (δ i + β i)))
        + ∑ i, ((θ i : Circle) - (θ' i : Circle)))
        + -(∑ i, ((θ i : Circle) - (θ' i : Circle)))
        = (∑ i, (γ i + α i)) - (∑ i, (δ i + β i)) := by abel
    rwa [h2'] at h
  rw [hsum0, norm_zero, zero_add] at hle
  linarith [hbase, hnorm, hle, hsmall']

end Work.BourgainPlan.IonescuWainger
