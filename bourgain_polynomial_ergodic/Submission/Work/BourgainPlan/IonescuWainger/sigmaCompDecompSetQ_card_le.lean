import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs
import Submission.Work.BourgainPlan.IonescuWainger.sigmaComp_repr_count

/-!
# The `2^k` counting bound on `ZMod (Q_S)` (Tao's `ortho-apply`(i))

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
§4 (Theorem `ortho-apply`(i)); see `REFS/Tao_2008.05066_IonescuWainger.tex` and
`Submission/Work/BourgainPlan/IonescuWainger/PLAN.md` (A4).

The circle-valued form of the counting bound is `sigmaComp_repr_count` (`ArcSep.lean`): the number of
sets `A₀ ⊆ S` with `A₀.card ≤ k` for which a point `β ∈ 𝕋` admits a decomposition
`β = α₀ + α`, `α₀ ∈ Σ_{A₀}`, `α ∈ Σ_{(A₀)}`, is at most `2 ^ k`.  Here we prove the same statement
for the *finite cyclic group* form used by the `ZMod`-valued orthogonality machinery of
`ZModArcs.lean`: the number of `A₀` for which `β ∈ ZMod (Q_S)` admits a decomposition
`β = α₀ + α` with `α₀ ∈ sigmaAQ (QA S) A₀` and `α ∈ sigmaCompQ (QA S) S k A₀` is at most `2 ^ k`.

The proof is the `ZMod` transcription of the circle argument.  The arithmetic input is that
`x = a · (Q_S / Q_A) ∈ ZMod (Q_S)` with `gcd(a, Q_A) = 1` has *exact* additive order `Q_A`
(`dvd_of_sigmaAQ_mul_eq_zero` / `sigmaAQ_mul_QA_eq_zero`): it is killed by `Q_A` and by nothing
smaller.  Consequently, if `β = α₀ + α₁` with `αᵢ ∈ Σ_{Aᵢ}` for disjoint `A₀, A₁ ⊆ S`, then `β` is
killed by exactly the multiples of `Q_{A₀} Q_{A₁}`; hence the set `A₀ ∪ A₁` is determined by `β`,
and every admissible `A₀` is a subset of it (of size `≤ k`), giving the bound `2 ^ k`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Elementary description of `sigmaAQ` -/

/-- Unfolding of membership in `sigmaAQ Q A`: the points `a · (Q/Q_A) ∈ ZMod Q` with
`a < Q_A` and `gcd(a, Q_A) = 1`. -/
lemma sigmaAQ_mem_iff {Q : ℕ} {A : Finset ℕ} {x : ZMod Q} :
    x ∈ sigmaAQ Q A ↔ ∃ a < QA A, Nat.Coprime a (QA A) ∧ arcLift Q A (a : ℤ) = x := by
  simp only [sigmaAQ, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨a, ⟨ha, hcop⟩, rfl⟩
    exact ⟨a, ha, hcop, rfl⟩
  · rintro ⟨a, ha, hcop, rfl⟩
    exact ⟨a, ⟨ha, hcop⟩, rfl⟩

/-- `arcLift Q A a` (with `a : ℕ`) is the integer point `a · (Q / Q_A)`. -/
lemma arcLift_eq_natCast {Q : ℕ} {A : Finset ℕ} (a : ℕ) :
    arcLift Q A (a : ℤ) = ((a * (Q / QA A) : ℕ) : ZMod Q) := by
  simp only [arcLift, Int.cast_natCast, Nat.cast_mul]

/-! ## The exact order of the points of `Σ_A` -/

/-- **`Q_A` kills `Σ_A`**: for `Q_A ∣ Q`, every point of `sigmaAQ Q A` is annihilated by `Q_A`. -/
lemma sigmaAQ_mul_QA_eq_zero {Q : ℕ} {A : Finset ℕ} (hdiv : QA A ∣ Q) {x : ZMod Q}
    (hx : x ∈ sigmaAQ Q A) : (QA A : ZMod Q) * x = 0 := by
  obtain ⟨a, -, -, rfl⟩ := sigmaAQ_mem_iff.mp hx
  rw [arcLift_eq_natCast, ← Nat.cast_mul]
  have hrew : QA A * (a * (Q / QA A)) = a * Q := by
    rw [← mul_assoc, mul_comm (QA A) a, mul_assoc, Nat.mul_div_cancel' hdiv]
  rw [hrew, Nat.cast_mul, ZMod.natCast_self, mul_zero]

/-- **`Σ_A` has exact denominator `Q_A`**: for `Q_A ∣ Q` and `Q ≠ 0`, a point of `sigmaAQ Q A` is
killed only by the multiples of `Q_A`. -/
lemma dvd_of_sigmaAQ_mul_eq_zero {Q : ℕ} [NeZero Q] {A : Finset ℕ} (hdiv : QA A ∣ Q)
    {x : ZMod Q} (hx : x ∈ sigmaAQ Q A) {n : ℕ} (hn : (n : ZMod Q) * x = 0) : QA A ∣ n := by
  obtain ⟨a, -, hcop, rfl⟩ := sigmaAQ_mem_iff.mp hx
  rw [arcLift_eq_natCast, ← Nat.cast_mul] at hn
  have hmul : QA A * (Q / QA A) = Q := Nat.mul_div_cancel' hdiv
  have hk : (0 : ℕ) < Q / QA A := by
    rcases Nat.eq_zero_or_pos (Q / QA A) with h0 | h0
    · rw [h0, mul_zero] at hmul
      exact absurd hmul.symm (NeZero.ne Q)
    · exact h0
  have hdvdZ : (Q : ℤ) ∣ ((n * (a * (Q / QA A)) : ℕ) : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ Q).mp (by rw [Int.cast_natCast]; exact hn)
  have hdvd : Q ∣ n * (a * (Q / QA A)) := Int.natCast_dvd_natCast.mp hdvdZ
  have hdvd' : QA A * (Q / QA A) ∣ (n * a) * (Q / QA A) := by
    rw [hmul]
    have heq : n * (a * (Q / QA A)) = (n * a) * (Q / QA A) := by ring
    rwa [heq] at hdvd
  have hdvd'' : QA A ∣ n * a := Nat.dvd_of_mul_dvd_mul_right hk hdvd'
  exact hcop.symm.dvd_of_dvd_mul_right hdvd''

/-- Points killed by two coprime `Q_A`, `Q_B` vanish (Bézout). -/
lemma eq_zero_of_coprime_mul_eq_zero {Q : ℕ} {A B : Finset ℕ} (hcop : Nat.Coprime (QA A) (QA B))
    {y : ZMod Q} (hA : (QA A : ZMod Q) * y = 0) (hB : (QA B : ZMod Q) * y = 0) : y = 0 := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have h1 : (u * (QA A : ℤ)) • y = 0 := by
    rw [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, hA, mul_zero]
  have h2 : (v * (QA B : ℤ)) • y = 0 := by
    rw [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, hB, mul_zero]
  calc y = (1 : ℤ) • y := (one_zsmul y).symm
    _ = ((u * (QA A : ℤ)) + (v * (QA B : ℤ))) • y := by rw [huv]
    _ = (u * (QA A : ℤ)) • y + (v * (QA B : ℤ)) • y := add_zsmul _ _ _
    _ = 0 := by rw [h1, h2, add_zero]

/-- **The exact order of a sum of two exact-denominator points.**  For disjoint `A₀, A₁ ⊆ S` and
`xᵢ ∈ Σ_{Aᵢ}`, the sum `x₀ + x₁ ∈ ZMod (Q_S)` is killed by exactly the multiples of
`Q_{A₀} · Q_{A₁}`. -/
lemma nsmul_add_eq_zero_iff_QA_mul_dvd {S : Finset ℕ} [NeZero (QA S)]
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ A₁ : Finset ℕ} (hA₀ : A₀ ⊆ S) (hA₁ : A₁ ⊆ S) (hdisj : Disjoint A₀ A₁)
    {x₀ x₁ : ZMod (QA S)} (hx₀ : x₀ ∈ sigmaAQ (QA S) A₀) (hx₁ : x₁ ∈ sigmaAQ (QA S) A₁)
    (n : ℕ) : n • (x₀ + x₁) = 0 ↔ QA A₀ * QA A₁ ∣ n := by
  have hdiv₀ : QA A₀ ∣ QA S := Finset.prod_dvd_prod_of_subset A₀ S (fun i => i) hA₀
  have hdiv₁ : QA A₁ ∣ QA S := Finset.prod_dvd_prod_of_subset A₁ S (fun i => i) hA₁
  have hcop : Nat.Coprime (QA A₀) (QA A₁) :=
    coprime_QA_of_disjoint fun q hq q' hq' =>
      hS q (hA₀ hq) q' (hA₁ hq') (fun he => Finset.disjoint_left.mp hdisj hq (he ▸ hq'))
  constructor
  · intro hn
    have hy₀ : (QA A₀ : ZMod (QA S)) * (n • x₀) = 0 := by
      rw [nsmul_eq_mul, mul_left_comm (QA A₀ : ZMod (QA S)) (n : ZMod (QA S)) x₀,
        sigmaAQ_mul_QA_eq_zero hdiv₀ hx₀, mul_zero]
    have hnx : n • x₀ = -(n • x₁) := by
      have h := hn
      rw [nsmul_add] at h
      exact eq_neg_of_add_eq_zero_left h
    have hy₁ : (QA A₁ : ZMod (QA S)) * (n • x₀) = 0 := by
      have hx₁' : (QA A₁ : ZMod (QA S)) * (n • x₁) = 0 := by
        rw [nsmul_eq_mul, mul_left_comm (QA A₁ : ZMod (QA S)) (n : ZMod (QA S)) x₁,
          sigmaAQ_mul_QA_eq_zero hdiv₁ hx₁, mul_zero]
      rw [hnx, mul_neg, hx₁', neg_zero]
    have hy : n • x₀ = 0 := eq_zero_of_coprime_mul_eq_zero hcop hy₀ hy₁
    have hx₀' : (n : ZMod (QA S)) * x₀ = 0 := by
      rwa [nsmul_eq_mul] at hy
    have hx₁'' : (n : ZMod (QA S)) * x₁ = 0 := by
      have h : n • x₁ = 0 := by
        have h' : -(n • x₁) = 0 := by rw [← hnx]; exact hy
        exact neg_eq_zero.mp h'
      rwa [nsmul_eq_mul] at h
    exact hcop.mul_dvd_of_dvd_of_dvd
      (dvd_of_sigmaAQ_mul_eq_zero hdiv₀ hx₀ hx₀')
      (dvd_of_sigmaAQ_mul_eq_zero hdiv₁ hx₁ hx₁'')
  · intro hdvd
    obtain ⟨s, hs⟩ := hdvd
    have h0 : n • x₀ = 0 := by
      have hn : n = (QA A₀) * (QA A₁ * s) := by rw [hs]; ring
      rw [hn, mul_nsmul]
      have hz : (QA A₀) • x₀ = 0 := by
        rw [nsmul_eq_mul]
        exact sigmaAQ_mul_QA_eq_zero hdiv₀ hx₀
      rw [hz, smul_zero]
    have h1 : n • x₁ = 0 := by
      have hn : n = (QA A₁) * (QA A₀ * s) := by rw [hs]; ring
      rw [hn, mul_nsmul]
      have hz : (QA A₁) • x₁ = 0 := by
        rw [nsmul_eq_mul]
        exact sigmaAQ_mul_QA_eq_zero hdiv₁ hx₁
      rw [hz, smul_zero]
    rw [smul_add, h0, h1, add_zero]

/-! ## The exact denominator of a sum is determined by the sum -/

/-- **The set `A₀ ∪ A₁` is determined by the sum.**  If `x₀ + x₁ = y₀ + y₁` with
`x₀ ∈ Σ_A`, `x₁ ∈ Σ_B`, `y₀ ∈ Σ_C`, `y₁ ∈ Σ_D` for pairwise disjoint `A, B` resp. `C, D` inside the
pairwise coprime set `S`, then `A ∪ B = C ∪ D`.

Indeed, writing `β` for the common sum, `β` is killed by exactly the multiples of `Q_{A∪B}` and
also by exactly the multiples of `Q_{C∪D}` (`nsmul_add_eq_zero_iff_QA_mul_dvd`), so
`Q_{A∪B} = Q_{C∪D}`, and `Q` is injective on subsets of `S` (`QA_injective`). -/
lemma sigmaUnion_unique_Q {S : Finset ℕ} [NeZero (QA S)]
    (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A B C D : Finset ℕ} (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S) (hD : D ⊆ S)
    (hdAB : Disjoint A B) (hdCD : Disjoint C D)
    {x₀ x₁ y₀ y₁ : ZMod (QA S)} (hx₀ : x₀ ∈ sigmaAQ (QA S) A) (hx₁ : x₁ ∈ sigmaAQ (QA S) B)
    (hy₀ : y₀ ∈ sigmaAQ (QA S) C) (hy₁ : y₁ ∈ sigmaAQ (QA S) D)
    (heq : x₀ + x₁ = y₀ + y₁) : A ∪ B = C ∪ D := by
  have h1 : QA A * QA B ∣ QA C * QA D :=
    (nsmul_add_eq_zero_iff_QA_mul_dvd hS hA hB hdAB hx₀ hx₁ (QA C * QA D)).mp (by
      rw [heq]
      exact (nsmul_add_eq_zero_iff_QA_mul_dvd hS hC hD hdCD hy₀ hy₁ (QA C * QA D)).mpr dvd_rfl)
  have h3 : QA C * QA D ∣ QA A * QA B :=
    (nsmul_add_eq_zero_iff_QA_mul_dvd hS hC hD hdCD hy₀ hy₁ (QA A * QA B)).mp (by
      rw [← heq]
      exact (nsmul_add_eq_zero_iff_QA_mul_dvd hS hA hB hdAB hx₀ hx₁ (QA A * QA B)).mpr dvd_rfl)
  refine QA_injective h2 hS (Finset.union_subset hA hB) (Finset.union_subset hC hD) ?_
  rw [QA_union hdAB, QA_union hdCD]
  exact Nat.dvd_antisymm h1 h3

/-! ## The counting bound -/

/-- **Tao's `2^k` counting bound for the decompositions `β = α₀ + α`, `α₀ ∈ Σ_{A₀}`,
`α ∈ Σ_{(A₀)}`, in the finite cyclic group `ZMod Q_S`.**

Let `S` be a finite set of pairwise coprime integers `≥ 2` and let `β ∈ ZMod (Q_S)`.  Then the number
of sets `A₀ ⊆ S` with `A₀.card ≤ k` for which `β` admits a decomposition `β = α₀ + α` with
`α₀ ∈ sigmaAQ (QA S) A₀` (the points of exact denominator `Q_{A₀}`) and
`α ∈ sigmaCompQ (QA S) S k A₀` (the complementary arc `⋃_{A₁ ⊆ S \ A₀, A₁.card ≤ k - A₀.card} Σ_{A₁}`)
is at most `2 ^ k`.

This is the counting fact used in the proof of Tao's Theorem `ortho-apply`(i)
(arXiv:2008.05066, §4), in the form needed by the `ZMod (Q_S)`-valued orthogonality machinery of
`ZModArcs.lean`; the circle-valued form is `sigmaComp_repr_count`.  Proof: choosing one admissible
`A₀` and one complementary `A₁`, every admissible `A₀'` decomposes as `A₀' ⊔ A₁'` with
`A₀' ∪ A₁' = A₀ ∪ A₁` (`sigmaUnion_unique_Q`), and the latter has at most
`A₀.card + (k - A₀.card) = k` elements. -/
theorem sigmaCompDecompSetQ_card_le {S : Finset ℕ} [NeZero (QA S)]
    (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) (β : ZMod (QA S)) :
    (sigmaCompDecompSetQ (QA S) S k β).card ≤ 2 ^ k := by
  classical
  by_cases hne : (sigmaCompDecompSetQ (QA S) S k β).Nonempty
  · obtain ⟨A₀, hA₀mem⟩ := hne
    have hA₀mem' := hA₀mem
    simp only [sigmaCompDecompSetQ, Finset.mem_filter, Finset.mem_powerset] at hA₀mem'
    obtain ⟨⟨hA₀sub, hA₀card⟩, α₀, hα₀mem, α, hαmem, hsum⟩ := hA₀mem'
    rw [sigmaCompQ] at hαmem
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset] at hαmem
    obtain ⟨A₁, hA₁mem, hα₁mem⟩ := hαmem
    obtain ⟨hA₁sub, hA₁card⟩ := hA₁mem
    have hA₁S : A₁ ⊆ S := hA₁sub.trans Finset.sdiff_subset
    have hdisj : Disjoint A₀ A₁ := Finset.disjoint_left.mpr fun q hq₀ hq₁ =>
      (Finset.mem_sdiff.mp (hA₁sub hq₁)).2 hq₀
    have hBcard : (A₀ ∪ A₁).card ≤ k := by
      rw [Finset.card_union_of_disjoint hdisj]
      omega
    have hsub : sigmaCompDecompSetQ (QA S) S k β ⊆ (A₀ ∪ A₁).powerset := by
      intro A₀' hA₀'mem
      rw [Finset.mem_powerset]
      have hA₀'mem' := hA₀'mem
      simp only [sigmaCompDecompSetQ, Finset.mem_filter, Finset.mem_powerset] at hA₀'mem'
      obtain ⟨⟨hA₀'sub, -⟩, α₀', hα₀'mem, α', hα'mem, hsum'⟩ := hA₀'mem'
      rw [sigmaCompQ] at hα'mem
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset] at hα'mem
      obtain ⟨A₁', hA₁'mem, hα₁'mem⟩ := hα'mem
      obtain ⟨hA₁'sub, -⟩ := hA₁'mem
      have hA₁'S : A₁' ⊆ S := hA₁'sub.trans Finset.sdiff_subset
      have hdisj' : Disjoint A₀' A₁' := Finset.disjoint_left.mpr fun q hq₀ hq₁ =>
        (Finset.mem_sdiff.mp (hA₁'sub hq₁)).2 hq₀
      have hunion : A₀' ∪ A₁' = A₀ ∪ A₁ :=
        sigmaUnion_unique_Q h2 hS hA₀'sub hA₁'S hA₀sub hA₁S hdisj' hdisj
          hα₀'mem hα₁'mem hα₀mem hα₁mem (by rw [hsum, hsum'])
      intro q hq
      rw [← hunion]
      exact Finset.mem_union_left _ hq
    calc (sigmaCompDecompSetQ (QA S) S k β).card
        ≤ ((A₀ ∪ A₁).powerset).card := Finset.card_le_card hsub
      _ = 2 ^ (A₀ ∪ A₁).card := Finset.card_powerset _
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hBcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

end Work.BourgainPlan.IonescuWainger
