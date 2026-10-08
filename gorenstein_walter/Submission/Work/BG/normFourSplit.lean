import Mathlib
import Submission.Work.BG.S02

/-!
# Area BG: a norm-`4` virtual character splits into a difference of two norm-`2` characters

`normFourSplit` is the "sign discipline" leaf of BG §2: if a `ℤ`-combination
`χ = ∑_{a ∈ s} c a · a` of irreducible characters is split over a partition
`s = S ⊔ T` into two parts, each of squared norm `2`, then `χ` is the *difference*
`g₁ - g₂` of two virtual characters `g₁, g₂ ∈ ℤ[Irr K]`, each of squared norm `2`
and with no common irreducible constituent (`DisjointCF g₁ g₂`).

The argument is elementary Fourier algebra, spelled out below:

* `subsum_mem_ZIrr_inner_sum_sq` — a sub-sum `∑_{S} c a · a` over irreducibles lies in
  `ℤ[Irr K]` and has squared norm `∑_{S} (c a)²`;
* `exists_signed_pair_of_mem_ZIrr_inner_self_eq_two` (existing library lemma) then writes
  each norm-`2` sub-sum `u`, `v` as a signed pair `ε₁·α₁ + ε₂·α₂`, `δ₁·β₁ + δ₂·β₂`;
* `inner_sum_irr_eq_ite` recovers the Fourier coefficient of a sub-sum `∑_S c a · a` at an
  irreducible `b` as `c b` when `b ∈ S` and `0` otherwise; applied through
  `inner_signedPair_eq_left/right` this shows the four characters `α₁, α₂ ∈ S` and
  `β₁, β₂ ∈ T` really live in the two parts, so they are pairwise distinct;
* the two "crossed" signed pairs `g₁ = ε₁·α₁ + δ₁·β₁` and `g₂ = -(ε₂·α₂ + δ₂·β₂)` are each
  of norm `2` (`signedPair_mem_ZIrr_inner_self_eq_two` for `g₁`, its negation for `g₂`),
  are disjoint (`disjointCF_signedPairs_of_ne`, transported through `disjointCF_neg_right`),
  and satisfy `g₁ - g₂ = u + v = χ`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

/-- Fourier coefficient of a `ℤ`-combination of irreducibles against an irreducible:
it is the coefficient `c b` if `b` occurs in the sum, and `0` otherwise. -/
theorem inner_sum_irr_eq_ite {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [DecidableEq (ClassFunction G ℂ)]
    {s : Finset (ClassFunction G ℂ)} {c : ClassFunction G ℂ → ℤ}
    (hsupp : ∀ a ∈ s, IsIrreducibleCharacter a) {b : ClassFunction G ℂ}
    (hb : IsIrreducibleCharacter b) :
    ClassFunction.inner (∑ a ∈ s, (c a : ℂ) • a) b = if b ∈ s then (c b : ℂ) else 0 := by
  classical
  rw [inner_sum_left]
  have step : (∑ a ∈ s, ClassFunction.inner ((c a : ℂ) • a) b)
      = ∑ a ∈ s, (if a = b then (c a : ℂ) else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [ClassFunction.inner_smul_left, irr_cf_inner (hsupp a ha) hb]
    by_cases h : a = b
    · rw [ite_eq_left h, ite_eq_left h, mul_one]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [step, Finset.sum_ite_eq' s b (fun a => (c a : ℂ))]

/-- A `ℤ`-combination `∑_{S} c a · a` of irreducibles is a virtual character, and its
squared norm (Parseval) is the sum of the squared coefficients. -/
theorem subsum_mem_ZIrr_inner_sum_sq {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {s : Finset (ClassFunction G ℂ)} {c : ClassFunction G ℂ → ℤ}
    (hsupp : ∀ a ∈ s, IsIrreducibleCharacter a) :
    (∑ a ∈ s, (c a : ℂ) • a) ∈ ZIrr G ∧
      ClassFunction.inner (∑ a ∈ s, (c a : ℂ) • a) (∑ a ∈ s, (c a : ℂ) • a) =
        ∑ a ∈ s, (c a : ℂ) ^ 2 := by
  classical
  have horth : ∀ a ∈ s, ∀ b ∈ s, ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 :=
    fun a ha b hb => irr_cf_inner (hsupp a ha) (hsupp b hb)
  refine ⟨?_, inner_self_orthonormalSum_eq_sum_sq horth⟩
  have hmem : (∑ a ∈ s, (c a : ℂ) • a) = ∑ a ∈ s, (c a : ℤ) • a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Int.cast_smul_eq_zsmul]
  rw [hmem]
  exact Submodule.sum_mem _ fun a ha =>
    Submodule.smul_mem _ (c a) (IsIrreducibleCharacter.mem_ZIrr (hsupp a ha))

/-- A signed pair `ε·α + δ·β` of two distinct irreducibles with signs `±1` is a virtual
character of squared norm `2`. -/
theorem signedPair_mem_ZIrr_inner_eq_two {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {α β : ClassFunction G ℂ} (hα : IsIrreducibleCharacter α) (hβ : IsIrreducibleCharacter β)
    (hαβ : α ≠ β) {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ((ε : ℂ) • α + (δ : ℂ) • β) ∈ ZIrr G ∧
      ClassFunction.inner ((ε : ℂ) • α + (δ : ℂ) • β) ((ε : ℂ) • α + (δ : ℂ) • β) = 2 := by
  classical
  have hαZ : α ∈ ZIrr G := IsIrreducibleCharacter.mem_ZIrr hα
  have hβZ : β ∈ ZIrr G := IsIrreducibleCharacter.mem_ZIrr hβ
  constructor
  · have e1 : (ε : ℂ) • α = (ε : ℤ) • α := Int.cast_smul_eq_zsmul ℂ ε α
    have e2 : (δ : ℂ) • β = (δ : ℤ) • β := Int.cast_smul_eq_zsmul ℂ δ β
    rw [e1, e2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ ε hαZ) (Submodule.smul_mem _ δ hβZ)
  · have hA : (⟨α, hα⟩ : IrreducibleCharacter G) ≠ (⟨β, hβ⟩ : IrreducibleCharacter G) :=
      fun h => hαβ (Subtype.ext_iff.mp h)
    have h1 : (ε : ℂ) • α = (ε : ℤ) • ((⟨α, hα⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) := by
      rw [Int.cast_smul_eq_zsmul]
    have h2 : (δ : ℂ) • β = (δ : ℤ) • ((⟨β, hβ⟩ : IrreducibleCharacter G) : ClassFunction G ℂ) := by
      rw [Int.cast_smul_eq_zsmul]
    rw [h1, h2, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_add_right, inner_zsmul_irreducible_eq, inner_zsmul_irreducible_eq,
      inner_zsmul_irreducible_eq, inner_zsmul_irreducible_eq,
      ite_eq_left rfl, ite_eq_right hA, ite_eq_right (Ne.symm hA), ite_eq_left rfl]
    rcases hε with h | h <;> rcases hδ with h' | h' <;> rw [h, h'] <;> norm_num

/-- Expansion of the inner product of a two-term signed combination with an irreducible,
by left-linearity. -/
theorem inner_signedPair_apply {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (a b : ℤ) {α β : ClassFunction G ℂ} (χ : IrreducibleCharacter G) :
    ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β) (χ : ClassFunction G ℂ) =
      (a : ℂ) * ClassFunction.inner α (χ : ClassFunction G ℂ) +
      (b : ℂ) * ClassFunction.inner β (χ : ClassFunction G ℂ) := by
  rw [ClassFunction.inner_add_left, ClassFunction.inner_smul_left, ClassFunction.inner_smul_left]

/-- The coefficient of `α` in the signed combination `a·α + b·β` (with `α ≠ β`) is `a`. -/
theorem inner_signedPair_eq_left {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [DecidableEq (ClassFunction G ℂ)]
    {α β : ClassFunction G ℂ} (a b : ℤ) (hα : IsIrreducibleCharacter α)
    (hβ : IsIrreducibleCharacter β) (hαβ : α ≠ β) :
    ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β) α = (a : ℂ) := by
  rw [inner_signedPair_apply a b (⟨α, hα⟩ : IrreducibleCharacter G),
    irr_cf_inner hα hα, irr_cf_inner hβ hα]
  rw [ite_eq_left rfl, ite_eq_right (fun h : β = α => hαβ h.symm)]
  ring

/-- The coefficient of `β` in the signed combination `a·α + b·β` (with `α ≠ β`) is `b`. -/
theorem inner_signedPair_eq_right {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [DecidableEq (ClassFunction G ℂ)]
    {α β : ClassFunction G ℂ} (a b : ℤ) (hα : IsIrreducibleCharacter α)
    (hβ : IsIrreducibleCharacter β) (hαβ : α ≠ β) :
    ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β) β = (b : ℂ) := by
  rw [inner_signedPair_apply a b (⟨β, hβ⟩ : IrreducibleCharacter G),
    irr_cf_inner hα hβ, irr_cf_inner hβ hβ]
  rw [ite_eq_right (fun h : α = β => hαβ h), ite_eq_left rfl]
  ring

/-- A nonzero Fourier coefficient of `a·α + b·β` at an irreducible `χ` forces `χ` to be one
of the two irreducible constituents `α`, `β`. -/
theorem signedPair_coeff_ne_zero {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [DecidableEq (ClassFunction G ℂ)]
    {a b : ℤ} {α β : ClassFunction G ℂ} (hα : IsIrreducibleCharacter α)
    (hβ : IsIrreducibleCharacter β) (χ : IrreducibleCharacter G)
    (h : ClassFunction.inner ((a : ℂ) • α + (b : ℂ) • β) (χ : ClassFunction G ℂ) ≠ 0) :
    (χ : ClassFunction G ℂ) = α ∨ (χ : ClassFunction G ℂ) = β := by
  rw [inner_signedPair_apply a b χ, irr_cf_inner hα χ.mem_irreducibleCharacters,
    irr_cf_inner hβ χ.mem_irreducibleCharacters] at h
  by_cases hA : (χ : ClassFunction G ℂ) = α
  · exact Or.inl hA
  by_cases hB : (χ : ClassFunction G ℂ) = β
  · exact Or.inr hB
  · exfalso
    rw [ite_eq_right (fun hh : α = (χ : ClassFunction G ℂ) => hA hh.symm),
        ite_eq_right (fun hh : β = (χ : ClassFunction G ℂ) => hB hh.symm)] at h
    simp at h

/-- Two signed pairs of irreducibles with disjoint supports are disjoint as virtual
characters (no common irreducible constituent). -/
theorem disjointCF_signedPairs_of_ne {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] [DecidableEq (ClassFunction G ℂ)]
    {α β γ ζ : ClassFunction G ℂ}
    (hα : IsIrreducibleCharacter α) (hβ : IsIrreducibleCharacter β)
    (hγ : IsIrreducibleCharacter γ) (hζ : IsIrreducibleCharacter ζ)
    (hαγ : α ≠ γ) (hαζ : α ≠ ζ) (hβγ : β ≠ γ) (hβζ : β ≠ ζ)
    (ε δ ε' δ' : ℤ) :
    DisjointCF ((ε : ℂ) • α + (δ : ℂ) • β) ((ε' : ℂ) • γ + (δ' : ℂ) • ζ) := by
  classical
  intro χ
  by_cases h1 : ClassFunction.inner ((ε : ℂ) • α + (δ : ℂ) • β) (χ : ClassFunction G ℂ) = 0
  · exact Or.inl h1
  · right
    have hχ : (χ : ClassFunction G ℂ) = α ∨ (χ : ClassFunction G ℂ) = β :=
      signedPair_coeff_ne_zero hα hβ χ h1
    rw [inner_signedPair_apply ε' δ' χ,
      irr_cf_inner hγ χ.mem_irreducibleCharacters, irr_cf_inner hζ χ.mem_irreducibleCharacters]
    rcases hχ with h | h
    · rw [ite_eq_right (fun hh : γ = (χ : ClassFunction G ℂ) => hαγ (hh.trans h).symm),
          ite_eq_right (fun hh : ζ = (χ : ClassFunction G ℂ) => hαζ (hh.trans h).symm)]
      ring
    · rw [ite_eq_right (fun hh : γ = (χ : ClassFunction G ℂ) => hβγ (hh.trans h).symm),
          ite_eq_right (fun hh : ζ = (χ : ClassFunction G ℂ) => hβζ (hh.trans h).symm)]
      ring

/-- Disjointness is preserved by negating the second argument. -/
theorem disjointCF_neg_right {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    {u v : ClassFunction G ℂ} (h : DisjointCF u v) : DisjointCF u (-v) := by
  intro χ
  rcases h χ with h1 | h1
  · exact Or.inl h1
  · right
    rw [ClassFunction.inner_neg_left, h1, neg_zero]

theorem normFourSplit {K : Type} [Group K] [Finite K] [Fintype K] [Invertible (Nat.card K : ℂ)]
    [DecidableEq (OddOrder.RepresentationTheory.ClassFunction K ℂ)]
    {s S T : Finset (OddOrder.RepresentationTheory.ClassFunction K ℂ)}
    {c : OddOrder.RepresentationTheory.ClassFunction K ℂ → ℤ}
    (hsupp : ∀ a ∈ s, OddOrder.RepresentationTheory.IsIrreducibleCharacter a)
    (hS : S ⊆ s) (hT : T ⊆ s) (hdisj : Disjoint S T) (hcover : S ∪ T = s)
    (hS2 : ∑ a ∈ S, c a ^ 2 = 2) (hT2 : ∑ a ∈ T, c a ^ 2 = 2) :
    ∃ g₁ g₂ : OddOrder.RepresentationTheory.ClassFunction K ℂ,
      (∑ a ∈ s, (c a : ℂ) • a) = g₁ - g₂ ∧
      g₁ ∈ OddOrder.RepresentationTheory.ZIrr K ∧ g₂ ∈ OddOrder.RepresentationTheory.ZIrr K ∧
      OddOrder.RepresentationTheory.ClassFunction.inner g₁ g₁ = 2 ∧
      OddOrder.RepresentationTheory.ClassFunction.inner g₂ g₂ = 2 ∧
      Work.BG.DisjointCF g₁ g₂ := by
  classical
  have hsuppS : ∀ a ∈ S, IsIrreducibleCharacter a := fun a ha => hsupp a (hS ha)
  have hsuppT : ∀ a ∈ T, IsIrreducibleCharacter a := fun a ha => hsupp a (hT ha)
  obtain ⟨huZ, huN⟩ := subsum_mem_ZIrr_inner_sum_sq hsuppS
  obtain ⟨hvZ, hvN⟩ := subsum_mem_ZIrr_inner_sum_sq hsuppT
  have hcastS : (∑ a ∈ S, (c a : ℂ) ^ 2) = ((∑ a ∈ S, c a ^ 2 : ℤ) : ℂ) := by
    push_cast; ring
  have hcastT : (∑ a ∈ T, (c a : ℂ) ^ 2) = ((∑ a ∈ T, c a ^ 2 : ℤ) : ℂ) := by
    push_cast; ring
  have hu_norm : ClassFunction.inner (∑ a ∈ S, (c a : ℂ) • a) (∑ a ∈ S, (c a : ℂ) • a) = 2 := by
    rw [huN, hcastS, hS2]; norm_num
  have hv_norm : ClassFunction.inner (∑ a ∈ T, (c a : ℂ) • a) (∑ a ∈ T, (c a : ℂ) • a) = 2 := by
    rw [hvN, hcastT, hT2]; norm_num
  obtain ⟨α₁, α₂, ε₁, ε₂, hα₁irr, hα₂irr, hα₁α₂, hε₁, hε₂, hu_eq⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two huZ hu_norm
  obtain ⟨β₁, β₂, δ₁, δ₂, hβ₁irr, hβ₂irr, hβ₁β₂, hδ₁, hδ₂, hv_eq⟩ :=
    exists_signed_pair_of_mem_ZIrr_inner_self_eq_two hvZ hv_norm
  have hα₁S : α₁ ∈ S := by
    have h2 : ClassFunction.inner (∑ a ∈ S, (c a : ℂ) • a) α₁ = (ε₁ : ℂ) := by
      rw [hu_eq, inner_signedPair_eq_left ε₁ ε₂ hα₁irr hα₂irr hα₁α₂]
    have hne : (ε₁ : ℂ) ≠ 0 := by rcases hε₁ with h | h <;> simp [h]
    by_contra hmem
    rw [inner_sum_irr_eq_ite hsuppS hα₁irr, ite_eq_right hmem] at h2
    exact hne h2.symm
  have hα₂S : α₂ ∈ S := by
    have h2 : ClassFunction.inner (∑ a ∈ S, (c a : ℂ) • a) α₂ = (ε₂ : ℂ) := by
      rw [hu_eq, inner_signedPair_eq_right ε₁ ε₂ hα₁irr hα₂irr hα₁α₂]
    have hne : (ε₂ : ℂ) ≠ 0 := by rcases hε₂ with h | h <;> simp [h]
    by_contra hmem
    rw [inner_sum_irr_eq_ite hsuppS hα₂irr, ite_eq_right hmem] at h2
    exact hne h2.symm
  have hβ₁T : β₁ ∈ T := by
    have h2 : ClassFunction.inner (∑ a ∈ T, (c a : ℂ) • a) β₁ = (δ₁ : ℂ) := by
      rw [hv_eq, inner_signedPair_eq_left δ₁ δ₂ hβ₁irr hβ₂irr hβ₁β₂]
    have hne : (δ₁ : ℂ) ≠ 0 := by rcases hδ₁ with h | h <;> simp [h]
    by_contra hmem
    rw [inner_sum_irr_eq_ite hsuppT hβ₁irr, ite_eq_right hmem] at h2
    exact hne h2.symm
  have hβ₂T : β₂ ∈ T := by
    have h2 : ClassFunction.inner (∑ a ∈ T, (c a : ℂ) • a) β₂ = (δ₂ : ℂ) := by
      rw [hv_eq, inner_signedPair_eq_right δ₁ δ₂ hβ₁irr hβ₂irr hβ₁β₂]
    have hne : (δ₂ : ℂ) ≠ 0 := by rcases hδ₂ with h | h <;> simp [h]
    by_contra hmem
    rw [inner_sum_irr_eq_ite hsuppT hβ₂irr, ite_eq_right hmem] at h2
    exact hne h2.symm
  have hα₁β₁ : α₁ ≠ β₁ := fun h => (Finset.disjoint_left.mp hdisj hα₁S) (h ▸ hβ₁T)
  have hα₁β₂ : α₁ ≠ β₂ := fun h => (Finset.disjoint_left.mp hdisj hα₁S) (h ▸ hβ₂T)
  have hα₂β₁ : α₂ ≠ β₁ := fun h => (Finset.disjoint_left.mp hdisj hα₂S) (h ▸ hβ₁T)
  have hα₂β₂ : α₂ ≠ β₂ := fun h => (Finset.disjoint_left.mp hdisj hα₂S) (h ▸ hβ₂T)
  refine ⟨(ε₁ : ℂ) • α₁ + (δ₁ : ℂ) • β₁,
    -((ε₂ : ℂ) • α₂ + (δ₂ : ℂ) • β₂), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hcover, Finset.sum_union hdisj, hu_eq, hv_eq, sub_neg_eq_add]
    abel
  · exact (signedPair_mem_ZIrr_inner_eq_two hα₁irr hβ₁irr hα₁β₁ hε₁ hδ₁).1
  · exact Submodule.neg_mem _ (signedPair_mem_ZIrr_inner_eq_two hα₂irr hβ₂irr hα₂β₂ hε₂ hδ₂).1
  · exact (signedPair_mem_ZIrr_inner_eq_two hα₁irr hβ₁irr hα₁β₁ hε₁ hδ₁).2
  · have h := (signedPair_mem_ZIrr_inner_eq_two hα₂irr hβ₂irr hα₂β₂ hε₂ hδ₂).2
    rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, neg_neg]
    exact h
  · exact disjointCF_neg_right (disjointCF_signedPairs_of_ne hα₁irr hβ₁irr hα₂irr hβ₂irr
      hα₁α₂ hα₁β₂ hα₂β₁.symm hβ₁β₂ ε₁ δ₁ ε₂ δ₂)

end Work.BG
