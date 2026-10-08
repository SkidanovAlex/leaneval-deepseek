/-
Area BG: verbatim copy of the lead's design pass 24 (`Submission/Work/_design_gw/Core24.lean`),
namespace `Work.GW2.C24`.  Kept in the area so that BG's leaves can import it
(`import Submission.Work.BG.Core24`); the design file itself is not part of the library.

Item 1: `coeff_kappa_zero`, `degEq_of_coeffs` (proved) — the coefficient identity of BG p. 211,
so that `Work.BG.c3DegEq` is provable as stated.
Item 2: `Lemma36InvProp` (Lemma 3.6 with the source's hypotheses on `K`), the G-leaf
`KInvNormalProp` (G11), and `lemma36_thmC` (proved) — the form `C3DegreeProp`/`C4DegreeProp`
consume.

Do not edit: re-copy from `_design_gw/Core24.lean` if the lead revises it.
-/
import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_assemblyCore
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedIrreducible
import Submission.OddOrder.GroupTheory.RepresentationTheory.ZIrrFourier

namespace Work.GW2.C24

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Item 1: the coefficient identity behind BG p. 211 -/

section Item1

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- Equivalent characters have equal `Λ`-orbits, hence equal orbit sizes. -/
theorem lamOrbit_eq_of_LamEquiv (C : Sec2Ctx G) {μ ν : ClassFunction ↥C.P.H0 ℂ}
    (h : LamEquiv C μ ν) : lamOrbit C μ = lamOrbit C ν := by
  ext χ
  exact ⟨fun h' => s02c_LamEquiv_trans C (s02c_LamEquiv_symm C h) h',
    fun h' => s02c_LamEquiv_trans C h h'⟩

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- `|Λν| ≠ |Λκ|` excludes `ν ~ κ` (used with `|Λνᵢ| ≠ m = |Λκ₁|`, BG (2)). -/
theorem not_LamEquiv_of_ncard_ne (C : Sec2Ctx G) {ν κ : ClassFunction ↥C.P.H0 ℂ}
    (h : (lamOrbit C ν).ncard ≠ (lamOrbit C κ).ncard) : ¬ LamEquiv C ν κ :=
  fun he => h (by rw [lamOrbit_eq_of_LamEquiv C he])

/-- **BG p. 210 (1), first half**: `κ̃₃ ∈ ±Irr(G)` and `𝒮(κ̃₃) = {κ₃, κ₃^s}`, from Lemma 3.4
(`Lemma34Prop`, proved in the workspace as `Work.BG.lemma34`). -/
theorem bset_kappa3 (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hL34 : Lemma34Prop D C) (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (κ₃ : ClassFunction ↥C.P.H0 ℂ) (h3 : IsIrreducibleCharacter κ₃)
    (hs3 : sconj C κ₃ ≠ κ₃) (horb3 : (lamOrbit C κ₃).ncard = D.n) :
    IsPmIrr (f κ₃) ∧ ClassFunction.inner (f κ₃) (f κ₃) = 1 ∧
      bset C f (f κ₃) = {κ₃, sconj C κ₃} := by
  have hkey : κ₃ ∈ orbitKey C κ₃ := Or.inl (s02c_LamEquiv_refl C κ₃)
  obtain ⟨hZ, -, hnorm, -⟩ := (hf.1 κ₃ h3) κ₃ hkey κ₃ hkey h3 h3
  have hn1 : ClassFunction.inner (f κ₃) (f κ₃) = 1 := by rw [hnorm]; simp [hs3]
  obtain ⟨ε, ψ, hε, hfeq⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hZ hn1
  have hpm : IsPmIrr (f κ₃) := by
    rcases hε with rfl | rfl
    · left; rw [hfeq, one_smul]; exact ψ.2
    · right
      have h2 : -(f κ₃) = (ψ : ClassFunction G ℂ) := by rw [hfeq]; simp
      rw [h2]; exact ψ.2
  have hmem : κ₃ ∈ bset C f (f κ₃) := ⟨h3, by rw [hn1]; exact one_ne_zero⟩
  exact ⟨hpm, hn1, (hL34 hDC hS3 f hf (f κ₃) hpm κ₃ hmem hs3 (Or.inr horb3)).1⟩

/-- An `s`-fixed irreducible `η` is not in `𝒮(κ̃₃)`, so `⟨η̃, κ̃₃⟩ = 0`. -/
theorem inner_kappa3_sfixed (D : BGData G) (C : Sec2Ctx G)
    [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hL34 : Lemma34Prop D C) (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (κ₃ : ClassFunction ↥C.P.H0 ℂ) (h3 : IsIrreducibleCharacter κ₃)
    (hs3 : sconj C κ₃ ≠ κ₃) (horb3 : (lamOrbit C κ₃).ncard = D.n)
    (η : ClassFunction ↥C.P.H0 ℂ) (hη : IsIrreducibleCharacter η) (hηs : sconj C η = η) :
    ClassFunction.inner (f η) (f κ₃) = 0 := by
  obtain ⟨-, -, hb⟩ := bset_kappa3 D C hL34 hDC hS3 f hf κ₃ h3 hs3 horb3
  have h0 : ClassFunction.inner (f κ₃) (f η) = 0 := by
    by_contra hne
    have hm : η ∈ bset C f (f κ₃) := ⟨hη, hne⟩
    rw [hb, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h
    · exact hs3 (h ▸ hηs)
    · -- `η = κ₃^s` and `η^s = η` give `κ₃ = η^s = η = κ₃^s`
      have h' : sconj C η = κ₃ := by rw [h, sconj_sconj]
      exact hs3 (by rw [← h, ← h', hηs])
  rw [OddOrder.RepresentationTheory.inner_conj_symm, h0, star_zero]

/-- **The coefficient identity (BG p. 211, "δᵢ orthogonal to κ̃₁ - κ̃₃ as well as to κ̃₃,
by (1)")**: for `ν ~ μ` both `s`-fixed with `ν ≁ κ`, and `κ₃ ~ κ` with
`κ₃^s ≠ κ₃`, `|Λκ₃| = m`: `⟨ν̃ - μ̃, κ̃⟩ = 0`. -/
theorem coeff_kappa_zero (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hL34 : Lemma34Prop D C) (hDC : Compat D C) (hS3 : Sec3Hyp D)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (κ κ₃ ν μ : ClassFunction ↥C.P.H0 ℂ)
    (hκ : IsIrreducibleCharacter κ) (h3 : IsIrreducibleCharacter κ₃)
    (hν : IsIrreducibleCharacter ν) (hμ : IsIrreducibleCharacter μ)
    (hκκ₃ : LamEquiv C κ κ₃) (hs3 : sconj C κ₃ ≠ κ₃) (horb3 : (lamOrbit C κ₃).ncard = D.n)
    (hνμ : LamEquiv C ν μ) (hνs : sconj C ν = ν) (hμs : sconj C μ = μ)
    (hνκ : ¬ LamEquiv C ν κ) :
    ClassFunction.inner (f ν - f μ) (f κ) = 0 := by
  have hiv : ClassFunction.inner (f ν - f μ) (f κ - f κ₃) = 0 :=
    hf.2.1 ν μ κ κ₃ hν hμ hκ h3 hνμ hκκ₃ hνκ (by rw [hνs]; exact hνκ)
  have hν3 := inner_kappa3_sfixed D C hL34 hDC hS3 f hf κ₃ h3 hs3 horb3 ν hν hνs
  have hμ3 := inner_kappa3_sfixed D C hL34 hDC hS3 f hf κ₃ h3 hs3 horb3 μ hμ hμs
  have hsplit : f κ = (f κ - f κ₃) + f κ₃ := by abel
  rw [hsplit, ClassFunction.inner_add_right, hiv, ClassFunction.inner_sub_left, hν3, hμ3]
  ring

omit [Finite G] in
/-- **The degree step of p. 211, normalized signs** (pure inner-product algebra):
`d := χ₁ - χ₂`; `w := δ₁ + δ₂ - 2d` has `⟨w, w⟩ = 0`, so `δ₁ + δ₂ = 2d` and `d(1) = 0`. -/
theorem degEq_core (χ₁ χ₂ δ₁ δ₂ : ClassFunction G ℂ)
    (h11 : ClassFunction.inner χ₁ χ₁ = 1) (h22 : ClassFunction.inner χ₂ χ₂ = 1)
    (h12 : ClassFunction.inner χ₁ χ₂ = 0)
    (hd1 : ClassFunction.inner δ₁ δ₁ = 4) (hd2 : ClassFunction.inner δ₂ δ₂ = 4)
    (hdd : ClassFunction.inner δ₁ δ₂ = 0)
    (ha1 : ClassFunction.inner δ₁ χ₁ = 1) (hb1 : ClassFunction.inner δ₁ χ₂ = -1)
    (ha2 : ClassFunction.inner δ₂ χ₁ = 1) (hb2 : ClassFunction.inner δ₂ χ₂ = -1)
    (h1 : δ₁ 1 = 0) (h2 : δ₂ 1 = 0) : χ₁ 1 = χ₂ 1 := by
  have c (a b : ClassFunction G ℂ) (z : ℂ) (h : ClassFunction.inner a b = z) :
      ClassFunction.inner b a = star z := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, h]
  have h21 := c _ _ _ h12
  have hdd' := c _ _ _ hdd
  have ha1' := c _ _ _ ha1
  have hb1' := c _ _ _ hb1
  have ha2' := c _ _ _ ha2
  have hb2' := c _ _ _ hb2
  simp only [star_zero, star_one, star_neg] at h21 hdd' ha1' hb1' ha2' hb2'
  set w : ClassFunction G ℂ := δ₁ + δ₂ - ((χ₁ - χ₂) + (χ₁ - χ₂)) with hw
  have hww : ClassFunction.inner w w = 0 := by
    simp only [hw, ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right]
    rw [h11, h22, h12, h21, hd1, hd2, hdd, hdd', ha1, hb1, ha2, hb2, ha1', hb1', ha2', hb2']
    ring
  have hw0 : w = 0 := eq_zero_of_inner_self_re_eq_zero (by rw [hww]; simp)
  have hv : w 1 = 0 := by rw [hw0]; rfl
  simp only [hw, ClassFunction.sub_apply, ClassFunction.add_apply, h1, h2] at hv
  linear_combination (-1 / 2 : ℂ) * hv

omit [Finite G] in
/-- **The degree step of p. 211** (`±δ₁ = χ₁ - χ₂ + ρ + σ`, `±δ₂ = χ₁ - χ₂ - ρ - σ` ⇒
`χ₁(1) = χ₂(1)`), arbitrary signs `⟨δᵢ, χ₁⟩ = εᵢ = ±1`, from `⟨δᵢ, χ₁ + χ₂⟩ = 0`. -/
theorem degEq_of_coeffs (χ₁ χ₂ δ₁ δ₂ : ClassFunction G ℂ)
    (h11 : ClassFunction.inner χ₁ χ₁ = 1) (h22 : ClassFunction.inner χ₂ χ₂ = 1)
    (h12 : ClassFunction.inner χ₁ χ₂ = 0)
    (hd1 : ClassFunction.inner δ₁ δ₁ = 4) (hd2 : ClassFunction.inner δ₂ δ₂ = 4)
    (hdd : ClassFunction.inner δ₁ δ₂ = 0)
    (ha1 : ClassFunction.inner δ₁ χ₁ = 1 ∨ ClassFunction.inner δ₁ χ₁ = -1)
    (ha2 : ClassFunction.inner δ₂ χ₁ = 1 ∨ ClassFunction.inner δ₂ χ₁ = -1)
    (hk1 : ClassFunction.inner δ₁ (χ₁ + χ₂) = 0) (hk2 : ClassFunction.inner δ₂ (χ₁ + χ₂) = 0)
    (h1 : δ₁ 1 = 0) (h2 : δ₂ 1 = 0) : χ₁ 1 = χ₂ 1 := by
  rw [ClassFunction.inner_add_right] at hk1 hk2
  -- normalize each `δᵢ` to `εᵢ δᵢ` with `⟨εᵢ δᵢ, χ₁⟩ = 1`
  have norm (δ : ClassFunction G ℂ) (hd : ClassFunction.inner δ δ = 4)
      (ha : ClassFunction.inner δ χ₁ = 1 ∨ ClassFunction.inner δ χ₁ = -1)
      (hk : ClassFunction.inner δ χ₁ + ClassFunction.inner δ χ₂ = 0) (h : δ 1 = 0) :
      ∃ δ' : ClassFunction G ℂ, (δ' = δ ∨ δ' = -δ) ∧ ClassFunction.inner δ' δ' = 4 ∧
        ClassFunction.inner δ' χ₁ = 1 ∧ ClassFunction.inner δ' χ₂ = -1 ∧ δ' 1 = 0 := by
    rcases ha with ha | ha
    · exact ⟨δ, Or.inl rfl, hd, ha, by linear_combination hk - ha, h⟩
    · refine ⟨-δ, Or.inr rfl, ?_, ?_, ?_, ?_⟩
      · rw [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, hd]; ring
      · rw [ClassFunction.inner_neg_left, ha]; ring
      · rw [ClassFunction.inner_neg_left]; linear_combination -hk + ha
      · rw [ClassFunction.neg_apply, h, neg_zero]
  obtain ⟨e₁, he₁, hd1', ha1', hb1', h1'⟩ := norm δ₁ hd1 ha1 hk1 h1
  obtain ⟨e₂, he₂, hd2', ha2', hb2', h2'⟩ := norm δ₂ hd2 ha2 hk2 h2
  have hdd' : ClassFunction.inner e₁ e₂ = 0 := by
    rcases he₁ with h | h <;> rcases he₂ with h' | h' <;> rw [h, h'] <;>
      simp only [ClassFunction.inner_neg_left, ClassFunction.inner_neg_right, hdd, neg_zero]
  exact degEq_core χ₁ χ₂ e₁ e₂ h11 h22 h12 hd1' hd2' hdd' ha1' hb1' ha2' hb2' h1' h2'

end Item1

/-! ## 2. Item 2: Lemma 3.6 with the source's hypotheses on `K` -/

section Item2

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **L36-INV (BG Lemma 3.6, p. 210), corrected.**  Replaces `C16.Lemma36Prop`.  The source's
`K = K₁ ∩ K₂` is inverted by `t₁` and `t₂` (so `S₀ = ⟨t₁t₂⟩` centralizes `K` and every element
of `S ∖ S₀ = t₁S₀` inverts `K`), and is normalized by `U`.  Both are used in "inverting `K`, each
element of `S - S₀` moves `a`": if `a^{s'} = a^u` (`s' ∈ S ∖ S₀`, `u ∈ U`) and `θ ≠ 1` is a
constituent of `a|_K`, then `θ̄ = θ^{s'}` is `U`-conjugate to `θ` (normality), `θ^{u²} = θ`,
`|u|` odd gives `θ = θ̄`, and a real irreducible character of the odd-order `K` is trivial. -/
def Lemma36InvProp (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (K : Subgroup G) : Prop :=
  Compat D C → Sec3Hyp D → K ≤ D.U →
    (∀ u ∈ D.U, ∀ x ∈ K, u * x * u⁻¹ ∈ K) →
    (∀ x ∈ K, D.t1 * x * D.t1⁻¹ = x⁻¹) → (∀ x ∈ K, D.t2 * x * D.t2⁻¹ = x⁻¹) →
    ∀ f, IsCoherent C f → ∀ χ : ClassFunction G ℂ,
    IsIrreducibleCharacter χ → (bset C f χ).Nonempty → (∃ x ∈ K, χ x ≠ χ 1) →
    (∀ ν ∈ bset C f χ, sconj C ν ∈ lamOrbit C ν) →
    ∃ a : ClassFunction ↥(Uin C) ℂ, IsIrreducibleCharacter a ∧
      (∃ u : ↥(Uin C), ((u : ↥C.P.H0) : G) ∈ K ∧ a u ≠ a 1) ∧
      ∃ dχ da : ℕ, χ 1 = dχ ∧ a 1 = da ∧ 2 * D.n * da < dχ

/-- **G11 (new group-theoretic leaf).** Under the hypotheses of Theorem C, `K = K₁ ∩ K₂`
satisfies the hypotheses of L36-INV.  Route: `K` has odd order and `H/U ≅ S`, so `K ≤ U`;
`tᵢ` inverts `Kᵢ ⊇ K`; `C_H(tᵢ)` normalizes `Kᵢ` (maximality clause of `IsMaxInverted`), so
`B ≤ C_H(t₁) ∩ C_H(t₂)` normalizes `K`, `K` normalizes `K`, and `B₁ ∩ K₂` centralizes
`B ⊔ K` (internal direct product); `U = (B₁ ∩ K₂)(B ⊔ K)`. -/
def KInvNormalProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : BGData G) (K1 K2 : Subgroup G),
    ThmCHyps D K1 K2 →
    K1 ⊓ K2 ≤ D.U ∧ (∀ u ∈ D.U, ∀ x ∈ K1 ⊓ K2, u * x * u⁻¹ ∈ K1 ⊓ K2) ∧
    (∀ x ∈ K1 ⊓ K2, D.t1 * x * D.t1⁻¹ = x⁻¹) ∧ (∀ x ∈ K1 ⊓ K2, D.t2 * x * D.t2⁻¹ = x⁻¹)

/-- The form consumed by `C3DegreeProp` / `C4DegreeProp` (PROVED from the two leaves). -/
theorem lemma36_thmC (hL : ∀ (D : BGData G) (C : Sec2Ctx G)
      [Invertible (Nat.card ↥C.P.H0 : ℂ)] (K : Subgroup G), Lemma36InvProp D C K)
    (hG : KInvNormalProp) (D : BGData G) (C : Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (K1 K2 : Subgroup G) (hDC : Compat D C) (hS3 : Sec3Hyp D) (hT : ThmCHyps D K1 K2)
    (f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ) (hf : IsCoherent C f)
    (χ : ClassFunction G ℂ) (hχ : IsIrreducibleCharacter χ) (hne : (bset C f χ).Nonempty)
    (hK : ∃ x ∈ K1 ⊓ K2, χ x ≠ χ 1) (hsl : ∀ ν ∈ bset C f χ, sconj C ν ∈ lamOrbit C ν) :
    ∃ a : ClassFunction ↥(Uin C) ℂ, IsIrreducibleCharacter a ∧
      (∃ u : ↥(Uin C), ((u : ↥C.P.H0) : G) ∈ K1 ⊓ K2 ∧ a u ≠ a 1) ∧
      ∃ dχ da : ℕ, χ 1 = dχ ∧ a 1 = da ∧ 2 * D.n * da < dχ := by
  obtain ⟨hle, hnorm, hi1, hi2⟩ := hG G D K1 K2 hT
  exact hL D C (K1 ⊓ K2) hDC hS3 hle hnorm hi1 hi2 f hf χ hχ hne hK hsl

end Item2

end Work.GW2.C24
