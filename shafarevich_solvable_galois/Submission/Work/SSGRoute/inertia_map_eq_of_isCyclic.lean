import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

-- GUIDANCE (requester). This is the "totally ramified" half of condition (ii) of
-- Schmidt-Wingberg's Theorem 15: if the local group `(decomp Q A).map ψ` is cyclic of
-- exponent dividing the prime `p` and some inertia element has nontrivial image, then the image
-- of the inertia group is the whole local group.
-- PROOF: `hne` gives a nontrivial subgroup `C := ψ(I_A) ≤ H := ψ(D_A)`; `hCyc` writes
-- `H = Subgroup.zpowers g` and `hexp` gives `g ^ p = 1`.  From `C ≠ ⊥` pick `c ∈ C`, `c ≠ 1`,
-- `c = g ^ m` (`Subgroup.mem_zpowers_iff`); `p ∤ m` (as `p ∣ n → g ^ n = 1`); by Bezout
-- (`Int.gcd_eq_gcd_ab` with `Int.gcd m p = 1`) `a * m + b * p = 1`, so
-- `g = g ^ (a*m + b*p) = (g ^ m) ^ a * (g ^ p) ^ b = c ^ a ∈ C`; hence `H = ⟨g⟩ ⊆ C`.
-- For inertia elements use the SUBGROUP structure: `Work.SSGRoute.mem_inertiaSubgroup_iff`
-- (`Submission/Work/SSGRoute/ramified_char_lift.lean`) identifies
-- `σ ∈ ValuationSubring.inertiaSubgroup ℚ A ↔ SSGRoute.IsInertia ℚ A σ` for
-- `σ : ↥(SSGRoute.decomp ℚ A)`; powers of `c` are then inertia.  If that file is unavailable,
-- prove directly that `{σ | IsInertia ℚ A σ}` is closed under products and inverses, using that
-- for `σ ∈ decomp ℚ A` the predicate `A.valuation z < 1` is preserved by `z ↦ σ z`
-- (`ValuationSubring.valuation_lt_one_iff`, `IsLocalRing.mem_maximalIdeal`, and the
-- `MulSemiringAction ↥(decomp ℚ A) ↥A` by ring automorphisms).
-- USEFUL: `isCyclic_iff_exists_zpowers_eq_top`, `Subgroup.isCyclic_iff_exists_zpowers_eq_top`,
-- `Subgroup.mem_zpowers_iff`, `zpow_mul`, `Int.gcd_eq_gcd_ab`,
-- `Nat.Prime.eq_one_or_self_of_dvd`, `Subgroup.mem_map`.

open _root_.SSGRoute

/-! ## The inertia subgroup of the decomposition group and inertia elements

The Mathlib subgroup `ValuationSubring.inertiaSubgroup ℚ A ≤ ↥(decomp ℚ A)` is the kernel of the
action of the decomposition group on the residue field of `A`.  The local predicate
`SSGRoute.IsInertia ℚ A σ` says instead that `σ` stabilises `A` and moves every element of `A` by
something of valuation `< 1`.  The two agree, and this section records the equivalence in both
directions (the "backwards" one is what lets us *manufacture* inertia elements out of subgroup
elements, the "forwards" one is what lets us recognise them). -/

/-- The action of the decomposition group on `A` is the Galois action on the ambient field. -/
private lemma coe_smul_val {A : ValuationSubring QBar} (σ : ↥(decomp ℚ A)) (x : ↥A) :
    ((σ • x : ↥A) : QBar) = (σ : GalQ) x := rfl

/-- Every element of the inertia subgroup `ValuationSubring.inertiaSubgroup ℚ A` is an inertia
element in the sense of `SSGRoute.IsInertia`. -/
lemma isInertia_of_mem_inertiaSubgroup {A : ValuationSubring QBar}
    {σ : ↥(decomp ℚ A)} (h : σ ∈ ValuationSubring.inertiaSubgroup ℚ A) :
    IsInertia ℚ A (σ : GalQ) := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at h
  refine ⟨σ.2, ?_⟩
  intro x hx
  have hres : ∀ b : ↥A, (IsLocalRing.residue ↥A) (σ • b) = (IsLocalRing.residue ↥A) b := by
    intro b
    have h1 : σ • (IsLocalRing.residue ↥A) b = (IsLocalRing.residue ↥A) b := by
      have h2 := congrArg (fun f : RingAut (IsLocalRing.ResidueField ↥A) =>
        f ((IsLocalRing.residue ↥A) b)) h
      simpa using h2
    rw [IsLocalRing.ResidueField.residue_smul]
    exact h1
  have hmem : (σ • (⟨x, hx⟩ : ↥A) - ⟨x, hx⟩) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  have hv := (ValuationSubring.valuation_lt_one_iff A (σ • (⟨x, hx⟩ : ↥A) - ⟨x, hx⟩)).mp hmem
  have hcoe : ((σ • (⟨x, hx⟩ : ↥A) - ⟨x, hx⟩ : ↥A) : QBar) = (σ : GalQ) x - x := rfl
  rwa [hcoe] at hv

/-- An inertia element of the decomposition group lies in
`ValuationSubring.inertiaSubgroup ℚ A`. -/
lemma mem_inertiaSubgroup_of_isInertia {A : ValuationSubring QBar}
    (σ : ↥(decomp ℚ A)) (h : IsInertia ℚ A (σ : GalQ)) :
    σ ∈ ValuationSubring.inertiaSubgroup ℚ A := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  ext r
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective r
  have hv : A.valuation ((σ : GalQ) (b : QBar) - (b : QBar)) < 1 := h.2 (b : QBar) b.2
  have hmem : (σ • b - b) ∈ IsLocalRing.maximalIdeal ↥A := by
    refine (ValuationSubring.valuation_lt_one_iff A (σ • b - b)).mpr ?_
    have hcoe : ((σ • b - b : ↥A) : QBar) = (σ : GalQ) (b : QBar) - (b : QBar) := rfl
    rwa [hcoe]
  have h1 : (IsLocalRing.residue ↥A) (σ • b - b) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  rw [map_sub, sub_eq_zero] at h1
  have h2 : (MulSemiringAction.toRingAut (↥(A.decompositionSubgroup ℚ))
      (IsLocalRing.ResidueField ↥A)) σ ((IsLocalRing.residue ↥A) b)
      = σ • ((IsLocalRing.residue ↥A) b) := rfl
  rw [h2, ← IsLocalRing.ResidueField.residue_smul]
  exact h1

/-- `ValuationSubring.inertiaSubgroup ℚ A` is exactly the set of inertia elements of the
decomposition group. -/
lemma isInertia_iff_mem_inertiaSubgroup {A : ValuationSubring QBar} (σ : ↥(decomp ℚ A)) :
    σ ∈ ValuationSubring.inertiaSubgroup ℚ A ↔ IsInertia ℚ A (σ : GalQ) :=
  ⟨isInertia_of_mem_inertiaSubgroup, mem_inertiaSubgroup_of_isInertia σ⟩

/-! ## The main lemma -/

theorem inertia_map_eq_of_isCyclic {Γ : Type*} [Group Γ] (p : ℕ) [Fact p.Prime]
    (ψ : GalQ →* Γ) (A : ValuationSubring QBar)
    (hexp : ∀ g ∈ (decomp ℚ A).map ψ, g ^ p = 1)
    (hCyc : IsCyclic ↥((decomp ℚ A).map ψ))
    (hne : ∃ σ : GalQ, IsInertia ℚ A σ ∧ ψ σ ≠ 1) :
    ∀ σ ∈ decomp ℚ A, ∃ τ, IsInertia ℚ A τ ∧ ψ τ = ψ σ := by
  classical
  intro σ hσ
  -- `H = ψ(D_A)` is cyclic; pick a generator `g` and note `g ^ p = 1`.
  obtain ⟨g, hg⟩ :=
    (Subgroup.isCyclic_iff_exists_zpowers_eq_top ((decomp ℚ A).map ψ)).mp hCyc
  have hgp : g ^ p = 1 := hexp g (hg ▸ Subgroup.mem_zpowers g)
  -- a nontrivial inertia element whose image is nontrivial
  obtain ⟨σ₀, hσ₀I, hσ₀ne⟩ := hne
  have hτ₀ : (⟨σ₀, hσ₀I.1⟩ : ↥(decomp ℚ A)) ∈ ValuationSubring.inertiaSubgroup ℚ A :=
    mem_inertiaSubgroup_of_isInertia _ hσ₀I
  -- `C = ψ(I_A) ≤ H` contains the nontrivial element `ψ σ₀`
  set C : Subgroup Γ :=
    (ValuationSubring.inertiaSubgroup ℚ A).map
      (ψ.comp (Subgroup.subtype (decomp ℚ A))) with hCdef
  have hc_mem : ψ σ₀ ∈ C := ⟨⟨σ₀, hσ₀I.1⟩, hτ₀, rfl⟩
  -- hence `ψ σ₀ = g ^ m` with `p ∤ m`, and Bézout puts `g = (ψ σ₀) ^ a` back into `C`
  have hg_mem_C : g ∈ C := by
    have hmemH : ψ σ₀ ∈ Subgroup.zpowers g := by
      rw [hg]; exact ⟨σ₀, hσ₀I.1, rfl⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmemH
    have hnotdvd : ¬ (p : ℤ) ∣ m := by
      rintro ⟨m', hm'⟩
      have h1 : g ^ m = 1 := by
        rw [hm', zpow_mul, zpow_natCast, hgp, one_zpow]
      exact hσ₀ne (by rw [← hm]; exact h1)
    have hnotdvd' : ¬ p ∣ m.natAbs := by
      intro hd
      exact hnotdvd ((Int.dvd_natAbs (a := (p : ℤ)) (b := m)).mp (by
        rw [Int.natCast_dvd_natCast]; exact hd))
    have hcop : Nat.Coprime m.natAbs p :=
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hnotdvd').symm
    have hgcd : Int.gcd m (p : ℤ) = 1 := by
      rw [Int.gcd_def, Int.natAbs_natCast]
      exact hcop.gcd_eq_one
    have hbez : m * m.gcdA (p : ℤ) + (p : ℤ) * m.gcdB (p : ℤ) = 1 := by
      have h := Int.gcd_eq_gcd_ab m (p : ℤ)
      rw [hgcd] at h
      simpa using h.symm
    have hg_eq : g = (ψ σ₀) ^ (m.gcdA (p : ℤ)) := by
      have h2 : g ^ (m * m.gcdA (p : ℤ) + (p : ℤ) * m.gcdB (p : ℤ)) = g := by
        rw [hbez, zpow_one]
      rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, hgp, one_zpow, mul_one] at h2
      rw [hm] at h2
      exact h2.symm
    rw [hg_eq]
    exact Subgroup.zpow_mem _ hc_mem _
  -- therefore `H = ⟨g⟩ ≤ C`, and `ψ σ ∈ C` is an image of an inertia element
  have hpsi_mem : ψ σ ∈ C := by
    refine (Subgroup.zpowers_le.mpr hg_mem_C) ?_
    exact hg.symm ▸ ⟨σ, hσ, rfl⟩
  obtain ⟨τ, hτI, hτψ⟩ := Subgroup.mem_map.mp hpsi_mem
  exact ⟨(τ : GalQ), isInertia_of_mem_inertiaSubgroup hτI, hτψ⟩

end Work.SSGRoute
