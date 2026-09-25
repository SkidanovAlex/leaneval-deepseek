import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic

/-!
# The Galois group of the Frattini layer is elementary abelian of exponent `3`

The Frattini layer `frattiniLayer F Ω` is the compositum, computed inside `Ω`, of all cubic
everywhere unramified Galois extensions `M/F` (the set `cubicUnramifiedSet F Ω`).  Each such `M`
has `Gal(↥M/F)` of order `3`.  Restricting an automorphism of the compositum to each factor gives
an injective group homomorphism into a product of groups of order `3`; a subgroup of a product of
commutative groups of exponent `3` is itself commutative of exponent `3`.  Hence
`Gal(frattiniLayer/F)` is a `3`-group of exponent `3`, and the extension is abelian Galois.

The group-theoretic core is isolated as `galoisGroup_iSup_cubic`, which is stated for an arbitrary
compositum `⨆ i, K i` of Galois extensions of degree `3` inside a common field.
-/

namespace Work.Tower.FrattiniLayer

/-- **The Galois group of a compositum of cubic Galois extensions** (inside a common field `Ω`) is
a `3`-group of exponent `3`, and in fact commutative.  Formally: for a family `K : ι → ` intermediate
fields of `Ω/F` with `K i / F` Galois of degree `3`, the group `Gal(↥(⨆ i, K i)/F)` is a `3`-group,
commutative, and every element has order dividing `3`.

The proof restricts automorphisms of the compositum to each factor `K i` (viewed inside the
compositum as `IntermediateField.restrict`), obtaining an injective homomorphism into the product
of the (commutative, exponent `3`) groups `Gal(↥(K i)/F)`. -/
theorem galoisGroup_iSup_cubic {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {ι : Type*} (K : ι → IntermediateField F Ω)
    (hG : ∀ i, IsGalois F ↥(K i)) (hD : ∀ i, Module.finrank F ↥(K i) = 3) :
    IsPGroup 3 (Gal(↥(⨆ i, K i)/F)) ∧
      IsMulCommutative (Gal(↥(⨆ i, K i)/F)) ∧
      (∀ σ : Gal(↥(⨆ i, K i)/F), σ ^ 3 = 1) := by
  haveI := hG
  -- `E i` is the factor `K i`, viewed as an intermediate field of the compositum.
  let E : ∀ i, IntermediateField F ↥(⨆ j, K j) := fun i =>
    IntermediateField.restrict (le_iSup K i)
  haveI hEnormal : ∀ i, Normal F ↥(E i) := fun i => by
    haveI : Normal F ↥(K i) := (hG i).to_normal
    exact Normal.of_algEquiv (IntermediateField.restrictAlgEquiv (le_iSup K i))
  haveI hEgalois : ∀ i, IsGalois F ↥(E i) := fun i =>
    IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv (le_iSup K i))
  have hD' : ∀ i, Module.finrank F ↥(E i) = 3 := fun i =>
    (LinearEquiv.finrank_eq
        (IntermediateField.restrictAlgEquiv (le_iSup K i)).toLinearEquiv).symm.trans (hD i)
  have hcard : ∀ i, Nat.card Gal(↥(E i)/F) = 3 := fun i => by
    haveI : FiniteDimensional F ↥(E i) :=
      FiniteDimensional.of_finrank_pos (by rw [hD' i]; norm_num)
    rw [IsGalois.card_aut_eq_finrank F ↥(E i), hD' i]
  have h3E : ∀ i (g : Gal(↥(E i)/F)), g ^ 3 = 1 := fun i g => by
    have h : orderOf g ∣ 3 := by
      rw [← hcard i]; exact orderOf_dvd_natCard g
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hcommE : ∀ i, IsMulCommutative Gal(↥(E i)/F) := fun i => by
    haveI : IsCyclic Gal(↥(E i)/F) := isCyclic_of_prime_card (p := 3) (hcard i)
    exact IsCyclic.isMulCommutative
  -- The restriction homomorphisms to the factors.
  let ρ : ∀ i, Gal(↥(⨆ j, K j)/F) →* Gal(↥(E i)/F) := fun i =>
    AlgEquiv.restrictNormalHom ↥(E i)
  -- The factors exhaust the compositum.
  have htop : (⨆ i, E i) = ⊤ := by
    apply IntermediateField.lift_injective (F := ⨆ j, K j)
    rw [IntermediateField.lift_top]
    refine le_antisymm (IntermediateField.lift_le _) (iSup_le fun j => ?_)
    · rw [← IntermediateField.lift_restrict (le_iSup K j)]
      exact IntermediateField.map_mono _ (le_iSup E j)
  -- Joint injectivity of the restrictions.
  have key : ∀ σ : Gal(↥(⨆ j, K j)/F), (∀ i, ρ i σ = 1) → σ = 1 := by
    intro σ hσ
    have hfix : (⊤ : IntermediateField F ↥(⨆ j, K j)) ≤
        IntermediateField.fixedField (Subgroup.zpowers σ) := by
      rw [← htop]
      apply iSup_le
      intro i
      rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
        IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact (AlgEquiv.restrictNormal_eq_one_iff (E i) σ).mp (hσ i) x hx
    have hmem : σ ∈ IntermediateField.fixingSubgroup (⊤ : IntermediateField F ↥(⨆ j, K j)) :=
      (IntermediateField.le_iff_le (Subgroup.zpowers σ)
        (⊤ : IntermediateField F ↥(⨆ j, K j))).mp hfix (Subgroup.mem_zpowers σ)
    rw [IntermediateField.fixingSubgroup_top] at hmem
    simpa using hmem
  have h3 : ∀ σ : Gal(↥(⨆ j, K j)/F), σ ^ 3 = 1 := fun σ =>
    key (σ ^ 3) fun i => by
      show ρ i (σ ^ 3) = 1
      rw [map_pow]; exact h3E i _
  refine ⟨?_, ?_, h3⟩
  · intro σ
    exact ⟨1, by simpa using h3 σ⟩
  · refine IsMulCommutative.of_comm fun σ τ => ?_
    have h : σ * τ * (τ * σ)⁻¹ = 1 := key _ fun i => by
      show ρ i (σ * τ * (τ * σ)⁻¹) = 1
      rw [map_mul, map_mul, map_inv, map_mul,
        IsMulCommutative.is_comm.comm (ρ i τ) (ρ i σ), mul_inv_cancel]
    exact mul_inv_eq_one.mp h

/-- **The Galois group of the Frattini layer of a number field is elementary abelian of exponent
`3`.**  The Frattini layer `frattiniLayer F Ω` is the compositum of the cubic everywhere unramified
Galois extensions of `F` inside `Ω`; its automorphism group over `F` is a `3`-group, the extension
`frattiniLayer F Ω / F` is abelian Galois, and every automorphism has order dividing `3`. -/
theorem frattiniLayer_galoisGroup {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] :
    IsPGroup 3 (↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω) ≃ₐ[F]
      ↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω)) ∧
    IsAbelianGalois F ↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω) ∧
    (∀ σ : ↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω) ≃ₐ[F]
      ↥(Work.Tower.FrattiniLayer.frattiniLayer F Ω), σ ^ 3 = 1) := by
  have key := galoisGroup_iSup_cubic (F := F) (Ω := Ω)
    (K := fun M : ↥(cubicUnramifiedSet F Ω) => (M : IntermediateField F Ω))
    (fun M => M.2.2.1) (fun M => M.2.1)
  haveI hN : ∀ M : ↥(cubicUnramifiedSet F Ω), Normal F ↥(M : IntermediateField F Ω) :=
    fun M => (M.2.2.1).to_normal
  haveI hSep : ∀ M : ↥(cubicUnramifiedSet F Ω),
      Algebra.IsSeparable F ↥(M : IntermediateField F Ω) :=
    fun M => (M.2.2.1).to_isSeparable
  haveI hgal : IsGalois F ↥(frattiniLayer F Ω) :=
    { to_normal := IntermediateField.normal_iSup F Ω
        (fun M : ↥(cubicUnramifiedSet F Ω) => (M : IntermediateField F Ω))
      to_isSeparable := IntermediateField.isSeparable_iSup F Ω
        (t := fun M : ↥(cubicUnramifiedSet F Ω) => (M : IntermediateField F Ω)) }
  haveI hcomm : IsMulCommutative Gal(↥(frattiniLayer F Ω)/F) := key.2.1
  refine ⟨key.1, ?_, key.2.2⟩
  exact { }

end Work.Tower.FrattiniLayer
