import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-
# Existence of a nontrivial block of imprimitivity from an intermediate subfield

Given an irreducible separable `p : ℚ[X]` and an element `α` of the abstract field
`K = AdjoinRoot p` which is neither rational nor a generator of `K`, we produce a
nontrivial block for the action of the Galois group `p.Gal` on the roots of `p`.

The block is the `e`-image of the fibre of the evaluation map
`x ↦ (the ℚ-algebra map `AdjoinRoot p →ₐ[ℚ] p.SplittingField` sending the root to `x`) α`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Polynomial

namespace Commons.NumberTheory.NumberField

section Setup

variable {p : Polynomial ℚ} [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)]

private noncomputable def psi (x : p.rootSet p.SplittingField) :
    AdjoinRoot p →ₐ[ℚ] p.SplittingField :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId ℚ p.SplittingField) x.1 (by
    have h := (Polynomial.mem_rootSet.mp x.2).2
    rwa [Polynomial.aeval_def] at h)

private lemma psi_root (x : p.rootSet p.SplittingField) :
    psi x (AdjoinRoot.root p) = x.1 :=
  AdjoinRoot.liftAlgHom_root p (Algebra.ofId ℚ p.SplittingField) x.1 _

private lemma psi_injective (x y : p.rootSet p.SplittingField) (h : psi x = psi y) : x = y := by
  apply Subtype.ext
  have h2 := congrArg (fun g : AdjoinRoot p →ₐ[ℚ] p.SplittingField => g (AdjoinRoot.root p)) h
  simpa [psi_root] using h2

private noncomputable def Q (σ : p.Gal) (x : p.rootSet p.SplittingField) :
    p.rootSet p.SplittingField :=
  ⟨σ x.1, Polynomial.rootSet_mapsTo σ.toAlgHom x.2⟩

private lemma Q_coe (σ : p.Gal) (x : p.rootSet p.SplittingField) : (Q σ x).1 = σ x.1 := rfl

private noncomputable def R : p.rootSet p.SplittingField ≃ p.rootSet p.SplittingField :=
  Polynomial.Gal.rootsEquivRoots p p.SplittingField

private lemma galActionHom_eq (σ : p.Gal) (x : p.rootSet p.SplittingField) :
    (Polynomial.Gal.galActionHom p p.SplittingField σ) x = R (Q σ (R.symm x)) := by
  show (σ • x) = R (Q σ (R.symm x))
  rw [Polynomial.Gal.smul_def]
  rfl

private lemma psi_Q (σ : p.Gal) (x : p.rootSet p.SplittingField) :
    psi (Q σ x) = σ.toAlgHom.comp (psi x) := by
  apply AdjoinRoot.algHom_ext
  rw [psi_root]
  show (Q σ x).1 = σ ((psi x) (AdjoinRoot.root p))
  rw [psi_root]
  rfl

private noncomputable def ev (α : AdjoinRoot p) (x : p.rootSet p.SplittingField) :
    p.SplittingField :=
  psi x α

private lemma ev_Q (α : AdjoinRoot p) (σ : p.Gal) (x : p.rootSet p.SplittingField) :
    ev α (Q σ x) = σ (ev α x) := by
  show psi (Q σ x) α = σ (psi x α)
  rw [psi_Q]
  rfl

private lemma permCongr_image (e : p.rootSet p.SplittingField ≃ Fin p.natDegree)
    (g : Equiv.Perm (p.rootSet p.SplittingField)) (S : Set (p.rootSet p.SplittingField)) :
    (e.permCongr g) '' (e '' S) = e '' (g '' S) := by
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨g x, ⟨x, hx, rfl⟩, by rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]⟩
  · rintro ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, by rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]⟩

private lemma galActionHom_image_R (σ : p.Gal) (S : Set (p.rootSet p.SplittingField)) :
    (Polynomial.Gal.galActionHom p p.SplittingField σ) '' (R '' S) = R '' (Q σ '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨Q σ z, ⟨z, hz, rfl⟩, by rw [galActionHom_eq, Equiv.symm_apply_apply]⟩
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨R z, ⟨z, hz, rfl⟩, by rw [galActionHom_eq, Equiv.symm_apply_apply]⟩

end Setup

end Commons.NumberTheory.NumberField

namespace Commons.NumberTheory.NumberField

open Polynomial

theorem exists_nontrivial_block_of_intermediate {p : Polynomial ℚ} (hp : Irreducible p)
    (hsep : p.Separable) [Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits)]
    (e : p.rootSet p.SplittingField ≃ Fin p.natDegree) {α : AdjoinRoot p}
    (hα : Algebra.adjoin ℚ ({α} : Set (AdjoinRoot p)) ≠ ⊤)
    (hrat : α ∉ Set.range (algebraMap ℚ (AdjoinRoot p))) :
    ∃ B : Set (Fin p.natDegree), ¬ B.Subsingleton ∧ B ≠ Set.univ ∧
      ∀ σ τ : p.Gal,
        (e.permCongr (Polynomial.Gal.galActionHom p p.SplittingField σ)) '' B ≠
          (e.permCongr (Polynomial.Gal.galActionHom p p.SplittingField τ)) '' B →
        Disjoint ((e.permCongr (Polynomial.Gal.galActionHom p p.SplittingField σ)) '' B)
          ((e.permCongr (Polynomial.Gal.galActionHom p p.SplittingField τ)) '' B) := by
  classical
  letI : Algebra ℚ (AdjoinRoot p) := AdjoinRoot.instAlgebra p
  haveI hFac : Fact (Irreducible p) := ⟨hp⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  haveI hSplits : p.IsSplittingField ℚ p.SplittingField := IsSplittingField.splittingField p
  haveI hGal : IsGalois ℚ p.SplittingField := IsGalois.of_separable_splitting_field hsep
  haveI hFD : FiniteDimensional ℚ p.SplittingField := inferInstance
  haveI hAlg : Algebra.IsAlgebraic ℚ (AdjoinRoot p) := by
    have hb := AdjoinRoot.powerBasis hp0
    haveI hfin : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.of_basis hb.basis
    exact Algebra.IsAlgebraic.of_finite ℚ (AdjoinRoot p)
  have hn : 0 < p.natDegree := hp.natDegree_pos
  have hcard : Fintype.card (p.rootSet p.SplittingField) = p.natDegree :=
    Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits p)
  haveI hne : Nonempty (p.rootSet p.SplittingField) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; exact hn)
  obtain ⟨x₀⟩ := hne
  set β : p.SplittingField := ev α x₀ with hβ
  -- M = ℚ(α) ⊆ AdjoinRoot p
  let M : IntermediateField ℚ (AdjoinRoot p) :=
    IntermediateField.adjoin ℚ ({α} : Set (AdjoinRoot p))
  have hM_toSub : M.toSubalgebra = Algebra.adjoin ℚ ({α} : Set (AdjoinRoot p)) :=
    IntermediateField.adjoin_toSubalgebra _
  have hM_ne : M ≠ ⊤ := by
    intro h
    apply hα
    have h2 : M.toSubalgebra = ⊤ := by rw [h]; rfl
    rwa [hM_toSub] at h2
  have hroot_notin : AdjoinRoot.root p ∉ M := by
    intro ht
    apply hM_ne
    have hle : Algebra.adjoin ℚ ({AdjoinRoot.root p} : Set (AdjoinRoot p)) ≤ M.toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ht
    rw [show Algebra.adjoin ℚ ({AdjoinRoot.root p} : Set (AdjoinRoot p)) = ⊤
        from AdjoinRoot.adjoinRoot_eq_top] at hle
    have htop : M.toSubalgebra = ⊤ := top_le_iff.mp hle
    exact IntermediateField.toSubalgebra_injective (by rw [htop]; rfl)
  -- L' = ψ(M) = ℚ(β)
  let L' : IntermediateField ℚ p.SplittingField := IntermediateField.map (psi x₀) M
  have hβL' : β ∈ L' := by
    change β ∈ IntermediateField.map (psi x₀) M
    rw [IntermediateField.mem_map]
    exact ⟨α, IntermediateField.mem_adjoin_simple_self ℚ α, hβ.symm⟩
  have hx₀_notin : x₀.1 ∉ L' := by
    intro hx
    apply hroot_notin
    change x₀.1 ∈ IntermediateField.map (psi x₀) M at hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨m, hm, hpm⟩ := hx
    have : m = AdjoinRoot.root p := by
      apply RingHom.injective (psi x₀).toRingHom
      simpa using hpm.trans (psi_root x₀).symm
    rwa [this] at hm
  obtain ⟨σ, hσ_mem, hσ_ne⟩ : ∃ σ : p.Gal, σ ∈ L'.fixingSubgroup ∧ σ x₀.1 ≠ x₀.1 := by
    have h : x₀.1 ∉ IntermediateField.fixedField L'.fixingSubgroup := by
      rwa [IsGalois.fixedField_fixingSubgroup L']
    rw [IntermediateField.mem_fixedField_iff] at h
    push Not at h
    exact h
  have hσβ : σ β = β :=
    (IntermediateField.mem_fixingSubgroup_iff L' σ).mp hσ_mem β hβL'
  set F₀ : Set (p.rootSet p.SplittingField) := {x | ev α x = β} with hF₀
  set B : Set (Fin p.natDegree) := e '' (R '' F₀) with hB
  have hx₀_mem : x₀ ∈ F₀ := by rw [hF₀]; exact hβ.symm
  have hy_mem : Q σ x₀ ∈ F₀ := by
    rw [hF₀]
    show ev α (Q σ x₀) = β
    rw [ev_Q, show ev α x₀ = β from hβ.symm, hσβ]
  have hy_ne : Q σ x₀ ≠ x₀ := by
    intro h
    exact hσ_ne ((Q_coe σ x₀).symm.trans (congrArg Subtype.val h))
  have hF₀_ns : ¬ F₀.Subsingleton := by
    intro hs
    exact hy_ne (hs hy_mem hx₀_mem)
  have hF₀_ne_univ : F₀ ≠ Set.univ := by
    intro huniv
    have hconst : ∀ x : p.rootSet p.SplittingField, ev α x = β := by
      intro x
      have : x ∈ F₀ := by rw [huniv]; trivial
      rwa [hF₀] at this
    have hfix : ∀ ρ : p.Gal, ρ β = β := by
      intro ρ
      have h1 : ev α (Q ρ x₀) = ρ β := by rw [ev_Q α ρ x₀]
      rw [hconst (Q ρ x₀)] at h1
      exact h1.symm
    have hmem : β ∈ IntermediateField.fixedField
        (⊤ : Subgroup (p.SplittingField ≃ₐ[ℚ] p.SplittingField)) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro ρ _
      exact hfix ρ
    rw [IsGalois.fixedField_top] at hmem
    change β ∈ Set.range (algebraMap ℚ p.SplittingField) at hmem
    obtain ⟨c, hc⟩ := hmem
    refine hrat ⟨c, ?_⟩
    have hkey : psi x₀ (algebraMap ℚ (AdjoinRoot p) c) = psi x₀ α := by
      rw [AlgHom.commutes, hc]
      exact hβ
    exact RingHom.injective (psi x₀).toRingHom hkey
  have hQ : ∀ ρ : p.Gal,
      Q ρ '' {x : p.rootSet p.SplittingField | ev α x = β} = {y | ev α y = ρ β} := by
    intro ρ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show ev α (Q ρ x) = ρ β
      rw [ev_Q α ρ x, hx]
    · intro hy
      refine ⟨Q ρ⁻¹ y, ?_, ?_⟩
      · show ev α (Q ρ⁻¹ y) = β
        rw [ev_Q α ρ⁻¹ y, hy]
        rw [show ρ⁻¹ = ρ.symm from rfl]
        exact AlgEquiv.symm_apply_apply ρ β
      · ext
        rw [Q_coe, Q_coe, show ρ⁻¹ = ρ.symm from rfl]
        exact AlgEquiv.apply_symm_apply ρ ↑y
  have himage : ∀ ρ : p.Gal,
      (e.permCongr (Polynomial.Gal.galActionHom p p.SplittingField ρ)) '' B
        = e '' (R '' {y | ev α y = ρ β}) := by
    intro ρ
    rw [hB, permCongr_image, galActionHom_image_R, hF₀, hQ ρ]
  refine ⟨B, ?_, ?_, ?_⟩
  · rw [hB]
    intro hs
    apply hF₀_ns
    intro a ha b hb
    apply R.injective
    apply e.injective
    exact hs ⟨R a, ⟨a, ha, rfl⟩, rfl⟩ ⟨R b, ⟨b, hb, rfl⟩, rfl⟩
  · rw [hB]
    intro h
    apply hF₀_ne_univ
    ext x
    constructor
    · intro _; trivial
    · intro _
      have hx : e (R x) ∈ e '' (R '' F₀) := by rw [h]; trivial
      obtain ⟨y, hy, hyeq⟩ := hx
      obtain ⟨z, hz, hzy⟩ := hy
      have hzy' : R z = R x := hzy.trans (e.injective hyeq)
      have : z = x := R.injective hzy'
      rw [this] at hz
      exact hz
  · intro ρ τ hne
    have hβne : ρ β ≠ τ β := by
      intro h
      exact hne (by rw [himage ρ, himage τ, h])
    rw [himage ρ, himage τ, Set.disjoint_left]
    rintro u ⟨v, hv, rfl⟩ ⟨v', hv', hv'e⟩
    obtain ⟨a, ha, rfl⟩ := hv
    obtain ⟨b, hb, hbR⟩ := hv'
    have h1 : R b = R a := by
      apply e.injective
      rw [hbR]
      exact hv'e
    have h2 : b = a := R.injective h1
    exact hβne (by rw [← ha, ← h2, hb])

end Commons.NumberTheory.NumberField