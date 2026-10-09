import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.local_lifting_setup
import Submission.Work.SSGRoute.exists_div_of_char_killing_level
import Submission.Work.SSGRoute.exists_kummerCharacter_of_zmod
import Submission.Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le
import Submission.Work.SSGRoute.isOpen_map_fixingSubgroupEquiv
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise Topology

namespace Work.SSGRoute

/-- **Kummer/Hilbert-90 surjectivity over a closed subgroup of `G_ℚ`.**

This is the auxiliary form of `Work.SSGRoute.exists_kummer_theta_of_decomp` for an arbitrary
*closed* subgroup `H ≤ G_ℚ`: writing `F := ℚ̄^H` for its fixed field (`F.fixingSubgroup = H`),
every continuous character `χ : H →* ZMod (p^a)` (open kernel) is realized, through a primitive
`p^a`-th root of unity `ζ ∈ F` fixed by `H`, by the Kummer character of some `θ ≠ 0`:
`σ θ / θ = ζ ^ (toAdd (χ σ)).val` for all `σ ∈ H`.

The proof transports `χ` to the character `χF` of `↥F.fixingSubgroup` (the two subgroups have the
same carrier, so openness of the kernel is preserved), converts it into the `μ_{p^a}`-valued
character `ω` (`Work.SSGRoute.exists_kummerCharacter_of_zmod`) and thus into a character
`ω' : Gal(ℚ̄/↥F) →* (↥F)ˣ`; the Krull topology supplies a finite-dimensional normal extension
`M` of `↥F` inside `ℚ̄` whose fixing subgroup is killed by `χF`
(`Work.SSGRoute.isOpen_map_fixingSubgroupEquiv` followed by
`Work.SSGRoute.exists_finiteDimensional_normal_fixingSubgroup_le`), and
`Work.SSGRoute.exists_div_of_char_killing_level` (finite Hilbert 90 over `M/↥F`) produces `θ`. -/
theorem exists_kummer_theta_of_closedSubgroup
    (H : Subgroup SSGRoute.GalQ) (hHcl : IsClosed (H : Set SSGRoute.GalQ))
    (p a : ℕ) (hp : p.Prime)
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ (p ^ a))
    (hζH : ∀ σ ∈ H, σ ζ = ζ)
    (χ : ↥H →* Multiplicative (ZMod (p ^ a)))
    (hopen : IsOpen (χ.ker : Set ↥H)) :
    ∃ θ : SSGRoute.QBar, θ ≠ 0 ∧ ∀ σ : ↥H,
      (σ : SSGRoute.GalQ) θ / θ = ζ ^ (Multiplicative.toAdd (χ σ)).val := by
  classical
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  haveI : IsGalois ℚ SSGRoute.QBar := inferInstance
  -- The fixed field of `H`.
  set F : IntermediateField ℚ SSGRoute.QBar := IntermediateField.fixedField H with hFdef
  have hfix : F.fixingSubgroup = H := by
    have h := InfiniteGalois.fixingSubgroup_fixedField (k := ℚ) (K := SSGRoute.QBar)
      ⟨H, hHcl⟩
    simpa [hFdef] using h
  have hζF : ζ ∈ F := by
    rw [hFdef, IntermediateField.mem_fixedField_iff]
    exact hζH
  -- Transport `χ` to `↥F.fixingSubgroup` (same carrier as `H`).
  let χF : ↥(F.fixingSubgroup) →* Multiplicative (ZMod (p ^ a)) :=
    χ.comp (Subgroup.inclusion hfix.le)
  have hopenF : IsOpen (χF.ker : Set ↥(F.fixingSubgroup)) := by
    obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.mp hopen
    have hmem : ∀ y : ↥H, χ y = 1 ↔ (y : SSGRoute.GalQ) ∈ U := by
      intro y
      rw [← MonoidHom.mem_ker]
      exact (Set.ext_iff.mp hUeq y).symm
    have hker : (χF.ker : Set ↥(F.fixingSubgroup)) = Subtype.val ⁻¹' U := by
      ext x
      change χ (Subgroup.inclusion hfix.le x) = 1 ↔ (x : SSGRoute.GalQ) ∈ U
      rw [hmem (Subgroup.inclusion hfix.le x), Subgroup.coe_inclusion]
    rw [hker]
    exact isOpen_induced hUopen
  -- The `μ_{p^a}`-valued character, and its transport to `Gal(ℚ̄/↥F)`.
  obtain ⟨ω, hω⟩ := exists_kummerCharacter_of_zmod F ζ hζ hζF χF
  let e : ↥(F.fixingSubgroup) ≃* (SSGRoute.QBar ≃ₐ[↥F] SSGRoute.QBar) :=
    IntermediateField.fixingSubgroupEquiv F
  let ω' : (SSGRoute.QBar ≃ₐ[↥F] SSGRoute.QBar) →* (↥F)ˣ := ω.comp e.symm.toMonoidHom
  -- Krull: a finite-dimensional normal level over `↥F` killed by `χF`.
  have hopenK : IsOpen
      ((χF.ker.map e.toMonoidHom : Subgroup (SSGRoute.QBar ≃ₐ[↥F] SSGRoute.QBar)) :
        Set (SSGRoute.QBar ≃ₐ[↥F] SSGRoute.QBar)) :=
    isOpen_map_fixingSubgroupEquiv (F := ℚ) (E := SSGRoute.QBar) F χF.ker hopenF
  obtain ⟨M, hMfin, hMnorm, hMsub⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le (U := ↥F) (L := SSGRoute.QBar)
      (χF.ker.map e.toMonoidHom) hopenK
  haveI : FiniteDimensional ↥F M := hMfin
  haveI : Normal ↥F M := hMnorm
  -- `ω'` kills the fixing subgroup of `M`.
  have hω' : ∀ σ : SSGRoute.QBar ≃ₐ[↥F] SSGRoute.QBar, σ ∈ M.fixingSubgroup → ω' σ = 1 := by
    intro σ hσ
    have hσK : σ ∈ (χF.ker.map e.toMonoidHom) := hMsub hσ
    rw [Subgroup.mem_map] at hσK
    obtain ⟨x, hxker, hx⟩ := hσK
    have hx1 : χF x = 1 := MonoidHom.mem_ker.mp hxker
    have hωx : (((ω x : (↥F)ˣ) : ↥F) : SSGRoute.QBar) = 1 := by
      simp [hω x, hx1]
    have hx' : ω' σ = ω x := by
      have hxs : e.symm σ = x := by
        rw [← hx]
        simp
      show ω (e.symm σ) = ω x
      rw [hxs]
    rw [hx']
    exact Units.ext (Subtype.ext (by simpa using hωx))
  -- Finite Hilbert 90 over `M/↥F`.
  obtain ⟨θ, hθne, hθ⟩ := exists_div_of_char_killing_level F M ω' hω'
  refine ⟨θ, hθne, fun σ₀ => ?_⟩
  let x : ↥(F.fixingSubgroup) := ⟨(σ₀ : SSGRoute.GalQ), by rw [hfix]; exact σ₀.2⟩
  have hxval : (x : SSGRoute.GalQ) = (σ₀ : SSGRoute.GalQ) := rfl
  have hχx : χF x = χ σ₀ := by
    have hincl : Subgroup.inclusion hfix.le x = σ₀ := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion, hxval]
    show χ (Subgroup.inclusion hfix.le x) = χ σ₀
    rw [hincl]
  have hω'x : ω' (e x) = ω x := by simp [ω']
  have happ : (e x) θ = (σ₀ : SSGRoute.GalQ) θ := rfl
  calc (σ₀ : SSGRoute.GalQ) θ / θ
      = (e x) θ / θ := by rw [happ]
    _ = algebraMap ↥F SSGRoute.QBar (((ω' (e x) : (↥F)ˣ) : ↥F)) := hθ (e x)
    _ = algebraMap ↥F SSGRoute.QBar (((ω x : (↥F)ˣ) : ↥F)) := by rw [hω'x]
    _ = ζ ^ (Multiplicative.toAdd (χF x)).val := by
          simpa [IntermediateField.algebraMap_apply] using hω x
    _ = ζ ^ (Multiplicative.toAdd (χ σ₀)).val := by rw [hχx]

/-- **Kummer/Hilbert-90 surjectivity over the decomposition field.**

Let `A` be a place of `ℚ̄`, `p` a prime, `a ≥ 0`, `ζ` a primitive `p ^ a`-th root of unity in `ℚ̄`
fixed by `D_A = decomp ℚ A` (equivalently `μ_{p^a} ⊆ F := ℚ̄^{D_A}`), and let
`χ : D_A → μ_{p^a} ≅ ZMod (p ^ a)` be a continuous character (open kernel). Then there is a nonzero
`θ : ℚ̄` whose Kummer character is `χ`: for all `σ ∈ D_A`, `σ θ / θ = ζ ^ (toAdd (χ σ)).val`.

Equivalently: the Kummer map `Fˣ/(Fˣ)^{p^a} → Hom(D_A, μ_{p^a})`, `[θ] ↦ (σ ↦ σ θ / θ)` restricted
to `p^a`-th roots of elements of `F`, is surjective, where `D_A = F.fixingSubgroup` for
`F = IntermediateField.fixedField (decomp ℚ A)` (this subgroup is closed, see
`Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring`).

Proved from `Work.AbsoluteKummer.Hilbert90.exists_div_of_isCrossedHom` (Hilbert 90 for the absolute
Galois group) with `k := ↥F`, or from `Work.AbsoluteKummer.Kummer.exists_kummerCocycle_eq`,
transported along an algebra isomorphism `AlgebraicClosure ↥F ≃ₐ[↥F] ℚ̄` (`IsAlgClosure ↥F QBar`). -/
lemma exists_kummer_theta_of_decomp (p a : ℕ) (hp : p.Prime)
    (A : ValuationSubring SSGRoute.QBar)
    (hμ : ∀ ζ : SSGRoute.QBar, IsPrimitiveRoot ζ (p ^ a) →
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ζ = ζ)
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ (p ^ a))
    (χ : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ a)))
    (hopen : IsOpen (χ.ker : Set ↥(SSGRoute.decomp ℚ A))) :
    ∃ θ : SSGRoute.QBar, θ ≠ 0 ∧ ∀ σ : ↥(SSGRoute.decomp ℚ A),
      (σ : SSGRoute.GalQ) θ / θ = ζ ^ (Multiplicative.toAdd (χ σ)).val := by
  refine exists_kummer_theta_of_closedSubgroup (SSGRoute.decomp ℚ A) ?_ p a hp ζ hζ ?_ χ hopen
  · exact Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
  · intro σ hσ
    exact hμ ζ hζ σ hσ

end Work.SSGRoute
