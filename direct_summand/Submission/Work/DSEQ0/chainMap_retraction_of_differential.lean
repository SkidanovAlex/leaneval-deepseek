import Mathlib
import Submission.Work.DSEQ0.Basic
import Submission.Work.DSEQ0.Model
import Submission.Work.DSEQ0.chainMap_retraction_of_functional

/-!
# DSEQ0: a chain-level retraction from a functional on `P⁰`

This is the general form of `Work.DSEQ0.chainMap_retraction_of_functional`: the model `P` is no
longer assumed to vanish in degree `-1` — which it cannot be in general, since a free resolution
of the cohomology in degree `0` of `RΓ` is concentrated in degrees `≤ 0` (see
`DESIGN_inputs_3_4.md`).  The trace functional `T = superTrace ∘ μ(−,−)` is a chain map
`P ⟶ A[0]` exactly because `T ∘ d = 0` (Leibniz rule plus vanishing of supertraces of graded
commutators), so the extra hypothesis here (`φ₀` kills the image of `d⁻¹`) is exactly what the
trace argument supplies.  See `Work.DSEQ0.chainMap_retraction_of_functional` for the special case
`P.X (-1) = 0`.
-/

namespace Work.DSEQ0

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- A complex `P` of `A`-modules, a chain map `c : A[0] ⟶ P`, and a functional `φ₀ : P⁰ ⟶ A`
which kills the image of `d : P⁻¹ ⟶ P⁰` and takes the value `χ ∈ A` on the coaugmentation class
`c(1)`, with `χ ≠ 0` (so `χ` is a unit, since the residue field of `A` has characteristic zero),
produce a chain-level retraction `φ : P ⟶ A[0]` of `c`.  Concretely `φ` is `(χ⁻¹ : A) • φ₀` in
degree `0` and `0` in all other degrees.

This is the form used by area `EQ0`: the trace functional satisfies the two hypotheses. -/
theorem chainMap_retraction_of_differential {A : Type u} [CommRing A] [IsLocalRing A]
    [CharZero (IsLocalRing.ResidueField A)]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (c : Work.DSEQ0.singleZ A ⟶ P) (φ₀ : P.X 0 ⟶ ModuleCat.of A A) (χ : ℕ) (hχ : χ ≠ 0)
    (hφ₀ : φ₀ (c.f 0 (1 : A)) = (χ : A))
    (hker : P.d (-1) 0 ≫ φ₀ = 0) :
    ∃ φ : P ⟶ Work.DSEQ0.singleZ A, c ≫ φ = 𝟙 (Work.DSEQ0.singleZ A) := by
  let u : Aˣ := Work.DSEQ0.unitOfNatCast χ hχ
  have hu : (u : A) = (χ : A) := Work.DSEQ0.coe_unitOfNatCast χ hχ
  let ψ : P.X 0 ⟶ ModuleCat.of A A := ((u⁻¹ : Aˣ) : A) • φ₀
  -- `A[0]` is concentrated in degree `0`, so the only chain condition is at `-1 ⟶ 0`,
  -- where it holds by hypothesis.
  have hψ : ∀ i : ℤ, (ComplexShape.up ℤ).Rel i 0 → P.d i 0 ≫ ψ = 0 := by
    intro i hi
    rw [ComplexShape.up_Rel] at hi
    have hi' : i = -1 := by omega
    subst hi'
    dsimp only [ψ]
    rw [Linear.comp_smul, hker, smul_zero]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of A A)
  let c₀ : ModuleCat.of A A ⟶ P.X 0 := e.inv ≫ c.f 0
  have h2 : c₀ ≫ ψ = 𝟙 (ModuleCat.of A A) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    rw [ConcreteCategory.comp_apply]
    dsimp only [c₀]
    rw [ConcreteCategory.comp_apply]
    rw [ConcreteCategory.id_apply]
    have hei : e.inv (1 : A) = (1 : A) := by
      dsimp only [e]
      simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
        HomologicalComplex.single]
    rw [hei]
    dsimp only [ψ]
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [hφ₀, smul_eq_mul, ← hu]
    exact Units.inv_mul u
  refine ⟨HomologicalComplex.mkHomToSingle ψ hψ, ?_⟩
  apply HomologicalComplex.to_single_hom_ext (j := 0)
  rw [mkHomToSingle_comp_f, HomologicalComplex.id_f]
  have hcf0 : c.f 0 = e.hom ≫ c₀ := (Iso.hom_inv_id_assoc e (c.f 0)).symm
  rw [hcf0, Category.assoc]
  have h3 : c₀ ≫ (ψ ≫ e.inv) = e.inv := by
    rw [← Category.assoc, h2, Category.id_comp]
  rw [h3, Iso.hom_inv_id e]

end Work.DSEQ0
