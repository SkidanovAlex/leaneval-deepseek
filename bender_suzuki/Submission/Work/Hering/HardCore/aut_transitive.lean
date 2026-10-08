import Mathlib
import Submission.Work.Hering.Step5.mulAut_eight_order21

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Aut(V)` is transitive on the non-identity elements of a group of exponent two and order `8`

Let `V` be a finite group of order `8` in which every element is an involution
(`x * x = 1`).  Such a group is elementary abelian of rank `3`, i.e. isomorphic to
`(ℤ/2)³`, and `Aut(V) ≅ GL(3,2)` acts transitively on the seven non-identity elements.

The proof reduces to the concrete model `Multiplicative (Fin 3 → ZMod 2) = (ℤ/2)³` via the
classification `Work.Hering.Step5.iso_fin3`, and in the concrete model the automorphism is an
explicit transvection: if `v ≠ w` are nonzero vectors of an `𝔽₂`-vector space, choose a linear
form `φ` with `φ v = φ w = 1` (`LinearMap.exists_extend_of_notMem`); then
`x ↦ x + φ x • (w - v)` is a linear involution (`LinearEquiv.transvection`) sending `v` to `w`.
-/

set_option autoImplicit false

namespace Work.Hering.HardCore

/-- In `𝔽₂` the only elements are `0` and `1`. -/
lemma zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- **A linear automorphism moving one nonzero vector to another.**  If `v ≠ w` are nonzero
vectors of an `𝔽₂`-vector space, there is a linear equivalence sending `v` to `w`. -/
theorem exists_linearEquiv_apply_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : w ≠ v) :
    ∃ e : V ≃ₗ[ZMod 2] V, e v = w := by
  -- `w` is not a scalar multiple of `v`
  have hws : w ∉ Submodule.span (ZMod 2) ({v} : Set V) := by
    intro hmem
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    rcases zmod_two_eq_zero_or_one a with rfl | rfl
    · rw [zero_smul] at ha; exact hw ha.symm
    · rw [one_smul] at ha; exact hvw ha.symm
  -- a linear form on `𝔽₂ ∙ v` with value `1` at `v`, extended with value `1` at `w`
  let f : (Submodule.span (ZMod 2) ({v} : Set V)) →ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.coord (ZMod 2) V v hv
  obtain ⟨φ, hφ, hφw⟩ := LinearMap.exists_extend_of_notMem f hws (1 : ZMod 2)
  have hφv : φ v = 1 := by
    have h1 := DFunLike.congr_fun hφ ⟨v, Submodule.mem_span_singleton_self v⟩
    simpa [f, LinearEquiv.coord_self] using h1
  have huv : φ (w - v) = 0 := by rw [map_sub, hφv, hφw, sub_self]
  refine ⟨LinearEquiv.transvection huv, ?_⟩
  rw [LinearEquiv.transvection.apply huv, hφv, one_smul]
  abel

/-- **`(ℤ/2)³` is transitive.**  Any two non-identity elements of the elementary abelian group
`(ℤ/2)³ = Multiplicative (Fin 3 → ZMod 2)` are related by an automorphism, by transport of the
transvection of `exists_linearEquiv_apply_eq` across `Multiplicative`/`Additive`. -/
theorem mulAut_transitive_fin3 (v w : Multiplicative (Fin 3 → ZMod 2))
    (hv : v ≠ 1) (hw : w ≠ 1) :
    ∃ φ : MulAut (Multiplicative (Fin 3 → ZMod 2)), φ v = w := by
  by_cases h : v = w
  · exact ⟨1, by rw [h]; rfl⟩
  · have hv' : Multiplicative.toAdd v ≠ 0 := fun h0 =>
      hv (by simpa using congrArg Multiplicative.ofAdd h0)
    have hw' : Multiplicative.toAdd w ≠ 0 := fun h0 =>
      hw (by simpa using congrArg Multiplicative.ofAdd h0)
    have hvw' : Multiplicative.toAdd w ≠ Multiplicative.toAdd v := fun hh =>
      h (Multiplicative.toAdd.injective hh.symm)
    obtain ⟨e, he⟩ := exists_linearEquiv_apply_eq hv' hw' hvw'
    refine ⟨{ toFun := fun x => Multiplicative.ofAdd (e (Multiplicative.toAdd x))
              invFun := fun y => Multiplicative.ofAdd (e.symm (Multiplicative.toAdd y))
              left_inv := by intro x; simp
              right_inv := by intro y; simp
              map_mul' := by intro x y; simp [toAdd_mul, ofAdd_add, map_add] }, ?_⟩
    show Multiplicative.ofAdd (e (Multiplicative.toAdd v)) = w
    rw [he, ofAdd_toAdd]

/-- **Bender–Suzuki, elementary abelian case.**  Let `V` be a finite group of order `8` all of
whose elements are involutions.  Then `Aut(V)` is transitive on the seven non-identity
elements. -/
theorem aut_transitive {V : Type*} [Group V] [Finite V] (hcard : Nat.card V = 8)
    (hexp : ∀ x : V, x * x = 1) :
    ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ φ : MulAut V, φ v = w := by
  intro v w hv hw
  obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard hexp
  have hev : e v ≠ 1 := fun h1 => hv (by
    simpa using congrArg e.symm h1)
  have hew : e w ≠ 1 := fun h1 => hw (by
    simpa using congrArg e.symm h1)
  obtain ⟨φ', hφ'⟩ := mulAut_transitive_fin3 (e v) (e w) hev hew
  refine ⟨(e.trans φ').trans e.symm, ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hφ', MulEquiv.symm_apply_apply]

end Work.Hering.HardCore
