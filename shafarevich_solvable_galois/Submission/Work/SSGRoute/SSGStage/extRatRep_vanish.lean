import Mathlib
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.E7cOmega.ratDivSES
import Submission.Work.SSGRoute.ExtOneAux
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The elementary half of local Tate duality for `p`-torsion coefficients

For a group `G`, a prime `p` and a `G`-module `M` killed by `p`:

* `Hom_G(M, ℚ) = 0` (`subsingleton_hom_ratRep`), hence
* `Ext⁰_G(M, ℚ) = Hom_G(M, ℚ) = 0` (`subsingleton_ext_zero_ratRep`), and
* every `Coeff`-linear map `M → ℚ` is zero (`linearMap_ratRep_eq_zero`).

Here `ℚ` carries the trivial `G`-action (`Work.SSGRoute.E7cOmega.ratRep`), and `M` has exponent `p`,
so `p • f m = f (p • m) = 0` while `ℚ` is torsion-free.

These are two of the three vanishing inputs of the local Tate duality step of node `C6`
(`Work.SSGRoute.SSGStage.unramifiedDetector`), i.e. of the statement that the connecting map of
`0 → ℤ → ℚ → ℚ/ℤ → 0` (`Work.SSGRoute.E7cOmega.ratDivSES`) is surjective onto `Ext¹_G(M, ℤ)`:

    `∃ μ : M ⟶ ℚ/ℤ, μ ≠ 0 ∧ φ = (mk₀ μ).comp extClass (zero_add 1)`   for every `φ ≠ 0`.

The third input is `Ext¹_G(M, ℚ) = 0`, which is the image of `Hom_ℤ(M,ℚ) = 0` under the dictionary
`Ext¹_G(M,ℚ) ≅ H¹(G, Hom_ℤ(M,ℚ))` (`Work.SSGRoute.ext_one_iso_divisible_cohomology`); the module
`Hom_ℤ(M,ℚ)` is the internal hom `Work.SSGRoute.homRep M (ratRep G)`, and formalising its vanishing
runs into the `ULift ℤ`-instance mismatch between `(homRep M N).V` and the linear-map type
`M.V →ₗ[Coeff] N.V` (a `Coeff`-module instance is part of the type, so the two are not
definitionally equal).  Everything here is stated at the level of the *honest* linear-map type or
of `Rep`-morphisms, where no transport across that mismatch is needed.
-/

open CategoryTheory

namespace Work.SSGRoute.SSGStage

attribute [local instance 10000] Rep.hV2 Rep.hV1

noncomputable section

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

theorem ratCast_prime_ne_zero : (p : ℚ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact (Fact.out : p.Prime).ne_zero

/-- **A `G`-morphism `M ⟶ ℚ` (trivial `G`-action) with `M` of exponent `p` is zero**: its
underlying linear map kills `p • m = 0`, and `p ≠ 0` in the torsion-free group `ℚ`. -/
theorem hom_ratRep_eq_zero (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) (f : M ⟶ Work.SSGRoute.E7cOmega.ratRep G) : f = 0 := by
  apply Rep.hom_ext
  rw [Rep.zero_hom]
  rw [Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro m
  have hz : (Rep.Hom.hom f).toLinearMap ((p : ℤ) • m) = 0 := by
    have h0 : (p : ℤ) • m = 0 := by simpa using hM m
    rw [h0, map_zero]
  have h2 := map_zsmul (Rep.Hom.hom f).toLinearMap (p : ℤ) m
  rw [h2] at hz
  exact (mul_eq_zero.mp (by rw [zsmul_eq_mul] at hz; exact hz)).resolve_left
    (by rw [Int.cast_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- **Every `Coeff`-linear map `M → ℚ` is zero** when `M` has exponent `p`, by the same
`p • f m = f (p • m) = 0` argument. -/
theorem linearMap_ratRep_eq_zero (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0)
    (f : M.V →ₗ[SSGRoute.PTExt.Coeff] (Work.SSGRoute.E7cOmega.ratRep G).V) : f = 0 := by
  ext m
  have hz : f ((p : ℤ) • m) = 0 := by
    have h0 : (p : ℤ) • m = 0 := by simpa using hM m
    rw [h0, map_zero]
  have h2 := map_zsmul f (p : ℤ) m
  rw [h2] at hz
  exact (mul_eq_zero.mp (by rw [zsmul_eq_mul] at hz; exact hz)).resolve_left
    (by rw [Int.cast_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- **`Hom_G(M, ℚ) = 0`** for `M` of exponent `p`. -/
theorem subsingleton_hom_ratRep (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) : Subsingleton (M ⟶ Work.SSGRoute.E7cOmega.ratRep G) :=
  ⟨fun f g => by rw [hom_ratRep_eq_zero M hM f, hom_ratRep_eq_zero M hM g]⟩

/-- **`Ext⁰_G(M, ℚ) = Hom_G(M, ℚ) = 0`** for `M` of exponent `p`. -/
theorem subsingleton_ext_zero_ratRep (M : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hM : ∀ m : M, p • m = 0) :
    Subsingleton (Abelian.Ext M (Work.SSGRoute.E7cOmega.ratRep G) 0) := by
  refine ⟨fun a b => ?_⟩
  apply (Abelian.Ext.addEquiv₀ (X := M) (Y := Work.SSGRoute.E7cOmega.ratRep G)).injective
  exact (subsingleton_hom_ratRep M hM).elim _ _

/-- `ℚ` is divisible: the third input of the duality is fed by
`Work.SSGRoute.ext_one_iso_divisible_cohomology`. -/
theorem rat_divisible (n : ℕ) (hn : 0 < n) (y : ℚ) : ∃ x : ℚ, n • x = y := by
  refine ⟨y / n, ?_⟩
  rw [nsmul_eq_mul]
  field_simp

end

end Work.SSGRoute.SSGStage
