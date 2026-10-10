import Mathlib.RingTheory.Henselian
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Galois

/-- Group-theoretic core of the norm-index argument.

For group homomorphisms `φ : H →* G` and `ψ : K →* H`, if `φ(ψ K)` has finite index in `G`
(equivalently the image `ψ K` pushed forward by `φ`), `φ.range` has finite index in `G`, and the
index of `φ(ψ K)` equals `[H : ψ K] · [G : φ H]`, then `ker φ ≤ range ψ`.

Concretely, `Subgroup.index_map` gives
`[G : φ(ψ K)] = [H : ψ K · ker φ] · [G : φ H]`; comparing with the hypothesis and cancelling
`[G : φ H]` yields `[H : ψ K · ker φ] = [H : ψ K]`, which forces `ψ K · ker φ = ψ K`, i.e.
`ker φ ≤ ψ K`. -/
theorem ker_le_range_of_index_map_eq_mul
    {G H K : Type*} [Group G] [Group H] [Group K]
    (φ : H →* G) (ψ : K →* H)
    (hfin : ((ψ.range).map φ).FiniteIndex)
    (hφfin : φ.range.FiniteIndex)
    (h : ((ψ.range).map φ).index = ψ.range.index * φ.range.index) :
    φ.ker ≤ ψ.range := by
  have hφ : φ.range.index ≠ 0 := hφfin.index_ne_zero
  have hψ : ψ.range.index ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at h
    exact hfin.index_ne_zero h
  have hψfi : ψ.range.FiniteIndex := Subgroup.finiteIndex_iff.mpr hψ
  have hm := Subgroup.index_map (H := ψ.range) φ
  rw [hm] at h
  have hcancel : (ψ.range ⊔ φ.ker).index = ψ.range.index :=
    mul_right_cancel₀ hφ h
  have hle : ψ.range ≤ ψ.range ⊔ φ.ker := le_sup_left
  have heq : ψ.range ⊔ φ.ker = ψ.range := by
    by_contra hne
    have hlt : ψ.range < ψ.range ⊔ φ.ker := lt_of_le_of_ne hle (Ne.symm hne)
    have hltidx : (ψ.range ⊔ φ.ker).index < ψ.range.index :=
      @Subgroup.index_strictAnti _ _ ψ.range (ψ.range ⊔ φ.ker) hlt hψfi
    rw [hcancel] at hltidx
    exact lt_irrefl _ hltidx
  rw [← heq]
  exact le_sup_right

/-- For a tower of finite-dimensional field extensions `F ⊆ M ⊆ E`, if both norm maps
`N_{E/F}` and `N_{M/F}` have finite-index image on units, and the index of `N_{E/F}(Eˣ)` in `Fˣ`
equals the product of the indices of `N_{E/M}(Eˣ)` in `Mˣ` and of `N_{M/F}(Mˣ)` in `Fˣ`, then
`ker N_{M/F} ≤ range N_{E/M}`.

This is the group-theoretic content behind the multiplicativity of unit-index classes in the
proof of the Neukirch–Uchida theorem: the transitivity of the norm
`N_{E/F} = N_{M/F} ∘ N_{E/M}` together with the index identity forces the kernel of `N_{M/F}`
into the image of `N_{E/M}`. -/
theorem ker_le_range_of_natCard_quotient_units_range_norm_eq_mul
    {F M E : Type*} [Field F] [Field M] [Field E]
    [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E]
    [FiniteDimensional F M] [FiniteDimensional M E]
    (hfin1 : (MonoidHom.range (Units.map (Algebra.norm F : E →* F))).FiniteIndex)
    (hfin2 : (MonoidHom.range (Units.map (Algebra.norm F : M →* F))).FiniteIndex)
    (h : Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : E →* F))) =
      Nat.card (Mˣ ⧸ MonoidHom.range (Units.map (Algebra.norm M : E →* M))) *
        Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : M →* F)))) :
    MonoidHom.ker (Units.map (Algebra.norm F : M →* F)) ≤
      MonoidHom.range (Units.map (Algebra.norm M : E →* M)) := by
  let φ : Mˣ →* Fˣ := Units.map (Algebra.norm F : M →* F)
  let ψ : Eˣ →* Mˣ := Units.map (Algebra.norm M : E →* M)
  let χ : Eˣ →* Fˣ := Units.map (Algebra.norm F : E →* F)
  have hcomp : χ = φ.comp ψ := by
    ext u
    simp only [χ, φ, ψ, MonoidHom.comp_apply, Units.coe_map]
    exact (Algebra.norm_norm).symm
  have hrange : χ.range = (ψ.range).map φ := by
    rw [hcomp, MonoidHom.range_comp]
  have hfin : ((ψ.range).map φ).FiniteIndex := by
    rw [← hrange]; exact hfin1
  have hφfin : φ.range.FiniteIndex := hfin2
  have hidx : ((ψ.range).map φ).index = ψ.range.index * φ.range.index := by
    rw [← hrange]
    exact h
  exact ker_le_range_of_index_map_eq_mul φ ψ hfin hφfin hidx

end Commons.FieldTheory.Galois