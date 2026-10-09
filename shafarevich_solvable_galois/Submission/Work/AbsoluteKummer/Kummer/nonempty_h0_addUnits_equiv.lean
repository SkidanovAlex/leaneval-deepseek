import Mathlib
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.AbsoluteKummer.Coefficients
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Kummer

open scoped Classical

noncomputable section

section Helpers

variable {k : Type*} [Field k]

/-- Membership in `H⁰(G_k, k̄ˣ)`, spelled out in terms of the underlying units of `k̄`. -/
theorem mem_h0_addUnits_iff (a : Additive (AlgebraicClosure k)ˣ) :
    a ∈ Work.AbsoluteKummer.H0 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ) ↔
      ∀ σ : Work.AbsoluteKummer.G k,
        Work.AbsoluteKummer.algEquivUnitsMap k σ (Additive.toMul a) = Additive.toMul a := by
  rw [Work.GroupCohomology.mem_invariants]
  constructor
  · intro h σ
    have h' := congrArg Additive.toMul (h σ)
    simpa using h'
  · intro h σ
    show Additive.ofMul
      (Work.AbsoluteKummer.algEquivUnitsMap k σ (Additive.toMul a)) = a
    rw [h σ]
    exact ofMul_toMul a

/-- The base-change map on units `kˣ → k̄ˣ`, `x ↦ x`, viewed as a map of additive groups. -/
def baseUnitsHom : Additive kˣ →+ Additive (AlgebraicClosure k)ˣ where
  toFun a := Additive.ofMul
    (Units.map (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k) (Additive.toMul a))
  map_zero' := by simp
  map_add' a b := by simp

theorem baseUnitsHom_mem (a : Additive kˣ) :
    baseUnitsHom (k := k) a ∈
      Work.AbsoluteKummer.H0 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ) := by
  rw [mem_h0_addUnits_iff]
  intro σ
  exact Work.AbsoluteKummer.algEquivUnitsMap_eq_self_of_mem_range k
    (x := Additive.toMul a) rfl σ

theorem baseUnitsHom_injective : Function.Injective (baseUnitsHom (k := k)) := by
  intro a b h
  have h1 : Units.map (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k)
        (Additive.toMul a) =
      Units.map (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k)
        (Additive.toMul b) := by
    simpa [baseUnitsHom] using congrArg (fun z : Additive (AlgebraicClosure k)ˣ => Additive.toMul z) h
  exact Additive.toMul.injective (Units.map_injective
    (show Function.Injective (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k) from
      (algebraMap k (AlgebraicClosure k)).injective) h1)

/-- Every Galois-fixed unit of `k̄` comes from a unit of `k`. -/
theorem exists_baseUnitsHom_eq [IsGalois k (AlgebraicClosure k)]
    (y : Work.AbsoluteKummer.H0 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ)) :
    ∃ a : Additive kˣ, baseUnitsHom a = y.1 := by
  have hy : ∀ σ : Work.AbsoluteKummer.G k,
      Work.AbsoluteKummer.algEquivUnitsMap k σ (Additive.toMul y.1) = Additive.toMul y.1 :=
    (mem_h0_addUnits_iff (k := k) y.1).mp y.2
  have hfix : ∀ σ : Work.AbsoluteKummer.G k,
      σ (((Additive.toMul y.1 : (AlgebraicClosure k)ˣ) : AlgebraicClosure k)) =
        ((Additive.toMul y.1 : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) := by
    intro σ
    have h' := congrArg (fun u : (AlgebraicClosure k)ˣ => (u : AlgebraicClosure k)) (hy σ)
    simpa [Work.AbsoluteKummer.algEquivUnitsMap_coe] using h'
  obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := k)
    (K := AlgebraicClosure k)
    ((Additive.toMul y.1 : (AlgebraicClosure k)ˣ) : AlgebraicClosure k)).mpr hfix
  have hx0 : x ≠ 0 := by
    intro h0
    have hz : ((Additive.toMul y.1 : (AlgebraicClosure k)ˣ) : AlgebraicClosure k) = 0 := by
      rw [← hx, h0, map_zero]
    exact (Additive.toMul y.1).ne_zero hz
  refine ⟨Additive.ofMul (Units.mk0 x hx0), ?_⟩
  have hmap : Units.map (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k)
        (Units.mk0 x hx0) = Additive.toMul y.1 := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_mk0]
    exact hx
  show Additive.ofMul (Units.map (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k)
    (Additive.toMul (Additive.ofMul (Units.mk0 x hx0)))) = y.1
  rw [toMul_ofMul, hmap, ofMul_toMul]

end Helpers

theorem nonempty_h0_addUnits_equiv {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] : Nonempty (Work.AbsoluteKummer.H0 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ) ≃+ Additive kˣ) := by
  refine ⟨(AddEquiv.ofBijective
    ((baseUnitsHom (k := k)).codRestrict
      (Work.AbsoluteKummer.H0 (Work.AbsoluteKummer.G k) (Additive (AlgebraicClosure k)ˣ))
      (baseUnitsHom_mem (k := k))) ?_).symm⟩
  constructor
  · intro a b h
    exact baseUnitsHom_injective (k := k) (congrArg Subtype.val h)
  · intro y
    obtain ⟨a, ha⟩ := exists_baseUnitsHom_eq (k := k) y
    exact ⟨a, Subtype.ext ha⟩

end

end Work.AbsoluteKummer.Kummer
