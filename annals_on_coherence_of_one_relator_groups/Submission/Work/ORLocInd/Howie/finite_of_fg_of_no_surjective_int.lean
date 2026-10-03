/-
# A finitely generated abelian group with no surjection onto `ℤ` is finite

A finitely generated commutative group `A` is, by the structure theorem for finitely generated
abelian groups, a product `(j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ e i)))`
with `j`, `ι` finite.  If the index set `j` of the free factor were nonempty, projecting onto the
corresponding coordinate would give a surjective homomorphism `A →* Multiplicative ℤ`.  Hence `j`
is empty, `A` is a finite product of finite cyclic groups, and so `A` is finite.
-/
import Mathlib

set_option linter.style.haveILetI false

namespace Work.ORLocInd.Howie

universe u

theorem finite_of_fg_of_no_surjective_int {A : Type u} [CommGroup A] (hfg : Group.FG A)
    (h : ∀ f : A →* Multiplicative ℤ, ¬ Function.Surjective f) : Finite A := by
  classical
  -- Structure theorem for finitely generated abelian groups: `A` is the product of a finite power
  -- of `ℤ` and of a finite product of finite cyclic groups.
  obtain ⟨ι, j, hι, hj, p, hp, e, ⟨φ⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod A (hG := hfg)
  letI : Fintype ι := hι
  letI : Fintype j := hj
  haveI hν : ∀ i, NeZero (p i ^ e i) := fun i => ⟨(pow_pos (hp i).pos (e i)).ne'⟩
  -- A nonempty index set `j` would produce a surjection `A →* Multiplicative ℤ`.
  have hjempty : IsEmpty j := by
    by_contra hne
    rw [not_isEmpty_iff] at hne
    obtain ⟨j0⟩ := hne
    let proj : ((j → Multiplicative ℤ) × ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) →*
        Multiplicative ℤ :=
      { toFun := fun x => x.1 j0
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hproj : Function.Surjective proj := by
      intro y
      refine ⟨(Function.update 1 j0 y, 1), ?_⟩
      show Function.update (1 : j → Multiplicative ℤ) j0 y j0 = y
      rw [Function.update_self]
    exact h (proj.comp (φ : A →* _)) (by
      simpa [MonoidHom.coe_comp, Function.comp_def] using hproj.comp φ.surjective)
  -- So the free factor is trivial and `A` is a finite product of finite cyclic groups.
  haveI : Subsingleton (j → Multiplicative ℤ) :=
    ⟨fun f g => funext fun x => (isEmpty_iff.mp hjempty x).elim⟩
  haveI : Finite (j → Multiplicative ℤ) := Finite.of_subsingleton
  haveI : Finite ((i : ι) → Multiplicative (ZMod (p i ^ e i))) := Finite.of_fintype _
  haveI : Finite ((j → Multiplicative ℤ) ×
      ((i : ι) → Multiplicative (ZMod (p i ^ e i)))) := inferInstance
  exact Finite.of_injective (φ : A → _) φ.injective

end Work.ORLocInd.Howie
