import Mathlib
import Submission.Commons.GroupTheory.Hom.card_range_mul_card_ker_add

namespace Commons.LinearAlgebra.LinearMap

/-- The fibre of a linear map over any element of its range is in bijection with its kernel:
translate by a chosen preimage. -/
private lemma fibre_equiv_ker_of_mem_range {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module (ZMod 2) E] [Module (ZMod 2) F] (f : E →ₗ[ZMod 2] F) {y : F}
    (hy : y ∈ LinearMap.range f) :
    Nonempty ({x : E // f x = y} ≃ LinearMap.ker f) := by
  classical
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hy
  let toFun : {x : E // f x = y} → LinearMap.ker f :=
    fun x => ⟨x.1 - a, by rw [LinearMap.mem_ker, map_sub, x.2, ha, sub_self]⟩
  let invFun : LinearMap.ker f → {x : E // f x = y} :=
    fun k => ⟨k.1 + a, by rw [map_add, LinearMap.mem_ker.mp k.2, zero_add, ha]⟩
  have hleft : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    dsimp only [toFun, invFun]
    rw [sub_add_cancel]
  have hright : Function.RightInverse invFun toFun := by
    intro k
    apply Subtype.ext
    dsimp only [toFun, invFun]
    rw [add_sub_cancel_right]
  exact ⟨Equiv.mk toFun invFun hleft hright⟩

/-- Cardinality of a fibre over a point of the range equals the cardinality of the kernel. -/
private lemma natCard_fiber_eq_card_ker {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module (ZMod 2) E] [Module (ZMod 2) F] (f : E →ₗ[ZMod 2] F) {y : F}
    (hy : y ∈ LinearMap.range f) :
    Nat.card {x : E // f x = y} = Nat.card (LinearMap.ker f) :=
  Nat.card_congr (Classical.choice (fibre_equiv_ker_of_mem_range f hy))

/-- The fibre over a point outside the range is empty, hence has cardinality `0`. -/
private lemma natCard_fiber_eq_zero_of_notMem {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module (ZMod 2) E] [Module (ZMod 2) F] (f : E →ₗ[ZMod 2] F) {y : F}
    (hy : y ∉ LinearMap.range f) :
    Nat.card {x : E // f x = y} = 0 := by
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun x => hy (LinearMap.mem_range.mpr ⟨x.1, x.2⟩)⟩

theorem card_preimage_add_mul_card_range {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [Fintype E] [AddCommGroup F] [Module (ZMod 2) F] [Fintype F]
    (f : E →ₗ[ZMod 2] F) (t : F) (T : Finset F) :
    Nat.card {x : E // f x + t ∈ T} * Nat.card ↥(LinearMap.range f)
      = Nat.card {y : F // y ∈ T ∧ y - t ∈ LinearMap.range f} * Nat.card E := by
  classical
  -- Cardinality of the domain as `range × ker`.
  have hE : Nat.card ↥(LinearMap.range f) * Nat.card ↥(LinearMap.ker f) = Nat.card E := by
    have h := Commons.GroupTheory.Hom.card_range_mul_card_ker_add f.toAddMonoidHom
    rw [show (f.toAddMonoidHom.range : AddSubgroup F) = (LinearMap.range f).toAddSubgroup from by
          ext x; rfl,
        show (f.toAddMonoidHom.ker : AddSubgroup E) = (LinearMap.ker f).toAddSubgroup from by
          ext x; rfl] at h
    exact h
  -- Cardinality of the preimage as `B × ker`.
  have hA : Nat.card {x : E // f x + t ∈ T}
      = Nat.card {y : F // y ∈ T ∧ y - t ∈ LinearMap.range f}
        * Nat.card ↥(LinearMap.ker f) := by
    -- Decompose the preimage of `T` under `x ↦ f x + t` into fibres.
    have hsum : Nat.card {x : E // f x + t ∈ T}
        = ∑ b ∈ T, Nat.card {x : E // f x = b - t} := by
      have hb : ∀ b ∈ T, Set.Finite {a : E | f a + t = b} :=
        fun b _ => Set.finite_univ.subset (Set.subset_univ _)
      have h1 := Finset.card_preimage_eq_sum_card_image_eq
        (f := fun x : E => f x + t) (s := T) hb
      rw [show Nat.card ↥((fun x : E => f x + t) ⁻¹' (↑T : Set F))
            = Nat.card {x : E // f x + t ∈ T} from rfl] at h1
      rw [h1]
      apply Finset.sum_congr rfl
      intro b _
      exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by
        constructor
        · intro hx; rw [← hx, add_sub_cancel_right]
        · intro hx; rw [hx, sub_add_cancel]))
    -- Only the `b` with `b - t ∈ range f` contribute.
    have hsum2 : ∑ b ∈ T, Nat.card {x : E // f x = b - t}
        = ∑ b ∈ T.filter (fun b => b - t ∈ LinearMap.range f),
            Nat.card {x : E // f x = b - t} := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro b hbT hbnot
      simp only [Finset.mem_filter, not_and] at hbnot
      exact natCard_fiber_eq_zero_of_notMem f (hbnot hbT)
    -- Each contributing summand is `Nat.card ker`.
    have hconst : ∑ b ∈ T.filter (fun b => b - t ∈ LinearMap.range f),
          Nat.card {x : E // f x = b - t}
        = (T.filter (fun b => b - t ∈ LinearMap.range f)).card
            * Nat.card ↥(LinearMap.ker f) := by
      apply Finset.sum_const_nat
      intro b hb
      exact natCard_fiber_eq_card_ker f (Finset.mem_filter.mp hb).2
    -- The index set is exactly `B`.
    have hBcard : Nat.card {y : F // y ∈ T ∧ y - t ∈ LinearMap.range f}
        = (T.filter (fun b => b - t ∈ LinearMap.range f)).card := by
      have h1 : Nat.card {y : F // y ∈ T ∧ y - t ∈ LinearMap.range f}
          = Nat.card ↥(T.filter (fun b => b - t ∈ LinearMap.range f)) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun y => by simp only [Finset.mem_filter]))
      rw [h1, Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [hsum, hsum2, hconst, hBcard]
  rw [hA, ← hE]
  ring

end Commons.LinearAlgebra.LinearMap
