import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.normalClosure_pow_le
import Submission.Work.ORLyndon.CLDirect.clChi_conj

namespace Work.ORLyndon.CLDirect

/-- `clChi` kills the normal closure of `u^l`. Sketch: generalise to `∀ h : n ∈ M, clChi D l ⟨n, h⟩ = 1`; `Subgroup.normalClosure s = Subgroup.closure (Group.conjugatesOfSet s)` holds by `rfl`, so use `Subgroup.closure_induction`; the generator `c * u^l * c⁻¹` is `(c u c⁻¹)^l`, whose image is `(ofAdd 1)^l = ofAdd (l : ZMod l) = 1` by `clChi_conj` and `ZMod.natCast_self`; the `one`/`mul`/`inv` cases are `map_one`, `map_mul`, `map_inv`. Equivalently: the composite `N ↪ M →* Multiplicative (ZMod l)` is trivial. -/
theorem clChi_eq_one_of_mem {X : Type*} {u : FreeGroup X} (D : Work.ORLyndon.CLDirect.CLData u)
    (l : ℕ) (n : FreeGroup X)
    (hn : n ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X))) :
    Work.ORLyndon.CLDirect.clChi D l ⟨n, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hn⟩ = 1 := by
  -- Generalise to the composite `N ↪ M →* Multiplicative (ZMod l)`, which we show is trivial:
  -- `clChi` is trivial on every conjugate of `u` (`clChi_conj`), hence on `u^l` and on all of `N`.
  have key : ∀ (y : FreeGroup X) (hy : y ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X))),
      Work.ORLyndon.CLDirect.clChi D l ⟨y, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hy⟩ = 1 := by
    intro y hy
    -- `N = closure (conjugatesOfSet {u^l})` by `rfl`; induct on that closure.
    refine (Subgroup.closure_induction
      (k := Group.conjugatesOfSet ({u ^ l} : Set (FreeGroup X)))
      (p := fun g (_ : g ∈ Subgroup.closure (Group.conjugatesOfSet ({u ^ l} : Set (FreeGroup X)))) =>
        ∀ hy' : g ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)),
          Work.ORLyndon.CLDirect.clChi D l ⟨g, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hy'⟩ = 1)
      ?_ ?_ ?_ ?_ hy) hy
    · -- Generator `x = c * u^l * c⁻¹ = (c * u * c⁻¹)^l`.
      intro x hx hy'
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      have ymem : c * u * c⁻¹ ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) :=
        (Subgroup.normalClosure_normal).conj_mem u
          (Subgroup.subset_normalClosure (Set.mem_singleton u)) c
      have heq : (⟨x, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hy'⟩ :
            ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) =
          (⟨c * u * c⁻¹, ymem⟩ : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) ^ l := by
        apply Subtype.ext
        simp only [Subgroup.coe_pow]
        rw [conj_pow]
        exact hc.symm
      rw [heq, map_pow, Work.ORLyndon.CLDirect.clChi_conj D l c ymem]
      rw [← ofAdd_nsmul l (1 : ZMod l), nsmul_eq_mul, mul_one, ZMod.natCast_self]
      rfl
    · -- `1`
      intro hy'
      have : (⟨(1 : FreeGroup X), Work.ORLyndon.CLDirect.normalClosure_pow_le u l hy'⟩ :
          ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) = 1 := Subtype.ext rfl
      rw [this, map_one]
    · -- Product
      intro x y hx hy ihx ihy hy'
      have hxy : (⟨x * y, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hy'⟩ :
            ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) =
          (⟨x, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hx⟩ :
            ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) *
          (⟨y, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hy⟩ :
            ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
      rw [hxy, map_mul, ihx hx, ihy hy, one_mul]
    · -- Inverse
      intro x hx ihx hy'
      have hx' : (⟨x⁻¹, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hy'⟩ :
            ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) =
          (⟨x, Work.ORLyndon.CLDirect.normalClosure_pow_le u l hx⟩ :
            ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X))))⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_inv]
      rw [hx', map_inv, ihx hx, inv_one]
  exact key n hn

end Work.ORLyndon.CLDirect
