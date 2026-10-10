import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Submission.Work.Tate.DimensionShiftH
import Submission.Work.Tate.Equivs
import Submission.Work.Tate.Hm1ToCoinv_injective
import Submission.Work.Tate.coind_augmentation_eq_ker_norm
import Submission.Work.Tate.coind_norm_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.tate

open scoped BigOperators
open Work.Tate

/-! ## Auxiliary lemmas about the coinduced module

These are small structural facts about the "diagonal" inclusion `coindUnit` and the
postcomposition map `coindMap` that are used to prove the naturality of the dimension-shifting
isomorphism. -/

/-- The diagonal inclusion `A → Coind(A)`, `a ↦ (x ↦ x • a)`, is injective. -/
theorem coindUnit_injective (G : Type*) [Group G] (A : Type*) [AddCommGroup A]
    [DistribMulAction G A] : Function.Injective (Work.Tate.coindUnit G A) := by
  intro a b h
  have := congrFun h 1
  simpa using this

/-- `coindMap` sends the diagonal copy of `A` to the diagonal copy of `B`. -/
theorem coindMap_coindUnit (G : Type*) [Group G] [Fintype G] (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] [DistribMulAction G A] [DistribMulAction G B]
    (f : A →+ B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) (a : A) :
    Work.Tate.coindMap f (Work.Tate.coindUnit G A a) = Work.Tate.coindUnit G B (f a) := by
  funext x
  rw [Work.Tate.coindMap_apply, Work.Tate.coindUnit_apply, Work.Tate.coindUnit_apply, hf]

/-- The norm of a diagonal element is again diagonal. -/
theorem norm_coindUnit (G : Type*) [Group G] [Fintype G] (B : Type*) [AddCommGroup B]
    [DistribMulAction G B] (d : B) :
    Work.Tate.norm G (G → B) (Work.Tate.coindUnit G B d)
      = Work.Tate.coindUnit G B (Work.Tate.norm G B d) := by
  funext z
  rw [Work.Tate.coindUnit_apply, Work.Tate.norm_apply, Finset.sum_apply]
  simp only [Work.Tate.coind_smul_eq, Work.Tate.coindUnit_apply, Work.Tate.norm_apply,
    Work.Tate.smul_sum_univ, mul_smul]

/-! ## Naturality of the connecting map on representatives -/

/-- Naturality of `SES.deltaLiftFun` for the shift sequence `0 → A → Coind(A) → A^* → 0`:
on a class `c ∈ ker N_{A^*}`, transporting along `φ : A → B` and a compatible map
`ψ : A^* → B^*` commutes with the explicit connecting construction. -/
theorem deltaLiftFun_coindShift_natural (p : ℕ) (G : Type*) [Group G] [Fintype G]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
      [SMulCommClass G (ZMod p) A]
    (B : Type*) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
      [SMulCommClass G (ZMod p) B]
    (φ : A →ₗ[ZMod p] B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a)
    (ψ : Work.Tate.coindShift G A →+ Work.Tate.coindShift G B)
    (hψproj : ∀ x : G → A,
      ψ (Work.Tate.coindProj G A x)
        = Work.Tate.coindProj G B (Work.Tate.coindMap (φ.toAddMonoidHom) x))
    (hψ : ∀ (γ : G) (x : Work.Tate.coindShift G A), ψ (γ • x) = γ • ψ x)
    (c : (Work.Tate.norm G (Work.Tate.coindShift G A)).ker) :
    Work.Tate.H0Map G A B (φ.toAddMonoidHom) hφ
        ((Work.Tate.coindSES G A).deltaLiftFun c)
      = (Work.Tate.coindSES G B).deltaLiftFun
          (Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c) := by
  -- Replace the equivariance hypothesis by its `toAddMonoidHom` form.
  have hφ' : ∀ (γ : G) (a : A), (φ.toAddMonoidHom) (γ • a) = γ • (φ.toAddMonoidHom) a :=
    fun γ a => hφ γ a
  rw [show Work.Tate.H0Map G A B (φ.toAddMonoidHom) hφ
        = Work.Tate.H0Map G A B (φ.toAddMonoidHom) hφ' from rfl]
  -- Notation for the chosen sections / preimages.
  have hxA : Work.Tate.coindProj G A ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
      = (c : Work.Tate.coindShift G A) :=
    (Work.Tate.coindSES G A).sec_spec (c : Work.Tate.coindShift G A)
  have hxB : Work.Tate.coindProj G B
        ((Work.Tate.coindSES G B).sec
          (((Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
            : (Work.Tate.norm G (Work.Tate.coindShift G B)).ker) : Work.Tate.coindShift G B)))
      = ((Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
          : Work.Tate.coindShift G B)) :=
    (Work.Tate.coindSES G B).sec_spec _
  have hmap : ((Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
        : Work.Tate.coindShift G B)) = ψ (c : Work.Tate.coindShift G A) :=
    Work.Tate.mapKer_apply ψ hψ c
  have hproj' : Work.Tate.coindProj G B
        (Work.Tate.coindMap (φ.toAddMonoidHom)
          ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A)))
      = ψ (c : Work.Tate.coindShift G A) := by
    rw [← hψproj ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A)), hxA]
  have hy' : Work.Tate.coindProj G B
        ((Work.Tate.coindSES G B).sec
          (((Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
            : (Work.Tate.norm G (Work.Tate.coindShift G B)).ker) : Work.Tate.coindShift G B)))
      = ψ (c : Work.Tate.coindShift G A) := by
    rw [hxB, hmap]
  -- The two chosen lifts of `ψ c` differ by a diagonal element.
  have hmem : Work.Tate.coindMap (φ.toAddMonoidHom)
        ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
      - (Work.Tate.coindSES G B).sec
          (((Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
            : (Work.Tate.norm G (Work.Tate.coindShift G B)).ker) : Work.Tate.coindShift G B))
      ∈ Work.Tate.coindDiag G B := by
    rw [← Work.Tate.coindProj_eq_zero_iff, map_sub, hproj', hy', sub_self]
  obtain ⟨d, hd⟩ := (Work.Tate.mem_coindDiag_iff G B).mp hmem
  have hd' : Work.Tate.coindMap (φ.toAddMonoidHom)
        ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
      - (Work.Tate.coindSES G B).sec
          (((Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
            : (Work.Tate.norm G (Work.Tate.coindShift G B)).ker) : Work.Tate.coindShift G B))
      = Work.Tate.coindUnit G B d := hd
  have h_eq : Work.Tate.coindMap (φ.toAddMonoidHom)
        ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
      = (Work.Tate.coindSES G B).sec
          (((Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
            : (Work.Tate.norm G (Work.Tate.coindShift G B)).ker) : Work.Tate.coindShift G B))
        + Work.Tate.coindUnit G B d := by
    rw [← hd']; abel
  -- Norms of the lifts.
  have hBA : Work.Tate.norm G (G → A) ((Work.Tate.coindSES G A).sec (c : Work.Tate.coindShift G A))
      = Work.Tate.coindUnit G A ((Work.Tate.coindSES G A).preimage c) :=
    ((Work.Tate.coindSES G A).f_preimage c).symm
  have hBB : Work.Tate.norm G (G → B)
        ((Work.Tate.coindSES G B).sec
          (((Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c
            : (Work.Tate.norm G (Work.Tate.coindShift G B)).ker) : Work.Tate.coindShift G B)))
      = Work.Tate.coindUnit G B
          ((Work.Tate.coindSES G B).preimage
            (Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c)) :=
    ((Work.Tate.coindSES G B).f_preimage
      (Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c)).symm
  have hnorm : Work.Tate.coindUnit G B
        ((φ.toAddMonoidHom) ((Work.Tate.coindSES G A).preimage c))
      = Work.Tate.coindUnit G B
          ((Work.Tate.coindSES G B).preimage
            (Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c))
        + Work.Tate.coindUnit G B (Work.Tate.norm G B d) := by
    rw [← coindMap_coindUnit G A B (φ.toAddMonoidHom) hφ'
        ((Work.Tate.coindSES G A).preimage c)]
    rw [← hBA]
    rw [← Work.Tate.norm_map (Work.Tate.coindMap (φ.toAddMonoidHom))
        (Work.Tate.coindMap_equiv (φ.toAddMonoidHom) hφ')]
    rw [h_eq]
    rw [map_add]
    rw [hBB]
    rw [norm_coindUnit]
  -- Hence the two preimages agree modulo the norm.
  have hkey : (φ.toAddMonoidHom) ((Work.Tate.coindSES G A).preimage c)
      = (Work.Tate.coindSES G B).preimage
          (Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c)
        + Work.Tate.norm G B d := by
    apply coindUnit_injective G B
    rw [map_add]
    exact hnorm
  rw [Work.Tate.deltaLiftFun_apply (Work.Tate.coindSES G A) c,
      Work.Tate.deltaLiftFun_apply (Work.Tate.coindSES G B)
        (Work.Tate.mapKer G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ c),
      Work.Tate.H0Map_H0π]
  refine (Work.Tate.H0π_eq_iff _ _).mpr ?_
  refine ⟨d, ?_⟩
  apply Subtype.ext
  rw [AddSubgroup.coe_sub, Work.Tate.mapFixed_apply, Work.Tate.normToFixed_apply]
  rw [hkey]; abel

/-! ## Naturality of dimension shifting with coinduced coefficients -/

theorem dimensionShiftCoind_natural (p : ℕ) (G : Type*) [Group G] [Fintype G]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
      [SMulCommClass G (ZMod p) A]
    (B : Type*) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
      [SMulCommClass G (ZMod p) B]
    (φ : A →ₗ[ZMod p] B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a)
    (ψ : Work.Tate.coindShift G A →+ Work.Tate.coindShift G B)
    (hψproj : ∀ x : G → A,
      ψ (Work.Tate.coindProj G A x) = Work.Tate.coindProj G B (Work.Tate.coindMap (φ.toAddMonoidHom) x))
    (hψ : ∀ (γ : G) (x : Work.Tate.coindShift G A), ψ (γ • x) = γ • ψ x) :
    (Work.Tate.H0Map G A B (φ.toAddMonoidHom) hφ).comp
        (Work.Tate.dimensionShiftCoind G A).toAddMonoidHom
      = (Work.Tate.dimensionShiftCoind G B).toAddMonoidHom.comp
          (Work.Tate.Hm1Map G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ) := by
  have hφ' : ∀ (γ : G) (a : A), (φ.toAddMonoidHom) (γ • a) = γ • (φ.toAddMonoidHom) a :=
    fun γ a => hφ γ a
  rw [show (Work.Tate.H0Map G A B (φ.toAddMonoidHom) hφ)
        = Work.Tate.H0Map G A B (φ.toAddMonoidHom) hφ' from rfl]
  apply AddMonoidHom.ext
  intro x
  induction x using Work.Tate.Hm1_induction_on with
  | h c =>
    show Work.Tate.H0Map G A B (φ.toAddMonoidHom) hφ'
          ((Work.Tate.dimensionShiftCoind G A) (Work.Tate.Hm1π G (Work.Tate.coindShift G A) c))
        = (Work.Tate.dimensionShiftCoind G B)
          ((Work.Tate.Hm1Map G (Work.Tate.coindShift G A) (Work.Tate.coindShift G B) ψ hψ)
            (Work.Tate.Hm1π G (Work.Tate.coindShift G A) c))
    rw [Work.Tate.dimensionShiftCoind_apply, Work.Tate.dimensionShiftCoind_apply,
      Work.Tate.SES.delta_Hm1π, Work.Tate.Hm1Map_Hm1π, Work.Tate.SES.delta_Hm1π]
    exact deltaLiftFun_coindShift_natural p G A B φ hφ ψ hψproj hψ c

end Work.CohomologicalShrinking.tate
