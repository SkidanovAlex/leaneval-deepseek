import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.centralizer_fitting_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A solvable group with cyclic Fitting subgroup has abelian quotient by it

If `B` is a finite solvable group whose Fitting subgroup `F(B)` is cyclic, then `B/F(B)` is
abelian, i.e. `⁅B, B⁆ ≤ F(B)`.

The proof is the classical one: in a solvable group the Fitting subgroup is self-centralizing
(`Work.Fitting.centralizer_fitting_le`), so `C_B(F(B)) ≤ F(B)`; hence `B/C_B(F(B))` embeds into
`MulAut F(B)`.  When `F(B)` is cyclic, `MulAut F(B)` is commutative (it is the unit group of a
`ZMod`, through `IsCyclic.mulAutMulEquiv`), so `B/C_B(F(B))` is commutative.  Concretely, for
`a b : B` the conjugation automorphism of `F(B)` attached to `⁅a, b⁆` is the commutator of the
automorphisms attached to `a` and `b`, hence trivial, so `⁅a, b⁆` centralizes `F(B)` and therefore
lies in `F(B)`.

The statement is phrased with `B` a subgroup of an ambient group `G` (the normalizer of a
strongly embedded subgroup in the Bender–Suzuki theorem) and with `F(B)` pushed into `G` along
`B.subtype`.
-/

noncomputable section

open Classical
open scoped commutatorElement

set_option linter.style.haveILetI false

namespace Work.Fitting

/-- **The automorphism group of a cyclic group is commutative.**  Via
`IsCyclic.mulAutMulEquiv` it is isomorphic to `(ZMod (Nat.card A))ˣ`. -/
theorem isMulCommutative_mulAut_of_isCyclic {A : Type*} [Group A] [IsCyclic A] :
    IsMulCommutative (MulAut A) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  have h := mul_comm' (IsCyclic.mulAutMulEquiv A a) (IsCyclic.mulAutMulEquiv A b)
  exact (IsCyclic.mulAutMulEquiv A).injective (by simpa using h)

/-- In a finite solvable group `B` with cyclic Fitting subgroup, the derived subgroup is contained
in the Fitting subgroup. -/
theorem commutator_le_fitting_of_isCyclic {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hsol : Group.IsSolvable ↥B)
    (hcyc : IsCyclic ↥((Work.Fitting.fitting ↥B).map B.subtype)) :
    ⁅B,B⁆ ≤ (Work.Fitting.fitting ↥B).map B.subtype := by
  haveI : Finite ↥B := inferInstance
  haveI : Group.IsSolvable ↥B := hsol
  set F : Subgroup ↥B := Work.Fitting.fitting ↥B with hF
  haveI : F.Normal := by rw [hF]; infer_instance
  -- `F` is cyclic: it is carried to `F.map B.subtype` by an isomorphism.
  haveI : IsCyclic ↥F := by
    rw [hF]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective (Work.Fitting.fitting ↥B) B.subtype
      (Subgroup.subtype_injective B))).mpr hcyc
  haveI : IsMulCommutative (MulAut ↥F) := isMulCommutative_mulAut_of_isCyclic
  -- The kernel of the conjugation action on `F` is contained in the centralizer of `F`.
  have hker_le : (MulAut.conjNormal (H := F)).ker ≤ Subgroup.centralizer (F : Set ↥B) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : (MulAut.conjNormal (H := F) x) ⟨y, hy⟩ = ⟨y, hy⟩ := by
      have := congrArg (fun f : MulAut ↥F => f ⟨y, hy⟩) hx
      simpa using this
    have h2 : x * y * x⁻¹ = y := by
      have := congrArg Subtype.val h1
      simpa using this
    have h3 : x * y = y * x := by
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h2]
    exact h3.symm
  -- Every commutator of `B` acts trivially on `F`, hence lies in `C_B(F) ≤ F`.
  have hmain : ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ ≤ F := by
    refine Subgroup.commutator_le.mpr ?_
    intro a _ b _
    have hmem : ⁅a, b⁆ ∈ (MulAut.conjNormal (H := F)).ker := by
      rw [MonoidHom.mem_ker]
      simp only [commutatorElement_def, map_mul, map_inv]
      rw [mul_comm' (MulAut.conjNormal (H := F) a) (MulAut.conjNormal (H := F) b)]
      group
    exact Work.Fitting.centralizer_fitting_le ↥B (hker_le hmem)
  -- Push the inequality forward along `B.subtype`.
  have hmap := Subgroup.map_mono (f := B.subtype) hmain
  rw [hF] at hmap
  have hL : Subgroup.map B.subtype ⁅(⊤ : Subgroup ↥B), (⊤ : Subgroup ↥B)⁆ = ⁅B, B⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [hL] at hmap
  exact hmap

end Work.Fitting
