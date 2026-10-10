import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Submission.Work.SSGRoute.PT.ClassFormation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Discreteness of the `G`-action on the coinduced module `Coind^G_U M`

For a topological group `G`, an open finite-index subgroup `U ≤ G` and a `U`-module `M`
whose action is discrete (every `m : M` has an open stabiliser in `U`), the coinduced module

  `Coind^G_U M = {f : G → M // ∀ g u, f (g * u) = u⁻¹ • f g}`

with the `G`-action `(g • f) x = f (g⁻¹ * x)` is again a discrete `G`-module.

The point is that `f` is determined by its values on a finite set of left-coset representatives
`S ⊆ G` (`G = ⋃_{s ∈ S} sU`): those values `f s` have open stabilisers `K_s ⊆ U`, and the open
neighbourhood

  `V = ⋂_{s ∈ S} {g | g⁻¹ * s ∈ s • W},    W = ⋂_{s ∈ S} ↑K_s ⊆ G`

of `1` is contained in the stabiliser of `f`.  Concretely, if `h ∈ V` and `x = s * u` with
`s ∈ S`, `u : U`, then `h⁻¹ * s = s * w` with `w ∈ W`, hence `h⁻¹ * x = s * (w * u)` and the
`U`-equivariance of `f`, together with `w • f s = f s`, gives `f (h⁻¹ * x) = f x`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical

namespace Work.SSGRoute.PT

theorem isDiscreteModule_coind {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (hM : Work.AbsoluteKummer.IsDiscreteModule U M) :
    Work.AbsoluteKummer.IsDiscreteModule G (Work.SSGRoute.PT.Coind G U M) := by
  classical
  intro f
  letI : Fintype (G ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  -- a finite set of left-coset representatives: `G = ⋃_{s ∈ S} s U`
  let S : Finset G := Finset.univ.image (fun q : G ⧸ U => Quotient.out q)
  have hcov : ∀ x : G, ∃ s ∈ S, ∃ u : U, x = s * (u : G) := by
    intro x
    refine ⟨Quotient.out (⟦x⟧ : G ⧸ U), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟦x⟧, Finset.mem_univ _, rfl⟩
    · have h : (QuotientGroup.leftRel U) (Quotient.out (⟦x⟧ : G ⧸ U)) x := by
        apply Quotient.exact
        exact Quotient.out_eq ⟦x⟧
      rw [QuotientGroup.leftRel_apply] at h
      exact ⟨⟨(Quotient.out (⟦x⟧ : G ⧸ U))⁻¹ * x, h⟩, by group⟩
  -- `W = ⋂_{s ∈ S} K_s`, the stabilisers of the values of `f` on `S`, viewed in `G`
  let W : Set G := ⋂ s ∈ S, ((↑) '' (MulAction.stabilizer U (f s) : Set U))
  have hWopen : IsOpen W := by
    refine isOpen_biInter_finset (fun s _ => ?_)
    exact hU.isOpenMap_subtype_val _ (hM (f s))
  have h1W : (1 : G) ∈ W := by
    refine Set.mem_iInter₂.mpr (fun s _ => ?_)
    exact ⟨1, MulAction.mem_stabilizer_iff.mpr (one_smul _ _), rfl⟩
  -- the open neighbourhood `V` of `1` contained in the stabiliser of `f`
  let V : Set G := ⋂ s ∈ S, {g : G | g⁻¹ * s ∈ (fun x : G => s * x) '' W}
  have hVopen : IsOpen V := by
    refine isOpen_biInter_finset (fun s _ => ?_)
    exact IsOpen.preimage (by fun_prop) (isOpenMap_mul_left s W hWopen)
  have h1V : (1 : G) ∈ V := by
    refine Set.mem_iInter₂.mpr (fun s _ => ?_)
    refine ⟨1, h1W, ?_⟩
    simp
  have hsub : V ⊆ (MulAction.stabilizer G f : Set G) := by
    intro h hh
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    refine Subtype.ext (funext fun x => ?_)
    obtain ⟨s, hsS, u₀, rfl⟩ := hcov x
    rw [Coind.smul_apply]
    have hhV : h⁻¹ * s ∈ (fun x : G => s * x) '' W := Set.mem_iInter₂.mp hh s hsS
    obtain ⟨w, hwW, hweq⟩ := hhV
    obtain ⟨u_w, hu_w_mem, hu_w_eq⟩ := Set.mem_iInter₂.mp hwW s hsS
    have hstab : u_w • f s = f s := MulAction.mem_stabilizer_iff.mp hu_w_mem
    have hinv : u_w⁻¹ • f s = f s := by
      calc u_w⁻¹ • f s = u_w⁻¹ • (u_w • f s) := by rw [hstab]
        _ = (u_w⁻¹ * u_w) • f s := by rw [mul_smul]
        _ = f s := by rw [inv_mul_cancel, one_smul]
    calc f (h⁻¹ * (s * ↑u₀))
        = f ((h⁻¹ * s) * ↑u₀) := by rw [mul_assoc]
      _ = f ((s * w) * ↑u₀) := by rw [← hweq]
      _ = f (s * (w * ↑u₀)) := by rw [mul_assoc]
      _ = f (s * ↑(u_w * u₀)) := by rw [← hu_w_eq]; rfl
      _ = (u_w * u₀)⁻¹ • f s := Coind.coe_mul f s (u_w * u₀)
      _ = u₀⁻¹ • (u_w⁻¹ • f s) := by rw [mul_inv_rev, mul_smul]
      _ = u₀⁻¹ • f s := by rw [hinv]
      _ = f (s * ↑u₀) := (Coind.coe_mul f s u₀).symm
  exact Subgroup.isOpen_of_mem_nhds (MulAction.stabilizer G f)
    (Filter.mem_of_superset (hVopen.mem_nhds h1V) hsub)

end Work.SSGRoute.PT
