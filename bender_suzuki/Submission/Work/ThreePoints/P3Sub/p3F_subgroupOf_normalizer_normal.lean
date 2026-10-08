import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.oddResidual_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `F = O^{2'}(C_G(X))` is normal in `N_G(X)`

`p3F X = (oddResidual (C_G(X))).map C_G(X).subtype` is the group `F` of Peterfalvi I Ch. II §4
Prop. 3.  This file proves that it is normalised by `N_G(X)` — the fact used (as `B ◁ N_H(X)`)
in the transfer step of Prop. 3 (b), where `B = F ⊓ H` and `N_H(X) = B·N_D(X)`.

The argument: for `n ∈ N_G(X)`, conjugation by `n` is an automorphism of `C = C_G(X)` (it
permutes `X`), and `O^{2'}` is invariant under every automorphism of `C`: `O^{2'}(C)` is the
intersection of the normal subgroups of odd index, and an automorphism permutes that family.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- Conjugation by `n ∈ N_G(X)` preserves `C_G(X)`. -/
theorem p3F_conj_mem_centralizer {X : Subgroup G} {n y : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G))
    (hy : y ∈ Subgroup.centralizer (X : Set G)) :
    n * y * n⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  have hn' : ∀ x : G, x ∈ X ↔ n⁻¹ * x * n ∈ X :=
    Subgroup.mem_normalizer_iff''.mp hn
  have hy' := Subgroup.mem_centralizer_iff.mp hy
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro x hx
  have hx' : n⁻¹ * x * n ∈ X := (hn' x).mp hx
  have h := hy' (n⁻¹ * x * n) hx'
  show x * (n * y * n⁻¹) = (n * y * n⁻¹) * x
  calc x * (n * y * n⁻¹) = n * ((n⁻¹ * x * n) * y) * n⁻¹ := by group
    _ = n * (y * (n⁻¹ * x * n)) * n⁻¹ := by rw [h]
    _ = (n * y * n⁻¹) * x := by group

/-- An element of `N_G(X)` lies in `N_G(C_G(X))`. -/
theorem mem_normalizer_centralizer_of_mem_normalizer {X : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) :
    n ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact p3F_conj_mem_centralizer hn hy
  · intro hy
    have h1 : n⁻¹ * (n * y * n⁻¹) * n ∈ Subgroup.centralizer (X : Set G) := by
      simpa using p3F_conj_mem_centralizer ((Subgroup.normalizer (X : Set G)).inv_mem hn) hy
    have h2 : n⁻¹ * (n * y * n⁻¹) * n = y := by group
    rwa [h2] at h1

/-- The automorphism of `C_G(X)` induced by conjugation with `n ∈ N_G(X)`. -/
noncomputable def conjCentralizer (X : Subgroup G) (n : G)
    (hn : n ∈ Subgroup.normalizer (X : Set G)) :
    ↥(Subgroup.centralizer (X : Set G)) ≃* ↥(Subgroup.centralizer (X : Set G)) :=
  { toFun := fun c => ⟨n * (c : G) * n⁻¹, p3F_conj_mem_centralizer hn c.2⟩
    invFun := fun c =>
      ⟨n⁻¹ * (c : G) * n, by
        simpa using
          p3F_conj_mem_centralizer ((Subgroup.normalizer (X : Set G)).inv_mem hn) c.2⟩
    left_inv := fun c => Subtype.ext (by group)
    right_inv := fun c => Subtype.ext (by group)
    map_mul' := fun a b => Subtype.ext (by
      show n * ((a : G) * (b : G)) * n⁻¹ =
        (n * (a : G) * n⁻¹) * (n * (b : G) * n⁻¹)
      group) }

/-- `O^{2'}(C_G(X))` is invariant under the conjugation automorphism of `C_G(X)`: `O^{2'}` is
the intersection of the normal subgroups of odd index, and an automorphism permutes them. -/
theorem conjCentralizer_oddResidual_le (X : Subgroup G) (n : G)
    (hn : n ∈ Subgroup.normalizer (X : Set G)) :
    Subgroup.map (conjCentralizer X n hn).toMonoidHom
        (Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (X : Set G))) ≤
      Submission.Blueprint.oddResidual ↥(Subgroup.centralizer (X : Set G)) := by
  classical
  refine (Subgroup.map_le_iff_le_comap).mpr ?_
  intro c hc
  rw [Subgroup.mem_comap]
  rw [Submission.Blueprint.oddResidual, Subgroup.mem_sInf] at hc ⊢
  intro N hN
  have hM : (N.map (conjCentralizer X n hn).symm.toMonoidHom).Normal :=
    hN.1.map _ (conjCentralizer X n hn).symm.surjective
  have hrange : (conjCentralizer X n hn).symm.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (conjCentralizer X n hn).symm.surjective
  have hMidx : Odd (N.map (conjCentralizer X n hn).symm.toMonoidHom).index := by
    rw [Subgroup.index_map_of_injective N (conjCentralizer X n hn).symm.injective,
      hrange, Subgroup.index_top, mul_one]
    exact hN.2
  have hthis := hc (N.map (conjCentralizer X n hn).symm.toMonoidHom) ⟨hM, hMidx⟩
  rw [Subgroup.mem_map] at hthis
  obtain ⟨y, hy, hyc⟩ := hthis
  have hy' : y = conjCentralizer X n hn c := by
    have h := congrArg (fun z => conjCentralizer X n hn z) hyc
    simpa using h
  exact hy' ▸ hy

/-- `F = O^{2'}(C_G(X))` is invariant under conjugation by elements of `N_G(X)`. -/
theorem p3F_le_normalizer_conj {X : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (X : Set G)) :
    Subgroup.map (MulAut.conj n).toMonoidHom (p3F X) ≤ p3F X := by
  intro h hh
  rw [Subgroup.mem_map] at hh
  obtain ⟨h₀, hh₀, rfl⟩ := hh
  rw [mem_p3F] at hh₀ ⊢
  obtain ⟨c, hc, rfl⟩ := hh₀
  refine ⟨⟨n * (c : G) * n⁻¹, p3F_conj_mem_centralizer hn c.2⟩, ?_, rfl⟩
  have hφ := conjCentralizer_oddResidual_le X n hn
  have hmem := Subgroup.mem_map_of_mem (conjCentralizer X n hn).toMonoidHom hc
  exact hφ hmem

/-- `F = O^{2'}(C_G(X))` is normal in `N_G(X)`. -/
theorem p3F_subgroupOf_normalizer_normal (X : Subgroup G) :
    ((p3F X).subgroupOf (Subgroup.normalizer (X : Set G))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    ((p3F_le_centralizer X).trans (Subgroup.centralizer_le_normalizer (X : Set G)))]
  rw [Subgroup.le_normalizer_iff]
  intro n hn h hh
  simpa [MulAut.conj_apply] using
    p3F_le_normalizer_conj hn (Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hh)

end Work.ThreePoints
