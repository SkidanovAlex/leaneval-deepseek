import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Work.DoubleTransitivity.App2

open Submission.Blueprint

/-!
# Peterfalvi, Appendix II (5)

Setting (Peterfalvi App. II): `X` is a finite group acting on a set `E`, `p` is a prime,
`a ≠ b` are points of `E`, and `D = X_a ⊓ X_b` is the two-point stabiliser.  If `X` is
`2`-transitive (multiply pretransitive of degree `2`) on `E` and `P` is a Sylow `p`-subgroup
of `D`, then `N_X(P)` is `2`-transitive on the set `E_P` of fixed points of `P`.

The mathematical proof is the classical four-line one:

* if `c ≠ d` lie in `E_P`, `2`-transitivity gives `g` with `g • a = c`, `g • b = d`, so the
  two-point stabiliser of `(c,d)` is `conj g D` and `conj g P` is a Sylow `p`-subgroup of it;
* `P` is a Sylow `p`-subgroup of that same group as well (it is a `p`-subgroup of equal order);
* Sylow conjugacy inside `X_c ⊓ X_d` now produces `y ∈ X_c ⊓ X_d` with `conj y P = conj g P`,
  i.e. `g⁻¹ y ∈ N_X(P)`, and its inverse `y⁻¹ g` maps `a ↦ c`, `b ↦ d`;
* consequently every pair of distinct points of `E_P` is the `N_X(P)`-image of `(a,b)`, and
  `2`-transitivity of `N_X(P)` on `E_P` follows by composing.

The four lemmas proved below are exactly the four ingredients: `stabilizer_inf_conj`,
`isSylowSubgroupOf_conj`, `isSylowSubgroupOf_of_le_conj` and `sylow_conj_in_subgroup`.
-/

/-- The two-point stabiliser of `(g • a, g • b)` is the `g`-conjugate of the two-point
stabiliser of `(a,b)`. -/
theorem stabilizer_inf_conj {X E : Type} [Group X] [MulAction X E] {a b c d : E} {g : X}
    (hga : g • a = c) (hgb : g • b = d) :
    MulAction.stabilizer X c ⊓ MulAction.stabilizer X d =
      conj g (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b) := by
  rw [← hga, ← hgb, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]

/-- Conjugation carries Sylow `p`-subgroups of `D` to Sylow `p`-subgroups of `conj t D`. -/
theorem isSylowSubgroupOf_conj {X : Type} [Group X] {p : ℕ} {D P : Subgroup X}
    (hP : IsSylowSubgroupOf p P D) (t : X) :
    IsSylowSubgroupOf p (conj t P) (conj t D) := by
  refine ⟨Subgroup.map_mono hP.1, ?_, ?_⟩
  · simpa [Submission.Blueprint.conj] using IsPGroup.map hP.2.1 (MulAut.conj t).toMonoidHom
  · have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t).toMonoidHom) P D
      (MulAut.conj t).injective
    rw [Subgroup.relIndex] at h
    intro hdvd
    rw [h] at hdvd
    exact hP.2.2 hdvd

/-- A `p`-subgroup of `D` of the same order as a conjugate of a Sylow `p`-subgroup of `D`
is itself Sylow in `D`. -/
theorem isSylowSubgroupOf_of_le_conj {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {D P : Subgroup X} {t : X} (h : IsSylowSubgroupOf p (conj t P) D) (hle : P ≤ D)
    (hgrp : IsPGroup p P) : IsSylowSubgroupOf p P D := by
  have hcard1 : Nat.card ↥(P.subgroupOf D) = Nat.card ↥P := by
    rw [← Subgroup.card_map_of_injective (f := D.subtype) (K := P.subgroupOf D)
        D.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
  have hcard2 : Nat.card ↥((conj t P).subgroupOf D) = Nat.card ↥(conj t P) := by
    rw [← Subgroup.card_map_of_injective (f := D.subtype)
        (K := (conj t P).subgroupOf D) D.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.1]
  have hcard3 : Nat.card ↥(conj t P) = Nat.card ↥P := by
    rw [Submission.Blueprint.conj]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom) (K := P)
      (MulAut.conj t).injective
  refine ⟨hle, hgrp, ?_⟩
  intro hdvd
  apply h.2.2
  rw [Subgroup.index_eq_card_div, hcard2, hcard3, ← hcard1, ← Subgroup.index_eq_card_div]
  exact hdvd

/-- **Sylow conjugacy inside a subgroup**: two Sylow `p`-subgroups of a subgroup `D ≤ X`
(finite `X`) are conjugate by an element of `D`. -/
theorem sylow_conj_in_subgroup {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {D P Q : Subgroup X} (hP : IsSylowSubgroupOf p P D) (hQ : IsSylowSubgroupOf p Q D) :
    ∃ d ∈ D, conj d P = Q := by
  have hPg : IsPGroup p (P.subgroupOf D) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hQg : IsPGroup p (Q.subgroupOf D) :=
    hQ.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm
  let SP : Sylow p ↥D := hPg.toSylow hP.2.2
  let SQ : Sylow p ↥D := hQg.toSylow hQ.2.2
  haveI : Finite (Sylow p ↥D) := Sylow.finite_of_finiteIndex SP
  obtain ⟨d, hd⟩ :=
    (inferInstance : MulAction.IsPretransitive ↥D (Sylow p ↥D)).exists_smul_eq SP SQ
  -- `d • SP = SQ` unfolds to `conj d P = Q` inside `X`
  have hd' : (MulAut.conj d) • (P.subgroupOf D) = Q.subgroupOf D := by
    have h := congrArg (fun S : Sylow p ↥D => (S : Subgroup ↥D)) hd
    simpa [SP, SQ, Sylow.coe_subgroup_smul] using h
  have htrans : ((MulAut.conj d) • (P.subgroupOf D)).map D.subtype = conj (d : X) P := by
    have hcomp : D.subtype.comp (MulDistribMulAction.toMonoidHom (↥D) (MulAut.conj d))
        = (MulAut.conj (d : X)).toMonoidHom.comp D.subtype := by
      ext x
      simp [MulAut.conj_apply]
    rw [Subgroup.pointwise_smul_def, MulDistribMulAction.toMonoidEnd_apply, Subgroup.map_map,
      hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hP.1]
  refine ⟨(d : X), d.2, ?_⟩
  rw [← htrans, hd', Subgroup.map_subgroupOf_eq_of_le hQ.1]

/-- **Peterfalvi, Appendix II (5)**: if `X` acts `2`-transitively on `E` and `P` is a Sylow
`p`-subgroup of the two-point stabiliser `X_a ⊓ X_b` (`a ≠ b`), then the normaliser `N_X(P)`
acts `2`-transitively on the set of fixed points of `P`. -/
theorem app2_5 {X E : Type} [Group X] [MulAction X E] [Finite X]
    {p : ℕ} [Fact p.Prime] {a b : E} (hab : a ≠ b)
    (h2 : MulAction.IsMultiplyPretransitive X E 2)
    {P : Subgroup X}
    (hP : IsSylowSubgroupOf p P (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b)) :
    IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set X)) (fixedBySub P : Set E) := by
  classical
  -- `a` and `b` are fixed by `P`
  have ha : a ∈ fixedBySub P := fun m hm => MulAction.mem_stabilizer_iff.mp ((hP.1 hm).1)
  have hb : b ∈ fixedBySub P := fun m hm => MulAction.mem_stabilizer_iff.mp ((hP.1 hm).2)
  -- key step: every pair of distinct points of `fixedBySub P` is the image of `(a,b)`
  -- under an element of `N_X(P)`
  have key : ∀ c ∈ fixedBySub P, ∀ d ∈ fixedBySub P, c ≠ d →
      ∃ y ∈ Subgroup.normalizer (P : Set X), y • a = c ∧ y • b = d := by
    intro c hc d hd hcd
    obtain ⟨g, hga, hgb⟩ := (MulAction.is_two_pretransitive_iff.mp h2) hab hcd
    have hPle : P ≤ MulAction.stabilizer X c ⊓ MulAction.stabilizer X d :=
      le_inf (fun m hm => MulAction.mem_stabilizer_iff.mpr (hc m hm))
        (fun m hm => MulAction.mem_stabilizer_iff.mpr (hd m hm))
    have hD' : MulAction.stabilizer X c ⊓ MulAction.stabilizer X d =
        conj g (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b) :=
      stabilizer_inf_conj hga hgb
    have hS1 : IsSylowSubgroupOf p (conj g P)
        (MulAction.stabilizer X c ⊓ MulAction.stabilizer X d) := by
      rw [hD']
      exact isSylowSubgroupOf_conj hP g
    have hS2 : IsSylowSubgroupOf p P (MulAction.stabilizer X c ⊓ MulAction.stabilizer X d) :=
      isSylowSubgroupOf_of_le_conj hS1 hPle hP.2.1
    obtain ⟨y, hy, hyconj⟩ := sylow_conj_in_subgroup hS2 hS1
    have hyc : y ∈ MulAction.stabilizer X c := hy.1
    have hyd : y ∈ MulAction.stabilizer X d := hy.2
    -- `g⁻¹ * y` normalises `P`, so its inverse `y⁻¹ * g` does too
    have hconj : conj (g⁻¹ * y) P = P := by
      rw [conj_mul, hyconj, conj_inv_conj]
    have hmem : y⁻¹ * g ∈ Subgroup.normalizer (P : Set X) := by
      rw [← conj_eq_self_iff_mem_normalizer]
      have h1 := conj_inv_conj (g⁻¹ * y) P
      rw [hconj] at h1
      simpa [mul_inv_rev, inv_inv] using h1
    refine ⟨y⁻¹ * g, hmem, ?_, ?_⟩
    · show (y⁻¹ * g) • a = c
      rw [mul_smul, hga]
      exact MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer X c).inv_mem hyc)
    · show (y⁻¹ * g) • b = d
      rw [mul_smul, hgb]
      exact MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer X d).inv_mem hyd)
  -- assembly: compose the two elements of `N_X(P)` produced by `key`
  intro c hc d hd hcd c' hc' d' hd' hcd'
  obtain ⟨y₁, hy₁, hy₁a, hy₁b⟩ := key c hc d hd hcd
  obtain ⟨y₂, hy₂, hy₂a, hy₂b⟩ := key c' hc' d' hd' hcd'
  refine ⟨y₂ * y₁⁻¹, (Subgroup.normalizer (P : Set X)).mul_mem hy₂
      ((Subgroup.normalizer (P : Set X)).inv_mem hy₁), ?_, ?_⟩
  · show (y₂ * y₁⁻¹) • c = c'
    have h : y₁⁻¹ • c = a := by rw [← hy₁a, inv_smul_smul]
    rw [mul_smul, h, hy₂a]
  · show (y₂ * y₁⁻¹) • d = d'
    have h : y₁⁻¹ • d = b := by rw [← hy₁b, inv_smul_smul]
    rw [mul_smul, h, hy₂b]

end Work.DoubleTransitivity.App2
