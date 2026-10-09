/-
# The `p`-torsion of `Ωˣ` and the triviality of the level-`K` subgroup on `Hom_ℤ(N₁,Ωˣ)`

The remaining bookkeeping input `hhtop` of the coprime case of local Tate duality in degrees `0`/`2`
(`Submussion/Work/SSGRoute/PT/mkb_ld02_core_of_h3.lean`'s `mkb_alphaTwo_bijective_of_inputs`,
`PTUr/NOTE_E7_h02_frontier_measured.md` §3, §7) is

  `Subsingleton (H³(D_A, Hom_ℤ(N₁, Ωˣ)))`,  `N₁ = Coind_U^{D_A} N ⧸ N`,

deduced from `cd_p(D_A) ≤ 2` (the hypothesis `h3`) through
`Work.SSGRoute.PT.h3_H3_subsingleton_of_image`.  The latter needs a `↥(im(res k K))`-action on
`V = Hom_ℤ(N₁,Ωˣ)` compatible with the `D_A`-action; such an action can be *transported along*
`D_A ↠ G/U ≅ im(res k K)` precisely because `U = levelFixSub k Ω A K` acts **trivially** on `V`.

This file supplies the mathematical content of that triviality:

* `ptu_units_eq_pow_of_pow_eq_one` — a `p`-th root of unity is a power of a fixed primitive root;
* `ptu_ptorsion_units_smul_eq` — the `p`-torsion `Ωˣ[p] = μ_p` of `Ωˣ` is fixed by every element
  of `K.fixingSubgroup`, because `μ_p ⊆ K` (given a primitive `p`-th root in `K`);
* `ptu_ptorsion_units_finite` — `Ωˣ[p]` is finite;
* `ptu_conjHom_units_sub_smul_eq` — consequently `U` acts trivially on `Hom_ℤ(N₁,Ωˣ)`, which is
  the well-definedness input of the transported `↥(im)`-action.
-/
import Mathlib
import Submission.Work.SSGRoute.PT.Hilbert90IsAlgClosure
import Submission.Work.SSGRoute.PT.DevissageSESFinal
import Submission.Work.SSGRoute.PT.AlphaPairing

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open Classical

namespace Work.SSGRoute.PTUr

open Work.SSGRoute.PT

/-! ## `μ_p` in a field -/

/-- **Every `p`-th root of unity is a power of a primitive `p`-th root.** -/
theorem ptu_units_eq_pow_of_pow_eq_one {Ω : Type*} [Field Ω] {p : ℕ} [NeZero p]
    (ζu : Ωˣ) (hζu : IsPrimitiveRoot ζu p) (y : Ωˣ) (hy : y ^ p = 1) :
    y ∈ Subgroup.zpowers ζu := by
  rw [hζu.zpowers_eq, mem_rootsOfUnity']
  have h : ((y ^ p : Ωˣ) : Ω) = ((1 : Ωˣ) : Ω) := congrArg (fun u : Ωˣ => (u : Ω)) hy
  simpa using h

/-- **A `p`-torsion unit of `Ω` is fixed by every `k`-automorphism fixing a primitive `p`-th root
of unity**: `Ωˣ[p] = μ_p ⊆ K`. -/
theorem ptu_ptorsion_units_smul_eq {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) {p : ℕ} [Fact p.Prime] (ζu : Ωˣ)
    (hζu : IsPrimitiveRoot ζu p) (hζuK : (ζu : Ω) ∈ K)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup)
    (y : Additive (Units Ω)) (hy : p • y = 0) : σ • y = y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the multiplicative form of `p • y = 0`
  have hyu : (Additive.toMul y) ^ p = 1 := by
    have h := congrArg Additive.toMul hy
    simpa [toMul_nsmul] using h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
    (ptu_units_eq_pow_of_pow_eq_one ζu hζu (Additive.toMul y) hyu)
  -- the automorphism fixes `ζu`
  have hσζ : σ (ζu : Ω) = (ζu : Ω) := by
    have h : ∀ x ∈ (K : Set Ω), σ x = x := by simpa using hσ
    exact h (ζu : Ω) hζuK
  -- conclude on the units
  have hfix : algEquivUnitsMapOfField k Ω σ ζu = ζu := by
    apply Units.ext
    rw [algEquivUnitsMapOfField_coe]
    exact hσζ
  have hunit : algEquivUnitsMapOfField k Ω σ (Additive.toMul y) = Additive.toMul y := by
    rw [← hm]
    rw [MonoidHom.map_zpow, hfix]
  show Additive.ofMul (algEquivUnitsMapOfField k Ω σ (Additive.toMul y)) = y
  rw [hunit, ofMul_toMul]

/-- **`Ωˣ[p]` is finite.** -/
theorem ptu_ptorsion_units_finite {Ω : Type*} [Field Ω] {p : ℕ} [NeZero p] (ζu : Ωˣ)
    (hζu : IsPrimitiveRoot ζu p) :
    Finite {y : Additive (Units Ω) // p • y = 0} := by
  haveI : Finite ↥(Subgroup.zpowers ζu) :=
    Finite.of_injective
      (fun x : ↥(Subgroup.zpowers ζu) =>
        (hζu.zmodEquivZPowers.symm (Additive.ofMul x) : ZMod p)) (by
      intro x y hxy
      have h := hζu.zmodEquivZPowers.symm.injective hxy
      have h' := congrArg Additive.toMul h
      simpa using h')
  let F : {y : Additive (Units Ω) // p • y = 0} → ↥(Subgroup.zpowers ζu) := fun y =>
    ⟨Additive.toMul y.1,
      ptu_units_eq_pow_of_pow_eq_one ζu hζu (Additive.toMul y.1) (by
        have h := congrArg Additive.toMul y.2
        simpa [toMul_nsmul] using h)⟩
  refine Finite.of_injective F ?_
  intro x y hxy
  have h : Additive.toMul x.1 = Additive.toMul y.1 :=
    congrArg (f := fun z : ↥(Subgroup.zpowers ζu) => (z : Ωˣ)) hxy
  refine Subtype.ext ?_
  simpa using congrArg Additive.ofMul h


/-! ## Triviality of a group fixing `μ_p` and acting trivially on the source -/

/-- **If every `g : G` fixes the `p`-torsion of `Ωˣ` and acts trivially on `N₁`, then `G` acts
trivially on `Hom_ℤ(N₁,Ωˣ)`.**  (The `p`-torsion of `Ωˣ` is `μ_p`, fixed by the level-`K`
subgroup `K.fixingSubgroup`; see `ptu_ptorsion_units_smul_eq`.) -/
theorem ptu_conjHom_units_smul_eq_of_fix {Ω : Type*} [Field Ω] {p : ℕ} [Fact p.Prime]
    {G : Type*} [Group G] {N₁ : Type*} [AddCommGroup N₁] [Module (ZMod p) N₁]
    [DistribMulAction G N₁] [DistribMulAction G (Additive (Units Ω))]
    (hfix : ∀ (g : G) (y : Additive (Units Ω)), p • y = 0 → g • y = y)
    (hgN : ∀ (g : G) (n : N₁), g • n = n)
    (hNp : ∀ n : N₁, p • n = 0)
    (g : G) (f : ConjHom N₁ (Additive (Units Ω))) : g • f = f := by
  refine ConjHom.ext_apply (fun n => ?_)
  rw [ConjHom.smul_apply, hgN g⁻¹ n]
  refine hfix g (f n) ?_
  rw [← map_nsmul]
  simp [hNp n]

end Work.SSGRoute.PTUr
