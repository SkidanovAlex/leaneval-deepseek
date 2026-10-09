import Mathlib
import Submission.Work.SSGRoute.PT.alphaTwo_trivAction_of_trivMod
import Submission.Work.SSGRoute.PT.kummerSES
import Submission.Work.SSGRoute.PT.KrullCorrespondence
import Submission.Work.SSGRoute.PT.alphaTwo_base_case
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option linter.style.haveILetI false

open Classical

noncomputable section

/-! ## The two structural side conditions of `kummerSES` for the coefficient module `Ωˣ`

The Kummer short exact sequence `0 → Hom_ℤ(ℤ/p, Ωˣ) → Ωˣ →^p Ωˣ → 0` (`PT.kummerSES`) requires
the coefficient module `C = Additive (Units Ω) = Ωˣ` to be `p`-**divisible** and **discrete** for
the action of the relevant Galois group.  Both are consequences of the standing hypotheses
(`Ω` an algebraic closure of the number field `k`, `U ≤ Gal(Ω/k)` an open subgroup), and they are
proved here as standalone lemmas so that `kummerSES` applies verbatim. -/

/-- **`Ωˣ` is `p`-divisible** for an algebraically closed field `Ω` and any `p > 0`: every unit
has a `p`-th root. -/
theorem addUnits_nsmul_surjective_of_isAlgClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (p : ℕ) (hp : 0 < p) :
    ∀ c : Additive (Units Ω), ∃ c' : Additive (Units Ω), p • c' = c := by
  intro c
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (((Additive.toMul c : Units Ω)) : Ω) hp
  have hz0 : z ≠ 0 := by
    intro h0
    have h1 : (((Additive.toMul c : Units Ω)) : Ω) = 0 := by
      rw [← hz, h0, zero_pow (Nat.ne_of_gt hp)]
    exact (Additive.toMul c).ne_zero h1
  refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
  show Additive.ofMul (Additive.toMul (Additive.ofMul (Units.mk0 z hz0)) ^ p) = c
  rw [toMul_ofMul, ← ofMul_toMul c]
  congr 1
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hz)

/-- **The `↥U`-module `Ωˣ` is discrete** for an open subgroup `U ≤ Gal(Ω/k)`: the stabiliser in
`↥U` of a unit is the preimage of the stabiliser of that unit in `Gal(Ω/k)` (a finite intersection
of open stabilisers of integral elements, `stabilizer_isOpen_of_isIntegral`), and `↥U → Gal(Ω/k)`
is continuous. -/
theorem isDiscreteModule_addUnits_openSubgroup {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (U : Subgroup (Ω ≃ₐ[k] Ω)) :
    Work.AbsoluteKummer.IsDiscreteModule ↥U (Additive (Units Ω)) := by
  intro m
  have hset : (MulAction.stabilizer ↥U m : Set ↥U)
      = Subtype.val ⁻¹' ((MulAction.stabilizer (Ω ≃ₐ[k] Ω) m) : Set (Ω ≃ₐ[k] Ω)) := by
    ext g
    exact Iff.rfl
  rw [hset]
  refine (?_ : IsOpen ((MulAction.stabilizer (Ω ≃ₐ[k] Ω) m) : Set (Ω ≃ₐ[k] Ω))).preimage
    continuous_subtype_val
  have hstab : (MulAction.stabilizer (Ω ≃ₐ[k] Ω) m : Set (Ω ≃ₐ[k] Ω))
      = (MulAction.stabilizer (Ω ≃ₐ[k] Ω) (((Additive.toMul m : Units Ω)) : Ω) :
          Set (Ω ≃ₐ[k] Ω)) := by
    ext σ
    rw [SetLike.mem_coe, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      have h0 : Additive.ofMul
          (algEquivUnitsMapOfField k Ω σ (Additive.toMul m)) = m := h
      have h2 : algEquivUnitsMapOfField k Ω σ (Additive.toMul m) = Additive.toMul m := by
        have h1 := congrArg Additive.toMul h0
        rw [toMul_ofMul] at h1
        exact h1
      exact congrArg (fun w : Units Ω => (w : Ω)) h2
    · intro h
      have h2 : algEquivUnitsMapOfField k Ω σ (Additive.toMul m) = Additive.toMul m :=
        Units.ext h
      show Additive.ofMul (algEquivUnitsMapOfField k Ω σ (Additive.toMul m)) = m
      rw [h2, ofMul_toMul]
  rw [hstab]
  exact stabilizer_isOpen_of_isIntegral _

/-- **The trivial-action base case of the `α²`-dévissage with the units coefficient at an open
subgroup.**  For an open subgroup `U ≤ Gal(Ω/k)` (`Ω` an algebraic closure of the number field
`k`) and a finite `𝔽_p[U]`-module `N` on which `U` acts trivially, the pairing
`α²(U, N) : H²(U, Hom_ℤ(N, Ωˣ)) → Hom_U(N, H²(U, Ωˣ))` is bijective.

This is the `hN₂`-slot input of `PT.alphaTwo_coind_bijective_of_cor` (the *base case* of Milne's
dévissage of Theorem I.1.8, Milne *ADT* (1.7) in the trivially-acting case), for the coefficient
module `C = Additive (Units Ω) = k̄^×`:

* `Work.SSGRoute.PT.alphaTwo_trivMod_bijective` gives `α²(U, ℤ/p)` from the Kummer short exact
  sequence `0 → Hom_ℤ(ℤ/p, Ωˣ) → Ωˣ →^p Ωˣ → 0` (`PT.kummerSES`, using the divisibility of `Ωˣ`)
  together with `H¹(U, Ωˣ) = 0`;
* `H¹(U, Ωˣ) = 0` is Hilbert 90 for the open subgroup `U`, proved in this workspace as
  `Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`
  (`Submission/Work/SSGRoute/PT/KrullCorrespondence.lean`);
* `Work.SSGRoute.PT.alphaTwo_trivAction_of_trivMod` upgrades `α²(U, ℤ/p)` to every finite
  `𝔽_p[U]`-module with trivial action.

The side conditions of `kummerSES` are both derivable: `p`-divisibility of `Ωˣ` (an algebraic
closure of a field of characteristic `0` contains `p`-th roots) and discreteness of the
`U`-module `Ωˣ` (every unit lies in a finite extension of `k`, hence is fixed by an open subgroup;
the same computation is carried out for decomposition groups in
`PT/br_pTorsion_openSubgroup.lean`). -/
theorem alphaTwo_trivAction_units_openSubgroup
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] [IsAlgClosure k Ω]
    (U : Subgroup (Ω ≃ₐ[k] Ω)) (hU : IsOpen (U : Set (Ω ≃ₐ[k] Ω)))
    {N : Type} [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction ↥U N]
    (htriv : ∀ (g : ↥U) (n : N), g • n = n) [Finite N] :
    Function.Bijective
      (Work.SSGRoute.PT.alphaTwo (G := ↥U) (N := N) (C := Additive (Units Ω))) := by
  haveI : IsTopologicalGroup ↥U := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- `H¹(U, Ωˣ) = 0`: Hilbert 90 at the open subgroup `U`
  have h1 : Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive (Units Ω))) :=
    hilbert90_H1_eq_zero_openSubgroup U hU
  -- the two side conditions of the Kummer sequence
  have hdiv : ∀ c : Additive (Units Ω), ∃ c', p • c' = c :=
    addUnits_nsmul_surjective_of_isAlgClosed p (Fact.out : p.Prime).pos
  have hdisc : Work.AbsoluteKummer.IsDiscreteModule ↥U (Additive (Units Ω)) :=
    isDiscreteModule_addUnits_openSubgroup U
  obtain ⟨S, hSι, hSπ⟩ := kummerSES (G := ↥U) p hdiv hdisc
  -- the Kummer base case `α²(U, ℤ/p)`, then the trivial-action reduction to `N`
  exact alphaTwo_trivAction_of_trivMod (G := ↥U) (C := Additive (Units Ω)) (N := N) p htriv
    (alphaTwo_trivMod_bijective (G := ↥U) p S hSι hSπ h1)

end

end Work.SSGRoute.PT
