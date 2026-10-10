import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Data.Nat.Prime.Defs
import Submission.Work.SSGRoute.PT.AlphaTwoKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer short exact sequence in the coefficient model

For a discrete `G`-module `C` that is `p`-divisible, the sequence

  `0 → Hom_ℤ(ℤ/p, C) →^{evalOne} C →^{p·} C → 0`

is a short exact sequence of discrete `G`-modules, where `Hom_ℤ(ℤ/p,C)` is the copy
`ConjHom (TrivMod G p) C` carrying the conjugation action, `evalOne φ = φ 1` and `p ·` is
multiplication by `p`.

The three ingredients are

* `evalOne` is injective, since an additive hom out of `ℤ/p` is determined by its value at `1`
  (`ConjHom.ext_one`);
* `range evalOne = {c | p • c = 0} = ker (p·)`: the inclusion `⊆` is `mem_PTor_evalOne` and the
  reverse inclusion is the inverse of the coefficient identification
  `conjHomTrivModEquivPTor : Hom_ℤ(ℤ/p,C) ≃+ C[p]` (which is `evalOne` followed by the subtype
  inclusion, `subtype_comp_conjHomTrivModEquivPTor`);
* `p·` is onto by the divisibility hypothesis `hdiv`;

and the three structural requirements are equivariance of `evalOne` (`evalOne_equivariant`) and of
`p·` (`DistribSMul.toAddMonoidHom _ g` is additive), and discreteness of the three coefficient
modules: `C` twice by hypothesis `hM`, and `ConjHom (TrivMod G p) C` by
`isDiscreteModule_conjHom_trivMod` below, which avoids the `[IsTopologicalGroup G]` hypothesis of
`isDiscreteModule_conjHom` by observing that the action on `TrivMod G p` is trivial, hence
`Stab_G(f) = Stab_G(f 1)`.
-/

set_option linter.unusedSectionVars false

open Classical

namespace Work.SSGRoute.PT

noncomputable section

/-- **Discreteness of `Hom_ℤ(ℤ/p, C)` with the conjugation action.**  Note that this does *not*
require `IsTopologicalGroup G` (unlike `isDiscreteModule_conjHom`): the action of `G` on
`TrivMod G p = ℤ/p` is trivial, so

  `Stab_G(f) = {g | g • f = f} = {g | g • f 1 = f 1} = Stab_G(f 1)`,

an open subgroup by the discreteness of `C`. -/
theorem isDiscreteModule_conjHom_trivMod {G : Type*} [TopologicalSpace G] [Group G] (p : ℕ)
    [Fact p.Prime] {C : Type*} [AddCommGroup C] [DistribMulAction G C]
    (hM : Work.AbsoluteKummer.IsDiscreteModule G C) :
    Work.AbsoluteKummer.IsDiscreteModule G (ConjHom (TrivMod G p) C) := by
  intro f
  have hstab : MulAction.stabilizer G f = MulAction.stabilizer G (f 1) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      simpa [ConjHom.smul_apply, TrivMod.smul_eq] using
        congrArg (fun φ : ConjHom (TrivMod G p) C => φ (1 : TrivMod G p)) h
    · intro h
      exact ConjHom.ext_one p (by simpa [ConjHom.smul_apply, TrivMod.smul_eq] using h)
  rw [hstab]
  exact hM (f 1)

/-- **The Kummer short exact sequence in the coefficient model.**  For a discrete `G`-module `C`
that is `p`-divisible, the sequence

  `0 → Hom_ℤ(ℤ/p, C) →^{evalOne} C →^{p·} C → 0`

is a short exact sequence of discrete `G`-modules, where `Hom_ℤ(ℤ/p,C)` is the copy
`ConjHom (TrivMod G p) C` carrying the conjugation action, `evalOne φ = φ 1` and `p ·` is
multiplication by `p`.

Proof ingredients: `evalOne` is injective (a hom out of `ℤ/p` is determined by its value at `1`);
`range evalOne = {c | p • c = 0}` using `Work.SSGRoute.PT.conjHomTrivModEquivPTor` (every `c`
killed by `p` is the value at `1` of an additive map out of `ℤ/p`); `pi = p·` is onto by the
divisibility hypothesis; equivariance is `Work.SSGRoute.PT.evalOne_equivariant` and the triviality
of the `G`-action on `TrivMod G p`.  **Note for the prover:** `isDiscreteModule_conjHom` requires
`[IsTopologicalGroup G]`, which is *not* assumed here; instead use that the action on `TrivMod G p`
is trivial, so `stabilizer G f = ⋂_{n : ZMod p} stabilizer G (f n)` is a finite intersection of
open sets. -/
theorem kummerSES {G : Type*} [TopologicalSpace G] [Group G] (p : ℕ) [Fact p.Prime]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C]
    (hdiv : ∀ c : C, ∃ c' : C, p • c' = c)
    (hM : Work.AbsoluteKummer.IsDiscreteModule G C) :
    ∃ S : Work.AbsoluteKummer.ShortExactSeq G
        (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.PT.TrivMod G p) C) C C,
      S.iota = Work.SSGRoute.PT.evalOne G p C ∧ (∀ c : C, S.pi c = p • c) := by
  -- `evalOne` is injective: a hom out of `ℤ/p` is determined by its value at `1`
  have hι_inj : Function.Injective (evalOne G p C) := by
    intro f g h
    exact ConjHom.ext_one p h
  -- `p ·` is onto by divisibility
  have hπ_surj : Function.Surjective (nsmulHom p C) := by
    intro c
    obtain ⟨c', hc'⟩ := hdiv c
    exact ⟨c', by rw [nsmulHom_apply]; exact hc'⟩
  -- exactness in the middle: `evalOne` is exactly the `p`-torsion of `C`
  have hι_eq : (evalOne G p C).range = (nsmulHom p C).ker := by
    ext c
    constructor
    · rintro ⟨f, rfl⟩
      rw [AddMonoidHom.mem_ker, nsmulHom_apply]
      exact mem_PTor_evalOne p f
    · intro hc
      rw [AddMonoidHom.mem_ker, nsmulHom_apply] at hc
      refine ⟨(conjHomTrivModEquivPTor G p C).symm ⟨c, hc⟩, ?_⟩
      rw [← subtype_comp_conjHomTrivModEquivPTor G p C]
      simp
  -- multiplication by `p` is `G`-equivariant (the action is additive)
  have hπ_eqv : Work.GroupCohomology.IsEquivariant G (nsmulHom p C) := by
    intro g c
    show nsmulHom p C (g • c) = g • nsmulHom p C c
    rw [nsmulHom_apply, nsmulHom_apply]
    exact (AddMonoidHom.map_nsmul (DistribSMul.toAddMonoidHom C g) p c).symm
  refine ⟨{ iota := evalOne G p C
            pi := nsmulHom p C
            iota_equivariant := evalOne_equivariant G p C
            pi_equivariant := hπ_eqv
            iota_injective := hι_inj
            pi_surjective := hπ_surj
            range_iota_eq_ker_pi := hι_eq
            isDiscreteM := isDiscreteModule_conjHom_trivMod p hM
            isDiscreteN := hM
            isDiscreteP := hM }, ?_, ?_⟩
  · rfl
  · intro c
    rw [nsmulHom_apply]

end

end Work.SSGRoute.PT
