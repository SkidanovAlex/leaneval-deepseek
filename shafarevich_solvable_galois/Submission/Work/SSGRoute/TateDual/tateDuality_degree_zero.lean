import Mathlib
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.Tate.All
import Submission.Work.SSGRoute.TateDual.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TateDual

/-!
**Finite-group Tate duality in degree `0`**, in the models of `Submission/Work/Tate`.

For a finite group `G` and a finite-dimensional `𝔽_p`-module `A` carrying a compatible
`G`-action, the evaluation pairing

  `ker(N_A) × (A^∨)^G → 𝔽_p`,  `⟨a, φ⟩ = φ a`,  `A^∨ = Work.SSGRoute.DualMod p A`,

where `N_A : A →+ A` is the norm `N_A a = ∑ g, g • a` (`Work.Tate.norm G A`), descends to a
perfect pairing `Ĥ⁻¹(G, A) × Ĥ⁰(G, A^∨) → 𝔽_p`, with
`Ĥ⁻¹(G, A) = Work.Tate.Hm1 G A = ker(N_A)/I_G·A` and
`Ĥ⁰(G, A^∨) = Work.Tate.H0 G (DualMod p A) = (A^∨)^G / N_{A^∨}(A^∨)`.
The statement below is the resulting additive isomorphism.  Together with dimension shifting it is
the finite-group Tate duality `Ĥ^{-n-1}(G, A^∨) ≅ Ĥ^n(G, A)^∨`.

PROOF OUTLINE (finite-dimensional linear algebra over the field `𝔽_p`; the only group-theoretic
input is the self-adjointness of the norm, `⟨N_A a, φ⟩ = ⟨a, N_{A^∨} φ⟩`, which follows from
`g ↦ g⁻¹` being a bijection).

Put `U := (Work.Tate.norm G A).ker` (an `AddSubgroup` of `A`), `U₀ := Work.Tate.augInKer G A`,
`V := Work.Tate.fixedSubgroup G (DualMod p A)`,
`V₀ := (Work.Tate.normToFixed G (DualMod p A)).range`.  Write
`P : U → (V → 𝔽_p)`, `P x = fun φ ↦ φ x`.  The two `⊥`-computations are

* `{x : A | ∀ φ ∈ V, φ x = 0} = I_G·A (= U₀)`: a functional `φ` is `G`-fixed iff it kills
  `I_G·A`, and for finite-dimensional spaces the double annihilator is the original subspace
  (`Submodule.dualAnnihilator`, `Submodule.dualCoannihilator`,
  `Subspace.dualAnnihilator_dualCoannihilator_eq`, `Module.evalEquiv` to transport along the
  reflexivity `Dual (Dual A) ≅ A`);
* `{φ : A^∨ | ∀ x ∈ U, φ x = 0} = V₀`, i.e. the functionals killing `ker N_A` are exactly the
  norms `N_{A^∨} ψ`.  One inclusion is `φ = N ψ ⟹ φ (N a) = ψ (N a) = 0`; the reverse is again
  the double annihilator identity, this time combined with
  `LinearMap.range_dualMap_eq_dualAnnihilator_ker` (`N_{A^∨}` is the transpose `N_A.dualMap` of
  `N_A` under the reflexivity `Dual (Dual A) ≅ A`).

From these, `P` descends (`QuotientAddGroup.lift`) to `Φ : U ⧸ U₀ →+ (V ⧸ V₀)^∨` and is
injective (first bullet), while the transposed map `Ψ : V ⧸ V₀ →+ (U ⧸ U₀)^∨` is injective
(second bullet).  The map `Ψ` is the `evalEquiv`-conjugate of `Φ.dualMap`; hence `Φ` injective and
`LinearMap.dualMap_surjective_of_injective` give that `Ψ` is surjective, hence bijective, hence
its transpose `Φ` is bijective as well (`LinearEquiv.dualMap`).  No finrank computation is needed.

IMPLEMENTATION.  The vocabulary (`normLin`, `augSub`, `fixSub`, `K`, `K0`, `V0` and the descended
pairing `pairQ`) together with the two `⊥`-computations `fixSub_eq_dualAnnihilator` /
`fixSub_dualCoannihilator` and `ker_dualAnnihilator_eq_range`, and the computation rule
`pairQ_mk`, is set up in `Submission.Work.SSGRoute.TateDual.Defs`, where the quotients
`↥K ⧸ K0` and `↥(fixSub) ⧸ V0` are *definitionally* `Work.Tate.Hm1 G A` and
`Work.Tate.H0 G (DualMod p A)`.  The pairing is non-degenerate in both variables
(`pairQ_mk` turns `pairQ (mk x) (mk φ) = 0` into `φ x = 0`, and the two annihilator computations
produce `x ∈ I_G·A`, resp. `φ ∈ N(A^∨)`); hence `pairQ` is a perfect pairing by
`LinearMap.IsPerfPair.of_injective` (finite dimensionality of `↥K ⧸ K0`), and
`pairQ.toPerfPair` is the desired additive isomorphism, composed with the identification of
`X →ₗ[𝔽_p] 𝔽_p` with `X →+ 𝔽_p` (`AddMonoidHom.toZModLinearMapEquiv`).
-/

theorem tateDuality_degree_zero (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] [FiniteDimensional (ZMod p) A] :
    Nonempty (Work.Tate.Hm1 G A ≃+
      (Work.Tate.H0 G (Work.SSGRoute.DualMod p A) →+ ZMod p)) := by
  -- The descended evaluation pairing is non-degenerate in both variables.
  have hker : ∀ z : ↥(K p G A) ⧸ K0 p G A, pairQ p G A z = 0 → z = 0 := by
    intro z hz
    revert hz
    refine Submodule.Quotient.induction_on (K0 p G A)
      (C := fun w => pairQ p G A w = 0 → w = 0) z ?_
    intro x hx0
    rw [Submodule.Quotient.mk_eq_zero]
    have hφ : ∀ φ : ↥(fixSub p G A), (φ : Work.SSGRoute.DualMod p A) x = 0 := by
      intro φ
      have h := congrArg (fun g => g (Submodule.Quotient.mk φ)) hx0
      simpa [pairQ_mk] using h
    have hxaug : (x : A) ∈ augSub p G A := by
      rw [← fixSub_dualCoannihilator]
      exact (Submodule.mem_dualAnnihilator (W := fixSub p G A) _).mpr
        (fun φ hφm => hφ ⟨φ, hφm⟩)
    exact hxaug
  have hinj : Function.Injective (pairQ p G A) := by
    intro y₁ y₂ h
    exact sub_eq_zero.mp (hker (y₁ - y₂) (by rw [map_sub, h, sub_self]))
  have hkerflip : ∀ z : ↥(fixSub p G A) ⧸ V0 p G A, (pairQ p G A).flip z = 0 → z = 0 := by
    intro z hz
    revert hz
    refine @Submodule.Quotient.induction_on (ZMod p) ↥(fixSub p G A) _ (Submodule.addCommGroup _)
      (fixSub p G A).module (V0 p G A) (fun w => (pairQ p G A).flip w = 0 → w = 0) z ?_
    intro φ hz0
    rw [Submodule.Quotient.mk_eq_zero]
    have hx : ∀ x : ↥(K p G A), (φ : Work.SSGRoute.DualMod p A) x = 0 := by
      intro x
      have h := congrArg (fun g => g (Submodule.Quotient.mk x)) hz0
      simpa [LinearMap.flip_apply, pairQ_mk] using h
    rw [mem_V0_iff_dualAnnihilator]
    exact (Submodule.mem_dualAnnihilator (W := K p G A) _).mpr (fun a ha => hx ⟨a, ha⟩)
  have hflip : Function.Injective (pairQ p G A).flip := by
    intro y₁ y₂ h
    exact sub_eq_zero.mp (hkerflip (y₁ - y₂) (by rw [map_sub, h, sub_self]))
  -- Hence the pairing is perfect, and identifies `Ĥ⁻¹(G, A)` with the dual of
  -- `Ĥ⁰(G, A^∨) = (A^∨)^G / N(A^∨)`.
  have hperf : (pairQ p G A).IsPerfPair := LinearMap.IsPerfPair.of_injective hinj hflip
  refine ⟨(pairQ p G A).toPerfPair.toAddEquiv.trans ?_⟩
  exact (AddMonoidHom.toZModLinearMapEquiv p (M := ↥(fixSub p G A) ⧸ V0 p G A)
    (M₁ := ZMod p)).symm

end Work.SSGRoute.TateDual
