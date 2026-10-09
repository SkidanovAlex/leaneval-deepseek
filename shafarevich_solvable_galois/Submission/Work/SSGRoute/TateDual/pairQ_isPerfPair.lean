import Mathlib
import Submission.Work.SSGRoute.TateDual.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.TateDual

/-- **Non-degeneracy of the degree-`0` Tate pairing.**

The evaluation pairing `pairQ : Ĥ⁻¹(G, A) × Ĥ⁰(G, A^∨) → 𝔽_p` of
`Submission.Work.SSGRoute.TateDual.Defs` is perfect in both variables.  (This is the `hperf`
used inside the proof of `Work.SSGRoute.TateDual.tateDuality_degree_zero`, extracted as a
standalone statement; the same proof works: the left kernel of `pairQ` is `I_G·A`
(`fixSub_dualCoannihilator`), the right kernel is `N_{A^∨}(A^∨)`
(`ker_dualAnnihilator_eq_range` / `mem_V0_iff_dualAnnihilator`), via `pairQ_mk`, ending with
`LinearMap.IsPerfPair.of_injective`.) -/
theorem pairQ_isPerfPair (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (A : Type) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
    [SMulCommClass G (ZMod p) A] [FiniteDimensional (ZMod p) A] :
    (Work.SSGRoute.TateDual.pairQ p G A).IsPerfPair := by
  -- The left kernel of `pairQ` is `K0 = I_G·A`.
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
  -- The right kernel of `pairQ` is `V0 = N_{A^∨}(A^∨)`.
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
  exact LinearMap.IsPerfPair.of_injective hinj hflip

end Work.SSGRoute.TateDual
