import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7M_eq
import Submission.Work.CORE4.API
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.A7KBound.K_le_layerIn_and_inf_center
import Submission.Work.CORE4.A7MEq.A7MEq_interHM6
import Submission.Work.CORE4.fittingIn_eq_self_of_isPGroup
import Submission.Work.CORE4.M_eq_layerIn_sup_of_oneInvClass
import Submission.Work.CORE4.NotA7.A3U_M_eq_E_sup_F
import Submission.Work.CORE4.NotA7.A3U_F_subgroupOf_E_eq_center
import Submission.Work.CORE4.NotA7.A3U_card_le_of_ker_hom

namespace Work.CORE4.NotA7

open Subgroup

set_option linter.style.haveILetI false

/-- **The quotient `M / F` is `A₇`.**

Under the `A₇` hypotheses the kernel `F = C.D.F` is normal in `M = C.D.M` (`N_G(F) = M`),
`M = E(M) ⊔ F` (`A3U_M_eq_E_sup_F`) and `F ⊓ E(M) = Z(E(M))` (`A3U_F_subgroupOf_E_eq_center`),
so the surjection `E(M) → M/F` (an element of `E(M)` goes to its class modulo `F`) has kernel
`F ⊓ E(M) = Z(E(M))`; it is onto because `M = E(M)·F`.  Composing with the isomorphism
`E(M)/Z(E(M)) ≃* A₇` of `IsA7Case` produces a homomorphism `M →* A₇` with kernel exactly `F`.

This is the object the coset estimate of Bender §4, p. 226 uses: every subgroup of `M/F` is
isomorphic to a subgroup of `A₇`, and `A₇` has no odd-order subgroup of order `> 21`
(`A7ModelProp`, the last conjunct of `I.toolkit.a7`). -/
theorem A3U_ker_hom (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
    Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
    Work.GW2.A7Facts2 B C.D → IsPGroup 3 B.U → Work.GW2.oddCoreIn C.D.M = C.D.F →
    ∃ π : ↥C.D.M →* alternatingGroup (Fin 7), π.ker = C.D.F.subgroupOf C.D.M := by
  intro G _ _ B C hHyp hA7 hf1 hf2 hU3 hoddC
  obtain ⟨ha7iso⟩ := hA7
  have hEM : Work.GW2.layerIn C.D.M ≤ C.D.M := Work.CORE4.layerIn_le C.D.M
  have hFM : C.D.F ≤ C.D.M :=
    le_trans (Work.GW2.Case2Data.F_le_B0 B C.D)
      (le_trans (Work.GW2.Case2Data.B0_le B C.D) inf_le_right)
  have hNF : Subgroup.normalizer (C.D.F : Set G) = C.D.M := Work.GW2.Case2Pre.N_F B C.D C.pre
  have hFnormM : C.D.M ≤ Subgroup.normalizer (C.D.F : Set G) := le_of_eq hNF.symm
  haveI hFnorm_sub : (C.D.F.subgroupOf C.D.M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hFnormM
  have hEnormF : Work.GW2.layerIn C.D.M ≤ Subgroup.normalizer (C.D.F : Set G) := by
    rw [hNF]; exact hEM
  have hEnormM : C.D.M ≤ Subgroup.normalizer (Work.GW2.layerIn C.D.M : Set G) :=
    Work.CORE4.layerIn_le_normalizer C.D.M
  haveI hEnorm_sub : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hEnormM
  have hMEF : C.D.M = Work.GW2.layerIn C.D.M ⊔ C.D.F := A3U_M_eq_E_sup_F I G B C hHyp hf2 hU3
  have hZF : C.D.F.subgroupOf (Work.GW2.layerIn C.D.M)
      = Subgroup.center ↥(Work.GW2.layerIn C.D.M) :=
    A3U_F_subgroupOf_E_eq_center I G B C hHyp hf1 hf2 hoddC
  let φ : ↥(Work.GW2.layerIn C.D.M) →* (↥C.D.M ⧸ C.D.F.subgroupOf C.D.M) :=
    (QuotientGroup.mk' (C.D.F.subgroupOf C.D.M)).comp (Subgroup.inclusion hEM)
  have hφker : φ.ker = Subgroup.center ↥(Work.GW2.layerIn C.D.M) := by
    ext x
    rw [MonoidHom.mem_ker]
    dsimp only [φ, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    rw [← hZF]
    exact Subgroup.mem_subgroupOf.symm
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (C.D.F.subgroupOf C.D.M) y
    have htop : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) ⊔ (C.D.F.subgroupOf C.D.M) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hEM hFM, ← hMEF, Subgroup.subgroupOf_self]
    have hm : m ∈ ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) ⊔ (C.D.F.subgroupOf C.D.M) := by
      rw [htop]; exact Subgroup.mem_top m
    obtain ⟨e, he, f, hf, hef⟩ := Subgroup.mem_sup_of_normal_left.mp hm
    refine ⟨⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩, ?_⟩
    have hxe : (Subgroup.inclusion hEM ⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩ : ↥C.D.M) = e :=
      Subtype.ext (by rw [Subgroup.coe_inclusion])
    simp only [φ, MonoidHom.comp_apply, hxe]
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨f, hf, hef⟩
  have Φ : (↥(Work.GW2.layerIn C.D.M) ⧸ Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      ≃* (↥C.D.M ⧸ C.D.F.subgroupOf C.D.M) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  let Θ : (↥C.D.M ⧸ C.D.F.subgroupOf C.D.M) ≃* alternatingGroup (Fin 7) :=
    Φ.symm.trans ha7iso
  refine ⟨Θ.toMonoidHom.comp (QuotientGroup.mk' (C.D.F.subgroupOf C.D.M)), ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ Θ.injective, QuotientGroup.ker_mk']

/-- **C10.A3' part 4**: every odd-order subgroup `X ≤ M` satisfies
`|X| ≤ 21 · |X ⊓ F|` — the form of "`M/F ≅ A₇`" used by the coset estimate of Bender §4, p. 226.

Hypotheses: `Hyp9 G B C`, `IsA7Case C.D` (`E(M)/Z(E) ≅ A₇`), `A7Facts1`, `A7Facts2`
(`S ≤ E(M)`), `IsPGroup 3 B.U` (so `B₀ = F`) and `oddCoreIn C.D.M = C.D.F` (so `Z(E) ≤ F`).

Route.
* `E := layerIn C.D.M`.  From `oddCoreIn C.D.M = C.D.F`: `Z(E)` is a normal odd subgroup of `M`
  (`Odd |Z(E)|` is `Work.CORE4.LayerCtx6`, `E ⊴ M`), hence `Z(E) ≤ oddCoreIn M = F`.  With
  `F ≤ C(E)` (`Case2Pre.F_cent`) this gives `E ⊓ F = Z(E)`.
* `M = E ⊔ F`: `M = E ⊔ (M ⊓ C_G(t))` (`M_eq_layerIn_sup_of_oneInvClass`, using
  `Case2Pre.oneClass` and `D.t_mem`); `M ⊓ C_G(t) = (U ⊓ M) ⊔ S` (`A7MEq.A7MEq_interHM6`);
  `U ⊓ M = K ⊔ B₀ = K ⊔ F` (`Case2Pre.U_eq` and `B₀ = F`, which follows from the `3`-group `U`
  and `Work.CORE4.fittingIn_eq_self_of_isPGroup`); `K ≤ E` (`Case2PrePlus` conjunct 2,
  `Work.CORE4.K_le_layerIn`) and `S ≤ E` (`A7Facts2`).
* Hence `M/F ≅ E/(E ⊓ F) = E/Z(E) ≅ A₇`.
* For odd `X ≤ M`, the image of `X` in `M ⧸ F` is isomorphic to `X/(X ⊓ F)` and has odd order
  `(X ⊓ F).relIndex X ≤ 21`, since all odd-order subgroups of `A₇` have order at most `21`
  (`I.toolkit.a7`, last conjunct).  Finally `|X| = (X ⊓ F).relIndex X * |X ⊓ F|`
  (`Subgroup.relIndex_mul_card`). -/
theorem A3UBound (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
    Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
      Work.GW2.A7Facts2 B C.D → IsPGroup 3 B.U → Work.GW2.oddCoreIn C.D.M = C.D.F →
      ∀ X : Subgroup G, X ≤ C.D.M → Odd (Nat.card X) →
        Nat.card X ≤ 21 * Nat.card (X ⊓ C.D.F : Subgroup G) := by
  intro G _ _ B C hHyp hA7 hf1 hf2 hU3 hoddC X hXM hXodd
  obtain ⟨π, hker⟩ := A3U_ker_hom I G B C hHyp hA7 hf1 hf2 hU3 hoddC
  exact A3U_card_le_of_ker_hom π hker (fun Y hY => I.toolkit.a7.2.2.2 Y hY) X hXM hXodd

end Work.CORE4.NotA7
