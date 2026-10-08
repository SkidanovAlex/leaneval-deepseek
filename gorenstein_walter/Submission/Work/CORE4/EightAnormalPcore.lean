/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# Bender 1981, §4 (8): `A ⊴ O_p(U)`

For `U = O(Ĥ)`, `p` an odd prime with a subgroup `P ≤ F` of order `p`, and `A` the unique
subgroup of `F ⊔ K` of order `p²` and exponent `p` containing `P` (Bender's "subgroup of type
`(p,p)` of `F × K₁`"), the group `A` is normal in the `p`-core `O_p(U) = pCoreIn p B.U`.

## Route

Bender's §4 (8) (p. 226) derives `A ⊴ F(U)` — and hence `A ⊴ O_p(U)`, since `A ≤ O_p(U) ≤ F(U)` —
from the trichotomy on `Q := Ω₁(Z₂(O_p(U)))`:

* case 1: `A = Q`; case 2: `Z(Q) < A < Q` with `|Q : A| = p`; case 3: `s` inverts `Q`.

In cases 1–2, `A ≤ Q ≤ Z₂(O_p(U))` and `Q ⊴ O_p(U)`, so `[A, O_p(U)] ≤ [Q, O_p(U)] ≤ Z(Q) ≤ A`;
case 3 is exactly Bender's exceptional clause `I_U(s) ⊴ Ĥ` (`Case2InvNormal B h.D`), which is
*impossible* in the §4 configuration — `Work.CORE4.not_Case2InvNormal_of_ctx` (from §4 (7)
conjunct 1, `SevenO2HM`) refutes it.  Hence `O_p(U) ≤ N_G(A)`, i.e. `A ⊴ O_p(U)`.

Concretely the two delegated inputs are

* `Work.CORE4.EightQsubA` (`A ≤ Qsub p B` and `Z(Qsub p B) ≤ A`, the trichotomy cases 1–2), and
* `Work.CORE4.QsubCommutatorLeCenterIn` (`[Qsub p B, O_p(U)] ≤ Z(Qsub p B)`, a hypothesis-free
  `p`-group fact: for a `p`-group `P`, `Q = Ω₁(Z₂(P))` is normal in `P` and `[Q, P] ≤ Z(P)`),

and the elementary ingredients

* `Work.CORE4.not_Case2InvNormal_of_ctx` (the case-3 exclusion), and
* `pCoreIn_le_fittingIn_c4` below (`O_p(U) ≤ F(U)`), used only through `A ⊴ F(U)`;
  the trichotomy route above needs no `F(U)` at all.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.S0CentUO2
import Submission.Work.CORE4.EightAeqOmega
import Submission.Work.CORE4.EightQsubA
import Submission.Work.CORE4.QsubCommutatorLeCenterIn

namespace Work.CORE4

open Work.GW2 Subgroup
open scoped commutatorElement

/-- `O_p(K) ≤ F(K)`: every `p`-subgroup of the Fitting subgroup `F(K)` lies in its unique Sylow
`p`-subgroup, which is characteristic in `F(K) ⊴ K`, hence a normal `p`-subgroup of `K`; so
`O_p(F(K)) ≤ O_p(K)`.  Conversely `O_p(K) ≤ F(K)` because a normal `p`-subgroup is nilpotent. -/
theorem pCoreIn_le_fittingIn_c4 {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (K : Subgroup G) : Work.GW2.pCoreIn p K ≤ Work.GW2.fittingIn K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have key : Work.GW2.pCore p ↥K ≤ Work.GW2.fitting ↥K := by
    refine (Subgroup.normalCore_le (sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N})).trans ?_
    rw [sSup_le_iff]
    intro N hN
    haveI : N.Normal := hN.1
    exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hN.1, hN.2.isNilpotent⟩)
  exact Subgroup.map_mono key

theorem EightAnormalPcore (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
          Work.GW2.Case2EightObj h.D p P A →
          (A.subgroupOf (Work.GW2.pCoreIn p B.U)).Normal := by
  intro G _ _ hbc B h p P A hp hPF hPcard hObj
  -- Bender's case 3 (`s` inverts `Q`) is the exceptional clause, refuted by §4 (7)
  have hInv : ¬ Work.GW2.Case2InvNormal B h.D :=
    Work.CORE4.not_Case2InvNormal_of_ctx I hbc h
  -- trichotomy cases 1–2: `A ≤ Q` and `Z(Q) ≤ A`
  obtain ⟨hAleQ, hZleA⟩ :=
    Work.CORE4.EightQsubA I G hbc B h hInv p P A hp hPF hPcard hObj
  -- `[Q, O_p(U)] ≤ Z(Q)` is a hypothesis-free `p`-group fact
  have hQcomm : ⁅Work.CORE4.Qsub p B, Work.GW2.pCoreIn p B.U⁆ ≤
      Work.CORE4.centerIn (Work.CORE4.Qsub p B) :=
    Work.CORE4.QsubCommutatorLeCenterIn p B
  -- hence `[A, O_p(U)] ≤ [Q, O_p(U)] ≤ Z(Q) ≤ A`
  have hAcomm : ⁅A, Work.GW2.pCoreIn p B.U⁆ ≤ A :=
    (Subgroup.commutator_mono hAleQ le_rfl).trans (hQcomm.trans hZleA)
  -- `[A, O_p(U)] ≤ A` says exactly `O_p(U) ≤ N_G(A)`, i.e. `A ⊴ O_p(U)`
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr ?_
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · have hmem : ⁅y, x⁆ ∈ ⁅A, Work.GW2.pCoreIn p B.U⁆ :=
      Subgroup.commutator_mem_commutator hy.1 hx
    have hcA : ⁅y, x⁆⁻¹ ∈ A := A.inv_mem (hAcomm hmem)
    have hxy : x * y * x⁻¹ = ⁅y, x⁆⁻¹ * y := by
      rw [commutatorElement_inv, commutatorElement_def]
      group
    rw [hxy]
    exact A.mul_mem hcA hy.1
  · exact (Work.GW2.pCoreIn p B.U).mul_mem
      ((Work.GW2.pCoreIn p B.U).mul_mem hx hy.2) ((Work.GW2.pCoreIn p B.U).inv_mem hx)

end Work.CORE4
