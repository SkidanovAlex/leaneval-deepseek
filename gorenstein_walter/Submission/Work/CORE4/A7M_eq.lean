/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the `A₇` case of §4: `M = E(M)·(F·K)`, `U ∩ M = F·K`, `|U| = 27`

Bender 1981, p. 226 (the elimination of `E/Z(E) ≃ A₇`).  Write `E = E(M) = layerIn D.M`,
`H = C_G(t)`, `U = O(H)`, `F = B₀ ∩ F(U)`, `K = I_{U∩M}(s)`.  In the `A₇` case (`|K| = 3`,
`|F| = 3`, `B₀ = F`, `U` a `3`-group and `S ≤ E`) the three facts

    M = E ⊔ (F ⊔ K),   U ⊓ M = F ⊔ K,   |U| = 27

hold, and they are the object layer on which the rest of the `A₇` argument runs: the last
conjunct of `A7Facts3` (`K = Z(U)`) is derived from exactly these (`|U| = 27` with `U`
non-abelian forces `|Z(U)| = 3`).

The proof:
* `U ⊓ M = K ⊔ B₀` is §4 (5) (`Case2Pre`), and `B₀ = F` is the second conjunct of `A7Facts3`;
* `A7Facts5` gives `|U : U ⊓ M| = 3`, and `|U ⊓ M| = |F ⊔ K| = |F| · |K| = 9` (`A7UMCard`),
  so `|U| = 3 · 9 = 27` (`Subgroup.relIndex_mul_card`);
* `M = E ⊔ (M ⊓ H)` is Bender's §4 opening (`M_eq_layerIn_sup_of_oneInvClass`, using the one
  class of involutions in `E` and `t ∈ E`).  For `x ∈ M ⊓ H`, `H = U ⊔ S` (`A7Split`), so
  `x = u·s` with `u ∈ U`, `s ∈ S`; then `s ∈ S ≤ E ≤ M` gives `u = x·s⁻¹ ∈ M`, i.e.
  `u ∈ U ⊓ M = F ⊔ K`, and `x = u·s ∈ (F ⊔ K) ⊔ E = E ⊔ (F ⊔ K)`.
  Hence `M ≤ E ⊔ (F ⊔ K)`, and the reverse inclusion is `E, F, K ≤ M`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.M_eq_layerIn_sup_of_oneInvClass
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7UMCard
import Submission.Work.CORE4.A7MEq.A7MEq_interHM6

set_option maxHeartbeats 1000000

namespace Work.CORE4

open Subgroup

/-- **The `A₇` object layer of Bender §4, p. 226.**

Given the pass-9 budget `Hyp9`, `E(M)/Z(E) ≅ A₇`, `A7Facts1` (`|K| = |F| = 3`),
`A7Facts2` (`S` has order `8` and `S ≤ E(M)`), `A7Facts3` (`U` a `3`-group, `B₀ = F`) and
`A7Facts5` (`|U : U ∩ M| = 3`), we get

* `M = E(M) ⊔ (F ⊔ K)`,
* `U ⊓ M = F ⊔ K`,
* `|U| = 27`. -/
theorem A7M_eq (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.GW2.A7Facts3 B C.D → Work.GW2.A7Facts5 B C.D →
          C.D.M = Work.GW2.layerIn C.D.M ⊔ (C.D.F ⊔ C.D.K) ∧
            B.U ⊓ C.D.M = C.D.F ⊔ C.D.K ∧ Nat.card ↥B.U = 27 := by
  intro G _ _ B C hHyp _hA7 hf1 hf2 hf3 hf5
  obtain ⟨hbc, _hcase2, _hplus, _hseven, _height⟩ := hHyp
  obtain ⟨hKcard, hFcard, _hK0eq, _hpi⟩ := hf1
  obtain ⟨_hU3, hB0F, _hoddCoreF, _hKUZ, _hXbound⟩ := hf3
  -- `S` has order `8` and lies in `E(M) ≤ M` (`A7Facts2`)
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn C.D.M := hf2.2.2.1
  -- ## 1. `U ⊓ M = F ⊔ K`  (§4 (5) with `B₀ = F`)
  have hUM : B.U ⊓ C.D.M = C.D.F ⊔ C.D.K := by
    rw [Work.GW2.Case2Pre.U_eq B C.D C.pre, hB0F]
    exact sup_comm C.D.K C.D.F
  -- ## 2. `|U| = 27`
  have hFKcard : Nat.card ↥(C.D.F ⊔ C.D.K) = 9 := A7UMCard hB0F hKcard hFcard
  have hcardUM : Nat.card ↥(B.U ⊓ C.D.M) = 9 := by rw [hUM, hFKcard]
  have hcardU : Nat.card ↥B.U = 27 := by
    have h := Subgroup.relIndex_mul_card (B.U ⊓ C.D.M) B.U
    have hinf : (B.U ⊓ C.D.M) ⊓ B.U = B.U ⊓ C.D.M := inf_eq_left.mpr inf_le_left
    rw [hinf, hf5.2.1, hcardUM] at h
    omega
  -- ## 3. `M ⊓ H ≤ E ⊔ (F ⊔ K)`: `M ⊓ H = (U ⊓ M)·S` (`A7MEq_interHM6`) and `S ≤ E`
  have hMH : C.D.M ⊓ B.H ≤ Work.GW2.layerIn C.D.M ⊔ (C.D.F ⊔ C.D.K) := by
    rw [Work.CORE4.A7MEq.A7MEq_interHM6 I G B C hbc hf2, hUM]
    exact sup_le le_sup_right (le_trans hSE le_sup_left)
  -- ## 4. `M = E ⊔ (F ⊔ K)`
  have hM : C.D.M = Work.GW2.layerIn C.D.M ⊔ (C.D.F ⊔ C.D.K) := by
    have h1 : C.D.M = Work.GW2.layerIn C.D.M ⊔ (C.D.M ⊓ B.H) :=
      M_eq_layerIn_sup_of_oneInvClass C.D.M C.pre.2.1 C.D.t_mem
    refine le_antisymm (h1.le.trans (sup_le le_sup_left hMH)) ?_
    refine sup_le (layerIn_le C.D.M)
      (sup_le ?_ (Work.GW2.Case2Data.K_le_M B C.D))
    exact le_trans (Work.GW2.Case2Data.F_le_B0 B C.D)
      (le_trans (Work.GW2.Case2Data.B0_le B C.D) inf_le_right)
  exact ⟨hM, hUM, hcardU⟩

end Work.CORE4
