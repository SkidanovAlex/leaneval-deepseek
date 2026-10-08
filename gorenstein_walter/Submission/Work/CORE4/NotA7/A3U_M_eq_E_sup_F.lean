import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.A7MEq.A7MEq_interHM6
import Submission.Work.CORE4.M_eq_layerIn_sup_of_oneInvClass
import Submission.Work.CORE4.fittingIn_eq_self_of_isPGroup
import Submission.Work.CORE4.A7KBound.K_le_layerIn_and_inf_center
import Submission.Work.CORE4.LayerCtx6

namespace Work.CORE4.NotA7

open Subgroup

/-- **`M = E(M) · F` in the `A₇`-case of Bender §4, once `U = O(H)` is a `3`-group.**

With `E = E(M) = layerIn D.M`, `F = B₀ ∩ F(U)` and `IsPGroup 3 B.U`:

* `F(U) = U` (a `3`-group is nilpotent), and `B₀ ≤ U`, so `F = B₀`;
* `M = E ⊔ (M ⊓ H)` (`M_eq_layerIn_sup_of_oneInvClass`, using `OneInvClassIn E` and `t ∈ E`,
  both from `Case2Pre`);
* `M ⊓ H = (U ⊓ M) ⊔ S` (`A7MEq_interHM6`, from `BenderCtx` and `A7Facts2`);
* `U ⊓ M = K ⊔ B₀` (`Case2Pre`), and `K ≤ E` (`K_le_layerIn_and_inf_center`, needing only
  `Case2PrePlus` and the oddness of `|U|`, which follows from `IsPGroup 3 B.U`), while
  `S ≤ E` is the third conjunct of `A7Facts2`.

Hence `M = E ⊔ (K ⊔ F ⊔ S) = E ⊔ F`. -/
theorem A3U_M_eq_E_sup_F (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
    Work.GW2.Hyp9 G B C → Work.GW2.A7Facts2 B C.D → IsPGroup 3 B.U →
      C.D.M = Work.GW2.layerIn C.D.M ⊔ C.D.F := by
  intro G _ _ B C h9 h2 hU
  -- unwind the hypothesis budget
  obtain ⟨hbc, _hc2, hplus, _hseven, _height⟩ := h9
  obtain ⟨_hHleM, hone, _hKcyc, hUeq, _hFne, _hFcent, _hNF, _hB0def⟩ := C.pre
  -- `F(U) = U` because `U` is a `3`-group, and `B₀ ≤ U`, so `F = B₀`
  have hfit : Work.GW2.fittingIn B.U = B.U :=
    Work.CORE4.fittingIn_eq_self_of_isPGroup hU
  have hB0U : C.D.B0 ≤ B.U := by
    rw [C.D.B0_def]
    exact inf_le_left.trans inf_le_left
  have hF : C.D.F = C.D.B0 := by
    rw [C.D.F_def, hfit, inf_eq_left.mpr hB0U]
  -- `|U|` is odd (a power of `3`), so `K ≤ E(M)`
  have hUodd : Odd (Nat.card ↥B.U) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).mp hU
    rw [hn]
    exact Odd.pow (by norm_num : Odd 3)
  have hKE : C.D.K ≤ Work.GW2.layerIn C.D.M :=
    (Work.CORE4.A7KBound.K_le_layerIn_and_inf_center hplus hUodd).1
  -- `S ≤ E(M)` is the third conjunct of `A7Facts2`
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn C.D.M := h2.2.2.1
  -- `M = E ⊔ (M ⊓ H)` (one class of involutions in `E`, `t ∈ E`)
  have hME : C.D.M = Work.GW2.layerIn C.D.M ⊔ (C.D.M ⊓ B.H) :=
    Work.CORE4.M_eq_layerIn_sup_of_oneInvClass C.D.M hone C.D.t_mem
  -- `M ⊓ H = (U ⊓ M) ⊔ S`
  have hint : C.D.M ⊓ B.H = (B.U ⊓ C.D.M) ⊔ (B.S : Subgroup G) :=
    Work.CORE4.A7MEq.A7MEq_interHM6 I G B C hbc h2
  -- the final lattice computation: `E ⊔ ((K ⊔ F) ⊔ S) = E ⊔ F`
  have hgoal : Work.GW2.layerIn C.D.M ⊔ ((C.D.K ⊔ C.D.F) ⊔ (B.S : Subgroup G))
      = Work.GW2.layerIn C.D.M ⊔ C.D.F := by
    refine le_antisymm ?_ ?_
    · refine sup_le le_sup_left ?_
      refine sup_le ?_ ?_
      · exact sup_le (le_trans hKE le_sup_left) le_sup_right
      · exact le_trans hSE le_sup_left
    · refine sup_le le_sup_left ?_
      have h2' : C.D.F ≤ C.D.K ⊔ C.D.F := le_sup_right
      have h3' : C.D.F ≤ (C.D.K ⊔ C.D.F) ⊔ (B.S : Subgroup G) := le_sup_of_le_left h2'
      exact le_sup_of_le_right h3'
  calc C.D.M = Work.GW2.layerIn C.D.M ⊔ (C.D.M ⊓ B.H) := hME
    _ = Work.GW2.layerIn C.D.M ⊔ ((B.U ⊓ C.D.M) ⊔ (B.S : Subgroup G)) := by rw [hint]
    _ = Work.GW2.layerIn C.D.M ⊔ ((C.D.K ⊔ C.D.B0) ⊔ (B.S : Subgroup G)) := by rw [hUeq]
    _ = Work.GW2.layerIn C.D.M ⊔ ((C.D.K ⊔ C.D.F) ⊔ (B.S : Subgroup G)) := by rw [← hF]
    _ = Work.GW2.layerIn C.D.M ⊔ C.D.F := hgoal

end Work.CORE4.NotA7
