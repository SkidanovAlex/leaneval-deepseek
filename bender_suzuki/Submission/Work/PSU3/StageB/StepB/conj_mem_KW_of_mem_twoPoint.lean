import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.StepB.W_normal_twoPoint
import Submission.Work.PSU3.StageA.Ksub_eq_Kset_cyclic_normal_of_W_ne_bot
import Submission.Work.PSU3.StageB.StepB.exists_generating_frame

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.StepB

/-
# `Work.PSU3.StageB.StepB.conj_mem_KW_of_mem_twoPoint`

The complement `KW` carried by a `CoarseFrame` is normalised by the two-point stabiliser
`D = twoPoint H t`, *provided* `ζ` generates `W = C_V(K)` (the hypothesis `hgen`).

The two structural inputs are the frame axiom `KW_gen` ("every element of `KW` is
`k · ζ^j`, `k ∈ Ksub`") and the two normality statements for `D`:

* `Ksub H t ⊴ D` — Peterfalvi II Ch. V §1 Prop. 2, available in the workspace as
  `Work.PSU3.StageA.Ksub_eq_Kset_cyclic_normal_of_W_ne_bot` (case `W ≠ 1`), with
  `W ≠ 1` supplied by the frame's `ζ`;
* `W ⊴ D` — Peterfalvi II Ch. II §4 Prop. 4, available as
  `Work.PSU3.StageB.StepB.W_normal_twoPoint`.

Since `hgen : o(ζ) = |W|` together with `ζ ∈ W` forces `⟨ζ⟩ = W` (a finite subgroup
contained in `W` with the same cardinality), the frame axiom gives
`KW = Ksub · ⟨ζ⟩ = Ksub · W`, and the two normalities give the result.
-/

theorem conj_mem_KW_of_mem_twoPoint {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (fr : Work.PSU3.CoarseFrame H Q t n)
    (hgen : orderOf (fr.ζ : G) = Nat.card ↥(Work.ThmF.W H t)) :
    ∀ d : ↥(Submission.Blueprint.twoPoint H t), ∀ w : fr.KW,
      (d : G)⁻¹ * (w : G) * (d : G) ∈ fr.KW := by
  classical
  -- `W ≠ ⊥`, since the frame carries the nontrivial element `ζ ∈ W`.
  have hWne : Work.ThmF.W H t ≠ ⊥ := by
    intro hbot
    have hmem : (fr.ζ : G) ∈ (⊥ : Subgroup G) := hbot ▸ fr.ζ_mem_W
    exact fr.ζ_ne_one (Subtype.ext (Subgroup.mem_bot.mp hmem))
  -- `K̄ = ⟨K⟩` is normal in `D` (Peterfalvi II, Ch. V §1 Prop. 2, case `W ≠ 1`).
  obtain ⟨-, -, hKnorm⟩ :=
    Work.PSU3.StageA.Ksub_eq_Kset_cyclic_normal_of_W_ne_bot hS hC4 hWne
  -- `W` is normal in `D` (Peterfalvi II, Ch. II §4 Prop. 4).
  have hWnorm : ((Work.ThmF.W H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal :=
    Work.PSU3.StageB.StepB.W_normal_twoPoint hS hC4
  have hKsub_le : Work.ThmF.Ksub H t ≤ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.Ksub_le_twoPoint t
  have hW_le : Work.ThmF.W H t ≤ Submission.Blueprint.twoPoint H t :=
    le_trans (Work.ThmF.W_le_centD H t) (Work.ThmF.centD_le_twoPoint (H := H) t)
  -- `hgen` says exactly that `ζ` generates `W`.
  have hzp_eq_W : Subgroup.zpowers (fr.ζ : G) = Work.ThmF.W H t := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr fr.ζ_mem_W) ?_
    rw [Nat.card_zpowers, hgen]
  have hW_le_KW : Work.ThmF.W H t ≤ fr.KW := by
    rw [← hzp_eq_W]
    exact Subgroup.zpowers_le.mpr fr.ζ.2
  intro d w
  -- every element of `KW` is `k · ζ^j` with `k ∈ K̄`.
  obtain ⟨k, hkK, j, hw⟩ := fr.KW_gen w
  have hdD : (d : G) ∈ Submission.Blueprint.twoPoint H t := d.2
  have hdiD : (d : G)⁻¹ ∈ Submission.Blueprint.twoPoint H t :=
    (Submission.Blueprint.twoPoint H t).inv_mem hdD
  -- `d⁻¹ k d ∈ K̄`
  have hkconj : (d : G)⁻¹ * (k : G) * (d : G) ∈ Work.ThmF.Ksub H t := by
    have h := (Subgroup.normal_subgroupOf_iff hKsub_le).mp hKnorm (k : G) (d : G)⁻¹ hkK hdiD
    simpa using h
  -- `d⁻¹ ζ d ∈ W`
  have hzconj : (d : G)⁻¹ * (fr.ζ : G) * (d : G) ∈ Work.ThmF.W H t := by
    have h := (Subgroup.normal_subgroupOf_iff hW_le).mp hWnorm (fr.ζ : G) (d : G)⁻¹ fr.ζ_mem_W hdiD
    simpa using h
  -- and hence `d⁻¹ ζ^j d ∈ W`
  have hzpowconj : (d : G)⁻¹ * (fr.ζ : G) ^ j * (d : G) ∈ Work.ThmF.W H t := by
    have h2 : (d : G)⁻¹ * (fr.ζ : G) ^ j * (d : G)
        = ((d : G)⁻¹ * (fr.ζ : G) * (d : G)) ^ j := by
      calc (d : G)⁻¹ * (fr.ζ : G) ^ j * (d : G)
          = (MulAut.conj (d : G)⁻¹) ((fr.ζ : G) ^ j) := by
            rw [MulAut.conj_apply, inv_inv]
        _ = ((MulAut.conj (d : G)⁻¹) (fr.ζ : G)) ^ j := map_pow _ _ _
        _ = ((d : G)⁻¹ * (fr.ζ : G) * (d : G)) ^ j := by
            rw [MulAut.conj_apply, inv_inv]
    rw [h2]
    exact (Work.ThmF.W H t).pow_mem hzconj j
  have hwcoe : (w : G) = (k : G) * (fr.ζ : G) ^ j := by
    have h := congrArg (fun z : fr.KW => (z : G)) hw
    simpa [Subgroup.coe_mul, Subgroup.coe_pow] using h
  rw [hwcoe]
  have hgroup : (d : G)⁻¹ * ((k : G) * (fr.ζ : G) ^ j) * (d : G) =
      ((d : G)⁻¹ * (k : G) * (d : G)) * ((d : G)⁻¹ * (fr.ζ : G) ^ j * (d : G)) := by
    group
  rw [hgroup]
  exact fr.KW.mul_mem (fr.K_le hkconj) (hW_le_KW hzpowconj)

end Work.PSU3.StageB.StepB
