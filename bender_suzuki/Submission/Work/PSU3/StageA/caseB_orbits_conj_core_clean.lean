import Mathlib
import Submission.Work.PSU3.StageA.GoodRepsDef
import Submission.Work.PSU3.StageA.caseB_canon_data_rrk
import Submission.Work.PSU3.StageA.caseB_Ksub_action_coords
import Submission.Work.PSU3.StageA.Ksub_cyclic_caseB
import Submission.Work.PSU3.StageA.false_of_commuting_involutions
import Submission.Work.PSU3.StageA.caseB_GoodReps_mem_Q0sub_iff
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.PSU3.StageA.caseC_W_semireg
import Submission.Work.PSU3.StageA.caseB_field_algebra
import Submission.Work.Higman.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `Kset H t` acts freely on `Q#` (Ch. V §2, `Work.ThmF.ChV12.prop1a`). -/
theorem Kset_free_on_Q_K {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {k : G} (hk : k ∈ Work.ThmF.Kset H t)
    (hk1 : k ≠ 1) {x : G} (hx : x ∈ Q) (hconj : k⁻¹ * x * k = x) : x = 1 := by
  refine Work.ThmF.ChV12.prop1a hS.situation hC4 H Q t hS.split k hk hk1 x hx ?_
  have h := congrArg (fun z : G => k * z) hconj
  simpa [mul_assoc] using h

/-- The element of `↥(Ksub H t)` underlying a member of `Kset H t` (via the identification
`hKsub` of the two sets). -/
def mkK_K (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) {k : G}
    (hk : k ∈ Work.ThmF.Kset H t) : ↥(Work.ThmF.Ksub H t) := ⟨k, Work.ThmF.Kset_le_Ksub H t hk⟩

@[simp] lemma mkK_coe_K (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) {k : G}
    (hk : k ∈ Work.ThmF.Kset H t) : ((mkK_K hKsub hk) : G) = k := rfl

/-- `s * k * s * k⁻¹` is an involution of `H`, for `1 ≠ k ∈ Kset H t`. -/
theorem caseB_sksk_mem_involutions_K {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) {k : G} (hk : k ∈ Work.ThmF.Kset H t) (hkne : k ≠ 1) :
    s * k * s * k⁻¹ ∈ involutions (H : Set G) := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  have hQ0 := Q0sub_structure hS hC4
  have hs_mem : s ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hsplit.le hs, hs2⟩))
  have hs_sq : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hkH : k ∈ H :=
    Work.RankOneUniqueness.twoPoint_le_left H t (Work.ThmF.Kset_subset H t hk)
  have hksk : k * s * k⁻¹ ∈ Work.ThmF.Q0sub H := hQ0.2.2.1 k hkH s hs_mem
  have hprod : s * k * s * k⁻¹ ∈ Work.ThmF.Q0sub H := by
    have h := (Work.ThmF.Q0sub H).mul_mem hs_mem hksk
    rwa [show s * (k * s * k⁻¹) = s * k * s * k⁻¹ from by group] at h
  have hne1 : s * k * s * k⁻¹ ≠ 1 := by
    intro hcon
    have h1 : k * s * k⁻¹ = s := by
      have h2 := congrArg (fun z : G => s * z) hcon
      rw [mul_one] at h2
      have h3 : s * (s * k * s * k⁻¹) = k * s * k⁻¹ := by
        rw [show s * (s * k * s * k⁻¹) = (s * s) * (k * s * k⁻¹) from by group, hs_sq, one_mul]
      rwa [h3] at h2
    have h4 : k⁻¹ * s * k = s := by
      have h5 := congrArg (fun z : G => k⁻¹ * z * k) h1
      have h6 : k⁻¹ * (k * s * k⁻¹) * k = s := by group
      rw [h6] at h5
      exact h5.symm
    have h6 := Kset_free_on_Q_K hS hC4 hk hkne hs h4
    rw [h6, orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  exact hQ0.2.2.2 (s * k * s * k⁻¹) hprod hne1

/-- There is `w ∈ Kset H t` with `w s w⁻¹ = s k s k⁻¹`. -/
theorem caseB_exists_w_K {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) {k : G} (hk : k ∈ Work.ThmF.Kset H t) (hkne : k ≠ 1) :
    ∃ w ∈ Work.ThmF.Kset H t, w * s * w⁻¹ = s * k * s * k⁻¹ := by
  have hsplit : IsSplitRankOne H Q t := hS.split
  exact Kset_transitive_involutions hsplit.stronglyEmbedded hsplit.invol hsplit.not_mem
    s ⟨hsplit.le hs, hs2⟩ (s * k * s * k⁻¹)
    (caseB_sksk_mem_involutions_K hS hC4 hs hs2 hk hkne)

/-- **`K`-equivariance of the canonical data, in `α`-form.** -/
theorem alpha_canon_conj_K {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    {F : Type} [Field F] {α : ↥Q → F} {κ : ↥(Work.ThmF.Ksub H t) ≃* Fˣ}
    (hαact : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x y : ↥Q),
      (y : G) = (k : G)⁻¹ * (x : G) * (k : G) → α y = (κ k : F) * α x)
    (b : ↥(Work.ThmF.Ksub H t)) {x y : ↥Q} (hx : (x : G) ≠ 1)
    (hy : (y : G) = (b : G)⁻¹ * (x : G) * (b : G)) :
    α y = (κ b : F) * α x ∧
    α (Work.PSU3.StageB.gcan hsplit y)
      = ((κ b : Fˣ) : F)⁻¹ * α (Work.PSU3.StageB.gcan hsplit x) ∧
    α (Work.PSU3.StageB.fcan hsplit y)
      = ((κ b : Fˣ) : F)⁻¹ * α (Work.PSU3.StageB.fcan hsplit x) ∧
    (Work.PSU3.StageB.hcan hsplit y : G)
      = (b : G) * (Work.PSU3.StageB.hcan hsplit x : G) * (b : G) := by
  have hbKset : (b : G) ∈ Work.ThmF.Kset H t := hKsub ▸ b.2
  have hbD : (b : G) ∈ twoPoint H t := Work.ThmF.Kset_subset H t hbKset
  have hbt : t * (b : G) * t = (b : G)⁻¹ := by
    have h := (Work.ThmF.mem_Kset_iff.mp hbKset).2
    rwa [Work.RankOneUniqueness.inv_eq_self hsplit] at h
  have hbtinv : (t * (b : G) * t)⁻¹ = (b : G) := by rw [hbt, inv_inv]
  obtain ⟨xa, hxa, hfn, hgn, hhn⟩ :=
    Work.PSU3.StageB.canon_conj_fun hsplit hx ⟨(b : G), hbD⟩
  have hxa_eq : xa = y := Subtype.ext (hxa.trans hy.symm)
  have hf' : (Work.PSU3.StageB.fcan hsplit xa : G)
      = (b : G) * (Work.PSU3.StageB.fcan hsplit x : G) * (b : G)⁻¹ := by
    rw [hfn, hbtinv, hbt]
  have hg' : (Work.PSU3.StageB.gcan hsplit xa : G)
      = (b : G) * (Work.PSU3.StageB.gcan hsplit x : G) * (b : G)⁻¹ := by
    rw [hgn, hbtinv, hbt]
  have hh' : (Work.PSU3.StageB.hcan hsplit xa : G)
      = (b : G) * (Work.PSU3.StageB.hcan hsplit x : G) * (b : G) := by
    rw [hhn, hbtinv]
  have hbF : ((κ b : Fˣ) : F)⁻¹ = (κ b⁻¹ : F) := by
    rw [map_inv]
    exact (Units.val_inv_eq_inv_val (κ b)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hxa_eq]; exact hαact b x xa hxa
  · have hbx : (Work.PSU3.StageB.gcan hsplit xa : G)
        = (b⁻¹ : G)⁻¹ * (Work.PSU3.StageB.gcan hsplit x : G) * (b⁻¹ : G) := by
      rw [hg']
      simp only [Subgroup.coe_inv, inv_inv]
    have h := hαact b⁻¹ (Work.PSU3.StageB.gcan hsplit x) (Work.PSU3.StageB.gcan hsplit xa) hbx
    rw [← hxa_eq, h, hbF]
  · have hbx : (Work.PSU3.StageB.fcan hsplit xa : G)
        = (b⁻¹ : G)⁻¹ * (Work.PSU3.StageB.fcan hsplit x : G) * (b⁻¹ : G) := by
      rw [hf']
      simp only [Subgroup.coe_inv, inv_inv]
    have h := hαact b⁻¹ (Work.PSU3.StageB.fcan hsplit x) (Work.PSU3.StageB.fcan hsplit xa) hbx
    rw [← hxa_eq, h, hbF]
  · rw [← hxa_eq]; exact hh'

/-- **The `α`-values of the canonical data of `r r^{-k}`** (Peterfalvi II Ch. VI §2, (4)):
with `w ∈ Kset H t` satisfying `w s w⁻¹ = s k s k⁻¹`, `α(rr^{-k}) = α r - κ k · α r⁻¹`,
`α(g(rr^{-k})) = α r - κ w · α r⁻¹` and `α(f(rr^{-k}))` the corresponding expression. -/
theorem alpha_data_rrk_K {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hsplit : IsSplitRankOne H Q t)
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    {F : Type} [Field F] {α : ↥Q → F} {κ : ↥(Work.ThmF.Ksub H t) ≃* Fˣ}
    (hαadd : ∀ x y : ↥Q, α (x * y) = α x + α y)
    (hαact : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x y : ↥Q),
      (y : G) = (k : G)⁻¹ * (x : G) * (k : G) → α y = (κ k : F) * α x)
    {k w : G} (hk : k ∈ Work.ThmF.Kset H t) (hkne : k ≠ 1) (hw : w ∈ Work.ThmF.Kset H t)
    (hws : w * s * w⁻¹ = s * k * s * k⁻¹)
    (x : ↥Q) (hx : (x : G) = r * (k⁻¹ * r⁻¹ * k)) (hx1 : (x : G) ≠ 1) :
    α x = α (⟨r, hr⟩ : ↥Q) + (κ (mkK_K hKsub hk) : F) * α (⟨r⁻¹, Q.inv_mem hr⟩ : ↥Q) ∧
    α (Work.PSU3.StageB.gcan hsplit x)
      = α (⟨r, hr⟩ : ↥Q)
        + (κ (mkK_K hKsub hw) : F) * α (⟨r⁻¹, Q.inv_mem hr⟩ : ↥Q) ∧
    α (Work.PSU3.StageB.fcan hsplit x)
      = (κ (mkK_K hKsub hk) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw) : F) * α (⟨r, hr⟩ : ↥Q)
        + (κ (mkK_K hKsub hk) : F)⁻¹ * α (⟨r⁻¹, Q.inv_mem hr⟩ : ↥Q) := by
  have hkH : k ∈ H :=
    Work.RankOneUniqueness.twoPoint_le_left H t (Work.ThmF.Kset_subset H t hk)
  have hwH : w ∈ H :=
    Work.RankOneUniqueness.twoPoint_le_left H t (Work.ThmF.Kset_subset H t hw)
  have hrinvQ : r⁻¹ ∈ Q := Q.inv_mem hr
  have hw1rw : w⁻¹ * r * w ∈ Q := by
    simpa only [inv_inv] using
      Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := w⁻¹) (H.inv_mem hwH) hr
  have hw1rinvw : w⁻¹ * r⁻¹ * w ∈ Q := by
    simpa only [inv_inv] using
      Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := w⁻¹) (H.inv_mem hwH) hrinvQ
  have hk1rinvk : k⁻¹ * r⁻¹ * k ∈ Q := by
    simpa only [inv_inv] using
      Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := k⁻¹) (H.inv_mem hkH) hrinvQ
  have hYQ : k * (w⁻¹ * r * w) * k⁻¹ ∈ Q :=
    Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := k) hkH hw1rw
  have hP1 : k * k * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹) ∈ Q := by
    have h := Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := k) hkH hYQ
    simpa only [mul_assoc] using h
  have hA2 : k * r⁻¹ * k⁻¹ ∈ Q :=
    Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := k) hkH hrinvQ
  -- `α` of the inverse of `r`
  have hαone : α (1 : ↥Q) = 0 := by
    have h2 := hαadd (1 : ↥Q) (1 : ↥Q)
    rw [mul_one] at h2
    exact add_left_cancel (show α (1 : ↥Q) + α (1 : ↥Q) = α (1 : ↥Q) + 0 by
      rw [add_zero]; exact h2.symm)
  have hαrinv : α (⟨r⁻¹, hrinvQ⟩ : ↥Q) = - α (⟨r, hr⟩ : ↥Q) := by
    have h := hαadd (⟨r, hr⟩ : ↥Q) (⟨r⁻¹, hrinvQ⟩ : ↥Q)
    have hmul : (⟨r, hr⟩ : ↥Q) * (⟨r⁻¹, hrinvQ⟩ : ↥Q) = 1 := Subtype.ext (by simp)
    rw [hmul, hαone] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  -- the derived conjugation rule `α (u x u⁻¹) = (κ u)⁻¹ α x`
  have hαconj' : ∀ (u : ↥(Work.ThmF.Ksub H t)) (y z : ↥Q),
      (z : G) = (u : G) * (y : G) * (u : G)⁻¹ → α z = ((κ u : Fˣ) : F)⁻¹ * α y := by
    intro u y z hz
    have h := hαact u⁻¹ y z (by rw [hz]; simp only [Subgroup.coe_inv, inv_inv])
    rw [h, map_inv, Units.val_inv_eq_inv_val]
  -- canonical data
  obtain ⟨hg, hd, hy, heq⟩ := caseB_canon_data_rrk hS hC4 hs hs2 hr hsr hKsub k hk hkne w hw hws
  obtain ⟨hc1, hc2⟩ := Work.PSU3.StageB.canon_unique'' hsplit hx1
    (g := (⟨r * (w⁻¹ * r⁻¹ * w), hg⟩ : ↥Q))
    (d := (⟨(w⁻¹ * w⁻¹) * (k * k), hd⟩ : ↥(twoPoint H t)))
    (y := (⟨((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹), hy⟩ : ↥Q))
    (by rw [hx]; exact heq)
  have hgx : (Work.PSU3.StageB.gcan hsplit x : G) = r * (w⁻¹ * r⁻¹ * w) := hc1.symm
  have hfx : (Work.PSU3.StageB.fcan hsplit x : G)
      = ((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹) := hc2.2.symm
  have hαw1rw : α (⟨w⁻¹ * r * w, hw1rw⟩ : ↥Q)
      = (κ (mkK_K hKsub hw) : F) * α (⟨r, hr⟩ : ↥Q) :=
    hαact (mkK_K hKsub hw) (⟨r, hr⟩ : ↥Q) (⟨w⁻¹ * r * w, hw1rw⟩ : ↥Q)
      (by simp [mkK_coe_K])
  have hαw1rinvw : α (⟨w⁻¹ * r⁻¹ * w, hw1rinvw⟩ : ↥Q)
      = (κ (mkK_K hKsub hw) : F) * α (⟨r⁻¹, hrinvQ⟩ : ↥Q) :=
    hαact (mkK_K hKsub hw) (⟨r⁻¹, hrinvQ⟩ : ↥Q) (⟨w⁻¹ * r⁻¹ * w, hw1rinvw⟩ : ↥Q)
      (by simp [mkK_coe_K])
  have hαk1rinvk : α (⟨k⁻¹ * r⁻¹ * k, hk1rinvk⟩ : ↥Q)
      = (κ (mkK_K hKsub hk) : F) * α (⟨r⁻¹, hrinvQ⟩ : ↥Q) :=
    hαact (mkK_K hKsub hk) (⟨r⁻¹, hrinvQ⟩ : ↥Q) (⟨k⁻¹ * r⁻¹ * k, hk1rinvk⟩ : ↥Q)
      (by simp [mkK_coe_K])
  have hαA2 : α (⟨k * r⁻¹ * k⁻¹, hA2⟩ : ↥Q)
      = (κ (mkK_K hKsub hk) : F)⁻¹ * α (⟨r⁻¹, hrinvQ⟩ : ↥Q) :=
    hαconj' (mkK_K hKsub hk) (⟨r⁻¹, hrinvQ⟩ : ↥Q) (⟨k * r⁻¹ * k⁻¹, hA2⟩ : ↥Q)
      (by simp [mkK_coe_K])
  have hαY : α (⟨k * (w⁻¹ * r * w) * k⁻¹, hYQ⟩ : ↥Q)
      = (κ (mkK_K hKsub hk) : F)⁻¹ * ((κ (mkK_K hKsub hw) : F) * α (⟨r, hr⟩ : ↥Q)) := by
    rw [hαconj' (mkK_K hKsub hk) (⟨w⁻¹ * r * w, hw1rw⟩ : ↥Q)
      (⟨k * (w⁻¹ * r * w) * k⁻¹, hYQ⟩ : ↥Q) (by simp [mkK_coe_K]), hαw1rw]
  have hαP1 : α (⟨k * k * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹), hP1⟩ : ↥Q)
      = (κ (mkK_K hKsub hk) : F)⁻¹
        * ((κ (mkK_K hKsub hk) : F)⁻¹ * ((κ (mkK_K hKsub hw) : F) * α (⟨r, hr⟩ : ↥Q))) := by
    rw [hαconj' (mkK_K hKsub hk) (⟨k * (w⁻¹ * r * w) * k⁻¹, hYQ⟩ : ↥Q)
      (⟨k * k * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹), hP1⟩ : ↥Q) (by
        simp only [mkK_coe_K]
        group), hαY]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : x = (⟨r, hr⟩ : ↥Q) * (⟨k⁻¹ * r⁻¹ * k, hk1rinvk⟩ : ↥Q) :=
      Subtype.ext (by rw [hx]; rfl)
    rw [h1, hαadd, hαk1rinvk]
  · have h1 : Work.PSU3.StageB.gcan hsplit x
        = (⟨r, hr⟩ : ↥Q) * (⟨w⁻¹ * r⁻¹ * w, hw1rinvw⟩ : ↥Q) :=
      Subtype.ext (by rw [hgx]; rfl)
    rw [h1, hαadd, hαw1rinvw]
  · have h1 : Work.PSU3.StageB.fcan hsplit x
        = (⟨k * k * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹), hP1⟩ : ↥Q) * (⟨k * r⁻¹ * k⁻¹, hA2⟩ : ↥Q) :=
      Subtype.ext (by rw [hfx]; rfl)
    rw [h1, hαadd, hαP1, hαA2]
    ring

/-- `r * (k⁻¹ r⁻¹ k) ≠ 1` for `1 ≠ k ∈ Kset H t` (else `k` would centralise `r`). -/
theorem caseB_rrk_ne_one_K {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hr : r ∈ Q) (hrQ0 : r ∉ Work.ThmF.Q0sub H) {k : G}
    (hk : k ∈ Work.ThmF.Kset H t) (hkne : k ≠ 1) :
    r * (k⁻¹ * r⁻¹ * k) ≠ 1 := by
  intro hcon1
  have h1 : k⁻¹ * r⁻¹ * k = r⁻¹ := by
    have h := congrArg (fun z : G => r⁻¹ * z) hcon1
    rw [mul_one] at h
    rw [show r⁻¹ * (r * (k⁻¹ * r⁻¹ * k)) = k⁻¹ * r⁻¹ * k from by group] at h
    exact h
  have h2 := Kset_free_on_Q_K hS hC4 hk hkne (Q.inv_mem hr) h1
  have hr1 : r = 1 := by
    have := congrArg (fun z : G => z⁻¹) h2
    simpa using this
  rw [hr1] at hrQ0
  exact hrQ0 (Work.ThmF.Q0sub H).one_mem

theorem caseB_orbits_conj_core_K {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r a g₁ g₂ : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hs : s ∈ Q) (hs2 : orderOf s = 2) (hr : r ∈ Q) (hsr : t * s * t = r⁻¹ * t * r)
    (h5 : orderOf (s * t) = 5) (hW : Work.ThmF.W H t = ⊥)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 2)
    (hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t)
    (hg₁ : g₁ ∈ Work.PSU3.StageA.GoodReps H t s r) (hg₂ : g₂ ∈ Work.PSU3.StageA.GoodReps H t s r)
    (h₁ : g₁ ∉ Work.ThmF.Q0sub H) (h₂ : g₂ ∉ Work.ThmF.Q0sub H)
    (ha : a ∈ Work.ThmF.Kset H t) (hconj : a⁻¹ * g₁ * a = g₂) : g₁ = g₂ := by
  classical
  have hsplit : IsSplitRankOne H Q t := hS.split
  have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hsplit
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hQ0 := Q0sub_structure hS hC4
  have hQ0Q : Work.ThmF.Q0sub H ≤ Q := Q0sub_le_Q hsplit
  have hQ0C : Work.ThmF.Q0sub H ≤ Work.ThmF.centerOf Q := Q0sub_le_centerOf hS hC4
  -- ## the `α`–`κ` coordinates
  have hKcyc : IsCyclic ↥(Work.ThmF.Ksub H t) :=
    Ksub_cyclic_caseB hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub
  obtain ⟨F, hF, hFint, α, κ, hcardF, hαsurj, hαadd, hαker, hαact⟩ :=
    caseB_Ksub_action_coords hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub hKcyc
  letI : Field F := hF
  have hαone : α (1 : ↥Q) = 0 := by
    have h2 := hαadd (1 : ↥Q) (1 : ↥Q)
    rw [mul_one] at h2
    exact add_left_cancel (show α (1 : ↥Q) + α (1 : ↥Q) = α (1 : ↥Q) + 0 by
      rw [add_zero]; exact h2.symm)
  -- ## characteristic two
  have h2 : (2 : F) = 0 := by
    obtain ⟨n, hn⟩ := hS.two.exists_card_eq
    have hmpow : ∀ (x : ↥Q) (m : ℕ), α (x ^ m) = (m : F) * α x := by
      intro x m
      induction m with
      | zero => simp [hαone]
      | succ m ih => rw [pow_succ, hαadd, ih, Nat.cast_succ, add_mul, one_mul]
    have hpow : ∀ x : ↥Q, x ^ 2 ^ n = 1 := by
      intro x
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [← hn]; exact orderOf_dvd_natCard x)
    have hzero : (2 : F) ^ n = 0 := by
      obtain ⟨x, hx⟩ := hαsurj (1 : F)
      have h1 := hmpow x (2 ^ n)
      rw [hpow x, hαone, hx, mul_one, Nat.cast_pow] at h1
      exact h1.symm
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at hzero
      exact absurd hzero one_ne_zero
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have hkey : ∀ j : ℕ, (2 : F) ^ (j + 1) = 0 → (2 : F) = 0 := by
        intro j
        induction j with
        | zero => intro h; simpa using h
        | succ j ih =>
            intro h
            rw [pow_succ] at h
            exact (mul_eq_zero.mp h).elim ih (fun h' => h')
      exact hkey m hzero
  have hneg : ∀ x : F, -x = x :=
    fun x => (neg_eq_iff_add_eq_zero).mpr (by rw [← two_mul, h2, zero_mul])
  have hsub : ∀ x y : F, x - y = x + y := fun x y => by rw [sub_eq_add_neg, hneg y]
  have hsqeq : ∀ {x y : F}, x ^ 2 = y ^ 2 → x = y := by
    intro x y hxy
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hxy) with h | h
    · exact h
    · rwa [hneg y] at h
  -- ## `s` and `Q₀sub H`
  have hs_mem_Q0 : s ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hsplit.le hs, hs2⟩))
  have hs_sq : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs2] at h
    simpa [pow_two] using h
  have hQ0sq : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 := by
    intro x
    constructor
    · intro hx
      exact Subtype.ext (hQ0.1 (x : G) hx)
    · intro hx
      have hxG : (x : G) * (x : G) = 1 := by simpa [Subgroup.coe_mul] using congrArg Subtype.val hx
      rcases eq_or_ne (x : G) 1 with h1 | h1
      · rw [h1]; exact (Work.ThmF.Q0sub H).one_mem
      · have ho : orderOf (x : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxG) h1
        exact Work.ThmF.Q0_le_Q0sub H
          (Work.ThmF.involutions_subset_Q0 H ⟨hsplit.le x.2, ho⟩)
  -- ## `r`
  have hrinvQ : r⁻¹ ∈ Q := Q.inv_mem hr
  have hr_ne_s : r ≠ s := by
    intro hrs
    have hs_sq : s * s = 1 := by
      have h := pow_orderOf_eq_one s
      rw [hs2] at h
      simpa [pow_two] using h
    have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs_sq
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have h1 : t * s * t = s * t * s := by rw [hrs, hs_inv] at hsr; exact hsr
    have hsq : (s * t) ^ 2 = (s * t)⁻¹ := by
      have ha : (s * t) ^ 2 = t * s := by
        calc (s * t) ^ 2 = s * (t * s * t) := by rw [pow_two]; group
          _ = s * (s * t * s) := by rw [h1]
          _ = (s * s) * (t * s) := by group
          _ = t * s := by rw [hs_sq, one_mul]
      have hb : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, hs_inv, htinv]
      rw [ha, hb]
    have h3 : (s * t) ^ 3 = 1 := by
      rw [show (s * t) ^ 3 = (s * t) ^ 2 * (s * t) from by rw [pow_succ], hsq]
      exact inv_mul_cancel _
    have hdvd : orderOf (s * t) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
    rw [h5] at hdvd
    exact absurd hdvd (by norm_num)
  have hrQ0 : r ∉ Work.ThmF.Q0sub H := by
    intro hr0
    have hgr : r ∈ Work.PSU3.StageA.GoodReps H t s r := by
      rw [Work.PSU3.StageA.GoodReps]
      exact Or.inl (by simp)
    exact hr_ne_s
      ((caseB_GoodReps_mem_Q0sub_iff hS hC4 hHig hs hs2 hr hsr h5 hW hnab hcard hKsub hgr).mp hr0)
  set A : F := α (⟨r, hr⟩ : ↥Q) with hA
  have hαrinv : α (⟨r⁻¹, hrinvQ⟩ : ↥Q) = -A := by
    have h := hαadd (⟨r, hr⟩ : ↥Q) (⟨r⁻¹, hrinvQ⟩ : ↥Q)
    have hmul : (⟨r, hr⟩ : ↥Q) * (⟨r⁻¹, hrinvQ⟩ : ↥Q) = 1 := Subtype.ext (by simp)
    rw [hmul, hαone] at h
    have h' := eq_neg_of_add_eq_zero_right h.symm
    rw [← hA] at h'
    exact h'
  have hA0 : A ≠ 0 := by
    rw [hA]
    intro h0
    exact hrQ0 ((hαker ⟨r, hr⟩).mp h0)
  have hxr1 : ((⟨r, hr⟩ : ↥Q) : G) ≠ 1 := fun h1 =>
    hrQ0 (by rw [show r = ((⟨r, hr⟩ : ↥Q) : G) from rfl, h1]; exact (Work.ThmF.Q0sub H).one_mem)
  have hxri1 : ((⟨r⁻¹, hrinvQ⟩ : ↥Q) : G) ≠ 1 := by
    intro h1
    refine hrQ0 ?_
    have h2 : r = 1 := by
      have := congrArg (fun z : G => z⁻¹) h1
      simpa using this
    rw [h2]
    exact (Work.ThmF.Q0sub H).one_mem
  -- ## `K`-equivariance
  have heq : ∀ (b : ↥(Work.ThmF.Ksub H t)) (x y : ↥Q), (x : G) ≠ 1 →
      (y : G) = (b : G)⁻¹ * (x : G) * (b : G) →
      α y = (κ b : F) * α x ∧
      α (Work.PSU3.StageB.gcan hsplit y)
        = ((κ b : Fˣ) : F)⁻¹ * α (Work.PSU3.StageB.gcan hsplit x) ∧
      α (Work.PSU3.StageB.fcan hsplit y)
        = ((κ b : Fˣ) : F)⁻¹ * α (Work.PSU3.StageB.fcan hsplit x) ∧
      (Work.PSU3.StageB.hcan hsplit y : G)
        = (b : G) * (Work.PSU3.StageB.hcan hsplit x : G) * (b : G) :=
    fun b x y hx hy => alpha_canon_conj_K hsplit hKsub hαact b hx hy
  -- ## the canonical data of `r` and `r⁻¹`
  have hcr := Work.PSU3.StageB.canon_unique'' hsplit hxr1
    (g := (⟨r, hr⟩ : ↥Q)) (d := (⟨1, (twoPoint H t).one_mem⟩ : ↥(twoPoint H t)))
    (y := (⟨s, hs⟩ : ↥Q))
    (by simpa using Work.PSU3.StageA.caseB_t_conj_r ht2 hs2 hsr)
  have hcri := Work.PSU3.StageB.canon_unique'' hsplit hxri1
    (g := (⟨s, hs⟩ : ↥Q)) (d := (⟨1, (twoPoint H t).one_mem⟩ : ↥(twoPoint H t)))
    (y := (⟨r⁻¹, hrinvQ⟩ : ↥Q))
    (by simpa using Work.PSU3.StageA.caseB_t_conj_r_inv ht2 hsr)
  have hαs : α (⟨s, hs⟩ : ↥Q) = 0 := (hαker ⟨s, hs⟩).mpr hs_mem_Q0
  have v_r1 : α (⟨r, hr⟩ : ↥Q) = A := rfl
  have v_r2 : α (Work.PSU3.StageB.gcan hsplit (⟨r, hr⟩ : ↥Q)) = A := by
    rw [show Work.PSU3.StageB.gcan hsplit (⟨r, hr⟩ : ↥Q) = (⟨r, hr⟩ : ↥Q) from
      Subtype.ext hcr.1.symm]
  have v_r3 : α (Work.PSU3.StageB.fcan hsplit (⟨r, hr⟩ : ↥Q)) = 0 := by
    rw [show Work.PSU3.StageB.fcan hsplit (⟨r, hr⟩ : ↥Q) = (⟨s, hs⟩ : ↥Q) from
      Subtype.ext hcr.2.2.symm, hαs]
  have v_ri1 : α (⟨r⁻¹, hrinvQ⟩ : ↥Q) = -A := hαrinv
  have v_ri2 : α (Work.PSU3.StageB.gcan hsplit (⟨r⁻¹, hrinvQ⟩ : ↥Q)) = 0 := by
    rw [show Work.PSU3.StageB.gcan hsplit (⟨r⁻¹, hrinvQ⟩ : ↥Q) = (⟨s, hs⟩ : ↥Q) from
      Subtype.ext hcri.1.symm, hαs]
  have v_ri3 : α (Work.PSU3.StageB.fcan hsplit (⟨r⁻¹, hrinvQ⟩ : ↥Q)) = -A := by
    rw [show Work.PSU3.StageB.fcan hsplit (⟨r⁻¹, hrinvQ⟩ : ↥Q) = (⟨r⁻¹, hrinvQ⟩ : ↥Q) from
      Subtype.ext hcri.2.2.symm]
    exact hαrinv
  set aa : ↥(Work.ThmF.Ksub H t) := mkK_K hKsub ha with haa
  have haaG : (aa : G) = a := mkK_coe_K hKsub ha
  have hmulQ : ∀ (k : G), k ∈ Work.ThmF.Kset H t → r * (k⁻¹ * r⁻¹ * k) ∈ Q := by
    intro k hk
    have hkH : k ∈ H :=
      Work.RankOneUniqueness.twoPoint_le_left H t (Work.ThmF.Kset_subset H t hk)
    refine Q.mul_mem hr ?_
    simpa only [inv_inv] using
      Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := k⁻¹) (H.inv_mem hkH) hrinvQ
  -- ## the exceptional case of the field computation
  have hexc : ∀ (k w : G) (hk : k ∈ Work.ThmF.Kset H t) (hkne : k ≠ 1)
      (hw : w ∈ Work.ThmF.Kset H t) (hws : w * s * w⁻¹ = s * k * s * k⁻¹),
      (κ (mkK_K hKsub hw) : F) * ((κ (mkK_K hKsub hk) : F)⁻¹ + 1) ≠ 1 := by
    intro k w hk hkne hw hws hcon
    have hkH : k ∈ H :=
      Work.RankOneUniqueness.twoPoint_le_left H t (Work.ThmF.Kset_subset H t hk)
    have hxQ : r * (k⁻¹ * r⁻¹ * k) ∈ Q := by
      refine Q.mul_mem hr ?_
      simpa only [inv_inv] using
        Work.RankOneUniqueness.conj_mem_of_mem hsplit (g := k⁻¹) (H.inv_mem hkH) hrinvQ
    set xx : ↥Q := ⟨r * (k⁻¹ * r⁻¹ * k), hxQ⟩ with hxx
    have hxx1 : (xx : G) ≠ 1 := caseB_rrk_ne_one_K hS hC4 hr hrQ0 hk hkne
    have hKne1 : (κ (mkK_K hKsub hk) : F) ≠ 1 := by
      intro hk1
      have h1 : mkK_K hKsub hk = 1 := κ.injective (Units.ext (by simpa using hk1))
      exact hkne (by
        have h := congrArg (fun z : ↥(Work.ThmF.Ksub H t) => (z : G)) h1
        simpa using h)
    obtain ⟨vxx1, vxx2, vxx3⟩ :=
      alpha_data_rrk_K hsplit hS hC4 hs hs2 hr hsr hKsub hαadd hαact hk hkne hw hws xx rfl hxx1
    have hαx0 : α xx ≠ 0 := by
      rw [vxx1, hαrinv]
      have h : A + (κ (mkK_K hKsub hk) : F) * (-A)
          = A * (1 - (κ (mkK_K hKsub hk) : F)) := by ring
      rw [h]
      exact mul_ne_zero hA0 (sub_ne_zero.mpr (Ne.symm hKne1))
    have hxxQ0 : (xx : G) ∉ Work.ThmF.Q0sub H := fun hmem => hαx0 ((hαker xx).mpr hmem)
    -- ## the canonical data of `xx`
    obtain ⟨hg, hd, hy, heq3⟩ := caseB_canon_data_rrk hS hC4 hs hs2 hr hsr hKsub k hk hkne w hw hws
    obtain ⟨hc1, hc2⟩ := Work.PSU3.StageB.canon_unique'' hsplit hxx1
      (g := (⟨r * (w⁻¹ * r⁻¹ * w), hg⟩ : ↥Q))
      (d := (⟨(w⁻¹ * w⁻¹) * (k * k), hd⟩ : ↥(twoPoint H t)))
      (y := (⟨((k * k) * (w⁻¹ * r * w) * (k⁻¹ * k⁻¹)) * (k * r⁻¹ * k⁻¹), hy⟩ : ↥Q))
      (by rw [hxx]; exact heq3)
    let FF : G := (Work.PSU3.StageB.fcan hsplit xx : G)
    let GG : G := (Work.PSU3.StageB.gcan hsplit xx : G)
    let HH : G := (Work.PSU3.StageB.hcan hsplit xx : G)
    have hmemHH : HH ∈ Work.ThmF.Ksub H t := by
      show (Work.PSU3.StageB.hcan hsplit xx : G) ∈ Work.ThmF.Ksub H t
      rw [show (Work.PSU3.StageB.hcan hsplit xx : G) = (w⁻¹ * w⁻¹) * (k * k) from hc2.1.symm]
      exact (Work.ThmF.Ksub H t).mul_mem
        ((Work.ThmF.Ksub H t).mul_mem
          ((Work.ThmF.Ksub H t).inv_mem (Work.ThmF.Kset_le_Ksub H t hw))
          ((Work.ThmF.Ksub H t).inv_mem (Work.ThmF.Kset_le_Ksub H t hw)))
        ((Work.ThmF.Ksub H t).mul_mem (Work.ThmF.Kset_le_Ksub H t hk)
          (Work.ThmF.Kset_le_Ksub H t hk))
    have hHHth : HH * t * HH = t := by
      have hth : t * HH * t = HH⁻¹ := by
        have hkK : HH ∈ Work.ThmF.Kset H t := by rw [← hKsub]; exact hmemHH
        have h := (Work.ThmF.mem_Kset_iff.mp hkK).2
        rwa [Work.RankOneUniqueness.inv_eq_self hsplit] at h
      have h2 : t * HH = HH⁻¹ * t := by
        have h := congrArg (fun z : G => z * t) hth
        rw [show (t * HH * t) * t = t * HH from by rw [mul_assoc, ht2, mul_one]] at h
        exact h
      calc HH * t * HH = HH * (t * HH) := by group
        _ = HH * (HH⁻¹ * t) := by rw [h2]
        _ = t := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    -- ## `x ^ 2` and the involution `(t x t) ^ 2`
    have hxx2mem : ((xx * xx : ↥Q) : G) ∈ Work.ThmF.Q0sub H := by
      apply (hαker _).mp
      rw [hαadd, ← two_mul, h2, zero_mul]
    have hxx4 : ((xx * xx : ↥Q) : G) * ((xx * xx : ↥Q) : G) = 1 := hQ0.1 _ hxx2mem
    have htxt2a : (t * (xx : G) * t) ^ 2 = t * ((xx * xx : ↥Q) : G) * t := by
      calc (t * ↑xx * t) ^ 2 = t * ↑xx * (t * t) * ↑xx * t := by rw [pow_two]; group
        _ = t * (↑xx * ↑xx) * t := by rw [ht2]; group
    have htxt2inv : ((t * (xx : G) * t) ^ 2) ^ 2 = 1 := by
      rw [htxt2a]
      calc (t * ↑(xx * xx) * t) ^ 2 = t * ↑(xx * xx) * (t * t) * ↑(xx * xx) * t := by
            rw [pow_two]; group
        _ = t * (↑(xx * xx) * ↑(xx * xx)) * t := by rw [ht2]; group
        _ = t * 1 * t := by rw [hxx4]
        _ = 1 := by rw [mul_one, ht2]
    have htxt2ne : (t * (xx : G) * t) ^ 2 ≠ 1 := by
      rw [htxt2a]
      intro hcon
      have h3 : ((xx * xx : ↥Q) : G) = 1 := by
        have h := congrArg (fun z : G => t * z * t) hcon
        have e1 : t * (t * ↑(xx * xx) * t) * t = ↑(xx * xx) := by
          rw [show t * (t * ↑(xx * xx) * t) * t
              = (t * t) * ↑(xx * xx) * (t * t) from by group]
          simp only [ht2, one_mul, mul_one]
        have e2 : t * (1 : G) * t = 1 := by simp only [mul_one, ht2]
        rw [e1, e2] at h
        exact h
      exact hxxQ0 ((hQ0sq xx).mpr (Subtype.ext h3))
    -- ## `f * g ∈ Q₀` and `f * g ≠ 1`
    have hfg0 : α (Work.PSU3.StageB.fcan hsplit xx * Work.PSU3.StageB.gcan hsplit xx) = 0 := by
      rw [hαadd, vxx3, vxx2, hαrinv]
      have hkey : (κ (mkK_K hKsub hk) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw) : F)
            - (κ (mkK_K hKsub hk) : F)⁻¹ + (1 - (κ (mkK_K hKsub hw) : F))
          = ((κ (mkK_K hKsub hk) : F)⁻¹ + 1)
            * ((κ (mkK_K hKsub hw) : F) * ((κ (mkK_K hKsub hk) : F)⁻¹ + 1) + 1) := by
        rw [hsub, hsub]
        ring_nf
        simp [h2]
      have h11 : (1 : F) + 1 = 0 := by rw [← two_mul, h2, zero_mul]
      calc (κ (mkK_K hKsub hk) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw) : F) * A
              + (κ (mkK_K hKsub hk) : F)⁻¹ * (-A) + (A + (κ (mkK_K hKsub hw) : F) * (-A))
          = A * ((κ (mkK_K hKsub hk) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw) : F)
              - (κ (mkK_K hKsub hk) : F)⁻¹ + (1 - (κ (mkK_K hKsub hw) : F))) := by ring
        _ = A * (((κ (mkK_K hKsub hk) : F)⁻¹ + 1)
              * ((κ (mkK_K hKsub hw) : F) * ((κ (mkK_K hKsub hk) : F)⁻¹ + 1) + 1)) := by
              rw [hkey]
        _ = A * (((κ (mkK_K hKsub hk) : F)⁻¹ + 1) * (1 + 1)) := by rw [hcon]
        _ = A * (((κ (mkK_K hKsub hk) : F)⁻¹ + 1) * 0) := by rw [h11]
        _ = 0 := by ring
    have hfgQ0 : ((Work.PSU3.StageB.fcan hsplit xx * Work.PSU3.StageB.gcan hsplit xx : ↥Q) : G)
        ∈ Work.ThmF.Q0sub H := (hαker _).mp hfg0
    have hfgQ0' : FF * GG ∈ Work.ThmF.Q0sub H := by
      show ((Work.PSU3.StageB.fcan hsplit xx : G) * (Work.PSU3.StageB.gcan hsplit xx : G))
        ∈ Work.ThmF.Q0sub H
      rw [Subgroup.coe_mul] at hfgQ0
      exact hfgQ0
    have hspec := Work.PSU3.StageB.canon_spec hsplit hxx1
    have hguf : (t * (xx : G) * t) ^ 2 = GG * (t * (HH⁻¹ * (FF * GG) * HH) * t) * FF := by
      rw [pow_two]
      rw [show t * ↑xx * t = GG * HH * t * FF from hspec]
      calc (GG * HH * t * FF) * (GG * HH * t * FF)
          = GG * (HH * t * (FF * GG) * HH * t) * FF := by group
        _ = GG * ((HH * t * HH) * (HH⁻¹ * (FF * GG) * HH) * t) * FF := by group
        _ = GG * (t * (HH⁻¹ * (FF * GG) * HH) * t) * FF := by rw [hHHth]
    have hFF_ne1 : FF * GG ≠ 1 := by
      intro hcon1
      have hgf : GG * FF = 1 := by
        have h2 : (FF : G)⁻¹ = GG := inv_eq_of_mul_eq_one_right hcon1
        rw [← h2]
        exact inv_mul_cancel _
      have hv : HH⁻¹ * (FF * GG) * HH = 1 := by
        rw [hcon1]
        group
      refine htxt2ne ?_
      rw [hguf, hv]
      rw [show t * (1 : G) * t = 1 from by simp only [mul_one, ht2]]
      simp only [mul_one]
      exact hgf
    -- ## `u = t v t` with `v = h⁻¹ (f g) h`
    have hv_mem : HH⁻¹ * (FF * GG) * HH ∈ Work.ThmF.Q0sub H := by
      have hHHH : HH ∈ H := by
        show (Work.PSU3.StageB.hcan hsplit xx : G) ∈ H
        exact Work.RankOneUniqueness.twoPoint_le_left H t (Work.PSU3.StageB.hcan hsplit xx).2
      simpa using hQ0.2.2.1 HH⁻¹ (H.inv_mem hHHH) (FF * GG) hfgQ0'
    have hv_ne1 : HH⁻¹ * (FF * GG) * HH ≠ 1 := by
      intro hv1
      refine hFF_ne1 ?_
      have h := congrArg (fun z : G => HH * z * HH⁻¹) hv1
      rw [show HH * (HH⁻¹ * (FF * GG) * HH) * HH⁻¹ = FF * GG from by group] at h
      rw [show HH * (1 : G) * HH⁻¹ = 1 from by simp only [mul_one, mul_inv_cancel]] at h
      exact h
    have huH : (t * (HH⁻¹ * (FF * GG) * HH) * t) ∉ H := by
      intro hmem
      have hvvH : HH⁻¹ * (FF * GG) * HH ∈ H := Work.ThmF.Q0sub_le H hv_mem
      have hvvHt : HH⁻¹ * (FF * GG) * HH ∈ H.map (MulAut.conj t).toMonoidHom := by
        refine ⟨t * (HH⁻¹ * (FF * GG) * HH) * t, hmem, ?_⟩
        show MulAut.conj t (t * (HH⁻¹ * (FF * GG) * HH) * t) = HH⁻¹ * (FF * GG) * HH
        rw [MulAut.conj_apply]
        rw [show t * (t * (HH⁻¹ * (FF * GG) * HH) * t) * t⁻¹
            = (t * t) * (HH⁻¹ * (FF * GG) * HH) * (t * t⁻¹) from by group]
        simp only [ht2, one_mul, mul_inv_cancel, mul_one]
      have hmem2 : HH⁻¹ * (FF * GG) * HH ∈ Q ⊓ twoPoint H t := ⟨hQ0Q hv_mem, hvvH, hvvHt⟩
      rw [hsplit.inf_eq] at hmem2
      exact hv_ne1 (Subgroup.mem_bot.mp hmem2)
    have hv2 : orderOf (HH⁻¹ * (FF * GG) * HH) = 2 := by
      refine orderOf_eq_prime ?_ hv_ne1
      rw [pow_two]
      exact hQ0.1 _ hv_mem
    have hu2 : orderOf (t * (HH⁻¹ * (FF * GG) * HH) * t) = 2 := by
      rw [show t * (HH⁻¹ * (FF * GG) * HH) * t
          = t * (HH⁻¹ * (FF * GG) * HH) * t⁻¹ from by rw [hti]]
      rw [Work.ThmF.Bender.orderOf_conj_eq]
      exact hv2
    have hY2 : orderOf (FF * GG) = 2 := by
      refine orderOf_eq_prime ?_ hFF_ne1
      rw [pow_two]
      exact hQ0.1 _ hfgQ0'
    have hcomm : (t * (HH⁻¹ * (FF * GG) * HH) * t) * (FF * GG)
        = (FF * GG) * (t * (HH⁻¹ * (FF * GG) * HH) * t) := by
      have h1 : (GG * (t * (HH⁻¹ * (FF * GG) * HH) * t) * FF) ^ 2 = 1 := by
        rw [← hguf, htxt2inv]
      rw [pow_two] at h1
      have h2 : (t * (HH⁻¹ * (FF * GG) * HH) * t) * (FF * GG)
          * (t * (HH⁻¹ * (FF * GG) * HH) * t) = FF * GG := by
        have h := congrArg (fun z : G => GG⁻¹ * z * FF⁻¹) h1
        have e1 : GG⁻¹ * ((GG * (t * (HH⁻¹ * (FF * GG) * HH) * t) * FF)
              * (GG * (t * (HH⁻¹ * (FF * GG) * HH) * t) * FF)) * FF⁻¹
            = (t * (HH⁻¹ * (FF * GG) * HH) * t) * (FF * GG)
              * (t * (HH⁻¹ * (FF * GG) * HH) * t) := by group
        have e2 : GG⁻¹ * (1 : G) * FF⁻¹ = GG⁻¹ * FF⁻¹ := by simp only [mul_one]
        rw [e1, e2] at h
        rw [show GG⁻¹ * FF⁻¹ = FF * GG from by
          rw [show GG⁻¹ * FF⁻¹ = (FF * GG)⁻¹ from by rw [mul_inv_rev]]
          exact inv_eq_of_mul_eq_one_right (hQ0.1 _ hfgQ0')] at h
        exact h
      have hu2' : (t * (HH⁻¹ * (FF * GG) * HH) * t)
          * (t * (HH⁻¹ * (FF * GG) * HH) * t) = 1 := by
        rw [← pow_two, ← hu2]
        exact pow_orderOf_eq_one _
      have h5 : (t * (HH⁻¹ * (FF * GG) * HH) * t) * (FF * GG)
          * ((t * (HH⁻¹ * (FF * GG) * HH) * t)
            * (t * (HH⁻¹ * (FF * GG) * HH) * t))
          = (FF * GG) * (t * (HH⁻¹ * (FF * GG) * HH) * t) := by
        have h := congrArg (fun z : G => z * (t * (HH⁻¹ * (FF * GG) * HH) * t)) h2
        rw [show ((t * (HH⁻¹ * (FF * GG) * HH) * t) * (FF * GG)
              * (t * (HH⁻¹ * (FF * GG) * HH) * t))
              * (t * (HH⁻¹ * (FF * GG) * HH) * t)
            = (t * (HH⁻¹ * (FF * GG) * HH) * t) * (FF * GG)
              * ((t * (HH⁻¹ * (FF * GG) * HH) * t)
                * (t * (HH⁻¹ * (FF * GG) * HH) * t)) from by group] at h
        exact h
      rw [hu2', mul_one] at h5
      exact h5
    exact false_of_commuting_involutions hS hu2 hY2 huH (Work.ThmF.Q0sub_le H hfgQ0') hcomm
  -- ## the case analysis
  -- ### `g₁ = r`
  rcases hg₁ with hg₁ | ⟨k₁, hk₁K, hk₁ne, rfl⟩
  · rcases Set.mem_insert_iff.mp hg₁ with hg₁ | hg₁
    · exact absurd (hg₁ ▸ hs_mem_Q0) h₁
    · rcases Set.mem_insert_iff.mp hg₁ with hg₁ | hg₁
      · rw [hg₁] at hconj ⊢
        rcases hg₂ with hg₂ | ⟨k₂, hk₂K, hk₂ne, rfl⟩
        · rcases Set.mem_insert_iff.mp hg₂ with hg₂ | hg₂
          · exact absurd (hg₂ ▸ hs_mem_Q0) h₂
          · rcases Set.mem_insert_iff.mp hg₂ with hg₂ | hg₂
            · rw [hg₂]
            · rw [Set.mem_singleton_iff] at hg₂
              rw [hg₂] at hconj ⊢
              exfalso
              have hya : ((⟨r⁻¹, hrinvQ⟩ : ↥Q) : G)
                  = (aa : G)⁻¹ * ((⟨r, hr⟩ : ↥Q) : G) * (aa : G) := by
                show (r⁻¹ : G) = a⁻¹ * r * a
                exact hconj.symm
              obtain ⟨-, e2, -, -⟩ :=
                heq aa (⟨r, hr⟩ : ↥Q) (⟨r⁻¹, hrinvQ⟩ : ↥Q) hxr1 hya
              rw [v_ri2, v_r2] at e2
              exact hA0 ((mul_eq_zero.mp e2.symm).resolve_left
                (inv_ne_zero (Units.ne_zero (κ aa))))
        · exfalso
          obtain ⟨w₂, hw₂K, hws₂⟩ := caseB_exists_w_K hS hC4 hs hs2 hk₂K hk₂ne
          set yy : ↥Q := ⟨r * (k₂⁻¹ * r⁻¹ * k₂), hmulQ k₂ hk₂K⟩ with hyy
          have hyy1 : (yy : G) ≠ 1 := caseB_rrk_ne_one_K hS hC4 hr hrQ0 hk₂K hk₂ne
          have hya : (yy : G) = (aa : G)⁻¹ * ((⟨r, hr⟩ : ↥Q) : G) * (aa : G) := by
            show (r * (k₂⁻¹ * r⁻¹ * k₂) : G) = a⁻¹ * r * a
            exact hconj.symm
          obtain ⟨e1, e2, e3, -⟩ := heq aa (⟨r, hr⟩ : ↥Q) yy hxr1 hya
          obtain ⟨w1, w2, w3⟩ :=
            alpha_data_rrk_K hsplit hS hC4 hs hs2 hr hsr hKsub hαadd hαact
              hk₂K hk₂ne hw₂K hws₂ yy rfl hyy1
          rw [hαrinv, v_r1] at w1 w2 w3
          rw [w1, v_r1] at e1
          rw [w2, v_r2] at e2
          rw [w3, v_r3, mul_zero] at e3
          have hK0 : (κ (mkK_K hKsub hk₂K) : F) ≠ 0 := Units.ne_zero _
          have hK1 : 1 + (κ (mkK_K hKsub hk₂K) : F) = (κ aa : F) := by
            have h' : A * (1 - (κ (mkK_K hKsub hk₂K) : F)) = (κ aa : F) * A := by
              calc A * (1 - (κ (mkK_K hKsub hk₂K) : F))
                  = A + (κ (mkK_K hKsub hk₂K) : F) * (-A) := by ring
                _ = (κ aa : F) * A := e1
            rw [mul_comm (κ aa : F) A] at h'
            have h'' := mul_left_cancel₀ hA0 h'
            rw [hsub 1 (κ (mkK_K hKsub hk₂K) : F)] at h''
            exact h''
          have hW1 : 1 - (κ (mkK_K hKsub hw₂K) : F) = (κ aa : F)⁻¹ := by
            have h' : A * (1 - (κ (mkK_K hKsub hw₂K) : F)) = (κ aa : F)⁻¹ * A := by
              calc A * (1 - (κ (mkK_K hKsub hw₂K) : F))
                  = A + (κ (mkK_K hKsub hw₂K) : F) * (-A) := by ring
                _ = (κ aa : F)⁻¹ * A := e2
            rw [mul_comm ((κ aa : F)⁻¹) A] at h'
            exact mul_left_cancel₀ hA0 h'
          have hW2 : (κ (mkK_K hKsub hw₂K) : F) = (κ (mkK_K hKsub hk₂K) : F) := by
            have hA3 : A * ((κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F)
                - (κ (mkK_K hKsub hk₂K) : F)⁻¹) = 0 := by
              have h : (κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F) * A
                  + (κ (mkK_K hKsub hk₂K) : F)⁻¹ * (-A)
                  = A * ((κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F)
                    - (κ (mkK_K hKsub hk₂K) : F)⁻¹) := by ring
              rw [← h]; exact e3
            have hJ : (κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F)
                - (κ (mkK_K hKsub hk₂K) : F)⁻¹ = 0 := (mul_eq_zero.mp hA3).resolve_left hA0
            have hJ' : (κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F)
                = (κ (mkK_K hKsub hk₂K) : F)⁻¹ := sub_eq_zero.mp hJ
            have h2' : (κ (mkK_K hKsub hk₂K) : F)⁻¹
                * ((κ (mkK_K hKsub hk₂K) : F)⁻¹ * (κ (mkK_K hKsub hw₂K) : F))
                = (κ (mkK_K hKsub hk₂K) : F)⁻¹ * 1 := by
              rw [mul_one]
              calc (κ (mkK_K hKsub hk₂K) : F)⁻¹
                    * ((κ (mkK_K hKsub hk₂K) : F)⁻¹ * (κ (mkK_K hKsub hw₂K) : F))
                  = (κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F) := by ring
                _ = (κ (mkK_K hKsub hk₂K) : F)⁻¹ := hJ'
            have h3' := mul_left_cancel₀ (inv_ne_zero hK0) h2'
            have h4 : (κ (mkK_K hKsub hk₂K) : F) * ((κ (mkK_K hKsub hk₂K) : F)⁻¹
                * (κ (mkK_K hKsub hw₂K) : F)) = (κ (mkK_K hKsub hk₂K) : F) := by
              simpa using congrArg (fun z : F => (κ (mkK_K hKsub hk₂K) : F) * z) h3'
            rw [← mul_assoc, mul_inv_cancel₀ hK0, one_mul] at h4
            exact h4
          have hfin : (κ (mkK_K hKsub hk₂K) : F) = 0 := by
            have hsq : (1 + (κ (mkK_K hKsub hk₂K) : F)) * (1 - (κ (mkK_K hKsub hw₂K) : F)) = 1 := by
              rw [hK1, hW1, mul_inv_cancel₀ (Units.ne_zero (κ aa))]
            rw [hW2] at hsq
            have h3 : (1 + (κ (mkK_K hKsub hk₂K) : F)) * (1 - (κ (mkK_K hKsub hk₂K) : F))
                = 1 - (κ (mkK_K hKsub hk₂K) : F) ^ 2 := by ring
            rw [h3] at hsq
            have h4 : (κ (mkK_K hKsub hk₂K) : F) ^ 2 = 0 := by
              refine add_left_cancel (a := (1 : F)) ?_
              rw [add_zero]
              exact (sub_eq_iff_eq_add.mp hsq).symm
            rw [pow_two] at h4
            exact mul_self_eq_zero.mp h4
          exact hK0 hfin
      · rw [Set.mem_singleton_iff] at hg₁
        rw [hg₁] at hconj ⊢
        rcases hg₂ with hg₂ | ⟨k₂, hk₂K, hk₂ne, rfl⟩
        · rcases Set.mem_insert_iff.mp hg₂ with hg₂ | hg₂
          · exact absurd (hg₂ ▸ hs_mem_Q0) h₂
          · rcases Set.mem_insert_iff.mp hg₂ with hg₂ | hg₂
            · rw [hg₂] at hconj ⊢
              exfalso
              have hya : ((⟨r, hr⟩ : ↥Q) : G)
                  = (aa : G)⁻¹ * ((⟨r⁻¹, hrinvQ⟩ : ↥Q) : G) * (aa : G) := by
                show (r : G) = a⁻¹ * r⁻¹ * a
                exact hconj.symm
              obtain ⟨-, e2, -, -⟩ :=
                heq aa (⟨r⁻¹, hrinvQ⟩ : ↥Q) (⟨r, hr⟩ : ↥Q) hxri1 hya
              simp only [v_r2, v_ri2, mul_zero] at e2
              exact hA0 e2
            · rw [Set.mem_singleton_iff] at hg₂
              rw [hg₂]
        · exfalso
          obtain ⟨w₂, hw₂K, hws₂⟩ := caseB_exists_w_K hS hC4 hs hs2 hk₂K hk₂ne
          set yy : ↥Q := ⟨r * (k₂⁻¹ * r⁻¹ * k₂), hmulQ k₂ hk₂K⟩ with hyy
          have hyy1 : (yy : G) ≠ 1 := caseB_rrk_ne_one_K hS hC4 hr hrQ0 hk₂K hk₂ne
          have hya : (yy : G) = (aa : G)⁻¹ * ((⟨r⁻¹, hrinvQ⟩ : ↥Q) : G) * (aa : G) := by
            show (r * (k₂⁻¹ * r⁻¹ * k₂) : G) = a⁻¹ * r⁻¹ * a
            exact hconj.symm
          obtain ⟨-, e2, -, -⟩ := heq aa (⟨r⁻¹, hrinvQ⟩ : ↥Q) yy hxri1 hya
          obtain ⟨-, w2, -⟩ :=
            alpha_data_rrk_K hsplit hS hC4 hs hs2 hr hsr hKsub hαadd hαact
              hk₂K hk₂ne hw₂K hws₂ yy rfl hyy1
          rw [hαrinv, v_r1] at w2
          simp only [w2, v_ri2, mul_zero] at e2
          have hw₂ne : w₂ ≠ 1 := by
            intro h1
            have h3 : k₂ * s * k₂⁻¹ = 1 := by
              have h2 : s = s * (k₂ * s * k₂⁻¹) := by
                have h := hws₂
                simp only [h1, one_mul, mul_one, inv_one] at h
                simpa only [mul_assoc] using h
              have h4 : s * s = s * (s * (k₂ * s * k₂⁻¹)) := congrArg (fun z : G => s * z) h2
              rw [show s * (s * (k₂ * s * k₂⁻¹)) = (s * s) * (k₂ * s * k₂⁻¹) from by group,
                hs_sq, one_mul] at h4
              exact h4.symm
            have h5 : s = 1 := by
              calc s = k₂⁻¹ * (k₂ * s * k₂⁻¹) * k₂ := by group
                _ = k₂⁻¹ * 1 * k₂ := by rw [h3]
                _ = 1 := by group
            rw [h5, orderOf_one] at hs2
            exact absurd hs2 (by norm_num)
          have hW0 : (κ (mkK_K hKsub hw₂K) : F) ≠ 1 := by
            intro h1
            have h1' : κ (mkK_K hKsub hw₂K) = (1 : Fˣ) := by
              ext
              simpa using h1
            have h1'' : mkK_K hKsub hw₂K = 1 := κ.injective (by rw [h1']; simp)
            exact hw₂ne (by
              have h' := congrArg (fun z : ↥(Work.ThmF.Ksub H t) => (z : G)) h1''
              simpa using h')
          have hzero : A * (1 - (κ (mkK_K hKsub hw₂K) : F)) = 0 := by
            have h : A + (κ (mkK_K hKsub hw₂K) : F) * (-A)
                = A * (1 - (κ (mkK_K hKsub hw₂K) : F)) := by ring
            rw [h] at e2
            exact e2
          exact (sub_ne_zero.mpr (Ne.symm hW0))
            ((mul_eq_zero.mp hzero).resolve_left hA0)
  · -- ### `g₁ = r (k₁⁻¹ r⁻¹ k₁)`
    rcases hg₂ with hg₂ | ⟨k₂, hk₂K, hk₂ne, rfl⟩
    · rcases Set.mem_insert_iff.mp hg₂ with hg₂ | hg₂
      · exact absurd (hg₂ ▸ hs_mem_Q0) h₂
      · rcases Set.mem_insert_iff.mp hg₂ with hg₂ | hg₂
        · rw [hg₂] at hconj ⊢
          exfalso
          obtain ⟨w₁, hw₁K, hws₁⟩ := caseB_exists_w_K hS hC4 hs hs2 hk₁K hk₁ne
          set xx : ↥Q := ⟨r * (k₁⁻¹ * r⁻¹ * k₁), hmulQ k₁ hk₁K⟩ with hxx
          have hxx1 : (xx : G) ≠ 1 := caseB_rrk_ne_one_K hS hC4 hr hrQ0 hk₁K hk₁ne
          have hya : ((⟨r, hr⟩ : ↥Q) : G) = (aa : G)⁻¹ * (xx : G) * (aa : G) := by
            show (r : G) = a⁻¹ * (r * (k₁⁻¹ * r⁻¹ * k₁)) * a
            exact hconj.symm
          obtain ⟨e1, e2, e3, -⟩ := heq aa xx (⟨r, hr⟩ : ↥Q) hxx1 hya
          obtain ⟨v1, v2, v3⟩ :=
            alpha_data_rrk_K hsplit hS hC4 hs hs2 hr hsr hKsub hαadd hαact
              hk₁K hk₁ne hw₁K hws₁ xx rfl hxx1
          rw [hαrinv, v_r1] at v1 v2 v3
          rw [v1, v_r1] at e1
          rw [v2, v_r2] at e2
          rw [v3, v_r3] at e3
          have hK0 : (κ (mkK_K hKsub hk₁K) : F) ≠ 0 := Units.ne_zero _
          have hW1 : 1 - (κ (mkK_K hKsub hw₁K) : F) = (κ aa : F) := by
            have h' : A * (1 - (κ (mkK_K hKsub hw₁K) : F)) = (κ aa : F) * A := by
              calc A * (1 - (κ (mkK_K hKsub hw₁K) : F))
                  = A + (κ (mkK_K hKsub hw₁K) : F) * (-A) := by ring
                _ = (κ aa : F) * A := by
                  have h := congrArg (fun z : F => (κ aa : F) * z) e2
                  rw [show (κ aa : F) * ((κ aa : F)⁻¹
                        * (A + (κ (mkK_K hKsub hw₁K) : F) * (-A)))
                      = A + (κ (mkK_K hKsub hw₁K) : F) * (-A) from by
                        rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (κ aa)), one_mul]] at h
                  exact h.symm
            rw [mul_comm (κ aa : F) A] at h'
            exact mul_left_cancel₀ hA0 h'
          have hW2 : (κ (mkK_K hKsub hw₁K) : F) = (κ (mkK_K hKsub hk₁K) : F) := by
            have hA3 : A * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                - (κ (mkK_K hKsub hk₁K) : F)⁻¹) = 0 := by
              have h0 : (κ aa : F)⁻¹ * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F) * A
                  + (κ (mkK_K hKsub hk₁K) : F)⁻¹ * (-A)) = 0 := e3.symm
              have hV : (κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F) * A
                  + (κ (mkK_K hKsub hk₁K) : F)⁻¹ * (-A) = 0 :=
                (mul_eq_zero.mp h0).resolve_left (inv_ne_zero (Units.ne_zero (κ aa)))
              have h : (κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F) * A
                  + (κ (mkK_K hKsub hk₁K) : F)⁻¹ * (-A)
                  = A * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                    - (κ (mkK_K hKsub hk₁K) : F)⁻¹) := by ring
              rw [h] at hV
              exact hV
            have hJ : (κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                - (κ (mkK_K hKsub hk₁K) : F)⁻¹ = 0 := (mul_eq_zero.mp hA3).resolve_left hA0
            have hJ' : (κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                = (κ (mkK_K hKsub hk₁K) : F)⁻¹ := sub_eq_zero.mp hJ
            have h2' : (κ (mkK_K hKsub hk₁K) : F)⁻¹
                * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ * (κ (mkK_K hKsub hw₁K) : F))
                = (κ (mkK_K hKsub hk₁K) : F)⁻¹ * 1 := by
              rw [mul_one]
              calc (κ (mkK_K hKsub hk₁K) : F)⁻¹
                    * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ * (κ (mkK_K hKsub hw₁K) : F))
                  = (κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F) := by ring
                _ = (κ (mkK_K hKsub hk₁K) : F)⁻¹ := hJ'
            have h3' := mul_left_cancel₀ (inv_ne_zero hK0) h2'
            have h4 : (κ (mkK_K hKsub hk₁K) : F) * ((κ (mkK_K hKsub hk₁K) : F)⁻¹
                * (κ (mkK_K hKsub hw₁K) : F)) = (κ (mkK_K hKsub hk₁K) : F) := by
              simpa using congrArg (fun z : F => (κ (mkK_K hKsub hk₁K) : F) * z) h3'
            rw [← mul_assoc, mul_inv_cancel₀ hK0, one_mul] at h4
            exact h4
          have hK1 : 1 + (κ (mkK_K hKsub hk₁K) : F) = (κ aa : F)⁻¹ := by
            have h' : A * (1 - (κ (mkK_K hKsub hk₁K) : F)) = (κ aa : F)⁻¹ * A := by
              calc A * (1 - (κ (mkK_K hKsub hk₁K) : F))
                  = A + (κ (mkK_K hKsub hk₁K) : F) * (-A) := by ring
                _ = (κ aa : F)⁻¹ * A := by
                  have h := congrArg (fun z : F => (κ aa : F)⁻¹ * z) e1
                  rw [show (κ aa : F)⁻¹ * ((κ aa : F)
                        * (A + (κ (mkK_K hKsub hk₁K) : F) * (-A)))
                      = A + (κ (mkK_K hKsub hk₁K) : F) * (-A) from by
                        rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero (κ aa)), one_mul]] at h
                  exact h.symm
            rw [mul_comm ((κ aa : F)⁻¹) A] at h'
            have h'' := mul_left_cancel₀ hA0 h'
            rw [hsub 1 (κ (mkK_K hKsub hk₁K) : F)] at h''
            exact h''
          have hfin : (κ (mkK_K hKsub hk₁K) : F) = 0 := by
            have hsq : (1 + (κ (mkK_K hKsub hk₁K) : F)) * (1 - (κ (mkK_K hKsub hw₁K) : F)) = 1 := by
              rw [hK1, hW1, inv_mul_cancel₀ (Units.ne_zero (κ aa))]
            rw [hW2] at hsq
            have h3 : (1 + (κ (mkK_K hKsub hk₁K) : F)) * (1 - (κ (mkK_K hKsub hk₁K) : F))
                = 1 - (κ (mkK_K hKsub hk₁K) : F) ^ 2 := by ring
            rw [h3] at hsq
            have h4 : (κ (mkK_K hKsub hk₁K) : F) ^ 2 = 0 := by
              refine add_left_cancel (a := (1 : F)) ?_
              rw [add_zero]
              exact (sub_eq_iff_eq_add.mp hsq).symm
            rw [pow_two] at h4
            exact mul_self_eq_zero.mp h4
          exact hK0 hfin
        · rw [Set.mem_singleton_iff] at hg₂
          rw [hg₂] at hconj ⊢
          exfalso
          obtain ⟨w₁, hw₁K, hws₁⟩ := caseB_exists_w_K hS hC4 hs hs2 hk₁K hk₁ne
          set xx : ↥Q := ⟨r * (k₁⁻¹ * r⁻¹ * k₁), hmulQ k₁ hk₁K⟩ with hxx
          have hxx1 : (xx : G) ≠ 1 := caseB_rrk_ne_one_K hS hC4 hr hrQ0 hk₁K hk₁ne
          have hya : ((⟨r⁻¹, hrinvQ⟩ : ↥Q) : G) = (aa : G)⁻¹ * (xx : G) * (aa : G) := by
            show (r⁻¹ : G) = a⁻¹ * (r * (k₁⁻¹ * r⁻¹ * k₁)) * a
            exact hconj.symm
          obtain ⟨-, e2, -, -⟩ := heq aa xx (⟨r⁻¹, hrinvQ⟩ : ↥Q) hxx1 hya
          obtain ⟨-, v2, -⟩ :=
            alpha_data_rrk_K hsplit hS hC4 hs hs2 hr hsr hKsub hαadd hαact
              hk₁K hk₁ne hw₁K hws₁ xx rfl hxx1
          rw [hαrinv, v_r1] at v2
          simp only [v2, v_ri2, mul_zero] at e2
          have hw₁ne : w₁ ≠ 1 := by
            intro h1
            have h3 : k₁ * s * k₁⁻¹ = 1 := by
              have h2 : s = s * (k₁ * s * k₁⁻¹) := by
                have h := hws₁
                simp only [h1, one_mul, mul_one, inv_one] at h
                simpa only [mul_assoc] using h
              have h4 : s * s = s * (s * (k₁ * s * k₁⁻¹)) := congrArg (fun z : G => s * z) h2
              rw [show s * (s * (k₁ * s * k₁⁻¹)) = (s * s) * (k₁ * s * k₁⁻¹) from by group,
                hs_sq, one_mul] at h4
              exact h4.symm
            have h5 : s = 1 := by
              calc s = k₁⁻¹ * (k₁ * s * k₁⁻¹) * k₁ := by group
                _ = k₁⁻¹ * 1 * k₁ := by rw [h3]
                _ = 1 := by group
            rw [h5, orderOf_one] at hs2
            exact absurd hs2 (by norm_num)
          have hW1ne : (κ (mkK_K hKsub hw₁K) : F) ≠ 1 := by
            intro h1
            have h1' : κ (mkK_K hKsub hw₁K) = (1 : Fˣ) := by
              ext
              simpa using h1
            have h1'' : mkK_K hKsub hw₁K = 1 := κ.injective (by rw [h1']; simp)
            exact hw₁ne (by
              have h' := congrArg (fun z : ↥(Work.ThmF.Ksub H t) => (z : G)) h1''
              simpa using h')
          have hzero : A * (1 - (κ (mkK_K hKsub hw₁K) : F)) = 0 := by
            have h : A + (κ (mkK_K hKsub hw₁K) : F) * (-A)
                = A * (1 - (κ (mkK_K hKsub hw₁K) : F)) := by ring
            rw [h] at e2
            exact (mul_eq_zero.mp e2.symm).resolve_left (inv_ne_zero (Units.ne_zero (κ aa)))
          exact (sub_ne_zero.mpr (Ne.symm hW1ne))
            ((mul_eq_zero.mp hzero).resolve_left hA0)
    · -- ### both are `r r^{-k}`
      by_cases hk12 : k₁ = k₂
      · rw [hk12]
      · exfalso
        obtain ⟨w₁, hw₁K, hws₁⟩ := caseB_exists_w_K hS hC4 hs hs2 hk₁K hk₁ne
        obtain ⟨w₂, hw₂K, hws₂⟩ := caseB_exists_w_K hS hC4 hs hs2 hk₂K hk₂ne
        set xx : ↥Q := ⟨r * (k₁⁻¹ * r⁻¹ * k₁), hmulQ k₁ hk₁K⟩ with hxx
        set yy : ↥Q := ⟨r * (k₂⁻¹ * r⁻¹ * k₂), hmulQ k₂ hk₂K⟩ with hyy
        have hxx1 : (xx : G) ≠ 1 := caseB_rrk_ne_one_K hS hC4 hr hrQ0 hk₁K hk₁ne
        have hyy1 : (yy : G) ≠ 1 := caseB_rrk_ne_one_K hS hC4 hr hrQ0 hk₂K hk₂ne
        have hya : (yy : G) = (aa : G)⁻¹ * (xx : G) * (aa : G) := by
          show (r * (k₂⁻¹ * r⁻¹ * k₂) : G) = a⁻¹ * (r * (k₁⁻¹ * r⁻¹ * k₁)) * a
          exact hconj.symm
        obtain ⟨e1, e2, e3, e4⟩ := heq aa xx yy hxx1 hya
        -- the h-equation, in `K`
        obtain ⟨hg₁', hd₁', hy₁', heq₁'⟩ :=
          caseB_canon_data_rrk hS hC4 hs hs2 hr hsr hKsub k₁ hk₁K hk₁ne w₁ hw₁K hws₁
        obtain ⟨hc1x, hc2x⟩ := Work.PSU3.StageB.canon_unique'' hsplit hxx1
          (g := (⟨r * (w₁⁻¹ * r⁻¹ * w₁), hg₁'⟩ : ↥Q))
          (d := (⟨(w₁⁻¹ * w₁⁻¹) * (k₁ * k₁), hd₁'⟩ : ↥(twoPoint H t)))
          (y := (⟨((k₁ * k₁) * (w₁⁻¹ * r * w₁) * (k₁⁻¹ * k₁⁻¹))
              * (k₁ * r⁻¹ * k₁⁻¹), hy₁'⟩ : ↥Q))
          (by rw [hxx]; exact heq₁')
        obtain ⟨hg₂', hd₂', hy₂', heq₂'⟩ :=
          caseB_canon_data_rrk hS hC4 hs hs2 hr hsr hKsub k₂ hk₂K hk₂ne w₂ hw₂K hws₂
        obtain ⟨hc1y, hc2y⟩ := Work.PSU3.StageB.canon_unique'' hsplit hyy1
          (g := (⟨r * (w₂⁻¹ * r⁻¹ * w₂), hg₂'⟩ : ↥Q))
          (d := (⟨(w₂⁻¹ * w₂⁻¹) * (k₂ * k₂), hd₂'⟩ : ↥(twoPoint H t)))
          (y := (⟨((k₂ * k₂) * (w₂⁻¹ * r * w₂) * (k₂⁻¹ * k₂⁻¹))
              * (k₂ * r⁻¹ * k₂⁻¹), hy₂'⟩ : ↥Q))
          (by rw [hyy]; exact heq₂')
        have hhh₁ : (w₁⁻¹ * w₁⁻¹) * (k₁ * k₁) ∈ Work.ThmF.Ksub H t :=
          (Work.ThmF.Ksub H t).mul_mem
            ((Work.ThmF.Ksub H t).mul_mem
              ((Work.ThmF.Ksub H t).inv_mem (Work.ThmF.Kset_le_Ksub H t hw₁K))
              ((Work.ThmF.Ksub H t).inv_mem (Work.ThmF.Kset_le_Ksub H t hw₁K)))
            ((Work.ThmF.Ksub H t).mul_mem (Work.ThmF.Kset_le_Ksub H t hk₁K)
              (Work.ThmF.Kset_le_Ksub H t hk₁K))
        have hhh₂ : (w₂⁻¹ * w₂⁻¹) * (k₂ * k₂) ∈ Work.ThmF.Ksub H t :=
          (Work.ThmF.Ksub H t).mul_mem
            ((Work.ThmF.Ksub H t).mul_mem
              ((Work.ThmF.Ksub H t).inv_mem (Work.ThmF.Kset_le_Ksub H t hw₂K))
              ((Work.ThmF.Ksub H t).inv_mem (Work.ThmF.Kset_le_Ksub H t hw₂K)))
            ((Work.ThmF.Ksub H t).mul_mem (Work.ThmF.Kset_le_Ksub H t hk₂K)
              (Work.ThmF.Kset_le_Ksub H t hk₂K))
        have hhh₃ : (aa : G) * ((w₁⁻¹ * w₁⁻¹) * (k₁ * k₁)) * (aa : G) ∈ Work.ThmF.Ksub H t :=
          (Work.ThmF.Ksub H t).mul_mem
            ((Work.ThmF.Ksub H t).mul_mem aa.2 hhh₁) aa.2
        rw [show (Work.PSU3.StageB.hcan hsplit xx : G) = (w₁⁻¹ * w₁⁻¹) * (k₁ * k₁)
            from hc2x.1.symm,
          show (Work.PSU3.StageB.hcan hsplit yy : G) = (w₂⁻¹ * w₂⁻¹) * (k₂ * k₂)
            from hc2y.1.symm, haaG] at e4
        have hκe : (κ (⟨(w₂⁻¹ * w₂⁻¹) * (k₂ * k₂), hhh₂⟩ : ↥(Work.ThmF.Ksub H t)) : F)
            = (κ (⟨a * ((w₁⁻¹ * w₁⁻¹) * (k₁ * k₁)) * a, hhh₃⟩ : ↥(Work.ThmF.Ksub H t)) : F) := by
          apply congrArg (fun z : ↥(Work.ThmF.Ksub H t) => (κ z : F))
          exact Subtype.ext e4
        -- square-root form of the `h`-equation
        have hE6 : (κ (mkK_K hKsub hw₂K) : F)⁻¹ * (κ (mkK_K hKsub hk₂K) : F)
            = (κ aa : F) * (κ (mkK_K hKsub hw₁K) : F)⁻¹ * (κ (mkK_K hKsub hk₁K) : F) := by
          apply hsqeq
          have hL : (κ (⟨(w₂⁻¹ * w₂⁻¹) * (k₂ * k₂), hhh₂⟩ : ↥(Work.ThmF.Ksub H t)) : F)
              = ((κ (mkK_K hKsub hw₂K) : F)⁻¹ * (κ (mkK_K hKsub hk₂K) : F)) ^ 2 := by
            rw [show (⟨(w₂⁻¹ * w₂⁻¹) * (k₂ * k₂), hhh₂⟩ : ↥(Work.ThmF.Ksub H t))
                  = (mkK_K hKsub hw₂K)⁻¹ * (mkK_K hKsub hw₂K)⁻¹
                    * (mkK_K hKsub hk₂K * mkK_K hKsub hk₂K)
                  from Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, mkK_coe_K])]
            simp only [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val]
            ring_nf
          have hR : (κ (⟨a * ((w₁⁻¹ * w₁⁻¹) * (k₁ * k₁)) * a, hhh₃⟩ : ↥(Work.ThmF.Ksub H t)) : F)
              = ((κ (mkK_K hKsub ha) : F) * (κ (mkK_K hKsub hw₁K) : F)⁻¹
                * (κ (mkK_K hKsub hk₁K) : F)) ^ 2 := by
            rw [show (⟨a * ((w₁⁻¹ * w₁⁻¹) * (k₁ * k₁)) * a, hhh₃⟩ : ↥(Work.ThmF.Ksub H t))
                  = (mkK_K hKsub ha) * ((mkK_K hKsub hw₁K)⁻¹ * (mkK_K hKsub hw₁K)⁻¹
                    * (mkK_K hKsub hk₁K * mkK_K hKsub hk₁K)) * (mkK_K hKsub ha)
                  from Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, mkK_coe_K])]
            simp only [map_mul, Units.val_mul, map_inv, Units.val_inv_eq_inv_val]
            ring_nf
          rw [← hL, hκe, hR]
        -- the values of `x` (from `alpha_data_rrk_K`) are used to extract the three equations
        obtain ⟨v1x, v2x, v3x⟩ :=
          alpha_data_rrk_K hsplit hS hC4 hs hs2 hr hsr hKsub hαadd hαact
            hk₁K hk₁ne hw₁K hws₁ xx rfl hxx1
        obtain ⟨v1y, v2y, v3y⟩ :=
          alpha_data_rrk_K hsplit hS hC4 hs hs2 hr hsr hKsub hαadd hαact
            hk₂K hk₂ne hw₂K hws₂ yy rfl hyy1
        rw [hαrinv, v_r1] at v1x v2x v3x v1y v2y v3y
        rw [v1y, v1x] at e1
        rw [v2y, v2x] at e2
        rw [v3y, v3x] at e3
        have hE5 : 1 + (κ (mkK_K hKsub hk₂K) : F)
            = (κ aa : F) * (1 + (κ (mkK_K hKsub hk₁K) : F)) := by
          have h' : A * (1 - (κ (mkK_K hKsub hk₂K) : F))
              = A * ((κ aa : F) * (1 - (κ (mkK_K hKsub hk₁K) : F))) := by
            calc A * (1 - (κ (mkK_K hKsub hk₂K) : F))
                = A + (κ (mkK_K hKsub hk₂K) : F) * (-A) := by ring
              _ = (κ aa : F) * (A + (κ (mkK_K hKsub hk₁K) : F) * (-A)) := e1
              _ = A * ((κ aa : F) * (1 - (κ (mkK_K hKsub hk₁K) : F))) := by ring
          have h'' := mul_left_cancel₀ hA0 h'
          rw [hsub 1 (κ (mkK_K hKsub hk₂K) : F), hsub 1 (κ (mkK_K hKsub hk₁K) : F)] at h''
          exact h''
        have hE7 : (κ (mkK_K hKsub hw₂K) : F) * ((κ (mkK_K hKsub hk₂K) : F)⁻¹) ^ 2
              + (κ (mkK_K hKsub hk₂K) : F)⁻¹
            = (κ aa : F)⁻¹ * ((κ (mkK_K hKsub hw₁K) : F) * ((κ (mkK_K hKsub hk₁K) : F)⁻¹) ^ 2
              + (κ (mkK_K hKsub hk₁K) : F)⁻¹) := by
          have h' : A * ((κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F)
                - (κ (mkK_K hKsub hk₂K) : F)⁻¹)
              = (κ aa : F)⁻¹ * (A * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                - (κ (mkK_K hKsub hk₁K) : F)⁻¹)) := by
            calc A * ((κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F)
                  - (κ (mkK_K hKsub hk₂K) : F)⁻¹)
                = (κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F) * A
                  + (κ (mkK_K hKsub hk₂K) : F)⁻¹ * (-A) := by ring
              _ = (κ aa : F)⁻¹ * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F) * A
                  + (κ (mkK_K hKsub hk₁K) : F)⁻¹ * (-A)) := e3
              _ = (κ aa : F)⁻¹ * (A * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                  - (κ (mkK_K hKsub hk₁K) : F)⁻¹)) := by ring
          have h'' : A * ((κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F)
                - (κ (mkK_K hKsub hk₂K) : F)⁻¹)
              = A * ((κ aa : F)⁻¹ * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                - (κ (mkK_K hKsub hk₁K) : F)⁻¹)) := by
            rw [h']; ring
          have h3 := mul_left_cancel₀ hA0 h''
          rw [hsub ((κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F))
              (κ (mkK_K hKsub hk₂K) : F)⁻¹,
            hsub ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F))
              (κ (mkK_K hKsub hk₁K) : F)⁻¹] at h3
          have h4 : (κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₂K) : F)
              + (κ (mkK_K hKsub hk₂K) : F)⁻¹
              = (κ aa : F)⁻¹ * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                + (κ (mkK_K hKsub hk₁K) : F)⁻¹) := h3
          rw [mul_comm ((κ (mkK_K hKsub hk₂K) : F)⁻¹ ^ 2) (κ (mkK_K hKsub hw₂K) : F)] at h4
          rw [show (κ aa : F)⁻¹ * ((κ (mkK_K hKsub hk₁K) : F)⁻¹ ^ 2 * (κ (mkK_K hKsub hw₁K) : F)
                + (κ (mkK_K hKsub hk₁K) : F)⁻¹)
              = (κ aa : F)⁻¹ * ((κ (mkK_K hKsub hw₁K) : F) * ((κ (mkK_K hKsub hk₁K) : F)⁻¹) ^ 2
                + (κ (mkK_K hKsub hk₁K) : F)⁻¹) from by ring] at h4
          exact h4
        have hfld := caseB_field_algebra h2 (Units.ne_zero (κ aa))
          (Units.ne_zero (κ (mkK_K hKsub hk₁K))) (Units.ne_zero (κ (mkK_K hKsub hk₂K)))
          (Units.ne_zero (κ (mkK_K hKsub hw₁K))) (Units.ne_zero (κ (mkK_K hKsub hw₂K)))
          hE5 hE6 hE7
          (hexc k₁ w₁ hk₁K hk₁ne hw₁K hws₁) (hexc k₂ w₂ hk₂K hk₂ne hw₂K hws₂)
        exact hk12 (by
          have h := κ.injective (Units.ext hfld)
          have h' := congrArg (fun z : ↥(Work.ThmF.Ksub H t) => (z : G)) h
          simpa using h')

end Work.PSU3.StageA
