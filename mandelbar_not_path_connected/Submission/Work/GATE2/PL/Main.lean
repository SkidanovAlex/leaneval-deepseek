import Mathlib
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.PL.isCoveringMapOn_tantibar_five
import Submission.Work.GATE2.PL.eq_v_of_eq_c0
import Submission.Work.GATE2.PL.ne_iterate_crit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Set Function Filter
open Classical
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}


section Step

variable (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (G5 c₀) d.z₁)
variable (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (G5 c₀) d.z₁ fl.Pa fl.φa)
variable {v X : ℝ}

/-- The critical-value set `{T^[j] c₀ : 0 ≤ j ≤ 4}` of `G5 c₀ = (T_{c₀})^[5]`. -/
def critVals : Set ℂ := {z : ℂ | ∃ j : ℕ, j ≤ 4 ∧ z = (Tantibar c₀)^[j] c₀}

theorem exists_step_of_avoid (hX : v - 1 / 2 ≤ X) {k : ℕ} {ψ : ℂ → ℂ}
    (hψ : Good fl FF v X k ψ)
    (havoid : ∀ z : ℂ, z ∈ Dom v X (k + 1) → ψ (sig z) ∉ critVals (c₀ := c₀)) :
    ∃ ψ' : ℂ → ℂ, Good fl FF v X (k + 1) ψ' ∧ ∀ w ∈ Dom v X k, ψ' w = ψ w := by
  have hSmem : ∀ z : ℂ, z ∈ Dom v X (k + 1) → sig z ∈ Dom v X k :=
    fun z hz => dom_sig_succ hz
  have hcont : ContinuousOn (fun z : ℂ => ψ (sig z)) (Dom v X (k + 1)) :=
    hψ.cont.comp continuous_sig.continuousOn hSmem
  haveI hLP : LocallyPathConnectedSpace ↥(Dom v X (k + 1)) :=
    (isOpen_Dom v X (k + 1)).locallyPathConnectedSpace
  haveI hCT : ContractibleSpace ↥(Dom v X (k + 1)) := contractibleSpace_Dom hX (k + 1)
  haveI hSC : SimplyConnectedSpace ↥(Dom v X (k + 1)) := SimplyConnectedSpace.ofContractible _
  have hp : ((X + 1 : ℝ) : ℂ) ∈ Dom v X (k + 1) := mem_Dom_starP hX (k + 1)
  have hpk : ((X + 1 : ℝ) : ℂ) ∈ Dom v X k := mem_Dom_starP hX k
  let hb : C(↥(Dom v X (k + 1)), ℂ) :=
    ⟨(Dom v X (k + 1)).domRestrict (fun z : ℂ => ψ (sig z)), hcont.domRestrict⟩
  have hb_val : ∀ (z : ℂ) (hz : z ∈ Dom v X (k + 1)), hb ⟨z, hz⟩ = ψ (sig z) :=
    fun z hz => rfl
  obtain ⟨F, ⟨hFp, hFg⟩, huniq⟩ :=
    IsCoveringMapOn.existsUnique_continuousMap_lifts (isCoveringMapOn_tantibar_five c₀) hb
      (a₀ := ⟨_, hp⟩) (e₀ := ψ _) (by rw [hb_val _ hp]; exact hψ.anti _ hpk)
      (fun a => by rw [hb_val a.1 a.2]; exact havoid a.1 a.2)
  haveI hLPk : LocallyPathConnectedSpace ↥(Dom v X k) :=
    (isOpen_Dom v X k).locallyPathConnectedSpace
  haveI hCTk : ContractibleSpace ↥(Dom v X k) := contractibleSpace_Dom hX k
  haveI hSCk : SimplyConnectedSpace ↥(Dom v X k) := SimplyConnectedSpace.ofContractible _
  have hcontk : ContinuousOn (fun z : ℂ => ψ (sig z)) (Dom v X k) :=
    hψ.cont.comp continuous_sig.continuousOn (fun z hz => dom_sig_mem hz)
  let hbk : C(↥(Dom v X k), ℂ) :=
    ⟨(Dom v X k).domRestrict (fun z : ℂ => ψ (sig z)), hcontk.domRestrict⟩
  have hbk_val : ∀ (z : ℂ) (hz : z ∈ Dom v X k), hbk ⟨z, hz⟩ = ψ (sig z) := fun z hz => rfl
  obtain ⟨Fk, ⟨hFkp, hFkg⟩, huniqk⟩ :=
    IsCoveringMapOn.existsUnique_continuousMap_lifts (isCoveringMapOn_tantibar_five c₀) hbk
      (a₀ := ⟨_, hpk⟩) (e₀ := ψ _) (by rw [hbk_val _ hpk]; exact hψ.anti _ hpk)
      (fun a => by
        rw [hbk_val a.1 a.2]
        exact havoid a.1 (dom_mono (Nat.le_succ k) a.2))
  let incl : C(↥(Dom v X k), ↥(Dom v X (k + 1))) :=
    ⟨fun z => ⟨z.1, dom_mono (Nat.le_succ k) z.2⟩, by fun_prop⟩
  have hFlift : F.comp incl = Fk := by
    refine huniqk _ ⟨?_, ?_⟩
    · show F (incl ⟨_, hpk⟩) = ψ _
      rw [show incl ⟨((X + 1 : ℝ) : ℂ), hpk⟩ = ⟨((X + 1 : ℝ) : ℂ), hp⟩ from rfl, hFp]
    · funext z
      have h1 : hbk z = hb (incl z) := by
        show ψ (sig z.1) = hb (incl z)
        show ψ (sig z.1) = hb ⟨z.1, dom_mono (Nat.le_succ k) z.2⟩
        rw [hb_val z.1 (dom_mono (Nat.le_succ k) z.2)]
      rw [h1]
      exact congr_fun hFg (incl z)
  have hψlift : (⟨(Dom v X k).domRestrict ψ, hψ.cont.domRestrict⟩ : C(↥(Dom v X k), ℂ)) = Fk := by
    refine huniqk _ ⟨rfl, ?_⟩
    funext z
    exact hψ.anti z.1 z.2
  have hLift : ∀ (w : ℂ) (hw : w ∈ Dom v X k),
      F ⟨w, dom_mono (Nat.le_succ k) hw⟩ = ψ w := by
    intro w hw
    have h2 := congr_fun (congr_arg (fun g : C(↥(Dom v X k), ℂ) => (g : ↥(Dom v X k) → ℂ))
      (hFlift.trans hψlift.symm)) ⟨w, hw⟩
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, incl, Set.domRestrict_apply,
      Function.comp_apply] using h2
  refine ⟨fun z => if h : z ∈ Dom v X (k + 1) then F ⟨z, h⟩ else 0, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      have hw1 : sig w ∈ Dom v X (k + 1) := dom_sig_mem hw
      rw [dif_pos hw, dif_pos hw1, hLift (sig w) (hSmem w hw)]
      exact congr_fun hFg ⟨w, hw⟩
    · intro w hw
      have hwk : w ∈ Dom v X k := mem_Dom.mpr ⟨?_, ?_⟩
      · rw [dif_pos (dom_mono (Nat.le_succ k) hwk), hLift w hwk]
        exact hψ.far w hw
      · rintro ⟨him, hle⟩
        linarith
      · have hk : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
        linarith
    · rw [continuousOn_iff_continuous_domRestrict]
      have hres : (Dom v X (k + 1)).domRestrict
          (fun z : ℂ => if h : z ∈ Dom v X (k + 1) then F ⟨z, h⟩ else 0) = ⇑F := by
        funext z
        rw [Set.domRestrict_apply]
        exact dif_pos z.2
      rw [hres]
      exact F.continuous
  · intro w hw
    have hw1 : w ∈ Dom v X (k + 1) := dom_mono (Nat.le_succ k) hw
    simp only [dif_pos hw1]
    exact hLift w hw

end Step


section Recursion

variable (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (G5 c₀) d.z₁)
variable (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (G5 c₀) d.z₁ fl.Pa fl.φa)
variable {v X : ℝ}

/-- **The avoidance of the critical values**: no `Good` function on `Dom v X k` takes, at a point
of `sig '' Dom v X (k+1)`, a value in the critical-value set of `G5 c₀`. -/
theorem avoidance (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) {k : ℕ} {ψ : ℂ → ℂ} (hψ : Good fl FF v X k ψ) :
    ∀ z : ℂ, z ∈ Dom v X (k + 1) → ψ (sig z) ∉ critVals (c₀ := c₀) := by
  intro z hz
  have hsk : sig z ∈ Dom v X k := dom_sig_succ hz
  rintro ⟨j, hj4, hjw⟩
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have hsv : sig z = (v : ℂ) := eq_v_of_eq_c0 hψ hv hsk hjw
    have hzmem : z ∈ slitAt v := (mem_Dom.mp hz).1
    rw [slitAt, Set.mem_ofPred_eq] at hzmem
    apply hzmem
    have hz' : z = ((v - 1 / 2 : ℝ) : ℂ) := by
      refine Complex.ext ?_ ?_
      · have h := congrArg Complex.re hsv
        simp only [sig_re, Complex.ofReal_re] at h
        simp only [Complex.ofReal_re]
        linarith
      · have h := congrArg Complex.im hsv
        simp only [sig_im, Complex.ofReal_im, neg_eq_zero] at h
        simp only [Complex.ofReal_im, h]
    rw [hz']
    constructor
    · simp
    · simp
  · exact (ne_iterate_crit hψ hsk (Finset.mem_Ioo.mpr ⟨hpos, by omega⟩)) hjw

/-- One step of the half-step lifting: extend a `Good` function from `Dom v X k` to
`Dom v X (k+1)`. -/
theorem exists_step (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) {k : ℕ} {ψ : ℂ → ℂ} (hψ : Good fl FF v X k ψ) :
    ∃ ψ' : ℂ → ℂ, Good fl FF v X (k + 1) ψ' ∧ ∀ w ∈ Dom v X k, ψ' w = ψ w :=
  exists_step_of_avoid fl FF hX hψ (avoidance fl FF hHalf hv hX hψ)

/-- The recursively constructed sequence of good functions. -/
noncomputable def seqGood (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) : (k : ℕ) → {ψ : ℂ → ℂ // Good fl FF v X k ψ}
  | 0 => ⟨baseψ fl FF, good_base fl FF hHalf⟩
  | k + 1 => ⟨Classical.choose (exists_step fl FF hHalf hv hX (seqGood hHalf hv hX k).2),
      (Classical.choose_spec (exists_step fl FF hHalf hv hX (seqGood hHalf hv hX k).2)).1⟩

theorem seqGood_agree_succ (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) (k : ℕ) :
    ∀ w ∈ Dom v X k,
      (seqGood fl FF hHalf hv hX (k + 1)).1 w = (seqGood fl FF hHalf hv hX k).1 w :=
  (Classical.choose_spec (exists_step fl FF hHalf hv hX (seqGood fl FF hHalf hv hX k).2)).2

theorem seqGood_agree (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) {j k : ℕ} (hjk : j ≤ k) :
    ∀ w ∈ Dom v X j, (seqGood fl FF hHalf hv hX k).1 w = (seqGood fl FF hHalf hv hX j).1 w := by
  induction k with
  | zero =>
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero hjk
    intro w _
    rfl
  | succ k ih =>
    intro w hw
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have hjk' : j ≤ k := Nat.lt_succ_iff.mp h
      rw [seqGood_agree_succ fl FF hHalf hv hX k w (dom_mono hjk' hw), ih hjk' w hw]
    · have hje : j = k + 1 := le_antisymm hjk h
      subst hje
      rfl

/-- The level of a point: the least `k` with `X - k/2 < Re w`. -/
noncomputable def lvl (X : ℝ) (w : ℂ) : ℕ := Nat.find (exists_nat_gt (2 * (X - w.re)))

theorem lvl_spec {X : ℝ} {w : ℂ} : 2 * (X - w.re) < (lvl X w : ℝ) :=
  Nat.find_spec (exists_nat_gt (2 * (X - w.re)))

theorem lvl_le {X : ℝ} {w : ℂ} {k : ℕ} (h : X - (k : ℝ) / 2 < w.re) : lvl X w ≤ k := by
  refine Nat.find_min' _ ?_
  linarith

theorem mem_Dom_lvl {v X : ℝ} {w : ℂ} (hw : w ∈ slitAt v) : w ∈ Dom v X (lvl X w) := by
  refine mem_Dom.mpr ⟨hw, ?_⟩
  have := lvl_spec (X := X) (w := w)
  linarith

/-- **The principal Fatou parametrisation of the `c₀`-flower** on the slit plane. -/
noncomputable def Psi (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) : ℂ → ℂ :=
  fun w => (seqGood fl FF hHalf hv hX (lvl X w)).1 w

theorem Psi_eq (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) {k : ℕ} {w : ℂ} (hw : w ∈ Dom v X k) :
    Psi fl FF hHalf hv hX w = (seqGood fl FF hHalf hv hX k).1 w :=
  (seqGood_agree fl FF hHalf hv hX (lvl_le (X := X) (mem_Dom.mp hw).2) w
    (mem_Dom_lvl (mem_Dom.mp hw).1)).symm

theorem Psi_far (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) {w : ℂ} (hw : X < w.re) :
    Psi fl FF hHalf hv hX w ∈ FF.Pg ∧ fl.φa (Psi fl FF hHalf hv hX w) = w := by
  have hwk : w ∈ Dom v X 0 := by
    refine mem_Dom.mpr ⟨?_, by simpa using hw⟩
    rintro ⟨him, hle⟩
    linarith
  rw [Psi_eq fl FF hHalf hv hX hwk]
  exact (seqGood fl FF hHalf hv hX 0).2.far w hw

theorem Psi_anti (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) {w : ℂ} (hw : w ∈ slitAt v) :
    G5 c₀ (Psi fl FF hHalf hv hX w) = Psi fl FF hHalf hv hX (sig w) := by
  have h1 : w ∈ Dom v X (lvl X w) := mem_Dom_lvl hw
  have h2 : sig w ∈ Dom v X (lvl X w) := by
    refine mem_Dom.mpr ⟨mem_Dom_sig hw, ?_⟩
    have := (mem_Dom.mp h1).2
    simp only [sig_re]
    linarith
  rw [Psi_eq fl FF hHalf hv hX h1, Psi_eq fl FF hHalf hv hX h2]
  exact (seqGood fl FF hHalf hv hX (lvl X w)).2.anti w h1

theorem Psi_shift (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) {w : ℂ} (hw : w ∈ slitAt v) :
    Work.EL.F c₀ (Psi fl FF hHalf hv hX w) = Psi fl FF hHalf hv hX (w + 1) := by
  have h1 := Psi_anti fl FF hHalf hv hX hw
  have h2 := Psi_anti fl FF hHalf hv hX (mem_Dom_sig hw)
  calc Work.EL.F c₀ (Psi fl FF hHalf hv hX w)
      = G5 c₀ (G5 c₀ (Psi fl FF hHalf hv hX w)) := by rw [F_eq_comp_G5]; rfl
    _ = G5 c₀ (Psi fl FF hHalf hv hX (sig w)) := by rw [h1]
    _ = Psi fl FF hHalf hv hX (sig (sig w)) := h2
    _ = Psi fl FF hHalf hv hX (w + 1) := by rw [sig_sig]

theorem Psi_cont (hHalf : ∀ w : ℂ, X < w.re → ∃ z ∈ FF.Pg, fl.φa z = w)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    (hX : v - 1 / 2 ≤ X) :
    ContinuousOn (Psi fl FF hHalf hv hX) (slitAt v) := by
  intro x hx
  obtain ⟨k, hk⟩ := dom_exhaust (v := v) (X := X) hx
  have hcont : ContinuousOn (Psi fl FF hHalf hv hX) (Dom v X k) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hres : (Dom v X k).domRestrict (Psi fl FF hHalf hv hX) =
        (Dom v X k).domRestrict (seqGood fl FF hHalf hv hX k).1 := by
      funext z
      rw [Set.domRestrict_apply, Set.domRestrict_apply]
      exact Psi_eq fl FF hHalf hv hX z.2
    rw [hres]
    exact continuousOn_iff_continuous_domRestrict.mp (seqGood fl FF hHalf hv hX k).2.cont
  exact (hcont.continuousAt ((isOpen_Dom v X k).mem_nhds hk)).continuousWithinAt

end Recursion

end

end Work.GATE2.PL
