/-
# `PL/UCore` — the cut-free half-plane recursion behind `eq_c0_of_good`

The module `Submission/Work/GATE2/PL/Main.lean` builds the principal Fatou parametrisation on
the *slit plane* `slitAt v = ℂ \ (−∞, v − 1/2]`, lifting half-steps through the antiholomorphic
root `G5 c₀ = (T_{c₀})^[5]` over the domains `Dom v X k = slitAt v ∩ {X − k/2 < Re w}`.

For the Liouville argument of `eq_c0_of_good` we need the same recursion over the *cut-free*
domains

  `U X k = {w : ℂ | X − k/2 < Re w}`,

which will extend a function defined far to the right to *all* of `ℂ`.  The only new point
(compared with `Main.lean`) is the avoidance of the critical values: a `GoodU` function `ψ` on
`U X k` takes the value `c₀` only at `w = v` (`eq_v_of_eq_c0_U`), and the values `T^j c₀`
(`1 ≤ j ≤ 4`) not at all (`ne_iterate_crit_U`).  Hence, if the given parametrisation `Ψs` does
*not* take the value `c₀` at `v` (the assumption `hne` of `eq_c0_of_good`), every half-step can
be performed, so `Ψs` extends to an entire bounded function — contradiction.

This file contains the domains, the `GoodU`/`GoodU2` predicates, the lift step
`exists_stepU`, the recursive sequence, the glued global function `PsiU` and its properties
(intertwining, continuity, inverse Fatou coordinate far to the right, boundedness).
-/
import Mathlib
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.GATE2.ExitPath
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.PL.Main
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

/-! ## The cut-free domains `U X k` -/

/-- The cut-free level-`k` domain: the half-plane `{Re w > X − k/2}`. -/
def U (X : ℝ) (k : ℕ) : Set ℂ := {w : ℂ | X - (k : ℝ) / 2 < w.re}

theorem mem_U {X : ℝ} {k : ℕ} {w : ℂ} : w ∈ U X k ↔ X - (k : ℝ) / 2 < w.re := Iff.rfl

theorem U_mono {X : ℝ} {j k : ℕ} (hjk : j ≤ k) : U X j ⊆ U X k := by
  intro w hw
  rw [mem_U] at hw ⊢
  have : ((j : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hjk
  linarith

theorem isOpen_U (X : ℝ) (k : ℕ) : IsOpen (U X k) := by
  have : U X k = {w : ℂ | (X - (k : ℝ) / 2) < w.re} := rfl
  rw [this]
  exact isOpen_lt continuous_const Complex.continuous_re

/-- `sig` maps `U X k` into itself. -/
theorem sig_mem_U {X : ℝ} {k : ℕ} {w : ℂ} (hw : w ∈ U X k) : sig w ∈ U X k := by
  rw [mem_U] at hw ⊢
  rw [sig_re]
  linarith

/-- `sig` lowers the level by one: it maps `U X (k+1)` into `U X k`. -/
theorem sig_mem_U_succ {X : ℝ} {k : ℕ} {w : ℂ} (hw : w ∈ U X (k + 1)) : sig w ∈ U X k := by
  rw [mem_U] at hw ⊢
  rw [sig_re]
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hw
  linarith

/-- The base point `X + 1` lies in every `U X k`. -/
theorem mem_U_starP (X : ℝ) (k : ℕ) : ((X + 1 : ℝ) : ℂ) ∈ U X k := by
  rw [mem_U]
  simp only [Complex.ofReal_re]
  have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
  linarith

theorem nonempty_U (X : ℝ) (k : ℕ) : (U X k).Nonempty := ⟨_, mem_U_starP X k⟩

/-- `U X k` is star-shaped with respect to the real point `X + 1`. -/
theorem starConvex_U (X : ℝ) (k : ℕ) :
    StarConvex ℝ ((X + 1 : ℝ) : ℂ) (U X k) :=
  (convex_halfSpace_re_gt (X - (k : ℝ) / 2)).starConvex (mem_U_starP X k)

theorem contractibleSpace_U (X : ℝ) (k : ℕ) : ContractibleSpace ↥(U X k) :=
  (starConvex_U X k).contractibleSpace (nonempty_U X k)

/-- Every point of `ℂ` lies in some `U X k`. -/
theorem exists_mem_U (X : ℝ) (w : ℂ) : ∃ k : ℕ, w ∈ U X k := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * (X - w.re))
  refine ⟨k, ?_⟩
  rw [mem_U]
  linarith

/-- `w ∈ U X (lvl X w)`, the level of `w` defined in `Main.lean`. -/
theorem mem_U_lvl {X : ℝ} {w : ℂ} : w ∈ U X (lvl X w) := by
  rw [mem_U]
  have := lvl_spec (X := X) (w := w)
  linarith

/-! ## The cut-free "good" predicate and the lift step -/

variable (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (G5 c₀) d.z₁)
variable (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (G5 c₀) d.z₁ fl.Pa fl.φa)

/-- A half-step lift of `Ψ` on the cut-free domain `U X k`: it intertwines `G5` with `sig` on
`U X k` and is the inverse of the Fatou coordinate `φa` far to the right. -/
structure GoodU (v X : ℝ) (k : ℕ) (ψ : ℂ → ℂ) : Prop where
  anti : ∀ w ∈ U X k, G5 c₀ (ψ w) = ψ (sig w)
  far : ∀ w : ℂ, X < w.re → ψ w ∈ FF.Pg ∧ fl.φa (ψ w) = w
  cont : ContinuousOn ψ (U X k)

/-- `GoodU` together with the avoidance of the critical values of `G5 c₀`, which is the extra
invariant that makes the recursion run. -/
structure GoodU2 (v X : ℝ) (k : ℕ) (ψ : ℂ → ℂ) : Prop where
  good : GoodU fl FF v X k ψ
  avoid : ∀ w ∈ U X k, ψ w ∉ critVals (c₀ := c₀)

theorem GoodU2.goodU {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ} (h : GoodU2 fl FF v X k ψ) :
    GoodU fl FF v X k ψ := h.good

/-- The iterated shift relation on `U X k`: `ψ (w + n) = F^[n] (ψ w)`. -/
theorem GoodU.shift {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ} (hψ : GoodU fl FF v X k ψ) :
    ∀ w ∈ U X k, Work.EL.F c₀ (ψ w) = ψ (w + 1) := by
  intro w hw
  have h1 := hψ.anti w hw
  have h2 := hψ.anti (sig w) (sig_mem_U hw)
  calc Work.EL.F c₀ (ψ w) = G5 c₀ (G5 c₀ (ψ w)) := by rw [F_eq_comp_G5]; rfl
    _ = G5 c₀ (ψ (sig w)) := by rw [h1]
    _ = ψ (sig (sig w)) := h2
    _ = ψ (w + 1) := by rw [sig_sig]

theorem GoodU.iterate_shift {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ} (hψ : GoodU fl FF v X k ψ)
    {w : ℂ} (hw : w ∈ U X k) :
    ∀ n : ℕ, ψ (w + (n : ℂ)) = (Work.EL.F c₀)^[n] (ψ w) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hmem : w + (n : ℂ) ∈ U X k := by
      rw [mem_U] at hw ⊢
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    have h1 : w + ((n + 1 : ℕ) : ℂ) = (w + (n : ℂ)) + 1 := by push_cast; ring
    rw [h1, ← GoodU.shift fl FF hψ (w + (n : ℂ)) hmem, ih]
    rw [Function.iterate_succ_apply']

/-- **The lift step over the cut-free domain.**  If `ψ` is a half-step lift on `U X k` and the
base map `z ↦ ψ (sig z)` avoids the critical values of `G5 c₀` on `U X (k+1)`, then `ψ` extends
to a half-step lift on `U X (k+1)`, agreeing with `ψ` on `U X k`. -/
theorem exists_stepU {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ}
    (hψ : GoodU fl FF v X k ψ)
    (havoid : ∀ z : ℂ, z ∈ U X (k + 1) → ψ (sig z) ∉ critVals (c₀ := c₀)) :
    ∃ ψ' : ℂ → ℂ, GoodU fl FF v X (k + 1) ψ' ∧ ∀ w ∈ U X k, ψ' w = ψ w := by
  have hSmem : ∀ z : ℂ, z ∈ U X (k + 1) → sig z ∈ U X k :=
    fun z hz => sig_mem_U_succ hz
  have hcont : ContinuousOn (fun z : ℂ => ψ (sig z)) (U X (k + 1)) :=
    hψ.cont.comp continuous_sig.continuousOn hSmem
  haveI hLP : LocallyPathConnectedSpace ↥(U X (k + 1)) :=
    (isOpen_U X (k + 1)).locallyPathConnectedSpace
  haveI hCT : ContractibleSpace ↥(U X (k + 1)) := contractibleSpace_U X (k + 1)
  haveI hSC : SimplyConnectedSpace ↥(U X (k + 1)) := SimplyConnectedSpace.ofContractible _
  have hp : ((X + 1 : ℝ) : ℂ) ∈ U X (k + 1) := mem_U_starP X (k + 1)
  have hpk : ((X + 1 : ℝ) : ℂ) ∈ U X k := mem_U_starP X k
  let hb : C(↥(U X (k + 1)), ℂ) :=
    ⟨(U X (k + 1)).domRestrict (fun z : ℂ => ψ (sig z)), hcont.domRestrict⟩
  have hb_val : ∀ (z : ℂ) (hz : z ∈ U X (k + 1)), hb ⟨z, hz⟩ = ψ (sig z) :=
    fun z hz => rfl
  obtain ⟨F, ⟨hFp, hFg⟩, huniq⟩ :=
    IsCoveringMapOn.existsUnique_continuousMap_lifts (isCoveringMapOn_tantibar_five c₀) hb
      (a₀ := ⟨_, hp⟩) (e₀ := ψ _) (by rw [hb_val _ hp]; exact hψ.anti _ hpk)
      (fun a => by rw [hb_val a.1 a.2]; exact havoid a.1 a.2)
  haveI hLPk : LocallyPathConnectedSpace ↥(U X k) :=
    (isOpen_U X k).locallyPathConnectedSpace
  haveI hCTk : ContractibleSpace ↥(U X k) := contractibleSpace_U X k
  haveI hSCk : SimplyConnectedSpace ↥(U X k) := SimplyConnectedSpace.ofContractible _
  have hcontk : ContinuousOn (fun z : ℂ => ψ (sig z)) (U X k) :=
    hψ.cont.comp continuous_sig.continuousOn (fun z hz => sig_mem_U hz)
  let hbk : C(↥(U X k), ℂ) :=
    ⟨(U X k).domRestrict (fun z : ℂ => ψ (sig z)), hcontk.domRestrict⟩
  have hbk_val : ∀ (z : ℂ) (hz : z ∈ U X k), hbk ⟨z, hz⟩ = ψ (sig z) := fun z hz => rfl
  obtain ⟨Fk, ⟨hFkp, hFkg⟩, huniqk⟩ :=
    IsCoveringMapOn.existsUnique_continuousMap_lifts (isCoveringMapOn_tantibar_five c₀) hbk
      (a₀ := ⟨_, hpk⟩) (e₀ := ψ _) (by rw [hbk_val _ hpk]; exact hψ.anti _ hpk)
      (fun a => by
        rw [hbk_val a.1 a.2]
        exact havoid a.1 (U_mono (Nat.le_succ k) a.2))
  let incl : C(↥(U X k), ↥(U X (k + 1))) :=
    ⟨fun z => ⟨z.1, U_mono (Nat.le_succ k) z.2⟩, by fun_prop⟩
  have hFlift : F.comp incl = Fk := by
    refine huniqk _ ⟨?_, ?_⟩
    · show F (incl ⟨_, hpk⟩) = ψ _
      rw [show incl ⟨((X + 1 : ℝ) : ℂ), hpk⟩ = ⟨((X + 1 : ℝ) : ℂ), hp⟩ from rfl, hFp]
    · funext z
      have h1 : hbk z = hb (incl z) := by
        show ψ (sig z.1) = hb (incl z)
        show ψ (sig z.1) = hb ⟨z.1, U_mono (Nat.le_succ k) z.2⟩
        rw [hb_val z.1 (U_mono (Nat.le_succ k) z.2)]
      rw [h1]
      exact congr_fun hFg (incl z)
  have hψlift : (⟨(U X k).domRestrict ψ, hψ.cont.domRestrict⟩ : C(↥(U X k), ℂ)) = Fk := by
    refine huniqk _ ⟨rfl, ?_⟩
    funext z
    exact hψ.anti z.1 z.2
  have hLift : ∀ (w : ℂ) (hw : w ∈ U X k),
      F ⟨w, U_mono (Nat.le_succ k) hw⟩ = ψ w := by
    intro w hw
    have h2 := congr_fun (congr_arg (fun g : C(↥(U X k), ℂ) => (g : ↥(U X k) → ℂ))
      (hFlift.trans hψlift.symm)) ⟨w, hw⟩
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, incl, Set.domRestrict_apply,
      Function.comp_apply] using h2
  refine ⟨fun z => if h : z ∈ U X (k + 1) then F ⟨z, h⟩ else 0, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      have hw1 : sig w ∈ U X (k + 1) := sig_mem_U hw
      rw [dif_pos hw, dif_pos hw1, hLift (sig w) (hSmem w hw)]
      exact congr_fun hFg ⟨w, hw⟩
    · intro w hw
      have hwk : w ∈ U X k := by
        rw [mem_U]
        have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
        linarith
      rw [dif_pos (U_mono (Nat.le_succ k) hwk), hLift w hwk]
      exact hψ.far w hw
    · rw [continuousOn_iff_continuous_domRestrict]
      have hres : (U X (k + 1)).domRestrict
          (fun z : ℂ => if h : z ∈ U X (k + 1) then F ⟨z, h⟩ else 0) = ⇑F := by
        funext z
        rw [Set.domRestrict_apply]
        exact dif_pos z.2
      rw [hres]
      exact F.continuous
  · intro w hw
    have hw1 : w ∈ U X (k + 1) := U_mono (Nat.le_succ k) hw
    simp only [dif_pos hw1]
    exact hLift w hw

end

end Work.GATE2.PL
