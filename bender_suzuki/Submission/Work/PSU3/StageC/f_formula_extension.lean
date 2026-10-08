/-
# `Work.PSU3.StageC.f_formula_extension`

Peterfalvi II Ch. VII §3 (5): the propagation of the formula `f(x,y) = (x/y, 1/y)` from
the centre `Q₀` and one coset `pQ₀` (`p ∉ Q₀`) to all of `Q`.

The proof follows the structure of §2–§3:

* the set `Good x := e (fcan x) = fMapTot (e x)` contains `Q₀` (`hQ0`) and `pQ₀` (`hbase`);
* `Good` is closed under `fcan` and under conjugation by `KW`;
* the recursion §2(2) (`fcan_mul_zcQ`) together with the model identity
  `torusAct_fMapTot_zel` (Lemma M of `FExtAux`) shows that the `Good`-set of a coset can be
  read off from the `Good`-set of the `fcan`-image coset; passing to `fcan` shows that a
  whole `Good` coset has a `Good` `fcan`-image coset;
* the arithmetic fact `exists_v_div_line` shows that the `fcan`-images of the coset `pQ₀`
  meet every `F*`-line of `E*`, which together with the `F*`-action covers every coset.
-/
import Mathlib
import Submission.Work.PSU3.StageC.FSuz
import Submission.Work.PSU3.StageC.FAsm
import Submission.Work.PSU3.StageC.ConjQ
import Submission.Work.PSU3.StageC.FExtAux
import Submission.Work.PSU3.StageB.Omega.API

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.PSU3.StageB

namespace Work.PSU3.StageC

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `barE x` is the image of `x ∈ Q` in `Q/Q₀ ≅ E n`, in additive notation. -/
noncomputable def barE (fr : Work.PSU3.CoarseFrame H Q t n) (x : Q) : Work.PSU3.E n :=
  Multiplicative.toAdd (fr.bar x)

/-- The points where the fine coordinates `e` carry `fcan` to `fMapTot`. -/
def Good (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (e : Q ≃* SZ (Work.PSU3.E n)) (x : Q) : Prop :=
  e (fcan hS.split x) = Work.PSU3.fMapTot (e x)

/-- All of a `Q₀`-coset is `Good`. -/
def GoodCoset (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (e : Q ≃* SZ (Work.PSU3.E n)) (c : Work.PSU3.E n) : Prop :=
  ∀ x : Q, barE fr x = c → Good hS fr e x

lemma barE_eq_zero_iff (fr : Work.PSU3.CoarseFrame H Q t n) {x : Q} :
    barE fr x = 0 ↔ (x : G) ∈ fr.Q0 := by
  have h1 : barE fr x = 0 ↔ fr.bar x = 1 := by
    rw [barE]
    constructor
    · intro h
      rw [← Equiv.symm_apply_apply Multiplicative.toAdd (fr.bar x), h]
      rfl
    · intro h
      rw [h]
      rfl
  rw [h1]
  exact fr.bar_eq_one_iff x

lemma barE_eq_zero_of_mem_Q0 (fr : Work.PSU3.CoarseFrame H Q t n) {x : Q}
    (hx : (x : G) ∈ fr.Q0) : barE fr x = 0 :=
  (barE_eq_zero_iff fr).mpr hx

/-- Two elements with the same `barE` differ by an element of `Q₀` on the right. -/
lemma eq_mul_Q0_of_barE_eq (fr : Work.PSU3.CoarseFrame H Q t n) {x y : Q}
    (h : barE fr x = barE fr y) :
    ∃ u : Q, (u : G) ∈ fr.Q0 ∧ x = y * u := by
  have hbar : fr.bar x = fr.bar y := Multiplicative.toAdd.injective h
  refine ⟨y⁻¹ * x, ?_, ?_⟩
  · rw [← fr.bar_eq_one_iff, map_mul, map_inv, hbar, inv_mul_cancel]
  · group

lemma e_zcQ_zel (fr : Work.PSU3.CoarseFrame H Q t n) (hS : Work.PSU3.PSU3Hyp H Q t)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    (v : Work.PSU3.E n) (hv : σE v = v) :
    e (zcQ fr v hv) = zel v hv :=
  e_zcQ fr hS hsq e μ hex hes heq v hv

theorem Good_one (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (e : Q ≃* SZ (Work.PSU3.E n)) : Good hS fr e 1 := by
  rw [Good]
  simp [fcan]

theorem Good_fcan (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (e : Q ≃* SZ (Work.PSU3.E n)) {x : Q} (hx : Good hS fr e x) :
    Good hS fr e (fcan hS.split x) := by
  rw [Good] at hx ⊢
  rcases eq_or_ne x 1 with rfl | hx1
  · simp [fcan]
  · rcases eq_or_ne (fcan hS.split x) 1 with hfx | hfx
    · rw [hfx]; simp [fcan]
    · have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hff : fcan hS.split (fcan hS.split x) = x :=
        Subtype.ext (fcan_fcan hS.split hx1').1
      rw [hff, hx]
      exact (fMapTot_invol (e x)).symm

theorem Good_conjQ (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (e : Q ≃* SZ (Work.PSU3.E n))
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {x : Q} (hx : Good hS fr e x) (d : fr.KW) :
    Good hS fr e (conjQ hS fr d x) := by
  rw [Good] at hx ⊢
  rcases eq_or_ne x 1 with rfl | hx1
  · rw [conjQ_one]; simp [fcan]
  · obtain ⟨d', hd', hκd'⟩ := tdt_KW hS fr d
    have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    rw [fcan_conjQ_eq hS fr hd' hx1', e_conjQ hS fr e heq d' (fcan hS.split x), hx,
      e_conjQ hS fr e heq d x, fMapTot_torusAct]
    congr 1
    apply Units.ext
    rw [hκd', sunit_inv_val]

theorem Good_mul_Q0 (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {x : Q} (hxQ : (x : G) ∉ fr.Q0) (hx : Good hS fr e x)
    (hcos : ∀ w : Q, (w : G) ∈ fr.Q0 → Good hS fr e (fcan hS.split x * w)) :
    ∀ v : Q, (v : G) ∈ fr.Q0 → Good hS fr e (x * v) := by
  intro v hv
  rcases eq_or_ne v 1 with rfl | hv1
  · simpa using hx
  · obtain ⟨u, hu, hzu⟩ := fr.zc_surj (v : G) hv
    have hu0 : u ≠ 0 := by
      intro h
      apply hv1
      apply Subtype.ext
      rw [Subgroup.coe_one, ← hzu, h, StageB.zc_zero fr]
    have hveq : v = zcQ fr u hu := Subtype.ext (by rw [zcQ_coe]; exact hzu.symm)
    rw [hveq]
    obtain ⟨A, hAK, hκA, hEq⟩ := fcan_mul_zcQ hS fr hsq hxQ u hu hu0
    have hz1 : σE u⁻¹ = u⁻¹ := by rw [map_inv₀, hu]
    have hY : Good hS fr e (fcan hS.split x * zcQ fr u⁻¹ hz1) :=
      hcos (zcQ fr u⁻¹ hz1) (by simpa using fr.zc_mem u⁻¹ hz1)
    rw [Good] at hY
    have hAun : (fr.κ A : (Work.PSU3.E n)ˣ) = (Units.mk0 (u⁻¹) (inv_ne_zero hu0)) := by
      apply Units.ext
      rw [hκA]
      rfl
    rw [Good]
    have hEqQ : fcan hS.split (x * zcQ fr u hu) =
        conjQ hS fr A (fcan hS.split (fcan hS.split x * zcQ fr u⁻¹ hz1)) *
          zcQ fr u⁻¹ hz1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, conjQ_coe]
      exact hEq
    rw [hEqQ, map_mul,
      e_conjQ hS fr e heq A (fcan hS.split (fcan hS.split x * zcQ fr u⁻¹ hz1)),
      hY, map_mul, hx, e_zcQ_zel fr hS hsq e μ hex hes heq u⁻¹ hz1, hAun]
    have hzx : (e x).x ≠ 0 := by
      rw [hex x]
      exact mul_ne_zero (Units.ne_zero μ) (fun h => hxQ ((barE_eq_zero_iff fr).mp h))
    have hkey : SZ.torusAct (Units.mk0 (u⁻¹) (inv_ne_zero hu0))
        (fMapTot (fMapTot (e x) * zel u⁻¹ hz1)) * zel u⁻¹ hz1 =
        fMapTot (e x * zel u hu) := by
      have h := torusAct_fMapTot_zel (e x) hzx (Units.mk0 (u⁻¹) (inv_ne_zero hu0)) hz1
      simpa [inv_inv] using h
    rw [show e (x * zcQ fr u hu) = e x * zel u hu from by
      rw [map_mul, e_zcQ_zel fr hS hsq e μ hex hes heq u hu]]
    exact hkey

/-- A whole `Good` coset has a `Good` `fcan`-image coset. -/
theorem Good_fcan_coset (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {x : Q} (hxQ : (x : G) ∉ fr.Q0) (hx : Good hS fr e x)
    (hcos : ∀ w : Q, (w : G) ∈ fr.Q0 → Good hS fr e (x * w)) :
    ∀ w : Q, (w : G) ∈ fr.Q0 → Good hS fr e (fcan hS.split x * w) := by
  have hx1 : (x : G) ≠ 1 :=
    fun h => hxQ (by rw [h]; exact (fr.mem_Q0_iff 1 Q.one_mem).mpr (by simp))
  have hfxQ : ((fcan hS.split x : Q) : G) ∉ fr.Q0 :=
    fun h => hxQ ((fcan_mem_Q0_iff hS fr x).mp h)
  have hff : ∀ w : Q, (w : G) ∈ fr.Q0 → Good hS fr e (fcan hS.split (fcan hS.split x) * w) := by
    intro w hw
    rw [show fcan hS.split (fcan hS.split x) = x from Subtype.ext (fcan_fcan hS.split hx1).1]
    exact hcos w hw
  exact Good_mul_Q0 hS fr hsq e μ hex hes heq hfxQ (Good_fcan hS fr e hx) hff

theorem f_formula_extension {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {p : Q} (hp : (p : G) ∉ fr.Q0)
    (hbase : ∀ u : Q, (u : G) ∈ fr.Q0 →
      e (Work.PSU3.StageB.fcan hS.split (p * u)) = Work.PSU3.fMapTot (e (p * u)))
    (hQ0 : ∀ u : Q, (u : G) ∈ fr.Q0 →
      e (Work.PSU3.StageB.fcan hS.split u) = Work.PSU3.fMapTot (e u)) :
    ∀ x : Q, e (Work.PSU3.StageB.fcan hS.split x) = Work.PSU3.fMapTot (e x) := by
  change ∀ x : Q, Good hS fr e x
  set w : Work.PSU3.E n := barE fr p with hwdef
  set β : Work.PSU3.E n := (e p).y with hβdef
  have hbarp : Multiplicative.toAdd (fr.bar p) = w := hwdef.symm
  have hμ0 : (μ : Work.PSU3.E n) ≠ 0 := Units.ne_zero μ
  have hw0 : w ≠ 0 := by
    rw [hwdef]; exact fun h => hp ((barE_eq_zero_iff fr).mp h)
  have hσ0 : ∀ x : Work.PSU3.E n, x ≠ 0 → σE x ≠ 0 :=
    fun x hx h => hx (σE.injective (by rw [h, map_zero]))
  have htr : β + σE β = ((μ : Work.PSU3.E n) * σE (μ : Work.PSU3.E n)) * (w * σE w) := by
    have h := (e p).herm
    rw [hex p, hbarp, ← hβdef, map_mul] at h
    rw [h]; ring
  have hc0 : GoodCoset hS fr e 0 := fun y hy => hQ0 y ((barE_eq_zero_iff fr).mp hy)
  have hcw : GoodCoset hS fr e w := by
    intro y hy
    obtain ⟨u, hu, hyu⟩ := eq_mul_Q0_of_barE_eq fr (hy.trans hwdef)
    rw [hyu]; exact hbase u hu
  -- the `fcan`-image cosets of the `p`-coset
  have hcdiv : ∀ v : Work.PSU3.E n, σE v = v →
      GoodCoset hS fr e (w / (β + v)) := by
    intro v hv
    set x : Q := p * zcQ fr v hv with hxdef
    have hbarx : Multiplicative.toAdd (fr.bar x) = w := by
      rw [hxdef, map_mul,
        show fr.bar (zcQ fr v hv) = 1 from
          (fr.bar_eq_one_iff _).mpr (by simpa using fr.zc_mem v hv),
        mul_one]
      exact hbarp
    have hxbase : Good hS fr e x := by
      rw [hxdef]; exact hbase (zcQ fr v hv) (by simpa using fr.zc_mem v hv)
    have hxQ0 : (x : G) ∉ fr.Q0 := by
      rw [hxdef]
      intro hcon
      apply hp
      have h2 : (p : G) = ((p * zcQ fr v hv : Q) : G) * (((zcQ fr v hv : Q) : G))⁻¹ := by
        rw [Subgroup.coe_mul]; group
      rw [h2]
      exact (fr.Q0).mul_mem hcon ((fr.Q0).inv_mem (fr.zc_mem v hv))
    have hxcos : ∀ w' : Q, (w' : G) ∈ fr.Q0 → Good hS fr e (x * w') := by
      intro w' hw'
      rw [hxdef, show (p * zcQ fr v hv) * w' = p * (zcQ fr v hv * w') from by group]
      exact hbase (zcQ fr v hv * w') (by
        simpa using (fr.Q0).mul_mem (fr.zc_mem v hv) hw')
    have hfc := Good_fcan_coset hS fr hsq e μ hex hes heq hxQ0 hxbase hxcos
    have hb : barE fr (fcan hS.split x) = w / (β + v) := by
      have hxne : e x ≠ 1 := by
        intro h
        have h1 : (e x).x = 0 := by rw [h]; rfl
        rw [hex x, hbarx] at h1
        exact mul_ne_zero hμ0 hw0 h1
      have hey : (e x).y = β + v := by
        rw [hxdef, map_mul, SZ.mul_y, e_zcQ_zel fr hS hsq e μ hex hes heq v hv]
        simp [zel, hβdef]
      have hfx1 : (e (fcan hS.split x)).x = (μ : Work.PSU3.E n) * (w / (β + v)) := by
        rw [show e (fcan hS.split x) = fMapTot (e x) from hxbase, fMapTot_of_ne_one hxne,
          SZ.fMap_x, hex x, hbarx, hey]
        ring
      have heq1 : (μ : Work.PSU3.E n) * (w / (β + v)) =
          (μ : Work.PSU3.E n) * barE fr (fcan hS.split x) :=
        hfx1.symm.trans (hex (fcan hS.split x))
      exact (mul_left_cancel₀ hμ0 heq1).symm
    intro y hy
    obtain ⟨u', hu', hyu'⟩ := eq_mul_Q0_of_barE_eq fr (hy.trans hb.symm)
    rw [hyu']; exact hfc u' hu'
  -- the `F*`-action on cosets
  have hmul : ∀ (f : Work.PSU3.E n), σE f = f → f ≠ 0 → ∀ c : Work.PSU3.E n,
      GoodCoset hS fr e c → GoodCoset hS fr e (f * c) := by
    intro f hf hf0 c hc
    obtain ⟨d, hd⟩ := fr.K_surj (Units.mk0 f hf0) (by simpa using hf)
    have hdk : (fr.κ d : Work.PSU3.E n) = f := by
      rw [hd]
      rfl
    intro y hy
    have hy2 : barE fr (conjQ hS fr d⁻¹ y) = c := by
      have h := fr.act_bar d⁻¹ y (conjQ hS fr d⁻¹ y) rfl
      simp only [barE] at h hy ⊢
      rw [h, map_inv, Units.val_inv_eq_inv_val, hdk, hy]
      rw [← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
    have hgood : Good hS fr e (conjQ hS fr d⁻¹ y) := hc _ hy2
    have hconj := Good_conjQ hS fr e heq hgood d
    rwa [show conjQ hS fr d (conjQ hS fr d⁻¹ y) = y from by
      rw [conjQ_conjQ, inv_mul_cancel,
        show conjQ hS fr 1 y = y from Subtype.ext (by rw [conjQ_coe]; simp)]] at hconj
  have hall : ∀ c : Work.PSU3.E n, GoodCoset hS fr e c := by
    intro c
    by_cases hc : c = 0
    · rwa [hc]
    · by_cases hline : w * σE c + σE w * c ≠ 0
      · obtain ⟨v, hv, f₀, hf₀, hf₀0, heqv⟩ :=
          exists_v_div_line w β (μ : Work.PSU3.E n) hw0 hμ0 htr c hc hline
        have h1 : GoodCoset hS fr e (w / (β + v)) := hcdiv v hv
        rw [heqv] at h1
        have h2 := hmul f₀⁻¹ (by rw [map_inv₀, hf₀]) (inv_ne_zero hf₀0) (f₀ * c) h1
        rwa [show f₀⁻¹ * (f₀ * c) = c from by rw [← mul_assoc, inv_mul_cancel₀ hf₀0, one_mul]] at h2
      · push_neg at hline
        have hwe : w * σE c = σE w * c := by
          have h := eq_neg_of_add_eq_zero_left hline
          rwa [CharTwo.neg_eq] at h
        have hwc0 : w / c ≠ 0 := div_ne_zero hw0 hc
        have hf : σE (w / c) = w / c := by
          rw [map_div₀, div_eq_div_iff (hσ0 c hc) hc]
          exact hwe.symm
        have h2 := hmul ((w / c)⁻¹) (by rw [map_inv₀, hf]) (inv_ne_zero hwc0) w hcw
        rwa [show (w / c)⁻¹ * w = c from by rw [inv_div]; exact div_mul_cancel₀ c hw0] at h2
  intro x
  exact hall (barE fr x) x rfl

end Work.PSU3.StageC
