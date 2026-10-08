/-
# `Work.PSU3.StageB.ThetaBarPrep` — coordinates for Peterfalvi Ch. VII §3 (2)

This module collects the elementary infrastructure needed for the computation of
`bar (f (ω s^a))` in Peterfalvi II, Ch. VII, §3, step (2):

* `zeta_commutes_t`, `t_conj_zeta`, `t_conj_zeta_inv`, `zeta_conj_Q0` — the element `ζ` of the
  frame lies in `W ≤ C_D(t)` and centralises `Q₀`;
* `qact d x = d⁻¹ x d` — the conjugation action of `fr.KW ≤ D` on `Q` (this is Peterfalvi's
  right action `x^d`), with `qact_bar` the formula `bar (x^d) = κ(d) · bar x`;
* `fcan_qact_of_t_conj` — **H3** for a `d ∈ KW` with `t d t = d`:
  `f (x^d) = f(x)^d`;
* `fcan_inv_omQ` — from `f(ω) = ω^{-ζ}` (H2 + H3) one gets `f(ω⁻¹) = ω^{ζ⁻¹}`;
* `ne_one_mul_sconj`, `ne_one_sconj_mul_inv` — the side conditions of H6.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Theta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3
open Classical

namespace Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## §1. Elementary facts about `ζ` -/

section Zeta

variable (fr : CoarseFrame H Q t n)

lemma zeta_commutes_t : t * (fr.ζ : G) = (fr.ζ : G) * t := by
  have hc : (fr.ζ : G) ∈ centD H t := (le_W_iff.mp fr.ζ_mem_W).1
  rw [centD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hc
  exact hc.2 t (by simp)

lemma t_conj_zeta (h : IsSplitRankOne H Q t) : t * (fr.ζ : G) * t = (fr.ζ : G) := by
  rw [zeta_commutes_t fr, mul_assoc, mul_self_eq_one h, mul_one]

lemma t_conj_zeta_inv (h : IsSplitRankOne H Q t) :
    t * (fr.ζ : G)⁻¹ * t = (fr.ζ : G)⁻¹ := by
  have h1 : (t * (fr.ζ : G) * t)⁻¹ = t * (fr.ζ : G)⁻¹ * t := by
    rw [mul_inv_rev, mul_inv_rev, inv_eq_self h]
    group
  rw [← h1, t_conj_zeta fr h]

/-- `ζ` centralises `Q₀`. -/
lemma zeta_conj_Q0 {z : G} (hz : z ∈ fr.Q0) : (fr.ζ : G)⁻¹ * z * (fr.ζ : G) = z := by
  obtain ⟨y, hy, hyz⟩ := fr.zc_surj z hz
  rw [← hyz]
  exact fr.act_zc_ζ y hy

lemma zeta_inv_conj_Q0 {z : G} (hz : z ∈ fr.Q0) : (fr.ζ : G) * z * (fr.ζ : G)⁻¹ = z := by
  have h := zeta_conj_Q0 fr hz
  have h2 := congrArg (fun w : G => (fr.ζ : G) * w * (fr.ζ : G)⁻¹) h
  rw [← h2]
  group

/-- `t`-conjugation fixes `ζ⁻¹ζ⁻¹ζ⁻¹` (the value of `h(ω⁻¹)` in Ch. VII §3 (1)). -/
lemma t_conj_zeta_inv_cube (h : IsSplitRankOne H Q t) :
    t * ((fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹) * t =
      (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ := by
  have ht := mul_self_eq_one h
  have h1 : t * ((fr.ζ : G)⁻¹ * ((fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹)) * t =
      (t * (fr.ζ : G)⁻¹ * t) * (t * ((fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹) * t) :=
    conj_mul_self ht _ _
  have h2 : t * ((fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹) * t =
      (t * (fr.ζ : G)⁻¹ * t) * (t * (fr.ζ : G)⁻¹ * t) := conj_mul_self ht _ _
  rw [show (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹ =
      (fr.ζ : G)⁻¹ * ((fr.ζ : G)⁻¹ * (fr.ζ : G)⁻¹) from by group, h1, h2,
    t_conj_zeta_inv fr h]

end Zeta

/-! ## §2. The conjugation action of `KW` on `Q` -/

section Qact

variable (fr : CoarseFrame H Q t n) (h : IsSplitRankOne H Q t)

/-- The conjugation action `x ↦ d⁻¹ x d` of `d ∈ KW ≤ D` on `Q`. -/
def qact (d : fr.KW) (x : ↥Q) : ↥Q :=
  ⟨(d : G)⁻¹ * (x : G) * (d : G), by
    have hc := conj_mem_of_mem h (H.inv_mem (twoPoint_le_left H t (fr.KW_le d.2))) x.2
    simpa using hc⟩

@[simp] lemma qact_coe (d : fr.KW) (x : ↥Q) :
    ((qact fr h d x : ↥Q) : G) = (d : G)⁻¹ * (x : G) * (d : G) := rfl

@[simp] lemma qact_one (d : fr.KW) : qact fr h d (1 : ↥Q) = 1 := by
  apply Subtype.ext
  simp [qact_coe]

@[simp] lemma qact_one_apply (x : ↥Q) : qact fr h (1 : fr.KW) x = x := by
  apply Subtype.ext
  simp [qact_coe]

lemma qact_mul (d : fr.KW) (x y : ↥Q) :
    qact fr h d (x * y) = qact fr h d x * qact fr h d y := by
  apply Subtype.ext
  simp only [qact_coe, Subgroup.coe_mul]
  group

lemma qact_inv (d : fr.KW) (x : ↥Q) : qact fr h d x⁻¹ = (qact fr h d x)⁻¹ := by
  apply Subtype.ext
  simp only [qact_coe, Subgroup.coe_inv]
  group

lemma qact_qact (d e : fr.KW) (x : ↥Q) :
    qact fr h d (qact fr h e x) = qact fr h (e * d) x := by
  apply Subtype.ext
  simp only [qact_coe, Subgroup.coe_mul]
  group

/-- The bar of a conjugate: `bar (x^d) = κ(d) · bar x`. -/
lemma qact_bar (d : fr.KW) (x : ↥Q) :
    Multiplicative.toAdd (fr.bar (qact fr h d x)) =
      ((fr.κ d : (E n)ˣ) : E n) * Multiplicative.toAdd (fr.bar x) :=
  fr.act_bar d x (qact fr h d x) rfl

/-- **H3** for a `d ∈ KW` with `t d t = d`: `f (x^d) = f(x)^d` (i.e. `f(qact d x) = qact d (f x)`),
since `d^t = d`. -/
lemma fcan_qact_of_t_conj (d : fr.KW) (hd : t * (d : G) * t = (d : G)) (x : ↥Q)
    (hx : (x : G) ≠ 1) : fcan h (qact fr h d x) = qact fr h d (fcan h x) := by
  have hdD : (d : G) ∈ twoPoint H t := fr.KW_le d.2
  obtain ⟨xa, hxa, hf, -, -⟩ := canon_conj_fun h hx ⟨(d : G), hdD⟩
  have hsub : xa = qact fr h d x := Subtype.ext (by rw [hxa]; rfl)
  have hft : t * ((⟨(d : G), hdD⟩ : ↥(twoPoint H t)) : G) * t =
      ((⟨(d : G), hdD⟩ : ↥(twoPoint H t)) : G) := hd
  rw [hsub, hft] at hf
  exact Subtype.ext hf

lemma fcan_qact_zeta (x : ↥Q) (hx : (x : G) ≠ 1) :
    fcan h (qact fr h fr.ζ x) = qact fr h fr.ζ (fcan h x) :=
  fcan_qact_of_t_conj fr h fr.ζ (t_conj_zeta fr h) x hx

lemma fcan_qact_zeta_inv (x : ↥Q) (hx : (x : G) ≠ 1) :
    fcan h (qact fr h fr.ζ⁻¹ x) = qact fr h fr.ζ⁻¹ (fcan h x) := by
  have hd : t * ((fr.ζ⁻¹ : fr.KW) : G) * t = ((fr.ζ⁻¹ : fr.KW) : G) := by
    simpa using t_conj_zeta_inv fr h
  exact fcan_qact_of_t_conj fr h fr.ζ⁻¹ hd x hx

/-- `ζ⁻¹` acts trivially on `Q₀`. -/
lemma qact_zeta_inv_of_mem_Q0 {z : ↥Q} (hz : (z : G) ∈ fr.Q0) :
    qact fr h fr.ζ⁻¹ z = z := by
  apply Subtype.ext
  simpa using zeta_inv_conj_Q0 fr hz

end Qact

/-! ## §2b. The canonical data of `s^{a⁻¹}` -/

section SconjInv

variable (fr : CoarseFrame H Q t n) (h : IsSplitRankOne H Q t)

/-- `t`-conjugating `a⁻¹` gives `a` back, for `a ∈ Ksub H t`. -/
lemma t_conj_KW_inv (h : IsSplitRankOne H Q t) (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    t * ((a⁻¹ : fr.KW) : G) * t = (a : G) := by
  have hai : ((a⁻¹ : fr.KW) : G) ∈ Ksub H t := (Ksub H t).inv_mem ha
  simpa using tconj_eq_inv h fr hai

/-- The canonical data of `s^{a⁻¹}`: `f` and `g` take the value `s^a`, and `h` is `a⁻²`. -/
lemma canon_sconj_inv (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    fcan h (sconj fr a⁻¹ ((Ksub H t).inv_mem ha)) = sconj fr a ha ∧
    gcan h (sconj fr a⁻¹ ((Ksub H t).inv_mem ha)) = sconj fr a ha ∧
    (hcan h (sconj fr a⁻¹ ((Ksub H t).inv_mem ha)) : G) =
      ((a⁻¹ : fr.KW) : G) * ((a⁻¹ : fr.KW) : G) := by
  have hai : ((a⁻¹ : fr.KW) : G) ∈ Ksub H t := (Ksub H t).inv_mem ha
  have hc := canon_sconj fr h a⁻¹ hai
  refine ⟨?_, ?_, hc.2.2⟩
  · apply Subtype.ext
    rw [hc.1, sconjInv_coe, sconj_coe]
    simp
  · apply Subtype.ext
    rw [hc.2.1, sconjInv_coe, sconj_coe]
    simp

lemma t_conj_canon_sconj_inv (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    t * (hcan h (sconj fr a⁻¹ ((Ksub H t).inv_mem ha)) : G) * t =
      (a : G) * (a : G) := by
  have hai : ((a⁻¹ : fr.KW) : G) ∈ Ksub H t := (Ksub H t).inv_mem ha
  have hc := (canon_sconj fr h a⁻¹ hai).2.2
  rw [hc, conj_mul_self (mul_self_eq_one h), t_conj_KW_inv fr h a ha]

end SconjInv

/-! ## §3. `f(ω⁻¹) = ω^{ζ⁻¹}` and the H6 side conditions -/

section Omega

variable (fr : CoarseFrame H Q t n) (h : IsSplitRankOne H Q t)

/-- **`f(ω⁻¹) = ω^{ζ⁻¹}`.**  From `f(ω) = ω^{-ζ}` (hypothesis `hfω`), H2 gives
`f(f(ω)) = ω` and H3 (`ζ^t = ζ`) turns this into `f(ω⁻¹)^ζ = ω`. -/
lemma fcan_inv_omQ {ω : G} (hω : OmegaHyp fr ω)
    (hfω : (fcan h (omQ fr hω) : G) = (fr.ζ : G)⁻¹ * ω⁻¹ * (fr.ζ : G)) :
    fcan h ((omQ fr hω)⁻¹) = qact fr h fr.ζ⁻¹ (omQ fr hω) := by
  have hx1 : ((omQ fr hω : ↥Q) : G) ≠ 1 := omQ_ne_one fr hω
  have hxi1 : (((omQ fr hω)⁻¹ : ↥Q) : G) ≠ 1 := by simpa using hx1
  have hF1 : fcan h (omQ fr hω) = qact fr h fr.ζ ((omQ fr hω)⁻¹) := by
    apply Subtype.ext
    rw [qact_coe, Subgroup.coe_inv]
    exact hfω
  have h2 : (fcan h (fcan h (omQ fr hω)) : G) = ((omQ fr hω : ↥Q) : G) :=
    (fcan_fcan h hx1).1
  rw [hF1, fcan_qact_zeta fr h _ hxi1] at h2
  have h3 : qact fr h fr.ζ (fcan h ((omQ fr hω)⁻¹)) = omQ fr hω := Subtype.ext h2
  calc fcan h ((omQ fr hω)⁻¹)
      = qact fr h fr.ζ⁻¹ (qact fr h fr.ζ (fcan h ((omQ fr hω)⁻¹))) := by
        rw [qact_qact, mul_inv_cancel, qact_one_apply]
    _ = qact fr h fr.ζ⁻¹ (omQ fr hω) := by rw [h3]

/-- `x ∉ Q₀` implies `x⁻¹ ∉ Q₀`. -/
lemma inv_not_mem_Q0 {x : G} (hx : x ∉ fr.Q0) : x⁻¹ ∉ fr.Q0 :=
  fun h => hx (by simpa using fr.Q0.inv_mem h)

/-- `ω ∉ Q₀` for the frame coordinate of `ω`. -/
lemma omQ_not_mem_Q0 {ω : G} (hω : OmegaHyp fr ω) :
    ((omQ fr hω : ↥Q) : G) ∉ fr.Q0 :=
  fun h => hω.2.1 (by simpa [omQ_coe fr hω] using h)

/-- If `x ∉ Q₀` and `z ∈ Q₀` then `x z ≠ 1`. -/
lemma ne_one_mul_of_not_mem_Q0 {x z : ↥Q} (hx : (x : G) ∉ fr.Q0)
    (hz : (z : G) ∈ fr.Q0) : ((x * z : ↥Q) : G) ≠ 1 := by
  intro hcon
  have hmul : x * z = 1 := Subtype.ext hcon
  have hxz : x = z⁻¹ := eq_inv_of_mul_eq_one_left hmul
  exact hx (by rw [hxz, Subgroup.coe_inv]; exact fr.Q0.inv_mem hz)

/-- If `x ∉ Q₀` and `z ∈ Q₀` then `z x ≠ 1`. -/
lemma ne_one_mul_left_of_not_mem_Q0 {x z : ↥Q} (hx : (x : G) ∉ fr.Q0)
    (hz : (z : G) ∈ fr.Q0) : ((z * x : ↥Q) : G) ≠ 1 := by
  intro hcon
  have hmul : z * x = 1 := Subtype.ext hcon
  have hxz : x = z⁻¹ := eq_inv_of_mul_eq_one_right hmul
  exact hx (by rw [hxz, Subgroup.coe_inv]; exact fr.Q0.inv_mem hz)

/-- `ω · s^a ≠ 1` (this is the H6 side condition for `x = ω`, `y = s^a`). -/
lemma ne_one_mul_sconj (h : IsSplitRankOne H Q t) {ω : G} (hω : OmegaHyp fr ω) (a : fr.KW)
    (ha : (a : G) ∈ Ksub H t) :
    (((omQ fr hω) * sconj fr a ha : ↥Q) : G) ≠ 1 :=
  ne_one_mul_of_not_mem_Q0 fr (omQ_not_mem_Q0 fr hω) (sconj_mem_Q0 fr a ha)

/-- `s^{a⁻¹} · ω⁻¹ ≠ 1` (this is the H6 side condition for `x = s^{a⁻¹}`, `y = ω⁻¹`). -/
lemma ne_one_sconj_inv_mul (h : IsSplitRankOne H Q t) {ω : G} (hω : OmegaHyp fr ω)
    (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    ((sconj fr a⁻¹ ((Ksub H t).inv_mem ha) * (omQ fr hω)⁻¹ : ↥Q) : G) ≠ 1 :=
  ne_one_mul_left_of_not_mem_Q0 fr (inv_not_mem_Q0 fr (omQ_not_mem_Q0 fr hω))
    (sconj_mem_Q0 fr a⁻¹ _)

/-- `ω⁻¹ · s^{a⁻¹} ≠ 1` (the H6 side condition for `x = ω⁻¹`, `y = s^{a⁻¹}`). -/
lemma ne_one_inv_mul_sconj_inv (h : IsSplitRankOne H Q t) {ω : G} (hω : OmegaHyp fr ω)
    (a : fr.KW) (ha : (a : G) ∈ Ksub H t) :
    (((omQ fr hω)⁻¹ * sconj fr a⁻¹ ((Ksub H t).inv_mem ha) : ↥Q) : G) ≠ 1 :=
  ne_one_mul_of_not_mem_Q0 fr (inv_not_mem_Q0 fr (omQ_not_mem_Q0 fr hω))
    (sconj_mem_Q0 fr a⁻¹ _)

end Omega

end Work.PSU3.StageB
