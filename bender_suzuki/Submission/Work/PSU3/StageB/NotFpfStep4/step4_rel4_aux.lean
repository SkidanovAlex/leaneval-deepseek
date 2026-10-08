/-
# Auxiliary lemmas for `step4_rel4` (Peterfalvi II, Ch. VII §4)

Peterfalvi II Ch. VII §4, "Setting for the computation" (pp. 278-280): let `ω ∈ Q ∖ Q₀` with
`f(ω) = ω^{-ζ}` and `h(ω) = ζ³η^{-1}`, where `η ∈ V = C_D(t)` centralises `ω` and `ζ`.  For
`a ∈ K` the source computes the relation (4)

  `a² · \overline{f(ω s^a)} = ζ^{-1} · \overline{f(ω s^a)}^{η} + \barω`

by evaluating `f(ω^{-1} s^{a^{-1}})` in two ways: with the recursion (2) of §2 and with the
recursion (3).  This file collects the elementary group-theoretic ingredients of that
computation:

* `f(ω^{-1}) = ζ ω ζ^{-1}`, `g(ω^{-1}) = ζ^{-1} ω ζ`, `h(ω^{-1}) = η (ζ³)^{-1}`;
* `ω⁻¹ = ω · zc α` (as `ω⁴ = 1`);
* `ζ` acts trivially on `Q₀`, hence on every `s^a`;
* the canonical data of `s^{a^{-1}}` and its `t`-conjugate;
* the `bar`-images of the conjugates by `ζ` (via `act_bar`).

Nothing here depends on the semilinearity of the `η`-action.

## Derivation sketch (for the two consumers)

Write `c := (fr.κ fr.ζ : E n)`, `A := kElF fr a` (so `κ A = fval a`), and let
`X := fcan hS.split (ω * sconjF fr a)`.

**Left branch (§2 (2) = `fcan_mul_zcQF`).**  Apply `fcan_mul_zcQF hS fr` with `x := ω⁻¹` and
`u := nmF fr a⁻¹` (so `zcQF fr u = sconjF fr a⁻¹` and `zcQF fr u⁻¹ = sconjF fr a`).  With
`hcan_sconjF_inv` and `t_hcan_sconjF_inv` the surrounding block is `(A*A)⁻¹ · (·) · (A*A)`,
whose `bar` is `κ(A*A) = (fval a)^2` times the `bar` of the middle term (`qconj_KW_bar`,
`kappa_kElF_sq`).  The middle term is `f(f(ω⁻¹)·sconjF fr a)`, and `fcan_omega_inv` rewrites
`f(ω⁻¹) = ζωζ⁻¹`, so it is `f(ζ(ω s^a)ζ⁻¹) = f(qconj (zetaD fr)⁻¹ (ω s^a))`; `fcan_qconj`
with `(zetaD fr)⁻¹` (`t ζ⁻¹ t = ζ⁻¹`) turns this into `ζ · X · ζ⁻¹`, whose `bar` is
`c⁻¹ · toAdd(bar X)` (`bar_qconj_zetaD_inv`).

**Right branch (§2 (3) = `canon_mul_fun` with `x := sconjF fr a⁻¹`, `y := ω⁻¹`).**  Note
`sconjF fr a⁻¹ * ω⁻¹ = ω⁻¹ * sconjF fr a⁻¹` (`sconjF_comm`).  There `f(s^{a⁻¹}) = s^a`
(`fcan_sconjF`), `g(ω⁻¹) = ζ⁻¹ωζ` (`gcan_omega_inv`), `f(ω⁻¹) = ζωζ⁻¹` (`fcan_omega_inv`),
`h(ω⁻¹) = η(ζ³)⁻¹` (`hcan_omega_inv`) and `t h(ω⁻¹) t = h(ω⁻¹)` (`t_conj_of_mem_centD`).
The middle term is `f(s^a·ζ⁻¹ωζ) = f((ω s^a)^ζ) = qconj (zetaD fr) X` (`fcan_qconj`), and the
outer block `h⁻¹·(·)·h = ζ³(·)^ηζ⁻³` gets `bar` coefficient `(κ ζ)⁻³` (`bar_qconj_zetaD3_inv`)
times `toAdd(bar (qconj η X))` — the inner conjugation by `ζ` contributing the extra `c`
(`bar_qconj_zetaD`, and `hcentζ` to move `η` past `ζ`).  The remaining term is `f(ω⁻¹)`, whose
`bar` is `c⁻¹ · toAdd (fr.bar ω)` (`bar_qconj_zetaD_inv`).
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.ThetaOmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.NotFpfStep4

open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

@[simp] lemma zetaD_coe (fr : CoarseFrame H Q t n) : (zetaD fr : G) = fr.ζ := rfl

lemma t_mul_self (hS : PSU3Hyp H Q t) : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split

lemma t_inv (hS : PSU3Hyp H Q t) : t⁻¹ = t := Work.RankOneUniqueness.inv_eq_self hS.split

/-- `t`-conjugation is multiplicative. -/
lemma t_conj_mul (hS : PSU3Hyp H Q t) (x y : G) :
    t * (x * y) * t = (t * x * t) * (t * y * t) :=
  Work.PSU3.StageB.conj_mul_self (t_mul_self hS) x y

/-- `t`-conjugation of powers. -/
lemma t_conj_pow (hS : PSU3Hyp H Q t) (x : G) (k : ℕ) :
    t * x ^ k * t = (t * x * t) ^ k := by
  have h := map_pow (MulAut.conj t) x k
  simpa [MulAut.conj_apply, t_inv hS] using h

/-! ## Elementary facts about `Q₀` and `zcQF` -/

lemma zcQF_mem (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((zcQF fr u : Q) : G) ∈ fr.Q0 := by
  rw [zcQF_coe]
  exact fr.zc_mem (fval u) u.2

lemma bar_zcQF_eq_one (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    fr.bar (zcQF fr u) = 1 :=
  bar_eq_one_of_mem_Q0 fr (zcQF_mem fr u)

lemma sconjF_mem_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    ((sconjF fr u : Q) : G) ∈ fr.Q0 := by
  rw [sconjF_eq_zcQF fr hS u]
  exact zcQF_mem fr (nmF fr u)

lemma bar_sconjF_eq_one (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    fr.bar (sconjF fr u) = 1 :=
  bar_eq_one_of_mem_Q0 fr (sconjF_mem_Q0 hS fr u)

/-- `zc u` is central in `Q`. -/
lemma zcQF_comm (fr : CoarseFrame H Q t n) (u : ↥(FX n)) (x : ↥Q) :
    zcQF fr u * x = x * zcQF fr u := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact fr.Q0_central _ (zcQF_mem fr u) _ x.2

/-- `s^u` is central in `Q`. -/
lemma sconjF_comm (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) (x : ↥Q) :
    sconjF fr u * x = x * sconjF fr u := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact fr.Q0_central _ (sconjF_mem_Q0 hS fr u) _ x.2

/-! ## Conjugation by `ζ` acts trivially on `Q₀` -/

lemma zeta_conj_Q0 (fr : CoarseFrame H Q t n) {z : G} (hz : z ∈ fr.Q0) :
    (fr.ζ : G)⁻¹ * z * (fr.ζ : G) = z := by
  obtain ⟨y, hy, hyz⟩ := fr.zc_surj z hz
  rw [← hyz]
  exact fr.act_zc_ζ y hy

lemma zeta_conj_Q0' (fr : CoarseFrame H Q t n) {z : G} (hz : z ∈ fr.Q0) :
    (fr.ζ : G) * z * (fr.ζ : G)⁻¹ = z := by
  calc (fr.ζ : G) * z * (fr.ζ : G)⁻¹
      = (fr.ζ : G) * ((fr.ζ : G)⁻¹ * z * (fr.ζ : G)) * (fr.ζ : G)⁻¹ := by
        rw [zeta_conj_Q0 fr hz]
    _ = z := by group

/-- `qconj` by `ζ` fixes the elements of `Q₀`. -/
lemma qconj_zetaD_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {z : ↥Q}
    (hz : (z : G) ∈ fr.Q0) : qconj hS.split (zetaD fr) z = z := by
  apply Subtype.ext
  rw [qconj_coe, zetaD_coe]
  exact zeta_conj_Q0 fr hz

/-- `qconj` by `ζ⁻¹` fixes the elements of `Q₀`. -/
lemma qconj_zetaD_inv_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {z : ↥Q}
    (hz : (z : G) ∈ fr.Q0) : qconj hS.split ((zetaD fr)⁻¹) z = z := by
  apply Subtype.ext
  rw [qconj_coe]
  simp only [zetaD_coe, Subgroup.coe_inv, inv_inv]
  exact zeta_conj_Q0' fr hz

lemma qconj_zetaD_sconjF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    qconj hS.split (zetaD fr) (sconjF fr u) = sconjF fr u :=
  qconj_zetaD_Q0 hS fr (sconjF_mem_Q0 hS fr u)

lemma qconj_zetaD_inv_sconjF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    qconj hS.split ((zetaD fr)⁻¹) (sconjF fr u) = sconjF fr u :=
  qconj_zetaD_inv_Q0 hS fr (sconjF_mem_Q0 hS fr u)

/-! ## `ω⁻¹ = ω · zc α` -/

/-- `ω⁻¹ = ω · zc α` since `ω² = zc α` is an involution. -/
lemma omega_mul_zcQF_eq_inv (fr : CoarseFrame H Q t n) {ω : ↥Q} {α : ↥(FX n)}
    (hsq : ω * ω = zcQF fr α) : ω * zcQF fr α = ω⁻¹ := by
  have hcomm := zcQF_comm fr α ω
  have hu2 : zcQF fr α * zcQF fr α = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact Q0_mul_self fr (zcQF_mem fr α)
  have h2 : (ω * zcQF fr α) * ω = 1 := by
    calc (ω * zcQF fr α) * ω = ω * (zcQF fr α * ω) := by rw [mul_assoc]
      _ = ω * (ω * zcQF fr α) := by rw [hcomm]
      _ = (ω * ω) * zcQF fr α := (mul_assoc _ _ _).symm
      _ = zcQF fr α * zcQF fr α := by rw [hsq]
      _ = 1 := hu2
  exact eq_inv_of_mul_eq_one_left h2

/-! ## The canonical data of `ω⁻¹` -/

lemma fcan_omega_inv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    (hsq : ω * ω = zcQF fr α) :
    (fcan hS.split ω⁻¹ : G) = (fr.ζ : G) * (ω : G) * (fr.ζ : G)⁻¹ := by
  have hω1 : (ω : G) ≠ 1 := fun h => hω (by rw [h]; exact Q0_one_mem fr)
  have hfx1 : ((fcan hS.split ω : ↥Q) : G) ≠ 1 := fcan_ne_one hS.split hω1
  have hcoe : ((ω * zcQF fr α : ↥Q) : G) =
      (fr.ζ : G) * (fcan hS.split ω : G) * (fr.ζ : G)⁻¹ := by
    rw [hf, qconj_coe, zetaD_coe]
    group
  have hx1 : ((ω * zcQF fr α : ↥Q) : G) ≠ 1 := by
    rw [hcoe]
    intro hc
    refine hfx1 ?_
    have h2 := congrArg (fun z => (fr.ζ : G)⁻¹ * z * (fr.ζ : G)) hc
    simpa [mul_assoc] using h2
  have hconj := fcan_qconj hS.split hx1 (zetaD fr)
  rw [← hf] at hconj
  rw [(fcan_fcan hS.split hω1).1] at hconj
  simp only [zetaD_coe] at hconj
  rw [t_zeta_t hS.split fr] at hconj
  have hfx : (fcan hS.split (ω * zcQF fr α) : G) =
      (fr.ζ : G) * (ω : G) * (fr.ζ : G)⁻¹ := by
    rw [hconj]
    group
  rw [← omega_mul_zcQF_eq_inv fr hsq, hfx]

lemma gcan_omega_inv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    (hsq : ω * ω = zcQF fr α) :
    (gcan hS.split ω⁻¹ : G) = (fr.ζ : G)⁻¹ * (ω : G) * (fr.ζ : G) := by
  have hω1 : (ω : G) ≠ 1 := fun h => hω (by rw [h]; exact Q0_one_mem fr)
  have h1 := gcan_inv hS.split hω1
  have hfc : (fcan hS.split ω : G) =
      (fr.ζ : G)⁻¹ * ((ω * zcQF fr α : ↥Q) : G) * (fr.ζ : G) := by
    rw [hf, qconj_coe, zetaD_coe]
  have hxinv : ((ω * zcQF fr α : ↥Q) : G)⁻¹ = (ω : G) := by
    rw [omega_mul_zcQF_eq_inv fr hsq, Subgroup.coe_inv, inv_inv]
  rw [h1, hfc]
  have h2 : ((fr.ζ : G)⁻¹ * ((ω * zcQF fr α : ↥Q) : G) * (fr.ζ : G))⁻¹ =
      (fr.ζ : G)⁻¹ * ((ω * zcQF fr α : ↥Q) : G)⁻¹ * (fr.ζ : G) := by group
  rw [h2, hxinv]

/-- `t`-conjugation of an element of `V = C_D(t)`. -/
lemma t_conj_of_mem_centD (hS : PSU3Hyp H Q t) {d : G} (hd : d ∈ centD H t) :
    t * d * t = d := by
  have hc : d * t = t * d := ((Subgroup.mem_inf.mp hd).2 t (Set.mem_singleton t)).symm
  calc t * d * t = t * (d * t) := by rw [mul_assoc]
    _ = t * (t * d) := by rw [hc]
    _ = (t * t) * d := (mul_assoc _ _ _).symm
    _ = d := by rw [t_mul_self hS, one_mul]

lemma hcan_omega_inv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {η : G} (hηV : η ∈ centD H t)
    (hh : (hcan hS.split ω : G) = (fr.ζ : G) ^ 3 * η⁻¹) :
    (hcan hS.split ω⁻¹ : G) = η * (((fr.ζ : G) ^ 3)⁻¹) := by
  have hω1 : (ω : G) ≠ 1 := fun h => hω (by rw [h]; exact Q0_one_mem fr)
  have h1 := hcan_inv hS.split hω1
  have htη : t * η * t = η := t_conj_of_mem_centD hS hηV
  have htz3 : t * (((fr.ζ : G) ^ 3)⁻¹) * t = (((fr.ζ : G) ^ 3)⁻¹) := by
    have hzinv : t * (fr.ζ : G)⁻¹ * t = (fr.ζ : G)⁻¹ := t_zeta_inv_t hS.split fr
    rw [← inv_pow]
    have h := t_conj_pow hS ((fr.ζ : G)⁻¹) 3
    rw [hzinv] at h
    exact h
  have hkey : ((fr.ζ : G) ^ 3 * η⁻¹)⁻¹ = η * (((fr.ζ : G) ^ 3)⁻¹) := by
    rw [mul_inv_rev, inv_inv]
  rw [h1, hh, hkey]
  calc t * (η * (((fr.ζ : G) ^ 3)⁻¹)) * t
      = (t * η * t) * (t * (((fr.ζ : G) ^ 3)⁻¹) * t) := t_conj_mul hS η _
    _ = η * (((fr.ζ : G) ^ 3)⁻¹) := by rw [htη, htz3]

/-! ## The canonical data of `s^{a^{-1}}` -/

lemma fcan_sconjF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    fcan hS.split (sconjF fr u) = sconjF fr u⁻¹ := by
  refine Subtype.ext ?_
  exact ((canon_sconj fr hS.split (kElF fr u) (kElF_mem_Ksub fr u)).1).trans
    (congrArg (fun z : ↥Q => (z : G)) (sconjInv_kElF fr u))

lemma gcan_sconjF (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (u : ↥(FX n)) :
    gcan hS.split (sconjF fr u) = sconjF fr u⁻¹ := by
  refine Subtype.ext ?_
  exact ((canon_sconj fr hS.split (kElF fr u) (kElF_mem_Ksub fr u)).2.1).trans
    (congrArg (fun z : ↥Q => (z : G)) (sconjInv_kElF fr u))

/-- The coerced form of `kElF_inv`. -/
lemma kElF_inv_coe (fr : CoarseFrame H Q t n) (a : ↥(FX n)) :
    ((kElF fr a⁻¹ : fr.KW) : G) = ((kElF fr a : fr.KW) : G)⁻¹ := by
  rw [kElF_inv, Subgroup.coe_inv]

/-- `h(s^{a^{-1}}) = (kElF a)^{-1} · (kElF a)^{-1}`. -/
lemma hcan_sconjF_inv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (a : ↥(FX n)) :
    (hcan hS.split (sconjF fr a⁻¹) : G) =
      ((kElF fr a : fr.KW) : G)⁻¹ * ((kElF fr a : fr.KW) : G)⁻¹ := by
  have h := (canon_sconj fr hS.split (kElF fr a⁻¹) (kElF_mem_Ksub fr a⁻¹)).2.2
  rw [kElF_inv_coe fr a] at h
  exact h

/-- `t · h(s^{a^{-1}}) · t = (kElF a)²`. -/
lemma t_hcan_sconjF_inv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (a : ↥(FX n)) :
    t * (hcan hS.split (sconjF fr a⁻¹) : G) * t =
      ((kElF fr a : fr.KW) : G) * ((kElF fr a : fr.KW) : G) := by
  have hd : ((kElF fr a : fr.KW) : G) ∈ Ksub H t := kElF_mem_Ksub fr a
  have h1 : t * ((kElF fr a : fr.KW) : G) * t = ((kElF fr a : fr.KW) : G)⁻¹ :=
    tconj_eq_inv hS.split fr hd
  have h2 : t * ((kElF fr a : fr.KW) : G)⁻¹ * t = ((kElF fr a : fr.KW) : G) := by
    have h3 := congrArg Inv.inv h1
    simp only [mul_inv_rev, inv_inv, t_inv hS] at h3
    simpa only [mul_assoc] using h3
  rw [hcan_sconjF_inv hS fr a,
    show t * (((kElF fr a : fr.KW) : G)⁻¹ * ((kElF fr a : fr.KW) : G)⁻¹) * t =
      (t * ((kElF fr a : fr.KW) : G)⁻¹ * t) * (t * ((kElF fr a : fr.KW) : G)⁻¹ * t) from
      t_conj_mul hS _ _, h2]

lemma kappa_kElF (fr : CoarseFrame H Q t n) (a : ↥(FX n)) :
    (fr.κ (kElF fr a) : E n) = fval a := by
  rw [kElF_kappa]

/-- `κ ((kElF a)²) = (fval a)²`. -/
lemma kappa_kElF_sq (fr : CoarseFrame H Q t n) (a : ↥(FX n)) :
    (fr.κ ((kElF fr a) * (kElF fr a)) : E n) = (fval a) ^ 2 := by
  rw [map_mul, Units.val_mul]
  simp only [kappa_kElF]
  rw [pow_two]

/-! ## `bar` of the conjugates by `ζ` -/

lemma qconj_KW_bar (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (d : fr.KW) (x : ↥Q) :
    Multiplicative.toAdd (fr.bar (qconj hS.split ⟨(d : G), fr.KW_le d.2⟩ x)) =
      (fr.κ d : E n) * Multiplicative.toAdd (fr.bar x) :=
  fr.act_bar d x _ (qconj_coe hS.split ⟨(d : G), fr.KW_le d.2⟩ x)

lemma bar_qconj_zetaD (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (x : ↥Q) :
    Multiplicative.toAdd (fr.bar (qconj hS.split (zetaD fr) x)) =
      (fr.κ fr.ζ : E n) * Multiplicative.toAdd (fr.bar x) :=
  qconj_KW_bar hS fr fr.ζ x

lemma bar_qconj_zetaD_inv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (x : ↥Q) :
    Multiplicative.toAdd (fr.bar (qconj hS.split ((zetaD fr)⁻¹) x)) =
      (fr.κ fr.ζ : E n)⁻¹ * Multiplicative.toAdd (fr.bar x) := by
  have h : ((qconj hS.split ((zetaD fr)⁻¹) x : ↥Q) : G) =
      (((fr.ζ : fr.KW)⁻¹ : fr.KW) : G)⁻¹ * (x : G) * (((fr.ζ : fr.KW)⁻¹ : fr.KW) : G) := by
    rw [qconj_coe]
    simp only [zetaD_coe, Subgroup.coe_inv]
  have h2 := fr.act_bar ((fr.ζ : fr.KW)⁻¹) x (qconj hS.split ((zetaD fr)⁻¹) x) h
  rw [h2, map_inv, Units.val_inv_eq_inv_val]

lemma bar_qconj_zetaD3_inv (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (x : ↥Q) :
    Multiplicative.toAdd (fr.bar (qconj hS.split (((zetaD fr)^3)⁻¹) x)) =
      (((fr.κ fr.ζ : E n))^3)⁻¹ * Multiplicative.toAdd (fr.bar x) := by
  have h : ((qconj hS.split (((zetaD fr)^3)⁻¹) x : ↥Q) : G) =
      ((((fr.ζ : fr.KW)^3)⁻¹ : fr.KW) : G)⁻¹ * (x : G) * ((((fr.ζ : fr.KW)^3)⁻¹ : fr.KW) : G) := by
    rw [qconj_coe]
    simp only [zetaD_coe, Subgroup.coe_pow, Subgroup.coe_inv]
  have h2 := fr.act_bar (((fr.ζ : fr.KW)^3)⁻¹) x (qconj hS.split (((zetaD fr)^3)⁻¹) x) h
  rw [h2, map_inv, map_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

end Work.PSU3.StageB.NotFpfStep4
