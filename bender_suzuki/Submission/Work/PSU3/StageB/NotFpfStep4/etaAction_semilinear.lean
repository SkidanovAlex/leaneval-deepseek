import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.ThmF.ChV12.appV_semilinear
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.PSU3.StageB.NotFpfStep4

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## Elementary facts about `t` and about the elements of `V = C_D(t)`

The proof of `etaAction_semilinear` follows Peterfalvi II Ch. VII §4, "Setting for the
computation" (pp. 278–280): an element `η ∈ V = C_D(t)` acting on `Q` by conjugation induces a
semilinear map of `E ≅ Q/Q₀ ≅ GF(q²)`; when `η` fixes the class of an element of `bar`-image `1`
(hypothesis `hη1`, which comes from the model `PSU(3,ℓ)`), the induced map is a *ring*
automorphism `μ` of `E`, with `μ` also describing the action of `η` on `KW ≅ K₁W₁`
(hypothesis `hηN`).  This is the input to the computation (4)–(10) of the source. -/

section Basic

theorem eta_t_inv_eq_self (hS : PSU3Hyp H Q t) : t⁻¹ = t :=
  Work.RankOneUniqueness.inv_eq_self hS.split

theorem eta_t_mul_t (hS : PSU3Hyp H Q t) : t * t = 1 :=
  Work.RankOneUniqueness.mul_self_eq_one hS.split

/-- `η ∈ V = C_D(t)` commutes with `t`. -/
theorem eta_comm_t {η : G} (hηV : η ∈ centD H t) : η * t = t * η :=
  ((Subgroup.mem_inf.mp hηV).2 t (Set.mem_singleton t)).symm

theorem eta_inv_comm_t (hS : PSU3Hyp H Q t) {η : G} (hηV : η ∈ centD H t) :
    η⁻¹ * t = t * η⁻¹ := by
  have h : η * t = t * η := eta_comm_t hηV
  have h2 : (η * t)⁻¹ = (t * η)⁻¹ := congrArg Inv.inv h
  simp only [mul_inv_rev] at h2
  rw [eta_t_inv_eq_self hS] at h2
  exact h2.symm

theorem eta_comm_t_inv (hS : PSU3Hyp H Q t) {η : G} (hηV : η ∈ centD H t) :
    η * t⁻¹ = t⁻¹ * η := by
  rw [eta_t_inv_eq_self hS]
  exact eta_comm_t hηV

/-- `η ∈ V` viewed as an element of `D = twoPoint H t`. -/
abbrev etaD {η : G} (hηV : η ∈ centD H t) : ↥(twoPoint H t) :=
  ⟨η, centD_le_twoPoint (H := H) t hηV⟩

end Basic

/-! ## `η` preserves `Q₀ = ker bar` -/

section Q0

/-- An element of `D = twoPoint H t` preserves `Q₀` (both `D ≤ N(Q)` and the description
`Q₀ = {x ∈ Q | x² = 1}` are frame axioms/consequences). -/
theorem eta_conj_mem_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {d : G}
    (hd : d ∈ twoPoint H t) {z : G} (hz : z ∈ fr.Q0) : d⁻¹ * z * d ∈ fr.Q0 := by
  have hzQ : z ∈ Q := fr.Q0_le hz
  have hmem : d⁻¹ * z * d ∈ Q := by
    have h := conj_mem_of_mem hS.split (H.inv_mem (Work.Models.twoPoint_le_left H t hd)) hzQ
    simpa using h
  refine (fr.mem_Q0_iff _ hmem).mpr ?_
  have hsq : z ^ 2 = 1 := Q0_sq_eq_one fr hz
  calc (d⁻¹ * z * d) ^ 2 = d⁻¹ * z ^ 2 * d := by rw [pow_two, pow_two]; group
    _ = 1 := by rw [hsq]; group

theorem eta_qconj_mem_Q0 (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {η : G}
    (hηV : η ∈ centD H t) {z : ↥Q} (hz : (z : G) ∈ fr.Q0) :
    ((qconj hS.split (etaD hηV) z : ↥Q) : G) ∈ fr.Q0 := by
  rw [qconj_coe]
  exact eta_conj_mem_Q0 hS fr (centD_le_twoPoint (H := H) t hηV) hz

/-- `bar` of the `η`-conjugate depends only on `bar` of the argument. -/
theorem eta_bar_qconj_eq_of_bar_eq (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) {η : G}
    (hηV : η ∈ centD H t) {x y : ↥Q} (h : fr.bar x = fr.bar y) :
    fr.bar (qconj hS.split (etaD hηV) x) = fr.bar (qconj hS.split (etaD hηV) y) := by
  rw [bar_eq_iff_mul_mem_Q0]
  have hxy : (x : G)⁻¹ * (y : G) ∈ fr.Q0 := (bar_eq_iff_mul_mem_Q0 fr x y).mp h
  have key : ((qconj hS.split (etaD hηV) x : ↥Q) : G)⁻¹ *
      ((qconj hS.split (etaD hηV) y : ↥Q) : G) = η⁻¹ * ((x : G)⁻¹ * (y : G)) * η := by
    rw [qconj_coe, qconj_coe]; group
  rw [key]
  exact eta_conj_mem_Q0 hS fr (centD_le_twoPoint (H := H) t hηV) hxy

/-- If `η` normalises `KW` by conjugation, then so does `η⁻¹` (finiteness). -/
theorem eta_exists_conj_mem_KW_inv (fr : CoarseFrame H Q t n) {η : G}
    (hηN : ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η) :
    ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η * (d : G) * η⁻¹ := by
  classical
  choose f hf using hηN
  have hinj : Function.Injective f := by
    intro a b hab
    have hv : ((f a : fr.KW) : G) = ((f b : fr.KW) : G) := by rw [hab]
    rw [hf a, hf b] at hv
    have h2 := congrArg (fun z : G => η * z * η⁻¹) hv
    have h3 : η * (η⁻¹ * (a : G) * η) * η⁻¹ = (a : G) := by group
    have h4 : η * (η⁻¹ * (b : G) * η) * η⁻¹ = (b : G) := by group
    rw [h3, h4] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hinj
  intro d
  obtain ⟨e, he⟩ := hsurj d
  refine ⟨e, ?_⟩
  have h1 : (f e : G) = (d : G) := by rw [he]
  rw [hf e] at h1
  calc (e : G) = η * (η⁻¹ * (e : G) * η) * η⁻¹ := by group
    _ = η * (d : G) * η⁻¹ := by rw [h1]

end Q0

/-! ## The element `t = κ ζ ∈ E = GF(q²)` and the trace `c = t + t⁻¹` -/

section Field

theorem eta_kappa_zeta_ne_one (fr : CoarseFrame H Q t n) : fr.κ fr.ζ ≠ 1 := by
  intro h
  refine fr.ζ_ne_one (fr.κ_injective ?_)
  rw [h, map_one]

theorem eta_sigmaE_zetaE (fr : CoarseFrame H Q t n) :
    σE (fr.κ fr.ζ : E n) = ((fr.κ fr.ζ : E n))⁻¹ :=
  eq_inv_of_mul_eq_one_right fr.ζ_norm

theorem eta_traceE_fixed (fr : CoarseFrame H Q t n) :
    σE ((fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹) =
      (fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹ := by
  have h := eta_sigmaE_zetaE fr
  rw [map_add, σE_inv, h, inv_inv]
  exact add_comm _ _

theorem eta_traceE_ne_zero (fr : CoarseFrame H Q t n) :
    (fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹ ≠ 0 := by
  intro h0
  set x : E n := (fr.κ fr.ζ : E n) with hx
  have h0' : x + x⁻¹ = 0 := by rw [hx]; exact h0
  have hx0 : x ≠ 0 := by rw [hx]; exact Units.ne_zero _
  have hx1 : x ≠ 1 := by
    rw [hx]
    intro h
    exact eta_kappa_zeta_ne_one fr (Units.ext h)
  have hsq : x ^ 2 = 1 := by
    have hm : x * x = 1 := by
      have h2 : (x + x⁻¹) * x = 0 := by rw [h0', zero_mul]
      rw [add_mul, inv_mul_cancel₀ hx0] at h2
      have h3 : x * x = -(1 : E n) := add_eq_zero_iff_eq_neg.mp h2
      rwa [CharTwo.neg_eq] at h3
    rwa [pow_two]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact hx1 h
  · rw [CharTwo.neg_eq] at h
    exact hx1 h

/-- Every `y ∈ E` is `p + q·t` with `p, q ∈ F` (the fixed field of `σE`): explicit coordinates with
respect to the `F`-basis `{1, t}`. -/
theorem eta_exists_decomp (fr : CoarseFrame H Q t n) (y : E n) :
    ∃ p q : E n, σE p = p ∧ σE q = q ∧ y = p + q * (fr.κ fr.ζ : E n) := by
  haveI : CharP (E n) 2 := inferInstance
  refine ⟨y + ((y + σE y) * ((fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹)⁻¹) * (fr.κ fr.ζ : E n),
    (y + σE y) * ((fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹)⁻¹, ?_, ?_, ?_⟩
  · set t : E n := (fr.κ fr.ζ : E n) with htx
    set q : E n := (y + σE y) * (t + t⁻¹)⁻¹ with hq
    have ht : σE t = t⁻¹ := by rw [htx]; exact eta_sigmaE_zetaE fr
    have hc : σE (t + t⁻¹) = t + t⁻¹ := by rw [htx]; exact eta_traceE_fixed fr
    have hc0 : t + t⁻¹ ≠ 0 := by rw [htx]; exact eta_traceE_ne_zero fr
    have hqfix : σE q = q := by
      rw [hq, map_mul, map_add, σE_σE, σE_inv, hc]
      exact congrArg (fun z => z * (t + t⁻¹)⁻¹) (add_comm _ _)
    have hqc : q * (t + t⁻¹) = y + σE y := by
      rw [hq, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    have hp : σE (y + q * t) = σE y + q * t⁻¹ := by
      rw [map_add, map_mul, hqfix, ht]
    rw [hp]
    have key : (σE y + q * t⁻¹) + (y + q * t) = 0 := by
      calc (σE y + q * t⁻¹) + (y + q * t)
          = (σE y + y) + (q * t⁻¹ + q * t) := by abel
        _ = (σE y + y) + q * (t⁻¹ + t) := by rw [← mul_add]
        _ = (σE y + y) + q * (t + t⁻¹) := by rw [add_comm t⁻¹ t]
        _ = (σE y + y) + (y + σE y) := by rw [hqc]
        _ = 0 := by
            rw [show y + σE y = σE y + y from add_comm y (σE y), CharTwo.add_self_eq_zero]
    exact (add_eq_zero_iff_eq_neg.mp key).trans (CharTwo.neg_eq _)
  · set t : E n := (fr.κ fr.ζ : E n) with htx
    have hc : σE (t + t⁻¹) = t + t⁻¹ := by rw [htx]; exact eta_traceE_fixed fr
    rw [map_mul, map_add, σE_σE, σE_inv, hc]
    exact congrArg (fun z => z * (t + t⁻¹)⁻¹) (add_comm _ _)
  · set t : E n := (fr.κ fr.ζ : E n) with htx
    set q : E n := (y + σE y) * (t + t⁻¹)⁻¹ with hq
    show y = (y + q * t) + q * t
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Every nonzero `σE`-fixed element of `E` is `κ d` for some `d ∈ KW`. -/
theorem eta_exists_kappa_eq_of_sigmaE_fixed (fr : CoarseFrame H Q t n) {a : E n} (ha : a ≠ 0)
    (hfix : σE a = a) : ∃ d : fr.KW, (fr.κ d : E n) = a := by
  have hval : ((Units.mk0 a ha : (E n)ˣ) : E n) = a := Units.val_mk0 ..
  have h : σE (((Units.mk0 a ha) : (E n)ˣ) : E n) = (((Units.mk0 a ha) : (E n)ˣ) : E n) := by
    rw [hval, hfix]
  obtain ⟨d, hd⟩ := fr.K_surj (Units.mk0 a ha) h
  exact ⟨d, by rw [hd, hval]⟩

end Field

/-! ## The additive map `φ` induced by `η` on `E ≅ Q/Q₀` -/

section Phi

/-- A section of `bar : Q → E`. -/
noncomputable def etaSec (fr : CoarseFrame H Q t n) (y : E n) : ↥Q :=
  Classical.choose (fr.bar_surjective (Multiplicative.ofAdd y))

theorem etaSec_spec (fr : CoarseFrame H Q t n) (y : E n) :
    fr.bar (etaSec fr y) = Multiplicative.ofAdd y :=
  Classical.choose_spec (fr.bar_surjective (Multiplicative.ofAdd y))

/-- The additive map `E → E` induced by conjugation by `η` on `Q/Q₀ ≅ E`. -/
noncomputable def phi (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G)
    (hηV : η ∈ centD H t) (y : E n) : E n :=
  Multiplicative.toAdd (fr.bar (qconj hS.split (etaD hηV) (etaSec fr y)))

theorem phi_apply (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G)
    (hηV : η ∈ centD H t) (x : ↥Q) :
    Multiplicative.toAdd (fr.bar (qconj hS.split (etaD hηV) x)) =
      phi hS fr η hηV (Multiplicative.toAdd (fr.bar x)) := by
  have hb : fr.bar (etaSec fr (Multiplicative.toAdd (fr.bar x))) = fr.bar x := by
    rw [etaSec_spec, ofAdd_toAdd]
  exact (congrArg Multiplicative.toAdd (eta_bar_qconj_eq_of_bar_eq hS fr hηV hb)).symm

theorem phi_add (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G)
    (hηV : η ∈ centD H t) (y y' : E n) :
    phi hS fr η hηV (y + y') = phi hS fr η hηV y + phi hS fr η hηV y' := by
  have hb : fr.bar (etaSec fr (y + y')) = fr.bar (etaSec fr y * etaSec fr y') := by
    rw [bar_mul fr, etaSec_spec, etaSec_spec, etaSec_spec, ofAdd_add]
  have h := eta_bar_qconj_eq_of_bar_eq hS fr hηV hb
  have hq : qconj hS.split (etaD hηV) (etaSec fr y * etaSec fr y') =
      qconj hS.split (etaD hηV) (etaSec fr y) * qconj hS.split (etaD hηV) (etaSec fr y') := by
    apply Subtype.ext
    show η⁻¹ * ((etaSec fr y : G) * (etaSec fr y')) * η =
      (η⁻¹ * (etaSec fr y : G) * η) * (η⁻¹ * (etaSec fr y' : G) * η)
    group
  have h' : Multiplicative.toAdd (fr.bar (qconj hS.split (etaD hηV) (etaSec fr (y + y')))) =
      Multiplicative.toAdd (fr.bar (qconj hS.split (etaD hηV) (etaSec fr y))) +
        Multiplicative.toAdd (fr.bar (qconj hS.split (etaD hηV) (etaSec fr y'))) := by
    have h2 := congrArg Multiplicative.toAdd h
    rw [hq, bar_mul fr, toAdd_mul] at h2
    exact h2
  exact h'

theorem phi_zero (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G)
    (hηV : η ∈ centD H t) : phi hS fr η hηV 0 = 0 := by
  have h : phi hS fr η hηV 0 = phi hS fr η hηV 0 + phi hS fr η hηV 0 := by
    simpa using phi_add hS fr η hηV 0 0
  rw [h, CharTwo.add_self_eq_zero]

theorem phi_one (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G)
    (hηV : η ∈ centD H t)
    (hη1 : ∃ s : ↥Q, (s : G) ∉ fr.Q0 ∧ Multiplicative.toAdd (fr.bar s) = 1 ∧
      ((qconj hS.split (etaD hηV) s * s⁻¹ : ↥Q) : G) ∈ fr.Q0) :
    phi hS fr η hηV 1 = 1 := by
  obtain ⟨s, hsQ0, hsbar, hsfix⟩ := hη1
  have h2 : fr.bar (qconj hS.split (etaD hηV) s) = fr.bar s := by
    have hb : fr.bar (qconj hS.split (etaD hηV) s * s⁻¹) = 1 :=
      bar_eq_one_of_mem_Q0 fr hsfix
    rw [bar_mul fr, map_inv] at hb
    exact eq_of_mul_inv_eq_one hb
  have h4 : phi hS fr η hηV (Multiplicative.toAdd (fr.bar s)) =
      Multiplicative.toAdd (fr.bar s) := by
    rw [(phi_apply hS fr η hηV s).symm, h2]
  rw [← hsbar]
  exact h4

/-- **The semilinearity of the `η`-action**: conjugation by `η` transforms the `KW`-scalar
multiplication (which is the `E`-multiplication by `κ d`) into multiplication by `κ e`, where
`e = η⁻¹ d η`.  This is the compatibility `(c x)^η = c^μ x^η` of the source. -/
theorem phi_smul_of (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G)
    (hηV : η ∈ centD H t) {d e : fr.KW} (hde : (e : G) = η⁻¹ * (d : G) * η) (y : E n) :
    phi hS fr η hηV ((fr.κ d : E n) * y) = (fr.κ e : E n) * phi hS fr η hηV y := by
  set x : ↥Q := etaSec fr y with hx
  set dD : ↥(twoPoint H t) := ⟨(d : G), fr.KW_le d.2⟩ with hdD
  set xd : ↥Q := qconj hS.split dD x with hxd
  have hxd_c : (xd : G) = (d : G)⁻¹ * (x : G) * (d : G) := by
    rw [hxd, hdD, qconj_coe]
  have hbar_xd : Multiplicative.toAdd (fr.bar xd) =
      (fr.κ d : E n) * Multiplicative.toAdd (fr.bar x) :=
    fr.act_bar d x xd hxd_c
  have hbar_x : Multiplicative.toAdd (fr.bar x) = y := by
    rw [hx, etaSec_spec, toAdd_ofAdd]
  set xe : ↥Q := qconj hS.split (etaD hηV) x with hxe
  set xed : ↥Q := qconj hS.split (etaD hηV) xd with hxed
  have hrel : (xed : G) = (e : G)⁻¹ * (xe : G) * (e : G) := by
    have hL : (xed : G) = η⁻¹ * ((d : G)⁻¹ * (x : G) * (d : G)) * η := by
      rw [hxed, qconj_coe, hxd_c]
    have hR : (e : G)⁻¹ * (xe : G) * (e : G) =
        η⁻¹ * ((d : G)⁻¹ * (x : G) * (d : G)) * η := by
      rw [hxe, qconj_coe, hde]
      group
    rw [hL, hR]
  have hbar_xed : Multiplicative.toAdd (fr.bar xed) =
      (fr.κ e : E n) * Multiplicative.toAdd (fr.bar xe) :=
    fr.act_bar e xe xed hrel
  have hbd : Multiplicative.toAdd (fr.bar xd) = (fr.κ d : E n) * y := by
    rw [hbar_xd, hbar_x]
  have hb : fr.bar (etaSec fr ((fr.κ d : E n) * y)) = fr.bar xd := by
    rw [etaSec_spec, ← hbd]
    exact ofAdd_toAdd _
  have h1 := eta_bar_qconj_eq_of_bar_eq hS fr hηV hb
  rw [← hxed] at h1
  have h2 : phi hS fr η hηV ((fr.κ d : E n) * y) =
      (fr.κ e : E n) * Multiplicative.toAdd (fr.bar xe) := by
    change Multiplicative.toAdd
      (fr.bar (qconj hS.split (etaD hηV) (etaSec fr ((fr.κ d : E n) * y)))) = _
    rw [h1, hbar_xed]
  rw [hxe] at h2
  have h3 : Multiplicative.toAdd (fr.bar (qconj hS.split (etaD hηV) x)) =
      phi hS fr η hηV y := by
    rw [← hbar_x]
    exact phi_apply hS fr η hηV x
  rw [h3] at h2
  exact h2

end Phi

/-! ## Multiplicativity, injectivity and the assembly -/

section Main

theorem phi_mul (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G) (hηV : η ∈ centD H t)
    (hηN : ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η)
    (hη1 : ∃ s : ↥Q, (s : G) ∉ fr.Q0 ∧ Multiplicative.toAdd (fr.bar s) = 1 ∧
      ((qconj hS.split (etaD hηV) s * s⁻¹ : ↥Q) : G) ∈ fr.Q0)
    (x y : E n) : phi hS fr η hηV (x * y) = phi hS fr η hηV x * phi hS fr η hηV y := by
  have hphi1 : phi hS fr η hηV 1 = 1 := phi_one hS fr η hηV hη1
  -- scalars from the fixed field `F = GF(q)` (i.e. `κ(Ksub)` together with `0`)
  have hsmul : ∀ p : E n, σE p = p → ∀ z : E n,
      phi hS fr η hηV (p * z) = phi hS fr η hηV p * phi hS fr η hηV z := by
    intro p hp z
    rcases eq_or_ne p 0 with h0 | h0
    · rw [h0, zero_mul, phi_zero hS fr η hηV, zero_mul]
    · obtain ⟨d, hd⟩ := eta_exists_kappa_eq_of_sigmaE_fixed fr h0 hp
      obtain ⟨e, hde⟩ := hηN d
      have hpe : phi hS fr η hηV (fr.κ d : E n) = (fr.κ e : E n) := by
        have h1 := phi_smul_of hS fr η hηV (d := d) (e := e) hde (1 : E n)
        rw [mul_one, hphi1, mul_one] at h1
        exact h1
      rw [← hd, phi_smul_of hS fr η hηV (d := d) (e := e) hde z, hpe]
  obtain ⟨p, q, hp, hq, hy⟩ := eta_exists_decomp fr y
  obtain ⟨eζ, heζ⟩ := hηN fr.ζ
  have hphi_y : phi hS fr η hηV y =
      phi hS fr η hηV p + (fr.κ eζ : E n) * phi hS fr η hηV q := by
    rw [hy]
    rw [phi_add hS fr η hηV p (q * (fr.κ fr.ζ : E n))]
    rw [mul_comm q (fr.κ fr.ζ : E n)]
    rw [phi_smul_of hS fr η hηV (d := fr.ζ) (e := eζ) heζ q]
  calc phi hS fr η hηV (x * y)
      = phi hS fr η hηV (p * x + (q * x) * (fr.κ fr.ζ : E n)) := by
        congr 1
        rw [hy]; ring
    _ = phi hS fr η hηV (p * x) + phi hS fr η hηV ((q * x) * (fr.κ fr.ζ : E n)) :=
        phi_add hS fr η hηV (p * x) ((q * x) * (fr.κ fr.ζ : E n))
    _ = phi hS fr η hηV p * phi hS fr η hηV x +
          (fr.κ eζ : E n) * (phi hS fr η hηV q * phi hS fr η hηV x) := by
        rw [hsmul p hp x, mul_comm (q * x) (fr.κ fr.ζ : E n),
          phi_smul_of hS fr η hηV (d := fr.ζ) (e := eζ) heζ (q * x), hsmul q hq x]
    _ = phi hS fr η hηV x * phi hS fr η hηV y := by
        rw [hphi_y]; ring

theorem phi_injective (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G)
    (hηV : η ∈ centD H t) : Function.Injective (phi hS fr η hηV) := by
  intro y y' hyy
  have hyy' : Multiplicative.toAdd (fr.bar (qconj hS.split (etaD hηV) (etaSec fr y))) =
      Multiplicative.toAdd (fr.bar (qconj hS.split (etaD hηV) (etaSec fr y'))) := hyy
  have hbar := Multiplicative.toAdd.injective hyy'
  have hmem : ((etaSec fr y : G)⁻¹ * (etaSec fr y' : G)) ∈ fr.Q0 := by
    have h1 : (((qconj hS.split (etaD hηV) (etaSec fr y) : ↥Q) : G)⁻¹ *
        ((qconj hS.split (etaD hηV) (etaSec fr y') : ↥Q) : G)) ∈ fr.Q0 :=
      (bar_eq_iff_mul_mem_Q0 fr _ _).mp hbar
    have h3 : (η⁻¹)⁻¹ * ((((qconj hS.split (etaD hηV) (etaSec fr y) : ↥Q) : G)⁻¹ *
        ((qconj hS.split (etaD hηV) (etaSec fr y') : ↥Q) : G))) * η⁻¹ ∈ fr.Q0 :=
      eta_conj_mem_Q0 hS fr ((twoPoint H t).inv_mem (centD_le_twoPoint (H := H) t hηV)) h1
    have h4 : (η⁻¹)⁻¹ * ((((qconj hS.split (etaD hηV) (etaSec fr y) : ↥Q) : G)⁻¹ *
        ((qconj hS.split (etaD hηV) (etaSec fr y') : ↥Q) : G))) * η⁻¹ =
        ((etaSec fr y : G)⁻¹ * (etaSec fr y' : G)) := by
      rw [qconj_coe, qconj_coe]; group
    rwa [h4] at h3
  have hbar2 : fr.bar (etaSec fr y) = fr.bar (etaSec fr y') :=
    (bar_eq_iff_mul_mem_Q0 fr _ _).mpr hmem
  rw [etaSec_spec, etaSec_spec] at hbar2
  exact Multiplicative.ofAdd.injective hbar2

theorem phi_bijective (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) (η : G)
    (hηV : η ∈ centD H t) : Function.Bijective (phi hS fr η hηV) :=
  ⟨phi_injective hS fr η hηV, (Finite.injective_iff_surjective).mp (phi_injective hS fr η hηV)⟩

end Main

theorem etaAction_semilinear {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {η : G} (hηV : η ∈ Submission.Blueprint.centD H t)
    (hηN : ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η)
    (hη1 : ∃ s : ↥Q, (s : G) ∉ fr.Q0 ∧ Multiplicative.toAdd (fr.bar s) = 1 ∧
      ((Work.PSU3.StageB.qconj hS.split
          (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
            ↥(Submission.Blueprint.twoPoint H t)) s * s⁻¹ : ↥Q) : G) ∈ fr.Q0) :
    ∃ μ : Work.PSU3.E n ≃+* Work.PSU3.E n,
      (∀ x : ↥Q, Multiplicative.toAdd
          (fr.bar (Work.PSU3.StageB.qconj hS.split
            (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
              ↥(Submission.Blueprint.twoPoint H t)) x)) =
        μ (Multiplicative.toAdd (fr.bar x))) ∧
      (∀ (d e : fr.KW), (e : G) = η⁻¹ * (d : G) * η →
        (fr.κ e : Work.PSU3.E n) = μ (fr.κ d : Work.PSU3.E n)) := by
  have hbij : Function.Bijective (phi hS fr η hηV) := phi_bijective hS fr η hηV
  let phiHom : E n →+* E n :=
    { toFun := phi hS fr η hηV
      map_one' := phi_one hS fr η hηV hη1
      map_zero' := phi_zero hS fr η hηV
      map_add' := fun a b => phi_add hS fr η hηV a b
      map_mul' := fun a b => phi_mul hS fr η hηV hηN hη1 a b }
  refine ⟨RingEquiv.ofBijective phiHom hbij, ?_, ?_⟩
  · intro x
    exact phi_apply hS fr η hηV x
  · intro d e heq
    have h1 := phi_smul_of hS fr η hηV (d := d) (e := e) heq (1 : E n)
    rw [mul_one, phi_one hS fr η hηV hη1, mul_one] at h1
    exact h1.symm

end Work.PSU3.StageB.NotFpfStep4
