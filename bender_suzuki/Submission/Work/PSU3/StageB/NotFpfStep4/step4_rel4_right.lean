import Mathlib
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_rel4_aux
import Submission.Work.PSU3.StageB.Omega.API

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

/-!
# The right branch of relation (4) of Peterfalvi II, Ch. VII §4

This file proves the second half of the source's `(4)`: the value of
`Multiplicative.toAdd (bar (f(ω⁻¹ s^{a⁻¹})))`, computed with the recursion **(3)** of §2
(`fcan_zcQF_mul`, i.e. H6 applied to `x = s^{a⁻¹}`, `y = ω⁻¹`), expressed through the
`η`-image of `bar (f(ω s^a))` and `bar ω`:

  `bar (f(ω⁻¹ s^{a⁻¹})) = ζ^{-2} · bar (f(ω s^a))^η + ζ^{-1} · bar ω`.

Indeed, with `Y = t h(ω⁻¹) t = h(ω)^{-1} = ηζ^{-3}` and `X = f(s^a g(ω⁻¹)) = ζ^{-1} f(ω s^a) ζ`,
the recursion reads `f(ω⁻¹ s^{a⁻¹}) = Y⁻¹ X Y · f(ω⁻¹)`; since `Y = ηζ^{-3}` and `ηζ = ζη`,
the inner block is `ζ³ (η⁻¹ X η) ζ^{-3}`, and going to `E ≅ Q/Q₀` multiplies by
`(κ ζ)^{-3} · (κ ζ)` (the inner `ζ`-conjugation of `X = qconj ζ Z`, `Z = f(ω s^a)`, contributing
the extra `κ ζ`), while `f(ω⁻¹) = ζ ω ζ⁻¹` contributes `(κ ζ)^{-1} bar ω`.
-/

section GroupLemmas

variable {G : Type} [Group G] {x y z : G}

/-- From `x y = y x` deduce `y⁻¹ x = x y⁻¹`. -/
lemma step4_inv_mul_comm (h : x * y = y * x) : y⁻¹ * x = x * y⁻¹ := by
  have hconj : y * x * y⁻¹ = x := by rw [← h]; group
  calc y⁻¹ * x = y⁻¹ * (y * x * y⁻¹) := (congrArg (fun t => y⁻¹ * t) hconj).symm
    _ = x * y⁻¹ := by group

/-- From `x y = y x` push the conjugation by `y` inside a product. -/
lemma step4_mul_conj_comm (h : x * y = y * x) : x * (y⁻¹ * z * y) = y⁻¹ * (x * z) * y := by
  have h' : y⁻¹ * x = x * y⁻¹ := step4_inv_mul_comm h
  calc x * (y⁻¹ * z * y) = (x * y⁻¹) * (z * y) := by group
    _ = (y⁻¹ * x) * (z * y) := by rw [← h']
    _ = y⁻¹ * (x * z) * y := by group

/-- From `x y = y x` exchange the two conjugations of `z`. -/
lemma step4_swap_conj (h : x * y = y * x) :
    x⁻¹ * (y⁻¹ * z * y) * x = y⁻¹ * (x⁻¹ * z * x) * y := by
  have h' : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
    have hh := congrArg Inv.inv h
    simpa only [mul_inv_rev] using hh.symm
  calc x⁻¹ * (y⁻¹ * z * y) * x = (x⁻¹ * y⁻¹) * z * (y * x) := by group
    _ = (y⁻¹ * x⁻¹) * z * (x * y) := by rw [h', ← h]
    _ = y⁻¹ * (x⁻¹ * z * x) * y := by group

end GroupLemmas

theorem step4_rel4_right {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    (hsq : ω * ω = Work.PSU3.StageB.zcQF fr α)
    {η : G} (hηV : η ∈ Submission.Blueprint.centD H t)
    (hh : (Work.PSU3.StageB.hcan hS.split ω : G) = (fr.ζ : G) ^ 3 * η⁻¹)
    (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η)
    (a : ↥(Work.PSU3.StageB.FX n)) :
    Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
        (ω⁻¹ * Work.PSU3.StageB.sconjF fr a⁻¹))) =
      (((fr.κ fr.ζ : Work.PSU3.E n))^2)⁻¹ *
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.qconj hS.split
          (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
            ↥(Submission.Blueprint.twoPoint H t))
          (Work.PSU3.StageB.fcan hS.split (ω * Work.PSU3.StageB.sconjF fr a))))
      + (fr.κ fr.ζ : Work.PSU3.E n)⁻¹ * Multiplicative.toAdd (fr.bar ω) := by
  have hω1 : (ω : G) ≠ 1 := fun h => hω (by rw [h]; exact Q0_one_mem fr)
  set ηD : ↥(twoPoint H t) := ⟨η, centD_le_twoPoint (H := H) t hηV⟩ with hηD
  set Z : ↥Q := fcan hS.split (ω * sconjF fr a) with hZ
  set X : ↥Q := fcan hS.split (sconjF fr a * gcan hS.split ω⁻¹) with hX
  -- ## `ζ` commutes with `s^a`
  have hconjζ : (fr.ζ : G) * (sconjF fr a : G) * (fr.ζ : G)⁻¹ = (sconjF fr a : G) := by
    have hc := qconj_coe hS.split ((zetaD fr)⁻¹) (sconjF fr a)
    simp only [zetaD_coe, Subgroup.coe_inv, inv_inv] at hc
    rw [← hc, qconj_zetaD_inv_sconjF hS fr a]
  have hζa : (sconjF fr a : G) * (fr.ζ : G) = (fr.ζ : G) * (sconjF fr a : G) := by
    have h2 : ((fr.ζ : G) * (sconjF fr a : G) * (fr.ζ : G)⁻¹) * (fr.ζ : G) =
        (fr.ζ : G) * (sconjF fr a : G) := by group
    have h3 := congrArg (fun t : G => t * (fr.ζ : G)) hconjζ
    rw [h2] at h3
    exact h3.symm
  -- ## the recursion **(3)** of §2 with `u = nmF fr a⁻¹` and `p = ω⁻¹`
  have hωi1 : ((ω⁻¹ : ↥Q) : G) ≠ 1 := by simpa using hω1
  have hzp : ((zcQF fr (nmF fr a⁻¹) * ω⁻¹ : ↥Q) : G) ≠ 1 := by
    intro hc
    have hmem : ((zcQF fr (nmF fr a⁻¹) : ↥Q) : G) ∈ fr.Q0 := zcQF_mem fr (nmF fr a⁻¹)
    have h1 : (zcQF fr (nmF fr a⁻¹) * ω⁻¹ : ↥Q) = 1 := Subtype.ext hc
    have h2 : (ω⁻¹ : ↥Q) = (zcQF fr (nmF fr a⁻¹))⁻¹ := by
      calc (ω⁻¹ : ↥Q) = (zcQF fr (nmF fr a⁻¹))⁻¹ * (zcQF fr (nmF fr a⁻¹) * ω⁻¹) := by group
        _ = (zcQF fr (nmF fr a⁻¹))⁻¹ * 1 := by rw [h1]
        _ = (zcQF fr (nmF fr a⁻¹))⁻¹ := by rw [mul_one]
    have h3 : ((ω⁻¹ : ↥Q) : G) ∈ fr.Q0 := by rw [h2]; exact (fr.Q0).inv_mem hmem
    exact hω (by simpa using (fr.Q0).inv_mem h3)
  have hrec := fcan_zcQF_mul hS fr (nmF fr a⁻¹) (p := ω⁻¹) hωi1 hzp
  have hs1 : zcQF fr (nmF fr a⁻¹) = sconjF fr a⁻¹ := (sconjF_eq_zcQF fr hS a⁻¹).symm
  have hs2 : zcQF fr (nmF fr a⁻¹)⁻¹ = sconjF fr a := by
    have h : (nmF fr a⁻¹)⁻¹ = nmF fr a := by rw [nmF_inv, inv_inv]
    rw [h]
    exact (sconjF_eq_zcQF fr hS a).symm
  rw [hs1, hs2, sconjF_comm hS fr a⁻¹ ω⁻¹, ← hX] at hrec
  -- ## `X` is the `ζ`-conjugate of `Z`
  have hneX : ((sconjF fr a * ω : ↥Q) : G) ≠ 1 := by
    intro hc
    have hmem : ((sconjF fr a : ↥Q) : G) ∈ fr.Q0 := sconjF_mem_Q0 hS fr a
    have h2 : ((ω : G)) = (((sconjF fr a)⁻¹ : ↥Q) : G) := by
      rw [Subgroup.coe_inv]
      calc (ω : G) = ((sconjF fr a : ↥Q) : G)⁻¹ * ((sconjF fr a * ω : ↥Q) : G) := by
            rw [Subgroup.coe_mul]; group
        _ = ((sconjF fr a : ↥Q) : G)⁻¹ * 1 := by rw [hc]
        _ = ((sconjF fr a : ↥Q) : G)⁻¹ := by rw [mul_one]
    exact hω (by rw [h2]; exact (fr.Q0).inv_mem hmem)
  have hXZ : X = qconj hS.split (zetaD fr) Z := by
    have hg : gcan hS.split ω⁻¹ = qconj hS.split (zetaD fr) ω := by
      apply Subtype.ext
      rw [qconj_coe, zetaD_coe]
      exact gcan_omega_inv hS fr hω hf hsq
    have hsub : sconjF fr a * gcan hS.split ω⁻¹
        = qconj hS.split (zetaD fr) (sconjF fr a * ω) := by
      apply Subtype.ext
      simp only [qconj_coe, zetaD_coe, Subgroup.coe_mul, hg]
      exact step4_mul_conj_comm hζa
    have hstep : fcan hS.split (qconj hS.split (zetaD fr) (sconjF fr a * ω))
        = qconj hS.split (zetaD fr) (fcan hS.split (sconjF fr a * ω)) := by
      apply Subtype.ext
      rw [fcan_qconj hS.split hneX (zetaD fr)]
      simp only [qconj_coe, zetaD_coe, t_zeta_t hS.split fr]
    rw [hX, hsub, hstep]
    congr 1
    rw [hZ, sconjF_comm hS fr a ω]
  -- ## the `t`-conjugate of `h(ω⁻¹)`
  have hY : t * (hcan hS.split ω⁻¹ : G) * t = η * ((fr.ζ : G)^3)⁻¹ := by
    rw [hcan_omega_inv hS fr hω hηV hh]
    rw [t_conj_mul hS η (((fr.ζ : G)^3)⁻¹)]
    rw [t_conj_of_mem_centD hS hηV]
    congr 1
    have hzinv : t * (fr.ζ : G)⁻¹ * t = (fr.ζ : G)⁻¹ := t_zeta_inv_t hS.split fr
    rw [← inv_pow]
    have h := t_conj_pow hS ((fr.ζ : G)⁻¹) 3
    rw [hzinv] at h
    exact h
  -- ## the inner block is a `qconj`
  have hblock : (t * (hcan hS.split ω⁻¹ : G) * t)⁻¹ * (X : G) * (t * (hcan hS.split ω⁻¹ : G) * t)
      = (qconj hS.split (((zetaD fr)^3)⁻¹) (qconj hS.split ηD X) : G) := by
    rw [hY, qconj_coe, qconj_coe]
    simp only [zetaD_coe, Subgroup.coe_pow, Subgroup.coe_inv, inv_inv]
    rw [hηD]
    group
  -- ## assembly at the level of `Q`
  have hQ : fcan hS.split (ω⁻¹ * sconjF fr a⁻¹)
      = qconj hS.split (((zetaD fr)^3)⁻¹) (qconj hS.split ηD X) * fcan hS.split ω⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← hblock]
    exact hrec
  have hbar := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hQ
  simp only [map_mul, toAdd_mul] at hbar
  -- ## `bar (qconj η X) = κ ζ · bar (qconj η Z)`
  have hηX : qconj hS.split ηD X = qconj hS.split (zetaD fr) (qconj hS.split ηD Z) := by
    apply Subtype.ext
    simp only [qconj_coe, zetaD_coe]
    rw [hηD]
    rw [hXZ]
    simp only [qconj_coe, zetaD_coe]
    exact step4_swap_conj hcentζ
  have hfω : fcan hS.split ω⁻¹ = qconj hS.split ((zetaD fr)⁻¹) ω := by
    apply Subtype.ext
    rw [qconj_coe]
    simp only [zetaD_coe, Subgroup.coe_inv, inv_inv]
    exact fcan_omega_inv hS fr hω hf hsq
  -- ## the field arithmetic
  have harith : (((fr.κ fr.ζ : E n))^3)⁻¹ * ((fr.κ fr.ζ : E n) *
        Multiplicative.toAdd (fr.bar (qconj hS.split ηD Z)))
      = (((fr.κ fr.ζ : E n))^2)⁻¹ *
        Multiplicative.toAdd (fr.bar (qconj hS.split ηD Z)) := by
    rw [← mul_assoc]
    congr 1
    field_simp
  rw [hbar, bar_qconj_zetaD3_inv hS fr (qconj hS.split ηD X), hηX,
      bar_qconj_zetaD hS fr (qconj hS.split ηD Z), hfω, bar_qconj_zetaD_inv hS fr ω, harith]

end Work.PSU3.StageB.NotFpfStep4
