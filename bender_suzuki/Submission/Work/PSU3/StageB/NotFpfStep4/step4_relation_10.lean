/-
# Peterfalvi II, Ch. VII §4, relation (10)

This file proves the source's relation (10)

  `(ζ + ζ⁻¹ + X^μ)·X = (ζ + ζ⁻¹ + X^{μ²})·X^μ`

for the elements `X` of the fixed field `F` of the Frobenius `σE`, off at most one exceptional
value.  The derivation is the "algebraic core" of §4 (the source's computation (4)–(10)):

* `step4_core` is the pure field computation: from the two linear relations
  `ζ·Y = X^μ·Y^μ + ω`, `f·Y = ζ⁻¹·Y^μ + ω` (the source's (5) and (6), obtained from (4) at `a`
  and at `b` together with (3)), it produces relation (10) at the point `X^μ`.
  The argument is the source's: solve the linear system (7)/(8), apply `μ` to (7) and compare
  with (8) to obtain (9), read (9) as the quadratic relation of `step4_lambda_eq_one`, conclude
  `λ = 1` and `f + X^{μ²} = ζ + ζ⁻¹`, whence the `μ`-fixedness of `(ζ+ζ⁻¹+X^{μ²})X^μ`.

* `step4_relation_10` instantiates it: for each `a ∈ F*` there is a partner `b` with
  `fval (nmF b) = fval α + (fval (nmF a))⁻¹` (the source's proviso defining `b`), except for the
  single exceptional `a`; `h3` and `h4` supply the two linear relations, so relation (10) holds at
  every `μ (fval a)^{-2}`, i.e. at every element of `F` except possibly one.  The exceptional
  value is the witness `x₀`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_linear_system
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_lambda_eq_one
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_mu_sq_fix_of_relation_exc
import Submission.Work.PSU3.StageB.NotFpfStep4.etaAction_semilinear

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.NotFpfStep4

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## The pure field computation -/

/-- **The algebraic core of §4.**  Let `K = E n = GF(2^{2n})` have characteristic `2`, let
`μ` be a ring automorphism of `K` preserving the fixed field `F` of `σE`, let `z ≠ 0` with
`σE z = z⁻¹ ≠ z`, let `W ≠ 0` be `μ`-fixed and `z` `μ`-fixed.  If `X, f` are `σE`-fixed and

  `z * Y = (μ X) * (μ Y) + W`,  `f * Y = z⁻¹ * (μ Y) + W`,

then the relation (10) holds at the point `μ X`:

  `(z + z⁻¹ + μ (μ X)) * μ X = (z + z⁻¹ + μ (μ (μ X))) * μ (μ X)`.

This is the source's computation (5)–(10) with `ζ = z`, `ωbar = W`, `X = a^{-2}`,
`f = b²`. -/
theorem step4_core {n : ℕ} (hn : 2 ≤ n) {μ : E n ≃+* E n} {z W X f Y : E n}
    (hz0 : z ≠ 0) (hσz : σE z = z⁻¹) (hzne : σE z ≠ z) (hW : W ≠ 0)
    (hzW : μ z = z) (hμW : μ W = W)
    (hμF : ∀ x : E n, σE x = x → σE (μ x) = μ x)
    (hX : σE X = X) (hfF : σE f = f)
    (h5 : z * Y = (μ X) * (μ Y) + W) (h6 : f * Y = z⁻¹ * (μ Y) + W) :
    ((z + z⁻¹) + μ (μ X)) * (μ X) =
      ((z + z⁻¹) + μ (μ (μ X))) * (μ (μ X)) := by
  have hQF : σE (μ X) = μ X := hμF X hX
  have hPF : σE (μ (μ X)) = μ (μ X) := hμF (μ X) hQF
  have hμfF : σE (μ f) = μ f := hμF f hfF
  -- (6) cleared of the inverse
  have h6z : z * (f * Y) = μ Y + z * W := by
    have h := congrArg (fun s => z * s) h6
    rw [mul_add] at h
    have h2 : z * (z⁻¹ * μ Y) = μ Y := by rw [← mul_assoc, mul_inv_cancel₀ hz0, one_mul]
    rw [h2] at h
    exact h
  have hμY2 : μ Y = z * (f * Y + W) := by
    have h : μ Y = z * (f * Y) + z * W := by
      linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h6z
    rw [h, mul_add]
  -- the key equation
  have hkey : z * Y * (1 + f * (μ X)) = W * (1 + z * (μ X)) := by
    have h5' : z * Y = (μ X) * (z * (f * Y + W)) + W := by rw [← hμY2]; exact h5
    have h5'' : z * Y + ((μ X) * (z * (f * Y + W)) + W) = 0 := by
      rw [CharTwo.add_eq_zero]; exact h5'
    rw [← CharTwo.add_eq_zero]
    linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h5''
  -- non-degeneracy of the linear system
  have hden : 1 + f * (μ X) ≠ 0 := by
    intro h0
    have hWy : W * (1 + z * (μ X)) = 0 := by
      have h := hkey
      rw [h0, mul_zero] at h
      exact h.symm
    have h1 : 1 + z * (μ X) = 0 := by
      rcases mul_eq_zero.mp hWy with h | h
      · exact absurd h hW
      · exact h
    have hzQ : z * (μ X) = 1 := (CharTwo.add_eq_zero.mp h1).symm
    have hQinv : μ X = z⁻¹ := eq_inv_of_mul_eq_one_right hzQ
    have hzzeq : σE z = z := by
      have h2 : σE (z⁻¹) = z⁻¹ := by rw [← hQinv]; exact hQF
      rw [σE_inv] at h2
      exact inv_inj.mp h2
    exact hzne hzzeq
  -- (7)
  have hY : Y = (1 + z * (μ X)) / (z * (1 + f * (μ X))) * W := by
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hz0 hden)]
    linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) hkey
  -- (8)
  have hμY3 : μ Y = (f + z) / (1 + f * (μ X)) * W := by
    have hmain : μ Y * (1 + f * (μ X)) = (f + z) * W := by
      rw [hμY2]
      linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) f * hkey
    rw [div_mul_eq_mul_div, eq_div_iff hden]
    exact hmain
  -- `μ` applied to (7)
  have hμY4 : μ Y = (1 + z * (μ (μ X))) / (z * (1 + μ f * (μ (μ X)))) * W := by
    have h := congrArg (fun s => μ s) hY
    simp only [map_mul, map_div₀, map_add, map_one, hzW, hμW] at h
    exact h
  -- (9)
  have h9 : (1 + z * (μ (μ X))) / (z * (1 + μ f * (μ (μ X)))) =
      (f + z) / (1 + f * (μ X)) := by
    have h := hμY4.symm.trans hμY3
    exact mul_right_cancel₀ hW h
  have hD : 1 + μ f * (μ (μ X)) ≠ 0 := by
    intro hD0
    have hzD : z * (1 + μ f * (μ (μ X))) = 0 := by rw [hD0, mul_zero]
    have h0 : (1 + z * (μ (μ X))) / (z * (1 + μ f * (μ (μ X)))) = 0 := by
      rw [hzD, div_zero]
    rw [h9] at h0
    have hB0 : f + z = 0 := by
      rcases div_eq_zero_iff.mp h0 with h | h
      · exact h
      · exact absurd h hden
    have hfz : f = z := by
      have := add_eq_zero_iff_eq_neg.mp hB0
      rwa [CharTwo.neg_eq] at this
    refine hzne ?_
    rw [← hfz]
    exact hfF
  -- (9) cross-multiplied
  have hstar : (1 + z * (μ (μ X))) * (1 + f * (μ X)) =
      z * (1 + μ f * (μ (μ X))) * (f + z) := by
    have hzD : z * (1 + μ f * (μ (μ X))) ≠ 0 := mul_ne_zero hz0 hD
    have h := h9
    rw [div_eq_div_iff hzD hden] at h
    linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h
  -- the quadratic relation of `step4_lambda_eq_one`
  set lam : E n := (1 + μ f * (μ (μ X))) / (1 + f * (μ X)) with hlam
  set w : E n := lam * f + μ (μ X) with hw
  have hlamF : σE lam = lam := by
    rw [hlam, map_div₀, map_add, map_one, map_mul, hμfF, hPF, map_add, map_one, map_mul, hfF, hQF]
  have hwF : σE w = w := by
    rw [hw, map_add, map_mul, hlamF, hfF, hPF]
  have hquad : lam * z ^ 2 + w * z + 1 = 0 := by
    have hmul : (lam * z ^ 2 + w * z + 1) * (1 + f * (μ X)) = 0 := by
      have h1 : (1 + μ f * (μ (μ X))) / (1 + f * (μ X)) * (1 + f * (μ X)) =
          (1 + μ f * (μ (μ X))) := div_mul_cancel₀ _ hden
      rw [hw, hlam]
      have h2 : (((1 + μ f * (μ (μ X))) / (1 + f * (μ X))) * z ^ 2 +
            (((1 + μ f * (μ (μ X))) / (1 + f * (μ X))) * f + μ (μ X)) * z + 1) *
            (1 + f * (μ X)) =
          (1 + μ f * (μ (μ X))) * z ^ 2 +
            ((1 + μ f * (μ (μ X))) * f + μ (μ X) * (1 + f * (μ X))) * z +
            (1 + f * (μ X)) := by
        linear_combination (norm := ring_nf) (z ^ 2 + f * z) * h1
      rw [h2]
      linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) hstar
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h hden
  obtain ⟨hl1, hw1⟩ := step4_lambda_eq_one hn hz0 hσz hzne hlamF hwF hquad
  -- `λ = 1` gives `μ f · μ²X = f · μX`
  have hfg : μ f * (μ (μ X)) = f * (μ X) := by
    have h : 1 + μ f * (μ (μ X)) = 1 + f * (μ X) := by
      have hh := hl1
      rw [hlam] at hh
      exact (div_eq_one_iff_eq hden).mp hh
    linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h
  -- `f + μ²X = z + z⁻¹`
  have hCP : (z + z⁻¹) + μ (μ X) = f := by
    have h := hw1
    rw [hw, hl1, one_mul] at h
    linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h
  have hCμP : (z + z⁻¹) + μ (μ (μ X)) = μ f := by
    have hC : μ (z + z⁻¹) = (z + z⁻¹) := by
      rw [map_add, hzW, map_inv₀, hzW]
    rw [← hC, ← map_add, hCP]
  have hL : ((z + z⁻¹) + μ (μ X)) * (μ X) = f * (μ X) := by rw [hCP]
  have hR : ((z + z⁻¹) + μ (μ (μ X))) * (μ (μ X)) = f * (μ X) := by
    rw [hCμP, hfg]
  rw [hL, hR]

/-! ## The main statement -/

theorem step4_relation_10 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) (hn : 2 ≤ n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    {η : G} (hηV : η ∈ Submission.Blueprint.centD H t)
    {μ : Work.PSU3.E n ≃+* Work.PSU3.E n}
    (hμbar : ∀ x : ↥Q, Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.qconj hS.split
        (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
          ↥(Submission.Blueprint.twoPoint H t)) x)) = μ (Multiplicative.toAdd (fr.bar x)))
    (hμκ : ∀ (d e : fr.KW), (e : G) = η⁻¹ * (d : G) * η → fr.κ e = μ (fr.κ d))
    (hcentω : η * (ω : G) = (ω : G) * η) (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η)
    (hμF : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → Work.PSU3.σE (μ x) = μ x)
    (h4 : ∀ a : ↥(Work.PSU3.StageB.FX n),
      (Work.PSU3.StageB.fval a) ^ 2 *
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
      ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹ *
        μ (Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))))
      + Multiplicative.toAdd (fr.bar ω))
    (h3 : ∀ a b : ↥(Work.PSU3.StageB.FX n),
      Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr b) =
        Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a))⁻¹ →
      Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
        (fr.κ fr.ζ : Work.PSU3.E n) *
          ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr b)))) :
    ∃ x₀ : Work.PSU3.E n, ∀ X : Work.PSU3.E n, Work.PSU3.σE X = X → X ≠ x₀ → X + 1 ≠ x₀ →
      ((fr.κ fr.ζ : Work.PSU3.E n) + ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹ + μ X) * X =
        ((fr.κ fr.ζ : Work.PSU3.E n) + ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹ + μ (μ X)) * μ X
  := by
  classical
  let z : Work.PSU3.E n := (fr.κ fr.ζ : Work.PSU3.E n)
  -- ## elementary facts about `z = κζ` and `ω`
  have hz0 : z ≠ 0 := Units.ne_zero _
  have hσz : Work.PSU3.σE z = z⁻¹ := eta_sigmaE_zetaE fr
  have hzne : Work.PSU3.σE z ≠ z := by
    intro h
    have hσ := hσz
    rw [h] at hσ
    have h2 : z * z = 1 := by nth_rewrite 1 [hσ]; exact inv_mul_cancel₀ hz0
    have h3 : z = 1 := by
      have hsq : z ^ 2 = 1 := by rwa [pow_two]
      rcases sq_eq_one_iff.mp hsq with h' | h'
      · exact h'
      · rwa [CharTwo.neg_eq] at h'
    exact eta_kappa_zeta_ne_one fr (Units.ext h3)
  have hW : Multiplicative.toAdd (fr.bar ω) ≠ 0 := by
    intro h
    have h1 : fr.bar ω = 1 := Multiplicative.toAdd.injective (by rw [h]; rfl)
    exact hω ((fr.bar_eq_one_iff ω).mp h1)
  have hzW : μ z = z := by
    have hconj : (fr.ζ : G) = η⁻¹ * (fr.ζ : G) * η := by
      have h1 : η⁻¹ * (fr.ζ : G) * η = (fr.ζ : G) := by rw [mul_assoc, ← hcentζ]; group
      exact h1.symm
    exact (hμκ fr.ζ fr.ζ hconj).symm
  have hμW : μ (Multiplicative.toAdd (fr.bar ω)) = Multiplicative.toAdd (fr.bar ω) := by
    have h := hμbar ω
    have hqω : Work.PSU3.StageB.qconj hS.split
        (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
          ↥(Submission.Blueprint.twoPoint H t)) ω = ω := by
      apply Subtype.ext
      rw [Work.PSU3.StageB.qconj_coe]
      exact (by rw [mul_assoc, ← hcentω]; group : η⁻¹ * (ω : G) * η = (ω : G))
    rw [hqω] at h
    exact h.symm
  -- ## `μ` is surjective on the fixed field `F` of `σE`
  have hμsurj : ∀ y : Work.PSU3.E n, Work.PSU3.σE y = y →
      ∃ x : Work.PSU3.E n, Work.PSU3.σE x = x ∧ μ x = y := by
    intro y hy
    have hinj : Function.Injective
        (fun s : {x : Work.PSU3.E n // Work.PSU3.σE x = x} =>
          (⟨μ s.1, hμF s.1 s.2⟩ : {x : Work.PSU3.E n // Work.PSU3.σE x = x})) := by
      intro a b hab
      exact Subtype.ext (μ.injective (Subtype.ext_iff.mp hab))
    obtain ⟨u, hu⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
    exact ⟨u.1, u.2, Subtype.ext_iff.mp hu⟩
  -- ## squaring is surjective on `F*` (characteristic `2`, `F` finite)
  have hsqrtsurj : ∀ y : Work.PSU3.E n, Work.PSU3.σE y = y → y ≠ 0 →
      ∃ s : Work.PSU3.E n, Work.PSU3.σE s = s ∧ s ≠ 0 ∧ s * s = y := by
    intro y hy hy0
    have hinj : Function.Injective
        (fun s : {x : Work.PSU3.E n // Work.PSU3.σE x = x} =>
          (⟨s.1 * s.1, by rw [map_mul, s.2]⟩ : {x : Work.PSU3.E n // Work.PSU3.σE x = x})) := by
      intro a b hab
      apply Subtype.ext
      have h : a.1 * a.1 = b.1 * b.1 := Subtype.ext_iff.mp hab
      have hsq : (a.1 + b.1) * (a.1 + b.1) = 0 := by
        linear_combination (norm := (ring_nf <;> simp [CharTwo.two_eq_zero])) h
      have h0 : a.1 + b.1 = 0 := mul_self_eq_zero.mp hsq
      have h1 : a.1 = -b.1 := add_eq_zero_iff_eq_neg.mp h0
      rwa [CharTwo.neg_eq] at h1
    obtain ⟨u, hu⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
    refine ⟨u.1, u.2, ?_, Subtype.ext_iff.mp hu⟩
    intro h
    apply hy0
    have hu' : u.1 * u.1 = y := Subtype.ext_iff.mp hu
    rw [h, mul_zero] at hu'
    exact hu'.symm
  -- ## relation (10) at `μ (fval a)^{-2}` for every admissible `a`
  have hparam : ∀ a : ↥(Work.PSU3.StageB.FX n),
      Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a) ≠ (Work.PSU3.StageB.fval α)⁻¹ →
      ((z + z⁻¹) + μ (μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹))) *
          (μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹)) =
        ((z + z⁻¹) + μ (μ (μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹)))) *
          (μ (μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹))) := by
    intro a ha
    -- the source's `b`, defined by `fval (nmF b) = fval α + (fval (nmF a))⁻¹`
    let A : Work.PSU3.E n := Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a)
    have hA0 : Work.PSU3.StageB.fval α + A⁻¹ ≠ 0 := by
      intro hc
      apply ha
      have h3' := add_eq_zero_iff_eq_neg.mp hc
      rw [CharTwo.neg_eq] at h3'
      exact (show A = (Work.PSU3.StageB.fval α)⁻¹ by rw [← inv_inv A, h3'])
    have hAfix : Work.PSU3.σE (Work.PSU3.StageB.fval α + A⁻¹) =
        Work.PSU3.StageB.fval α + A⁻¹ := by
      rw [map_add, map_inv₀, α.2, (Work.PSU3.StageB.nmF fr a).2]
    let b : ↥(Work.PSU3.StageB.FX n) := (Work.PSU3.StageB.nmEquiv hS fr).symm
        (Work.PSU3.StageB.mkFX (Work.PSU3.StageB.fval α + A⁻¹) hAfix hA0)
    have hb : Work.PSU3.StageB.nmF fr b =
        Work.PSU3.StageB.mkFX (Work.PSU3.StageB.fval α + A⁻¹) hAfix hA0 := by
      rw [← Work.PSU3.StageB.nmEquiv_apply hS fr b]
      exact (Work.PSU3.StageB.nmEquiv hS fr).apply_symm_apply _
    have hcond : Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr b) =
        Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a))⁻¹ := by
      rw [hb, Work.PSU3.StageB.fval_mkFX]
    -- the source's (3) and (4)
    have h3ab := h3 a b hcond
    have h4a := h4 a
    have h4b := h4 b
    let Ta : Work.PSU3.E n := Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
      (ω * Work.PSU3.StageB.sconjF fr a)))
    let Tb : Work.PSU3.E n := Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
      (ω * Work.PSU3.StageB.sconjF fr b)))
    -- (5)
    have h5 : z * Tb = (μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹)) * (μ Tb)
        + Multiplicative.toAdd (fr.bar ω) := by
      have h := h4a
      rw [h3ab] at h
      have hμTa : μ (z * ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) * Tb) =
          z * μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) * μ Tb := by
        rw [map_mul, map_mul, hzW]
      rw [hμTa] at h
      have h1 : (Work.PSU3.StageB.fval a) ^ 2 *
          ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) = 1 := by field_simp
      have hL : (Work.PSU3.StageB.fval a) ^ 2 *
          (z * ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) * Tb) = z * Tb := by
        linear_combination (norm := ring_nf) (z * Tb) * h1
      have hR : z⁻¹ * (z * μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) * μ Tb) =
          μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) * (μ Tb) := by
        have hz1 : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
        calc z⁻¹ * (z * μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) * μ Tb)
            = (z⁻¹ * z) * (μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) * μ Tb) := by
              ring
          _ = μ ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) * (μ Tb) := by
              rw [hz1, one_mul]
      rw [hL, hR] at h
      exact h
    -- (6)
    have h6 : (Work.PSU3.StageB.fval b) ^ 2 * Tb =
        z⁻¹ * (μ Tb) + Multiplicative.toAdd (fr.bar ω) := h4b
    have hXf : Work.PSU3.σE ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) =
        (Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹ := by
      rw [map_mul, map_inv₀, a.2]
    have hfF : Work.PSU3.σE ((Work.PSU3.StageB.fval b) ^ 2) = (Work.PSU3.StageB.fval b) ^ 2 := by
      rw [map_pow, b.2]
    exact step4_core hn hz0 hσz hzne hW hzW hμW hμF hXf hfF h5 h6
  -- ## the exceptional value and the conclusion
  refine ⟨μ ((Work.PSU3.StageB.fval (Work.PSU3.StageB.tau hS fr α⁻¹))⁻¹ *
      (Work.PSU3.StageB.fval (Work.PSU3.StageB.tau hS fr α⁻¹))⁻¹), ?_⟩
  intro X hX hne _
  by_cases hX0 : X = 0
  · subst hX0
    simp
  · obtain ⟨t, htF, hμt⟩ := hμsurj X hX
    have ht0 : t ≠ 0 := by
      intro h
      apply hX0
      rw [← hμt, h, map_zero]
    have htinvF : Work.PSU3.σE t⁻¹ = t⁻¹ := by rw [map_inv₀, htF]
    have htinv0 : t⁻¹ ≠ 0 := inv_ne_zero ht0
    obtain ⟨s, hsF, hs0, hssq⟩ := hsqrtsurj t⁻¹ htinvF htinv0
    let a : ↥(Work.PSU3.StageB.FX n) := Work.PSU3.StageB.mkFX s hsF hs0
    have haf : Work.PSU3.StageB.fval a = s := Work.PSU3.StageB.fval_mkFX s hsF hs0
    have haX : (Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹ = t := by
      rw [haf, ← mul_inv_rev, hssq, inv_inv]
    have hane : Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a) ≠
        (Work.PSU3.StageB.fval α)⁻¹ := by
      intro hc
      have h1 : Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a) =
          Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr (Work.PSU3.StageB.tau hS fr α⁻¹)) := by
        rw [Work.PSU3.StageB.nm_tau, Work.PSU3.StageB.fval_inv]
        exact hc
      have h2 : Work.PSU3.StageB.nmF fr a =
          Work.PSU3.StageB.nmF fr (Work.PSU3.StageB.tau hS fr α⁻¹) := by
        apply Subtype.ext; apply Units.ext; exact h1
      have h3 : a = Work.PSU3.StageB.tau hS fr α⁻¹ := Work.PSU3.StageB.nmF_injective hS fr h2
      refine hne ?_
      rw [← hμt, ← haX, h3]
    have hrel := hparam a hane
    rw [haX, hμt] at hrel
    exact hrel

end Work.PSU3.StageB.NotFpfStep4
