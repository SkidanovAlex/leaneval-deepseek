/-
# `Work.PSU3.StageB.StepB.square_eq_shift_of_good_cover` — the Proposition of p. 274, unconditional

Peterfalvi II Ch. VII §2, the Proposition of p. 274, in the form used by Stage B1: for a *good*
transversal `rep` of the `KW`-orbits on `(Q/Q₀)^#` (common shift `α`) in a frame whose `ζ`
*generates* `W H t` (so that `h(rep i) ∈ W` by §2 (18)), the fixed-point-free hypothesis
`DFpfBar` forces `∃ i, rep i * rep i = zcQF fr α`.

This is `Omega.square_eq_shift_of_good_cover_hKW` with its *global* hypothesis

`hKW : ∀ x ∉ Q₀, h(x) ∈ fr.KW`

**removed**: the three instances of `hKW` that its proof consumes are all *derivable* from
`hS`, `fr`, `hfpf`, the generating hypothesis on `ζ` and `W H t ≤ fr.KW`:

1. `hKW` at the base element `ω₁` — this is §2 (18) plus the cyclic Sylow input:
   `StepB.hcan_mem_W_of_good_generating` (`h(ω₁) ∈ W H t`), transported into `fr.KW` by
   `hWKW : W H t ≤ fr.KW`;
2. `hKW` at the good translate `ω₁ · zcQF fr α` — `StepB.hcan_mul_zcQF_alpha_mem_KW`
   (H4a/H4c: `h(ω₁ · zc α) = ζ · h(ω₁)⁻¹ · ζ⁻¹` with `ζ, h(ω₁) ∈ fr.KW`);
3. `hKW` at `x₅ = (rep k)⁻¹ · zcQF fr r` — `StepB.hcan_inv_mul_zcQF_mem_KW`.  There the source
   ("Moreover by H4, `h(ω_k⁻¹(0,r)) ∈ KW`") is used as follows: `x₅ = (rep k · zcQF fr r)⁻¹` so
   `h(x₅) = t · h(rep k · zc r)⁻¹ · t` (H4b); the cross relation
   `f(ω₁ · zc(r+α)) = (rep k · zc r)^{d₂}` gives, through H4c and H4a,
   `h(rep k · zc r) ∈ fr.KW ⟺ h(ω₁ · zc(r+α)) ∈ fr.KW`; and `h(ω₁ · zc(r+α)) ∈ fr.KW` holds
   because `ω₁ · zc r = ω₁⁻¹`, so `(ω₁ · zc α)⁻¹ = ω₁ · zc(r+α)` and H4b plus (2) give it.

Consequently the Proposition — hence the whole fpf branch of Ch. VII §2 — no longer depends on
the (frame-undetermined, see `StepB/NOTES_S2_final_step.md`) off-frame input `h ∈ KW`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.square_eq_shift_of_good_cover_hKW
import Submission.Work.PSU3.StageB.Omega.fpf_b1
import Submission.Work.PSU3.StageB.Omega.good_of_orbit
import Submission.Work.PSU3.StageB.Omega.omegaHyp_of_good
import Submission.Work.PSU3.StageB.StepB.hcan_mul_zcQF_alpha_mem_KW
import Submission.Work.PSU3.StageB.StepB.self_pos_eq_mem_KW
import Submission.Work.PSU3.StageB.StepB.shifted_pos_eq_mem
import Submission.Work.PSU3.StageB.StepB.hcan_inv_mul_zcQF_mem_KW
import Submission.Work.PSU3.StageB.StepB.hcan_mem_W_of_good_generating

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.StepB

open Work.PSU3.StageB.Omega
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

theorem square_eq_shift_of_good_cover {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hfpf : Work.PSU3.DFpfBar H Q t)
    (hgen : orderOf (fr.ζ : G) = Nat.card ↥(Work.ThmF.W H t))
    (hpow : ∀ x ∈ Submission.Blueprint.twoPoint H t,
      x ^ Nat.card ↥(Work.ThmF.W H t) = 1 → x ∈ Work.ThmF.W H t)
    (hWKW : Work.ThmF.W H t ≤ fr.KW)
    {ι : Type} [Finite ι] (rep : ι → ↥Q) {α : ↥(Work.PSU3.StageB.FX n)}
    (hne : ∀ i, (rep i : G) ∉ fr.Q0)
    (hgood : ∀ i, Work.PSU3.StageB.fcan hS.split (rep i) =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (rep i * Work.PSU3.StageB.zcQF fr α))
    (hcover : ∀ y : ↥Q, (y : G) ∉ fr.Q0 → ∃ i, y ∈ Work.PSU3.StageB.orbKW hS fr (rep i))
    (hdis : ∀ i j, i ≠ j → Multiplicative.toAdd (fr.bar (rep i)) ∉
      Work.PSU3.StageB.orbE fr (Multiplicative.toAdd (fr.bar (rep j)))) :
    ∃ i, rep i * rep i = Work.PSU3.StageB.zcQF fr α := by
  -- `fr.KW` is stable under conjugation by `t` (`Omega.tconjKW_exists`).
  have htN : ∀ w : fr.KW, t * (w : G) * t ∈ fr.KW := fun w => by
    obtain ⟨e, he⟩ := tconjKW_exists hS fr w
    rw [← he]; exact e.2
  have hex : ∃ y : ↥Q, (y : G) ∉ fr.Q0 := by
    obtain ⟨y, hy⟩ := fr.bar_surjective (Multiplicative.ofAdd (1 : E n))
    refine ⟨y, fun hc => ?_⟩
    have h1 : fr.bar y = 1 := (fr.bar_eq_one_iff y).mpr hc
    rw [hy] at h1
    have h2 : (1 : E n) = 0 := by
      have h3 := congrArg Multiplicative.toAdd h1
      simpa using h3
    exact one_ne_zero h2
  haveI : Nonempty ι := ⟨(hcover hex.choose hex.choose_spec).choose⟩
  let j₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let ω₁ : ↥Q := rep j₀
  have hω₁ : (ω₁ : G) ∉ fr.Q0 := hne j₀
  have hω₁f : fcan hS.split ω₁ = qconj hS.split (zetaD fr) (ω₁ * zcQF fr α) := hgood j₀
  -- the `fr.KW`-memberships consumed by the three cases below (all derivable, see the header)
  have hWω₁ : (hcan hS.split ω₁ : G) ∈ Work.ThmF.W H t :=
    hcan_mem_W_of_good_generating hS fr hgen hpow hω₁ hω₁f
  have hω₁KW : ((hcan hS.split ω₁ : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW :=
    hWKW hWω₁
  have hαKW : ((hcan hS.split (ω₁ * zcQF fr α) :
      ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW :=
    hcan_mul_zcQF_alpha_mem_KW hS fr hWKW hω₁ hω₁f hWω₁
  have hω₁1 : (ω₁ : G) ≠ 1 := fun h => hω₁ (by rw [h]; exact Q0_one_mem fr)
  have hsq_mem : ((ω₁ * ω₁ : ↥Q) : G) ∈ fr.Q0 := by
    rw [Subgroup.coe_mul, ← pow_two]
    exact fr.sq_mem_Q0 ω₁ ω₁.2
  have hsq_ne : (ω₁ * ω₁ : ↥Q) ≠ 1 := by
    intro h
    have h2 : (ω₁ : G) * (ω₁ : G) = 1 := by
      have h3 := congrArg (fun z : ↥Q => (z : G)) h
      simpa [Subgroup.coe_mul] using h3
    exact hω₁ ((fr.mem_Q0_iff ω₁ ω₁.2).mpr (by rw [pow_two]; exact h2))
  obtain ⟨r, hr⟩ := exists_zcQF_eq_of_mem_Q0 fr hsq_mem hsq_ne
  have hsq : ω₁ * ω₁ = zcQF fr r := hr.symm
  have hzrQ0 : (zcQF fr r : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ r.2
  have hα_self : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr α))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω₁)) := by
    have h1 : fcan hS.split (ω₁ * zcQF fr α) = kact hS fr (fr.ζ⁻¹ : fr.KW) ω₁ := by
      rw [fcan_zcQF_alpha hS fr hω₁ hω₁f, kact_eq_qconj']
      congr 1
    rw [h1, kact_bar]
    exact ⟨fr.ζ⁻¹, rfl⟩
  have hfzr : ((fcan hS.split (ω₁ * zcQF fr r) : ↥Q) : G) ∉ fr.Q0 := by
    intro hc
    have h3 : ((ω₁ * zcQF fr r : ↥Q) : G) ∈ fr.Q0 :=
      (fcan_mem_Q0_iff hS fr (ω₁ * zcQF fr r)).mp hc
    have h4 : (ω₁ : G) ∈ fr.Q0 := by
      have h5 : (ω₁ * zcQF fr r) * zcQF fr r = ω₁ := by rw [mul_assoc, zcQF_sq fr r, mul_one]
      rw [← h5, Subgroup.coe_mul]
      exact fr.Q0.mul_mem h3 hzrQ0
    exact hω₁ h4
  by_cases hself : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr r))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω₁))
  · have hrα := self_pos_eq_mem_KW hS fr hω₁ hω₁f hsq hself hω₁KW
    exact ⟨j₀, by show ω₁ * ω₁ = zcQF fr α; rw [hrα] at hsq; exact hsq⟩
  · have hr_ne : fval r ≠ fval α := by
      intro h
      apply hself
      have h2 : zcQF fr r = zcQF fr α := Subtype.ext (by rw [zcQF_coe, zcQF_coe, h])
      rw [h2]; exact hα_self
    have hfix : σE (fval r + fval α) = fval r + fval α := by rw [map_add, r.2, α.2]
    have hne0 : fval r + fval α ≠ 0 := by
      intro h
      apply hr_ne
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h
    let x₂ : ↥(FX n) := mkFX (fval r + fval α) hfix hne0
    have hval : fval x₂ = fval r + fval α := fval_mkFX _ _ _
    have hzx₂Q0 : (zcQF fr x₂ : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem _ x₂.2
    have hx2_Q0 : ((ω₁ * zcQF fr x₂ : ↥Q) : G) ∉ fr.Q0 := by
      intro hc
      have h4 : (ω₁ : G) ∈ fr.Q0 := by
        have h5 : (ω₁ * zcQF fr x₂) * zcQF fr x₂ = ω₁ := by
          rw [mul_assoc, zcQF_sq fr x₂, mul_one]
        rw [← h5, Subgroup.coe_mul]
        exact fr.Q0.mul_mem hc hzx₂Q0
      exact hω₁ h4
    have hf2 : ((fcan hS.split (ω₁ * zcQF fr x₂) : ↥Q) : G) ∉ fr.Q0 := by
      intro hc
      exact hx2_Q0 ((fcan_mem_Q0_iff hS fr (ω₁ * zcQF fr x₂)).mp hc)
    by_cases hx2self : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr x₂))) ∈
        orbE fr (Multiplicative.toAdd (fr.bar ω₁))
    · have hrα := shifted_pos_eq_mem hS fr hω₁ hω₁f hsq hval hx2self hαKW
      exact ⟨j₀, by show ω₁ * ω₁ = zcQF fr α; rw [hrα] at hsq; exact hsq⟩
    · -- the cross case
      obtain ⟨i, hi⟩ := hcover (fcan hS.split (ω₁ * zcQF fr r)) hfzr
      obtain ⟨k, hk⟩ := hcover (fcan hS.split (ω₁ * zcQF fr x₂)) hf2
      have hi_ne : i ≠ j₀ := by
        intro heq
        apply hself
        have h3 := (mem_orbKW_iff_orbE hS fr (rep i) (fcan hS.split (ω₁ * zcQF fr r))).mp hi
        rwa [heq] at h3
      have hk_ne : k ≠ j₀ := by
        intro heq
        apply hx2self
        have h3 := (mem_orbKW_iff_orbE hS fr (rep k) (fcan hS.split (ω₁ * zcQF fr x₂))).mp hk
        rwa [heq] at h3
      have hwi : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr r))) ∈
          orbE fr (Multiplicative.toAdd (fr.bar (rep i))) :=
        (mem_orbKW_iff_orbE hS fr (rep i) (fcan hS.split (ω₁ * zcQF fr r))).mp hi
      have hwk : Multiplicative.toAdd (fr.bar (fcan hS.split (ω₁ * zcQF fr x₂))) ∈
          orbE fr (Multiplicative.toAdd (fr.bar (rep k))) :=
        (mem_orbKW_iff_orbE hS fr (rep k) (fcan hS.split (ω₁ * zcQF fr x₂))).mp hk
      obtain ⟨d₀, hd₀⟩ := cross_orbit_shift_proof hS fr hω₁ (hne i) hω₁f (hgood i)
        (hdis j₀ i (Ne.symm hi_ne)) hwi
      obtain ⟨d₂, hd₂⟩ := cross_orbit_shift_proof hS fr hω₁ (hne k) hω₁f (hgood k)
        (hdis j₀ k (Ne.symm hk_ne)) hwk
      have hzq_all : ∀ (hv : σE (fval r + fval α) = fval r + fval α),
          (zcQ fr (fval r + fval α) hv : ↥Q) = zcQF fr r * zcQF fr α := by
        intro hv
        apply Subtype.ext
        simp only [zcQ_coe, Subgroup.coe_mul, zcQF_coe]
        exact fr.zc_add (fval r) (fval α) r.2 α.2
      have hA : fcan hS.split (ω₁ * zcQF fr r) =
          kact hS fr d₀ (rep i * (zcQF fr r * zcQF fr α)) := by
        rw [hd₀, kact_eq_qconj']
        exact congrArg (fun z : ↥Q =>
          qconj hS.split ⟨(d₀ : G), fr.KW_le d₀.2⟩ (rep i * z)) (hzq_all _)
      have hzx₂ : (zcQF fr r * zcQF fr α : ↥Q) = zcQF fr x₂ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, zcQF_coe]
        rw [hval]
        exact (fr.zc_add (fval r) (fval α) r.2 α.2).symm
      have hzq2 : ∀ (hv : σE (fval x₂ + fval α) = fval x₂ + fval α),
          (zcQ fr (fval x₂ + fval α) hv : ↥Q) = zcQF fr r := by
        intro hv
        apply Subtype.ext
        simp only [zcQ_coe, zcQF_coe]
        rw [hval, add_assoc, CharTwo.add_self_eq_zero, add_zero]
      have hB : fcan hS.split (ω₁ * (zcQF fr r * zcQF fr α)) =
          kact hS fr d₂ (rep k * zcQF fr r) := by
        rw [hzx₂]
        rw [hd₂, kact_eq_qconj']
        exact congrArg (fun z : ↥Q =>
          qconj hS.split ⟨(d₂ : G), fr.KW_le d₂.2⟩ (rep k * z)) (hzq2 _)
      obtain ⟨b, hb_eq⟩ := cross_chain_step hS fr hω₁ (hne k) hω₁f hsq hA hB
      have hx₅_Q0 : (((rep k)⁻¹ * zcQF fr r : ↥Q) : G) ∉ fr.Q0 := by
        intro hc
        have hinv : (((rep k)⁻¹ : ↥Q) : G) ∈ fr.Q0 := by
          have h5 : (rep k)⁻¹ * zcQF fr r * zcQF fr r = (rep k)⁻¹ := by
            rw [mul_assoc, zcQF_sq fr r, mul_one]
          rw [← h5, Subgroup.coe_mul]
          exact fr.Q0.mul_mem hc hzrQ0
        exact hne k (by
          have h6 := (fr.Q0).inv_mem hinv
          rwa [Subgroup.coe_inv, inv_inv] at h6)
      have hx₅_1 : (((rep k)⁻¹ * zcQF fr r : ↥Q) : G) ≠ 1 :=
        fun h => hx₅_Q0 (by rw [h]; exact Q0_one_mem fr)
      have hx₅KW : ((hcan hS.split ((rep k)⁻¹ * zcQF fr r) :
          ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW :=
        hcan_inv_mul_zcQF_mem_KW hS fr htN hWKW hω₁ hω₁f hsq hWω₁ (hne k) hB
      set hh : fr.KW := ⟨(hcan hS.split ((rep k)⁻¹ * zcQF fr r) : ↥(twoPoint H t)),
        hx₅KW⟩ with hhh
      have hH5 : fcan hS.split
          ((fcan hS.split ((fcan hS.split (((rep k)⁻¹ * zcQF fr r : ↥Q)⁻¹))⁻¹))⁻¹) =
          kact hS fr hh⁻¹ ((rep k)⁻¹ * zcQF fr r) := by
        apply Subtype.ext
        rw [fcan_jjj hS.split hx₅_1]
        simp only [kact_coe, hhh, Subgroup.coe_inv, inv_inv]
      have hcomp : kact hS fr b (rep i * (zcQF fr r * zcQF fr α)) =
          kact hS fr hh⁻¹ ((rep k)⁻¹ * zcQF fr r) := by rw [← hb_eq, hH5]
      have hposQ0 : ((zcQF fr r * zcQF fr α : ↥Q) : G) ∈ fr.Q0 := by
        rw [Subgroup.coe_mul]
        exact fr.Q0.mul_mem hzrQ0 (by rw [zcQF_coe]; exact fr.zc_mem _ α.2)
      have hbw_i : Multiplicative.toAdd (fr.bar (rep i * (zcQF fr r * zcQF fr α))) =
          Multiplicative.toAdd (fr.bar (rep i)) := toAdd_bar_mul_Q0 fr (rep i) hposQ0
      have hbar_eq : (fr.κ b : E n) * Multiplicative.toAdd (fr.bar (rep i)) =
          (fr.κ hh⁻¹ : E n) * Multiplicative.toAdd (fr.bar ((rep k)⁻¹ * zcQF fr r)) := by
        have h := congrArg (fun z : ↥Q => Multiplicative.toAdd (fr.bar z)) hcomp
        rw [kact_bar, kact_bar, hbw_i] at h
        exact h
      have hbar_k_sq : fr.bar (rep k) * fr.bar (rep k) = 1 := by
        have h := bar_eq_one_of_mem_Q0 fr (x := (rep k) ^ 2) (fr.sq_mem_Q0 (rep k) (rep k).2)
        rw [map_pow, pow_two] at h
        exact h
      have hbarx₅ : Multiplicative.toAdd (fr.bar ((rep k)⁻¹ * zcQF fr r)) =
          Multiplicative.toAdd (fr.bar (rep k)) := by
        rw [map_mul, bar_eq_one_of_mem_Q0 fr hzrQ0, mul_one, map_inv,
          inv_eq_of_mul_eq_one_right hbar_k_sq]
      have hmem_ik : Multiplicative.toAdd (fr.bar (rep i)) ∈
          orbE fr (Multiplicative.toAdd (fr.bar (rep k))) := by
        have h4 : (fr.κ (b⁻¹ * hh⁻¹) : E n) =
            (fr.κ b : E n)⁻¹ * (fr.κ hh⁻¹ : E n) := by
          rw [map_mul fr.κ, map_inv fr.κ, Units.val_mul, Units.val_inv_eq_inv_val]
        refine ⟨b⁻¹ * hh⁻¹, ?_⟩
        rw [h4, mul_assoc]
        calc Multiplicative.toAdd (fr.bar (rep i))
            = 1 * Multiplicative.toAdd (fr.bar (rep i)) := by rw [one_mul]
          _ = ((fr.κ b : E n)⁻¹ * (fr.κ b : E n)) * Multiplicative.toAdd (fr.bar (rep i)) := by
                rw [inv_mul_cancel₀ (Units.ne_zero (fr.κ b))]
          _ = (fr.κ b : E n)⁻¹ * ((fr.κ b : E n) * Multiplicative.toAdd (fr.bar (rep i))) := by
                rw [mul_assoc]
          _ = (fr.κ b : E n)⁻¹ * ((fr.κ hh⁻¹ : E n) *
                Multiplicative.toAdd (fr.bar ((rep k)⁻¹ * zcQF fr r))) := by
                rw [← hbar_eq]
          _ = (fr.κ b : E n)⁻¹ * ((fr.κ hh⁻¹ : E n) * Multiplicative.toAdd (fr.bar (rep k))) := by
                rw [hbarx₅]
      have hik : i = k := by
        by_contra hneik
        exact hdis i k hneik hmem_ik
      have hb : b = hh⁻¹ := by
        apply fr.κ_injective
        apply Units.ext
        have h := hbar_eq
        rw [hbarx₅, ← hik] at h
        exact mul_right_cancel₀ (toAdd_bar_ne_zero fr (hne i)) h
      have hrep_eq : rep k * (zcQF fr r * zcQF fr α) = (rep k)⁻¹ * zcQF fr r := by
        have h := hcomp
        rw [hb, hik] at h
        have h2 := congrArg (kact hS fr (hh⁻¹)⁻¹) h
        simpa [kact_mul, kact_one] using h2
      have hsqk_ne : (rep k * rep k : ↥Q) ≠ 1 := by
        intro h
        have h2 : (rep k : G) * (rep k : G) = 1 := by
          have h3 := congrArg (fun z : ↥Q => (z : G)) h
          simpa [Subgroup.coe_mul] using h3
        exact hne k ((fr.mem_Q0_iff (rep k) (rep k).2).mpr (by rw [pow_two]; exact h2))
      have hsqk_mem : ((rep k * rep k : ↥Q) : G) ∈ fr.Q0 := by
        rw [Subgroup.coe_mul, ← pow_two]
        exact fr.sq_mem_Q0 (rep k) (rep k).2
      obtain ⟨r_k, hr_k⟩ := exists_zcQF_eq_of_mem_Q0 fr hsqk_mem hsqk_ne
      have hsqk : rep k * rep k = zcQF fr r_k := hr_k.symm
      have h2 : zcQF fr r_k * (zcQF fr r * zcQF fr α) = zcQF fr r := by
        rw [← hsqk]
        calc (rep k * rep k) * (zcQF fr r * zcQF fr α)
            = rep k * (rep k * (zcQF fr r * zcQF fr α)) := by group
          _ = rep k * ((rep k)⁻¹ * zcQF fr r) := congrArg (fun z : ↥Q => rep k * z) hrep_eq
          _ = (rep k * (rep k)⁻¹) * zcQF fr r := by group
          _ = zcQF fr r := by rw [mul_inv_cancel, one_mul]
      have hsum : fval r_k + fval r + fval α = fval r := by
        have hh2 : fr.zc (fval r_k) * (fr.zc (fval r) * fr.zc (fval α)) = fr.zc (fval r) := by
          have hh3 := congrArg (fun z : ↥Q => (z : G)) h2
          simpa only [Subgroup.coe_mul, zcQF_coe] using hh3
        have h3 : fr.zc (fval r_k + fval r + fval α) = fr.zc (fval r) := by
          rw [fr.zc_add (fval r_k + fval r) (fval α) (by rw [map_add, r_k.2, r.2]) α.2,
            fr.zc_add (fval r_k) (fval r) r_k.2 r.2, mul_assoc]
          exact hh2
        exact fr.zc_inj (fval r_k + fval r + fval α) (fval r)
          (by rw [map_add, map_add, r_k.2, r.2, α.2]) r.2 h3
      have h7 : fval r_k = fval α := by
        have h8 : fval r_k + fval α = 0 := by
          have hcancel : (fval r_k + fval α) + fval r = fval r := by
            rw [show (fval r_k + fval α) + fval r = fval r_k + fval r + fval α from by abel]
            exact hsum
          exact add_eq_left.mp (by rw [add_comm]; exact hcancel)
        rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h8
        exact h8
      have h9 : zcQF fr r_k = zcQF fr α := by
        apply Subtype.ext
        rw [zcQF_coe, zcQF_coe, h7]
      exact ⟨k, by rw [hsqk, h9]⟩

/-- `fval` is injective on `F*`. -/
lemma fval_injective_uncond : Function.Injective (fval : ↥(FX n) → E n) := by
  intro u v h
  exact Subtype.ext (Units.ext h)

/-- **The good square of §2 (9)/(19)/(20), unconditionally**: in a frame whose `ζ` generates
`W H t` and with `W H t ≤ fr.KW`, `DFpfBar` produces `ω ∈ Q ∖ Q₀` and `α` with
`f(ω) = (ω · zcQF fr α)^ζ` and `ω * ω = zcQF fr α` — the input of `Omega.omegaHyp_of_good`.

This is `Work.PSU3.StageB.exists_good_square_of_hKW` with its off-frame hypothesis `hKW` removed:
the transversal is built as there (orbit representatives `orbSet_exists_rep`, the good element of
each orbit `good_of_orbit`, the common shift `alpha_eq_of_two_orbits`), and the Proposition is the
unconditional `square_eq_shift_of_good_cover` above. -/
theorem exists_good_square {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hfpf : Work.PSU3.DFpfBar H Q t)
    (hgen : orderOf (fr.ζ : G) = Nat.card ↥(Work.ThmF.W H t))
    (hpow : ∀ x ∈ Submission.Blueprint.twoPoint H t,
      x ^ Nat.card ↥(Work.ThmF.W H t) = 1 → x ∈ Work.ThmF.W H t)
    (hWKW : Work.ThmF.W H t ≤ fr.KW) :
    ∃ ω : ↥Q, ∃ α : ↥(Work.PSU3.StageB.FX n), (ω : G) ∉ fr.Q0 ∧
      Work.PSU3.StageB.fcan hS.split ω =
        Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α) ∧
      ω * ω = Work.PSU3.StageB.zcQF fr α := by
  classical
  haveI : Finite (OrbSet fr) := inferInstance
  -- ## orbit representatives in `Q`
  let ωO : OrbSet fr → ↥Q := fun O => Classical.choose (orbSet_exists_rep fr O)
  have hωO_ne : ∀ O : OrbSet fr, (ωO O : G) ∉ fr.Q0 :=
    fun O => (Classical.choose_spec (orbSet_exists_rep fr O)).1
  have hωO_orb : ∀ O : OrbSet fr,
      (O : Set (E n)) = orbE fr (Multiplicative.toAdd (fr.bar (ωO O))) :=
    fun O => (Classical.choose_spec (orbSet_exists_rep fr O)).2
  -- ## the good element of each orbit
  let g : OrbSet fr → ↥Q := fun O => Classical.choose (good_of_orbit hS fr (hωO_ne O))
  have hg : ∀ O : OrbSet fr, g O ∈ orbKW hS fr (ωO O) ∧ ((g O : G) ∉ fr.Q0) ∧
      (∃ α : ↥(FX n), fcan hS.split (g O) =
        qconj hS.split (zetaD fr) (g O * zcQF fr α)) :=
    fun O => Classical.choose_spec (good_of_orbit hS fr (hωO_ne O))
  have hg_ne : ∀ O : OrbSet fr, (g O : G) ∉ fr.Q0 := fun O => (hg O).2.1
  -- ## the good elements lie in their orbit's class
  have hbar_inE : ∀ O : OrbSet fr,
      Multiplicative.toAdd (fr.bar (g O)) ∈ orbE fr (Multiplicative.toAdd (fr.bar (ωO O))) := by
    intro O
    have hmem : g O ∈ orbKW hS fr (ωO O) := (hg O).1
    rwa [mem_orbKW_iff_orbE] at hmem
  have hbar_in : ∀ O : OrbSet fr, Multiplicative.toAdd (fr.bar (g O)) ∈ (O : Set (E n)) := by
    intro O
    rw [hωO_orb O]
    exact hbar_inE O
  have hbar_orb : ∀ O : OrbSet fr,
      orbE fr (Multiplicative.toAdd (fr.bar (g O))) = (O : Set (E n)) := by
    intro O
    rw [orbE_eq_of_mem fr (hbar_inE O), hωO_orb O]
  have hdis : ∀ O₁ O₂ : OrbSet fr, O₁ ≠ O₂ →
      Multiplicative.toAdd (fr.bar (g O₁)) ∉ orbE fr (Multiplicative.toAdd (fr.bar (g O₂))) := by
    intro O₁ O₂ hne hmem
    have h1 : orbE fr (Multiplicative.toAdd (fr.bar (g O₁))) =
        orbE fr (Multiplicative.toAdd (fr.bar (g O₂))) := orbE_eq_of_mem fr hmem
    rw [hbar_orb O₁, hbar_orb O₂] at h1
    exact hne (Subtype.ext h1)
  -- ## common coordinate `α` for all the representatives (Peterfalvi (19)/(20))
  have hgood_ex : ∀ O : OrbSet fr, ∃ α : ↥(FX n), fcan hS.split (g O) =
      qconj hS.split (zetaD fr) (g O * zcQF fr α) := fun O => (hg O).2.2
  let αO : OrbSet fr → ↥(FX n) := fun O => Classical.choose (hgood_ex O)
  have hαO : ∀ O : OrbSet fr, fcan hS.split (g O) =
      qconj hS.split (zetaD fr) (g O * zcQF fr (αO O)) :=
    fun O => Classical.choose_spec (hgood_ex O)
  let O₀ : OrbSet fr := ⟨orbE fr 1, ⟨1, one_ne_zero, rfl⟩⟩
  have hαeq : ∀ O : OrbSet fr, fval (αO O) = fval (αO O₀) := by
    intro O
    by_cases h : O = O₀
    · rw [h]
    · exact alpha_eq_of_two_orbits hS fr (hg_ne O) (hg_ne O₀) (hαO O) (hαO O₀) (hdis O O₀ h)
  have hαeq' : ∀ O : OrbSet fr, αO O = αO O₀ := fun O => fval_injective_uncond (hαeq O)
  -- ## the covering hypothesis
  have hcover : ∀ y : ↥Q, (y : G) ∉ fr.Q0 → ∃ O : OrbSet fr, y ∈ orbKW hS fr (g O) := by
    intro y hy
    refine ⟨⟨orbE fr (Multiplicative.toAdd (fr.bar y)),
      ⟨Multiplicative.toAdd (fr.bar y), toAdd_bar_ne_zero fr hy, rfl⟩⟩, ?_⟩
    have hOe : ((⟨orbE fr (Multiplicative.toAdd (fr.bar y)),
        ⟨Multiplicative.toAdd (fr.bar y), toAdd_bar_ne_zero fr hy, rfl⟩⟩ : OrbSet fr) : Set (E n))
        = orbE fr (Multiplicative.toAdd (fr.bar y)) := rfl
    rw [mem_orbKW_iff_orbE, hbar_orb _, hOe]
    exact orbE_refl fr _
  -- ## the Proposition (p. 274), now without any off-frame input
  obtain ⟨O, hO⟩ := square_eq_shift_of_good_cover hS fr hfpf hgen hpow hWKW g (α := αO O₀) hg_ne
    (fun O => by rw [← hαeq' O]; exact hαO O) hcover hdis
  exact ⟨g O, αO O₀, hg_ne O, (by rw [← hαeq' O]; exact hαO O), hO⟩

end Work.PSU3.StageB.StepB
