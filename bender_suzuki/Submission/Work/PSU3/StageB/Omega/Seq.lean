/-
# `Work.PSU3.StageB.Omega.Seq` — the sequences of Peterfalvi Ch. VII §2 (10)–(18)

Setting: `ω ∈ Q ∖ Q₀` with `f (ω) = (ω · zc α)^ζ` and `α ∈ F*` (the output of §2 (9)),
and `β ∈ E` with `β + β⁻¹ = α` (Ch. VII §2 (12)).  The recursion (11) of the proof is
encoded in closed form (13)/(14) — this is what the formalisation can use, since the
"stopping time" of the recursion is not known before the argument of (15) — and the
recursion identities become lemmas:

* `uSeq β i = (β^{i-1} + β^{1-i})/(β^i + β^{-i})` — §2 (13);
* `vSeq α β i = uSeq β i + α` — because `v_i = u_i + α` in characteristic two;
* `wSeq α β i = ((β^i + β^{-i})/α)²` — the `F*`-coordinate of the `K`-part of `d_i`;
  then §2 (14) says `κ (d_i) = (κ ζ)^i · τ (wSeq α β i)`.
-/
import Mathlib
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

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## The sequences `u_i`, `v_i` of §2 (11) in closed form (13) -/

/-- Peterfalvi's `u_i` (§2 (13)) in closed form.  For `i = 1` this is `0`; the recursion
`u_{i+1} = 1/(α + u_i)` is `uSeq_rec`. -/
noncomputable def uSeq (β : E n) (i : ℕ) : E n :=
  (β ^ i / β + β / β ^ i) / (β ^ i + (β ^ i)⁻¹)

/-- Peterfalvi's `v_i`, which is `u_i + α` in characteristic two. -/
noncomputable def vSeq (α β : E n) (i : ℕ) : E n := uSeq β i + α

/-- The `F*`-coordinate of the `K`-part of `d_i` (§2 (14)). -/
noncomputable def wSeq (α β : E n) (i : ℕ) : E n := ((β ^ i + (β ^ i)⁻¹) / α) ^ 2

lemma uSeq_one (β : E n) : uSeq β 1 = 0 := by
  simp only [uSeq, pow_one]
  rw [show β / β + β / β = 0 from CharTwo.add_self_eq_zero _]
  exact zero_div _

lemma vSeq_one (α β : E n) : vSeq α β 1 = α := by
  rw [vSeq, uSeq_one, zero_add]

/-- The numerator/denominator closed form without division: `u_i · (β^i + β^{-i}) =
β^{i-1} + β^{1-i}`. -/
lemma uSeq_mul (β : E n) {i : ℕ} (hden : β ^ i + (β ^ i)⁻¹ ≠ 0) :
    uSeq β i * (β ^ i + (β ^ i)⁻¹) = β ^ i / β + β / β ^ i := by
  rw [uSeq, div_mul_cancel₀ _ hden]


/-! ## The elements `d_i ∈ KW` of §2 (11)/(14) -/

/-- The `KW`-element `d_i = ζ^i · kElF (τ (λ i))` of §2 (14), for a prescribed family
`λ : ℕ → F*` of `K`-coordinates (in (14), `fval (λ i) = wSeq (fval α) β i`). -/
noncomputable def dSeq (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (lam : ℕ → ↥(FX n)) (i : ℕ) : fr.KW :=
  fr.ζ ^ i * kElF fr (tau hS fr (lam i))

@[simp] lemma dSeq_kappa (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (lam : ℕ → ↥(FX n)) (i : ℕ) :
    fr.κ (dSeq hS fr lam i) = (fr.κ fr.ζ) ^ i * tau hS fr (lam i) := by
  rw [dSeq, map_mul, map_pow, kElF_kappa]

/-- `ζ ∈ KW` acts trivially on `Q₀` (`act_zc_ζ`), hence so do its powers. -/
lemma zeta_pow_conj_zc (fr : CoarseFrame H Q t n) (i : ℕ) (y : E n) (hy : σE y = y) :
    ((fr.ζ : G) ^ i)⁻¹ * fr.zc y * (fr.ζ : G) ^ i = fr.zc y := by
  induction i with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      calc (((fr.ζ : G)) ^ k * fr.ζ)⁻¹ * fr.zc y * (((fr.ζ : G)) ^ k * fr.ζ)
          = (((fr.ζ : G)) ^ k)⁻¹ * (((fr.ζ : G))⁻¹ * fr.zc y * fr.ζ) *
              (((fr.ζ : G)) ^ k) := by group
        _ = (((fr.ζ : G)) ^ k)⁻¹ * fr.zc y * (((fr.ζ : G)) ^ k) := by
              rw [fr.act_zc_ζ y hy]
        _ = fr.zc y := ih

/-- **(14), action form.**  `d_i` acts on `Q₀ ≅ F` by multiplication by `fval (λ i)`. -/
theorem dSeq_act (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (lam : ℕ → ↥(FX n)) (i : ℕ) (y : E n) (hy : σE y = y) :
    (((dSeq hS fr lam i : fr.KW) : G))⁻¹ * fr.zc y * ((dSeq hS fr lam i : fr.KW) : G) =
      fr.zc (fval (lam i) * y) := by
  have hk : ((kElF fr (tau hS fr (lam i)) : fr.KW) : G) ∈ Ksub H t :=
    kElF_mem_Ksub fr (tau hS fr (lam i))
  have h1 : (((dSeq hS fr lam i : fr.KW)) : G)⁻¹ * fr.zc y * ((dSeq hS fr lam i : fr.KW) : G)
      = ((kElF fr (tau hS fr (lam i)) : fr.KW) : G)⁻¹ *
        (((fr.ζ : G) ^ i)⁻¹ * fr.zc y * ((fr.ζ : G) ^ i)) *
        ((kElF fr (tau hS fr (lam i)) : fr.KW) : G) := by
    rw [dSeq]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
    group
  rw [h1, zeta_pow_conj_zc fr i y hy]
  have h2 := fr.act_zc_K (kElF fr (tau hS fr (lam i))) hk y hy
  rw [kElF_kappa] at h2
  have h3 : (((fr.nm ((tau hS fr (lam i)) : (E n)ˣ) : (E n)ˣ) : E n)) = fval (lam i) :=
    congrArg (fun z : ↥(FX n) => ((z : (E n)ˣ) : E n)) (nm_tau hS fr (lam i))
  rw [h3] at h2
  exact h2

lemma dSeq_mem_D (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (lam : ℕ → ↥(FX n)) (i : ℕ) : ((dSeq hS fr lam i : fr.KW) : G) ∈ twoPoint H t :=
  fr.KW_le (dSeq hS fr lam i).2

end Work.PSU3.StageB.Omega
