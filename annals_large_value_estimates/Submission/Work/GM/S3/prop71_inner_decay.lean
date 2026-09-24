import Mathlib
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.w2C_iteratedDeriv_bound

namespace Work.GM.S3

open Submission.LargeValues
open scoped BigOperators

/-!
# Non-stationary phase for the inner integral of GM Proposition 7.1

This file proves `Work.GM.S3.prop71_inner_decay`, the decay of the inner (linear) oscillatory
integral

`innerInt N m v = ∫ u, exp(-2πi·(N·(m₁v₁+m₂v₂+m₃))·u) · w₂(u,v) du`,
`w₂(u,v) = u² w(u)² w(v₁u)² w(v₂u)²`,

by repeated integration by parts.  The engine is `Work.GM.S3.osc_integral_decay`, which needs,
for the weight `φ = w₂(·,v)`:

* `C^∞` smoothness, `w2v_contDiff`;
* vanishing off `[1,2]`, `w2v_eq_zero_off`;
* a derivative bound `∀ i ≤ j, ∀ x, ‖φ^{(i)}(x)‖ ≤ B` with `B` **uniform in `v ∈ pbox`**,
  `w2v_iteratedDeriv_bound`.  This last point is GM's "for any `j`, `w₂(u₃,v₁,v₂)` has `j`-th
  derivative with respect to `u₃` bounded by `O_j(1)`": the point is that the `v`-dependence
  enters only through the factors `w(vᵢu₃)²`, whose `i`-th derivative is `vᵢ^i·(…)`, and
  `|vᵢ| ≤ 2` on `pbox`.
-/

/-- `w(u)²` as a complex valued function is `C^∞`. -/
private theorem w2C_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w2C := by
  have h : w2C = fun u : ℝ => ((bumpW u ^ 2 : ℝ) : ℂ) := funext fun u => w2C_eq u
  rw [h]
  exact Complex.ofRealCLM.contDiff.comp (bumpW_contDiff.pow 2)

/-- Leibniz's formula bounds the iterated derivative of a product by the iterated derivatives of
the factors: if `‖f^{(i)}‖ ≤ Cf` and `‖g^{(i)}‖ ≤ Cg` for `i ≤ j` then
`‖(fg)^{(i)}‖ ≤ (j+1) 2^j Cf Cg` for `i ≤ j`. -/
private lemma iteratedDeriv_mul_bound {j : ℕ} {f g : ℝ → ℂ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hbdf : ∀ i ≤ j, ∀ x : ℝ, ‖iteratedDeriv i f x‖ ≤ Cf)
    (hbdg : ∀ i ≤ j, ∀ x : ℝ, ‖iteratedDeriv i g x‖ ≤ Cg) :
    ∀ i ≤ j, ∀ x : ℝ,
      ‖iteratedDeriv i (f * g) x‖ ≤ ((j : ℝ) + 1) * 2 ^ j * (Cf * Cg) := by
  intro i hi x
  have hfi : ContDiffAt ℝ ((i : ℕ∞) : WithTop ℕ∞) f x :=
    (hf.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgi : ContDiffAt ℝ ((i : ℕ∞) : WithTop ℕ∞) g x :=
    (hg.contDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDeriv_mul hfi hgi]
  have hCG : (0 : ℝ) ≤ Cf * Cg := mul_nonneg hCf hCg
  calc ‖∑ l ∈ Finset.range (i + 1),
        (i.choose l : ℂ) * iteratedDeriv l f x * iteratedDeriv (i - l) g x‖
      ≤ ∑ l ∈ Finset.range (i + 1),
          ‖(i.choose l : ℂ) * iteratedDeriv l f x * iteratedDeriv (i - l) g x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _l ∈ Finset.range (i + 1), (2 : ℝ) ^ j * (Cf * Cg) := by
        refine Finset.sum_le_sum (fun l hl => ?_)
        have hl' : l ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
        have h1 : ‖iteratedDeriv l f x‖ ≤ Cf := hbdf l (le_trans hl' hi) x
        have h2 : ‖iteratedDeriv (i - l) g x‖ ≤ Cg :=
          hbdg (i - l) (le_trans (Nat.sub_le _ _) hi) x
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        have hcl : (i.choose l : ℝ) ≤ (2 : ℝ) ^ j := by
          have h1' : (i.choose l : ℝ) ≤ (2 : ℝ) ^ i := by
            exact_mod_cast (Nat.choose_le_two_pow i l)
          exact h1'.trans (pow_le_pow_right₀ (by norm_num) hi)
        calc (i.choose l : ℝ) * ‖iteratedDeriv l f x‖ * ‖iteratedDeriv (i - l) g x‖
            ≤ (2 : ℝ) ^ j * Cf * Cg := by
              apply mul_le_mul (mul_le_mul hcl h1 (norm_nonneg _) (by positivity)) h2
                (norm_nonneg _)
              positivity
          _ = (2 : ℝ) ^ j * (Cf * Cg) := by ring
    _ = ((i : ℝ) + 1) * ((2 : ℝ) ^ j * (Cf * Cg)) := by
        rw [Finset.sum_const, Finset.card_range]
        ring
    _ ≤ ((j : ℝ) + 1) * 2 ^ j * (Cf * Cg) := by
        have hi1 : ((i : ℝ) + 1) ≤ ((j : ℝ) + 1) := by
          have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hi
          linarith
        have h2j : (0 : ℝ) ≤ (2 : ℝ) ^ j * (Cf * Cg) := by positivity
        calc ((i : ℝ) + 1) * ((2 : ℝ) ^ j * (Cf * Cg))
            ≤ ((j : ℝ) + 1) * ((2 : ℝ) ^ j * (Cf * Cg)) :=
              mul_le_mul_of_nonneg_right hi1 h2j
          _ = ((j : ℝ) + 1) * 2 ^ j * (Cf * Cg) := by ring

/-- The `v`-independent factor `u ↦ u² w(u)²` of `w₂` has bounded iterated derivatives
(it is `C^∞` with compact support). -/
private lemma exists_bound_sq_w2C (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ j, ∀ x : ℝ,
      ‖iteratedDeriv i (fun u : ℝ => (u : ℂ) ^ 2 * w2C u) x‖ ≤ C := by
  let AR : ℝ → ℝ := fun u => u ^ 2 * bumpW u ^ 2
  have hARs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) AR := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => u ^ 2) := contDiff_id.pow 2
    exact h1.mul (bumpW_contDiff.pow 2)
  have hARcs : HasCompactSupport AR := HasCompactSupport.intro isCompact_Icc (fun x hx => by
    show x ^ 2 * bumpW x ^ 2 = 0
    rw [bumpW_eq_zero_of_notMem hx]
    ring)
  choose Ck hCk using fun k =>
    Commons.Analysis.Calculus.exists_bound_iteratedDeriv_of_hasCompactSupport_smooth hARs hARcs k
  refine ⟨∑ k ∈ Finset.range (j + 1), Ck k, Finset.sum_nonneg (fun k _ => (hCk k).1), ?_⟩
  have hAeq : (fun u : ℝ => (u : ℂ) ^ 2 * w2C u) = fun u : ℝ => ((AR u : ℝ) : ℂ) := by
    funext u
    show (u : ℂ) ^ 2 * w2C u = ((u ^ 2 * bumpW u ^ 2 : ℝ) : ℂ)
    rw [w2C_eq]
    push_cast
    ring
  intro i hi x
  rw [hAeq, iteratedDeriv_ofReal_comp]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hmem : i ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact ((hCk i).2 x).trans (Finset.single_le_sum (fun k _ => (hCk k).1) hmem)

/-- For `|c| ≤ 2`, the composed factor `u ↦ w(cu)²` has iterated derivatives bounded by
`2^j · sup_{k ≤ j} ‖w^{(k)}‖_∞` for all orders `≤ j`. -/
private lemma exists_bound_comp_smul (j : ℕ) {c : ℝ} (hc : |c| ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ j, ∀ x : ℝ,
      ‖iteratedDeriv i (fun u : ℝ => w2C (c * u)) x‖ ≤ C := by
  obtain ⟨Cw, hCw0, hCw⟩ := w2C_iteratedDeriv_bound j
  refine ⟨2 ^ j * Cw, by positivity, ?_⟩
  intro i hi x
  rw [iteratedDeriv_comp_const_smul (w2C_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) c,
    norm_smul]
  have hnorm : ‖(c : ℝ) ^ i‖ = |c| ^ i := by rw [Real.norm_eq_abs, abs_pow]
  rw [hnorm]
  have h1 : |c| ^ i ≤ (2 : ℝ) ^ i := pow_le_pow_left₀ (abs_nonneg c) hc i
  have h2 : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hi
  calc |c| ^ i * ‖iteratedDeriv i w2C (c * x)‖
      ≤ (2 : ℝ) ^ i * Cw :=
        mul_le_mul h1 (hCw i hi (c * x)) (norm_nonneg _) (by positivity)
    _ ≤ (2 : ℝ) ^ j * Cw := mul_le_mul_of_nonneg_right h2 hCw0

/-- GM, proof of Prop 7.1: `w₂(·,v)` has `C^∞` derivatives in `u₃`, bounded uniformly over
`v ∈ pbox = [1/2,2]²`. -/
private theorem w2v_iteratedDeriv_bound (j : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v : ℝ × ℝ, v ∈ pbox → ∀ i ≤ j, ∀ x : ℝ,
      ‖iteratedDeriv i (w2v v) x‖ ≤ B := by
  obtain ⟨QA, hQA0, hQA⟩ := exists_bound_sq_w2C j
  obtain ⟨Cw, hCw0, hCw⟩ := w2C_iteratedDeriv_bound j
  set Cc : ℝ := 2 ^ j * Cw with hCcdef
  have hCc0 : 0 ≤ Cc := by positivity
  have hcomp : ∀ c : ℝ, |c| ≤ 2 → ∀ i ≤ j, ∀ x : ℝ,
      ‖iteratedDeriv i (fun u : ℝ => w2C (c * u)) x‖ ≤ Cc := by
    intro c hc i hi x
    rw [iteratedDeriv_comp_const_smul (w2C_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) c,
      norm_smul, show ‖(c : ℝ) ^ i‖ = |c| ^ i by rw [Real.norm_eq_abs, abs_pow]]
    have h1 : |c| ^ i ≤ (2 : ℝ) ^ i := pow_le_pow_left₀ (abs_nonneg c) hc i
    have h2 : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hi
    calc |c| ^ i * ‖iteratedDeriv i w2C (c * x)‖
        ≤ (2 : ℝ) ^ i * Cw :=
          mul_le_mul h1 (hCw i hi (c * x)) (norm_nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ j * Cw := mul_le_mul_of_nonneg_right h2 hCw0
      _ = Cc := by rw [hCcdef]
  have hAc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (u : ℂ) ^ 2 * w2C u) :=
    (Complex.ofRealCLM.contDiff.pow 2).mul w2C_contDiff
  have hD0 : (0 : ℝ) ≤ ((j : ℝ) + 1) * 2 ^ j * (QA * Cc) := by positivity
  refine ⟨((j : ℝ) + 1) * 2 ^ j * ((((j : ℝ) + 1) * 2 ^ j * (QA * Cc)) * Cc) + 1, by positivity, ?_⟩
  intro v hv i hi x
  have hv' : v.1 ∈ Set.Icc (1 / 2 : ℝ) 2 ∧ v.2 ∈ Set.Icc (1 / 2 : ℝ) 2 := by
    simpa only [pbox, Set.mem_prod, Set.mem_Icc] using hv
  have hv1 : |v.1| ≤ 2 := abs_le.mpr ⟨by linarith [hv'.1.1], hv'.1.2⟩
  have hv2 : |v.2| ≤ 2 := abs_le.mpr ⟨by linarith [hv'.2.1], hv'.2.2⟩
  have hB1c : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => w2C (v.1 * u)) :=
    w2C_contDiff.comp (contDiff_const.mul contDiff_id)
  have hB2c : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => w2C (v.2 * u)) :=
    w2C_contDiff.comp (contDiff_const.mul contDiff_id)
  have hP1 : ∀ k ≤ j, ∀ y : ℝ,
      ‖iteratedDeriv k ((fun u : ℝ => (u : ℂ) ^ 2 * w2C u) *
        (fun u : ℝ => w2C (v.1 * u))) y‖ ≤ ((j : ℝ) + 1) * 2 ^ j * (QA * Cc) :=
    iteratedDeriv_mul_bound hAc hB1c hQA0 hCc0 hQA (hcomp v.1 hv1)
  have hP2 : ∀ k ≤ j, ∀ y : ℝ,
      ‖iteratedDeriv k (((fun u : ℝ => (u : ℂ) ^ 2 * w2C u) *
        (fun u : ℝ => w2C (v.1 * u))) * (fun u : ℝ => w2C (v.2 * u))) y‖
        ≤ ((j : ℝ) + 1) * 2 ^ j * ((((j : ℝ) + 1) * 2 ^ j * (QA * Cc)) * Cc) :=
    iteratedDeriv_mul_bound (hAc.mul hB1c) hB2c hD0 hCc0 hP1 (hcomp v.2 hv2)
  have hfun : w2v v = ((fun u : ℝ => (u : ℂ) ^ 2 * w2C u) *
      (fun u : ℝ => w2C (v.1 * u))) * (fun u : ℝ => w2C (v.2 * u)) := rfl
  rw [hfun]
  exact (hP2 i hi x).trans (le_add_of_nonneg_right zero_le_one)

/-- `w₂(·,v)` is `C^∞`. -/
private theorem w2v_contDiff (v : ℝ × ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w2v v) := by
  have hsq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (u : ℂ) ^ 2) :=
    Complex.ofRealCLM.contDiff.pow 2
  rw [show w2v v = ((fun u : ℝ => (u : ℂ) ^ 2) * w2C) *
      (fun u : ℝ => w2C (v.1 * u)) * (fun u : ℝ => w2C (v.2 * u)) from rfl]
  exact ((hsq.mul w2C_contDiff).mul
    (w2C_contDiff.comp (contDiff_const.mul contDiff_id))).mul
    (w2C_contDiff.comp (contDiff_const.mul contDiff_id))

/-- `w₂(·,v)` vanishes off `[1,2]`. -/
private theorem w2v_eq_zero_off (v : ℝ × ℝ) {x : ℝ} (hx : x ∉ Set.Icc 1 2) : w2v v x = 0 := by
  rw [show w2v v x = (x : ℂ) ^ 2 * w2C x * w2C (v.1 * x) * w2C (v.2 * x) from rfl,
    w2C_eq_zero_of_notMem hx]
  ring

/-- **Non-stationary phase for the inner integral.** For every `j` there is `C > 0` such that for
all `N : ℕ`, `m : ℤ³` and `v ∈ [1/2,2]²`, if `N·(m₁v₁+m₂v₂+m₃) ≠ 0` then

`‖innerInt N m v‖ ≤ C / |N(m₁v₁+m₂v₂+m₃)|^j`.

This is GM Prop 7.1's "for any `j`, the `j`-th derivative of `w₂` with respect to `u₃` is `O_j(1)`,
so the inner integral is `O_j((N|m₁v₁+m₂v₂+m₃|)^{-j})` by repeated integration by parts (equivalently
`O(T^{-300})` unless `|m₁v₁+m₂v₂+m₃| ≤ T^η/N`).

Proof route: `innerInt N m v = ∫ u, exp (-(2πi·A·u)) * w2v v u` with `A = N·phas m v`, and the
integrand is exactly the shape handled by `Work.GM.S3.osc_integral_decay j`:
it gives `C ≥ 1` with `‖∫ u, exp(-(2πiAu)) * φ u‖ ≤ C * B / |A|^j` for every smooth `φ` supported in
`[1,2]` with `∀ i ≤ j, ∀ x, ‖iteratedDeriv i φ x‖ ≤ B`. Take `φ = w2v v` (smoothness: a product of
`bumpW`'s composed with `u ↦ v.u`; support: `w(u) = 0` for `u ∉ [1,2]`) and
`B = sup_{v ∈ [1/2,2]², i ≤ j} sup_x ‖iteratedDeriv i (w2v v) x‖`, which is finite by
`Work.GM.S3.prop71_w2v_deriv` (a companion file being written in parallel; if it is present you may
import `Submission.Work.GM.S3.prop71_w2v_deriv`, otherwise prove the same bound directly using
`iteratedDeriv_mul` and `iteratedDeriv_comp_const_smul` and `Submission.LargeValues.bumpW_deriv_bdd`,
bounding `|v.1|^k, |v.2|^k ≤ 2^k` on `pbox`). -/
theorem prop71_inner_decay (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (m : ℤ × ℤ × ℤ) (v : ℝ × ℝ), v ∈ pbox →
      (N : ℝ) * phas m v ≠ 0 →
      ‖innerInt N m v‖ ≤ C / |(N : ℝ) * phas m v| ^ j := by
  obtain ⟨Co, hCo, hosc⟩ := osc_integral_decay j
  obtain ⟨B, hB, hBd⟩ := w2v_iteratedDeriv_bound j
  refine ⟨Co * B, mul_pos hCo hB, ?_⟩
  intro N m v hv hne
  have h := hosc B (w2v v) (w2v_contDiff v) (fun x hx => w2v_eq_zero_off v hx)
    (fun i hi x => hBd v hv i hi x) ((N : ℝ) * phas m v) hne
  rw [innerInt]
  convert h using 1
  push_cast
  ring

end Work.GM.S3
