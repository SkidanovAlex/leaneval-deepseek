import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le

/-!
# The uniform `O(ε)` estimate for the perturbation term, with all hypotheses on `Ω`

This file proves `Work.NN.Core.Lcoef_uniform_estimate_on`: it is the same
product-rule computation as `Work.NN.Core.Lcoef_uniform_estimate`, but the
smallness of the vector fields `V` is assumed directly on the open set `Ω`
(for orders `≤ k`) instead of on all of `ℂⁿ` (for orders `≤ k+1`).
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

open Work.CR.Flat.Holder

universe u v

/-! ### The product-rule bounds for `z ↦ du_z (V_j z)` -/

private lemma choose_sum_eq (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) = ENNReal.ofReal ((2:ℝ)^i) := by
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]

/-- The `C^i`-seminorm of a pointwise evaluation `x ↦ f x (g x)` is bounded by the Leibniz sum
of the seminorms of `f` and `g`. -/
private lemma iDN_eval_le {X : Type*} {E : Type*} {G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : X → E →L[ℝ] G} {g : X → E} {Ω : Set X} (i : ℕ)
    (hf : ContDiffOn ℝ (i : ℕ∞) f Ω) (hg : ContDiffOn ℝ (i : ℕ∞) g Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    iDN i (fun x => (f x) (g x)) Ω ≤
      ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (iDN j f Ω * iDN (i - j) g Ω) := by
  let B : (E →L[ℝ] G) →L[ℝ] E →L[ℝ] G := ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ G)
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  have hfun : (fun x => B (f x) (g x)) = fun x => (f x) (g x) := by
    funext x; rfl
  have h := iDN_bilinear_le B i hf hg hΩ
  rw [hfun] at h
  refine h.trans ?_
  calc ENNReal.ofReal ‖B‖ * _ ≤ 1 * _ := mul_le_mul_left (ENNReal.ofReal_le_one.mpr hB) _
    _ = _ := one_mul _

/-- The `C^{i,α}`-Hölder seminorm of a pointwise evaluation `x ↦ f x (g x)` is bounded by the
Leibniz sum of the seminorms of `f` and `g`. -/
private lemma hSN_eval_le {X : Type u} {E : Type u} {G : Type u}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : X → E →L[ℝ] G} {g : X → E} {Ω : Set X} (i : ℕ) (α : ℝ)
    (hf : ContDiffOn ℝ (i : ℕ∞) f Ω) (hg : ContDiffOn ℝ (i : ℕ∞) g Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    hSN i α (fun x => (f x) (g x)) Ω ≤
      ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω) := by
  let B : (E →L[ℝ] G) →L[ℝ] E →L[ℝ] G := ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ G)
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  have hfun : (fun x => B (f x) (g x)) = fun x => (f x) (g x) := by
    funext x; rfl
  have h := hSN_bilinear_le i α B hf hg hΩ
  rw [hfun] at h
  refine h.trans ?_
  calc ENNReal.ofReal ‖B‖ * _ ≤ 1 * _ := mul_le_mul_left (ENNReal.ofReal_le_one.mpr hB) _
    _ = _ := one_mul _

/-! ### The uniform estimate -/

/-- **The perturbation term is `O(ε)` in the `C^{k,α}`-norm, with all hypotheses on `Ω`.**  Let
`V : Fin n → Cn n → Cn n` be smooth vector fields which are `ε`-small in `C^{k,α}` on an open
set `Ω`.  Then for every `u` of class `C^{k+1}` on `Ω`, the `C^{k,α}`-norm on `Ω` of
`j ↦ du (V j)` is bounded by `C ε` times the `C^{k+1,α}`-norm of `u` on `Ω`, with `C`
depending only on `k` and `α`. -/
theorem Lcoef_uniform_estimate_on {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Fin n → Work.NN.Core.Cn n → Work.NN.Core.Cn n) (ε : ℝ), 0 ≤ ε →
        (∀ i, ContDiff ℝ (k + 1) (V i)) →
        ∀ (Ω : Set (Work.NN.Core.Cn n)), IsOpen Ω →
        (∀ i, ∀ l ≤ k,
            Work.CR.Flat.Holder.iDN l (V i) Ω ≤ ENNReal.ofReal ε ∧
            Work.CR.Flat.Holder.hSN l α (V i) Ω ≤ ENNReal.ofReal ε) →
        ∀ (u : Work.NN.Core.Cn n → ℂ),
          ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ENat) u Ω →
          ∀ j : Fin n,
            Work.CR.Flat.holderNorm k α
                (fun z => fderivWithin ℝ u Ω z (V j z)) Ω
              ≤ ENNReal.ofReal C * (ENNReal.ofReal ε *
                  Work.CR.Flat.holderNorm (k + 1) α u Ω) := by
  refine ⟨(k + 1 : ℝ) * (2 * (4 * (2 : ℝ) ^ k)), ?_, ?_⟩
  · have hk : (0 : ℝ) < (k + 1 : ℝ) := by exact_mod_cast Nat.succ_pos k
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    positivity
  · intro V ε hε hVcont Ω hΩopen hV u hu j
    have hΩ : UniqueDiffOn ℝ Ω := hΩopen.uniqueDiffOn
    set f : Cn n → (Cn n →L[ℝ] ℂ) := fun z => fderivWithin ℝ u Ω z with hfdef
    set g : Cn n → Cn n := V j with hgdef
    set F : Cn n → ℂ := fun z => (fderivWithin ℝ u Ω z) (V j z) with hFdef
    have hFfg : F = fun z => f z (g z) := by rw [hFdef, hfdef, hgdef]
    -- smoothness of the two factors
    have hf_cont : ∀ i ≤ k, ContDiffOn ℝ (i : ℕ∞) f Ω := by
      intro i hi
      rw [hfdef]
      exact hu.fderivWithin hΩ (by exact_mod_cast Nat.succ_le_succ hi)
    have hg_cont : ∀ i ≤ k, ContDiffOn ℝ (i : ℕ∞) g Ω := by
      intro i hi
      rw [hgdef]
      exact ((hVcont j).contDiffOn.of_le (by exact_mod_cast (le_trans hi (Nat.le_succ k))))
    -- the seminorm bounds
    have hNw : ∀ l ≤ k + 1, iDN l u Ω ≤ Work.CR.Flat.holderNorm (k + 1) α u Ω :=
      fun l hl => Work.CR.Flat.iterDerivNorm_le_holderNorm (k + 1) α u Ω hl
    have hNsw : ∀ l ≤ k + 1, hSN l α u Ω ≤ Work.CR.Flat.holderNorm (k + 1) α u Ω :=
      fun l hl => Work.CR.Flat.holderSeminorm_le_holderNorm (k + 1) α u Ω hl
    have hfi : ∀ i ≤ k, iDN i f Ω ≤ Work.CR.Flat.holderNorm (k + 1) α u Ω := by
      intro i hi
      rw [hfdef, iDN_fderivWithin i u Ω hΩ]
      exact hNw (i + 1) (by omega)
    have hfh : ∀ i ≤ k, hSN i α f Ω ≤ Work.CR.Flat.holderNorm (k + 1) α u Ω := by
      intro i hi
      rw [hfdef, hSN_fderivWithin i α u Ω hΩ]
      exact hNsw (i + 1) (by omega)
    have hgi : ∀ i ≤ k, iDN i g Ω ≤ ENNReal.ofReal ε := by
      intro i hi
      rw [hgdef]
      exact (hV j i hi).1
    have hgh : ∀ i ≤ k, hSN i α g Ω ≤ ENNReal.ofReal ε := by
      intro i hi
      rw [hgdef]
      exact (hV j i hi).2
    -- the two top-order bounds
    have hidnF : ∀ i ≤ k, iDN i F Ω ≤
        ENNReal.ofReal (4 * (2:ℝ)^k * ε) * Work.CR.Flat.holderNorm (k + 1) α u Ω := by
      intro i hi
      have h := iDN_eval_le (X := Cn n) i (hf_cont i hi) (hg_cont i hi) hΩ
      rw [hFfg]
      refine h.trans ?_
      calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
              (iDN j f Ω * iDN (i - j) g Ω)
          ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
              (Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjle : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have h1 : iDN j f Ω ≤ Work.CR.Flat.holderNorm (k + 1) α u Ω := hfi j (by omega)
            have h2 : iDN (i - j) g Ω ≤ ENNReal.ofReal ε := hgi (i - j) (by omega)
            gcongr
        _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) *
              (Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε) := by
            rw [Finset.sum_mul]
        _ = ENNReal.ofReal ((2:ℝ)^i) *
              (Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε) := by
            rw [choose_sum_eq]
        _ ≤ ENNReal.ofReal (4 * (2:ℝ)^k * ε) *
              Work.CR.Flat.holderNorm (k + 1) α u Ω := by
            rw [mul_comm (Work.CR.Flat.holderNorm (k + 1) α u Ω) (ENNReal.ofReal ε),
              ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
            have h2i : (2:ℝ)^i ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hi
            have h2k0 : (0:ℝ) ≤ (2:ℝ)^k := by positivity
            nlinarith [h2i, hε, h2k0]
    have hhsnF : ∀ i ≤ k, hSN i α F Ω ≤
        ENNReal.ofReal (4 * (2:ℝ)^k * ε) * Work.CR.Flat.holderNorm (k + 1) α u Ω := by
      intro i hi
      have h := hSN_eval_le (X := Cn n) i α (hf_cont i hi) (hg_cont i hi) hΩ
      rw [hFfg]
      refine h.trans ?_
      calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
              (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω)
          ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
              (Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε
                + Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjle : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have h1 : hSN j α f Ω ≤ Work.CR.Flat.holderNorm (k + 1) α u Ω := hfh j (by omega)
            have h2 : iDN (i - j) g Ω ≤ ENNReal.ofReal ε := hgi (i - j) (by omega)
            have h3 : iDN j f Ω ≤ Work.CR.Flat.holderNorm (k + 1) α u Ω := hfi j (by omega)
            have h4 : hSN (i - j) α g Ω ≤ ENNReal.ofReal ε := hgh (i - j) (by omega)
            gcongr
        _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) *
              (Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε
                + Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε) := by
            rw [Finset.sum_mul]
        _ = ENNReal.ofReal ((2:ℝ)^i) *
              (Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε
                + Work.CR.Flat.holderNorm (k + 1) α u Ω * ENNReal.ofReal ε) := by
            rw [choose_sum_eq]
        _ ≤ ENNReal.ofReal (4 * (2:ℝ)^k * ε) *
              Work.CR.Flat.holderNorm (k + 1) α u Ω := by
            rw [mul_comm (Work.CR.Flat.holderNorm (k + 1) α u Ω) (ENNReal.ofReal ε)]
            rw [← add_mul, ← ENNReal.ofReal_add hε hε, show ε + ε = 2 * ε from by ring]
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            rw [show (2:ℝ)^i * (2 * ε) = (2:ℝ)^(i+1) * ε from by rw [pow_succ]; ring]
            refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
            have h2i : (2:ℝ)^(i+1) ≤ (2:ℝ)^(k+1) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            have h2k0 : (0:ℝ) ≤ (2:ℝ)^k := by positivity
            have hp : (2:ℝ)^(k+1) = 2 * (2:ℝ)^k := by rw [pow_succ]; ring
            nlinarith [h2i, hε, h2k0, hp]
    -- summing over the orders
    have hstep : ∀ i ≤ k, iDN i F Ω + hSN i α F Ω ≤
        ENNReal.ofReal (2 * (4 * (2:ℝ)^k * ε)) * Work.CR.Flat.holderNorm (k + 1) α u Ω := by
      intro i hi
      have h1 := hidnF i hi
      have h2 := hhsnF i hi
      have hc : ENNReal.ofReal (4 * (2:ℝ)^k * ε) + ENNReal.ofReal (4 * (2:ℝ)^k * ε)
          = ENNReal.ofReal (2 * (4 * (2:ℝ)^k * ε)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      calc iDN i F Ω + hSN i α F Ω
          ≤ ENNReal.ofReal (4 * (2:ℝ)^k * ε) * Work.CR.Flat.holderNorm (k + 1) α u Ω
            + ENNReal.ofReal (4 * (2:ℝ)^k * ε) * Work.CR.Flat.holderNorm (k + 1) α u Ω :=
            add_le_add h1 h2
        _ = (ENNReal.ofReal (4 * (2:ℝ)^k * ε) + ENNReal.ofReal (4 * (2:ℝ)^k * ε)) *
              Work.CR.Flat.holderNorm (k + 1) α u Ω := by rw [← add_mul]
        _ = ENNReal.ofReal (2 * (4 * (2:ℝ)^k * ε)) *
              Work.CR.Flat.holderNorm (k + 1) α u Ω := by rw [hc]
    have hcnt : (∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (2 * (4 * (2:ℝ)^k * ε)))
        = ENNReal.ofReal ((k + 1 : ℝ) * (2 * (4 * (2:ℝ)^k * ε))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast (k + 1),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring
    have hFbound : Work.CR.Flat.holderNorm k α F Ω
        ≤ ENNReal.ofReal ((k + 1 : ℝ) * (2 * (4 * (2:ℝ)^k * ε))) *
            Work.CR.Flat.holderNorm (k + 1) α u Ω := by
      calc Work.CR.Flat.holderNorm k α F Ω
          = ∑ i ∈ Finset.range (k + 1), (iDN i F Ω + hSN i α F Ω) := by
            rw [Work.CR.Flat.holderNorm]
            rfl
        _ ≤ ∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (2 * (4 * (2:ℝ)^k * ε)) *
              Work.CR.Flat.holderNorm (k + 1) α u Ω :=
            Finset.sum_le_sum fun i hi =>
              hstep i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        _ = (∑ i ∈ Finset.range (k + 1), ENNReal.ofReal (2 * (4 * (2:ℝ)^k * ε))) *
              Work.CR.Flat.holderNorm (k + 1) α u Ω := by rw [Finset.sum_mul]
        _ = ENNReal.ofReal ((k + 1 : ℝ) * (2 * (4 * (2:ℝ)^k * ε))) *
              Work.CR.Flat.holderNorm (k + 1) α u Ω := by rw [hcnt]
    refine hFbound.trans ?_
    have hCe : (k + 1 : ℝ) * (2 * (4 * (2:ℝ)^k * ε))
        = ((k + 1 : ℝ) * (2 * (4 * (2:ℝ)^k))) * ε := by ring
    rw [hCe, ENNReal.ofReal_mul (by positivity), mul_assoc]

end Work.NN.Core
