/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymExpBase
import Submission.Vinogradov.LocalisedDecoupling

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §4: the crude (trivial) bound for the asymmetric bilinear constants

The trivial bound for the asymmetric bilinear decoupling inequality of GLYZ Definition 3.1,
obtained from Tonelli, a pointwise weighted Hölder inequality inside the convolution, Hölder in the
space variable and Cauchy–Schwarz.  It shows that the exponent `1/2` always works, with a constant
independent of the data and of the level, whence the exponent set `AsymExpSet k hk l b` is
nonempty (`half_mem_asymExpSet`), which is what the `sInf` API needs.

The content of this module is *slow to elaborate* (the `ℝ≥0∞`-valued `rpow` bookkeeping on
`WithLp`-valued spaces); it is therefore split off from `AsymExpBase.lean`, so that the later
bootstrap work only needs its (cached) object file.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 16000000

namespace Submission.Vinogradov

/-! ## 3. The crude (trivial) bound for the asymmetric bilinear inequality -/

/-- The Fubini/translation computation `∫⁻ x, (|F|^r ∗ Ψ)(x) = (∫⁻Ψ)·∫⁻|F|^r`. -/
lemma lintegral_convPow_eq (k : ℕ) (r : ℝ) {F : E k → ℂ} (hF : Measurable F)
    {Ψ : E k → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ x, convPow k r F Ψ x
      = (∫⁻ y, Ψ y) * (∫⁻ u, (‖F u‖₊ : ℝ≥0∞) ^ r) := by
  have h1 : Measurable (fun p : E k × E k => (‖F (p.1 - p.2)‖₊ : NNReal)) :=
    (hF.comp (measurable_fst.sub measurable_snd)).nnnorm
  have hmeas : AEMeasurable (Function.uncurry fun x y : E k => (‖F (x - y)‖₊ : ℝ≥0∞) ^ r * Ψ y)
      (volume.prod volume) :=
    ((h1.coe_nnreal_ennreal.pow_const r).mul (hΨ.comp measurable_snd)).aemeasurable
  unfold convPow
  rw [lintegral_lintegral_swap hmeas]
  have htrans : ∀ y : E k,
      ∫⁻ x, (‖F (x - y)‖₊ : ℝ≥0∞) ^ r = ∫⁻ u, (‖F u‖₊ : ℝ≥0∞) ^ r := by
    intro y
    have h := lintegral_add_right_eq_self (μ := (volume : Measure (E k)))
      (fun u : E k => (‖F u‖₊ : ℝ≥0∞) ^ r) (-y)
    have h2 : (fun x : E k => (‖F (x - y)‖₊ : ℝ≥0∞) ^ r)
        = (fun x : E k => (‖F (x + (-y))‖₊ : ℝ≥0∞) ^ r) := by
      funext x; rw [sub_eq_add_neg]
    rw [h2, h]
  have hinner : ∀ y : E k, (∫⁻ x, (‖F (x - y)‖₊ : ℝ≥0∞) ^ r * Ψ y)
      = (∫⁻ u, (‖F u‖₊ : ℝ≥0∞) ^ r) * Ψ y := by
    intro y
    have hgm : AEMeasurable
        (fun x : E k => (‖F (x - y)‖₊ : ℝ≥0∞) ^ r) (volume : Measure (E k)) :=
      ((((hF.comp (measurable_id.sub measurable_const)).nnnorm).coe_nnreal_ennreal).pow_const r).aemeasurable
    rw [lintegral_mul_const'' (f := fun x : E k => (‖F (x - y)‖₊ : ℝ≥0∞) ^ r) (Ψ y) hgm]
    rw [htrans y]
  rw [show (fun y : E k => ∫⁻ x, (‖F (x - y)‖₊ : ℝ≥0∞) ^ r * Ψ y)
      = fun y : E k => (∫⁻ u, (‖F u‖₊ : ℝ≥0∞) ^ r) * Ψ y from funext hinner]
  have hgm2 : AEMeasurable (fun y : E k => Ψ y) (volume : Measure (E k)) := hΨ.aemeasurable
  rw [lintegral_const_mul'' (f := fun y : E k => Ψ y)
      ((∫⁻ u, (‖F u‖₊ : ℝ≥0∞) ^ r)) hgm2]
  ring


set_option maxHeartbeats 64000000 in
/-- The pointwise weighted Hölder inequality for the convolved power (fix #1: the constant is
pinned and the subtraction runs in the right direction). -/
lemma convPow_holder_pow {k : ℕ} {θ p : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp0 : 0 < p)
    {g : E k → ℂ} (hg : Measurable g) {Ψ : E k → ℝ≥0∞} (hΨ : Measurable Ψ) (x : E k) :
    convPow k (θ * p) g Ψ x ≤ (convPow k p g Ψ x) ^ θ * (∫⁻ y, Ψ y) ^ (1 - θ) := by
  have hθ1' : (0 : ℝ) < 1 - θ := by linarith
  have hc1 : Real.HolderConjugate (1 / θ) (1 / (1 - θ)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by rw [one_lt_div hθ0]; exact hθ1, ?_⟩
    rw [inv_div, inv_div]
    ring
  have hc : Measurable (fun _ : E k => x) := measurable_const
  have h1 : Measurable (fun y : E k => (‖g (x - y)‖₊ : NNReal)) :=
    (hg.comp (hc.sub measurable_id)).nnnorm
  have hfm : AEMeasurable (fun y : E k => ((‖g (x - y)‖₊ : ℝ≥0∞) ^ p * Ψ y) ^ θ)
      (volume : Measure (E k)) :=
    (((h1.coe_nnreal_ennreal.pow_const p).mul hΨ).aemeasurable.pow_const θ)
  have hgm : AEMeasurable (fun y : E k => Ψ y ^ (1 - θ)) (volume : Measure (E k)) :=
    hΨ.aemeasurable.pow_const _
  have hmain := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ := (volume : Measure (E k))) hc1 hfm hgm
  have hθi : (1 : ℝ) / (1 / θ) = θ := by field_simp
  have hθi' : (1 : ℝ) / (1 / (1 - θ)) = 1 - θ := by field_simp
  rw [hθi, hθi'] at hmain
  have hpt : ∀ y : E k, (fun y : E k => ((‖g (x - y)‖₊ : ℝ≥0∞) ^ p * Ψ y) ^ θ) y
        * (fun y : E k => Ψ y ^ (1 - θ)) y
      = (‖g (x - y)‖₊ : ℝ≥0∞) ^ (θ * p) * Ψ y := by
    intro y
    simp only
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0.le, ← ENNReal.rpow_mul]
    rw [show p * θ = θ * p from by ring]
    rw [show (‖g (x - y)‖₊ : ℝ≥0∞) ^ (θ * p) * Ψ y ^ θ * Ψ y ^ (1 - θ)
        = (‖g (x - y)‖₊ : ℝ≥0∞) ^ (θ * p) * (Ψ y ^ θ * Ψ y ^ (1 - θ)) from by ring]
    rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0.le hθ1'.le,
      show θ + (1 - θ) = 1 from by ring, ENNReal.rpow_one]
  have e1 : (∫⁻ a : E k, ((fun y : E k => ((‖g (x - y)‖₊ : ℝ≥0∞) ^ p * Ψ y) ^ θ)
      * (fun y : E k => Ψ y ^ (1 - θ))) a) = convPow k (θ * p) g Ψ x := by
    rw [convPow]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    exact hpt y
  have e2 : (∫⁻ a : E k, (fun y : E k => ((‖g (x - y)‖₊ : ℝ≥0∞) ^ p * Ψ y) ^ θ)
        a ^ (1 / θ)) = convPow k p g Ψ x := by
    rw [convPow]
    refine lintegral_congr fun y => ?_
    simp only
    rw [← ENNReal.rpow_mul, show θ * (1 / θ) = 1 from by field_simp, ENNReal.rpow_one]
  have e3 : (∫⁻ a : E k, (fun y : E k => Ψ y ^ (1 - θ)) a ^ (1 / (1 - θ)))
      = ∫⁻ y, Ψ y := by
    refine lintegral_congr fun y => ?_
    simp only
    rw [← ENNReal.rpow_mul, show (1 - θ) * (1 / (1 - θ)) = 1 from by field_simp,
      ENNReal.rpow_one]
  rw [e1, e2, e3] at hmain
  exact hmain


set_option maxHeartbeats 16000000 in
/-- `lpNorm` of a finite sum is at most the `ℓ²`-sum of the `lpNorm`s. -/
lemma lpNorm_sum_le_L2 {k N : ℕ} (hk : 1 ≤ k) (s : Finset (Fin (2 ^ N)))
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) volume) :
    lpNorm k (pE k) (fun x => ∑ i ∈ s, f i x)
      ≤ (s.card : ℝ≥0∞) ^ ((1:ℝ)/2) * l2Of s (fun i => lpNorm k (pE k) (f i)) := by
  have hpk1 : (1 : ℝ≥0∞) ≤ pE k := by
    rw [pE]
    have h1 : (1 : ℕ) ≤ k * (k + 1) := by nlinarith [hk]
    exact_mod_cast h1
  have h1 : lpNorm k (pE k) (fun x => ∑ i ∈ s, f i x)
      ≤ ∑ i ∈ s, lpNorm k (pE k) (f i) := by
    have := eLpNorm_sum_le (μ := (volume : Measure (E k))) (p := pE k) (s := s) (f := f) hpk1
    simpa only [lpNorm, ← Finset.sum_apply] using this
  have h2 : (∑ i ∈ s, lpNorm k (pE k) (f i)) ^ (2:ℝ)
      ≤ (s.card : ℝ≥0∞) ^ ((2:ℝ) - 1)
        * ∑ i ∈ s, (lpNorm k (pE k) (f i)) ^ (2:ℝ) :=
    Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow s
      (fun i => lpNorm k (pE k) (f i)) (by norm_num)
  have h3 : ((∑ i ∈ s, lpNorm k (pE k) (f i)) ^ (2:ℝ)) ^ ((1:ℝ)/2)
      = ∑ i ∈ s, lpNorm k (pE k) (f i) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have h4 : ((s.card : ℝ≥0∞) ^ ((2:ℝ) - 1)
        * ∑ i ∈ s, (lpNorm k (pE k) (f i)) ^ (2:ℝ)) ^ ((1:ℝ)/2)
      = (s.card : ℝ≥0∞) ^ ((1:ℝ)/2) * l2Of s (fun i => lpNorm k (pE k) (f i)) := by
    have e2 : sqSum s (fun i => lpNorm k (pE k) (f i))
        = ∑ i ∈ s, (lpNorm k (pE k) (f i)) ^ (2:ℝ) := rfl
    rw [← e2, show (2:ℝ) - 1 = 1 from by norm_num, ENNReal.rpow_one,
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), l2Of]
  calc lpNorm k (pE k) (fun x => ∑ i ∈ s, f i x)
      ≤ ∑ i ∈ s, lpNorm k (pE k) (f i) := h1
    _ = ((∑ i ∈ s, lpNorm k (pE k) (f i)) ^ (2:ℝ)) ^ ((1:ℝ)/2) := h3.symm
    _ ≤ ((s.card : ℝ≥0∞) ^ ((2:ℝ) - 1)
            * ∑ i ∈ s, (lpNorm k (pE k) (f i)) ^ (2:ℝ)) ^ ((1:ℝ)/2) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = (s.card : ℝ≥0∞) ^ ((1:ℝ)/2)
          * l2Of s (fun i => lpNorm k (pE k) (f i)) := h4

set_option maxHeartbeats 16000000 in
/-- The same with the block cardinality replaced by `2^N`. -/
lemma lpNorm_sum_pow_le {k N : ℕ} (hk : 1 ≤ k) (s : Finset (Fin (2 ^ N))) {r : ℝ} (hr : 0 ≤ r)
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) volume) :
    (lpNorm k (pE k) (fun x => ∑ i ∈ s, f i x)) ^ r
      ≤ (2 : ℝ≥0∞) ^ ((N : ℝ) * r / 2)
        * (l2Of s (fun i => lpNorm k (pE k) (f i))) ^ r := by
  have hcard : (s.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ N := by
    have h1 : s.card ≤ 2 ^ N := by simpa using Finset.card_le_univ s
    calc (s.card : ℝ≥0∞) ≤ ((2 ^ N : ℕ) : ℝ≥0∞) := by exact_mod_cast h1
      _ = (2 : ℝ≥0∞) ^ N := by push_cast; ring
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc (lpNorm k (pE k) (fun x => ∑ i ∈ s, f i x)) ^ r
      ≤ ((s.card : ℝ≥0∞) ^ ((1:ℝ)/2) * l2Of s (fun i => lpNorm k (pE k) (f i))) ^ r :=
        ENNReal.rpow_le_rpow (lpNorm_sum_le_L2 hk s hf) hr
    _ = (s.card : ℝ≥0∞) ^ (((1:ℝ)/2) * r)
          * (l2Of s (fun i => lpNorm k (pE k) (f i))) ^ r := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr, ← ENNReal.rpow_mul]
    _ ≤ ((2 : ℝ≥0∞) ^ N) ^ (((1:ℝ)/2) * r)
          * (l2Of s (fun i => lpNorm k (pE k) (f i))) ^ r :=
        mul_le_mul_left (ENNReal.rpow_le_rpow hcard (mul_nonneg hhalf hr)) _
    _ = (2 : ℝ≥0∞) ^ ((N : ℝ) * r / 2)
          * (l2Of s (fun i => lpNorm k (pE k) (f i))) ^ r := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        rw [show (N : ℝ) * ((1:ℝ)/2 * r) = (N : ℝ) * r / 2 from by ring]

/-- The `L^{p_k}` norm of a class member, raised to the `p_k`, is the integral of the `p_k`-th
power of its norm. -/
lemma lintegral_nnnorm_rpow_pk (k : ℕ) (hk : 1 ≤ k) (F : E k → ℂ)
    (hF : AEStronglyMeasurable F volume) :
    ∫⁻ x, (‖F x‖₊ : ℝ≥0∞) ^ (pkExp k) = (lpNorm k (pE k) F) ^ (pkExp k) := by
  have h := lintegral_nnnorm_rpow_eq_lpNorm_pow k hk F hF
  rwa [show plExp k = pkExp k from rfl] at h


lemma plExp_zero : plExp 0 = 0 := by rw [plExp]; norm_num

lemma convPow_exp_zero (k : ℕ) (g : E k → ℂ) (Ψ : E k → ℝ≥0∞) (x : E k) :
    convPow k 0 g Ψ x = ∫⁻ y, Ψ y := by
  rw [convPow]
  exact lintegral_congr fun y => by rw [ENNReal.rpow_zero, one_mul]

lemma plExp_lt_pkExp {k l : ℕ} (h : l < k) : plExp l < pkExp k := by
  rw [plExp, pkExp]
  have hl : (l:ℝ) < k := by exact_mod_cast h
  have hl0 : (0:ℝ) ≤ l := by positivity
  have hk0 : (0:ℝ) < k := lt_of_le_of_lt hl0 hl
  nlinarith


-- `half_mem_asymExpSet` (nonemptiness of the exponent set, via the crude bound `asymDec_crude`):
-- since `AsymExpSet` now consists of the SINGLE canonical pair `(⌊asymRatio k l·b·N⌋, ⌊b·N⌋)`,
-- the level side conditions `2 ≤ m₁, m₂, m₁ ≤ N, m₂ ≤ N` are discharged from `N ≥ N₀` alone
-- (taking `N₀` so large that `2 ≤ b·N` and `2 ≤ asymRatio k l·b·N`).


set_option maxHeartbeats 32000000 in
/-- **The crude (trivial) bound for the asymmetric bilinear inequality.**  Tonelli, Hölder and
Cauchy–Schwarz give the asymmetric bilinear decoupling inequality with a constant that is a fixed
number times `2^{N p_k / 2}`. -/
theorem asymDec_crude {k : ℕ} (hk : 1 ≤ k) {l : ℕ} (hl : l ≤ k - 1)
    {N m m' : ℕ} (hm : 2 ≤ m) (hm' : 2 ≤ m') (hmN : m ≤ N) (hm'N : m' ≤ N)
    (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')) (f : Fin (2 ^ N) → E k → ℂ)
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) :
    (∫⁻ x, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N m q, f i x)
          (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x
        * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
          (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)
      ≤ (uncConst k hk) ^ 2 * ((2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2)
          * (2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2))
          * (l2Of (blkFin N m q) fun i => lpNorm k (pE k) (f i)) ^ (plExp l)
          * (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k - plExp l) := by
  classical
  have hδm : 0 < plateHalf m := by rw [plateHalf]; positivity
  have hδm' : 0 < plateHalf m' := by rw [plateHalf]; positivity
  set FI : E k → ℂ := fun x => ∑ i ∈ blkFin N m q, f i x with hFI
  set FJ : E k → ℂ := fun x => ∑ i ∈ blkFin N m' q', f i x with hFJ
  set ΦI : E k → ℝ≥0∞ := platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q) with hΦI
  set ΦJ : E k → ℝ≥0∞ := platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q') with hΦJ
  have hFIm : Measurable FI := Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable)
  have hFJm : Measurable FJ := Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable)
  have hΦIm : Measurable ΦI := (continuous_platePhi k hk _ _).measurable
  have hΦJm : Measurable ΦJ := (continuous_platePhi k hk _ _).measurable
  have hKI : ∫⁻ y, ΦI y = uncConst k hk := by
    rw [hΦI]
    exact lintegral_platePhi hk (plateHalf m) (pieceCenter (2 ^ m) q) hδm.ne'
  have hKJ : ∫⁻ y, ΦJ y = uncConst k hk := by
    rw [hΦJ]
    exact lintegral_platePhi hk (plateHalf m') (pieceCenter (2 ^ m') q') hδm'.ne'
  -- the two `L^{p_k}` integrals
  have hIp : ∫⁻ x, convPow k (pkExp k) FI ΦI x
      = uncConst k hk * (lpNorm k (pE k) FI) ^ (pkExp k) := by
    rw [lintegral_convPow_eq k (pkExp k) hFIm hΦIm, hKI, lintegral_nnnorm_rpow_pk k hk FI hFIm.aestronglyMeasurable]
  have hJp : ∫⁻ x, convPow k (pkExp k) FJ ΦJ x
      = uncConst k hk * (lpNorm k (pE k) FJ) ^ (pkExp k) := by
    rw [lintegral_convPow_eq k (pkExp k) hFJm hΦJm, hKJ, lintegral_nnnorm_rpow_pk k hk FJ hFJm.aestronglyMeasurable]
  -- the `ℓ²` bounds for the two block sums
  have hbndI : (lpNorm k (pE k) FI) ^ (plExp l)
      ≤ (2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2)
        * (l2Of (blkFin N m q) (fun i => lpNorm k (pE k) (f i))) ^ (plExp l) := by
    rw [hFI]
    exact lpNorm_sum_pow_le hk (blkFin N m q) (plExp_nonneg l)
      (fun i _ => ((hf i).continuous.measurable).aestronglyMeasurable)
  have hbndJ : (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l)
      ≤ (2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2)
        * (l2Of (blkFin N m' q') (fun i => lpNorm k (pE k) (f i))) ^ (pkExp k - plExp l) := by
    rw [hFJ]
    exact lpNorm_sum_pow_le hk (blkFin N m' q') (pkExp_sub_plExp_nonneg (by omega))
      (fun i _ => ((hf i).continuous.measurable).aestronglyMeasurable)
  rcases Nat.eq_zero_or_pos l with hl0 | hlpos
  · -- the case `l = 0`
    have hpz : plExp l = 0 := by rw [hl0]; exact plExp_zero
    have hsub : pkExp k - plExp l = pkExp k := by rw [hpz, sub_zero]
    have hA : ∀ x : E k, convPow k (plExp l) FI ΦI x = ∫⁻ y, ΦI y := by
      intro x; rw [hpz]; exact convPow_exp_zero k FI ΦI x
    have hfun : (fun x : E k => convPow k (plExp l) FI ΦI x
          * convPow k (pkExp k - plExp l) FJ ΦJ x)
        = fun x : E k => (∫⁻ y, ΦI y) * convPow k (pkExp k) FJ ΦJ x := by
      funext x; rw [hA x, hsub]
    have hstep : (∫⁻ x, convPow k (plExp l) FI ΦI x
          * convPow k (pkExp k - plExp l) FJ ΦJ x)
        = (uncConst k hk) ^ 2 * (lpNorm k (pE k) FJ) ^ (pkExp k) := by
      rw [hfun, lintegral_const_mul'' _ (measurable_convPow k _ hFJm hΦJm).aemeasurable,
        hKI, hJp]
      ring
    rw [hstep]
    have hbndJ' : (lpNorm k (pE k) FJ) ^ (pkExp k)
        ≤ (2 : ℝ≥0∞) ^ ((N : ℝ) * pkExp k / 2)
          * (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k) := by
      simpa only [hpz, sub_zero] using hbndJ
    rw [show (uncConst k hk) ^ 2 * ((2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2)
            * (2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2))
            * (l2Of (blkFin N m q) fun i => lpNorm k (pE k) (f i)) ^ (plExp l)
            * (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k - plExp l)
        = (uncConst k hk) ^ 2 * ((2 : ℝ≥0∞) ^ ((N : ℝ) * pkExp k / 2)
            * (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k)) from by
      have hA0 : (2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2) = 1 := by
        rw [hpz, show (N : ℝ) * 0 / 2 = (0 : ℝ) from by ring, ENNReal.rpow_zero]
      have hB0 : (2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2)
          = (2 : ℝ≥0∞) ^ ((N : ℝ) * pkExp k / 2) := by
        rw [hpz, show pkExp k - 0 = pkExp k from sub_zero _]
      have hX0 : (l2Of (blkFin N m q) fun i => lpNorm k (pE k) (f i)) ^ (plExp l) = 1 := by
        rw [hpz, ENNReal.rpow_zero]
      have hY0 : (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k - plExp l)
          = (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k) := by
        rw [hpz, show pkExp k - 0 = pkExp k from sub_zero _]
      rw [hA0, hB0, hX0, hY0, one_mul, mul_one, mul_assoc]]
    exact mul_le_mul' le_rfl hbndJ'
  · -- the case `l ≥ 1`
    set θ : ℝ := plExp l / pkExp k with hθdef
    have hp0 : 0 < pkExp k := pkExp_pos hk
    have hθ0 : 0 < θ := by rw [hθdef]; exact div_pos (plExp_pos hlpos) hp0
    have hθ1 : θ < 1 := by
      rw [hθdef, div_lt_one hp0]
      exact plExp_lt_pkExp (by omega)
    have hθeq : θ * pkExp k = plExp l := by rw [hθdef]; field_simp
    have hθeq' : (1 - θ) * pkExp k = pkExp k - plExp l := by
      rw [hθdef]; field_simp
    have hptA : ∀ x : E k, convPow k (plExp l) FI ΦI x
        ≤ (convPow k (pkExp k) FI ΦI x) ^ θ * (∫⁻ y, ΦI y) ^ (1 - θ) := by
      intro x
      have h := convPow_holder_pow (k := k) (θ := θ) (p := pkExp k) hθ0 hθ1 hp0 hFIm hΦIm x
      rwa [hθeq] at h
    have hptB : ∀ x : E k, convPow k (pkExp k - plExp l) FJ ΦJ x
        ≤ (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ := by
      intro x
      have h := convPow_holder_pow (k := k) (θ := 1 - θ) (p := pkExp k)
        (by linarith) (by linarith) hp0 hFJm hΦJm x
      rw [hθeq', show 1 - (1 - θ) = θ from by ring] at h
      exact h
    have hpt : ∀ x : E k, convPow k (plExp l) FI ΦI x * convPow k (pkExp k - plExp l) FJ ΦJ x
        ≤ (∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ
          * ((convPow k (pkExp k) FI ΦI x) ^ θ
              * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)) := by
      intro x
      refine (mul_le_mul' (hptA x) (hptB x)).trans (le_of_eq ?_)
      ring
    have hAc : AEMeasurable (fun x : E k => convPow k (pkExp k) FI ΦI x) volume :=
      (measurable_convPow k _ hFIm hΦIm).aemeasurable
    have hBc : AEMeasurable (fun x : E k => convPow k (pkExp k) FJ ΦJ x) volume :=
      (measurable_convPow k _ hFJm hΦJm).aemeasurable
    have hInt := lintegral_rpow_interp (μ := (volume : Measure (E k))) hθ0 hθ1 hAc hBc
      (measurable_const.aemeasurable : AEMeasurable (fun _ : E k => (1 : ℝ≥0∞)) volume)
    simp only [mul_one] at hInt
    have hmeasc : AEMeasurable (fun x : E k => (convPow k (pkExp k) FI ΦI x) ^ θ
        * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)) volume :=
      (hAc.pow_const θ).mul (hBc.pow_const (1 - θ))
    have hpull : (∫⁻ x, (∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ
          * ((convPow k (pkExp k) FI ΦI x) ^ θ
              * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)))
        = ((∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ)
          * ∫⁻ x, (convPow k (pkExp k) FI ΦI x) ^ θ
              * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ) := by
      rw [lintegral_const_mul'' (f := fun x : E k =>
        (convPow k (pkExp k) FI ΦI x) ^ θ * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ))
        (((∫⁻ y, ΦI y) ^ (1 - θ)) * ((∫⁻ y, ΦJ y) ^ θ)) hmeasc]
    have hmain : ((∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ)
          * ((∫⁻ x, convPow k (pkExp k) FI ΦI x) ^ θ
              * (∫⁻ x, convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ))
        = (uncConst k hk) ^ 2 * (lpNorm k (pE k) FI) ^ (plExp l)
            * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l) := by
      rw [hKI, hKJ, hIp, hJp]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0.le,
        ENNReal.mul_rpow_of_nonneg _ _ (by linarith : (0:ℝ) ≤ 1 - θ)]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      rw [show pkExp k * θ = plExp l from by rw [hθdef]; field_simp,
        show pkExp k * (1 - θ) = pkExp k - plExp l from by rw [hθdef]; field_simp]
      have hK1 : uncConst k hk ^ (1 - θ) * uncConst k hk ^ θ = uncConst k hk := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith : (0:ℝ) ≤ 1 - θ) hθ0.le]
        rw [show (1 - θ) + θ = 1 from by ring, ENNReal.rpow_one]
      have hK2 : uncConst k hk ^ θ * uncConst k hk ^ (1 - θ) = uncConst k hk := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0.le (by linarith : (0:ℝ) ≤ 1 - θ)]
        rw [show θ + (1 - θ) = 1 from by ring, ENNReal.rpow_one]
      rw [hK1,
        show uncConst k hk * (uncConst k hk ^ θ * (lpNorm k (pE k) FI) ^ (plExp l)
              * (uncConst k hk ^ (1 - θ) * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l)))
            = (uncConst k hk ^ θ * uncConst k hk ^ (1 - θ))
              * (uncConst k hk * ((lpNorm k (pE k) FI) ^ (plExp l)
                * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l))) from by ac_rfl,
        hK2, pow_two]
      ac_rfl
    calc (∫⁻ x, convPow k (plExp l) FI ΦI x * convPow k (pkExp k - plExp l) FJ ΦJ x)
        ≤ ∫⁻ x, (∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ
            * ((convPow k (pkExp k) FI ΦI x) ^ θ
                * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)) := lintegral_mono hpt
      _ = ((∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ)
            * ∫⁻ x, (convPow k (pkExp k) FI ΦI x) ^ θ
                * (convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ) := hpull
      _ ≤ ((∫⁻ y, ΦI y) ^ (1 - θ) * (∫⁻ y, ΦJ y) ^ θ)
            * ((∫⁻ x, convPow k (pkExp k) FI ΦI x) ^ θ
                * (∫⁻ x, convPow k (pkExp k) FJ ΦJ x) ^ (1 - θ)) :=
          mul_le_mul' le_rfl hInt
      _ = (uncConst k hk) ^ 2 * (lpNorm k (pE k) FI) ^ (plExp l)
            * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l) := hmain
      _ ≤ (uncConst k hk) ^ 2 * ((2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2)
            * (2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2))
            * (l2Of (blkFin N m q) fun i => lpNorm k (pE k) (f i)) ^ (plExp l)
            * (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i)) ^ (pkExp k - plExp l) := by
          have h2 := mul_le_mul' hbndI hbndJ
          calc (uncConst k hk) ^ 2 * (lpNorm k (pE k) FI) ^ (plExp l)
                * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l)
              = (uncConst k hk) ^ 2 * ((lpNorm k (pE k) FI) ^ (plExp l)
                  * (lpNorm k (pE k) FJ) ^ (pkExp k - plExp l)) := by rw [mul_assoc]
            _ ≤ (uncConst k hk) ^ 2 * (((2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2)
                  * (l2Of (blkFin N m q) fun i => lpNorm k (pE k) (f i)) ^ (plExp l))
                * ((2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2)
                  * (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i))
                    ^ (pkExp k - plExp l))) := mul_le_mul' le_rfl h2
            _ = (uncConst k hk) ^ 2 * ((2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2)
                  * (2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2))
                  * (l2Of (blkFin N m q) fun i => lpNorm k (pE k) (f i)) ^ (plExp l)
                  * (l2Of (blkFin N m' q') fun i => lpNorm k (pE k) (f i))
                    ^ (pkExp k - plExp l) := by ac_rfl



/-! ## 2. Nonemptiness of the exponent set -/

set_option maxHeartbeats 16000000 in
/-- **Nonemptiness of the exponent set.**  The exponent `1/2` works, with a constant independent of
the data and of the level: this is `asymDec_crude` together with the arithmetic
`(ofReal (K·2^{N/2}))^{p_k} = ofReal (K^{p_k})·2^{N p_k/2}`. -/
theorem half_mem_asymExpSet (k : ℕ) (hk : 1 ≤ k) {l : ℕ} (hl : l ≤ k - 1) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hb2 : asymRatio k l * b ≤ 1) :
    ((1 : ℝ) / 2) ∈ AsymExpSet k hk l b := by
  classical
  have hK2ne : ((uncConst k hk) ^ 2) ≠ ⊤ := by
    rw [pow_two]
    exact ENNReal.mul_ne_top (uncConst_ne_top k hk) (uncConst_ne_top k hk)
  have hbpos : (0 : ℝ) ≤ ((uncConst k hk) ^ 2).toReal := ENNReal.toReal_nonneg
  have hzpos : (0 : ℝ) ≤ 1 / pkExp k := div_nonneg zero_le_one (le_of_lt (pkExp_pos hk))
  have hrp : (0 : ℝ) ≤ (((uncConst k hk) ^ 2).toReal) ^ (1 / pkExp k) :=
    Real.rpow_nonneg hbpos (1 / pkExp k)
  have hb1' : (0 : ℝ) ≤ (((uncConst k hk) ^ 2).toReal) ^ (1 / pkExp k) + 1 := by linarith
  -- the two sides of the constant comparison
  have hfinal : (uncConst k hk) ^ 2
      ≤ ENNReal.ofReal (((((uncConst k hk) ^ 2).toReal) ^ (1 / pkExp k) + 1) ^ (pkExp k)) := by
    have h1 : (uncConst k hk) ^ 2
        = (ENNReal.ofReal ((((uncConst k hk) ^ 2).toReal) ^ (1 / pkExp k))) ^ (pkExp k) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hbpos hzpos, ENNReal.ofReal_toReal hK2ne,
        ← ENNReal.rpow_mul,
        show (1 / pkExp k) * pkExp k = 1 from by rw [div_mul_cancel₀ _ (pkExp_pos hk).ne'],
        ENNReal.rpow_one]
    conv_lhs => rw [h1]
    rw [← ENNReal.ofReal_rpow_of_nonneg
      (x := ((((uncConst k hk) ^ 2).toReal) ^ (1 / pkExp k) + 1)) hb1' (pkExp_nonneg k)]
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)) (pkExp_nonneg k)
  refine ⟨by norm_num, (((uncConst k hk) ^ 2).toReal) ^ (1 / pkExp k) + 1, by linarith,
    max (⌈2 / b⌉₊ + 1) (⌈2 / (asymRatio k l * b)⌉₊ + 1), fun N hN q q' hsep f hf => ?_⟩
  have hCeq : (ENNReal.ofReal (((((uncConst k hk) ^ 2).toReal) ^ (1 / pkExp k) + 1)
        * (2 : ℝ) ^ ((N : ℝ) * ((1 : ℝ) / 2)))) ^ (pkExp k)
      = ENNReal.ofReal (((((uncConst k hk) ^ 2).toReal) ^ (1 / pkExp k) + 1) ^ (pkExp k))
        * (2 : ℝ≥0∞) ^ ((N : ℝ) * pkExp k / 2) := by
    rw [ENNReal.ofReal_mul hb1', ENNReal.mul_rpow_of_nonneg _ _ (pkExp_nonneg k),
      ENNReal.ofReal_rpow_of_nonneg hb1' (pkExp_nonneg k),
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (mul_nonneg (Nat.cast_nonneg N) (by norm_num : (0:ℝ) ≤ (1:ℝ)/2))]
    have h2 : (ENNReal.ofReal (2 : ℝ)) = (2 : ℝ≥0∞) := by norm_num
    rw [h2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    ring_nf
  have h2 : (2 : ℝ≥0∞) ^ ((N : ℝ) * plExp l / 2)
        * (2 : ℝ≥0∞) ^ ((N : ℝ) * (pkExp k - plExp l) / 2)
      = (2 : ℝ≥0∞) ^ ((N : ℝ) * pkExp k / 2) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _
      (div_nonneg (mul_nonneg (Nat.cast_nonneg N) (plExp_nonneg l)) (by norm_num))
      (div_nonneg (mul_nonneg (Nat.cast_nonneg N) (pkExp_sub_plExp_nonneg (by omega))) (by norm_num))]
    ring_nf
  have hb0' : 0 < asymRatio k l := asymRatio_pos' hk hl
  have hb2' : asymRatio k l * b * (N : ℝ) ≤ (N : ℝ) := by
    calc asymRatio k l * b * (N : ℝ) ≤ 1 * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hb2 (Nat.cast_nonneg N)
      _ = (N : ℝ) := one_mul _
  have hb1'' : b * (N : ℝ) ≤ (N : ℝ) := by
    calc b * (N : ℝ) ≤ 1 * (N : ℝ) := mul_le_mul_of_nonneg_right hb1 (Nat.cast_nonneg N)
      _ = (N : ℝ) := one_mul _
  have hm₂ : 2 ≤ lvlOf b N := by
    refine two_le_lvlOf ?_
    have h1 : 2 / b ≤ (⌈2 / b⌉₊ : ℝ) := Nat.le_ceil _
    have h2' : ((⌈2 / b⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : (⌈2 / b⌉₊ : ℕ) ≤ N := by omega
      exact_mod_cast this
    calc (2 : ℝ) = (2 / b) * b := by rw [div_mul_cancel₀ _ hb0.ne']
      _ ≤ (⌈2 / b⌉₊ : ℝ) * b := mul_le_mul_of_nonneg_right h1 hb0.le
      _ ≤ (N : ℝ) * b := mul_le_mul_of_nonneg_right h2' hb0.le
      _ = b * (N : ℝ) := by ring
  have hm₁ : 2 ≤ lvlOf (asymRatio k l * b) N := by
    refine two_le_lvlOf ?_
    have h1 : 2 / (asymRatio k l * b) ≤ (⌈2 / (asymRatio k l * b)⌉₊ : ℝ) := Nat.le_ceil _
    have h2' : ((⌈2 / (asymRatio k l * b)⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      have : (⌈2 / (asymRatio k l * b)⌉₊ : ℕ) ≤ N := by omega
      exact_mod_cast this
    calc (2 : ℝ) = (2 / (asymRatio k l * b)) * (asymRatio k l * b) := by
          rw [div_mul_cancel₀ _ (mul_ne_zero hb0'.ne' hb0.ne')]
      _ ≤ (⌈2 / (asymRatio k l * b)⌉₊ : ℝ) * (asymRatio k l * b) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt (mul_pos hb0' hb0))
      _ ≤ (N : ℝ) * (asymRatio k l * b) :=
          mul_le_mul_of_nonneg_right h2' (le_of_lt (mul_pos hb0' hb0))
      _ = asymRatio k l * b * (N : ℝ) := by ring
  have hm₁N : lvlOf (asymRatio k l * b) N ≤ N := lvlOf_le_of_mul_le hb2'
  have hm₂N : lvlOf b N ≤ N := lvlOf_le_of_mul_le hb1''
  refine (asymDec_crude hk hl hm₁ hm₂ hm₁N hm₂N q q' f hf).trans ?_
  rw [hCeq, h2]
  exact mul_le_mul' (mul_le_mul' (mul_le_mul' hfinal le_rfl) le_rfl) le_rfl

lemma asymExpSet_nonempty (k : ℕ) (hk : 1 ≤ k) {l : ℕ} (hl : l ≤ k - 1) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b ≤ 1) (hb2 : asymRatio k l * b ≤ 1) :
    (AsymExpSet k hk l b).Nonempty :=
  ⟨1 / 2, half_mem_asymExpSet k hk hl hb0 hb1 hb2⟩

end Submission.Vinogradov
