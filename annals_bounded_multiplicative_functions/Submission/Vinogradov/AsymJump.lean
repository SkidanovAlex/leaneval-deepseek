/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.UniformChain
import Submission.Vinogradov.AsymRefine
import Submission.Vinogradov.TentCompare
import Submission.Vinogradov.UncertaintyBlock
import Submission.Vinogradov.AsymFine
import Submission.Commons.Analysis.Inequalities.sum_rpow_le_rpow_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# GLYZ §4: the level coarsening of the asymmetric bilinear inequality

This module proves the **first-slot coarsening** of the asymmetric bilinear decoupling
inequality: if the level-`M'` blocks are `2^d`-fold refinements of the level-`M` blocks and
`M' - M ≤ D`, then

  `AsymDec k hk l N M' m' C  →  AsymDec k hk l N M m' (C · K₀^{1/p_k})`

with a constant `K₀` depending only on `(k, l, D)`.

This is the formal counterpart of GLYZ Lemma 3.9 *in the direction actually consumed by the
§4 recursion*: the recursion expresses `A_l(b)` through the canonical levels
`A_{k-l}(a_l(b))` and `A_{l-1}(b)`, whose first slots are `O(k)` levels *finer* than the
slots the recursion needs.  Merging the `2^d` refined blocks back into one block costs only
the bounded factor `(2^d)^{p_l - 1}` (triangle inequality plus convexity of `x ↦ x^{p_l}`),
and the weight comparison `Φ_M ∗ Φ_{M'} ≤ C·Φ_{M'}` (GLYZ Lemma A.1) keeps the second
factor unchanged.

The module is imported by `ROADMAP.lean` only; it is not on the comparator chain.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

lemma plExp_one_le {l : ℕ} (hl : 1 ≤ l) : 1 ≤ plExp l := by
  rw [plExp]; exact_mod_cast (by nlinarith : 1 ≤ l * (l + 1))

lemma plExp_two_le {l : ℕ} (hl : 1 ≤ l) : 2 ≤ plExp l := by
  rw [plExp]; exact_mod_cast (by nlinarith : 2 ≤ l * (l + 1))

lemma plateHalf_anti {m M : ℕ} (h : m ≤ M) : plateHalf M ≤ plateHalf m := by
  rw [plateHalf, plateHalf, one_div, one_div, inv_le_inv₀ (by positivity) (by positivity)]
  exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : m + 1 ≤ M + 1)

/-! ### Step 1: the convolution coarsening of a block sum -/

lemma convPow_blkSum_coarsen {k N M M' D : ℕ} (l : ℕ) (q : Fin (2 ^ M))
    (hMM' : M ≤ M') (hMN : M' ≤ N) (hMD : M' ≤ M + D)
    (hpl1 : 1 ≤ plExp l)
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, Measurable (f i))
    (Ψ : E k → ℝ≥0∞) (hΨ : Measurable Ψ) (x : E k) :
    convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M q, f i x) Ψ x
      ≤ (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
        * ∑ q'' ∈ subBlkLvl M M' q,
            convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x) Ψ x := by
  have hpl0 : 0 ≤ plExp l := le_trans zero_le_one hpl1
  have hr0 : 0 ≤ plExp l - 1 := by linarith
  set S : Finset (Fin (2 ^ M')) := subBlkLvl M M' q with hS
  have hAcard : (S.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ D := by
    rw [hS]
    have h := card_subBlkLvl_le M M' hMM' q
    have hsub : M' - M ≤ D := by omega
    have h2 : ((subBlkLvl M M' q).card : ℝ≥0∞) ≤ ((2 ^ D : ℕ) : ℝ≥0∞) := by
      exact_mod_cast h.trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hsub)
    rwa [Nat.cast_pow] at h2
  have hK1card : (S.card : ℝ≥0∞) ^ (plExp l - 1)
      ≤ (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1)) := by
    calc (S.card : ℝ≥0∞) ^ (plExp l - 1)
        ≤ ((2 : ℝ≥0∞) ^ D) ^ (plExp l - 1) := ENNReal.rpow_le_rpow hAcard hr0
      _ = (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1)) := by
          rw [← ENNReal.rpow_natCast (2 : ℝ≥0∞) D, ← ENNReal.rpow_mul]
  have hpt : ∀ y : E k, ((‖∑ i ∈ blkFin N M q, f i y‖₊ : ℝ≥0∞)) ^ (plExp l)
      ≤ (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
        * ∑ q'' ∈ S, ((‖∑ i ∈ blkFin N M' q'', f i y‖₊ : ℝ≥0∞)) ^ (plExp l) := by
    intro y
    have hid : (∑ i ∈ blkFin N M q, f i y)
        = ∑ q'' ∈ S, ∑ i ∈ blkFin N M' q'', f i y := by
      rw [hS]
      exact sum_subBlkLvl hMM' hMN q (fun i : Fin (2 ^ N) => f i y)
    rw [hid]
    have h1 : (‖∑ q'' ∈ S, ∑ i ∈ blkFin N M' q'', f i y‖₊ : ℝ≥0∞)
        ≤ ∑ q'' ∈ S, (‖∑ i ∈ blkFin N M' q'', f i y‖₊ : ℝ≥0∞) := by
      exact_mod_cast nnnorm_sum_le S (fun q'' => ∑ i ∈ blkFin N M' q'', f i y)
    have h2 := Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow S
      (fun q'' => (‖∑ i ∈ blkFin N M' q'', f i y‖₊ : ℝ≥0∞)) hpl1
    exact (ENNReal.rpow_le_rpow h1 hpl0).trans (h2.trans (mul_le_mul' hK1card le_rfl))
  have hsummeas : ∀ q'' ∈ S, Measurable (fun y : E k =>
      ((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l) * Ψ y) := by
    intro q'' _
    have h1 : Measurable (fun y : E k => ∑ i ∈ blkFin N M' q'', f i (x - y)) :=
      Finset.measurable_sum _ (fun i _ =>
        (hf i).comp (measurable_const.sub measurable_id))
    exact (h1.nnnorm.coe_nnreal_ennreal).pow_const (plExp l) |>.mul hΨ
  calc convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M q, f i x) Ψ x
      = ∫⁻ y, ((‖∑ i ∈ blkFin N M q, f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l) * Ψ y := rfl
    _ ≤ ∫⁻ y, ((2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
          * ∑ q'' ∈ S, ((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l)) * Ψ y :=
        lintegral_mono (fun y => mul_le_mul' (hpt (x - y)) le_rfl)
    _ = (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
          * ∫⁻ y, (∑ q'' ∈ S, ((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l)) * Ψ y := by
        rw [show (fun y : E k => ((2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
              * ∑ q'' ∈ S, ((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l)) * Ψ y)
            = fun y : E k => (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
              * ((∑ q'' ∈ S, ((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l)) * Ψ y)
          from by funext y; ring]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num))]
    _ = (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
          * ∑ q'' ∈ S, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x) Ψ x := by
        congr 1
        have hsplit : (∫⁻ y, (∑ q'' ∈ S, ((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l)) * Ψ y)
            = ∑ q'' ∈ S, ∫⁻ y, ((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l) * Ψ y := by
          rw [show (fun y : E k => (∑ q'' ∈ S, ((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l)) * Ψ y)
              = fun y : E k => ∑ q'' ∈ S, (((‖∑ i ∈ blkFin N M' q'', f i (x - y)‖₊ : ℝ≥0∞)) ^ (plExp l) * Ψ y)
            from by funext y; rw [Finset.sum_mul]]
          exact lintegral_finsetSum S hsummeas
        rw [hsplit]
        exact Finset.sum_congr rfl (fun q'' _ => rfl)

end Submission.Vinogradov

namespace Submission.Vinogradov

/-! ### Step 2: replacing the coarse weight by the fine one -/

lemma convPow_blkSum_weight_le {k N M M' : ℕ} (hk : 1 ≤ k) {l : ℕ} (hl : 1 ≤ l) {CA : ℝ}
    (hCA : ∀ (δ_I δ_J c_I c_J : ℝ) (x : E k),
      0 < δ_J → δ_J ≤ δ_I → δ_I ≤ 1 → c_I ∈ Set.Icc (0 : ℝ) 1 →
      c_J ∈ Set.Icc (0 : ℝ) 1 → |c_J - c_I| ≤ δ_I →
      (∫⁻ y : E k, platePhi k hk δ_I c_I (x - y) * platePhi k hk δ_J c_J y)
        ≤ ENNReal.ofReal CA * platePhi k hk δ_J c_J x)
    (hMM' : M ≤ M') (hMN : M' ≤ N) (hmD2 : 2 ≤ M') (q : Fin (2 ^ M)) (q'' : Fin (2 ^ M'))
    (hq'' : q'' ∈ subBlkLvl M M' q)
    {f : Fin (2 ^ N) → E k → ℂ} (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    (x : E k) :
    convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
        (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q)) x
      ≤ ((uncConst k hk) ^ (plExp l - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
        * ENNReal.ofReal (max CA 1)
        * convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
          (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x := by
  have hpl1 : 1 ≤ plExp l := plExp_one_le hl
  have hMD : M ≤ M' := hMM'
  have hclass : IsFourierRep k (plate k (8 * plateHalf M') (pieceCenter (2 ^ M') q''))
      (fun x => ∑ i ∈ blkFin N M' q'', f i x) :=
    isFourierRep_sum_blkFin hk hmD2 hMN q'' f hf
  have hunc : ∀ v : E k, ((‖∑ i ∈ blkFin N M' q'', f i v‖₊ : ℝ≥0∞)) ^ (plExp l)
      ≤ (uncConst k hk) ^ (plExp l - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
        * convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
          (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) v :=
    fun v => norm_rpow_le_convPow_of_isFourierRep hk (plateHalf_pos M') hclass hpl1 v
  have hca : ∀ z : E k, (∫⁻ y : E k, platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q) (z - y)
        * platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'') y)
      ≤ ENNReal.ofReal (max CA 1)
        * platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'') z := by
    intro z
    have h1 := hCA (plateHalf M) (plateHalf M') (pieceCenter (2 ^ M) q)
      (pieceCenter (2 ^ M') q'') z (plateHalf_pos M')
      (plateHalf_anti hMD) (plateHalf_le_one M)
      (pieceCenter_mem_Icc (2 ^ M) (Nat.one_le_two_pow) q)
      (pieceCenter_mem_Icc (2 ^ M') (Nat.one_le_two_pow) q'')
      (by
        have h2 := abs_pieceCenter_subBlkLvl_sub_le (m := M) (m'' := M') hMD hq''
        linarith [plateHalf_pos M'])
    exact h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
  have hmeas : ∀ q'' : Fin (2 ^ M'),
      Measurable (fun x : E k => ∑ i ∈ blkFin N M' q'', f i x) :=
    fun q'' => Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable)
  have hH : Measurable (fun v : E k => ((‖∑ i ∈ blkFin N M' q'', f i v‖₊ : ℝ≥0∞)) ^ (plExp l)) :=
    ((hmeas q'').nnnorm.coe_nnreal_ennreal).pow_const (plExp l)
  have hKutop : (uncConst k hk) ^ (plExp l - 1)
      * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (uncConst_ne_top k hk))
      ENNReal.ofReal_ne_top
  have step1 : convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
        (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q)) x
      ≤ ((uncConst k hk) ^ (plExp l - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
        * (∫⁻ u : E k, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) (x - u)
          * platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q) u) := by
    rw [convPow]
    refine (lintegral_mono fun y => mul_le_mul' (hunc (x - y)) le_rfl).trans (le_of_eq ?_)
    rw [show (fun y : E k => (((uncConst k hk) ^ (plExp l - 1)
            * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) (x - y))
          * platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q) y)
        = fun y : E k => ((uncConst k hk) ^ (plExp l - 1)
            * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * (convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) (x - y)
            * platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q) y) from by funext y; ring]
    rw [lintegral_const_mul' _ _ hKutop]
  have step2 : (∫⁻ u : E k, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
        (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) (x - u)
        * platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q) u)
      ≤ ENNReal.ofReal (max CA 1)
        * ∫⁻ w : E k, ((‖∑ i ∈ blkFin N M' q'', f i (x - w)‖₊ : ℝ≥0∞)) ^ (plExp l)
          * platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'') w := by
    have := lintegral_convPow_le_of_conv_le
      (Φ₁ := platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q))
      (Φ₂ := platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q''))
      (continuous_platePhi k hk _ _).measurable (continuous_platePhi k hk _ _).measurable hca hH x
    simpa only [convPow] using this
  calc convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
        (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q)) x
      ≤ ((uncConst k hk) ^ (plExp l - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
        * (ENNReal.ofReal (max CA 1)
          * ∫⁻ w : E k, ((‖∑ i ∈ blkFin N M' q'', f i (x - w)‖₊ : ℝ≥0∞)) ^ (plExp l)
            * platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'') w) :=
        step1.trans (mul_le_mul' le_rfl step2)
    _ = ((uncConst k hk) ^ (plExp l - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
        * ENNReal.ofReal (max CA 1)
        * convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
          (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x := by
        rw [convPow]; ring

end Submission.Vinogradov

namespace Submission.Vinogradov

theorem asymDec_coarsen {k : ℕ} (hk : 1 ≤ k) {l : ℕ} (hl : 1 ≤ l) (D : ℕ) :
    ∃ K0 : ℝ≥0∞, K0 ≠ 0 ∧ K0 ≠ ⊤ ∧
      ∀ {N M M' m' : ℕ}, 2 ≤ M → M ≤ M' → M' ≤ M + D → M' ≤ N → ∀ {C : ℝ≥0∞},
        AsymDec k hk l N M' m' C → AsymDec k hk l N M m' (C * K0 ^ (1 / pkExp k)) := by
  obtain ⟨CA, _, hCA⟩ := platePhi_conv_le k hk
  set K1 : ℝ≥0∞ := (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1)) with hK1
  set Ku : ℝ≥0∞ := (uncConst k hk) ^ (plExp l - 1)
      * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)) with hKu
  set Kc : ℝ≥0∞ := ENNReal.ofReal (max CA 1) with hKc
  set KK : ℝ≥0∞ := K1 * Ku * Kc with hKK
  have hKKtop : KK ≠ ⊤ := by
    rw [hKK, hK1, hKu, hKc]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg
        (mul_nonneg (Nat.cast_nonneg D) (by linarith [plExp_one_le hl])) (by norm_num)
    · exact ENNReal.mul_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by linarith [plExp_one_le hl]) (uncConst_ne_top k hk))
        ENNReal.ofReal_ne_top
  have hK0ne : (max 1 KK) ≠ 0 := by
    intro h
    have h1 : (1 : ℝ≥0∞) ≤ max 1 KK := le_max_left _ _
    rw [h] at h1; exact absurd h1 (by norm_num)
  have hK0top : (max 1 KK) ≠ ⊤ := by
    rcases lt_or_ge (1 : ℝ≥0∞) KK with h | h
    · rw [max_eq_right h.le]; exact hKKtop
    · rw [max_eq_left h]; exact ENNReal.one_ne_top
  refine ⟨max 1 KK, hK0ne, hK0top, ?_⟩
  intro N M M' m' h2M hMM' hMD' hMN C hdec
  have hpl1 : 1 ≤ plExp l := plExp_one_le hl
  have hpl2 : 2 ≤ plExp l := plExp_two_le hl
  have hpl0 : 0 ≤ plExp l := le_trans zero_le_one hpl1
  have hmD2 : 2 ≤ M' := by omega
  have hMD : M ≤ M' := hMM'
  have hpkne : pkExp k ≠ 0 := ne_of_gt (pkExp_pos hk)
  rw [AsymDec] at hdec ⊢
  intro q q' hsep f hf
  set S : Finset (Fin (2 ^ M')) := subBlkLvl M M' q with hS
  set A : Fin (2 ^ N) → ℝ≥0∞ := fun i => lpNorm k (pE k) (f i) with hA
  set X : ℝ≥0∞ := (l2Of (blkFin N M q) A) ^ (plExp l) with hX
  set Y : ℝ≥0∞ := (l2Of (blkFin N m' q') A) ^ (pkExp k - plExp l) with hY
  have hKh : KK = (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
      * ((uncConst k hk) ^ (plExp l - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
      * ENNReal.ofReal (max CA 1) := by rw [hKK, hK1, hKu, hKc]
  -- pointwise coarsening of the first factor
  have hpt : ∀ x : E k,
      convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M q, f i x)
        (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q)) x
        ≤ KK * ∑ q'' ∈ S, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x := by
    intro x
    have h1 := convPow_blkSum_coarsen l q hMM' hMN hMD' hpl1
      (fun i => (hf i).continuous.measurable)
      (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q))
      (continuous_platePhi k hk _ _).measurable x
    have h2 : ∀ q'' ∈ S, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
        (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q)) x
        ≤ ((uncConst k hk) ^ (plExp l - 1) * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
          * ENNReal.ofReal (max CA 1)
          * convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x := by
      intro q'' hq''
      rw [hS] at hq''
      exact convPow_blkSum_weight_le hk hl hCA hMM' hMN hmD2 q q'' hq'' hf x
    calc convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M q, f i x)
          (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q)) x
        ≤ (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
            * ∑ q'' ∈ S, convPow k (plExp l)
                (fun x => ∑ i ∈ blkFin N M' q'', f i x)
                (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q)) x := h1
      _ ≤ (2 : ℝ≥0∞) ^ ((D : ℝ) * (plExp l - 1))
            * ∑ q'' ∈ S, (((uncConst k hk) ^ (plExp l - 1)
                * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2)))
              * ENNReal.ofReal (max CA 1)
              * convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
                (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x) :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun q'' hq'' => h2 q'' hq'')
      _ = KK * ∑ q'' ∈ S, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x := by
          rw [hKh, ← Finset.mul_sum]
          ring
  -- the per-q'' refinement
  have hdec' : ∀ (q'' : Fin (2 ^ M')), q'' ∈ S →
      (∫⁻ x, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x
          * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
            (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x
        ≤ C ^ (pkExp k) * (l2Of (blkFin N M' q'') A) ^ (plExp l) * Y) := by
    intro q'' hq''
    rw [hS] at hq''
    have hsep' := sepLevel_of_subBlkLvl hMD hq'' hsep
    have h := hdec q'' q' hsep' f hf
    rw [hA, hY]
    exact h
  have hsummeas : ∀ q'' ∈ S, Measurable (fun x : E k =>
      convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M' q'', f i x)
        (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x
      * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
        (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x) := by
    intro q'' _
    exact (measurable_convPow k (plExp l)
        (Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable))
        (continuous_platePhi k hk _ _).measurable).mul
      (measurable_convPow k (pkExp k - plExp l)
        (Finset.measurable_sum _ (fun i _ => (hf i).continuous.measurable))
        (continuous_platePhi k hk _ _).measurable)
  have hK0pow : (C * (max 1 KK) ^ (1 / pkExp k)) ^ (pkExp k) = C ^ (pkExp k) * (max 1 KK) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (pkExp_nonneg k), ← ENNReal.rpow_mul,
      show (1 / pkExp k) * pkExp k = 1 by field_simp, ENNReal.rpow_one]
  have htel : ∑ q'' ∈ S, (l2Of (blkFin N M' q'') A) ^ (plExp l) ≤ X := by
    have hsum_sq : ∑ q'' ∈ S, sqSum (blkFin N M' q'') A = sqSum (blkFin N M q) A := by
      rw [hS]
      exact (sum_subBlkLvl hMD hMN q (fun i => A i ^ (2 : ℝ))).symm
    have h1 : ∀ q'' : Fin (2 ^ M'),
        (l2Of (blkFin N M' q'') A) ^ (plExp l)
        = (sqSum (blkFin N M' q'') A) ^ (plExp l / 2) := by
      intro q''
      rw [l2Of, ← ENNReal.rpow_mul, show (1 : ℝ) / 2 * plExp l = plExp l / 2 by ring]
    have h2 : ∑ q'' ∈ S, (sqSum (blkFin N M' q'') A) ^ (plExp l / 2)
        ≤ (∑ q'' ∈ S, sqSum (blkFin N M' q'') A) ^ (plExp l / 2) :=
      Commons.Analysis.Inequalities.sum_rpow_le_rpow_sum S (fun q'' => sqSum (blkFin N M' q'') A)
        (by linarith : 1 ≤ plExp l / 2)
    have h3 : (sqSum (blkFin N M q) A) ^ (plExp l / 2) = X := by
      rw [hX, l2Of, ← ENNReal.rpow_mul, show (1 : ℝ) / 2 * plExp l = plExp l / 2 by ring]
    calc ∑ q'' ∈ S, (l2Of (blkFin N M' q'') A) ^ (plExp l)
        = ∑ q'' ∈ S, (sqSum (blkFin N M' q'') A) ^ (plExp l / 2) :=
          Finset.sum_congr rfl fun q'' _ => h1 q''
      _ ≤ (∑ q'' ∈ S, sqSum (blkFin N M' q'') A) ^ (plExp l / 2) := h2
      _ = (sqSum (blkFin N M q) A) ^ (plExp l / 2) := by rw [hsum_sq]
      _ = X := h3
  have hmain3 : ∑ q'' ∈ S, (C ^ (pkExp k) * (l2Of (blkFin N M' q'') A) ^ (plExp l) * Y)
      = C ^ (pkExp k) * (∑ q'' ∈ S, (l2Of (blkFin N M' q'') A) ^ (plExp l)) * Y := by
    have h1 : ∀ q'' : Fin (2 ^ M'),
        C ^ (pkExp k) * (l2Of (blkFin N M' q'') A) ^ (plExp l) * Y
        = C ^ (pkExp k) * ((l2Of (blkFin N M' q'') A) ^ (plExp l) * Y) := by
      intro q''; ring
    rw [Finset.sum_congr rfl (fun q'' _ => h1 q''), ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hmain4 : ∑ q'' ∈ S, (C ^ (pkExp k) * (l2Of (blkFin N M' q'') A) ^ (plExp l) * Y)
      ≤ C ^ (pkExp k) * (X * Y) := by
    rw [hmain3, mul_assoc]
    exact mul_le_mul' le_rfl (mul_le_mul' htel le_rfl)
  calc (∫⁻ x, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N M q, f i x)
        (platePhi k hk (plateHalf M) (pieceCenter (2 ^ M) q)) x
      * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
        (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)
      ≤ ∫⁻ x, (KK * ∑ q'' ∈ S, convPow k (plExp l)
            (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x)
        * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
          (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x :=
        lintegral_mono fun x => mul_le_mul' (hpt x) le_rfl
    _ = KK * ∑ q'' ∈ S, (∫⁻ x, convPow k (plExp l)
            (fun x => ∑ i ∈ blkFin N M' q'', f i x)
            (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x
          * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
            (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x) := by
        rw [show (fun x : E k => (KK * ∑ q'' ∈ S, convPow k (plExp l)
              (fun x => ∑ i ∈ blkFin N M' q'', f i x)
              (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x)
            * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
              (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)
          = fun x : E k => KK * ((∑ q'' ∈ S, convPow k (plExp l)
              (fun x => ∑ i ∈ blkFin N M' q'', f i x)
              (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x)
            * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
              (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x) from by
          funext x; ring]
        rw [lintegral_const_mul' _ _ hKKtop]
        congr 1
        rw [show (fun x : E k => (∑ q'' ∈ S, convPow k (plExp l)
              (fun x => ∑ i ∈ blkFin N M' q'', f i x)
              (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x)
            * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
              (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)
          = fun x : E k => ∑ q'' ∈ S, (convPow k (plExp l)
              (fun x => ∑ i ∈ blkFin N M' q'', f i x)
              (platePhi k hk (plateHalf M') (pieceCenter (2 ^ M') q'')) x
            * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
              (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x) from by
          funext x; simp only [Finset.sum_mul]]
        exact lintegral_finsetSum S hsummeas
    _ ≤ KK * ∑ q'' ∈ S, (C ^ (pkExp k) * (l2Of (blkFin N M' q'') A) ^ (plExp l) * Y) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun q'' hq'' => hdec' q'' hq'')
    _ ≤ KK * (C ^ (pkExp k) * (X * Y)) := mul_le_mul' le_rfl hmain4
    _ = C ^ (pkExp k) * (KK * (X * Y)) := by ring
    _ ≤ C ^ (pkExp k) * ((max 1 KK) * (X * Y)) :=
        mul_le_mul' le_rfl (mul_le_mul' (le_max_right _ _) le_rfl)
    _ = ((C * (max 1 KK) ^ (1 / pkExp k)) ^ (pkExp k)) * (X * Y) := by
        rw [← mul_assoc, ← hK0pow]
    _ = ((C * (max 1 KK) ^ (1 / pkExp k)) ^ (pkExp k) * X) * Y := by rw [← mul_assoc]

end Submission.Vinogradov
