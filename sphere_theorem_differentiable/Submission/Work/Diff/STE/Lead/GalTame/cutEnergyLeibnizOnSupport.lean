import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.commutator_pd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.Lead.GalTame

set_option maxHeartbeats 2000000

/-! ## Elementary list and norm bookkeeping -/

/-- Lowering a smoothness level from `∞` to a finite one. -/
private lemma cut_contDiff_level_le (m : ℕ) :
    ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr (le_top : ((m : ℕ) : ℕ∞) ≤ ⊤)

/-- `pdVec` of a globally smooth function is continuous, at any order. -/
private lemma cut_continuous_pdVec_of_smooth {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) (l : Fin m → Fin n) :
    Continuous (Work.Diff.STE.pdVec m l f) :=
  Work.Diff.STE.continuous_pdVec m l f (hf.of_le (cut_contDiff_level_le m))

/-- A list sum of terms bounded by `c` is at most `length * c`. -/
private lemma cut_list_sum_le_card_mul {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a ∈ L, f a ≤ c) : (L.map f).sum ≤ (L.length : ℝ) * c := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : f a ≤ c := h a (by simp)
      have ht : ∀ b ∈ t, f b ≤ c := fun b hb => h b (by simp [hb])
      have hrec := ih ht
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith

/-- A list sum of pointwise bounded terms is bounded termwise. -/
private lemma cut_list_sum_le_sum {α : Type*} (L : List α) {f g : α → ℝ}
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : f a ≤ g a := h a (by simp)
      have ht : ∀ b ∈ t, f b ≤ g b := fun b hb => h b (by simp [hb])
      have hrec := ih ht
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- Factoring a constant out of a list sum. -/
private lemma cut_list_sum_map_mul_left {α : Type*} (L : List α) (c : ℝ) (f : α → ℝ) :
    (L.map (fun a => c * f a)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- The norm of a complexified real is its absolute value. -/
private lemma cut_norm_ofReal_eq_abs (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  exact Real.sqrt_mul_self_eq_abs x

/-- `pdRList` of a list is `pdRVec` of the corresponding tuple. -/
private lemma cut_pdRList_eq_pdRVec {n : ℕ} (q : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdRList q f
      = Work.Diff.STE.pdRVec q.length (fun i : Fin q.length => q.get i) f := by
  rw [Work.Diff.STE.pdRVec]
  congr 1
  exact (List.ofFn_get q).symm

/-- The `pdList` of the complexified cut-off is bounded by `Kφ`. -/
private lemma cut_pdList_ofReal_norm_le {n m : ℕ} {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : ∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
      |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ)
    {q : List (Fin n)} (hq : q.length ≤ m) (z : Fin n → ℝ) :
    ‖Work.Diff.STE.pdList q (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z‖ ≤ Kφ := by
  rw [Work.Diff.STE.cm_pdList_ofReal_smooth q φ hφ]
  show ‖((Work.Diff.STE.pdRList q φ z : ℝ) : ℂ)‖ ≤ Kφ
  rw [cut_norm_ofReal_eq_abs, cut_pdRList_eq_pdRVec q φ]
  exact hφb q.length hq (fun i => q.get i) z

/-- Continuity of the squared norm of an iterated partial derivative. -/
private lemma cut_continuous_normSq_pdVec {n : ℕ} {W : (Fin n → ℝ) → ℂ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (j : ℕ) (γ : Fin j → Fin n) :
    Continuous (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2) := by
  have h := (cut_continuous_pdVec_of_smooth hW j γ).norm
  convert h.mul h using 1
  ext z
  simp only [Pi.mul_apply, pow_two]

/-- A continuous function is integrable on a ball. -/
private lemma cut_integrableOn_ball {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (R : ℝ) : IntegrableOn f (Metric.ball (0 : Fin n → ℝ) R) volume := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-|R|) |R|)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine (ContinuousOn.integrableOn_compact hK hf.continuousOn).mono_set ?_
  intro z hz
  simp only [Metric.mem_ball, dist_zero_right, Set.mem_pi, Set.mem_univ, true_implies] at hz ⊢
  intro i
  exact abs_le.mp (le_trans (norm_le_pi_norm z i) (le_trans (le_of_lt hz) (le_abs_self R)))

/-! ## The pointwise Leibniz bound -/

/-- **Pointwise Cauchy–Schwarz Leibniz bound.**  For a smooth cut-off `φ` whose jets of order
`≤ m` are bounded by `Kφ` and a smooth `F`, the `m`-th jet of `φ · F` at a point `z` is bounded
by `(2^{m+1} Kφ)` times the square root of the sum of the squared norms of all the jets of `F` of
order `≤ m` at `z`; the statement below is its square. -/
private lemma cutEnergy_pointwise {n m : ℕ} {φ : (Fin n → ℝ) → ℝ} {F : (Fin n → ℝ) → ℂ}
    {Kφ : ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hφb : ∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
      |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ)
    (β : Fin m → Fin n) (z : Fin n → ℝ) :
    ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z) z‖ ^ 2
      ≤ (4 : ℝ) ^ (m + 1) * Kφ ^ 2 *
        ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ‖Work.Diff.STE.pdVec j γ F z‖ ^ 2 := by
  classical
  set G : (Fin n → ℝ) → ℂ := fun y => ((φ y : ℝ) : ℂ) with hG
  set l : List (Fin n) := List.ofFn β with hl
  have hl_len : l.length = m := by rw [hl]; exact List.length_ofFn
  set B : ℝ := ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
      ‖Work.Diff.STE.pdVec j γ F z‖ ^ 2 with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun γ _ => sq_nonneg _
  -- jet bounds
  have hφnorm : ∀ q : List (Fin n), q.length ≤ m → ‖Work.Diff.STE.pdList q G z‖ ≤ Kφ := by
    intro q hq
    rw [hG]
    exact cut_pdList_ofReal_norm_le hφ hφb hq z
  have hFnorm : ∀ q : List (Fin n), q.length ≤ m →
      ‖Work.Diff.STE.pdList q F z‖ ≤ Real.sqrt B := by
    intro q hq
    refine Real.le_sqrt_of_sq_le ?_
    have hpd' : Work.Diff.STE.pdList q F
        = Work.Diff.STE.pdVec q.length (fun i : Fin q.length => q.get i) F := by
      rw [Work.Diff.STE.pdVec]
      congr 1
      exact (List.ofFn_get q).symm
    rw [hpd']
    refine (Finset.single_le_sum
      (f := fun γ : Fin q.length → Fin n => ‖Work.Diff.STE.pdVec q.length γ F z‖ ^ 2)
      (fun γ _ => sq_nonneg _) (Finset.mem_univ (fun i => q.get i))).trans ?_
    rw [hB]
    exact Finset.single_le_sum
      (f := fun j => ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ F z‖ ^ 2)
      (fun j _ => Finset.sum_nonneg fun γ _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
  -- differentiability hypotheses of the Leibniz rule
  have hGdiff : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q G) := by
    intro q _ _
    rw [hG]
    exact Work.Diff.STE.cm_diff_pdList_ofReal φ hφ q
  have hFdiff : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F) := by
    intro q _ _
    refine (Work.Diff.STE.cm_contDiff_pdList q 1 F ?_).differentiable (by norm_num)
    exact hF.of_le (cut_contDiff_level_le (q.length + 1))
  set S : List (List (Fin n) × List (Fin n)) :=
    (Work.Diff.STE.splits l).filter (fun p => p.1 ≠ []) with hS
  -- the iterated Leibniz rule in difference form
  have hexp : Work.Diff.STE.pdList l (fun w => G w * F w) z
      = G z * Work.Diff.STE.pdList l F z
        + (S.map (fun p => Work.Diff.STE.pdList p.1 G z
            * Work.Diff.STE.pdList p.2 F z)).sum := by
    have h := congrFun (Work.Diff.STE.pdList_mul_sub l G F hGdiff hFdiff) z
    rw [sub_eq_iff_eq_add] at h
    rw [hS, add_comm]
    exact h
  -- each split contributes at most `Kφ * ‖∂^{p.2}F‖`
  have hterm : ∀ p ∈ S, ‖Work.Diff.STE.pdList p.1 G z * Work.Diff.STE.pdList p.2 F z‖
      ≤ Kφ * ‖Work.Diff.STE.pdList p.2 F z‖ := by
    intro p hp
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hps : p ∈ Work.Diff.STE.splits l := by
      rw [hS] at hp
      exact (List.mem_filter.mp hp).1
    have hlen := Work.Diff.STE.cm_splits_mem_length l p hps
    have hlen1 : p.1.length ≤ m := by rw [hl_len] at hlen; omega
    exact hφnorm p.1 hlen1
  -- the list of the norms of all the Leibniz terms (including the top order term of `F`)
  set T : List ℝ := ‖Work.Diff.STE.pdList l F z‖
      :: (S.map (fun p => ‖Work.Diff.STE.pdList p.2 F z‖)) with hT
  have hTnorm : ∀ a ∈ T, a ≤ Real.sqrt B := by
    intro a ha
    rw [hT] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hFnorm l (by rw [hl_len])
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      have hps : p ∈ Work.Diff.STE.splits l := by
        rw [hS] at hp
        exact (List.mem_filter.mp hp).1
      have hlen := Work.Diff.STE.cm_splits_mem_length l p hps
      have hlen2 : p.2.length ≤ m := by rw [hl_len] at hlen; omega
      exact hFnorm p.2 hlen2
  have hTsum : T.sum ≤ (T.length : ℝ) * Real.sqrt B := by
    simpa using cut_list_sum_le_card_mul T (fun a : ℝ => a) (Real.sqrt B) hTnorm
  have hTnn : 0 ≤ T.sum := by
    rw [hT, List.sum_cons]
    refine add_nonneg (norm_nonneg _) ?_
    exact List.sum_nonneg fun a ha => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      exact norm_nonneg _
  have hTlen : T.length = S.length + 1 := by rw [hT]; simp
  have hSlen : S.length ≤ 2 ^ m := by
    rw [hS]
    calc (List.filter (fun p : List (Fin n) × List (Fin n) => p.1 ≠ [])
            (Work.Diff.STE.splits l)).length
        ≤ (Work.Diff.STE.splits l).length := List.length_filter_le _ _
      _ = 2 ^ l.length := Work.Diff.STE.cm_splits_length_count l
      _ = 2 ^ m := by rw [hl_len]
  have hTcard : (T.length : ℝ) ≤ (2 : ℝ) ^ (m + 1) := by
    rw [hTlen]
    have h1 : (S.length : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast hSlen
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    push_cast
    calc (S.length : ℝ) + 1 ≤ (2 : ℝ) ^ m + 1 := by linarith
      _ ≤ (2 : ℝ) ^ m + (2 : ℝ) ^ m := by linarith
      _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  -- the norm bound
  have hmain : ‖Work.Diff.STE.pdList l (fun w => G w * F w) z‖ ≤ Kφ * T.sum := by
    have hphiz : |φ z| ≤ Kφ := by
      simpa [Work.Diff.STE.pdRVec, Work.Diff.STE.pdRList] using
        hφb 0 (Nat.zero_le m) (fun i : Fin 0 => i.elim0) z
    have h1 : ‖G z * Work.Diff.STE.pdList l F z
        + (S.map (fun p => Work.Diff.STE.pdList p.1 G z
            * Work.Diff.STE.pdList p.2 F z)).sum‖
        ≤ Kφ * ‖Work.Diff.STE.pdList l F z‖
          + Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 F z‖)).sum := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hGz : ‖G z‖ = |φ z| := by rw [hG]; exact cut_norm_ofReal_eq_abs (φ z)
        rw [hGz]
        exact hphiz
      · refine (Work.Diff.STE.cm_list_sum_norm_le S _).trans ?_
        refine (cut_list_sum_le_sum S (fun p hp => hterm p hp)).trans ?_
        exact le_of_eq (cut_list_sum_map_mul_left S Kφ
          (fun p => ‖Work.Diff.STE.pdList p.2 F z‖))
    rw [hexp]
    calc ‖G z * Work.Diff.STE.pdList l F z
          + (S.map (fun p => Work.Diff.STE.pdList p.1 G z
              * Work.Diff.STE.pdList p.2 F z)).sum‖
        ≤ Kφ * ‖Work.Diff.STE.pdList l F z‖
          + Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 F z‖)).sum := h1
      _ = Kφ * T.sum := by rw [hT, List.sum_cons]; ring
  -- square and insert the cardinality bound
  have hpd : Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z)
      = Work.Diff.STE.pdList l (fun w => G w * F w) := by
    rw [hl]
    rfl
  have h4 : ((2 : ℝ) ^ (m + 1)) ^ 2 = (4 : ℝ) ^ (m + 1) := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [hpd]
  calc ‖Work.Diff.STE.pdList l (fun w => G w * F w) z‖ ^ 2
      ≤ (Kφ * T.sum) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmain 2
    _ = Kφ ^ 2 * T.sum ^ 2 := by ring
    _ ≤ Kφ ^ 2 * ((T.length : ℝ) * Real.sqrt B) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Kφ)
        exact pow_le_pow_left₀ hTnn hTsum 2
    _ = Kφ ^ 2 * (T.length : ℝ) ^ 2 * B := by
        rw [mul_pow, Real.sq_sqrt hBnn]
        ring
    _ ≤ Kφ ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 * B := by
        refine mul_le_mul_of_nonneg_right ?_ hBnn
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg Kφ)
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hTcard 2
    _ = (4 : ℝ) ^ (m + 1) * Kφ ^ 2 * B := by
        rw [h4]
        ring

/-- **The `L²` Leibniz estimate for a product with a cut-off, integrated over a ball — support
condition on the product.**

For a smooth cutoff `φ` whose iterated partial derivatives of order `≤ m` are pointwise bounded by
`Kφ`, and a smooth `F : (Fin n → ℝ) → ℂ` whose product with `φ` is supported in the open ball of
radius `R ≤ 1/2`,

`∫_{ball 0 R} ‖∂^m_β (φ · F)‖² ≤ C · Kφ² · Σ_{j ≤ m} Σ_{γ : Fin j → Fin n} ∫_{ball 0 R} ‖∂^j_γ F‖²`.

This is the *same* estimate as `Work.Diff.STE.Lead.GalTame.cutEnergyLeibniz`
(`Submission/Work/Diff/STE/Lead/GalTame/cutEnergyLeibniz.lean`, where the full proof is already
written and the support hypothesis is *unused* in it), with the hypothesis
`Function.support F ⊆ Metric.ball 0 R` replaced by the weaker
`Function.support (fun z => (φ z : ℂ) * F z) ⊆ Metric.ball 0 R`.  The weaker hypothesis is what the
consumer needs: it must apply the estimate to `F = Ht - lam' · 1`, which is *not* compactly
supported (it equals `(1 - lam') · 1` off the support of the cut-off), while the *product* is
supported.  The proof is a verbatim transcription of the existing one: the iterated Leibniz rule
`Work.Diff.STE.pdList_mul_sub` gives the pointwise bound
`‖pdVec m β (φ · F) z‖² ≤ 4^{m+1} Kφ² · Σ_{j ≤ m} Σ_γ ‖pdVec j γ F z‖²` for *every* `z` (this is
`cutEnergy_pointwise` in `cutEnergyLeibniz.lean`), which is then integrated over `ball 0 R` with
`setIntegral_mono_on`; neither the support condition nor `R ≤ 1/2` is used (the condition only
records that the left-hand side is the whole-space integral of a compactly supported function).
The file `Submission/Work/Diff/STE/B3/mulJet_le_clean.lean` contains the complete `unitCube`
version as well.  Do **not** use `Work.Diff.STE.B3.mulJet_le` (it depends on `sorryAx`). -/
theorem cutEnergyLeibnizOnSupport {n : ℕ} (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : (Fin n → ℝ) → ℝ) (F : (Fin n → ℝ) → ℂ) (Kφ R : ℝ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ →
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) F →
      (∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
        |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ) →
      (Function.support (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z) ⊆ Metric.ball 0 R) →
      R ≤ 1 / 2 →
      ∀ β : Fin m → Fin n,
        ∫ z in Metric.ball 0 R,
            ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z) z‖ ^ 2
          ≤ C * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Metric.ball 0 R, ‖Work.Diff.STE.pdVec j γ F z‖ ^ 2 := by
  classical
  refine ⟨(4 : ℝ) ^ (m + 1), by positivity, ?_⟩
  intro φ F Kφ R hφ hF hφb _hsupp _hR β
  set B : (Fin n → ℝ) → ℝ := fun z => ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
      ‖Work.Diff.STE.pdVec j γ F z‖ ^ 2 with hB
  -- the pointwise bound
  have hpt : ∀ z : Fin n → ℝ,
      ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z) z‖ ^ 2
        ≤ (4 : ℝ) ^ (m + 1) * Kφ ^ 2 * B z := by
    intro z
    rw [hB]
    exact cutEnergy_pointwise hφ hF hφb β z
  -- continuity of the integrands
  have hcontL : Continuous (fun z : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z) z‖ ^ 2) := by
    have hsm : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z) :=
      (Complex.ofRealCLM.contDiff.comp hφ).mul hF
    have h := (cut_continuous_pdVec_of_smooth hsm m β).norm
    convert h.mul h using 1
    ext z
    simp only [Pi.mul_apply, pow_two]
  have hcontB : Continuous B := by
    rw [hB]
    refine continuous_finset_sum (Finset.range (m + 1)) (fun j _ => ?_)
    exact continuous_finset_sum (Finset.univ : Finset (Fin j → Fin n))
      (fun γ _ => cut_continuous_normSq_pdVec hF j γ)
  have hint1 : IntegrableOn (fun z : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z) z‖ ^ 2)
      (Metric.ball 0 R) volume := cut_integrableOn_ball hcontL R
  have hint2 : IntegrableOn (fun z : Fin n → ℝ => (4 : ℝ) ^ (m + 1) * Kφ ^ 2 * B z)
      (Metric.ball 0 R) volume := cut_integrableOn_ball (hcontB.const_mul _) R
  have hmono : ∫ z in Metric.ball 0 R,
        ‖Work.Diff.STE.pdVec m β (fun z : Fin n → ℝ => ((φ z : ℝ) : ℂ) * F z) z‖ ^ 2
      ≤ ∫ z in Metric.ball 0 R, (4 : ℝ) ^ (m + 1) * Kφ ^ 2 * B z :=
    setIntegral_mono_on hint1 hint2 Metric.isOpen_ball.measurableSet (fun z _ => hpt z)
  have hconst : ∫ z in Metric.ball 0 R, (4 : ℝ) ^ (m + 1) * Kφ ^ 2 * B z
      = (4 : ℝ) ^ (m + 1) * Kφ ^ 2 * ∫ z in Metric.ball 0 R, B z := by
    rw [MeasureTheory.integral_const_mul]
  have hFubini : ∫ z in Metric.ball 0 R, B z
      = ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z in Metric.ball 0 R, ‖Work.Diff.STE.pdVec j γ F z‖ ^ 2 := by
    rw [hB]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finset_sum]
      intro γ _
      exact cut_integrableOn_ball (cut_continuous_normSq_pdVec hF j γ) R
    · intro j _
      exact integrable_finset_sum _ fun γ _ =>
        cut_integrableOn_ball (cut_continuous_normSq_pdVec hF j γ) R
  rw [hconst, hFubini] at hmono
  exact hmono

end Work.Diff.STE.Lead.GalTame
