import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.chart_uniform_tails
import Submission.Work.EQ.gpd_aux

/-! # The middle of a punctured chart converges off the `O₁`-cone -/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- Each `invBranch` of `Q` is one of the two partners `paramΛ a Q (±S)`. -/
lemma eq_paramΛ_or_eq_neg {a : ℝ} {Q P : ℂ × ℂ} {S : ℂ} (hS : S ^ 2 = rhoPrimeSq a Q)
    (hQ : rhoPrimeSq a Q ≠ 0)
    (hP : P = invBranch a true Q ∨ P = invBranch a false Q) :
    P = paramΛ a Q S ∨ P = paramΛ a Q (-S) := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg (a := S) (b := (rhoPrimeSq a Q) ^ (1 / 2 : ℂ))).mp
    (by rw [hS, sqhalf]) with h | h
  · rw [h, paramΛ_sqrt_eq_true a Q hQ, paramΛ_sqrt_eq_false a Q hQ]
    exact hP
  · rw [h, neg_neg, paramΛ_sqrt_eq_true a Q hQ, paramΛ_sqrt_eq_false a Q hQ]
    exact hP.symm

/-- **The middle of a punctured chart converges off the `O₁`-cone.** -/
theorem gpd_middle_limits {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ v₀ : ℂ} {N : ℕ}
    {ρ ρg : ℝ} (hρ : 0 < ρ) (hρg : 0 < ρg)
    (hcont : ContinuousOn e (Metric.ball (0 : ℂ) ρ \ {0}))
    (hH0 : ∀ ζ ∈ Metric.ball (0 : ℂ) ρ \ {0}, e ζ ∈ H0 a h)
    (hψ1 : Tendsto (fun ζ => (e ζ).2.1) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds u₀))
    (hv : Tendsto (fun ζ => (e ζ).2.2) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds v₀))
    (htail : ∀ ζ ∈ Metric.ball (0 : ℂ) ρ \ {0}, ∀ n : ℕ, N ≤ n →
      (e ζ).1 (n : ℤ) = germC a h (eqLamC a ^ n * (e ζ).2.1) ∧
      (e ζ).1 (-(n : ℤ)) = ugermC a h (eqLamC a ^ n * (e ζ).2.2))
    (hgermAn : AnalyticOnNhd ℂ (germC a h) (Metric.ball (0 : ℂ) ρg))
    (hgermC : ∀ u ∈ Metric.ball (0 : ℂ) ρg,
      bsq (subO1 a (germC a h u)) ≠ 0 ∧ bsq (subO2 a (germC a h u)) ≠ 0 ∧
        EqRelC a (germC a h u) (germC a h (eqLamC a * u)))
    (hu0g : ‖eqLamC a ^ N * u₀‖ < ρg) (hv0g : ‖eqLamC a ^ N * v₀‖ < ρg)
    (hdeg : ∀ σ : List Bool, σ.length ≤ 2 * N →
      bsq (subO1 a (bwdP a σ (germC a h (eqLamC a ^ N * u₀)))) ≠ 0) :
    ∃ q : ℤ → ℂ × ℂ,
      q (N : ℤ) = germC a h (eqLamC a ^ N * u₀) ∧
      q (-(N : ℤ)) = ugermC a h (eqLamC a ^ N * v₀) ∧
      (∀ j : ℤ, (N : ℤ) < j → q j = germC a h (eqLamC a ^ j * u₀)) ∧
      (∀ j : ℤ, j < -(N : ℤ) → q j = ugermC a h (eqLamC a ^ (-j) * v₀)) ∧
      (∀ j : ℤ, Tendsto (fun ζ => (e ζ).1 j) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (q j))) ∧
      (∀ j : ℤ, -((N : ℤ)) ≤ j → j ≤ (N : ℤ) → bsq (subO1 a (q j)) ≠ 0) ∧
      (∀ j : ℤ, -((N : ℤ)) ≤ j → j < (N : ℤ) → EqRelC a (q j) (q (j + 1))) := by
  classical
  have hlam0 : 0 < eqLam a := lam_pos ha0 ha1
  have hlamlt : eqLam a < 1 := lam_lt_one ha0 ha1
  have hnormC : ‖eqLamC a‖ = eqLam a := lamC_norm ha0 ha1
  have hdom : Metric.ball (0 : ℂ) ρ \ {0} ∈ nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ :=
    Filter.inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hρ)) self_mem_nhdsWithin
  have hnormpow : ∀ (n : ℕ) (z : ℂ), ‖eqLamC a ^ n * z‖ = eqLam a ^ n * ‖z‖ := by
    intro n z
    rw [norm_mul, norm_pow, hnormC]
  have hsmall : ∀ (n : ℕ) (w : ℂ), N ≤ n → ‖eqLamC a ^ N * w‖ < ρg →
      ‖eqLamC a ^ n * w‖ < ρg := by
    intro n w hn hw
    have hle : eqLam a ^ n ≤ eqLam a ^ N := pow_le_pow_of_le_one hlam0.le hlamlt.le hn
    have h1 : eqLam a ^ n * ‖w‖ ≤ eqLam a ^ N * ‖w‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg w)
    have h2 : eqLam a ^ N * ‖w‖ < ρg := by simpa only [hnormpow] using hw
    calc ‖eqLamC a ^ n * w‖ = eqLam a ^ n * ‖w‖ := hnormpow n w
      _ ≤ eqLam a ^ N * ‖w‖ := h1
      _ < ρg := h2
  -- ## the tail limits
  have hlimUp : ∀ n : ℕ, N ≤ n →
      Tendsto (fun ζ => (e ζ).1 (n : ℤ)) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
        (nhds (germC a h (eqLamC a ^ n * u₀))) := by
    intro n hn
    have hmem : eqLamC a ^ n * u₀ ∈ Metric.ball (0 : ℂ) ρg := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hsmall n u₀ hn hu0g
    have h1 : Tendsto (fun ζ => germC a h (eqLamC a ^ n * (e ζ).2.1))
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (germC a h (eqLamC a ^ n * u₀))) :=
      ((hgermAn _ hmem).continuousAt).tendsto.comp (Tendsto.const_mul _ hψ1)
    refine h1.congr' ?_
    exact Filter.eventually_iff.mpr
      (Filter.mem_of_superset hdom (fun ζ hζ => (htail ζ hζ n hn).1.symm))
  have hlimDn : ∀ n : ℕ, N ≤ n →
      Tendsto (fun ζ => (e ζ).1 (-(n : ℤ))) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
        (nhds (ugermC a h (eqLamC a ^ n * v₀))) := by
    intro n hn
    have hmem : eqLamC a ^ n * v₀ ∈ Metric.ball (0 : ℂ) ρg := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hsmall n v₀ hn hv0g
    have h1 : Tendsto (fun ζ => ugermC a h (eqLamC a ^ n * (e ζ).2.2))
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (ugermC a h (eqLamC a ^ n * v₀))) := by
      have hg : ContinuousAt (fun v : ℂ => germC a h (eqLamC a ^ n * v)) v₀ :=
        ((hgermAn _ hmem).continuousAt).comp (continuousAt_const.mul continuousAt_id)
      have hm : ContinuousAt eqMirror (germC a h (eqLamC a ^ n * v₀)) := by
        rw [show eqMirror = fun z : ℂ × ℂ => (-z.1, z.2) from rfl]
        exact ContinuousAt.prodMk continuousAt_fst.neg continuousAt_snd
      exact ((hm.comp (f := fun v : ℂ => germC a h (eqLamC a ^ n * v)) hg).tendsto.comp hv)
    refine h1.congr' ?_
    exact Filter.eventually_iff.mpr
      (Filter.mem_of_superset hdom (fun ζ hζ => (htail ζ hζ n hn).2.symm))
  -- ## the downward induction
  have key : ∀ m : ℕ, m ≤ 2 * N → ∃ (Q : ℕ → ℂ × ℂ) (σ : List Bool), σ.length = m ∧
      Q 0 = germC a h (eqLamC a ^ N * u₀) ∧
      (∀ i ≤ m, Tendsto (fun ζ => (e ζ).1 ((N : ℤ) - (i : ℤ))) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
        (nhds (Q i))) ∧
      (∀ i ≤ m, Q i = bwdP a (σ.take i) (germC a h (eqLamC a ^ N * u₀))) ∧
      (∀ i ≤ m, bsq (subO1 a (Q i)) ≠ 0) ∧
      (∀ i < m, EqRelC a (Q (i + 1)) (Q i)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => germC a h (eqLamC a ^ N * u₀), [], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro i hi
        have hi0 : i = 0 := Nat.le_zero.mp hi
        subst hi0
        simpa using hlimUp N le_rfl
      · intro i hi
        have hi0 : i = 0 := Nat.le_zero.mp hi
        subst hi0
        simp [bwdP]
      · intro i hi
        have hi0 : i = 0 := Nat.le_zero.mp hi
        subst hi0
        exact hdeg [] (by simp)
      · intro i hi
        omega
    | succ m ih =>
      intro hm
      obtain ⟨Q, σ, hσlen, hQ0, hconv, hid, hbsq, hEq⟩ := ih (by omega)
      have hconvQ : Tendsto (fun ζ => (e ζ).1 ((N : ℤ) - (m : ℤ))) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
          (nhds (Q m)) := hconv m le_rfl
      have hbsqQ : bsq (subO1 a (Q m)) ≠ 0 := hbsq m le_rfl
      obtain ⟨ρS, hρS, S, hSan, hS2, hSsq⟩ := exists_sqrt_bsq_subO1 (a := a) hbsqQ
      have hSne0 : S (Q m) ≠ 0 := by
        intro hc
        exact hbsqQ (by rw [← hS2, hc]; ring)
      have hScont : ContinuousAt S (Q m) := (hSan (Q m) (Metric.mem_ball_self hρS)).continuousAt
      obtain ⟨ρS', hρS'0, hρS'⟩ := Metric.mem_nhds_iff.mp (hScont.eventually_ne hSne0)
      set ρS'' : ℝ := min ρS ρS' with hρS''def
      have hρS''pos : 0 < ρS'' := lt_min hρS hρS'0
      have hSsq'' : ∀ x ∈ Metric.ball (Q m) ρS'', S x ^ 2 = bsq (subO1 a x) :=
        fun x hx => hSsq x (Metric.ball_subset_ball (min_le_left _ _) hx)
      have hSne'' : ∀ x ∈ Metric.ball (Q m) ρS'', S x ≠ 0 :=
        fun x hx => hρS' (Metric.ball_subset_ball (min_le_right _ _) hx)
      set U : ℂ × ℂ → ℂ × ℂ := fun x => paramΛ a x (S x) with hUdef
      set W : ℂ × ℂ → ℂ × ℂ := fun x => paramΛ a x (-(S x)) with hWdef
      have hUcont : ContinuousAt U (Q m) := by
        rw [hUdef]
        simp only [paramΛ]
        refine ContinuousAt.prodMk ?_ ?_
        · exact (continuousAt_const.add (((continuousAt_const.sub hScont).mul
            (continuousAt_fst.add continuousAt_const)).div hScont hSne0))
        · exact (((continuousAt_const.sub hScont).mul continuousAt_snd).div hScont hSne0)
      have hWcont : ContinuousAt W (Q m) := by
        rw [hWdef]
        simp only [paramΛ]
        refine ContinuousAt.prodMk ?_ ?_
        · exact (continuousAt_const.add (((continuousAt_const.sub hScont.neg).mul
            (continuousAt_fst.add continuousAt_const)).div hScont.neg (neg_ne_zero.mpr hSne0)))
        · exact (((continuousAt_const.sub hScont.neg).mul continuousAt_snd).div hScont.neg
            (neg_ne_zero.mpr hSne0))
      -- the punctured disc on which the previous point is in the ball
      obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ ζ : ℂ, ζ ∈ Metric.ball (0 : ℂ) δ \ {0} →
          (e ζ).1 ((N : ℤ) - (m : ℤ)) ∈ Metric.ball (Q m) ρS'' ∧
            ζ ∈ Metric.ball (0 : ℂ) ρ \ {0} := by
        have hset : ({ζ : ℂ | (e ζ).1 ((N : ℤ) - (m : ℤ)) ∈ Metric.ball (Q m) ρS''}
            ∩ (Metric.ball (0 : ℂ) ρ \ {0})) ∈ nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ :=
          Filter.inter_mem
            (hconvQ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρS''pos))) hdom
        obtain ⟨δ, hδ0, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hset
        refine ⟨δ, hδ0, fun ζ hζ => ?_⟩
        exact hδsub ⟨hζ.1, by simpa using hζ.2⟩
      set Dd : Set ℂ := Metric.ball (0 : ℂ) δ \ {0} with hDddef
      have hDdsub : Dd ⊆ Metric.ball (0 : ℂ) ρ \ {0} := fun ζ hζ => (hδ ζ hζ).2
      have hDdb : ∀ ζ ∈ Dd, (e ζ).1 ((N : ℤ) - (m : ℤ)) ∈ Metric.ball (Q m) ρS'' :=
        fun ζ hζ => (hδ ζ hζ).1
      have hDdpre : IsPreconnected Dd := (isConnected_punctured_ball_zero hδ0).isPreconnected
      haveI : PreconnectedSpace ↥Dd := isPreconnected_iff_preconnectedSpace.mp hDdpre
      have hDdnhds : Dd ∈ nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ :=
        Filter.inter_mem (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hδ0)) self_mem_nhdsWithin
      -- the candidate dichotomy
      have hcand : ∀ ζ ∈ Dd,
          (e ζ).1 ((N : ℤ) - ((m : ℤ) + 1)) = U ((e ζ).1 ((N : ℤ) - (m : ℤ))) ∨
          (e ζ).1 ((N : ℤ) - ((m : ℤ) + 1)) = W ((e ζ).1 ((N : ℤ) - (m : ℤ))) := by
        intro ζ hζ
        have hζdom : ζ ∈ Metric.ball (0 : ℂ) ρ \ {0} := hDdsub hζ
        have hxmem := hDdb ζ hζ
        have hchainζ : IsChain a h (e ζ) := isChain_of_mem_H0 (hH0 ζ hζdom)
        have hidx : ((N : ℤ) - ((m : ℤ) + 1)) + 1 = (N : ℤ) - (m : ℤ) := by ring
        have hreg := hchainζ.1 ((N : ℤ) - ((m : ℤ) + 1))
        rw [hidx] at hreg
        have hrel : EqRelC a ((e ζ).1 ((N : ℤ) - ((m : ℤ) + 1)))
            ((e ζ).1 ((N : ℤ) - (m : ℤ))) := hreg.1
        have hbsqx : bsq (subO1 a ((e ζ).1 ((N : ℤ) - (m : ℤ)))) ≠ 0 := hreg.2.2
        have hP := eqRelC_solutions hrel hbsqx
        have hSx : S ((e ζ).1 ((N : ℤ) - (m : ℤ))) ^ 2
            = rhoPrimeSq a ((e ζ).1 ((N : ℤ) - (m : ℤ))) := by
          rw [hSsq'' _ hxmem]
          simp only [rhoPrimeSq, subO1, bsq, Prod.fst, Prod.snd]
        have hQx : rhoPrimeSq a ((e ζ).1 ((N : ℤ) - (m : ℤ))) ≠ 0 := by
          simpa only [rhoPrimeSq, subO1, bsq, Prod.fst, Prod.snd] using hbsqx
        exact eq_paramΛ_or_eq_neg hSx hQx hP
      -- continuity of the two sides on the subtype
      have hcontL : ContinuousOn (fun ζ : ↥Dd => (e ζ.1).1 ((N : ℤ) - ((m : ℤ) + 1))) Set.univ := by
        have hg : ContinuousOn (fun p : ChainData => p.1 ((N : ℤ) - ((m : ℤ) + 1))) Set.univ :=
          ((continuous_apply _).comp continuous_fst).continuousOn
        exact hg.comp (hcont.comp continuous_subtype_val.continuousOn (fun ζ _ => hDdsub ζ.2))
          (fun ζ _ => Set.mem_univ _)
      have hcontM : ContinuousOn (fun ζ : ↥Dd => (e ζ.1).1 ((N : ℤ) - (m : ℤ))) Set.univ := by
        have hg : ContinuousOn (fun p : ChainData => p.1 ((N : ℤ) - (m : ℤ))) Set.univ :=
          ((continuous_apply _).comp continuous_fst).continuousOn
        exact hg.comp (hcont.comp continuous_subtype_val.continuousOn (fun ζ _ => hDdsub ζ.2))
          (fun ζ _ => Set.mem_univ _)
      have hUon : ContinuousOn U (Metric.ball (Q m) ρS'') := by
        intro x hx
        have hSx : S x ≠ 0 := hSne'' x hx
        have hSc : ContinuousAt S x :=
          (hSan x (Metric.ball_subset_ball (min_le_left _ _) hx)).continuousAt
        rw [hUdef]
        simp only [paramΛ]
        exact ContinuousAt.continuousWithinAt (ContinuousAt.prodMk
          (continuousAt_const.add (((continuousAt_const.sub hSc).mul
            (continuousAt_fst.add continuousAt_const)).div hSc hSx))
          (((continuousAt_const.sub hSc).mul continuousAt_snd).div hSc hSx))
      have hWon : ContinuousOn W (Metric.ball (Q m) ρS'') := by
        intro x hx
        have hSx : S x ≠ 0 := hSne'' x hx
        have hSc : ContinuousAt S x :=
          (hSan x (Metric.ball_subset_ball (min_le_left _ _) hx)).continuousAt
        rw [hWdef]
        simp only [paramΛ]
        exact ContinuousAt.continuousWithinAt (ContinuousAt.prodMk
          (continuousAt_const.add (((continuousAt_const.sub hSc.neg).mul
            (continuousAt_fst.add continuousAt_const)).div hSc.neg (neg_ne_zero.mpr hSx)))
          (((continuousAt_const.sub hSc.neg).mul continuousAt_snd).div hSc.neg
            (neg_ne_zero.mpr hSx)))
      have hcontR : ContinuousOn (fun ζ : ↥Dd => U ((e ζ.1).1 ((N : ℤ) - (m : ℤ)))) Set.univ :=
        hUon.comp hcontM (fun ζ _ => hDdb ζ.1 ζ.2)
      have hcontRW : ContinuousOn (fun ζ : ↥Dd => W ((e ζ.1).1 ((N : ℤ) - (m : ℤ)))) Set.univ :=
        hWon.comp hcontM (fun ζ _ => hDdb ζ.1 ζ.2)
      set A : Set ↥Dd := {ζ | (e ζ.1).1 ((N : ℤ) - ((m : ℤ) + 1))
        = U ((e ζ.1).1 ((N : ℤ) - (m : ℤ)))} with hAdef
      have hAclosed : IsClosed A :=
        isClosed_eq (continuousOn_univ.mp hcontL) (continuousOn_univ.mp hcontR)
      have hWne : ∀ ζ : ↥Dd, U ((e ζ.1).1 ((N : ℤ) - (m : ℤ)))
          ≠ W ((e ζ.1).1 ((N : ℤ) - (m : ℤ))) := by
        intro ζ
        have hxmem := hDdb ζ.1 ζ.2
        have hSx : S ((e ζ.1).1 ((N : ℤ) - (m : ℤ))) ^ 2
            = rhoPrimeSq a ((e ζ.1).1 ((N : ℤ) - (m : ℤ))) := by
          rw [hSsq'' _ hxmem]
          simp only [rhoPrimeSq, subO1, bsq, Prod.fst, Prod.snd]
        have hQx : rhoPrimeSq a ((e ζ.1).1 ((N : ℤ) - (m : ℤ))) ≠ 0 := by
          have hchainζ : IsChain a h (e ζ.1) := isChain_of_mem_H0 (hH0 ζ.1 (hDdsub ζ.2))
          have hidx : ((N : ℤ) - ((m : ℤ) + 1)) + 1 = (N : ℤ) - (m : ℤ) := by ring
          have hb := (hchainζ.1 ((N : ℤ) - ((m : ℤ) + 1))).2.2
          rw [hidx] at hb
          simpa only [rhoPrimeSq, subO1, bsq, Prod.fst, Prod.snd] using hb
        exact paramΛ_ne_neg hSx hQx
      have hAcompl : Aᶜ = {ζ : ↥Dd | (e ζ.1).1 ((N : ℤ) - ((m : ℤ) + 1))
          = W ((e ζ.1).1 ((N : ℤ) - (m : ℤ)))} := by
        ext ζ
        simp only [Set.mem_compl_iff, hAdef, Set.mem_setOf_eq]
        constructor
        · intro hU
          rcases hcand ζ.1 ζ.2 with h1 | h1
          · exact absurd h1 hU
          · exact h1
        · intro hW hU
          exact hWne ζ (hU ▸ hW)
      have hAcompl_closed : IsClosed Aᶜ :=
        hAcompl ▸ isClosed_eq (continuousOn_univ.mp hcontL) (continuousOn_univ.mp hcontRW)
      have hsplit := (isPreconnected_iff_subset_of_disjoint_closed.mp
        (isPreconnected_univ : IsPreconnected (Set.univ : Set ↥Dd))) A Aᶜ hAclosed hAcompl_closed
        (fun x _ => by by_cases hx : x ∈ A <;> simp [hx])
        (by ext x; simp)
      have hcase : (∀ ζ ∈ Dd, (e ζ).1 ((N : ℤ) - ((m : ℤ) + 1))
            = U ((e ζ).1 ((N : ℤ) - (m : ℤ)))) ∨
          (∀ ζ ∈ Dd, (e ζ).1 ((N : ℤ) - ((m : ℤ) + 1))
            = W ((e ζ).1 ((N : ℤ) - (m : ℤ)))) := by
        rcases hsplit with hh | hh
        · left
          intro ζ hζ
          have := hh (Set.mem_univ (⟨ζ, hζ⟩ : ↥Dd))
          simpa only [hAdef, Set.mem_setOf_eq] using this
        · right
          intro ζ hζ
          have hmem : (⟨ζ, hζ⟩ : ↥Dd) ∈ (Aᶜ : Set ↥Dd) := hh (Set.mem_univ _)
          rw [hAcompl] at hmem
          exact hmem
      -- the new limit point
      obtain ⟨Qnext, hQnext, hQnext_form⟩ : ∃ Qnext : ℂ × ℂ,
          Tendsto (fun ζ => (e ζ).1 ((N : ℤ) - ((m : ℤ) + 1))) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
            (nhds Qnext) ∧ (Qnext = U (Q m) ∨ Qnext = W (Q m)) := by
        rcases hcase with hcaseU | hcaseW
        · refine ⟨U (Q m), ?_, Or.inl rfl⟩
          have h1 : Tendsto (fun ζ => U ((e ζ).1 ((N : ℤ) - (m : ℤ))))
              (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (U (Q m))) := hUcont.tendsto.comp hconvQ
          refine h1.congr' ?_
          exact Filter.eventually_iff.mpr
            (Filter.mem_of_superset hDdnhds (fun ζ hζ => (hcaseU ζ hζ).symm))
        · refine ⟨W (Q m), ?_, Or.inr rfl⟩
          have h1 : Tendsto (fun ζ => W ((e ζ).1 ((N : ℤ) - (m : ℤ))))
              (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (W (Q m))) := hWcont.tendsto.comp hconvQ
          refine h1.congr' ?_
          exact Filter.eventually_iff.mpr
            (Filter.mem_of_superset hDdnhds (fun ζ hζ => (hcaseW ζ hζ).symm))
      have hSx0 : S (Q m) ^ 2 = rhoPrimeSq a (Q m) := by
        rw [hS2]
        simp only [rhoPrimeSq, subO1, bsq, Prod.fst, Prod.snd]
      have hQx0 : rhoPrimeSq a (Q m) ≠ 0 := by
        simpa only [rhoPrimeSq, subO1, bsq, Prod.fst, Prod.snd] using hbsqQ
      obtain ⟨t, ht⟩ : ∃ t : Bool, Qnext = invBranch a t (Q m) := by
        rcases hQnext_form with hform | hform
        · rcases paramΛ_mem_invBranch (a := a) (Q := Q m) (S := S (Q m)) hSx0 hQx0 with h1 | h1
          · exact ⟨true, hform.trans h1⟩
          · exact ⟨false, hform.trans h1⟩
        · rcases paramΛ_neg_mem_invBranch (a := a) (Q := Q m) (S := S (Q m)) hSx0 hQx0 with h1 | h1
          · exact ⟨true, hform.trans h1⟩
          · exact ⟨false, hform.trans h1⟩
      have hQm : bwdP a σ (germC a h (eqLamC a ^ N * u₀)) = Q m := by
        have htake : σ.take m = σ := by rw [← hσlen]; exact List.take_length
        rw [← htake]
        exact (hid m le_rfl).symm
      have hidnext : Qnext = bwdP a (σ ++ [t]) (germC a h (eqLamC a ^ N * u₀)) := by
        rw [bwdP_append, show bwdP a [t] (bwdP a σ (germC a h (eqLamC a ^ N * u₀)))
          = invBranch a t (bwdP a σ (germC a h (eqLamC a ^ N * u₀))) from rfl]
        rw [hQm, ht]
      refine ⟨Function.update Q (m + 1) Qnext, σ ++ [t], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hσlen]
        simp
      · rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ m + 1)]
        exact hQ0
      · intro i hi
        by_cases heq : i = m + 1
        · rw [heq, Function.update_self]
          have hcast : ((N : ℤ) - (((m + 1 : ℕ)) : ℤ)) = (N : ℤ) - ((m : ℤ) + 1) := by
            push_cast; ring
          rw [hcast]
          exact hQnext
        · rw [Function.update_of_ne heq]
          exact hconv i (by omega)
      · intro i hi
        by_cases heq : i = m + 1
        · rw [heq, Function.update_self]
          have hlen : (σ ++ [t]).take (m + 1) = σ ++ [t] := by
            rw [show m + 1 = (σ ++ [t]).length by rw [List.length_append, hσlen]; simp]
            exact List.take_length
          rw [hlen]
          exact hidnext
        · rw [Function.update_of_ne heq]
          have htake : (σ ++ [t]).take i = σ.take i := List.take_append_of_le_length (by omega)
          rw [htake]
          exact hid i (by omega)
      · intro i hi
        by_cases heq : i = m + 1
        · rw [heq, Function.update_self]
          have hlen : (σ ++ [t]).length ≤ 2 * N := by
            rw [List.length_append, hσlen]; simp; omega
          rw [hidnext]
          exact hdeg (σ ++ [t]) hlen
        · rw [Function.update_of_ne heq]
          exact hbsq i (by omega)
      · intro i hi
        by_cases heq : i + 1 = m + 1
        · have him : i = m := by omega
          rw [show i + 1 = m + 1 by omega, Function.update_self, him,
            Function.update_of_ne (by omega : m ≠ m + 1)]
          exact (ht.symm ▸ eqRelC_invBranch t hbsqQ)
        · rw [Function.update_of_ne heq, Function.update_of_ne (by omega : i ≠ m + 1)]
          exact hEq i (by omega)
  -- ## packaging
  obtain ⟨Q, σ, hσlen, hQ0, hconv, hid, hbsq, hEq⟩ := key (2 * N) le_rfl
  have htailQ : Q (2 * N) = ugermC a h (eqLamC a ^ N * v₀) := by
    have h1 : Tendsto (fun ζ => (e ζ).1 ((N : ℤ) - (((2 * N : ℕ)) : ℤ)))
        (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (Q (2 * N))) := hconv (2 * N) le_rfl
    have h2 : ((N : ℤ) - (((2 * N : ℕ)) : ℤ)) = -(N : ℤ) := by push_cast; ring
    rw [h2] at h1
    exact tendsto_nhds_unique h1 (hlimDn N le_rfl)
  set q : ℤ → ℂ × ℂ := fun j =>
    if _ : -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ) then Q (((N : ℤ) - j).toNat)
    else if _ : (N : ℤ) ≤ j then germC a h (eqLamC a ^ j * u₀)
    else ugermC a h (eqLamC a ^ (-j) * v₀) with hqdef
  have hqval : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ (N : ℤ) → q j = Q (((N : ℤ) - j).toNat) := by
    intro j h1 h2
    rw [hqdef]
    exact dif_pos ⟨h1, h2⟩
  have hqup : ∀ j : ℤ, (N : ℤ) < j → q j = germC a h (eqLamC a ^ j * u₀) := by
    intro j hj
    rw [hqdef]
    show (if _ : -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ) then Q (((N : ℤ) - j).toNat)
      else if _ : (N : ℤ) ≤ j then germC a h (eqLamC a ^ j * u₀)
      else ugermC a h (eqLamC a ^ (-j) * v₀)) = germC a h (eqLamC a ^ j * u₀)
    rw [dif_neg (by omega : ¬ (-(N : ℤ) ≤ j ∧ j ≤ (N : ℤ))), dif_pos (by omega : (N : ℤ) ≤ j)]
  have hqdn : ∀ j : ℤ, j < -(N : ℤ) → q j = ugermC a h (eqLamC a ^ (-j) * v₀) := by
    intro j hj
    rw [hqdef]
    show (if _ : -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ) then Q (((N : ℤ) - j).toNat)
      else if _ : (N : ℤ) ≤ j then germC a h (eqLamC a ^ j * u₀)
      else ugermC a h (eqLamC a ^ (-j) * v₀)) = ugermC a h (eqLamC a ^ (-j) * v₀)
    rw [dif_neg (by omega : ¬ (-(N : ℤ) ≤ j ∧ j ≤ (N : ℤ))),
      dif_neg (by omega : ¬ ((N : ℤ) ≤ j))]
  have hqidx : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ (N : ℤ) → ((N : ℤ) - j).toNat ≤ 2 * N := by
    intro j h1 h2
    have h3 : (N : ℤ) - j ≤ ((2 * N : ℕ) : ℤ) := by push_cast; omega
    calc ((N : ℤ) - j).toNat ≤ (((2 * N : ℕ)) : ℤ).toNat := Int.toNat_le_toNat h3
      _ = 2 * N := by rw [Int.toNat_natCast]
  have hidxj : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ (N : ℤ) →
      (N : ℤ) - ((((N : ℤ) - j).toNat : ℕ) : ℤ) = j := by
    intro j h1 h2
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ (N : ℤ) - j)]
    ring
  have hqTend : ∀ j : ℤ, Tendsto (fun ζ => (e ζ).1 j) (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ)
      (nhds (q j)) := by
    intro j
    by_cases h1 : -(N : ℤ) ≤ j ∧ j ≤ (N : ℤ)
    · rw [hqval j h1.1 h1.2]
      refine (hconv _ (hqidx j h1.1 h1.2)).congr' ?_
      exact Filter.eventually_iff.mpr (Filter.univ_mem' fun ζ => by
        show (e ζ).1 ((N : ℤ) - ((((N : ℤ) - j).toNat : ℕ) : ℤ)) = (e ζ).1 j
        rw [hidxj j h1.1 h1.2])
    · by_cases h2 : (N : ℤ) ≤ j
      · have hqj : q j = germC a h (eqLamC a ^ j * u₀) := hqup j (by omega)
        rw [hqj]
        have hind : j = (((j.toNat : ℕ)) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
        have hz : eqLamC a ^ j = eqLamC a ^ j.toNat := by
          conv_lhs => rw [hind, zpow_natCast]
        rw [hz]
        have hfun : (fun ζ : ℂ => (e ζ).1 j) = (fun ζ => (e ζ).1 (((j.toNat : ℕ)) : ℤ)) := by
          funext ζ; conv_lhs => rw [hind]
        rw [hfun]
        exact hlimUp j.toNat (by omega)
      · have hqj : q j = ugermC a h (eqLamC a ^ (-j) * v₀) := hqdn j (by omega)
        rw [hqj]
        have hind : j = -((((-j).toNat : ℕ)) : ℤ) := by
          have h := (Int.toNat_of_nonneg (by omega : 0 ≤ -j)).symm
          omega
        have hz : eqLamC a ^ (-j) = eqLamC a ^ (-j).toNat := by
          have h2 : -j = ((((-j).toNat : ℕ)) : ℤ) := (Int.toNat_of_nonneg (by omega)).symm
          conv_lhs => rw [h2, zpow_natCast]
        rw [hz]
        have hfun : (fun ζ : ℂ => (e ζ).1 j) = (fun ζ => (e ζ).1 (-((((-j).toNat : ℕ)) : ℤ))) := by
          funext ζ; conv_lhs => rw [hind]
        rw [hfun]
        exact hlimDn (-j).toNat (by omega)
  refine ⟨q, ?_, ?_, ?_, ?_, hqTend, ?_, ?_⟩
  · rw [hqval _ (by omega) le_rfl]
    have h0 : ((N : ℤ) - (N : ℤ)).toNat = 0 := by
      rw [sub_self]
      exact Int.toNat_zero
    rw [h0]
    exact hQ0
  · rw [hqval _ (by omega) (by omega)]
    have h2N : ((N : ℤ) - (-(N : ℤ))).toNat = 2 * N := by
      have hcast : (N : ℤ) - (-(N : ℤ)) = ((2 * N : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring
      rw [hcast, Int.toNat_natCast]
    rw [h2N]
    exact htailQ
  · intro j hj
    exact hqup j hj
  · intro j hj
    exact hqdn j hj
  · intro j hj1 hj2
    rw [hqval j hj1 hj2]
    exact hbsq _ (hqidx j hj1 hj2)
  · intro j hj1 hj2
    rw [hqval j hj1 (le_of_lt hj2), hqval (j + 1) (by omega) (by omega)]
    have hkey : ((N : ℤ) - j).toNat = ((N : ℤ) - (j + 1)).toNat + 1 := by
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg (by omega : 0 ≤ (N : ℤ) - j),
        Int.toNat_of_nonneg (by omega : 0 ≤ (N : ℤ) - (j + 1))]
      ring
    rw [hkey]
    exact hEq _ (by omega)

end

end Work.EQ
