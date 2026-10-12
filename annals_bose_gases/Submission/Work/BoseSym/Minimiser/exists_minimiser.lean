import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseSym.Minimiser.Core
import Submission.Work.BoseSym.Minimiser.exists_unit_vec
import Submission.Work.BoseSym.Minimiser.rellich_subseq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Minimiser

open MeasureTheory Filter
open Work.BoseSym
open scoped Topology ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem exists_minimiser (N : ℕ) (L : ℝ) (hL : 0 < L) (C : ℝ) (W : Conf N → ℝ)
    (hW : BddBy N W C) (hWnn : AENonneg N W) (hWm : AEMeas N W) :
    ∃ p : {p : Hsub N L // l2Sq (p : Amb N) = 1},
      dirForm W (p : Amb N) =
        ⨅ q : {q : Hsub N L // l2Sq (q : Amb N) = 1}, dirForm W (q : Amb N) := by
  classical
  -- ## Setup: the shift and the `L∞` classes
  have hCnn : 0 ≤ C := by
    have h := hW 0
    exact le_trans (abs_nonneg _) h
  set K : ℝ := C + 1 with hK
  have hKpos : 0 < K := by positivity
  have hWmem : MemLp W (⊤ : ℝ≥0∞) (volC N) :=
    memLp_top_of_bound hWm.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hW x)
  set Wop : L2top N := hWmem.toLp W with hWopdef
  have hWop_ae : (Wop : Conf N → ℝ) =ᵐ[volC N] W := MemLp.coeFn_toLp hWmem
  have hKcst_ae : (constLp N K : Conf N → ℝ) =ᵐ[volC N] fun _ => K := constLp_coeFn K
  set Vop : L2top N := Wop + constLp N K with hVopdef
  have hVop_fun : (Vop : Conf N → ℝ) =ᵐ[volC N] fun x => W x + K := by
    filter_upwards [MeasureTheory.Lp.coeFn_add Wop (constLp N K), hWop_ae, hKcst_ae]
      with x h1 h2 h3
    rw [h1]
    simp only [Pi.add_apply, h2, h3]
  have hVnonneg : (0 : Conf N → ℝ) ≤ᵐ[volC N] (Vop : Conf N → ℝ) := by
    filter_upwards [hVop_fun] with x hx
    rw [hx, hK]
    simp only [Pi.zero_apply]
    have := (abs_le.mp (hW x)).1
    linarith
  have hVone_nonneg :
      (0 : Conf N → ℝ) ≤ᵐ[volC N] ((Vop - constLp N 1 : L2top N) : Conf N → ℝ) := by
    filter_upwards [MeasureTheory.Lp.coeFn_sub Vop (constLp N 1), hVop_fun,
      constLp_coeFn (N := N) 1] with x h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply, Pi.zero_apply, h2, h3, hK]
    have := (abs_le.mp (hW x)).1
    linarith
  -- ## The shifted quadratic form and its bilinear form
  have hG_self : ∀ p : Amb N, formP Vop p p = dirForm W p + K * l2Sq p := by
    intro p
    rw [formP_self, dirForm]
    have h1 : inner ℝ (Vop • p.1) p.1
        = inner ℝ (Wop • p.1) p.1 + K * inner ℝ p.1 p.1 := by
      rw [hVopdef, MeasureTheory.Lp.smul_add, inner_add_left, inner_lpSMul_constLp]
    rw [h1, inner_lpSMul_eq_potSq hWop_ae p, l2Sq_eq_inner]
    ring
  have hhSq_G : ∀ p : Amb N, hSq p ≤ formP Vop p p :=
    fun p => hSq_le_formP_self hVone_nonneg p
  have hGnn : ∀ p : Amb N, 0 ≤ formP Vop p p :=
    fun p => formP_self_nonneg hVnonneg p
  -- ## The admissible set and the infimum
  let Sset : Type := {p : Hsub N L // l2Sq (p : Amb N) = 1}
  haveI hne : Nonempty Sset := by
    obtain ⟨p, hp⟩ := exists_unit_vec N L hL
    exact ⟨⟨p, hp⟩⟩
  obtain ⟨p₀, hp₀⟩ := exists_unit_vec N L hL
  set m : ℝ := ⨅ q : Sset, dirForm W (q : Amb N) with hm
  have hWCnn : (0 : Conf N → ℝ) ≤ᵐ[volC N] ((Wop + constLp N C : L2top N) : Conf N → ℝ) := by
    filter_upwards [MeasureTheory.Lp.coeFn_add Wop (constLp N C), hWop_ae, constLp_coeFn (N := N) C]
      with x h1 h2 h3
    rw [h1]
    simp only [Pi.add_apply, Pi.zero_apply, h2, h3]
    linarith [(abs_le.mp (hW x)).1]
  have hbdd : BddBelow (Set.range fun q : Sset => dirForm W (q : Amb N)) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨q, rfl⟩
    have hpot : -C * l2Sq ((q : Hsub N L) : Amb N) ≤ potSq W ((q : Hsub N L) : Amb N) :=
      potSq_ge_shift hWop_ae hWCnn _
    have hl : l2Sq ((q : Hsub N L) : Amb N) = 1 := q.2
    have hg : 0 ≤ gSq ((q : Hsub N L) : Amb N) := by
      simp only [gSq]
      exact Finset.sum_nonneg fun j _ => by positivity
    simp only [dirForm]
    rw [hl, mul_one] at hpot
    linarith
  have hmle : ∀ q : Sset, m ≤ dirForm W (q : Amb N) := fun q => by
    rw [hm]; exact ciInf_le hbdd q
  -- ## The Rayleigh quotient inequality
  have hray : ∀ p : Hsub N L, m * l2Sq (p : Amb N) ≤ dirForm W (p : Amb N) := by
    intro p
    by_cases h0 : l2Sq (p : Amb N) = 0
    · rw [h0, mul_zero]
      have hp1 : (p : Amb N).1 = 0 := by
        have h : ‖(p : Amb N).1‖ ^ 2 = 0 := by simpa only [l2Sq] using h0
        exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
      have hpot : potSq W (p : Amb N) = 0 := by
        rw [potSq]
        have hc : ((p : Amb N).1 : Conf N → ℝ) =ᵐ[volC N] (0 : Conf N → ℝ) := by
          rw [hp1]; exact MeasureTheory.Lp.coeFn_zero ℝ 2 (volC N)
        have hz : (fun x => W x * (((p : Amb N).1 : Conf N → ℝ) x) ^ 2)
            =ᵐ[volC N] fun _ => (0 : ℝ) := by
          filter_upwards [hc] with x hx
          rw [hx]; simp
        rw [integral_congr_ae hz]; simp
      rw [dirForm, hpot, add_zero]
      rw [gSq]
      exact Finset.sum_nonneg fun j _ => by positivity
    · have hpos : 0 < l2Sq (p : Amb N) :=
        lt_of_le_of_ne (by rw [l2Sq]; positivity) (Ne.symm h0)
      have hlam : 0 ≤ l2Sq (p : Amb N) := hpos.le
      set c : ℝ := (Real.sqrt (l2Sq (p : Amb N)))⁻¹ with hc
      have hc2 : c ^ 2 = (l2Sq (p : Amb N))⁻¹ := by
        rw [hc, inv_pow, Real.sq_sqrt hlam]
      have hcl2 : c ^ 2 * l2Sq (p : Amb N) = 1 := by
        rw [hc2, inv_mul_cancel₀ (ne_of_gt hpos)]
      have hmem : m ≤ c ^ 2 * dirForm W (p : Amb N) := by
        have h := hmle ⟨c • p, by
          show l2Sq ((c • p : Hsub N L) : Amb N) = 1
          rw [show ((c • p : Hsub N L) : Amb N) = c • (p : Amb N) from rfl, l2Sq_smul_amb]
          exact hcl2⟩
        rw [show ((c • p : Hsub N L) : Amb N) = c • (p : Amb N) from rfl,
          dirForm_smul_amb] at h
        exact h
      have h1 : m * l2Sq (p : Amb N)
          ≤ (c ^ 2 * dirForm W (p : Amb N)) * l2Sq (p : Amb N) :=
        mul_le_mul_of_nonneg_right hmem hlam
      have h2 : (c ^ 2 * dirForm W (p : Amb N)) * l2Sq (p : Amb N)
          = dirForm W (p : Amb N) := by
        linear_combination (dirForm W (p : Amb N)) * hcl2
      linarith
  set κ : ℝ := m + K with hκdef
  have hHpos : ∀ p : Hsub N L,
      0 ≤ formP Vop (p : Amb N) (p : Amb N) - κ * inner ℝ (p : Amb N).1 (p : Amb N).1 := by
    intro p
    have h1 := hG_self (p : Amb N)
    have h2 := hray p
    rw [h1, l2Sq_eq_inner, hκdef] at *
    linarith
  have hHcs : ∀ p q : Hsub N L,
      (formP Vop (p : Amb N) (q : Amb N) - κ * inner ℝ (p : Amb N).1 (q : Amb N).1) ^ 2
        ≤ (formP Vop (p : Amb N) (p : Amb N) - κ * inner ℝ (p : Amb N).1 (p : Amb N).1)
          * (formP Vop (q : Amb N) (q : Amb N) - κ * inner ℝ (q : Amb N).1 (q : Amb N).1) :=
    fun p q => shiftH_sq_le Vop κ hHpos p q
  -- ## A minimising sequence
  have hseq : ∀ n : ℕ, ∃ q : Sset, dirForm W (q : Amb N) < m + 1 / ((n : ℝ) + 1) := by
    intro n
    have hlt : (⨅ q : Sset, dirForm W (q : Amb N)) < m + 1 / ((n : ℝ) + 1) := by
      rw [← hm]; exact lt_add_of_pos_right _ (by positivity)
    exact (ciInf_lt_iff hbdd).mp hlt
  let u : ℕ → Sset := fun n => Classical.choose (hseq n)
  have hu : ∀ n, dirForm W ((u n) : Amb N) < m + 1 / ((n : ℝ) + 1) :=
    fun n => Classical.choose_spec (hseq n)
  have hum : ∀ n, m ≤ dirForm W ((u n) : Amb N) := fun n => hmle (u n)
  have hlim : Tendsto (fun n => dirForm W ((u n) : Amb N)) atTop (nhds m) := by
    have hb : ∀ n, dirForm W ((u n) : Amb N) - m ≤ 1 / ((n : ℝ) + 1) := fun n => by
      linarith [hu n]
    have hb0 : ∀ n, 0 ≤ dirForm W ((u n) : Amb N) - m := fun n => by linarith [hum n]
    have hg : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h3 : Tendsto (fun n => dirForm W ((u n) : Amb N) - m) atTop (nhds 0) :=
      squeeze_zero hb0 hb hg
    have h4 : Tendsto (fun n => (dirForm W ((u n) : Amb N) - m) + m) atTop (nhds (0 + m)) :=
      h3.add_const m
    simpa using h4
  have hGlimeq : (fun n => formP Vop ((u n) : Amb N) ((u n) : Amb N))
      = fun n => dirForm W ((u n) : Amb N) + K := by
    funext n
    rw [hG_self, (u n).2, mul_one]
  have hGlim : Tendsto (fun n => formP Vop ((u n) : Amb N) ((u n) : Amb N)) atTop (nhds κ) := by
    rw [hGlimeq, hκdef]
    have h4 : Tendsto (fun n => dirForm W ((u n) : Amb N) + K) atTop (nhds (m + K)) :=
      hlim.add_const K
    simpa using h4
  -- ## Rellich compactness
  have hbd : ∀ n, hSq ((u n) : Amb N) ≤ κ + 1 := by
    intro n
    have h1 := hhSq_G ((u n) : Amb N)
    have h2 : formP Vop ((u n) : Amb N) ((u n) : Amb N) = dirForm W ((u n) : Amb N) + K := by
      rw [hG_self, (u n).2, mul_one]
    have h4 : dirForm W ((u n) : Amb N) < m + 1 / ((n : ℝ) + 1) := hu n
    have h5 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      have hd : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hd
      simpa using h
    rw [h2] at h1
    rw [hκdef]
    linarith
  obtain ⟨ψ, hψ, w, hw⟩ := rellich_subseq N L (κ + 1) (fun n => ((u n) : Hsub N L)) hbd
  -- ## Passing to the subsequence
  set v : ℕ → Hsub N L := fun n => ((u (ψ n)) : Hsub N L) with hv
  have hv2 : ∀ n, l2Sq (v n : Amb N) = 1 := fun n => (u (ψ n)).2
  have hvw : TendstoL2 N (fun n => jEmbed N L (v n)) w := hw
  have hvlim : Tendsto (fun n => dirForm W (v n : Amb N)) atTop (nhds m) :=
    hlim.comp hψ.tendsto_atTop
  have hvG : Tendsto (fun n => formP Vop (v n : Amb N) (v n : Amb N)) atTop (nhds κ) :=
    hGlim.comp hψ.tendsto_atTop
  have hfst : Tendsto (fun n => (v n : Amb N).1) atTop (nhds w) := hvw
  have hw1 : ‖w‖ = 1 := by
    have h2 : (fun n => ‖jEmbed N L (v n)‖) = fun _ => (1 : ℝ) := by
      funext n
      show ‖(v n : Amb N).1‖ = 1
      have hsq : ‖(v n : Amb N).1‖ ^ 2 = 1 := by rw [← l2Sq, hv2 n]
      calc ‖(v n : Amb N).1‖ = Real.sqrt (‖(v n : Amb N).1‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ = Real.sqrt 1 := by rw [hsq]
        _ = 1 := Real.sqrt_one
    have h1 := hvw.norm
    rw [h2] at h1
    exact (tendsto_const_nhds_iff.mp h1).symm
  have hnorm : ∀ n, ‖(v n : Amb N).1‖ = 1 := by
    intro n
    have hsq : ‖(v n : Amb N).1‖ ^ 2 = 1 := by rw [← l2Sq, hv2 n]
    calc ‖(v n : Amb N).1‖ = Real.sqrt (‖(v n : Amb N).1‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt 1 := by rw [hsq]
      _ = 1 := Real.sqrt_one
  -- ## The limit of the shifted form is `0`
  have hAfun : Tendsto (fun n => formP Vop (v n : Amb N) (v n : Amb N) - κ) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => formP Vop (v n : Amb N) (v n : Amb N) - κ) atTop (nhds (κ - κ)) :=
      hvG.sub_const κ
    simpa using h1
  have hA : ∀ δ > 0, ∃ M, ∀ n ≥ M,
      |formP Vop (v n : Amb N) (v n : Amb N) - κ| < δ := by
    intro δ hδ
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hAfun δ hδ
    exact ⟨M, fun n hn => by
      have := hM n hn
      rwa [Real.dist_eq, sub_zero] at this⟩
  have hB : ∀ δ > 0, ∃ M, ∀ n ≥ M, ‖(v n : Amb N).1 - w‖ < δ := by
    intro δ hδ
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hfst δ hδ
    exact ⟨M, fun n hn => by
      have := hM n hn
      rwa [dist_eq_norm] at this⟩
  -- ## Cauchy–Schwarz controls the pairings
  have hHp : ∀ n mm : ℕ,
      (formP Vop (v n : Amb N) (v mm : Amb N)
          - κ * inner ℝ (v n : Amb N).1 (v mm : Amb N).1) ^ 2
        ≤ (formP Vop (v n : Amb N) (v n : Amb N) - κ)
          * (formP Vop (v mm : Amb N) (v mm : Amb N) - κ) := by
    intro n mm
    have h := hHcs (v n) (v mm)
    rw [← l2Sq_eq_inner (v n : Amb N), hv2 n, mul_one,
      ← l2Sq_eq_inner (v mm : Amb N), hv2 mm, mul_one] at h
    exact h
  have hApos : ∀ n, 0 ≤ formP Vop (v n : Amb N) (v n : Amb N) - κ := by
    intro n
    have h1 : formP Vop (v n : Amb N) (v n : Amb N)
        = dirForm W (v n : Amb N) + K := by rw [hG_self, hv2 n, mul_one]
    have h2 := hum (ψ n)
    rw [h1, hκdef]
    linarith
  -- ## The sequence is Cauchy
  have hcauchy : CauchySeq (fun n => (v n : Amb N)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N1, hN1⟩ := hA (ε ^ 2 / 16) (by positivity)
    obtain ⟨N2, hN2⟩ := hB (ε ^ 2 / (16 * (|κ| + 1))) (by positivity)
    refine ⟨max N1 N2, fun n hn mm hmm => ?_⟩
    have hn1 : N1 ≤ n := le_trans (le_max_left N1 N2) hn
    have hmm1 : N1 ≤ mm := le_trans (le_max_left N1 N2) hmm
    have hn2 : N2 ≤ n := le_trans (le_max_right N1 N2) hn
    have hmm2 : N2 ≤ mm := le_trans (le_max_right N1 N2) hmm
    set An : ℝ := formP Vop (v n : Amb N) (v n : Amb N) - κ with hAn
    set Am : ℝ := formP Vop (v mm : Amb N) (v mm : Amb N) - κ with hAm
    have hAnn : 0 ≤ An := by rw [hAn]; exact hApos n
    have hAmm : 0 ≤ Am := by rw [hAm]; exact hApos mm
    have hAnabs : |An| < ε ^ 2 / 16 := by rw [hAn]; exact hN1 n hn1
    have hAmabs : |Am| < ε ^ 2 / 16 := by rw [hAm]; exact hN1 mm hmm1
    have hAnle : An < ε ^ 2 / 16 := by rw [abs_of_nonneg hAnn] at hAnabs; exact hAnabs
    have hAmle : Am < ε ^ 2 / 16 := by rw [abs_of_nonneg hAmm] at hAmabs; exact hAmabs
    have hβn : ‖(v n : Amb N).1 - w‖ < ε ^ 2 / (16 * (|κ| + 1)) := hN2 n hn2
    have hβm : ‖(v mm : Amb N).1 - w‖ < ε ^ 2 / (16 * (|κ| + 1)) := hN2 mm hmm2
    -- the key quadratic identity
    have hquad : formP Vop ((v n : Amb N) - (v mm : Amb N)) ((v n : Amb N) - (v mm : Amb N))
        = An + Am
          - 2 * (formP Vop (v n : Amb N) (v mm : Amb N)
              - κ * inner ℝ (v n : Amb N).1 (v mm : Amb N).1)
          + 2 * κ * (1 - inner ℝ (v n : Amb N).1 (v mm : Amb N).1) := by
      rw [hAn, hAm, formP_sub_self]
      ring
    -- the inner-product bound
    have hdec : inner ℝ (v n : Amb N).1 (v mm : Amb N).1 - inner ℝ w w
        = inner ℝ ((v n : Amb N).1 - w) (v mm : Amb N).1
          + inner ℝ w ((v mm : Amb N).1 - w) := by
      rw [inner_sub_left, inner_sub_right]
      ring
    have hww : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw1]; norm_num
    have hkey : inner ℝ (v n : Amb N).1 (v mm : Amb N).1 - 1
        = inner ℝ ((v n : Amb N).1 - w) (v mm : Amb N).1
          + inner ℝ w ((v mm : Amb N).1 - w) := by
      rw [← hww]; exact hdec
    have hInner : |1 - inner ℝ (v n : Amb N).1 (v mm : Amb N).1| ≤ ‖(v n : Amb N).1 - w‖
        + ‖(v mm : Amb N).1 - w‖ := by
      have h1 : 1 - inner ℝ (v n : Amb N).1 (v mm : Amb N).1
          = -(inner ℝ ((v n : Amb N).1 - w) (v mm : Amb N).1
              + inner ℝ w ((v mm : Amb N).1 - w)) := by linarith [hkey]
      rw [h1, abs_neg]
      calc |inner ℝ ((v n : Amb N).1 - w) (v mm : Amb N).1
            + inner ℝ w ((v mm : Amb N).1 - w)|
          ≤ |inner ℝ ((v n : Amb N).1 - w) (v mm : Amb N).1|
            + |inner ℝ w ((v mm : Amb N).1 - w)| := abs_add_le _ _
        _ ≤ ‖(v n : Amb N).1 - w‖ * ‖(v mm : Amb N).1‖
            + ‖w‖ * ‖(v mm : Amb N).1 - w‖ :=
            add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
        _ = ‖(v n : Amb N).1 - w‖ + ‖(v mm : Amb N).1 - w‖ := by
            rw [hnorm mm, hw1, mul_one, one_mul]
    -- the Cauchy–Schwarz bound on the pairing
    set Pq : ℝ := formP Vop (v n : Amb N) (v mm : Amb N)
      - κ * inner ℝ (v n : Amb N).1 (v mm : Amb N).1 with hPq
    have hP2 : Pq ^ 2 ≤ An * Am := by rw [hPq, hAn, hAm]; exact hHp n mm
    have hPabs : |Pq| ≤ (An + Am) / 2 := by
      have h1 : Pq ^ 2 ≤ An * Am := hP2
      have h2 : Real.sqrt (Pq ^ 2) ≤ Real.sqrt (An * Am) := Real.sqrt_le_sqrt h1
      rw [Real.sqrt_sq_eq_abs] at h2
      have h3 : Real.sqrt (An * Am) ≤ (An + Am) / 2 := by
        rw [Real.sqrt_mul hAnn Am]
        nlinarith [sq_nonneg (Real.sqrt An - Real.sqrt Am), Real.sq_sqrt hAnn,
          Real.sq_sqrt hAmm, Real.sqrt_nonneg An, Real.sqrt_nonneg Am]
      linarith
    -- conclude
    have hnorm2 : ‖(v n : Amb N) - (v mm : Amb N)‖ ^ 2
        ≤ formP Vop ((v n : Amb N) - (v mm : Amb N)) ((v n : Amb N) - (v mm : Amb N)) :=
      le_trans (norm_sq_le_hSq _) (hhSq_G _)
    have hfinal : ‖(v n : Amb N) - (v mm : Amb N)‖ ^ 2 < ε ^ 2 := by
      have hk1 : 2 * κ * (1 - inner ℝ (v n : Amb N).1 (v mm : Amb N).1)
          ≤ 2 * |κ| * |1 - inner ℝ (v n : Amb N).1 (v mm : Amb N).1| := by
        have h1 : 2 * κ * (1 - inner ℝ (v n : Amb N).1 (v mm : Amb N).1)
            ≤ |2 * κ * (1 - inner ℝ (v n : Amb N).1 (v mm : Amb N).1)| := le_abs_self _
        rwa [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h1
      have hk2 : 2 * |κ| * |1 - inner ℝ (v n : Amb N).1 (v mm : Amb N).1|
          ≤ 2 * |κ| * (‖(v n : Amb N).1 - w‖ + ‖(v mm : Amb N).1 - w‖) :=
        mul_le_mul_of_nonneg_left hInner (by positivity)
      have hPm : 2 * |Pq| ≤ An + Am := by linarith [hPabs]
      have hPq2 : -2 * Pq ≤ 2 * |Pq| := by linarith [neg_le_abs Pq]
      have hbound : ‖(v n : Amb N) - (v mm : Amb N)‖ ^ 2
          ≤ (An + Am) + (An + Am)
            + 2 * |κ| * (‖(v n : Amb N).1 - w‖ + ‖(v mm : Amb N).1 - w‖) := by
        rw [hquad] at hnorm2
        linarith [hnorm2, hPm, hPq2, hk1, hk2]
      have hA4 : (An + Am) + (An + Am) ≤ ε ^ 2 / 16 + ε ^ 2 / 16 + (ε ^ 2 / 16 + ε ^ 2 / 16) := by
        linarith [hAnle.le, hAmle.le]
      have hβ4 : 2 * |κ| * (‖(v n : Amb N).1 - w‖ + ‖(v mm : Amb N).1 - w‖)
          ≤ 2 * (|κ| + 1) * (ε ^ 2 / (16 * (|κ| + 1)) + ε ^ 2 / (16 * (|κ| + 1))) := by
        refine mul_le_mul (by linarith [abs_nonneg κ]) (add_le_add hβn.le hβm.le)
          (by positivity) (by positivity)
      have hβ4' : 2 * (|κ| + 1) * (ε ^ 2 / (16 * (|κ| + 1)) + ε ^ 2 / (16 * (|κ| + 1)))
          = ε ^ 2 / 4 := by
        have hne : (|κ| + 1) ≠ 0 := by positivity
        field_simp
        ring
      nlinarith [hbound, hA4, hβ4, hβ4', hε]
    have := lt_of_pow_lt_pow_left₀ 2 hε.le hfinal
    rwa [dist_eq_norm]
  -- ## The limit point
  obtain ⟨q0, hq0⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hq0Hsub : q0 ∈ Hsub N L := by
    have hcl : IsClosed (((Hsub N L : Submodule ℝ (Amb N))) : Set (Amb N)) := by
      rw [Hsub, Submodule.topologicalClosure_coe]
      exact isClosed_closure
    refine hcl.mem_of_tendsto hq0 (Filter.Eventually.of_forall fun n => ?_)
    exact (v n).2
  have hq0fst : Tendsto (fun n => (v n : Amb N).1) atTop (nhds q0.1) :=
    (continuous_fst.tendsto q0).comp hq0
  have hq0w : q0.1 = w := tendsto_nhds_unique hq0fst hfst
  have hq0l2 : l2Sq q0 = 1 := by
    rw [l2Sq, hq0w, hw1]
    norm_num
  -- ## The Dirichlet form is continuous along the sequence
  have hdircont : Tendsto (fun n => dirForm W (v n : Amb N)) atTop (nhds (dirForm W q0)) := by
    have hpot : Tendsto (fun n => potSq W (v n : Amb N)) atTop (nhds (potSq W q0)) :=
      Work.BoseSym.Form.tendsto_potSq hW hWm hq0fst
    have hgsq : Tendsto (fun n => gSq (v n : Amb N)) atTop (nhds (gSq q0)) := by
      have hcont : Continuous fun p : Amb N => gSq p := by
        have h : (fun p : Amb N => gSq p) = fun p => ∑ j : GIdx N, ‖p.2 j‖ ^ 2 := by
          funext p; simp only [gSq]
        rw [h]
        exact continuous_finsetSum _ fun j _ =>
          ((continuous_apply j).comp continuous_snd).norm.pow 2
      exact hcont.tendsto q0 |>.comp hq0
    have h2 : Tendsto (fun n => dirForm W (v n : Amb N)) atTop
        (nhds (gSq q0 + potSq W q0)) := by
      have := hgsq.add hpot
      simpa only [dirForm] using this
    simpa only [dirForm] using h2
  have hq0dir : dirForm W q0 = m := tendsto_nhds_unique hdircont hvlim
  refine ⟨⟨⟨q0, hq0Hsub⟩, hq0l2⟩, ?_⟩
  change dirForm W q0 = ⨅ q : Sset, dirForm W (q : Amb N)
  rw [← hm]
  exact hq0dir

end

end Work.BoseSym.Minimiser
