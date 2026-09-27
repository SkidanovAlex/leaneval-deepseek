import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.HeteroAlgebra

namespace Work.EQ.Junc

open Filter

noncomputable section

/-! **Cluster values of a backward branch at a limit point** (a genuine piece of
`Work.EQ.junction_limit_segment`, not a restatement of it).

Let `P k → S` with the `O₁`-radicand of `S` nonvanishing, and let the signs `t k` be arbitrary.
Then some subsequence of the labelled backward images `invBranch a (t k) (P k)` converges to one
of the two backward branches of `S`.  The letter may flip relative to `t` when the subsequence
crosses the branch cut of the complex square root, so **do not** try to use
`Work.EQ.invBranch_continuousAt` (it needs `Complex.slitPlane` and is unusable here). -/

/-! ### Elementary algebra of the backward branch -/

/-- The complex sign `±1` attached to a `Bool` letter. -/
def sgnC (b : Bool) : ℂ := if b then 1 else -1

@[simp] lemma sgnC_true : sgnC true = 1 := rfl
@[simp] lemma sgnC_false : sgnC false = -1 := rfl

lemma sgnC_not (b : Bool) : sgnC (!b) = -sgnC b := by
  cases b <;> simp [sgnC]

/-- The normalised "radial" vector `(brho w)⁻¹ • w`, where `w = subO1 a Q`. -/
def F (a : ℝ) (Q : ℂ × ℂ) : ℂ × ℂ := (brho (subO1 a Q))⁻¹ • subO1 a Q

lemma F_fst (a : ℝ) (Q : ℂ × ℂ) :
    (F a Q).1 = (subO1 a Q).1 / brho (subO1 a Q) := by
  simp only [F, Prod.smul_fst, smul_eq_mul, div_eq_mul_inv]
  ring

lemma F_snd (a : ℝ) (Q : ℂ × ℂ) :
    (F a Q).2 = (subO1 a Q).2 / brho (subO1 a Q) := by
  simp only [F, Prod.smul_snd, smul_eq_mul, div_eq_mul_inv]
  ring

lemma norm_F (a : ℝ) (Q : ℂ × ℂ) :
    ‖F a Q‖ = ‖subO1 a Q‖ / ‖brho (subO1 a Q)‖ := by
  rw [F, norm_smul, norm_inv, div_eq_mul_inv, mul_comm]

lemma F_mul_brho_fst {a : ℝ} {Q : ℂ × ℂ} (h : brho (subO1 a Q) ≠ 0) :
    (F a Q).1 * brho (subO1 a Q) = (subO1 a Q).1 := by
  rw [F_fst, div_mul_cancel₀ _ h]

lemma F_mul_brho_snd {a : ℝ} {Q : ℂ × ℂ} (h : brho (subO1 a Q) ≠ 0) :
    (F a Q).2 * brho (subO1 a Q) = (subO1 a Q).2 := by
  rw [F_snd, div_mul_cancel₀ _ h]

/-- The backward branch in terms of the normalised radial vector. -/
lemma invBranch_eq_sgnC_smul (a : ℝ) (s : Bool) (Q : ℂ × ℂ) :
    invBranch a s Q = -Q + sgnC s • F a Q := by
  cases s
  · ext
    · simp only [invBranch, F, sgnC_false, Bool.false_eq_true, ite_false, subO1, brho, bsq,
        Prod.fst_add, Prod.fst_neg, Prod.smul_fst, smul_eq_mul, div_eq_mul_inv, neg_one_mul]
      ring
    · simp only [invBranch, F, sgnC_false, Bool.false_eq_true, ite_false, subO1, brho, bsq,
        Prod.snd_add, Prod.snd_neg, Prod.smul_snd, smul_eq_mul, div_eq_mul_inv, neg_one_mul]
      ring
  · ext
    · simp only [invBranch, F, sgnC_true, ite_true, subO1, brho, bsq,
        Prod.fst_add, Prod.fst_neg, Prod.smul_fst, smul_eq_mul, div_eq_mul_inv, one_mul]
      ring
    · simp only [invBranch, F, sgnC_true, ite_true, subO1, brho, bsq,
        Prod.snd_add, Prod.snd_neg, Prod.smul_snd, smul_eq_mul, div_eq_mul_inv, one_mul]
      ring

/-! ### Elementary topological facts -/

lemma continuous_subO1 (a : ℝ) : Continuous (subO1 a) := by
  unfold subO1
  continuity

lemma continuous_bsq : Continuous (bsq : ℂ × ℂ → ℂ) := by
  unfold bsq
  continuity

lemma subO1_eq_add (a : ℝ) (Q : ℂ × ℂ) : subO1 a Q = Q + subO1 a 0 := by
  ext <;> simp [subO1]

lemma norm_brho_eq (P : ℂ × ℂ) : ‖brho P‖ = Real.sqrt ‖bsq P‖ := by
  have h : ‖brho P‖ ^ 2 = ‖bsq P‖ := by
    rw [← norm_pow, brho_sq]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- `bsq (subO1 a ·)` is nonvanishing on a neighbourhood of a regular point. -/
lemma eventually_bsq_ne {a : ℝ} {S : ℂ × ℂ} {P : ℕ → ℂ × ℂ}
    (hS : bsq (subO1 a S) ≠ 0) (hP : Tendsto P atTop (nhds S)) :
    ∀ᶠ k in atTop, bsq (subO1 a (P k)) ≠ 0 := by
  have hcont : Tendsto (fun k => bsq (subO1 a (P k))) atTop (nhds (bsq (subO1 a S))) :=
    ((continuous_bsq.tendsto (subO1 a S)).comp ((continuous_subO1 a).tendsto S)).comp hP
  have hball : Metric.ball (bsq (subO1 a S)) ‖bsq (subO1 a S)‖ ∈ nhds (bsq (subO1 a S)) :=
    Metric.ball_mem_nhds _ (norm_pos_iff.mpr hS)
  filter_upwards [hcont.eventually_mem hball] with k hk
  intro hzero
  rw [Metric.mem_ball, hzero, dist_comm, dist_zero_right] at hk
  exact lt_irrefl _ hk

/-- **Boundedness of the labelled backward state along a converging sequence.**
The only use of the nonvanishing hypothesis. -/
lemma eventually_state_bdd {a : ℝ} {S : ℂ × ℂ} {P : ℕ → ℂ × ℂ}
    (hS : bsq (subO1 a S) ≠ 0) (hP : Tendsto P atTop (nhds S)) :
    ∃ B : ℝ, ∀ᶠ k in atTop,
      ‖((F a (P k), brho (subO1 a (P k))) : (ℂ × ℂ) × ℂ)‖ ≤ B := by
  set c : ℝ := ‖bsq (subO1 a S)‖ / 2 with hcdef
  have hLpos : 0 < ‖bsq (subO1 a S)‖ := norm_pos_iff.mpr hS
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hcont : Tendsto (fun k => bsq (subO1 a (P k))) atTop (nhds (bsq (subO1 a S))) :=
    ((continuous_bsq.tendsto (subO1 a S)).comp ((continuous_subO1 a).tendsto S)).comp hP
  have hnorm : Tendsto (fun k => ‖bsq (subO1 a (P k))‖) atTop (nhds ‖bsq (subO1 a S)‖) :=
    hcont.norm
  have hlow : ∀ᶠ k in atTop, c ≤ ‖bsq (subO1 a (P k))‖ := by
    rcases (Metric.tendsto_atTop.mp hnorm) c hcpos with ⟨N, hN⟩
    rw [eventually_atTop]
    refine ⟨N, fun k hk => ?_⟩
    have h := hN k hk
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).1]
  have hup : ∀ᶠ k in atTop, ‖bsq (subO1 a (P k))‖ ≤ ‖bsq (subO1 a S)‖ + 1 := by
    rcases (Metric.tendsto_atTop.mp hnorm) 1 (by norm_num) with ⟨N, hN⟩
    rw [eventually_atTop]
    refine ⟨N, fun k hk => ?_⟩
    have h := hN k hk
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).2]
  have hPb : ∀ᶠ k in atTop, ‖P k‖ ≤ ‖S‖ + 1 := by
    rcases (Metric.tendsto_atTop.mp hP.norm) 1 (by norm_num) with ⟨N, hN⟩
    rw [eventually_atTop]
    refine ⟨N, fun k hk => ?_⟩
    have h := hN k hk
    rw [Real.dist_eq] at h
    linarith [(abs_lt.mp h).2]
  set D : ℝ := ‖S‖ + 1 + ‖subO1 a (0 : ℂ × ℂ)‖ with hDdef
  have hDnonneg : 0 ≤ D := by rw [hDdef]; positivity
  refine ⟨max (D / Real.sqrt c) (Real.sqrt (‖bsq (subO1 a S)‖ + 1)), ?_⟩
  filter_upwards [hlow, hup, hPb] with k hk1 hk2 hk3
  rw [Prod.norm_def]
  apply max_le
  · -- bound on `‖F a (P k)‖`
    have hρ : Real.sqrt c ≤ ‖brho (subO1 a (P k))‖ := by
      rw [norm_brho_eq]; exact Real.sqrt_le_sqrt hk1
    have hρpos : 0 < ‖brho (subO1 a (P k))‖ :=
      lt_of_lt_of_le (Real.sqrt_pos.mpr hcpos) hρ
    have hscpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
    have hw : ‖subO1 a (P k)‖ ≤ D := by
      rw [subO1_eq_add]
      calc ‖P k + subO1 a 0‖ ≤ ‖P k‖ + ‖subO1 a (0 : ℂ × ℂ)‖ := norm_add_le _ _
        _ ≤ D := by rw [hDdef]; linarith
    calc ‖F a (P k)‖ = ‖subO1 a (P k)‖ / ‖brho (subO1 a (P k))‖ := norm_F a (P k)
      _ ≤ D / Real.sqrt c := by
            rw [div_le_div_iff₀ hρpos hscpos]
            exact mul_le_mul hw hρ (Real.sqrt_nonneg c) hDnonneg
      _ ≤ max (D / Real.sqrt c) (Real.sqrt (‖bsq (subO1 a S)‖ + 1)) := le_max_left _ _
  · -- bound on `‖brho (subO1 a (P k))‖`
    rw [norm_brho_eq]
    exact le_trans (Real.sqrt_le_sqrt hk2) (le_max_right _ _)

/-! ### The main statement -/

theorem invBranch_cluster_subseq {a : ℝ} {S : ℂ × ℂ} {P : ℕ → ℂ × ℂ} {t : ℕ → Bool}
    (hS : Work.EQ.bsq (Work.EQ.subO1 a S) ≠ 0) (hP : Filter.Tendsto P Filter.atTop (nhds S)) :
    ∃ t' : Bool, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Filter.Tendsto (fun k => Work.EQ.invBranch a (t (ψ k)) (P (ψ k))) Filter.atTop
        (nhds (Work.EQ.invBranch a t' S)) := by
  -- ### Step 1: some letter is taken on a subsequence
  obtain ⟨b, ψ₁, hψ₁mono, hψ₁const⟩ :
      ∃ b : Bool, ∃ ψ₁ : ℕ → ℕ, StrictMono ψ₁ ∧ ∀ k, t (ψ₁ k) = b := by
    rcases Classical.em (∃ᶠ k in atTop, t k = true) with hf | hf
    · obtain ⟨φ, hφ, hφp⟩ := extraction_of_frequently_atTop hf
      exact ⟨true, φ, hφ, hφp⟩
    · have hnf : ∀ᶠ k in atTop, t k = false := by
        rw [not_frequently] at hf
        filter_upwards [hf] with k hk
        cases h : t k <;> simp_all
      obtain ⟨φ, hφ, hφp⟩ := extraction_of_frequently_atTop hnf.frequently
      exact ⟨false, φ, hφ, hφp⟩
  have hψ₁tend : Tendsto ψ₁ atTop atTop := hψ₁mono.tendsto_atTop
  -- ### Step 2: pass to a subsequence on which the labelled state converges
  have hPtend : Tendsto (fun k => P (ψ₁ k)) atTop (nhds S) := hP.comp hψ₁tend
  obtain ⟨B, hB⟩ := eventually_state_bdd (a := a) (S := S) (P := fun k => P (ψ₁ k)) hS hPtend
  have hfreq : ∃ᶠ k in atTop,
      (((F a (P (ψ₁ k)), brho (subO1 a (P (ψ₁ k))))) : (ℂ × ℂ) × ℂ) ∈
        Metric.closedBall 0 B :=
    (hB.mono (fun k hk => by rw [Metric.mem_closedBall, dist_zero_right]; exact hk)).frequently
  obtain ⟨w, -, ψ₀, hψ₀mono, htend⟩ := tendsto_subseq_of_frequently_bounded
      (x := fun k => (((F a (P (ψ₁ k)), brho (subO1 a (P (ψ₁ k))))) : (ℂ × ℂ) × ℂ))
      (Metric.isBounded_closedBall (x := (0 : (ℂ × ℂ) × ℂ)) (r := B)) hfreq
  obtain ⟨v, ζ'⟩ := w
  have hψmono : StrictMono (ψ₁ ∘ ψ₀) := hψ₁mono.comp hψ₀mono
  have hψtend : Tendsto (ψ₁ ∘ ψ₀) atTop atTop := hψmono.tendsto_atTop
  have hPtend2 : Tendsto (fun k => P (ψ₁ (ψ₀ k))) atTop (nhds S) := hP.comp hψtend
  -- components of the limit
  have hF : Tendsto (fun k => F a (P (ψ₁ (ψ₀ k)))) atTop (nhds v) :=
    (continuous_fst.tendsto (v, ζ')).comp htend
  have hζ : Tendsto (fun k => brho (subO1 a (P (ψ₁ (ψ₀ k))))) atTop (nhds ζ') :=
    (continuous_snd.tendsto (v, ζ')).comp htend
  -- ### Step 3: identify the limit
  have hbsqT : Tendsto (fun k => bsq (subO1 a (P (ψ₁ (ψ₀ k))))) atTop
      (nhds (bsq (subO1 a S))) :=
    ((continuous_bsq.tendsto (subO1 a S)).comp ((continuous_subO1 a).tendsto S)).comp hPtend2
  have hζsq : ζ' * ζ' = bsq (subO1 a S) := by
    have h1 : Tendsto
        (fun k => brho (subO1 a (P (ψ₁ (ψ₀ k)))) * brho (subO1 a (P (ψ₁ (ψ₀ k)))))
        atTop (nhds (ζ' * ζ')) := hζ.mul hζ
    refine tendsto_nhds_unique ?_ hbsqT
    refine h1.congr' (Eventually.of_forall (fun k => ?_))
    rw [← pow_two, brho_sq]
  have hSbrho : brho (subO1 a S) ≠ 0 := brho_ne_zero hS
  have hζ'mem : ζ' = brho (subO1 a S) ∨ ζ' = -brho (subO1 a S) := by
    have h : ζ' * ζ' = brho (subO1 a S) * brho (subO1 a S) := by
      rw [hζsq, ← pow_two, brho_sq]
    exact mul_self_eq_mul_self_iff.mp h
  have hbrho_ne : ∀ᶠ k in atTop, brho (subO1 a (P (ψ₁ (ψ₀ k)))) ≠ 0 :=
    (hψtend.eventually (eventually_bsq_ne hS hP)).mono (fun k hk => brho_ne_zero hk)
  have hF1 : Tendsto (fun k => (F a (P (ψ₁ (ψ₀ k)))).1) atTop (nhds v.1) :=
    (continuous_fst.tendsto v).comp hF
  have hF2 : Tendsto (fun k => (F a (P (ψ₁ (ψ₀ k)))).2) atTop (nhds v.2) :=
    (continuous_snd.tendsto v).comp hF
  have hw1 : Tendsto (fun k => (subO1 a (P (ψ₁ (ψ₀ k)))).1) atTop (nhds (subO1 a S).1) :=
    ((continuous_fst.tendsto (subO1 a S)).comp ((continuous_subO1 a).tendsto S)).comp hPtend2
  have hw2 : Tendsto (fun k => (subO1 a (P (ψ₁ (ψ₀ k)))).2) atTop (nhds (subO1 a S).2) :=
    ((continuous_snd.tendsto (subO1 a S)).comp ((continuous_subO1 a).tendsto S)).comp hPtend2
  have hrel1 : v.1 * ζ' = (subO1 a S).1 := by
    have hL : Tendsto
        (fun k => (F a (P (ψ₁ (ψ₀ k)))).1 * brho (subO1 a (P (ψ₁ (ψ₀ k)))))
        atTop (nhds (v.1 * ζ')) := hF1.mul hζ
    refine tendsto_nhds_unique ?_ hw1
    exact hL.congr' (hbrho_ne.mono (fun k hk => F_mul_brho_fst hk))
  have hrel2 : v.2 * ζ' = (subO1 a S).2 := by
    have hL : Tendsto
        (fun k => (F a (P (ψ₁ (ψ₀ k)))).2 * brho (subO1 a (P (ψ₁ (ψ₀ k)))))
        atTop (nhds (v.2 * ζ')) := hF2.mul hζ
    refine tendsto_nhds_unique ?_ hw2
    exact hL.congr' (hbrho_ne.mono (fun k hk => F_mul_brho_snd hk))
  have hv_eq : v = F a S ∨ v = -F a S := by
    have hRS1 : (F a S).1 * brho (subO1 a S) = (subO1 a S).1 := F_mul_brho_fst hSbrho
    have hRS2 : (F a S).2 * brho (subO1 a S) = (subO1 a S).2 := F_mul_brho_snd hSbrho
    rcases hζ'mem with h | h
    · left
      ext
      · refine mul_right_cancel₀ hSbrho ?_
        rw [hRS1, ← h]; exact hrel1
      · refine mul_right_cancel₀ hSbrho ?_
        rw [hRS2, ← h]; exact hrel2
    · right
      ext
      · refine mul_right_cancel₀ hSbrho ?_
        have hv1 : v.1 * brho (subO1 a S) = -((subO1 a S).1) := by
          have hh := hrel1
          rw [h] at hh
          linear_combination -hh
        have key : (-F a S).1 * brho (subO1 a S) = -((subO1 a S).1) := by
          have h1 : (-F a S).1 = -(F a S).1 := rfl
          rw [h1, neg_mul, hRS1]
        rw [hv1, key]
      · refine mul_right_cancel₀ hSbrho ?_
        have hv2 : v.2 * brho (subO1 a S) = -((subO1 a S).2) := by
          have hh := hrel2
          rw [h] at hh
          linear_combination -hh
        have key : (-F a S).2 * brho (subO1 a S) = -((subO1 a S).2) := by
          have h2 : (-F a S).2 = -(F a S).2 := rfl
          rw [h2, neg_mul, hRS2]
        rw [hv2, key]
  -- ### Step 4: conclude
  have heq : (fun k => -P (ψ₁ (ψ₀ k)) + sgnC b • F a (P (ψ₁ (ψ₀ k)))) =ᶠ[atTop]
      (fun k => invBranch a (t (ψ₁ (ψ₀ k))) (P (ψ₁ (ψ₀ k)))) := by
    filter_upwards with k
    rw [hψ₁const (ψ₀ k), invBranch_eq_sgnC_smul]
  have hconv : Tendsto (fun k => -P (ψ₁ (ψ₀ k)) + sgnC b • F a (P (ψ₁ (ψ₀ k)))) atTop
      (nhds (-S + sgnC b • v)) := by
    exact hPtend2.neg.add (hF.const_smul (sgnC b))
  rcases hv_eq with hv1 | hv1
  · refine ⟨b, ψ₁ ∘ ψ₀, hψmono, ?_⟩
    have hconv' : Tendsto (fun k => -P (ψ₁ (ψ₀ k)) + sgnC b • F a (P (ψ₁ (ψ₀ k)))) atTop
        (nhds (-S + sgnC b • F a S)) := by
      rw [hv1] at hconv
      exact hconv
    rw [invBranch_eq_sgnC_smul a b S]
    simpa only [Function.comp_apply] using hconv'.congr' heq
  · refine ⟨!b, ψ₁ ∘ ψ₀, hψmono, ?_⟩
    have hkey : -S + sgnC b • (-F a S) = invBranch a (!b) S := by
      rw [invBranch_eq_sgnC_smul, sgnC_not]
      simp only [smul_neg, neg_smul]
    have hconv' : Tendsto (fun k => -P (ψ₁ (ψ₀ k)) + sgnC b • F a (P (ψ₁ (ψ₀ k)))) atTop
        (nhds (-S + sgnC b • (-F a S))) := by
      rw [hv1] at hconv
      exact hconv
    rw [hkey] at hconv'
    simpa only [Function.comp_apply] using hconv'.congr' heq

end

end Work.EQ.Junc
