import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_XiAux
import Submission.Work.LinnikAreas.P3Rect.Work_ZeroFreeTables_P3_CompletedDerivPF
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_xiE_goodRadius
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_xiE_annulusBound
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_ownRepelNW_xiE_cofactor_logbound

namespace Work.LinnikAreas.DhExplicit


open scoped Classical BigOperators
open Filter Metric
open Work.LinnikAreas.DhK

set_option maxHeartbeats 0

lemma xiE_truncBound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ A₁ : ℝ, ∀ A : ℝ, A₁ ≤ A → ∀ T : ℝ, A ≤ T → T ≤ 2 * A →
      (∀ u : ℂ, Xi u = 0 → (xiL A) ^ 2 * |‖u‖ - T| ≥ 1) →
      ∀ s : ℂ, Xi s ≠ 0 → 8 * ‖s‖ ≤ T →
        ‖iteratedDeriv k (fun z => deriv Xi z / Xi z) s
            - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
              (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u : ℤ) : ℂ) *
                (1 / (s - u)) ^ (k + 1))‖
          ≤ C * (xiL A) ^ 2 / A * (1 + ‖s‖) := by
  classical
  obtain ⟨zc, hzcnn, hzc⟩ := Xi_zeroCount_L
  obtain ⟨gc, hgcnn, hgc⟩ := Xi_growth_L
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Xi_zero_ge_delta
  let K0 : ℝ := 4 * gc + 20 * zc + |Real.log ‖Xi 0‖| + 1
  have hK0nn : 0 ≤ K0 := by
    dsimp [K0]
    nlinarith [hzcnn, hgcnn, abs_nonneg (Real.log ‖Xi 0‖)]
  have hK0one : 1 ≤ K0 := by
    dsimp [K0]
    nlinarith [hzcnn, hgcnn, abs_nonneg (Real.log ‖Xi 0‖)]
  let C : ℝ := (k.factorial : ℝ) * 192 * 16 ^ k * K0 * 2
  have hCnn : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hCnn, max (Real.exp |Real.log δ₀|) 2, ?_⟩
  intro A hA T hAT hT2A hmargin s hXis hsT
  have hA2 : 2 ≤ A := le_trans (le_max_right _ _) hA
  have hA1 : 1 ≤ A := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hApos : 0 < A := by linarith
  have hAexp : Real.exp |Real.log δ₀| ≤ A := le_trans (le_max_left _ _) hA
  have hTpos : 0 < T := by linarith
  have hT2 : 2 ≤ T := by linarith
  have hLgeD : |Real.log δ₀| ≤ xiL A := by
    have h1 : |Real.log δ₀| ≤ Real.log A := by
      have h := Real.log_le_log (Real.exp_pos _) hAexp
      rwa [Real.log_exp] at h
    have h2 : Real.log A ≤ xiL A := by
      dsimp [xiL]
      have h3 : Real.log A ≤ Real.log (A + 2) := Real.log_le_log (by linarith) (by linarith)
      linarith
    linarith
  obtain ⟨g, M0, hM0nn, hg_an_T, hg_nz_T, hfac_T, hfacs, hball, horigin, hM0le⟩ :=
    Work.LinnikAreas.ownRepelNW.xiE_cofactor_logbound hA0 hA1 hTpos hT2 hT2A hmargin zc gc hzcnn hgcnn hzc hgc
      δ₀ hδ₀pos hLgeD hδ₀
  obtain ⟨ε, hε, hg_an_ε, hfac_ε⟩ := hfacs
  have hs_ball : s ∈ Metric.ball (0 : ℂ) (T + ε) := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h8 : ‖s‖ ≤ T / 8 := by linarith
    linarith
  have hdec := Work.ZeroFreeTables.P3.iteratedDeriv_logDeriv_decompose (f := Xi) (g := g)
    (R := T) (ε := ε) Xi_differentiable hfac_ε hg_an_ε hs_ball hXis k
  have hgd := Work.ZeroFreeTables.P3.cofactorIteratedDeriv_le hTpos k hk hg_an_T hg_nz_T
    hM0nn hball horigin hsT
  rw [← Work.ZeroFreeTables.P3.logDeriv_eq_div Xi]
  have hgoal_eq : iteratedDeriv k (logDeriv Xi) s
      - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall (0:ℂ) T)) u : ℤ) : ℂ)
          * (1 / (s - u)) ^ (k + 1))
      = iteratedDeriv k (logDeriv g) s := by
    rw [hdec]; ring
  rw [hgoal_eq]
  have hm0 : max M0 1 ≤ K0 * (A * (xiL A) ^ 2 + 1) := by
    have h1 : M0 ≤ (4 * gc + 20 * zc + |Real.log ‖Xi 0‖| + 1)
        * (A * (xiL A) ^ 2 + 1) := by
      simpa [K0] using hM0le
    have h2 : (4 * gc + 20 * zc + |Real.log ‖Xi 0‖| + 1) * (A * (xiL A) ^ 2 + 1)
        ≤ K0 * (A * (xiL A) ^ 2 + 1) := le_of_eq rfl
    have h3 : 1 ≤ K0 * (A * (xiL A) ^ 2 + 1) := by
      have h4 : 1 ≤ A * (xiL A) ^ 2 + 1 := by
        have h5 : 0 ≤ (xiL A) ^ 2 := sq_nonneg _
        nlinarith
      nlinarith [hK0one, h4, hK0nn]
    exact max_le (le_trans h1 h2) h3
  have hTpow : A * A ^ k ≤ T ^ (k + 1) := by
    have hAk : A ^ k ≤ T ^ k := pow_le_pow_left₀ hA0 hAT k
    have h1 : A * A ^ k ≤ A * T ^ k := mul_le_mul_of_nonneg_left hAk hA0
    have h2 : A * T ^ k ≤ T * T ^ k :=
      mul_le_mul_of_nonneg_right hAT (pow_nonneg (by linarith : (0:ℝ) ≤ T) k)
    have h3 : T * T ^ k = T ^ (k + 1) := by rw [pow_succ]; ring
    linarith
  have hden1 : (0:ℝ) < T ^ (k + 1) := pow_pos hTpos _
  have hden2 : (0:ℝ) < A * A ^ k := mul_pos hApos (pow_pos hApos k)
  have hAL2 : 1 ≤ (xiL A) ^ 2 := by
    have h := xiL_ge_two hA0
    nlinarith
  have hAkge : A ≤ A ^ k := by
    calc A = A ^ 1 := (pow_one A).symm
      _ ≤ A ^ k := pow_le_pow_right₀ hA1 hk
  have hkey : max M0 1 / T ^ (k + 1) ≤ 2 * K0 * (xiL A) ^ 2 / A := by
    have s1 : max M0 1 / T ^ (k + 1) ≤ max M0 1 / (A * A ^ k) :=
      div_le_div_of_nonneg_left (by positivity) hden2 hTpow
    have s2 : max M0 1 / (A * A ^ k) ≤ K0 * (A * (xiL A) ^ 2 + 1) / (A * A ^ k) :=
      div_le_div_of_nonneg_right hm0 (le_of_lt hden2)
    have s3 : K0 * (A * (xiL A) ^ 2 + 1) / (A * A ^ k)
        ≤ K0 * (2 * (xiL A) ^ 2 * A) / (A * A ^ k) := by
      have hnum : A * (xiL A) ^ 2 + 1 ≤ 2 * (xiL A) ^ 2 * A := by nlinarith [hAL2, hA1]
      have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hK0nn) (le_of_lt hden2)
      simpa [mul_assoc] using this
    have s4 : K0 * (2 * (xiL A) ^ 2 * A) / (A * A ^ k) = 2 * K0 * (xiL A) ^ 2 / A ^ k := by
      rw [div_eq_div_iff (ne_of_gt hden2) (ne_of_gt (pow_pos hApos k))]
      ring
    have s5 : 2 * K0 * (xiL A) ^ 2 / A ^ k ≤ 2 * K0 * (xiL A) ^ 2 / A := by
      have hnum2 : 0 ≤ 2 * K0 * (xiL A) ^ 2 := by positivity
      exact div_le_div_of_nonneg_left hnum2 hApos hAkge
    linarith [s1, s2, s3, s4.le, s4.ge, s5]
  have hCeq : C = (k.factorial : ℝ) * 192 * 16 ^ k * K0 * 2 := rfl
  have hstep : (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k + 1)
      ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (xiL A) ^ 2 / A) := by
    have hfac : 0 ≤ (k.factorial : ℝ) * 192 * 16 ^ k := by positivity
    calc (k.factorial : ℝ) * 192 * 16 ^ k * max M0 1 / T ^ (k + 1)
        = (k.factorial : ℝ) * 192 * 16 ^ k * (max M0 1 / T ^ (k + 1)) := by ring
      _ ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (xiL A) ^ 2 / A) :=
          mul_le_mul_of_nonneg_left hkey hfac
  refine le_trans hgd ?_
  refine le_trans hstep ?_
  rw [hCeq]
  have hpos : 1 ≤ 1 + ‖s‖ := by have := norm_nonneg s; linarith
  have hL2n : 0 ≤ (xiL A) ^ 2 := sq_nonneg _
  have hAinv : 0 ≤ (xiL A) ^ 2 / A := div_nonneg hL2n hA0
  have hbase : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (xiL A) ^ 2 / A)
      ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((xiL A) ^ 2 / A * (1 + ‖s‖)) := by
    have hfac2 : 0 ≤ (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) := by positivity
    have he : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0 * (xiL A) ^ 2 / A)
        = (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((xiL A) ^ 2 / A) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hAinv hpos) hfac2
  refine le_trans hbase ?_
  have heq2 : (k.factorial : ℝ) * 192 * 16 ^ k * (2 * K0) * ((xiL A) ^ 2 / A * (1 + ‖s‖))
      = C * (xiL A) ^ 2 / A * (1 + ‖s‖) := by
    rw [hCeq]; ring
  rw [heq2]


/-- The `k`-th derivative partial-fraction ("Mittag-Leffler") identity for the entire Riemann
completion `Ξ(s) = 1/2 + (1/2) s (s-1) Λ₀(s)` of the zeta function: for every `s` with `Ξ s ≠ 0`,
the closed-ball divisor sums `(-1)^k k! Σᶠ_{‖u‖≤R} ord_Ξ(u)·(1/(s-u))^{k+1}` converge, as `R → ∞`,
to `(Ξ'/Ξ)^{(k)}(s)`.

PROOF ROUTE (all ingredients exist in the workspace):
(i) cofactor for `Ξ`: adapt `Commons.NumberTheory.Linnik.pf_cofactor_logbound` (proved, for the
completed `L`-function; readable template) or `Commons.NumberTheory.Zeta.XiPF.xi_cofactor_bound`
(proved, for `XiPF.xiF`, which is definitionally the same function as `Work.LinnikAreas.DhK.Xi`)
to the statement of `DhK/_ScratchD.xiE_cofactor_logbound_s`, using the three inputs
`Xi_growth_L`, `Xi_zeroCount_L`, `Xi_zero_ge_delta` of `DhK.XiAux` (all proved).
(ii) a good radius: `Work.LinnikAreas.FarRepel.xiE_goodRadius` (proved).
(iii) the annulus bound: `Work.LinnikAreas.FarRepel.xiE_annulusBound` (proved).
(iv) the cofactor decomposition `Work.ZeroFreeTables.P3.iteratedDeriv_logDeriv_decompose`,
the cofactor derivative bound `Work.ZeroFreeTables.P3.cofactorIteratedDeriv_le`, the difference
lemma `Work.ZeroFreeTables.P3.finsum_divisor_diff_eq`.
(v) assemble exactly as in `DhK/xiDerivPF_new.lean` (whose proof is complete modulo (i)-(iii);
that file does not build only because its three imports were moved/renamed).
Do NOT import `Commons.NumberTheory.Zeta.xiE_partialFraction_eq`,
`Commons.NumberTheory.Linnik.completedL_pf_identity_rect` or anything importing them: they
declare `Commons.NumberTheory.Linnik.pfP`, which clashes with
`Commons.NumberTheory.Linnik.logDeriv_pf_identity` (imported, via `P3.CompletedDerivPF`). -/
theorem xiDerivPFBall (k : ℕ) (hk : 1 ≤ k) :
    ∀ s : ℂ, Work.LinnikAreas.DhK.Xi s ≠ 0 →
      Filter.Tendsto (fun R : ℝ => ((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 R)) u : ℤ) : ℂ) *
            (1 / (s - u)) ^ (k + 1)))
        Filter.atTop (nhds (iteratedDeriv k (fun z => deriv Work.LinnikAreas.DhK.Xi z / Work.LinnikAreas.DhK.Xi z) s)) := by
  classical
  intro s hXis
  obtain ⟨Ag, hAgpos, hgood⟩ := Work.LinnikAreas.FarRepel.xiE_goodRadius
  obtain ⟨C2, hC2nn, A2, hbound2⟩ := xiE_truncBound k hk
  obtain ⟨CB, hCBnn, hann⟩ := Work.LinnikAreas.FarRepel.xiE_annulusBound k hk
  set eR : ℝ → ℝ := fun R => (k.factorial : ℝ) * (CB * xiL R / R)
      + C2 * (xiL R) ^ 2 / R * (1 + ‖s‖) with heRdef
  have hterm1 : Filter.Tendsto (fun R : ℝ => (k.factorial : ℝ) * (CB * xiL R / R))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => ((k.factorial : ℝ) * CB) * (xiL R / R))
        Filter.atTop (nhds 0) := by
      simpa using xiL_div_self_tendsto_zero.const_mul ((k.factorial : ℝ) * CB)
    refine h.congr' ?_
    filter_upwards with R
    ring
  have hterm2 : Filter.Tendsto (fun R : ℝ => C2 * (xiL R) ^ 2 / R * (1 + ‖s‖))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => (C2 * (1 + ‖s‖)) * ((xiL R) ^ 2 / R))
        Filter.atTop (nhds 0) := by
      simpa using xiL_sq_div_self_tendsto_zero.const_mul (C2 * (1 + ‖s‖))
    refine h.congr' ?_
    filter_upwards with R
    ring
  have heR0 : Filter.Tendsto eR Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun R : ℝ => (k.factorial : ℝ) * (CB * xiL R / R)
        + C2 * (xiL R) ^ 2 / R * (1 + ‖s‖)) Filter.atTop (nhds 0) := by
      simpa using hterm1.add hterm2
    refine h.congr' ?_
    filter_upwards with R
    simp only [heRdef]
  have hev : ∀ᶠ R : ℝ in Filter.atTop,
      ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        - iteratedDeriv k (fun z => deriv Xi z / Xi z) s‖ ≤ eR R := by
    filter_upwards [Filter.eventually_ge_atTop (max (max Ag A2) (max 2 (8 * ‖s‖ + 1)))]
      with R hR
    have hRAg : Ag ≤ R := le_trans (le_trans (le_max_left Ag A2) (le_max_left _ _)) hR
    have hRA2 : A2 ≤ R := le_trans (le_trans (le_max_right Ag A2) (le_max_left _ _)) hR
    have hR2 : 2 ≤ R := le_trans (le_trans (le_max_left 2 (8 * ‖s‖ + 1)) (le_max_right _ _)) hR
    have hRs : 8 * ‖s‖ + 1 ≤ R :=
      le_trans (le_trans (le_max_right 2 (8 * ‖s‖ + 1)) (le_max_right _ _)) hR
    have hsR : 8 * ‖s‖ ≤ R := by linarith
    obtain ⟨T, hRT, hT2R, hmargin⟩ := hgood R hRAg
    have hTR : 8 * ‖s‖ ≤ T := by linarith
    have hb2 := hbound2 R hRA2 T hRT hT2R hmargin s hXis hTR
    set SR : ℂ := ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 R)) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1) with hSR
    set ST : ℂ := ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u : ℤ) : ℂ)
        * (1 / (s - u)) ^ (k + 1) with hST
    set V : ℂ := iteratedDeriv k (fun z => deriv Xi z / Xi z) s with hV
    have hb2' : ‖V - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST‖
        ≤ C2 * (xiL R) ^ 2 / R * (1 + ‖s‖) := by
      simpa only [hST, hV] using hb2
    have hann' : ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u
          - MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u : ℤ)) : ℂ)
          * (1 / (s - u)) ^ (k + 1)‖ ≤ CB * xiL R / R := hann s R T hR2 hRT hsR
    have hnormident : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
        (∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u
            - MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u : ℤ)) : ℂ)
          * (1 / (s - u)) ^ (k + 1))‖ ≤ (k.factorial : ℝ) * (CB * xiL R / R) := by
      rw [norm_mul]
      have hnorm : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ))‖ = (k.factorial : ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
        simp
      rw [hnorm]
      exact mul_le_mul_of_nonneg_left hann' (by positivity)
    have hsumdiff : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 R)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        - (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u : ℤ) : ℂ)
            * (1 / (s - u)) ^ (k + 1))
        = -(∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u
            - MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u : ℤ)) : ℂ)
            * (1 / (s - u)) ^ (k + 1)) := by
      rw [← neg_sub, Work.ZeroFreeTables.P3.finsum_divisor_diff_eq Xi_meromorphicOn hRT s k]
    have hfirst : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
        - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST‖
        ≤ (k.factorial : ℝ) * (CB * xiL R / R) := by
      have hid : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
          - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST
          = -(((-1 : ℂ) ^ k * (k.factorial : ℂ)) *
              (∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Xi (Metric.closedBall 0 T)) u
                  - MeromorphicOn.divisor Xi (Metric.closedBall 0 R) u : ℤ)) : ℂ)
                * (1 / (s - u)) ^ (k + 1))) := by
        rw [← mul_sub, hSR, hST, hsumdiff, mul_neg]
      rw [hid, norm_neg]
      exact hnormident
    have hsplit : ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR - V
        = (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * SR
            - ((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST)
          + (((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST - V) := by ring
    have hsecond : ‖((-1 : ℂ) ^ k * (k.factorial : ℂ)) * ST - V‖
        ≤ C2 * (xiL R) ^ 2 / R * (1 + ‖s‖) := by
      rw [norm_sub_rev]
      exact hb2'
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    simp only [heRdef]
    linarith [hfirst, hsecond]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun R => norm_nonneg _) hev heR0


end Work.LinnikAreas.DhExplicit
