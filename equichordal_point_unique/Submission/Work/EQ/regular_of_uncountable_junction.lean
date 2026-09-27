import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.exists_regular_of_family
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.ucj_defs
import Submission.Work.EQ.exists_accPt_of_subset_isOpen
import Submission.Work.EQ.ucj_exists_condensationPt
import Submission.Work.EQ.ucjChain_analytic
import Submission.Work.EQ.ucjChain_eqRelC

/-! Guidance from the project lead (the requester):

LEAD NOTE (re-dispatch): the statement is AMENDED with ε.length = N and s.length = N. The previous prover showed that without them the hypotheses depend only on λ^N·C, forcing λ^ℤ-invariance of the regular values, which is false; only k = 0 (N = s.length) is intended. With the lengths fixed, the depth-N junction equation IS the junction equation of the candidate-chain family (ψ₁ = z, ψ₂ = C/z); use the labelled backward-map pieces + identity theorem + exists_regular_of_family. See the workspace's proved LTBV.junction_regComp and h0rj_eqRelC_candChain_gen, which have the same length hypotheses.

ROUTE: read Submission/Work/EQ/DESIGN_LA.md (the lead's closing route for exists_compact_regular_cycle's limit_analysis; the fan-rigidity chain and la_witness route are retired).

# regular_of_uncountable_junction (2–3k)

**Claim.** Fix `N, ε, η, s` and `C ≠ 0`. If the junction set
`{w : bwdP s (fan ε w) = eqMirror (fan η (λᴺC/w))}` (both fan arguments `< δ₁`) is uncountable,
then some regular component has value `C`.

**Route.** No pieces and no labels.

1. **Remove degenerate points.** Take `δ₁ ≤` the radius of `bwdP_fan_degenerate_countable`.
   Remove its countable set, on which some prefix radicand vanishes. The junction points that
   remain are *genuine*: every `O₁`-radicand along the labelled segment is nonzero.
2. **Condensation point.** Map `w ↦ (w, labelled segment at w) ∈ ℂ × (ℂ²)^{N+1}`. The image is
   uncountable in a second-countable space, so it has a condensation point `(w₀, seg₀)` inside
   the image.
3. **The analytic sheet.** Let `g` be the analytic sheet through `seg₀`, built step by step from
   local square roots of the nonzero radicands. By separation of the two backward partners
   (`H0_invParam_ge_exists_invBranch`, `invBranch_true_ne_false`), labelled segments close to
   `seg₀` *are* `g`.
4. **Identity theorem.** So `g_N = U_C` at points accumulating at `w₀`, hence on a disc `D`.
5. **Apply `exists_regular_of_family`** on `D`:
   * `m(w)`: the forward fan `fan ε` (germ beyond `|ε|`), the middle `g`, and the backward
     `eqMirror (fan η …)` (`ugermC` beyond);
   * `u = id`, `v = C/w`;
   * `EqRelC` holds along `g` (the coefficients satisfy `t²R = 1`), and at the junction by (4);
   * `hsmall` holds at a large depth.

**Risk: low–medium.** This is exactly the shape of the proved `H0_junction_value_of_cluster` and
`junction_values_countable`. It is **not** "the hard core": the uncountability supplies the
accumulation that the single-sequence reflection lacked.

## Implementation notes (this file)

The "labelled backward-map pieces" are taken from `Submission.Work.EQ.bwdFanSheets`
(the locally analytic sheets `sheetU` of the labelled backward iterates) together with the
pointwise multiset identity `sheet_claim`; the identity theorem then produces the sheet that
realises the junction on a disc, and after that the chain `ucjChain`
(`Submission.Work.EQ.ucj_defs`), whose middle is the sheet, satisfies the hypotheses of
`exists_regular_of_family` (analyticity: `ucjChain_analytic`; the equichordal relation:
`ucjChain_eqRelC`).  The condensation point outside the countable degenerate locus is
`ucj_exists_condensationPt`.
-/

namespace Work.EQ

open Filter _root_.Topology

open scoped Topology

noncomputable section

lemma ucj_norm_ofReal_eqLam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eqLam_pos' ha0 ha1)]

lemma ucj_norm_pow_eqLam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) :
    ‖((eqLam a : ℝ) : ℂ) ^ n‖ = (eqLam a) ^ n := by
  rw [norm_pow, ucj_norm_ofReal_eqLam ha0 ha1]

lemma ucj_norm_zpow_eqLam {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℤ) :
    ‖((eqLam a : ℝ) : ℂ) ^ n‖ = (eqLam a) ^ n := by
  rw [norm_zpow, ucj_norm_ofReal_eqLam ha0 ha1]

/-- **An uncountable junction set is realised by a regular component.** If for fixed data
`N, ε, η, s` the junction set of the value `C ≠ 0` (both fan arguments in the analyticity
disc) is uncountable, then some regular component of `H0` has value `C`. Proof sketch: at a
genuine condensation point of the junction segments, the analytic sheet through it satisfies the
junction on a disc (identity theorem), and `exists_regular_of_family` applies. -/
theorem regular_of_uncountable_junction {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ (N : ℕ) (ε η s : List Bool) (C : ℂ), ε.length = N → s.length = N → C ≠ 0 →
      ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ₁ ∧ ‖((eqLam a : ℝ) : ℂ) ^ N * (C / w)‖ < δ₁ ∧
          bwdP a s (fan a h ε w) =
            eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / w)))}.Countable →
      ∃ T : Set ChainData, IsRegComp a h T C := by
  classical
  obtain ⟨Ke, Lam, Q, δf, hKe, hLam, hQ, hδf, hFG₀⟩ := fan_induction ha0 ha1 hh
  have hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v :=
    fun ε' v hv => hFG₀ ε' v (by rw [Metric.mem_ball, dist_zero_right]; exact hv)
  obtain ⟨ρg, hρg, hgan, hgc0, hgreg, hginj, hgd⟩ := germC_facts ha0 ha1 hh
  obtain ⟨δ₂, hδ₂, hdegc⟩ := bwdP_fan_degenerate_countable ha0 ha1 hh
  have hr : 0 < r := hh.1
  have hlam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  set Θ : ℝ := min (min δf ρg) δ₂ with hΘdef
  have hΘpos : 0 < Θ := lt_min (lt_min hδf hρg) hδ₂
  have hΘδf : Θ ≤ δf := le_trans (min_le_left _ _) (min_le_left _ _)
  have hΘρg : Θ ≤ ρg := le_trans (min_le_left _ _) (min_le_right _ _)
  have hΘδ₂ : Θ ≤ δ₂ := min_le_right _ _
  refine ⟨Θ / 2, by linarith, ?_⟩
  intro N ε η s C hε hs hC hunc
  set δ₁ : ℝ := Θ / 2 with hδ₁def
  have hδ₁pos : 0 < δ₁ := by rw [hδ₁def]; linarith
  have hδ₁δf : δ₁ < δf := by rw [hδ₁def]; linarith
  have hδ₁ρg : δ₁ < ρg := by rw [hδ₁def]; linarith
  have hδ₁δ₂ : δ₁ < δ₂ := by rw [hδ₁def]; linarith
  have hΘmin : Θ ≤ min δf ρg := le_min hΘδf hΘρg
  have hδ₁lt : δ₁ < min δf ρg := by rw [hδ₁def]; linarith
  -- the junction set of the hypothesis
  set S : Set ℂ := {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ₁ ∧
      ‖((eqLam a : ℝ) : ℂ) ^ N * (C / w)‖ < δ₁ ∧
      bwdP a s (fan a h ε w) =
        eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / w)))} with hSdef
  have huncS : ¬ S.Countable := hunc
  -- the degenerate locus up to depth `N`
  set D : Set ℂ := {w : ℂ | ‖w‖ < δ₂ ∧ ∃ σ : List Bool, σ.length ≤ N ∧
      bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0} with hDdef
  have hDc : D.Countable := hdegc ε N
  -- junction points off the degenerate locus and the origin
  set A : Set ℂ := S \ (D ∪ {0}) with hAdef
  have hAunc : ¬ A.Countable := by
    intro hAc
    refine huncS (Set.Countable.mono ?_ (hAc.union (hDc.union (Set.countable_singleton 0))))
    intro w hw
    by_cases h : w ∈ D ∪ {0}
    · exact Or.inr h
    · exact Or.inl ⟨hw, h⟩
  -- a condensation point of `A`, off the degenerate locus
  obtain ⟨x, hxD, hxcond⟩ : ∃ x : ℂ, x ∉ D ∪ {0} ∧
      ∀ U : Set ℂ, IsOpen U → x ∈ U → ¬ (A ∩ U).Countable :=
    ucj_exists_condensationPt (hDc.union (Set.countable_singleton 0)) hAunc
  have hx0 : x ≠ 0 := fun h0 => hxD (Or.inr (by simpa using h0))
  have hxDmem : x ∉ D := fun h => hxD (Or.inl h)
  have hxcl : x ∈ closure A := by
    rw [Metric.mem_closure_iff]
    intro e he
    by_contra hcon
    push Not at hcon
    refine hxcond (Metric.ball x e) Metric.isOpen_ball (Metric.mem_ball_self he)
      (Set.Countable.mono ?_ (Set.countable_empty))
    intro y hy
    exact absurd hy.2 (by
      rw [Metric.mem_ball]
      exact not_lt.mpr (by rw [dist_comm]; exact hcon y hy.1))
  have hxnorm_le : ‖x‖ ≤ δ₁ := by
    have hsub : A ⊆ Metric.closedBall (0 : ℂ) δ₁ := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      have hwS : w ∈ S := hw.1
      rw [hSdef] at hwS
      exact le_of_lt hwS.2.1
    have hmem := closure_minimal hsub Metric.isClosed_closedBall hxcl
    rwa [Metric.mem_closedBall, dist_zero_right] at hmem
  have hxlam_le : ‖((eqLam a : ℝ) : ℂ) ^ N * (C / x)‖ ≤ δ₁ := by
    by_contra hcon
    rw [not_le] at hcon
    have hopen : IsOpen {z : ℂ | δ₁ < ‖((eqLam a : ℝ) : ℂ) ^ N * (C / z)‖} := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      have hz0 : z ≠ 0 := by
        intro h0
        have hz' : δ₁ < ‖((eqLam a : ℝ) : ℂ) ^ N * (C / z)‖ := hz
        rw [h0, div_zero, mul_zero, norm_zero] at hz'
        exact absurd hz' (not_lt.mpr hδ₁pos.le)
      have hcont : ContinuousAt (fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ N * (C / w)) z :=
        ContinuousAt.const_mul (ContinuousAt.div continuousAt_const continuousAt_id hz0) _
      exact hcont.preimage_mem_nhds
        ((isOpen_lt continuous_const continuous_norm).mem_nhds (by simpa using hz))
    have hsub : A ∩ {z : ℂ | δ₁ < ‖((eqLam a : ℝ) : ℂ) ^ N * (C / z)‖} ⊆ (∅ : Set ℂ) := by
      intro y hy
      exfalso
      have hyS : y ∈ S := hy.1.1
      rw [hSdef] at hyS
      exact absurd hy.2 (not_lt.mpr (le_of_lt hyS.2.2.1))
    exact hxcond _ hopen hcon (Set.Countable.mono hsub Set.countable_empty)
  have hxδf : ‖x‖ < δf := lt_of_le_of_lt hxnorm_le (by rw [hδ₁def]; linarith)
  have hxρg : ‖x‖ < ρg := lt_of_le_of_lt hxnorm_le (by rw [hδ₁def]; linarith)
  have hxδ₂ : ‖x‖ < δ₂ := lt_of_le_of_lt hxnorm_le (by rw [hδ₁def]; linarith)
  have hxΛδf : ‖((eqLam a : ℝ) : ℂ) ^ N * (C / x)‖ < δf :=
    lt_of_le_of_lt hxlam_le (by rw [hδ₁def]; linarith)
  have hxΛρg : ‖((eqLam a : ℝ) : ℂ) ^ N * (C / x)‖ < ρg :=
    lt_of_le_of_lt hxlam_le (by rw [hδ₁def]; linarith)
  -- all the labelled radicands at `x` are non-zero
  have hxgen : ∀ σ : List Bool, σ.length ≤ N →
      bsq (subO1 a (bwdP a σ (fan a h ε x))) ≠ 0 := by
    intro σ hσ h0
    exact hxDmem ⟨hxδ₂, σ, hσ, h0⟩
  -- `sheet_claim` at the base point `x` and the word `ε`
  have hfanx : ∀ τ : List Bool, AnalyticAt ℂ (fan a h τ) x := fun τ => (hFG τ x hxδf).1
  obtain ⟨shA, shB, shC⟩ :=
    sheet_claim (a := a) (h := h) (ε := ε) (w₀ := x) (n := N) hfanx hxgen N (Nat.le_succ N)
  -- the word set of depth at most `N`
  set FN : Finset (List Bool) := (Finset.range (N + 1)).biUnion (fun k => (fanWords k).toFinset)
    with hFNdef
  have hFNmem : ∀ τ : List Bool, τ ∈ FN ↔ τ.length ≤ N := by
    intro τ
    rw [hFNdef, Finset.mem_biUnion]
    constructor
    · rintro ⟨k, hk, hmem⟩
      have hkle : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [List.mem_toFinset] at hmem
      rw [mem_fanWords] at hmem
      omega
    · intro hlen
      refine ⟨τ.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hlen), ?_⟩
      rw [List.mem_toFinset, mem_fanWords]
  -- the mirrored unstable fan as a function
  set Rf : ℂ → ℂ × ℂ := fun z => eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))
    with hRfdef
  have hRx : AnalyticAt ℂ Rf x := by
    have h1 : AnalyticAt ℂ (fun z : ℂ => ((eqLam a : ℝ) : ℂ) ^ N * (C / z)) x :=
      analyticAt_const.mul (AnalyticAt.div analyticAt_const analyticAt_id hx0)
    have h2 : AnalyticAt ℂ (fun z => fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z))) x :=
      AnalyticAt.comp (f := fun z : ℂ => ((eqLam a : ℝ) : ℂ) ^ N * (C / z))
        ((hFG η _ hxΛδf).1) h1
    exact AnalyticAt.comp (f := fun z => fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))
      (analyticAt_eqMirror _) h2
  -- the local conditions, as an eventually statement
  have hEv1 : ∀ᶠ z in 𝓝 x, z ≠ 0 := eventually_ne_nhds hx0
  have hEv2 : ∀ᶠ z in 𝓝 x, ‖z‖ < min δf ρg :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds
      (by simpa using (lt_of_le_of_lt hxnorm_le hδ₁lt))
  have hEv3 : ∀ᶠ z in 𝓝 x, ‖((eqLam a : ℝ) : ℂ) ^ N * (C / z)‖ < min δf ρg := by
    have hcont : ContinuousAt (fun w : ℂ => ((eqLam a : ℝ) : ℂ) ^ N * (C / w)) x :=
      ContinuousAt.const_mul (ContinuousAt.div continuousAt_const continuousAt_id hx0) _
    exact hcont.preimage_mem_nhds
      ((isOpen_lt continuous_norm continuous_const).mem_nhds
        (by simpa using (lt_of_le_of_lt hxlam_le hδ₁lt)))
  have hEv4 : ∀ᶠ z in 𝓝 x, ∀ τ ∈ FN, AnalyticAt ℂ (sheetU a h ε x τ) z := by
    rw [Finset.eventually_all]
    intro τ hτ
    exact (shA τ ((hFNmem τ).mp hτ)).eventually_analyticAt
  have hEv5 : ∀ᶠ z in 𝓝 x, ∀ τ ∈ FN, bsq (subO1 a (sheetU a h ε x τ z)) ≠ 0 := by
    rw [Finset.eventually_all]
    intro τ hτ
    have hτlen : τ.length ≤ N := (hFNmem τ).mp hτ
    have hsq := (shB τ (by simpa using hτlen)).2
    have hxne : bsq (subO1 a (sheetU a h ε x τ x)) ≠ 0 := by
      intro h0
      have h1 : (sheetS a h ε x τ x) ^ 2 = 0 := by rw [hsq.2 x, h0]
      exact hsq.1 (mul_self_eq_zero.mp (by simpa [pow_two] using h1))
    have hcont : ContinuousAt (fun z => bsq (subO1 a (sheetU a h ε x τ z))) x := by
      have h1 : ContinuousAt (fun z : ℂ => (sheetU a h ε x τ z).1) x :=
        (shA τ hτlen).continuousAt.fst
      have h2 : ContinuousAt (fun z : ℂ => (sheetU a h ε x τ z).2) x :=
        (shA τ hτlen).continuousAt.snd
      show ContinuousAt (fun z => ((sheetU a h ε x τ z).1 + (((a : ℝ) / 2 : ℝ) : ℂ)) ^ 2 +
        (sheetU a h ε x τ z).2 ^ 2) x
      exact ((h1.add continuousAt_const).pow 2).add (h2.pow 2)
    exact hcont.eventually_ne hxne
  have hEv6 : ∀ᶠ z in 𝓝 x, AnalyticAt ℂ Rf z := hRx.eventually_analyticAt
  have hall : ∀ᶠ z in 𝓝 x,
      z ≠ 0 ∧ ‖z‖ < min δf ρg ∧ ‖((eqLam a : ℝ) : ℂ) ^ N * (C / z)‖ < min δf ρg ∧
      (∀ τ ∈ FN, AnalyticAt ℂ (sheetU a h ε x τ) z) ∧
      (∀ τ ∈ FN, bsq (subO1 a (sheetU a h ε x τ z)) ≠ 0) ∧
      AnalyticAt ℂ Rf z := by
    refine (hEv1.and (hEv2.and (hEv3.and (hEv4.and (hEv5.and hEv6))))).mono ?_
    rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨ε₀, hε₀pos, hε₀sub⟩ := Metric.mem_nhds_iff.mp hall
  set W : Set ℂ := Metric.ball x ε₀ with hWdef
  have hWopen : IsOpen W := Metric.isOpen_ball
  have hxW : x ∈ W := Metric.mem_ball_self hε₀pos
  have hW0 : ∀ z ∈ W, z ≠ 0 := fun z hz => (hε₀sub hz).1
  have hWz : ∀ z ∈ W, ‖z‖ < min δf ρg := fun z hz => (hε₀sub hz).2.1
  have hWc : ∀ z ∈ W, ‖((eqLam a : ℝ) : ℂ) ^ N * (C / z)‖ < min δf ρg :=
    fun z hz => (hε₀sub hz).2.2.1
  have hWsh : ∀ z ∈ W, ∀ τ ∈ FN, AnalyticAt ℂ (sheetU a h ε x τ) z :=
    fun z hz τ hτ => (hε₀sub hz).2.2.2.1 τ hτ
  have hWnd : ∀ z ∈ W, ∀ τ ∈ FN, bsq (subO1 a (sheetU a h ε x τ z)) ≠ 0 :=
    fun z hz τ hτ => (hε₀sub hz).2.2.2.2.1 τ hτ
  have hWR : ∀ z ∈ W, AnalyticAt ℂ Rf z := fun z hz => (hε₀sub hz).2.2.2.2.2
  -- pigeonhole: some word of length `N` realises the junction on an uncountable set
  have hAuncW : ¬ (A ∩ W).Countable := hxcond W hWopen hxW
  have hmemSheet : ∀ w ∈ S, ∃ σ ∈ (fanWords N).toFinset,
      sheetU a h ε x σ w = bwdP a s (fan a h ε w) := by
    intro w hw
    have hperm := shC N le_rfl w
    have hs_mem : s ∈ fanWords N := mem_fanWords.mpr hs
    have h1 : bwdP a s (fan a h ε w) ∈ (fanWords N).map (fun σ => bwdP a σ (fan a h ε w)) :=
      List.mem_map.mpr ⟨s, hs_mem, rfl⟩
    obtain ⟨σ, hσ, hσeq⟩ := List.mem_map.mp (hperm.mem_iff.mpr h1)
    exact ⟨σ, List.mem_toFinset.mpr hσ, hσeq⟩
  have hcov : A ∩ W ⊆ ⋃ σ, ⋃ (_ : σ ∈ (fanWords N).toFinset),
      {w : ℂ | Rf w = sheetU a h ε x σ w} := by
    rintro w ⟨hwA, -⟩
    obtain ⟨σ, hσ, hσeq⟩ := hmemSheet w hwA.1
    refine Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨hσ, ?_⟩⟩
    have hwS : w ∈ S := hwA.1
    rw [hSdef] at hwS
    show Rf w = sheetU a h ε x σ w
    have h1 : Rf w = bwdP a s (fan a h ε w) := hwS.2.2.2.symm
    exact h1.trans hσeq.symm
  obtain ⟨σ, hσmem, hσunc⟩ : ∃ σ ∈ (fanWords N).toFinset,
      ¬ ({w : ℂ | Rf w = sheetU a h ε x σ w} ∩ (A ∩ W)).Countable := by
    by_contra hcon
    push Not at hcon
    refine hAuncW (Set.Countable.mono (s₂ := ⋃ σ, ⋃ (_ : σ ∈ (fanWords N).toFinset),
      ({w : ℂ | Rf w = sheetU a h ε x σ w} ∩ (A ∩ W))) ?_ ?_)
    · intro w hw
      obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp (hcov hw)
      obtain ⟨hσF, hσw⟩ := Set.mem_iUnion.mp hσ
      exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨hσF, hσw, hw⟩⟩
    · exact Set.Countable.biUnion (fanWords N).toFinset.finite_toSet.countable
        (fun σ hσ => hcon σ hσ)
  have hσlen : σ.length = N := mem_fanWords.mp (List.mem_toFinset.mp hσmem)
  -- an accumulation point of that set inside `W`
  obtain ⟨x', hx'W, hx'acc⟩ := exists_accPt_of_subset_isOpen hWopen
    (fun z hz => hz.2.2) hσunc
  -- the identity theorem
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.isOpen_iff.mp hWopen x' hx'W
  have hRana : AnalyticOnNhd ℂ Rf (Metric.ball x' ε₁) := fun z hz => hWR z (hε₁sub hz)
  have hGana : AnalyticOnNhd ℂ (sheetU a h ε x σ) (Metric.ball x' ε₁) :=
    fun z hz => hWsh z (hε₁sub hz) σ (by rw [hFNmem]; exact le_of_eq hσlen)
  have hEqOn : Set.EqOn Rf (sheetU a h ε x σ) (Metric.ball x' ε₁) := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hRana hGana
      Metric.isPreconnected_ball (Metric.mem_ball_self hε₁pos) ?_
    rw [frequently_nhdsWithin_iff]
    rw [accPt_iff_frequently] at hx'acc
    exact hx'acc.mono (fun y hy => ⟨hy.2.1, by simpa using hy.1⟩)
  -- the ball `U` on which the chain is built
  have hx'pos : 0 < ‖x'‖ := norm_pos_iff.mpr (hW0 x' hx'W)
  obtain ⟨ε₂, hε₂pos, hε₂le, hε₂sub⟩ :
      ∃ ε₂ > 0, ε₂ ≤ ‖x'‖ / 2 ∧ Metric.ball x' ε₂ ⊆ W ∩ Metric.ball x' ε₁ := by
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hWopen x' hx'W
    refine ⟨min (min r ε₁) (‖x'‖ / 2), lt_min (lt_min hr hε₁pos) (by linarith),
      min_le_right _ _, fun z hz => ⟨hrsub ?_, ?_⟩⟩
    · rw [Metric.mem_ball] at hz ⊢
      exact lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_left _ _))
    · rw [Metric.mem_ball] at hz ⊢
      exact lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_right _ _))
  set U : Set ℂ := Metric.ball x' ε₂ with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconn : IsConnected U := Metric.isConnected_ball hε₂pos
  have hUsubW : U ⊆ W := fun z hz => (hε₂sub hz).1
  have hUsubB : U ⊆ Metric.ball x' ε₁ := fun z hz => (hε₂sub hz).2
  have hU0 : ∀ z ∈ U, z ≠ 0 := fun z hz => hW0 z (hUsubW hz)
  have hUz : ∀ z ∈ U, ‖z‖ < min δf ρg := fun z hz => hWz z (hUsubW hz)
  have hUc : ∀ z ∈ U, ‖((eqLam a : ℝ) : ℂ) ^ N * (C / z)‖ < min δf ρg :=
    fun z hz => hWc z (hUsubW hz)
  -- the prescribed middle maps
  set g : ℕ → ℂ → ℂ × ℂ := fun k z => if k ≤ N then sheetU a h ε x (σ.take k) z
    else fan a h ε z with hgdef
  have hgtake : ∀ k : ℕ, k ≤ N → σ.take k ∈ FN := fun k hk =>
    (hFNmem _).mpr (by rw [List.length_take, hσlen]; exact min_le_right _ _)
  have hgAn : ∀ k ≤ N, AnalyticOnNhd ℂ (g k) U := by
    intro k hk
    have hgk : ∀ z : ℂ, g k z = sheetU a h ε x (σ.take k) z := by
      intro z
      show (if k ≤ N then sheetU a h ε x (σ.take k) z else fan a h ε z) = _
      rw [if_pos hk]
    refine fun z hz => (hWsh z (hUsubW hz) (σ.take k) (hgtake k hk)).congr
      (Filter.Eventually.of_forall (fun w => (hgk w).symm))
  have hg0 : ∀ z ∈ U, g 0 z = fan a h ε z := by
    intro z hz
    have hgk : g 0 z = sheetU a h ε x (σ.take 0) z := by
      show (if (0 : ℕ) ≤ N then sheetU a h ε x (σ.take 0) z else fan a h ε z) = _
      rw [if_pos (Nat.zero_le N)]
    rw [hgk, List.take_zero, sheetU_nil]
  have hgnd : ∀ k : ℕ, k < N → ∀ z ∈ U, bsq (subO1 a (g k z)) ≠ 0 := by
    intro k hk z hz
    have hgk : g k z = sheetU a h ε x (σ.take k) z := by
      show (if k ≤ N then sheetU a h ε x (σ.take k) z else fan a h ε z) = _
      rw [if_pos (le_of_lt hk)]
    rw [hgk]
    exact hWnd z (hUsubW hz) (σ.take k) (hgtake k (le_of_lt hk))
  have hgrec : ∀ k : ℕ, k < N → ∀ z ∈ U, EqRelC a (g (k+1) z) (g k z) := by
    intro k hk z hz
    have hgk : g k z = sheetU a h ε x (σ.take k) z := by
      show (if k ≤ N then sheetU a h ε x (σ.take k) z else fan a h ε z) = _
      rw [if_pos (le_of_lt hk)]
    have hgk1 : g (k+1) z = sheetU a h ε x (σ.take (k+1)) z := by
      show (if k + 1 ≤ N then sheetU a h ε x (σ.take (k+1)) z else fan a h ε z) = _
      rw [if_pos (by omega)]
    have hkN : k < σ.length := by rw [hσlen]; exact hk
    have htake : σ.take (k+1) = σ.take k ++ [σ[k]] := by
      rw [← List.take_concat_get' σ k hkN]
    have hroot := (shB (σ.take k) (by rw [List.length_take, hσlen]; exact min_le_min (le_of_lt hk) le_rfl)).2.2
    rw [hgk1, hgk, htake, sheetU_append]
    exact ucj_eqRelC_bchild (Q := sheetU a h ε x (σ.take k) z) (t := σ[k])
      (ρ := sheetS a h ε x (σ.take k) z) (hroot z)
      (hWnd z (hUsubW hz) (σ.take k) (hgtake k (le_of_lt hk)))
  have hgjunc : ∀ z ∈ U, g N z = Rf z := by
    intro z hz
    have hgk : g N z = sheetU a h ε x (σ.take N) z := by
      show (if N ≤ N then sheetU a h ε x (σ.take N) z else fan a h ε z) = _
      rw [if_pos le_rfl]
    rw [hgk, List.take_of_length_le (le_of_eq hσlen), ← hEqOn (hUsubB hz)]
  -- the depth at which the tails are principal and the family is small
  have hUboundz : ∀ z ∈ U, ‖z‖ ≤ ‖x'‖ + ε₂ := by
    intro z hz
    have hdist : dist z x' < ε₂ := Metric.mem_ball.mp hz
    calc ‖z‖ ≤ ‖z - x'‖ + ‖x'‖ := by
          have hz' : z = (z - x') + x' := by ring
          nth_rewrite 1 [hz']
          exact norm_add_le _ _
      _ ≤ ε₂ + ‖x'‖ := by
          have h2 : ‖z - x'‖ < ε₂ := by rwa [dist_eq_norm] at hdist
          linarith
      _ = ‖x'‖ + ε₂ := by ring
  have hUboundc : ∀ z ∈ U, ‖C / z‖ ≤ 2 * ‖C‖ / ‖x'‖ := by
    intro z hz
    have hdist : dist z x' < ε₂ := Metric.mem_ball.mp hz
    have hzlow : ‖x'‖ / 2 ≤ ‖z‖ := by
      have h2 : ‖z - x'‖ < ε₂ := by rwa [dist_eq_norm] at hdist
      have h1 : ‖x'‖ ≤ ‖x' - z‖ + ‖z‖ := by
        have hx' : x' = (x' - z) + z := by ring
        nth_rewrite 1 [hx']
        exact norm_add_le _ _
      rw [norm_sub_rev] at h1
      linarith
    rw [norm_div]
    have h2 : ‖C‖ / ‖z‖ ≤ ‖C‖ / (‖x'‖ / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg C) (by linarith) hzlow
    have h3 : ‖C‖ / (‖x'‖ / 2) = 2 * ‖C‖ / ‖x'‖ := by field_simp
    linarith
  set K : ℝ := max (‖x'‖ + ε₂) (2 * ‖C‖ / ‖x'‖) + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt_of_lt_one (show 0 < r / K by positivity) hlam1
  set M : ℕ := max M₀ (N + η.length + 1) with hMdef
  have hMge : N + η.length + 1 ≤ M := le_max_right _ _
  have hM0ge : M₀ ≤ M := le_max_left _ _
  have hpowM : (eqLam a) ^ M ≤ (eqLam a) ^ M₀ := pow_le_pow_of_le_one hlam0.le hlam1.le hM0ge
  have hsmall : ∀ z ∈ U, ‖((eqLam a : ℝ) : ℂ) ^ M * z‖ < r ∧
      ‖((eqLam a : ℝ) : ℂ) ^ M * (C / z)‖ < r := by
    intro z hz
    have hnorm : ‖((eqLam a : ℝ) : ℂ) ^ M‖ = (eqLam a) ^ M := ucj_norm_pow_eqLam ha0 ha1 M
    have h1 : ‖z‖ ≤ K := by
      rw [hKdef]
      linarith [hUboundz z hz, le_max_left (‖x'‖ + ε₂) (2 * ‖C‖ / ‖x'‖)]
    have h2 : ‖C / z‖ ≤ K := by
      rw [hKdef]
      linarith [hUboundc z hz, le_max_right (‖x'‖ + ε₂) (2 * ‖C‖ / ‖x'‖)]
    have hkey : (eqLam a) ^ M * K < r := by
      calc (eqLam a) ^ M * K ≤ (eqLam a) ^ M₀ * K := mul_le_mul_of_nonneg_right hpowM hKpos.le
        _ < (r / K) * K := mul_lt_mul_of_pos_right hM₀ hKpos
        _ = r := div_mul_cancel₀ r (ne_of_gt hKpos)
    constructor
    · rw [norm_mul, hnorm]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 (pow_pos hlam0 M).le) hkey
    · rw [norm_mul, hnorm]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h2 (pow_pos hlam0 M).le) hkey
  -- the tails
  have hs_tail : ∀ z ∈ U, ∀ n : ℕ, M ≤ n →
      (ucjChain a h ε η s N C g z).1 (n : ℤ) = germC a h ((eqLam a : ℂ) ^ n * z) := by
    intro z hz n hn
    have hnN : ¬ (n ≤ N) := by omega
    have htoNat : ((n : ℤ)).toNat = n := Int.toNat_natCast n
    rw [ucjChain_fst_apply, if_pos (Int.natCast_nonneg n), htoNat, if_neg hnN, zpow_natCast]
  have hus_tail : ∀ z ∈ U, ∀ n : ℕ, M ≤ n →
      (ucjChain a h ε η s N C g z).1 (-(n : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ n * (C / z)) := by
    intro z hz n hn
    have htoNat : (-(-(n : ℤ))).toNat = n := by rw [neg_neg, Int.toNat_natCast]
    have hnN : ¬ (n ≤ N) := by omega
    have hdrop : η.length ≤ n - N := by omega
    rw [ucjChain_fst_apply, if_neg (by omega : ¬ ((0 : ℤ) ≤ -(n : ℤ))), htoNat, if_neg hnN,
      List.drop_eq_nil_of_le hdrop, zpow_natCast]
    rfl
  -- the equichordal relation and the analyticity of the family
  have hreg' : ∀ u : ℂ, ‖u‖ < ρg → RegPair a (germC a h u) (germC a h ((eqLam a : ℂ) * u)) :=
    fun u hu => (hgreg u (by rw [Metric.mem_ball, dist_zero_right]; exact hu)).1
  have hrel : ∀ z ∈ U, ∀ n : ℤ, EqRelC a ((ucjChain a h ε η s N C g z).1 n)
      ((ucjChain a h ε η s N C g z).1 (n + 1)) :=
    ucjChain_eqRelC ha0 ha1 hh hFG hreg' hε hs hUz hUc hg0 hgnd hgrec hgjunc
  have hman : ∀ n : ℤ, AnalyticOnNhd ℂ (fun z => (ucjChain a h ε η s N C g z).1 n) U :=
    ucjChain_analytic ha0 ha1 hh hFG hgan hε hUopen hU0 hUz hUc hgAn
  -- two distinct points of `U`
  have hnc : ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ z₂ := by
    refine ⟨x', Metric.mem_ball_self hε₂pos, x' + ((ε₂ / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm,
        show x' + ((ε₂ / 2 : ℝ) : ℂ) - x' = ((ε₂ / 2 : ℝ) : ℂ) by rw [add_sub_cancel_left],
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ε₂ / 2)]
      linarith
    · intro hcon
      have h : ((ε₂ / 2 : ℝ) : ℂ) = 0 := by
        have h2 : x' + ((ε₂ / 2 : ℝ) : ℂ) - x' = 0 := by rw [← hcon, sub_self]
        simpa using h2
      have h3 := Complex.ofReal_injective h
      linarith
  obtain ⟨p, hp, hval⟩ := exists_regular_of_family ha0 ha1 hh hUopen hUconn
    (m := fun z n => (ucjChain a h ε η s N C g z).1 n) (u := fun z => z) (v := fun z => C / z)
    (c := C) hC hman analyticOnNhd_id hU0 (fun z hz => mul_div_cancel₀ C (hU0 z hz)) hnc
    hrel (N := M) hsmall hs_tail hus_tail
  exact ⟨connectedComponentIn (H0 a h) p, connectedComponentIn_subset (H0 a h) p,
    ⟨p, hp, rfl⟩, hval⟩
