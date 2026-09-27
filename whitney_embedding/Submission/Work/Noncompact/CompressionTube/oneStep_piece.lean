import Mathlib
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm
import Submission.Work.Noncompact.CompressionTube.germGlue
import Submission.Work.Noncompact.CompressionTube.smoothTransition_strictMonoOn
import Submission.Work.Noncompact.Routing.arcs_removal
import Submission.Work.Noncompact.Routing.twoRays_of_germedLine

/-!
# The piece step of the routing (geometric parameter)

One induction step of the line construction: inside an open preconnected corridor `C`, given the
preceding piece `P` (trace in `C`, ending at the junction `z = P 1` with a straight *arrival*-side
germ in a chart `c` centred at `z`), and a next junction `z' ∈ C` off the trace, produce the next
piece `X` from `z` to `z'`, `C^∞`, immersive everywhere, with image in `C`, with the prescribed
initial germ `c.symm (t • w)` and a straight terminal germ.

The parameter is the *geometric* one: `X s = c.symm (s • w)` on `[0, η]` and `X s = α (s - η)`
afterwards, so the endpoint is reached at `T = η + 1`.  Normalising to parameter `1` is a separate
reparametrisation step (`Work.Noncompact.CompressionTube.strictMonoOn_clamp`).

## Step 4 (this file, the current target): the ambient and the arc

With `η₁` from `forward_germ_avoids`, `η₂` from continuity at `0`, and

  `η := min (min η₁ η₂) (δ / (2 * ‖w‖)) / 4`,   `p := c.symm (η • w)`,   `T := η + 1`,

one must show: `η • w ∈ c.target` (needs `η ≤ δ/(2‖w‖)` — otherwise the chart-line part of the
splice is not known to lie in `c.target`, so neither `C^∞` nor the immersion at `s < η` is
available); `p ∈ C \ P '' Icc`; `p ≠ z'`; and the `immersedArcWithGerm` germ hypothesis at
`e₀ := min (η₁ - η) (η₂/2 - η)` — the germ points have chart parameter `η + t`, which must clear
*both* the `C`-membership bound (`η₂`, via `η ≤ η₂/2` so that `η + t < η₂` is *strict*) and the
trace-avoidance bound (`η₁`).  This bound, not `η₁ - η`, is the correct one.

Three Lean-level slips encountered when transcribing this:

* `ContinuousAt (⇑c.symm) ((0 : ℝ) • w)` mis-parses (`(0 : ℝ) • w` is read as the function
  `HSMul.hSMul 0`): ascribe the *model-space* zero, `ContinuousAt (⇑c.symm)
  (0 : EuclideanSpace ℝ (Fin n))`, and get the composite by `simpa using h2.comp h1`.
* the same mis-parsing bites an anonymous function inside `ContinuousAt`: writing
  `ContinuousAt (fun s : ℝ => c.symm (s • w)) 0` needs the lambda's type to be pinned down
  (e.g. `have h1 : ContinuousAt (fun s : ℝ => c.symm (s • w)) 0 := …` or obtain it with
  `fun_prop`), otherwise `h2.comp h1` is elaborated at the wrong point.
* the neighbourhood filter is `nhds`, not `Filter.nhds`; the ball extraction from a `nhds`
  membership on the *parameter* space ℝ must have the filter's type pinned by a named
  `have … : (fun s : ℝ => c.symm (s • w)) ⁻¹' C ∈ nhds (0:ℝ)` before `Metric.mem_nhds_iff.mp`;
* membership in the extracted ball is `s ∈ Metric.ball (0:ℝ) η₂`, so the rewrite chain is
  `rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]` — **not**
  `rw [dist_eq_norm, sub_zero, …]` (the goal is a `Metric.ball` membership, not a `dist`).
* for the `η`-estimates, avoid `set … with h` followed by `rw [h]`; keep the explicit term
  `min (min η₁ η₂) (δ / (2 * ‖w‖)) / 4` and derive `η ≤ η₁`, `η < η₁`, `η ≤ η₂ / 2`,
  `η ≤ δ / (2 * ‖w‖)` by `linarith` from `min_le_left`/`min_le_right` and the positivity of `η₁`,
  `η₂`, `δ/(2‖w‖)`.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology
open scoped Manifold ContDiff

noncomputable section

/-- (a) of the left-clamp sub-steps: the clamp `χ` of step 5 is bounded by `η` below `η`.
This is what makes the clamped chart line stay inside `c.target`. -/
theorem abs_chi_le {η : ℝ} (hη : 0 < η) :
    ∀ s : ℝ, s ≤ η → |s * Real.smoothTransition (1 + s / η)| ≤ η := by
  intro s hs
  by_cases hs0 : 0 ≤ s
  · have h1 : (1:ℝ) ≤ 1 + s / η := by
      have h2 : 0 ≤ s / η := div_nonneg hs0 hη.le
      linarith
    rw [Real.smoothTransition.one_of_one_le h1, mul_one, abs_of_nonneg hs0]
    exact hs
  · rw [not_le] at hs0
    by_cases hs1 : -η ≤ s
    · rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      have h2 : Real.smoothTransition (1 + s / η) ≤ 1 := Real.smoothTransition.le_one _
      have h3 : |s| ≤ η := by rw [abs_of_neg hs0]; linarith
      nlinarith [h2, Real.smoothTransition.nonneg (1 + s / η), abs_nonneg s]
    · rw [not_le] at hs1
      have h1 : 1 + s / η < 0 := by
        have h2 : (1:ℝ) + s / η = (η + s) / η := by field_simp
        rw [h2]
        exact div_neg_of_neg_of_pos (by linarith) hη
      rw [Real.smoothTransition.zero_of_nonpos h1.le, mul_zero, abs_zero]
      exact hη.le

/-- **The piece step.**  See the module docstring and `NOTES_S131_immersedLine_design.md` S131-5
for the five-step proof, every ingredient of which is already proved:

1. `forward_germ_avoids` (with the chart data of `P`) gives `η₁ > 0` with
   `c.symm (s • w) ∉ P '' Icc` for `0 < s ≤ η₁`;
2. continuity of `s ↦ c.symm (s • w)` at `0` and `z = P 1 ∈ C` give `η₂ > 0` with
   `c.symm (s • w) ∈ C` for `dist s 0 < η₂`; take `η` as above and `p := c.symm (η • w)`;
3. `C \ P '' Icc` is open (`hC.sdiff (isCompact_Icc.image hPc).isClosed`) and preconnected
   (`Work.Noncompact.Routing.isPreconnected_sdiff_image_arc`), and contains `p` and `z'`;
4. `Work.Noncompact.CompressionTube.immersedArcWithGerm` in that ambient from `p` to `z'`, with
   chart `c`, direction `w` and germ radius `min (η₁ - η) (η₂/2 - η)`, gives `α`;
5. `X s := if s ≤ η then c.symm (s • w) else α (s - η)` with `T := η + 1`: the splice is
   straight-through (`Work.Noncompact.CompressionTube.contMDiffAt_glue_same_germ`); on `s < η` the
   piece is a chart line (immersion by `isImmersion_chartLine`, smoothness because `s • w` lies in
   `c.target`), on `s > η` a translate of `α`
   (`Work.Noncompact.Routing.injective_mfderiv_reparam`); the remaining conjuncts follow from
   steps 1-4 with `T` in place of `1`. -/
theorem oneStep_piece_geometric {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {P : ℝ → M} (hPc : Continuous P) (hPinj : Set.InjOn P (Set.Icc (0:ℝ) 1))
    (hPmem : P '' Set.Icc (0:ℝ) 1 ⊆ C)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    (hcsrc : P 1 ∈ c.source) (hcz : c (P 1) = 0)
    {δ : ℝ} (hδpos : 0 < δ)
    (hδ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ ⊆ c.target)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) {e : ℝ} (he : 0 < e)
    (hger : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P t = c.symm ((t - 1) • w))
    {z' : M} (hz'C : z' ∈ C) (hz'P : z' ∉ P '' Set.Icc (0:ℝ) 1) (hz'ne : z' ≠ P 1)
    {η₁ : ℝ} (hη₁pos : 0 < η₁) (hη₁ : ∀ s : ℝ, 0 < s → s ≤ η₁ → c.symm (s • w) ∉ P '' Set.Icc (0:ℝ) 1)
    {η₂ : ℝ} (hη₂pos : 0 < η₂) (hη₂ : ∀ s : ℝ, s ∈ Metric.ball (0:ℝ) η₂ → c.symm (s • w) ∈ C)
    {η : ℝ} (hηpos : 0 < η) (hηlt₁ : η < η₁) (hηlt₂ : η < η₂ / 2)
    (hηltδ : η < δ / (2 * ‖w‖)) (hηz' : c.symm (η • w) ≠ z') :
    ∃ T : ℝ, 0 < T ∧ ∃ X : ℝ → M, X 0 = P 1 ∧ X T = z' ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder X ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) X t)) ∧
      X '' Set.Icc (0:ℝ) T ⊆ C ∧
      (X '' Set.Ioc (0:ℝ) T ∩ P '' Set.Icc (0:ℝ) 1 = ∅) ∧
      (∃ e' : ℝ, 0 < e' ∧ ∀ t : ℝ, 0 ≤ t → t ≤ e' → X t = c.symm (t • w)) ∧
      ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (w' : EuclideanSpace ℝ (Fin n)) (e' : ℝ), 0 < e' ∧ w' ≠ 0 ∧
        c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
          Work.Noncompact.CompressionTube.smoothOrder M ∧ z' ∈ c'.source ∧
        ∀ t : ℝ, T - e' ≤ t → t ≤ T → X t = c'.symm (c' z' + (t - T) • w') := by
  classical
  -- ## the access point and its basic properties (all by hypothesis)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have h0tgt : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target := by
    rw [← hcz]; exact c.map_source hcsrc
  have hηw_tgt : η • w ∈ c.target := by
    apply hδ
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hηpos]
    have h : η * ‖w‖ < δ / (2 * ‖w‖) * ‖w‖ :=
      mul_lt_mul_of_pos_right hηltδ hwpos
    have h2 : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 := by field_simp
    rw [h2] at h
    linarith
  set p : M := c.symm (η • w) with hpdef
  have hseg_mem : ∀ s : ℝ, 0 ≤ s → s ≤ η → c.symm (s • w) ∈ C := by
    intro s hs0 hsη
    apply hη₂
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]
    linarith
  have hseg_avoid : ∀ s : ℝ, 0 < s → s ≤ η → c.symm (s • w) ∉ P '' Set.Icc (0:ℝ) 1 :=
    fun s hs0 hsη => hη₁ s hs0 (le_trans hsη hηlt₁.le)
  have hpV : p ∈ C \ P '' Set.Icc (0:ℝ) 1 :=
    ⟨hseg_mem η hηpos.le le_rfl, hseg_avoid η hηpos le_rfl⟩
  have hz'V : z' ∈ C \ P '' Set.Icc (0:ℝ) 1 := ⟨hz'C, hz'P⟩
  have hpsrc : p ∈ c.source := by rw [hpdef]; exact c.map_target hηw_tgt
  have hpne : p ≠ z' := by rw [hpdef]; exact hηz'
  -- ## step 3: the ambient is open and preconnected
  have hVopen : IsOpen (C \ P '' Set.Icc (0:ℝ) 1) :=
    hC.sdiff (isCompact_Icc.image hPc).isClosed
  have hVpc : IsPreconnected (C \ P '' Set.Icc (0:ℝ) 1) :=
    Work.Noncompact.Routing.isPreconnected_sdiff_image_arc hn hC hCc hPc hPinj
      (fun t ht => hPmem ⟨t, ht, rfl⟩)
  -- ## step 4: the germ hypothesis, at `min (η₁ - η) (η₂/2 - η)`
  have hgermV : ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ t : ℝ, 0 < t → t ≤ e₀ →
      c.symm (c p + t • w) ∈ C \ P '' Set.Icc (0:ℝ) 1 := by
    refine ⟨min (η₁ - η) (η₂ / 2 - η), lt_min (by linarith) (by linarith), fun t ht0 ht1 => ?_⟩
    have hcp : c p = η • w := by rw [hpdef]; exact c.right_inv hηw_tgt
    have ht₁ : η + t ≤ η₁ := by linarith [min_le_left (η₁ - η) (η₂ / 2 - η)]
    have ht₂ : η + t ≤ η₂ / 2 := by linarith [min_le_right (η₁ - η) (η₂ / 2 - η)]
    simp only [hcp, ← add_smul]
    constructor
    · apply hη₂
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
      linarith
    · exact hη₁ (η + t) (by linarith) ht₁
  -- ## step 4 completed: the immersed arc in the ambient
  obtain ⟨α, hα0, hα1, hαsm, hαimm, hαinj, hαmem, hαgerm, c', w', e', he', hw'ne, hc'max,
      hq'src, hαterm⟩ :=
    immersedArcWithGerm (n := n) hn hVopen hVpc hpV hz'V hpne c hc hpsrc hw hgermV
  -- ## step 5: the splice at the junction, with the two-sided clamp `χ`
  obtain ⟨e₁, he₁pos, hαgerm'⟩ := hαgerm
  have hcpw : c p = η • w := by rw [hpdef]; exact c.right_inv hηw_tgt
  -- the clamp: the identity on `[-η/4, ∞)`, bounded by `η` below that
  set χ : ℝ → ℝ := fun s => s * Real.smoothTransition (2 + 4 * s / η) with hχdef
  have hχzero : χ 0 = 0 := by simp [hχdef]
  have hχid : ∀ s : ℝ, -(η / 4) ≤ s → χ s = s := by
    intro s hs
    have h1 : (1 : ℝ) ≤ 2 + 4 * s / η := by
      have h2 : -(1 : ℝ) ≤ 4 * s / η := by
        rw [le_div_iff₀ hηpos]
        linarith
      linarith
    simp only [hχdef]
    rw [Real.smoothTransition.one_of_one_le h1, mul_one]
  have hχid0 : ∀ s : ℝ, 0 ≤ s → χ s = s := fun s hs => hχid s (by linarith [hηpos])
  have hχsm : ContMDiff MCreal MCreal smoothOrder χ := by
    rw [hχdef, contMDiff_iff_contDiff]
    exact contDiff_id.mul (Real.smoothTransition.contDiff.comp
      (contDiff_const.add ((contDiff_const.mul contDiff_id).div_const η)))
  have hχle : ∀ s : ℝ, s ≤ η → |χ s| ≤ η := by
    intro s hs
    have hθ0 : 0 ≤ Real.smoothTransition (2 + 4 * s / η) := Real.smoothTransition.nonneg _
    have hθ1 : Real.smoothTransition (2 + 4 * s / η) ≤ 1 := Real.smoothTransition.le_one _
    rw [hχdef, abs_mul, abs_of_nonneg hθ0]
    by_cases h : -(η / 4) ≤ s
    · have h1 : (1 : ℝ) ≤ 2 + 4 * s / η := by
        have h2 : -(1 : ℝ) ≤ 4 * s / η := by
          rw [le_div_iff₀ hηpos]
          linarith
        linarith
      rw [Real.smoothTransition.one_of_one_le h1, mul_one]
      exact abs_le.mpr ⟨by linarith [h, hηpos], hs⟩
    · push_neg at h
      by_cases h2 : -(η / 2) ≤ s
      · have h4 : |s| ≤ η / 2 := by
          rw [abs_le]
          exact ⟨h2, by linarith [h, hηpos]⟩
        nlinarith [hθ1, abs_nonneg s]
      · push_neg at h2
        have hz : Real.smoothTransition (2 + 4 * s / η) = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          have h5 : 4 * s / η ≤ -2 := by
            rw [div_le_iff₀ hηpos]
            linarith
          linarith
        rw [hz, mul_zero]
        exact hηpos.le
  refine ⟨η + 1, by linarith, (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `X 0 = P 1`
    show (if (0 : ℝ) ≤ η then c.symm (χ 0 • w) else α (0 - η)) = P 1
    rw [if_pos hηpos.le, hχzero, zero_smul, ← hcz, c.left_inv hcsrc]
  · -- `X (η + 1) = z'`
    have hnot : ¬ ((η + 1 : ℝ) ≤ η) := by linarith
    show (if (η + 1 : ℝ) ≤ η then c.symm (χ (η + 1) • w) else α ((η + 1) - η)) = z'
    rw [if_neg hnot]
    have : η + 1 - η = (1 : ℝ) := by ring
    rw [this, hα1]
  · -- global smoothness: the two branches, glued at `η` along the straight line
    intro t
    by_cases ht : t < η
    · have hχtgt : χ t • w ∈ c.target := by
        apply hδ
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
        have h1 : |χ t| * ‖w‖ ≤ η * ‖w‖ := mul_le_mul_of_nonneg_right (hχle t ht.le) hwpos.le
        have h2 : η * ‖w‖ < δ / 2 := by
          have h3 := mul_lt_mul_of_pos_right hηltδ hwpos
          have h4 : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 := by field_simp
          rw [h4] at h3
          exact h3
        linarith
      have hsmul : ContMDiff MCreal (MC n) smoothOrder (fun s : ℝ => χ s • w) :=
        hχsm.smul contMDiff_const
      have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder (⇑c.symm) (χ t • w) :=
        (contMDiffOn_symm_of_mem_maximalAtlas (I := MC n) (n := smoothOrder) hc).contMDiffAt
          (c.open_target.mem_nhds hχtgt)
      refine (hsymm.comp t hsmul.contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact if_pos hs.le
    · rcases eq_or_lt_of_le (not_lt.mp ht) with hEq | hGt
      · -- at the junction: both branches are the same straight chart line
        subst hEq
        refine contMDiffAt_glue_same_germ (n := n) hc hpsrc (w := w)
          (A := fun s : ℝ => c.symm (χ s • w)) (B := fun s : ℝ => α (s - η))
          (τ := η) (δ := min (η / 4) e₁) (lt_min (by linarith) he₁pos) ?_ ?_
        · intro s hs1 hs2
          rw [hχid s (by linarith [min_le_left (η / 4) e₁, hs1]), hcpw, ← add_smul]
          congr 1
          ring
        · intro s hs1 hs2
          exact hαgerm' (s - η) (by linarith) (by linarith [min_le_right (η / 4) e₁, hs2])
      · have hev : (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η))
            =ᶠ[𝓝 t] (fun s : ℝ => α (s - η)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hGt] with s hs
          exact if_neg (not_le.mpr hs)
        refine (hαsm.contMDiffAt.comp t
          ((contMDiff_id.sub contMDiff_const).contMDiffAt)).congr_of_eventuallyEq hev
  · -- the immersion on `[0, T]`
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hline : ∀ u ∈ Set.Ioo (-(δ / (2 * ‖w‖))) (δ / (2 * ‖w‖)),
        Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => c.symm (s • w)) u) := by
      have h := isImmersion_chartLine (n := n) c hc hcsrc (V := w) hw
        (T := Set.Ioo (-(δ / (2 * ‖w‖))) (δ / (2 * ‖w‖))) isOpen_Ioo (fun s hs => ?_)
      · intro u hu
        have h2 := h.2 u hu
        rwa [show (fun t : ℝ => c.symm (c (P 1) + t • w)) = (fun s : ℝ => c.symm (s • w))
          from by funext t; rw [hcz, zero_add]] at h2
      · rw [hcz, zero_add]
        apply hδ
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
        have habs : |s| < δ / (2 * ‖w‖) := abs_lt.mpr ⟨hs.1, hs.2⟩
        have h4 : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 := by field_simp
        nlinarith [habs, h4, hwpos, hδpos]
    by_cases hlt : t < η
    · have hev : (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η))
          =ᶠ[𝓝 t] (fun s : ℝ => c.symm (s • w)) := by
        rcases eq_or_lt_of_le ht0 with h0 | h0
        · subst h0
          filter_upwards [Ioo_mem_nhds (by linarith [hηpos] : -(η / 4) < (0 : ℝ))
            (by linarith [hηpos] : (0 : ℝ) < η / 4)] with s hs
          show (if s ≤ η then c.symm (χ s • w) else α (s - η)) = c.symm (s • w)
          rw [if_pos (by linarith [hs.2]), hχid s (le_of_lt hs.1)]
        · filter_upwards [Ioo_mem_nhds (by linarith : t / 2 < t)
            (by linarith : t < η)] with s hs
          show (if s ≤ η then c.symm (χ s • w) else α (s - η)) = c.symm (s • w)
          rw [if_pos (le_of_lt hs.2), hχid s (by linarith [hs.1])]
      rw [hev.mfderiv_eq]
      refine hline t ⟨by linarith [ht0], by linarith [hlt, hηltδ]⟩
    · rcases eq_or_lt_of_le (not_lt.mp hlt) with hEq | hGt
      · subst hEq
        have hev : (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η))
            =ᶠ[𝓝 η] (fun s : ℝ => c.symm (s • w)) := by
          have hpos : (0 : ℝ) < min (η / 4) e₁ :=
            lt_min (by linarith [hηpos]) he₁pos
          filter_upwards [Ioo_mem_nhds (by linarith : η - min (η / 4) e₁ < η)
            (by linarith : η < η + min (η / 4) e₁)] with s hs
          by_cases hsη : s ≤ η
          · rw [if_pos hsη, hχid s (by linarith [min_le_left (η / 4) e₁, hs.1])]
          · rw [if_neg hsη]
            rw [hαgerm' (s - η) (by linarith [le_of_lt (not_le.mp hsη)])
              (by linarith [min_le_right (η / 4) e₁, hs.2]), hcpw, ← add_smul]
            congr 1
            ring
        rw [hev.mfderiv_eq]
        exact hline η ⟨by linarith [hηpos], hηltδ⟩
      · have hev : (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η))
            =ᶠ[𝓝 t] (fun s : ℝ => α (s - η)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hGt] with s hs
          exact if_neg (not_le.mpr hs)
        rw [hev.mfderiv_eq]
        have hdiff : MDifferentiableAt MCreal MCreal (fun s : ℝ => s - η) t := by
          have h : MDifferentiableAt MCreal MCreal (fun s : ℝ => s + (-η)) t :=
            mdifferentiableAt_id.add mdifferentiableAt_const
          refine h.congr_of_eventuallyEq ?_
          filter_upwards with s
          ring
        rw [show (fun s : ℝ => α (s - η)) = (α ∘ fun s : ℝ => s - η) from rfl]
        refine Work.Noncompact.Routing.injective_mfderiv_reparam
          (f := α) (a := fun s : ℝ => s - η) (x := t) ?_ hdiff ?_ (hαimm (t - η))
        · exact (hαsm.contMDiffAt (x := t - η)).mdifferentiableAt (by simp)
        · rw [mfderiv_sub_eq_id]
          exact Function.injective_id
  · -- the image lies in the corridor
    rintro x ⟨s, hs, rfl⟩
    by_cases hsη : s ≤ η
    · show (if s ≤ η then c.symm (χ s • w) else α (s - η)) ∈ C
      rw [if_pos hsη, hχid0 s hs.1]
      exact hseg_mem s hs.1 hsη
    · show (if s ≤ η then c.symm (χ s • w) else α (s - η)) ∈ C
      rw [if_neg hsη]
      exact (hαmem (s - η) ⟨by linarith [le_of_lt (not_le.mp hsη)], by linarith [hs.2]⟩).1
  · -- the piece meets the previous trace only at the junction
    have hmain : ∀ s ∈ Set.Ioc (0:ℝ) (η + 1),
        (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η)) s ∉
          P '' Set.Icc (0:ℝ) 1 := by
      intro s hs
      show (if s ≤ η then c.symm (χ s • w) else α (s - η)) ∉ P '' Set.Icc (0:ℝ) 1
      by_cases hsη : s ≤ η
      · rw [if_pos hsη, hχid0 s (le_of_lt hs.1)]
        exact hseg_avoid s hs.1 hsη
      · rw [if_neg hsη]
        exact (hαmem (s - η) ⟨by linarith [le_of_lt (not_le.mp hsη)],
          by linarith [hs.2]⟩).2
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨s, hs, hsx⟩, hxP⟩
    exact hmain s hs (hsx ▸ hxP)
  · -- the initial germ: `χ` is the identity on `[0, η]`
    refine ⟨η, hηpos, fun t ht0 ht1 => ?_⟩
    show (if t ≤ η then c.symm (χ t • w) else α (t - η)) = c.symm (t • w)
    rw [if_pos ht1, hχid0 t ht0]
  · -- the terminal germ, shifted by `η`
    refine ⟨c', w', min e' (1 / 2), lt_min he' (by norm_num), hw'ne, hc'max, hq'src,
      fun t ht1 ht2 => ?_⟩
    have hlt : η < t := by
      have h : (0 : ℝ) < min e' (1 / 2) := lt_min he' (by norm_num)
      have h2 : min e' (1 / 2) ≤ 1 / 2 := min_le_right _ _
      linarith
    show (if t ≤ η then c.symm (χ t • w) else α (t - η)) = c'.symm (c' z' + (t - (η + 1)) • w')
    rw [if_neg (not_le.mpr hlt)]
    have ht : 1 - e' ≤ t - η := by
      have := min_le_left e' (1 / 2)
      linarith
    have ht' : t - η ≤ 1 := by linarith
    rw [hαterm (t - η) ht ht']
    congr 1
    ring

theorem oneStep_piece_ambient {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    {P : ℝ → M} (hPc : Continuous P) (hPinj : Set.InjOn P (Set.Icc (0:ℝ) 1))
    (hCavoid : ∀ x ∈ C, x ∉ P '' Set.Icc (0:ℝ) 1)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M)
    (hcsrc : P 1 ∈ c.source) (hcz : c (P 1) = 0)
    {δ : ℝ} (hδpos : 0 < δ)
    (hδ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) δ ⊆ c.target)
    {w : EuclideanSpace ℝ (Fin n)} (hw : w ≠ 0) {e : ℝ} (he : 0 < e)
    (hger : ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → P t = c.symm ((t - 1) • w))
    {z' : M} (hz'C : z' ∈ C) (hz'P : z' ∉ P '' Set.Icc (0:ℝ) 1) (hz'ne : z' ≠ P 1)
    {η₁ : ℝ} (hη₁pos : 0 < η₁) (hη₁ : ∀ s : ℝ, 0 < s → s ≤ η₁ → c.symm (s • w) ∉ P '' Set.Icc (0:ℝ) 1)
    {η₂ : ℝ} (hη₂pos : 0 < η₂) (hη₂ : ∀ s : ℝ, s ∈ Metric.ball (0:ℝ) η₂ → c.symm (s • w) ∈ C)
    {η : ℝ} (hηpos : 0 < η) (hηlt₁ : η < η₁) (hηlt₂ : η < η₂ / 2)
    (hηltδ : η < δ / (2 * ‖w‖)) (hηz' : c.symm (η • w) ≠ z') :
    ∃ T : ℝ, 0 < T ∧ ∃ X : ℝ → M, X 0 = P 1 ∧ X T = z' ∧
      ContMDiff Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder X ∧
      (∀ t ∈ Set.Icc (0:ℝ) T, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) X t)) ∧
      X '' Set.Icc (0:ℝ) T ⊆ C ∪ (fun t : ℝ => c.symm (t • w)) '' Set.Icc (0:ℝ) η ∧
      (X '' Set.Ioc (0:ℝ) T ∩ P '' Set.Icc (0:ℝ) 1 = ∅) ∧
      (∃ e' : ℝ, 0 < e' ∧ ∀ t : ℝ, 0 ≤ t → t ≤ e' → X t = c.symm (t • w)) ∧
      ∃ (c' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (w' : EuclideanSpace ℝ (Fin n)) (e' : ℝ), 0 < e' ∧ w' ≠ 0 ∧
        c' ∈ IsManifold.maximalAtlas (Work.Noncompact.CompressionTube.MC n)
          Work.Noncompact.CompressionTube.smoothOrder M ∧ z' ∈ c'.source ∧
        ∀ t : ℝ, T - e' ≤ t → t ≤ T → X t = c'.symm (c' z' + (t - T) • w') := by
  classical
  -- ## the access point and its basic properties (all by hypothesis)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hPmem : P '' Set.Icc (0:ℝ) 1 ⊆ Cᶜ := fun x hx hxC => hCavoid x hxC hx
  have h0tgt : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target := by
    rw [← hcz]; exact c.map_source hcsrc
  have hηw_tgt : η • w ∈ c.target := by
    apply hδ
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hηpos]
    have h : η * ‖w‖ < δ / (2 * ‖w‖) * ‖w‖ :=
      mul_lt_mul_of_pos_right hηltδ hwpos
    have h2 : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 := by field_simp
    rw [h2] at h
    linarith
  set p : M := c.symm (η • w) with hpdef
  have hseg_mem : ∀ s : ℝ, 0 ≤ s → s ≤ η → c.symm (s • w) ∈ C := by
    intro s hs0 hsη
    apply hη₂
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]
    linarith
  have hseg_avoid : ∀ s : ℝ, 0 < s → s ≤ η → c.symm (s • w) ∉ P '' Set.Icc (0:ℝ) 1 :=
    fun s hs0 hsη => hη₁ s hs0 (le_trans hsη hηlt₁.le)
  have hpC : p ∈ C := hseg_mem η hηpos.le le_rfl
  have hz'C' : z' ∈ C := hz'C
  have hpsrc : p ∈ c.source := by rw [hpdef]; exact c.map_target hηw_tgt
  have hpne : p ≠ z' := by rw [hpdef]; exact hηz'
  -- ## step 3: the ambient itself is open and preconnected
  have hVopen : IsOpen C := hC
  have hVpc : IsPreconnected C := hCc
  -- ## step 4: the germ hypothesis, at `min (η₁ - η) (η₂/2 - η)`
  have hgermV : ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ t : ℝ, 0 < t → t ≤ e₀ →
      c.symm (c p + t • w) ∈ C := by
    refine ⟨min (η₁ - η) (η₂ / 2 - η), lt_min (by linarith) (by linarith), fun t ht0 ht1 => ?_⟩
    have hcp : c p = η • w := by rw [hpdef]; exact c.right_inv hηw_tgt
    have ht₁ : η + t ≤ η₁ := by linarith [min_le_left (η₁ - η) (η₂ / 2 - η)]
    have ht₂ : η + t ≤ η₂ / 2 := by linarith [min_le_right (η₁ - η) (η₂ / 2 - η)]
    simp only [hcp, ← add_smul]
    apply hη₂
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
    linarith
  -- ## step 4 completed: the immersed arc in the ambient
  obtain ⟨α, hα0, hα1, hαsm, hαimm, hαinj, hαmem, hαgerm, c', w', e', he', hw'ne, hc'max,
      hq'src, hαterm⟩ :=
    immersedArcWithGerm (n := n) hn hVopen hVpc hpC hz'C' hpne c hc hpsrc hw hgermV
  -- ## step 5: the splice at the junction, with the two-sided clamp `χ`
  obtain ⟨e₁, he₁pos, hαgerm'⟩ := hαgerm
  have hcpw : c p = η • w := by rw [hpdef]; exact c.right_inv hηw_tgt
  -- the clamp: the identity on `[-η/4, ∞)`, bounded by `η` below that
  set χ : ℝ → ℝ := fun s => s * Real.smoothTransition (2 + 4 * s / η) with hχdef
  have hχzero : χ 0 = 0 := by simp [hχdef]
  have hχid : ∀ s : ℝ, -(η / 4) ≤ s → χ s = s := by
    intro s hs
    have h1 : (1 : ℝ) ≤ 2 + 4 * s / η := by
      have h2 : -(1 : ℝ) ≤ 4 * s / η := by
        rw [le_div_iff₀ hηpos]
        linarith
      linarith
    simp only [hχdef]
    rw [Real.smoothTransition.one_of_one_le h1, mul_one]
  have hχid0 : ∀ s : ℝ, 0 ≤ s → χ s = s := fun s hs => hχid s (by linarith [hηpos])
  have hχsm : ContMDiff MCreal MCreal smoothOrder χ := by
    rw [hχdef, contMDiff_iff_contDiff]
    exact contDiff_id.mul (Real.smoothTransition.contDiff.comp
      (contDiff_const.add ((contDiff_const.mul contDiff_id).div_const η)))
  have hχle : ∀ s : ℝ, s ≤ η → |χ s| ≤ η := by
    intro s hs
    have hθ0 : 0 ≤ Real.smoothTransition (2 + 4 * s / η) := Real.smoothTransition.nonneg _
    have hθ1 : Real.smoothTransition (2 + 4 * s / η) ≤ 1 := Real.smoothTransition.le_one _
    rw [hχdef, abs_mul, abs_of_nonneg hθ0]
    by_cases h : -(η / 4) ≤ s
    · have h1 : (1 : ℝ) ≤ 2 + 4 * s / η := by
        have h2 : -(1 : ℝ) ≤ 4 * s / η := by
          rw [le_div_iff₀ hηpos]
          linarith
        linarith
      rw [Real.smoothTransition.one_of_one_le h1, mul_one]
      exact abs_le.mpr ⟨by linarith [h, hηpos], hs⟩
    · push_neg at h
      by_cases h2 : -(η / 2) ≤ s
      · have h4 : |s| ≤ η / 2 := by
          rw [abs_le]
          exact ⟨h2, by linarith [h, hηpos]⟩
        nlinarith [hθ1, abs_nonneg s]
      · push_neg at h2
        have hz : Real.smoothTransition (2 + 4 * s / η) = 0 := by
          apply Real.smoothTransition.zero_of_nonpos
          have h5 : 4 * s / η ≤ -2 := by
            rw [div_le_iff₀ hηpos]
            linarith
          linarith
        rw [hz, mul_zero]
        exact hηpos.le
  refine ⟨η + 1, by linarith, (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `X 0 = P 1`
    show (if (0 : ℝ) ≤ η then c.symm (χ 0 • w) else α (0 - η)) = P 1
    rw [if_pos hηpos.le, hχzero, zero_smul, ← hcz, c.left_inv hcsrc]
  · -- `X (η + 1) = z'`
    have hnot : ¬ ((η + 1 : ℝ) ≤ η) := by linarith
    show (if (η + 1 : ℝ) ≤ η then c.symm (χ (η + 1) • w) else α ((η + 1) - η)) = z'
    rw [if_neg hnot]
    have : η + 1 - η = (1 : ℝ) := by ring
    rw [this, hα1]
  · -- global smoothness: the two branches, glued at `η` along the straight line
    intro t
    by_cases ht : t < η
    · have hχtgt : χ t • w ∈ c.target := by
        apply hδ
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
        have h1 : |χ t| * ‖w‖ ≤ η * ‖w‖ := mul_le_mul_of_nonneg_right (hχle t ht.le) hwpos.le
        have h2 : η * ‖w‖ < δ / 2 := by
          have h3 := mul_lt_mul_of_pos_right hηltδ hwpos
          have h4 : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 := by field_simp
          rw [h4] at h3
          exact h3
        linarith
      have hsmul : ContMDiff MCreal (MC n) smoothOrder (fun s : ℝ => χ s • w) :=
        hχsm.smul contMDiff_const
      have hsymm : ContMDiffAt (MC n) (MC n) smoothOrder (⇑c.symm) (χ t • w) :=
        (contMDiffOn_symm_of_mem_maximalAtlas (I := MC n) (n := smoothOrder) hc).contMDiffAt
          (c.open_target.mem_nhds hχtgt)
      refine (hsymm.comp t hsmul.contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact if_pos hs.le
    · rcases eq_or_lt_of_le (not_lt.mp ht) with hEq | hGt
      · -- at the junction: both branches are the same straight chart line
        subst hEq
        refine contMDiffAt_glue_same_germ (n := n) hc hpsrc (w := w)
          (A := fun s : ℝ => c.symm (χ s • w)) (B := fun s : ℝ => α (s - η))
          (τ := η) (δ := min (η / 4) e₁) (lt_min (by linarith) he₁pos) ?_ ?_
        · intro s hs1 hs2
          rw [hχid s (by linarith [min_le_left (η / 4) e₁, hs1]), hcpw, ← add_smul]
          congr 1
          ring
        · intro s hs1 hs2
          exact hαgerm' (s - η) (by linarith) (by linarith [min_le_right (η / 4) e₁, hs2])
      · have hev : (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η))
            =ᶠ[𝓝 t] (fun s : ℝ => α (s - η)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hGt] with s hs
          exact if_neg (not_le.mpr hs)
        refine (hαsm.contMDiffAt.comp t
          ((contMDiff_id.sub contMDiff_const).contMDiffAt)).congr_of_eventuallyEq hev
  · -- the immersion on `[0, T]`
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hline : ∀ u ∈ Set.Ioo (-(δ / (2 * ‖w‖))) (δ / (2 * ‖w‖)),
        Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => c.symm (s • w)) u) := by
      have h := isImmersion_chartLine (n := n) c hc hcsrc (V := w) hw
        (T := Set.Ioo (-(δ / (2 * ‖w‖))) (δ / (2 * ‖w‖))) isOpen_Ioo (fun s hs => ?_)
      · intro u hu
        have h2 := h.2 u hu
        rwa [show (fun t : ℝ => c.symm (c (P 1) + t • w)) = (fun s : ℝ => c.symm (s • w))
          from by funext t; rw [hcz, zero_add]] at h2
      · rw [hcz, zero_add]
        apply hδ
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
        have habs : |s| < δ / (2 * ‖w‖) := abs_lt.mpr ⟨hs.1, hs.2⟩
        have h4 : δ / (2 * ‖w‖) * ‖w‖ = δ / 2 := by field_simp
        nlinarith [habs, h4, hwpos, hδpos]
    by_cases hlt : t < η
    · have hev : (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η))
          =ᶠ[𝓝 t] (fun s : ℝ => c.symm (s • w)) := by
        rcases eq_or_lt_of_le ht0 with h0 | h0
        · subst h0
          filter_upwards [Ioo_mem_nhds (by linarith [hηpos] : -(η / 4) < (0 : ℝ))
            (by linarith [hηpos] : (0 : ℝ) < η / 4)] with s hs
          show (if s ≤ η then c.symm (χ s • w) else α (s - η)) = c.symm (s • w)
          rw [if_pos (by linarith [hs.2]), hχid s (le_of_lt hs.1)]
        · filter_upwards [Ioo_mem_nhds (by linarith : t / 2 < t)
            (by linarith : t < η)] with s hs
          show (if s ≤ η then c.symm (χ s • w) else α (s - η)) = c.symm (s • w)
          rw [if_pos (le_of_lt hs.2), hχid s (by linarith [hs.1])]
      rw [hev.mfderiv_eq]
      refine hline t ⟨by linarith [ht0], by linarith [hlt, hηltδ]⟩
    · rcases eq_or_lt_of_le (not_lt.mp hlt) with hEq | hGt
      · subst hEq
        have hev : (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η))
            =ᶠ[𝓝 η] (fun s : ℝ => c.symm (s • w)) := by
          have hpos : (0 : ℝ) < min (η / 4) e₁ :=
            lt_min (by linarith [hηpos]) he₁pos
          filter_upwards [Ioo_mem_nhds (by linarith : η - min (η / 4) e₁ < η)
            (by linarith : η < η + min (η / 4) e₁)] with s hs
          by_cases hsη : s ≤ η
          · rw [if_pos hsη, hχid s (by linarith [min_le_left (η / 4) e₁, hs.1])]
          · rw [if_neg hsη]
            rw [hαgerm' (s - η) (by linarith [le_of_lt (not_le.mp hsη)])
              (by linarith [min_le_right (η / 4) e₁, hs.2]), hcpw, ← add_smul]
            congr 1
            ring
        rw [hev.mfderiv_eq]
        exact hline η ⟨by linarith [hηpos], hηltδ⟩
      · have hev : (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η))
            =ᶠ[𝓝 t] (fun s : ℝ => α (s - η)) := by
          filter_upwards [isOpen_Ioi.mem_nhds hGt] with s hs
          exact if_neg (not_le.mpr hs)
        rw [hev.mfderiv_eq]
        have hdiff : MDifferentiableAt MCreal MCreal (fun s : ℝ => s - η) t := by
          have h : MDifferentiableAt MCreal MCreal (fun s : ℝ => s + (-η)) t :=
            mdifferentiableAt_id.add mdifferentiableAt_const
          refine h.congr_of_eventuallyEq ?_
          filter_upwards with s
          ring
        rw [show (fun s : ℝ => α (s - η)) = (α ∘ fun s : ℝ => s - η) from rfl]
        refine Work.Noncompact.Routing.injective_mfderiv_reparam
          (f := α) (a := fun s : ℝ => s - η) (x := t) ?_ hdiff ?_ (hαimm (t - η))
        · exact (hαsm.contMDiffAt (x := t - η)).mdifferentiableAt (by simp)
        · rw [mfderiv_sub_eq_id]
          exact Function.injective_id
  · -- the image lies in the corridor, except the initial germ segment
    rintro x ⟨s, hs, rfl⟩
    by_cases hsη : s ≤ η
    · show (if s ≤ η then c.symm (χ s • w) else α (s - η)) ∈
        C ∪ (fun t : ℝ => c.symm (t • w)) '' Set.Icc (0:ℝ) η
      rw [if_pos hsη]
      exact Or.inr ⟨s, ⟨hs.1, hsη⟩, by rw [hχid0 s hs.1]⟩
    · show (if s ≤ η then c.symm (χ s • w) else α (s - η)) ∈
        C ∪ (fun t : ℝ => c.symm (t • w)) '' Set.Icc (0:ℝ) η
      rw [if_neg hsη]
      exact Or.inl (hαmem (s - η) ⟨by linarith [le_of_lt (not_le.mp hsη)],
        by linarith [hs.2]⟩)
  · -- the piece meets the previous trace only at the junction
    have hmain : ∀ s ∈ Set.Ioc (0:ℝ) (η + 1),
        (fun s : ℝ => if s ≤ η then c.symm (χ s • w) else α (s - η)) s ∉
          P '' Set.Icc (0:ℝ) 1 := by
      intro s hs
      show (if s ≤ η then c.symm (χ s • w) else α (s - η)) ∉ P '' Set.Icc (0:ℝ) 1
      by_cases hsη : s ≤ η
      · rw [if_pos hsη, hχid0 s (le_of_lt hs.1)]
        exact hseg_avoid s hs.1 hsη
      · rw [if_neg hsη]
        exact fun hcon => hCavoid _ (hαmem (s - η) ⟨by linarith [le_of_lt (not_le.mp hsη)],
          by linarith [hs.2]⟩) hcon
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨s, hs, hsx⟩, hxP⟩
    exact hmain s hs (hsx ▸ hxP)
  · -- the initial germ: `χ` is the identity on `[0, η]`
    refine ⟨η, hηpos, fun t ht0 ht1 => ?_⟩
    show (if t ≤ η then c.symm (χ t • w) else α (t - η)) = c.symm (t • w)
    rw [if_pos ht1, hχid0 t ht0]
  · -- the terminal germ, shifted by `η`
    refine ⟨c', w', min e' (1 / 2), lt_min he' (by norm_num), hw'ne, hc'max, hq'src,
      fun t ht1 ht2 => ?_⟩
    have hlt : η < t := by
      have h : (0 : ℝ) < min e' (1 / 2) := lt_min he' (by norm_num)
      have h2 : min e' (1 / 2) ≤ 1 / 2 := min_le_right _ _
      linarith
    show (if t ≤ η then c.symm (χ t • w) else α (t - η)) = c'.symm (c' z' + (t - (η + 1)) • w')
    rw [if_neg (not_le.mpr hlt)]
    have ht : 1 - e' ≤ t - η := by
      have := min_le_left e' (1 / 2)
      linarith
    have ht' : t - η ≤ 1 := by linarith
    rw [hαterm (t - η) ht ht']
    congr 1
    ring



end

end Work.Noncompact.CompressionTube
