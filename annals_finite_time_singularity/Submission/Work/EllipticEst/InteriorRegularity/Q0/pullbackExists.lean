/-
Work module for `annals_finite_time_singularity`: the pull-back of a smooth compactly supported
test function on the half-strip `ℝ × (0,π/2)` to the quadrant `Q0 = (0,∞) × (0,π/2)`, together
with the chain rule `bslOp α φ = kopDr ψ ∘ log` on `Q0`.

The pull-back used here is `φ (z,θ) = χ z · ψ ((1/α) log z) θ`, where `χ` is a smooth cut-off
which is `1` on the `z`-range of the (compactly supported) pull-back and vanishes for `z ≤ 0`:
this makes `φ` smooth and compactly supported on `ℝ²`, and it agrees with the composition
`(z,θ) ↦ ψ ((1/α) log z) θ` at every `z > 0`.  Its support is contained in `(0,∞) × (0,π/2)`
because `ψ` vanishes outside the `θ`-projection of its support, and that projection is a compact
subset of `(0,π/2)` (so it stays a positive distance away from the endpoints `0` and `π/2`).

On `Q0` the operator identity `bslOp α φ = kopDr ψ ∘ log` then follows from the pointwise chain
rule `bslOp_comp_exp` on the (open) region where the cut-off is `1` or where `ψ` does not
vanish (there `φ` agrees with the bare composition, which is locally `ψ ∘ log`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.EllipticEst.InteriorRegularity.Q0.RRBasic
import Submission.Work.EllipticEst.InteriorRegularity.Q0.exists_cutoff
import Submission.Work.EllipticEst.InteriorRegularity.bslOp_comp_exp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

set_option maxHeartbeats 1600000

/-! ## Auxiliary facts about supports -/

/-- A norm bound for the (topological) support of a compactly supported function on `ℝ × ℝ`. -/
lemma exists_norm_bound_tsupport {ψ : ℝ → ℝ → ℝ}
    (hψc : HasCompactSupport (Function.uncurry ψ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ tsupport (Function.uncurry ψ), ‖p‖ ≤ R := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).mp
    hψc.isCompact.isBounded
  refine ⟨|r|, abs_nonneg r, fun p hp => ?_⟩
  have hd : dist p (0 : ℝ × ℝ) ≤ r := Metric.mem_closedBall.mp (hr hp)
  have h1 : ‖p‖ ≤ r := by simpa using hd
  exact le_trans h1 (le_abs_self r)

/-- The `θ`-projection of a compact subset of the open half-strip `ℝ × (0,π/2)` stays a positive
distance away from both endpoints. -/
lemma thetaWindow {K : Set (ℝ × ℝ)} (hKc : IsCompact K)
    (hsub : K ⊆ Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.pi / 4 ∧ Prod.snd '' K ⊆ Set.Icc δ (Real.pi / 2 - δ) := by
  obtain ⟨ε, hεpos, hεsub⟩ :=
    hKc.exists_cthickening_subset_open
      (t := Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) (isOpen_univ.prod isOpen_Ioo) hsub
  refine ⟨min ε (Real.pi / 4), lt_min hεpos (by linarith [Real.pi_gt_three]),
    min_le_right _ _, ?_⟩
  rintro θ ⟨p, hp, rfl⟩
  have hdist_up : dist (p.1, p.2 + ε) (p.1, p.2) ≤ ε := by
    have h1 : dist (p.1 : ℝ) p.1 = 0 := dist_self _
    have h2 : dist (p.2 + ε) p.2 = ε := by
      rw [Real.dist_eq]
      have h3 : (p.2 + ε) - p.2 = ε := by ring
      rw [h3, abs_of_pos hεpos]
    rw [Prod.dist_eq, h1, h2]
    exact max_le (le_of_lt hεpos) le_rfl
  have hdist_dn : dist (p.1, p.2 - ε) (p.1, p.2) ≤ ε := by
    have h1 : dist (p.1 : ℝ) p.1 = 0 := dist_self _
    have h2 : dist (p.2 - ε) p.2 = ε := by
      rw [Real.dist_eq]
      have h3 : (p.2 - ε) - p.2 = -ε := by ring
      rw [h3, abs_neg, abs_of_pos hεpos]
    rw [Prod.dist_eq, h1, h2]
    exact max_le (le_of_lt hεpos) le_rfl
  have hup : p.2 ≤ Real.pi / 2 - ε := by
    have hmem := hεsub (Metric.mem_cthickening_of_dist_le (p.1, p.2 + ε) p ε K hp hdist_up)
    have hlt : p.2 + ε < Real.pi / 2 := (Set.mem_prod.mp hmem).2.2
    linarith
  have hlow : ε ≤ p.2 := by
    have hmem := hεsub (Metric.mem_cthickening_of_dist_le (p.1, p.2 - ε) p ε K hp hdist_dn)
    have hpos : 0 < p.2 - ε := (Set.mem_prod.mp hmem).2.1
    linarith
  exact ⟨le_trans (min_le_left _ _) hlow, by linarith [min_le_left ε (Real.pi / 4), hup]⟩

/-- If `ψ : ℝ → ℝ → ℝ` is smooth and `χ : ℝ → ℝ` is smooth and vanishes on `(-∞,A]`
(`χ z ≠ 0 → A < z` with `A > 0`), then `(z,θ) ↦ χ z * ψ ((1/α) log z) θ` is smooth on `ℝ²`:
the logarithm is smooth on `(0,∞)` and the vanishing of `χ` near `0` covers the rest. -/
lemma contDiff_cut_logComp {α : ℝ} (hα : 0 < α) {ψ : ℝ → ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    {χ : ℝ → ℝ} (hχ : ∀ n : ℕ, ContDiff ℝ n χ) {A : ℝ} (hA : 0 < A)
    (hχA : ∀ z : ℝ, χ z ≠ 0 → A < z) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (fun z θ : ℝ => χ z * ψ ((1 / α) * Real.log z) θ)) := by
  intro n
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p.1
  · have hVo : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
    have hcd : ContDiffOn ℝ (n : WithTop ℕ∞)
        (Function.uncurry (fun z θ : ℝ => χ z * ψ ((1 / α) * Real.log z) θ))
        {q : ℝ × ℝ | 0 < q.1} := by
      have hχ1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : ℝ × ℝ => χ q.1)
          {q : ℝ × ℝ | 0 < q.1} :=
        ((hχ n).comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ))).contDiffOn
      have hlog : ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : ℝ × ℝ => Real.log q.1)
          {q : ℝ × ℝ | 0 < q.1} :=
        Real.contDiffOn_log.comp (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contDiffOn
          (fun q hq => by simpa using ne_of_gt hq)
      have hsm : ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : ℝ × ℝ => (1 / α) * Real.log q.1)
          {q : ℝ × ℝ | 0 < q.1} := by
        simpa only [smul_eq_mul] using ContDiffOn.const_smul (𝕜 := ℝ) (1 / α) hlog
      have hsnd : ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : ℝ × ℝ => q.2)
          {q : ℝ × ℝ | 0 < q.1} :=
        (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ)).contDiffOn
      have hinner : ContDiffOn ℝ (n : WithTop ℕ∞)
          (fun q : ℝ × ℝ => ψ ((1 / α) * Real.log q.1) q.2) {q : ℝ × ℝ | 0 < q.1} :=
        (ContDiff.contDiffOn (hψ n) (s := Set.univ)).comp (hsm.prodMk hsnd)
          (fun q _ => trivial)
      exact hχ1.mul hinner
    exact hcd.contDiffAt (hVo.mem_nhds hp)
  · simp only [not_lt] at hp
    have hplt : p.1 < A := lt_of_le_of_lt hp hA
    have hVo : IsOpen {q : ℝ × ℝ | q.1 < A} := isOpen_lt continuous_fst continuous_const
    have hcd : ContDiffOn ℝ (n : WithTop ℕ∞)
        (Function.uncurry (fun z θ : ℝ => χ z * ψ ((1 / α) * Real.log z) θ))
        {q : ℝ × ℝ | q.1 < A} := by
      refine (contDiffOn_const (c := (0 : ℝ))).congr (fun q hq => ?_)
      show Function.uncurry (fun z θ : ℝ => χ z * ψ ((1 / α) * Real.log z) θ) q = (0 : ℝ)
      have h0 : χ q.1 = 0 := by
        by_contra hne
        exact absurd (hχA q.1 hne) (not_lt.mpr (le_of_lt hq))
      simp only [Function.uncurry, h0, zero_mul]
    exact hcd.contDiffAt (hVo.mem_nhds hplt)

/-! ## The pull-back -/

theorem pullbackExists {α : ℝ} (hα : 0 < α) {ψ : ℝ → ℝ → ℝ}
    (hψ : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry ψ))
    (hψc : HasCompactSupport (Function.uncurry ψ))
    (hψs : tsupport (Function.uncurry ψ) ⊆ Work.EllipticEst.InteriorRegularity.Q0.stripRR) :
    ∃ φ : ℝ → ℝ → ℝ,
      (∀ n : ℕ, ContDiff ℝ n (Function.uncurry φ)) ∧
      HasCompactSupport (Function.uncurry φ) ∧
      tsupport (Function.uncurry φ) ⊆ Work.FTS.EllipticEst.Q0 ∧
      (∀ z θ : ℝ, 0 < z → φ z θ = ψ ((1 / α) * Real.log z) θ) ∧
      (∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        Work.Elliptic.bslOp α φ z θ = Work.EllipticEst.InteriorRegularity.Q0.kopDr ψ ((1 / α) * Real.log z) θ) := by
  -- a Euclidean bound for the support of `ψ`, and the `θ`-window around its `θ`-projection
  obtain ⟨R, hR0, hR⟩ := exists_norm_bound_tsupport hψc
  obtain ⟨δ, hδpos, _hδ4, hδsub⟩ := thetaWindow hψc.isCompact hψs
  -- the `z`-cut-off
  set Az : ℝ := Real.exp (-(α * (R + 2))) / 2 with hAz
  set Lz : ℝ := Real.exp (-(α * (R + 1))) with hLz
  set Uz : ℝ := Real.exp (α * (R + 1)) with hUz
  set Bz : ℝ := 2 * Real.exp (α * (R + 1)) with hBz
  have hAzpos : 0 < Az := by rw [hAz]; positivity
  have hAzLz : Az < Lz := by
    rw [hAz, hLz]
    have h1 : Real.exp (-(α * (R + 2))) < Real.exp (-(α * (R + 1))) :=
      Real.exp_lt_exp.mpr (by nlinarith [hα, hR0])
    have h2 : 0 < Real.exp (-(α * (R + 1))) := Real.exp_pos _
    linarith
  have hLzUz : Lz ≤ Uz := by
    rw [hLz, hUz]
    exact Real.exp_le_exp.mpr (by nlinarith [hα, hR0])
  have hUzBz : Uz < Bz := by
    rw [hUz, hBz]
    linarith [Real.exp_pos (α * (R + 1))]
  obtain ⟨χz, hχzsm, hχzsupp, hχz1⟩ := exists_cutoff hAzpos hAzLz hLzUz hUzBz
  -- the support of the pull-back is contained in a compact box;
  -- `ψ` vanishes outside the `θ`-window, so the `θ`-coordinates of the box are strictly inside
  have hsuppK :
      Function.support (Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ))
        ⊆ Set.Icc Az Bz ×ˢ Set.Icc δ (Real.pi / 2 - δ) := by
    intro p hp
    rw [Function.mem_support] at hp
    have hz0 : χz p.1 ≠ 0 := fun h => hp (by simp only [Function.uncurry, h, zero_mul])
    have hψ0 : ψ ((1 / α) * Real.log p.1) p.2 ≠ 0 :=
      fun h => hp (by simp only [Function.uncurry, h, mul_zero])
    have hmem : ((1 / α) * Real.log p.1, p.2) ∈ tsupport (Function.uncurry ψ) :=
      subset_tsupport _ (Function.mem_support.mpr
        (by simpa only [Function.uncurry] using hψ0))
    exact ⟨⟨le_of_lt (hχzsupp p.1 hz0).1, le_of_lt (hχzsupp p.1 hz0).2⟩,
      hδsub ⟨_, hmem, rfl⟩⟩
  have hsubK :
      tsupport (Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ))
        ⊆ Set.Icc Az Bz ×ˢ Set.Icc δ (Real.pi / 2 - δ) :=
    (IsClosed.closure_subset_iff (isClosed_Icc.prod isClosed_Icc)).mpr hsuppK
  refine ⟨fun z θ => χz z * ψ ((1 / α) * Real.log z) θ, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro n
    exact contDiff_cut_logComp hα hψ hχzsm hAzpos (fun z hz => (hχzsupp z hz).1) n
  · -- compact support
    exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsubK
  · -- the support lies in the open quadrant
    intro p hpk
    have hmem := hsubK hpk
    have h1 : Az ≤ p.1 ∧ p.1 ≤ Bz := hmem.1
    have h2 : δ ≤ p.2 ∧ p.2 ≤ Real.pi / 2 - δ := hmem.2
    simp only [Work.FTS.EllipticEst.Q0, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨by linarith [h1.1, hAzpos], by linarith [h2.1, hδpos],
      by linarith [h2.2, hδpos]⟩
  · -- agreement with the composition at `z > 0`
    intro z θ hz
    by_cases h0 : ψ ((1 / α) * Real.log z) θ = 0
    · simp only [h0, mul_zero]
    · have hmem : ((1 / α) * Real.log z, θ) ∈ tsupport (Function.uncurry ψ) :=
        subset_tsupport _ (Function.mem_support.mpr
          (by simpa only [Function.uncurry] using h0))
      have hbnd : |(1 / α) * Real.log z| ≤ R :=
        le_trans (by simpa using norm_fst_le ((1 / α) * Real.log z, θ)) (hR _ hmem)
      obtain ⟨hl, hu⟩ := abs_le.mp hbnd
      have hmul : α * ((1 / α) * Real.log z) = Real.log z := by
        rw [← mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hα), one_mul]
      have hlogl : -(α * R) ≤ Real.log z :=
        calc -(α * R) = α * (-R) := by ring
          _ ≤ α * ((1 / α) * Real.log z) := mul_le_mul_of_nonneg_left hl hα.le
          _ = Real.log z := hmul
      have hlogu : Real.log z ≤ α * R :=
        calc Real.log z = α * ((1 / α) * Real.log z) := hmul.symm
          _ ≤ α * R := mul_le_mul_of_nonneg_left hu hα.le
      have hzL : Lz ≤ z := by
        rw [hLz, ← Real.exp_log hz]
        exact Real.exp_le_exp.mpr (by nlinarith [hα, hlogl])
      have hzU : z ≤ Uz := by
        rw [hUz, ← Real.exp_log hz]
        exact Real.exp_le_exp.mpr (by nlinarith [hα, hlogu])
      simp only [hχz1 z hzL hzU, one_mul]
  · -- the chain rule on the quadrant
    intro z θ hz hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    have hexp : Real.exp (α * ((1 / α) * Real.log z)) = z := exp_alpha_eq_self hα hz
    have hce : Work.Elliptic.bslOp α (fun z θ' : ℝ => ψ ((1 / α) * Real.log z) θ') z θ
        = kopDr ψ ((1 / α) * Real.log z) θ := by
      have h := bslOp_comp_exp (α := α) hα (ψ := ψ) hψ (s := (1 / α) * Real.log z)
        (θ := θ) hcos
      rwa [hexp] at h
    by_cases hmem : ((1 / α) * Real.log z, θ) ∈ tsupport (Function.uncurry ψ)
    · -- near the support of `ψ` the cut-off is `1`
      have hbnd : |(1 / α) * Real.log z| ≤ R :=
        le_trans (by simpa using norm_fst_le ((1 / α) * Real.log z, θ)) (hR _ hmem)
      obtain ⟨hl, hu⟩ := abs_le.mp hbnd
      have hmul : α * ((1 / α) * Real.log z) = Real.log z := by
        rw [← mul_assoc, one_div, mul_inv_cancel₀ (ne_of_gt hα), one_mul]
      have hlogl : -(α * R) ≤ Real.log z :=
        calc -(α * R) = α * (-R) := by ring
          _ ≤ α * ((1 / α) * Real.log z) := mul_le_mul_of_nonneg_left hl hα.le
          _ = Real.log z := hmul
      have hlogu : Real.log z ≤ α * R :=
        calc Real.log z = α * ((1 / α) * Real.log z) := hmul.symm
          _ ≤ α * R := mul_le_mul_of_nonneg_left hu hα.le
      have hzI1 : Lz < z := by
        rw [hLz, ← Real.exp_log hz]
        exact Real.exp_lt_exp.mpr (by nlinarith [hα, hlogl])
      have hzI2 : z < Uz := by
        rw [hUz, ← Real.exp_log hz]
        exact Real.exp_lt_exp.mpr (by nlinarith [hα, hlogu])
      have hV : IsOpen (Set.Ioo Lz Uz ×ˢ Set.univ) :=
        isOpen_Ioo.prod (isOpen_univ : IsOpen (Set.univ : Set ℝ))
      have hEq : Set.EqOn
          (Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ))
          (Function.uncurry (fun z θ' : ℝ => ψ ((1 / α) * Real.log z) θ'))
          (Set.Ioo Lz Uz ×ˢ Set.univ) := by
        intro q hq
        simp only [Function.uncurry]
        rw [hχz1 q.1 (le_of_lt hq.1.1) (le_of_lt hq.1.2), one_mul]
      have hcongr := bslOp_congr_of_isOpen (α := α) hV hEq
        (show (z, θ) ∈ Set.Ioo Lz Uz ×ˢ Set.univ from ⟨⟨hzI1, hzI2⟩, trivial⟩)
      simp only [Function.uncurry] at hcongr
      rw [hcongr, hce]
    · -- off the support of `ψ` the pull-back vanishes near `(z,θ)`, so both sides are `0`
      have hnear : Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ)
          =ᶠ[𝓝 (z, θ)] 0 := by
        have hcont : ContinuousAt (fun q : ℝ × ℝ => ((1 / α) * Real.log q.1, q.2)) (z, θ) := by
          have hlog : ContinuousAt (fun q : ℝ × ℝ => Real.log q.1) (z, θ) :=
            ContinuousAt.log (f := fun q : ℝ × ℝ => q.1) continuousAt_fst
              (by simpa using ne_of_gt hz)
          exact ContinuousAt.prodMk (ContinuousAt.const_mul hlog (1 / α)) continuousAt_snd
        have hU : (fun q : ℝ × ℝ => ((1 / α) * Real.log q.1, q.2)) ⁻¹'
            (tsupport (Function.uncurry ψ))ᶜ ∈ 𝓝 (z, θ) :=
          hcont.preimage_mem_nhds ((isClosed_tsupport _).isOpen_compl.mem_nhds hmem)
        filter_upwards [hU] with q hq
        have h0 : ψ ((1 / α) * Real.log q.1) q.2 = 0 := by
          have hval := (notMem_tsupport_iff_eventuallyEq.mp hq).eq_of_nhds
          simpa [Function.uncurry] using hval
        have hval : Function.uncurry (fun z θ : ℝ => χz z * ψ ((1 / α) * Real.log z) θ) q = (0 : ℝ) := by
          simp only [Function.uncurry, h0, mul_zero]
        simpa using hval
      exact (bslOp_eq_zero_of_notMem_tsupport (notMem_tsupport_iff_eventuallyEq.mpr hnear)).trans
        (kopDr_eq_zero_of_notMem_tsupport hmem).symm

end Work.EllipticEst.InteriorRegularity.Q0
