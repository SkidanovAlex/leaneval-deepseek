import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.mat_csq_le_components

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The change-of-partition bound for the chart-`l` matrix entry, with the `σ`-ball hypothesis

This is the **`σ`-ball variant** of `Work.Diff.STE.B3.VarCoef.mat_csq_le_components`: the cut-off
`θ` is assumed to be `1` only on the ball of radius `D.σ l` (rather than on the ball of radius
`2 * D.σ l`).

The proof of `mat_csq_le_components` never uses that hypothesis at all: the partition of unity is
subordinate to `tsupport θ`, and the transfer estimates are uniform in `θ` (only `hθsm`, `hθc` and
`hθt` enter).  Hence the same argument yields the strictly stronger statement, reproduced here
with the weakened hypothesis, so that a consumer may use a cut-off `η` with `η = 1` on `‖z‖ ≤ σ l`
only.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3.VarCoef

theorem mat_csq_le_components_sigma
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (s : ℕ) (l : ι₀)
    (θ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hθ : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ l → θ z = 1)
    (hθsm : ContDiff ℝ (⊤ : ℕ∞) θ) (hθc : HasCompactSupport θ)
    (hθt : ∀ z : Fin (Module.finrank ℝ E) → ℝ, z ∈ tsupport θ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ (extChartAt I (D.x₀ l)).target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)),
        (∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R j h a' b')) →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
          ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
            ((θ (z + Work.Diff.STE.iVec m) * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ)
              : ℂ)))))
          ≤ C * ∑ i : ι₀, ∑ a' : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (D.Rper i h a' b')) := by  classical
  -- ## 1. The open cover of `tsupport θ` and a subordinate partition of unity
  have hVopen : IsOpen {z : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target)} :=
    isOpen_interior.preimage (Work.Diff.STE.D.contDiff_flatToE (I := I) (D.x₀ l)).continuous
  have hUopen : ∀ i : ι₀, IsOpen ({z : Fin (Module.finrank ℝ E) → ℝ |
      D.ζ i (D.pt l z) ≠ 0} ∩ {z : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target)}) := by
    intro i
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hz1, hz2⟩
    have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D l z hz2
    have hcont : ContinuousAt (fun y : Fin (Module.finrank ℝ E) → ℝ => D.ζ i (D.pt l y)) z :=
      (((D.hζsm i).contMDiffAt).comp z hpt).continuousAt
    have h1 : {y : Fin (Module.finrank ℝ E) → ℝ | D.ζ i (D.pt l y) ≠ 0} ∈ 𝓝 z :=
      hcont.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hz1)
    exact Filter.mem_of_superset (Filter.inter_mem h1 (hVopen.mem_nhds hz2)) fun y hy => hy
  have hcov : tsupport θ ⊆ ⋃ i : ι₀, ({z : Fin (Module.finrank ℝ E) → ℝ |
      D.ζ i (D.pt l z) ≠ 0} ∩ {z : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target)}) := by
    intro z hz
    obtain ⟨i, hi⟩ : ∃ i : ι₀, D.ζ i (D.pt l z) ≠ 0 := by
      by_contra h
      push_neg at h
      have h0 : ∑ i : ι₀, (D.ζ i (D.pt l z)) ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [h i]; ring
      rw [D.hζsq (D.pt l z)] at h0
      norm_num at h0
    exact Set.mem_iUnion.mpr ⟨i, hi, interiorPt_of_mem_tsupport D l θ hθt hz⟩
  obtain ⟨ρ, hρsm, hρnn, hρts, hρcpt, hρsum⟩ :=
    Work.Diff.STE.B3.exists_partition_compact (tsupport θ) hθc _ hUopen hcov
  -- ## 2. The coefficient function of a single transfer term (indexed by `(a,b)` and the
  --         triple `k = (i,c,d)`)
  set cc : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
      (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun ab k z =>
      θ z * ρ k.1 z * (D.ζ k.1 (D.pt l z))⁻¹
        * (Real.sqrt (D.dens k.1 (Work.Diff.STE.coord (I := I) (D.x₀ k.1) (D.pt l z))))⁻¹
        * (g₀.inner (D.pt l z) (D.e l ab.1 (D.pt l z)) (D.e k.1 k.2.1 (D.pt l z))
          * g₀.inner (D.pt l z) (D.e l ab.2 (D.pt l z)) (D.e k.1 k.2.2 (D.pt l z)))
    with hccdef
  have hccsm : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (cc ab k) := by
    intro ab k
    simpa only [hccdef] using
      Work.Diff.STE.B3.VarCoef.coeff_contDiff (I := I) (M := M) D l ab.1 ab.2 θ (ρ k.1)
        k.1 k.2.1 k.2.2 hθsm (hρsm k.1) (hρts k.1)
  have hccK : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      HasCompactSupport (cc ab k) := by
    intro ab k
    refine IsCompact.of_isClosed_subset hθc (isClosed_tsupport _) ?_
    refine closure_mono ?_
    intro z hz
    rw [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by rw [hccdef]; simp [h0])
  have hccU : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      tsupport (cc ab k) ⊆ {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ interior ((extChartAt I (D.x₀ l)).target) ∧
        D.pt l z ∈ (extChartAt I (D.x₀ k.1)).source} := by
    intro ab k z hz
    have hsub : Function.support (cc ab k) ⊆ Function.support (ρ k.1) := by
      intro y hy
      rw [Function.mem_support] at hy ⊢
      intro h0
      exact hy (by rw [hccdef]; simp [h0])
    have hz' := hρts k.1 (closure_mono hsub hz)
    exact ⟨hz'.2, (D.hζsupp k.1 (D.pt l z) hz'.1).1⟩
  have hgood : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      tsupport (cc ab k) ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D k.1 l := by
    intro ab k z hz
    have hz' := hccU ab k hz
    refine ⟨hz'.1, hz'.2, ?_⟩
    have hIP := isInteriorPoint_of_B3Data D (D.pt l z)
    exact (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := I) (M := M) (H := H)
      (n := ((⊤ : ENat) : WithTop ENat)) (hn := by simp) (e := chartAt H (D.x₀ k.1))
      (he := chart_mem_atlas H (D.x₀ k.1))
      (hx := by rw [← extChartAt_source (I := I) (D.x₀ k.1)]; exact hz'.2)).mp hIP
  -- the same coefficient, read as a `ℂ`-valued amplitude
  set ccC : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
      (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun ab k z => ((cc ab k z : ℝ) : ℂ)
    with hccCdef
  have htsupp_eq : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      tsupport (ccC ab k) = tsupport (cc ab k) := by
    intro ab k
    have h1 : Function.support (ccC ab k) = Function.support (cc ab k) := by
      ext z
      simp only [Function.mem_support, hccCdef]
      exact Complex.ofReal_ne_zero
    simp only [tsupport, h1]

  have hccCsm : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (ccC ab k) := by
    intro ab k
    show ContDiff ℝ (⊤ : ℕ∞) (fun z => ((cc ab k z : ℝ) : ℂ))
    exact (Complex.ofRealCLM.contDiff (n := (⊤ : ℕ∞))).comp (hccsm ab k)

  have hccCK : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      HasCompactSupport (ccC ab k) := by
    intro ab k
    have h2 : IsCompact (closure (Function.support (ccC ab k))) := by
      have h1 : Function.support (ccC ab k) = Function.support (cc ab k) := by
        ext z
        simp only [Function.mem_support, hccCdef]
        exact Complex.ofReal_ne_zero
      rw [h1]
      exact hccK ab k
    simpa only [HasCompactSupport, tsupport] using h2

  -- ## 3. The transfer maps: globalisations of the flat transition map
  have hTex : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      ∃ T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) T ∧
        (∀ z ∈ tsupport (cc ab k), T z =
          Work.Diff.STE.coord (I := I) (D.x₀ k.1) (D.pt l z)) ∧
        (∀ z ∈ tsupport (cc ab k), fderiv ℝ T z =
          fderiv ℝ (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.coord (I := I) (D.x₀ k.1) (D.pt l w)) z) := fun ab k =>
    Work.Diff.STE.B3.VarCoef.exists_transMap_globalisation (I := I) (M := M) D l k.1
      (hccK ab k) (hccU ab k)
  choose T hTsm hTeq hTder using hTex
  -- ## 4. The per-transfer constants (independent of the section `h`)
  have hCex : ∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) V → Work.Diff.STE.Periodic1 V →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (Work.Diff.STE.B3.perTransfer (ccC ab k) (T ab k) V))
          ≤ C * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff V) := by
    intro ab k
    have hinj : Set.InjOn (T ab k) (tsupport (ccC ab k)) := by
      rw [htsupp_eq ab k]
      intro x hx y hy hxy
      have hteq : ∀ w ∈ tsupport (cc ab k),
          T ab k w = Work.Diff.STE.D.tMapFun (I := I) (M := M) D k.1 l w :=
        fun w hw => hTeq ab k w hw
      exact (Work.Diff.STE.B3.injOn_tMapFun_goodSet (I := I) (M := M) D k.1 l)
        (hgood ab k hx) (hgood ab k hy) (by rw [← hteq x hx, ← hteq y hy]; exact hxy)
    have hdet : ∀ z ∈ tsupport (ccC ab k), (fderiv ℝ (T ab k) z).det ≠ 0 := by
      rw [htsupp_eq ab k]
      intro z hz
      rw [hTder ab k z hz]
      exact Work.Diff.STE.B3.tMapFun_det_ne_zero (I := I) (M := M) D k.1 l (hgood ab k hz)
    exact Work.Diff.STE.B3.SymCalcStep8.perTransfer_csq_le_of_support (ccC ab k) (hccCsm ab k)
      (hccCK ab k) (T ab k) (hTsm ab k) hinj hdet s

  choose Ck hCknn hCkb using hCex
  refine ⟨(Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
      * ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck ab k, ?_, ?_⟩
  · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => ?_)
    exact Finset.sum_nonneg fun ab _ => hCknn ab k
  · intro h a b hsmooth
    -- the amplitudes and the pointwise reconstruction identity for this section
    set W : (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
        (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      fun k => D.Rper k.1 h k.2.1 k.2.2 with hWdef
    have hWsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (W k) := fun k =>
      (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D k.1 h
        k.2.1 k.2.2 (hsmooth k.1 k.2.1 k.2.2)).1
    have hWp : ∀ k, Work.Diff.STE.Periodic1 (W k) := fun k =>
      (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D k.1 h
        k.2.1 k.2.2 (hsmooth k.1 k.2.1 k.2.2)).2
    -- ## 5. The pointwise reconstruction identity
    --    `θ w · mat_l(w) = Σ_k cc_k(w) · W_k(T_k w)`, i.e. the chart-`l` matrix entry is recovered
    --    from the transferred components.
    have hpoint : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
        ((θ w * D.mat l h a b w : ℝ) : ℂ)
          = ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ccC (a, b) k w * W k (T (a, b) k w) := by
      intro w
      -- per-chart contribution
      have hgrp : ∀ i : ι₀,
          (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ccC (a, b) (i, c, d) w * W (i, c, d) (T (a, b) (i, c, d) w))
            = ((θ w * ρ i w * D.mat l h a b w : ℝ) : ℂ) := by
        intro i
        by_cases hρ0 : ρ i w = 0
        · -- the chart `i` does not contribute
          have hzero : ∀ c d : Fin (Module.finrank ℝ E),
              ccC (a, b) (i, c, d) w * W (i, c, d) (T (a, b) (i, c, d) w) = 0 := by
            intro c d
            have hz : cc (a, b) (i, c, d) w = 0 := by
              simp only [hccdef]
              rw [hρ0]
              ring
            have hCev : ccC (a, b) (i, c, d) w = ((cc (a, b) (i, c, d) w : ℝ) : ℂ) := rfl
            rw [hCev, hz, Complex.ofReal_zero, zero_mul]
          rw [Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun d _ => hzero c d)), hρ0]
          simp
        · -- the chart `i` contributes: on the support of `ρ i` the transfer is genuine
          have hρmem : w ∈ tsupport (ρ i) :=
            subset_tsupport _ (Function.mem_support.mpr hρ0)
          have hζ : D.ζ i (D.pt l w) ≠ 0 := (hρts i hρmem).1
          have hy : ∀ j : Fin (Module.finrank ℝ E),
              (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) j
                ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
            intro j
            obtain ⟨-, hlt⟩ := D.hζsupp i (D.pt l w) hζ
            have h1 : ‖(Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) j‖
                ≤ ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)‖ :=
              norm_le_pi_norm _ _
            rw [Real.norm_eq_abs] at h1
            have h2 : |(Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) j| < (1 / 2 : ℝ) := by
              have hσ2 := D.hσ2 i
              have hσ := D.hσ i
              linarith
            rw [Set.mem_Ioo, ← abs_lt]
            exact h2
          -- the individual summands: the periodisation collapses onto the single component value
          have hterm : ∀ c d : Fin (Module.finrank ℝ E),
              ccC (a, b) (i, c, d) w * W (i, c, d) (T (a, b) (i, c, d) w)
                = ccC (a, b) (i, c, d) w
                  * ((D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) : ℝ)
                      : ℂ) := by
            intro c d
            by_cases hcc0 : cc (a, b) (i, c, d) w = 0
            · have hCev : ccC (a, b) (i, c, d) w = ((cc (a, b) (i, c, d) w : ℝ) : ℂ) := rfl
              rw [hCev, hcc0, Complex.ofReal_zero, zero_mul, zero_mul]
            · have hmem : w ∈ tsupport (cc (a, b) (i, c, d)) :=
                subset_tsupport _ (Function.mem_support.mpr hcc0)
              have hTw : T (a, b) (i, c, d) w
                  = Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w) :=
                hTeq (a, b) (i, c, d) w hmem
              rw [hTw]
              have hsuppR : Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                    ((D.R i h c d z : ℝ) : ℂ))
                  ⊆ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
                      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
                intro z hz
                rw [Function.mem_support] at hz
                refine D.psi_supp i (Function.mem_support.mpr ?_)
                intro hpsi
                exact hz (by rw [Work.Diff.STE.B3Data.R, hpsi, zero_mul, zero_mul,
                  Complex.ofReal_zero])
              have hcoll : W (i, c, d) (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w))
                  = ((D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) : ℝ)
                      : ℂ) := by
                rw [hWdef]
                exact Work.Diff.STE.periodization_eq_self (f := fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ((D.R i h c d z : ℝ) : ℂ)) hsuppR hy
              rw [hcoll]
          rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => hterm c d))]
          -- the real reconstruction
          have hrew : (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                cc (a, b) (i, c, d) w
                  * D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
              = θ w * ρ i w * D.mat l h a b w := by
            have hbil := Work.Diff.STE.Lead.bil_apply_eq_sum_R (I := I) (M := M) D i
              (D.pt l w) h hζ (D.e l a (D.pt l w)) (D.e l b (D.pt l w))
            have hyσ : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)‖ ≤ 2 * D.σ i := by
              obtain ⟨-, hlt⟩ := D.hζsupp i (D.pt l w) hζ
              have hσ := D.hσ i
              linarith
            have hdens : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) :=
              Work.Diff.STE.B3.dens_pos_of_mem_target D i (D.htarget i _ hyσ)
            have hsne : Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
                ≠ 0 := (Real.sqrt_pos.mpr hdens).ne'
            have hne : D.ζ i (D.pt l w)
                * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w))) ≠ 0 :=
              mul_ne_zero hζ hsne
            have h1 : (∑ c, ∑ d, cc (a, b) (i, c, d) w
                  * D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
                = (θ w * ρ i w
                    * ((D.ζ i (D.pt l w))⁻¹
                      * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i)
                          (D.pt l w))))⁻¹))
                  * (∑ c, ∑ d,
                      (g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e i c (D.pt l w))
                          * g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e i d (D.pt l w)))
                        * D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w))) := by
              rw [show (∑ c, ∑ d, cc (a, b) (i, c, d) w
                    * D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
                  = ∑ c, ∑ d, (θ w * ρ i w
                      * ((D.ζ i (D.pt l w))⁻¹
                        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i)
                            (D.pt l w))))⁻¹))
                      * ((g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e i c (D.pt l w))
                          * g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e i d (D.pt l w)))
                        * D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
                  from Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
                    simp only [hccdef]; ring]
              simp only [Finset.mul_sum]
            have h2 : (∑ c, ∑ d,
                    (g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e i c (D.pt l w))
                        * g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e i d (D.pt l w)))
                      * D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
                = D.ζ i (D.pt l w)
                    * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
                    * D.mat l h a b w := by
              have hS : (∑ c, ∑ d,
                    (g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e i c (D.pt l w))
                        * g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e i d (D.pt l w)))
                      * D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
                  = ∑ c, ∑ d, D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w))
                      * g₀.inner (D.pt l w) (D.e l a (D.pt l w)) (D.e i c (D.pt l w))
                      * g₀.inner (D.pt l w) (D.e l b (D.pt l w)) (D.e i d (D.pt l w)) := by
                apply Finset.sum_congr rfl; intro c _
                apply Finset.sum_congr rfl; intro d _
                ring
              rw [show D.mat l h a b w
                    = h (D.pt l w) (D.e l a (D.pt l w)) (D.e l b (D.pt l w)) from rfl]
              rw [hS, hbil, mul_inv_cancel_left₀ hne]
            have hinv : (D.ζ i (D.pt l w))⁻¹
                * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w))))⁻¹
                = (D.ζ i (D.pt l w)
                  * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w))))⁻¹ := by
              rw [mul_comm (D.ζ i (D.pt l w))⁻¹
                  (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w))))⁻¹,
                ← mul_inv_rev]
            rw [h1, h2, mul_assoc (θ w * ρ i w)
                ((D.ζ i (D.pt l w))⁻¹
                  * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w))))⁻¹)
                (D.ζ i (D.pt l w)
                  * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)))
                  * D.mat l h a b w),
              hinv, inv_mul_cancel_left₀ hne]
          -- lift the reconstruction to `ℂ`
          have hcast : (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                ccC (a, b) (i, c, d) w
                  * ((D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) : ℝ)
                      : ℂ))
              = ((∑ c, ∑ d, cc (a, b) (i, c, d) w
                  * D.R i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) : ℝ) : ℂ) := by
            rw [ofReal_sum₂]
            apply Finset.sum_congr rfl; intro c _
            apply Finset.sum_congr rfl; intro d _
            have hCev : ccC (a, b) (i, c, d) w = ((cc (a, b) (i, c, d) w : ℝ) : ℂ) := rfl
            rw [hCev, ← Complex.ofReal_mul]
          rw [hcast, hrew]
      -- split the sum over `κ = ι₀ × (Fin n × Fin n)`
      have hsplit : (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ccC (a, b) k w * W k (T (a, b) k w))
          = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ccC (a, b) (i, c, d) w * W (i, c, d) (T (a, b) (i, c, d) w) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fintype.sum_prod_type]
      have hkey : (∑ i : ι₀, θ w * ρ i w * D.mat l h a b w) = θ w * D.mat l h a b w := by
        by_cases hw : w ∈ tsupport θ
        · rw [← Finset.sum_mul, ← Finset.mul_sum, hρsum w hw, mul_one]
        · have hθ0 : θ w = 0 := by
            by_contra hh
            exact hw (subset_tsupport _ (Function.mem_support.mpr hh))
          simp [hθ0]
      rw [hsplit, Finset.sum_congr rfl (fun i _ => hgrp i)]
      rw [← Complex.ofReal_sum]
      rw [hkey]
    -- ## 6. The periodisation identity
    have hperid :
        (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
              ((θ (z + Work.Diff.STE.iVec m)
                * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))))
          = fun z => ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k) z := by
      funext z
      obtain ⟨r, hr⟩ := hθc.isBounded.subset_ball (0 : Fin (Module.finrank ℝ E) → ℝ)
      set N : ℕ := ⌈‖z‖ + r⌉₊ + 1 with hNdef
      have hNgt : ‖z‖ + r < (N : ℝ) := by
        have h1 : ‖z‖ + r ≤ (⌈‖z‖ + r⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈‖z‖ + r⌉₊ + 1 : ℕ) : ℝ) = (⌈‖z‖ + r⌉₊ : ℝ) + 1 := by push_cast; ring
        rw [hNdef, h2]
        linarith
      set S : Finset (Fin (Module.finrank ℝ E) → ℤ) :=
        Fintype.piFinset (fun _ : Fin (Module.finrank ℝ E) =>
          Finset.Icc (-((N : ℤ))) ((N : ℤ))) with hSdef
      have hzero : ∀ (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
          (m : Fin (Module.finrank ℝ E) → ℤ), m ∉ S →
          ccC (a, b) k (z + Work.Diff.STE.iVec m)
            * W k (T (a, b) k (z + Work.Diff.STE.iVec m)) = 0 := by
        intro k m hm
        obtain ⟨j, hj⟩ := exists_abs_gt_of_not_mem_piFinset (n := Module.finrank ℝ E)
          (N := N) (by rwa [hSdef] at hm)
        have hnotmem : z + Work.Diff.STE.iVec m ∉ tsupport θ := by
          intro hmem
          have h1 : ‖z + Work.Diff.STE.iVec m‖ < r := by
            have h := hr hmem
            rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
            exact h
          have h2 : ‖Work.Diff.STE.iVec m‖ ≤ ‖z + Work.Diff.STE.iVec m‖ + ‖z‖ := by
            calc ‖Work.Diff.STE.iVec m‖ = ‖(z + Work.Diff.STE.iVec m) - z‖ := by
                  rw [add_sub_cancel_left]
              _ ≤ ‖z + Work.Diff.STE.iVec m‖ + ‖z‖ := norm_sub_le _ _
          have h3 : (N : ℝ) < |((m j : ℤ) : ℝ)| := hj
          have h4 : |((m j : ℤ) : ℝ)| ≤ ‖Work.Diff.STE.iVec m‖ := by
            have h := norm_le_pi_norm (Work.Diff.STE.iVec m) j
            simpa [Work.Diff.STE.iVec] using h
          linarith
        have hθ0 : θ (z + Work.Diff.STE.iVec m) = 0 := by
          by_contra hh
          exact hnotmem (subset_tsupport _ (Function.mem_support.mpr hh))
        have hcc0 : cc (a, b) k (z + Work.Diff.STE.iVec m) = 0 := by
          simp only [hccdef]
          rw [hθ0]
          ring
        have hCev : ccC (a, b) k (z + Work.Diff.STE.iVec m)
            = ((cc (a, b) k (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) := rfl
        rw [hCev, hcc0, Complex.ofReal_zero, zero_mul]
      have hL : ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
            ((θ (z + Work.Diff.STE.iVec m)
              * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)))
          = ∑' m : Fin (Module.finrank ℝ E) → ℤ,
              ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                ccC (a, b) k (z + Work.Diff.STE.iVec m)
                  * W k (T (a, b) k (z + Work.Diff.STE.iVec m)) :=
        tsum_congr (fun m => hpoint (z + Work.Diff.STE.iVec m))
      have hR : (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k) z)
          = ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              ∑' m : Fin (Module.finrank ℝ E) → ℤ,
                ccC (a, b) k (z + Work.Diff.STE.iVec m)
                  * W k (T (a, b) k (z + Work.Diff.STE.iVec m)) := by
        apply Finset.sum_congr rfl
        intro k _
        rfl
      rw [hL, hR, Work.Diff.STE.B3.tsum_finset_sum_eq (S := S)
        (f := fun (k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
            (m : Fin (Module.finrank ℝ E) → ℤ) =>
          ccC (a, b) k (z + Work.Diff.STE.iVec m)
            * W k (T (a, b) k (z + Work.Diff.STE.iVec m))) hzero]
    -- ## 7. The `CSq` chain
    have hpersm : ∀ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ContDiff ℝ (⊤ : ℕ∞)
          (Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k)) := fun k =>
      (Work.Diff.STE.B3.SymCalcStep8.perTransfer_contDiff_periodic_of (ccC (a, b) k)
        (hccCsm (a, b) k) (hccCK (a, b) k) (T (a, b) k) (hTsm (a, b) k) (W k) (hWsm k)
        (hWp k)).1
    have hperp : ∀ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        Work.Diff.STE.Periodic1
          (Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k)) := fun k =>
      (Work.Diff.STE.B3.SymCalcStep8.perTransfer_contDiff_periodic_of (ccC (a, b) k)
        (hccCsm (a, b) k) (hccCK (a, b) k) (T (a, b) k) (hTsm (a, b) k) (W k) (hWsm k)
        (hWp k)).2
    have hsummable : ∀ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        Summable fun m : Fin (Module.finrank ℝ E) → ℤ =>
          Work.Diff.STE.wt m ^ s
            * ‖Work.Diff.STE.fourierCoeff
                (Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k)) m‖ ^ 2 :=
      fun k => Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _
        (hpersm k) (hperp k) s
    have hcoeff : Work.Diff.STE.fourierCoeff (fun z =>
          ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k) z)
        = fun m => ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.fourierCoeff
              (Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k)) m := by
      funext m
      exact Work.Diff.STE.B3.fourierCoeff_finset_sum_of_continuous
        (fun k => Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k))
        (fun k => (hpersm k).continuous) m
    have hstep1 : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
          ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k) z))
        ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
          * ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
                (Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k))) := by
      rw [hcoeff]
      exact Work.Diff.STE.B3.CSq_sum_le s
        (fun k => Work.Diff.STE.fourierCoeff
          (Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k))) hsummable
    have hstep2 : (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
              (Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k))))
        ≤ ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Ck (a, b) k * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k)) :=
      Finset.sum_le_sum fun k _ => hCkb (a, b) k (W k) (hWsm k) (hWp k)
    have hstep3 : (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Ck (a, b) k * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k)))
        ≤ (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck (a, b) k)
          * (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k))) := by
      calc (∑ k, Ck (a, b) k * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k)))
          ≤ ∑ k, Ck (a, b) k
              * (∑ k' : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                  Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k'))) :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
              (Finset.single_le_sum
                (f := fun k' : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
                  Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k')))
                (fun k' _ => Work.Diff.STE.CSq_nonneg s _)
                (Finset.mem_univ k)) (hCknn (a, b) k)
        _ = (∑ k, Ck (a, b) k)
              * (∑ k' : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                  Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k'))) := by
            rw [Finset.sum_mul]
    have hstep4 : (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Ck (a, b) k)
        ≤ ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            ∑ ab' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck ab' k := by
      refine Finset.sum_le_sum fun k _ => ?_
      exact Finset.single_le_sum (fun ab' _ => hCknn ab' k) (Finset.mem_univ (a, b))
    have hreindex : (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k)))
        = ∑ i : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
            Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (D.Rper i h a' b')) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]
    calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
            ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
              ((θ (z + Work.Diff.STE.iVec m)
                * D.mat l h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)))))
        = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z =>
            ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k) z)) := by
          rw [hperid]
      _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
            * ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
                  (Work.Diff.STE.B3.perTransfer (ccC (a, b) k) (T (a, b) k) (W k))) := hstep1
      _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
            * ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                Ck (a, b) k * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k)) :=
          mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
            * ((∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck (a, b) k)
              * (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                  Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k)))) :=
          mul_le_mul_of_nonneg_left hstep3 (by positivity)
      _ ≤ (Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
            * ((∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                  ∑ ab' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck ab' k)
              * (∑ i : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
                  Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (D.Rper i h a' b')))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hB : (0 : ℝ) ≤ ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
              Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k)) :=
            Finset.sum_nonneg fun k _ => Work.Diff.STE.CSq_nonneg s _
          calc (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck (a, b) k)
                * (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k)))
              ≤ (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    ∑ ab' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck ab' k)
                * (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W k))) :=
                mul_le_mul_of_nonneg_right hstep4 hB
            _ = (∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                    ∑ ab' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck ab' k)
                * (∑ i : ι₀, ∑ a' : Fin (Module.finrank ℝ E),
                    ∑ b' : Fin (Module.finrank ℝ E),
                      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (D.Rper i h a' b'))) := by
                rw [hreindex]
      _ = ((Fintype.card (ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) : ℝ)
            * ∑ k : ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
                ∑ ab' : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Ck ab' k)
          * (∑ i : ι₀, ∑ a' : Fin (Module.finrank ℝ E), ∑ b' : Fin (Module.finrank ℝ E),
              Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (D.Rper i h a' b'))) := by
          ring

end Work.Diff.STE.B3.VarCoef
