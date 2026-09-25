import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.gagliardoNirenbergGeomMean
import Submission.Work.NN.Core.gnsLipschitz

namespace Work.NN.Core.Lev

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-! ## Auxiliary lemmas

The complexification `W = Complex.ofReal ∘ g` of a real-valued function `g` preserves both the
`Lᵖ`-(semi)norm of `g` and the `L²`-norm of its Fréchet derivative (up to the harmless factor
`‖Complex.ofRealCLM‖ ≤ 1`), so the `ℂ`-valued Gagliardo–Nirenberg inequality of
`Work.NN.Core.gnsLipschitz` transfers to real-valued functions. -/

/-- The derivative of the complexification of a real-valued function. -/
private lemma fderiv_ofReal_comp {n : ℕ} {g : Work.NN.Core.Cn n → ℝ} {z : Work.NN.Core.Cn n}
    (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun w => ((g w : ℝ) : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ g z) := by
  have h : HasFDerivAt (fun w => ((g w : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ g z)) z := by
    have h' := (Complex.ofRealCLM.hasFDerivAt (x := g z)).comp z hg.hasFDerivAt
    convert h' using 1
    ext w
    rfl
  exact h.fderiv

/-- Composition with the inclusion `ℝ → ℂ` does not increase the operator norm. -/
private lemma norm_ofRealCLM_comp_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] ℝ) : ‖Complex.ofRealCLM.comp A‖ ≤ ‖A‖ := by
  have h1 : ‖Complex.ofRealCLM‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => ?_
    rw [Complex.ofRealCLM_apply, Complex.norm_real, one_mul]
  calc ‖Complex.ofRealCLM.comp A‖ ≤ ‖Complex.ofRealCLM‖ * ‖A‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖A‖ := by gcongr
    _ = ‖A‖ := one_mul _

/-- `eLpNorm` is unchanged by complexifying a real-valued function. -/
private lemma eLpNorm_ofReal_comp {n : ℕ} {g : Work.NN.Core.Cn n → ℝ} (hcont : Continuous g)
    (p : ℝ≥0∞) :
    eLpNorm (fun z => ((g z : ℝ) : ℂ)) p volume = eLpNorm g p volume := by
  refine eLpNorm_congr_norm_ae (f := fun z => ((g z : ℝ) : ℂ)) (g := g)
    ((Complex.continuous_ofReal.comp hcont).aestronglyMeasurable) hcont.aestronglyMeasurable ?_
  filter_upwards with z
  exact Complex.norm_real (g z)

end

/-- Gagliardo--Nirenberg geometric-mean inequality for real-valued functions that are Lipschitz on
the polydisc `polydisc 0 ρ` and whose topological support lies in it.  `Cn n = Fin n → ℂ` has real
dimension `2n`, so the exponent is `2 * conjExponent (2n) = 4n/(2n-1)`.

Hints: `tsupport g ⊆ polydisc 0 ρ` with the polydisc open and bounded makes `g` vanish on a
neighbourhood of `∂(polydisc 0 ρ)` and outside, so `g` extends to a *globally* Lipschitz function with
compact support (a valid global Lipschitz constant is `max L (M/δ)`, `M = |g 0| + L * (max radius)`,
`δ = dist (tsupport g) (polydisc 0 ρ)ᶜ > 0`); then complexify and use the corresponding statement for
`Cn n → ℂ`.  The file `Submission/Work/NN/Core/gnsLipschitz.lean` contains a (currently non-compiling,
`sorry`-containing) proof template of exactly that ℂ-valued globally-Lipschitz statement, obtained from
`Work.NN.Core.gagliardoNirenbergGeomMean` by mollification; it can be repaired/adapted.  Do NOT import
that file (it does not build). -/
theorem gnsLipschitzOn {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : NNReal) (ρ : Fin n → ℝ) (g : Work.NN.Core.Cn n → ℝ),
        LipschitzOnWith L g (Work.CR.Flat.polydisc 0 ρ) →
        tsupport g ⊆ Work.CR.Flat.polydisc 0 ρ →
        (MeasureTheory.eLpNorm g
            ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))) ^ 2
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g 2 MeasureTheory.volume *
              MeasureTheory.eLpNorm (fderiv ℝ g) 2 MeasureTheory.volume := by
  classical
  obtain ⟨C₀, hC₀pos, hGNS⟩ := Work.NN.Core.gnsLipschitz hn
  refine ⟨C₀, hC₀pos, ?_⟩
  intro L ρ g hLip hsupp
  set P : Set (Work.NN.Core.Cn n) := Work.CR.Flat.polydisc 0 ρ with hP
  have hLipP : LipschitzOnWith L g P := hLip
  have hsuppP : tsupport g ⊆ P := hsupp
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 ρ
  -- `g` vanishes outside the polydisc, hence outside its own (closed) support
  have hzero_out : ∀ z, z ∉ P → g z = 0 := by
    intro z hz
    by_contra hne
    exact hz (hsuppP (subset_tsupport g (Function.mem_support.mpr hne)))
  have hzero_ts : ∀ z, z ∉ tsupport g → g z = 0 := by
    intro z hz
    by_contra hne
    exact hz (subset_tsupport g (Function.mem_support.mpr hne))
  -- the polydisc is bounded, so `tsupport g` is compact
  set R : ℝ := ∑ j : Fin n, max (ρ j) 0 with hR
  have hRnn : 0 ≤ R := Finset.sum_nonneg fun j _ => le_max_right _ _
  have hsub_ball : P ⊆ Metric.closedBall (0 : Work.NN.Core.Cn n) R := by
    intro z hz
    have hz' : ∀ j, ‖z j‖ < ρ j := by
      intro j
      simpa using hz j
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ ∑ j, ‖z j‖ :=
          pi_norm_le_iff_of_nonneg (by positivity) |>.mpr fun j =>
            Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ j, max (ρ j) 0 := Finset.sum_le_sum fun j _ =>
            le_trans (le_of_lt (hz' j)) (le_max_left _ _)
  have hnorm_le : ∀ z ∈ P, ‖z‖ ≤ R := fun z hz => by
    have h := Metric.mem_closedBall.mp (hsub_ball hz)
    rwa [dist_zero_right] at h
  have hKc : IsCompact (tsupport g) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport g)
      ((Metric.isBounded_closedBall (x := (0 : Work.NN.Core.Cn n)) (r := R)).subset
        (hsuppP.trans hsub_ball))
  -- `g` is globally Lipschitz
  have hglob : ∃ K : NNReal, LipschitzWith K g := by
    by_cases hKne : (tsupport g).Nonempty
    · obtain ⟨b, hbK⟩ := hKne
      have hbP : b ∈ P := hsuppP hbK
      obtain ⟨δ, hδpos, hδsub⟩ := hKc.exists_cthickening_subset_open hPopen hsuppP
      set M : ℝ := |g b| + (L : ℝ) * (2 * R) with hM
      have hM0 : 0 ≤ M := by
        rw [hM]; positivity
      have hbound : ∀ z ∈ tsupport g, |g z| ≤ M := by
        intro z hzK
        have hzP : z ∈ P := hsuppP hzK
        have hdist : ‖z - b‖ ≤ 2 * R := by
          calc ‖z - b‖ ≤ ‖z‖ + ‖b‖ := norm_sub_le _ _
            _ ≤ R + R := add_le_add (hnorm_le z hzP) (hnorm_le b hbP)
            _ = 2 * R := by ring
        have h2 : |g z - g b| ≤ (L : ℝ) * (2 * R) := by
          have h1 := hLipP.dist_le_mul z hzP b hbP
          rw [Real.dist_eq, dist_eq_norm] at h1
          calc |g z - g b| ≤ (L : ℝ) * ‖z - b‖ := h1
            _ ≤ (L : ℝ) * (2 * R) := mul_le_mul_of_nonneg_left hdist L.coe_nonneg
        have h3 : |g z| ≤ |g z - g b| + |g b| := by
          have h4 := abs_add_le (g z - g b) (g b)
          rwa [sub_add_cancel] at h4
        calc |g z| ≤ |g z - g b| + |g b| := h3
          _ ≤ (L : ℝ) * (2 * R) + |g b| := add_le_add h2 le_rfl
          _ = M := by rw [hM]; ring
      set A : ℝ := max (L : ℝ) (M / δ) with hA
      have hA0 : 0 ≤ A := le_trans L.coe_nonneg (le_max_left _ _)
      refine ⟨⟨A, hA0⟩, LipschitzWith.of_dist_le_mul ?_⟩
      show ∀ x y, dist (g x) (g y) ≤ A * dist x y
      have key1 : ∀ x ∈ P, ∀ y ∉ P, dist (g x) (g y) ≤ A * dist x y := by
        intro x hxP y hyP
        have hy0 : g y = 0 := hzero_out y hyP
        by_cases hxK : x ∈ tsupport g
        · have hxM : |g x| ≤ M := hbound x hxK
          have hδle : δ ≤ dist x y := by
            by_contra hle
            have hlt : dist x y < δ := not_le.mp hle
            have hmem : y ∈ Metric.cthickening δ (tsupport g) :=
              Metric.thickening_subset_cthickening δ _
                (Metric.mem_thickening_iff.mpr ⟨x, hxK, by rw [dist_comm]; exact hlt⟩)
            exact hyP (hδsub hmem)
          calc dist (g x) (g y) = |g x| := by rw [hy0, Real.dist_eq, sub_zero]
            _ ≤ M := hxM
            _ = (M / δ) * δ := (div_mul_cancel₀ M (ne_of_gt hδpos)).symm
            _ ≤ (M / δ) * dist x y := mul_le_mul_of_nonneg_left hδle (div_nonneg hM0 hδpos.le)
            _ ≤ A * dist x y := mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
        · have hx0 : g x = 0 := hzero_ts x hxK
          rw [hx0, hy0, dist_self]
          exact mul_nonneg hA0 dist_nonneg
      have key2 : ∀ x ∈ P, ∀ y ∈ P, dist (g x) (g y) ≤ A * dist x y := by
        intro x hx y hy
        calc dist (g x) (g y) ≤ (L : ℝ) * dist x y := hLipP.dist_le_mul x hx y hy
          _ ≤ A * dist x y := mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
      have key3 : ∀ x ∉ P, ∀ y ∉ P, dist (g x) (g y) ≤ A * dist x y := by
        intro x hx y hy
        rw [hzero_out x hx, hzero_out y hy, dist_self]
        exact mul_nonneg hA0 dist_nonneg
      intro x y
      by_cases hx : x ∈ P
      · by_cases hy : y ∈ P
        · exact key2 x hx y hy
        · exact key1 x hx y hy
      · by_cases hy : y ∈ P
        · simpa [dist_comm] using key1 y hy x hx
        · exact key3 x hx y hy
    · rw [not_nonempty_iff_eq_empty] at hKne
      have hg0 : ∀ z, g z = 0 := fun z => by
        by_contra hne
        have hmem : z ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hne)
        rw [hKne] at hmem
        exact hmem
      refine ⟨0, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
      simp [hg0]
  obtain ⟨K, hK⟩ := hglob
  set W : Work.NN.Core.Cn n → ℂ := fun z => ((g z : ℝ) : ℂ) with hW
  have hWK : LipschitzWith K W := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    show dist (((g x : ℝ) : ℂ)) (((g y : ℝ) : ℂ)) ≤ (K : ℝ) * dist x y
    rw [Complex.isometry_ofReal.dist_eq]
    exact hK.dist_le_mul x y
  have hWcs : HasCompactSupport W := by
    have hcsg : HasCompactSupport g := hKc
    have hs : Function.support W = Function.support g := by
      ext z
      rw [Function.mem_support, Function.mem_support, hW]
      exact Complex.ofReal_ne_zero
    have hts : tsupport W = tsupport g := by
      simp only [tsupport, hs]
    show IsCompact (tsupport W)
    rw [hts]
    exact hcsg
  have hq : eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)) volume
      = eLpNorm g ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)) volume := by
    rw [hW]
    exact eLpNorm_ofReal_comp hK.continuous _
  have h2 : eLpNorm W 2 volume = eLpNorm g 2 volume := by
    rw [hW]
    exact eLpNorm_ofReal_comp hK.continuous 2
  have hfd_eq : ∀ᵐ z ∂(volume : Measure (Work.NN.Core.Cn n)),
      fderiv ℝ W z = Complex.ofRealCLM.comp (fderiv ℝ g z) := by
    filter_upwards [hK.ae_differentiableAt (μ := volume)] with z hz
    rw [hW]
    exact fderiv_ofReal_comp hz
  have h3 : eLpNorm (fderiv ℝ W) 2 volume ≤ eLpNorm (fderiv ℝ g) 2 volume := by
    refine eLpNorm_mono_ae (f := fderiv ℝ W) (g := fderiv ℝ g)
      ((measurable_fderiv ℝ W).aestronglyMeasurable) ?_
    filter_upwards [hfd_eq] with z hz
    rw [hz]
    exact norm_ofRealCLM_comp_le (fderiv ℝ g z)
  have hgns := hGNS K W hWK hWcs
  calc (eLpNorm g ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)) volume) ^ 2
      = (eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)) volume) ^ 2 := by
        rw [hq]
    _ ≤ ENNReal.ofReal C₀ * eLpNorm W 2 volume * eLpNorm (fderiv ℝ W) 2 volume := hgns
    _ ≤ ENNReal.ofReal C₀ * eLpNorm g 2 volume * eLpNorm (fderiv ℝ g) 2 volume := by
        rw [h2]
        gcongr

end Work.NN.Core.Lev
