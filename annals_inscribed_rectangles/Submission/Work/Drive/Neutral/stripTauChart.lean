import Mathlib
import Submission.Work.Drive.Neutral.stripTauData
import Submission.Work.Drive.contMDiffAt_confPiece_mk
import Submission.Work.Drive.cappedPlaneFamily
import Submission.Work.Drive.exists_contDiff_strip_doubledDir
import Submission.Work.Drive.exists_contMDiffAt_stripChart_closed

/-!
# The `τ = s²` chart of the configuration strip

`Submission/Work/Drive/TAU_CHART_STATUS.md` explains why a chart of the configuration Möbius band `M`
must use `τ = s²` (the square of the chord-opening parameter) as its transverse coordinate.  This
file carries out the construction away from the gluing curve.

* `Work.Drive.Neutral.symmD_norm_lt_one`: off the seam (`s ≠ 0`, `|s| < π/2`) the capping disk coordinate of
  a chord is *strictly* inside the unit disk — this is what makes the "honest branch" of the chart a
  *neighbourhood* of the point;
* `Work.Drive.Neutral.tauData` clamps the factorised data `G` into the side conditions of the configuration
  piece (`r > 0`, `‖d‖ ≤ 1`) so that the chart is globally defined, and `Work.Drive.Neutral.stripTauChart` is
  the resulting chart;
* `Work.Drive.Neutral.contMDiffOn_stripTauChart`: if a `C^∞` map `G` reproduces the symmetric data on the
  half-plane `{0 < τ < π²}`, then the chart is `C^∞` on `{0 < τ < π²/4}` — the *strip side* of the
  charted surface;
* `Work.Drive.Neutral.stripTauChart_eq_stripChart`: on `τ = s²` (`0 < |s| < π/2`) the chart is the strip
  chart of `Work.Drive.stripChart` at the parameter `(σ+s, σ-s)`, i.e. its image is `M`.

**The seam is *not* covered, and it cannot be.**  Along the strip the squared disk radius is
`1 - ‖d (σ,τ)‖² = ‖chord (σ,√τ)‖²/r² ≈ 4 τ ‖γ'‖²/‖γ‖²`, so `‖d‖ - 1` *changes sign* across the
gluing curve and any `C^∞` extension of the data to `τ < 0` has `‖d‖ > 1` just below the seam;
therefore no chart of `M` alone, with the side conditions of `ConfigPiece`, can be smooth *at* the
seam.  This is the precise sense in which the capped plane must be presented as the **sum of two
chains** (the strip for `τ ≥ 0`, the cap for the other side), as recorded in `CREASE_CORRECTION.md`
§7 — and it shows that the "crease" is forced, not an artefact.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff Topology
open Classical
open Submission.Configuration Submission.Geometry Submission.Collision

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## The disk coordinate is strictly inside the disk away from the seam -/

/-- The divided difference of the symmetric family does not vanish when `0 < |s| < π/2`. -/
lemma symmWC_ne_zero_of_lt (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {σ s : ℝ} (hspi : |s| < Real.pi / 2) : symmWC γ σ s ≠ 0 := by
  have hw : secantW (curve γ) (σ + s, σ - s) ≠ 0 := by
    refine stripSecantW_ne_zero γ hγ ?_
    have : |(σ + s) - (σ - s)| = 2 * |s| := by
      rw [show (σ + s) - (σ - s) = 2 * s from by ring, abs_mul]
      norm_num
    rw [this]
    linarith [abs_nonneg s]
  intro h
  exact hw (symmC_eq_zero_iff.mp (by simpa only [symmWC] using h))

/-- The chord of the symmetric family does not vanish when `0 < |s| < π/2` (its two endpoints are
distinct points of the curve). -/
lemma symmChordC_ne_zero (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {σ s : ℝ} (hs : s ≠ 0) (hspi : |s| < Real.pi / 2) : symmChordC γ σ s ≠ 0 := by
  have hw' : symmWC γ σ s ≠ 0 := symmWC_ne_zero_of_lt hγ hspi
  have hchord : chordC γ (σ + s, σ - s) = ((2 * s : ℝ) : ℂ) * symmWC γ σ s := by
    have hsub : γ (Circle.exp (σ + s)) - γ (Circle.exp (σ - s))
        = ((2 * s : ℝ)) • secantW (curve γ) (σ + s, σ - s) := by
      have h' := sub_eq_smul_secantW (contDiff_curve γ hγ) (σ + s) (σ - s)
      rwa [show σ + s - (σ - s) = 2 * s from by ring] at h'
    rw [chordC_eq_symmC, hsub, symmC_smul, symmWC]
  rw [show symmChordC γ σ s = chordC γ (σ + s, σ - s) from rfl, hchord]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) hw'

/-- **Away from the seam the capping disk coordinate is strictly inside the unit disk.**  This is the
statement that the honest branch of the `τ`-chart is used on a *neighbourhood* of a point with
`τ > 0`. -/
lemma symmD_norm_lt_one (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {σ s : ℝ} (hs : s ≠ 0) (hspi : |s| < Real.pi / 2) : ‖symmD γ σ s‖ < 1 := by
  have hchord : symmChordC γ σ s ≠ 0 := symmChordC_ne_zero hγ hs hspi
  have hpos : 0 < Complex.normSq (symmChordC γ σ s) := Complex.normSq_pos.mpr hchord
  have hmid : 0 ≤ (symmMid γ σ s).1 ^ 2 + (symmMid γ σ s).2 ^ 2 := by positivity
  have hApos : 0 < symmA γ σ s := by
    simp only [symmA]; linarith
  have hnum : (↑(symmMid γ σ s).1 : ℂ) + (↑(symmMid γ σ s).2 : ℂ) * Complex.I
      = symmC (symmMid γ σ s) := by
    refine Complex.ext ?_ ?_ <;> simp [symmC]
  have hnorm : ‖symmD γ σ s‖ = Real.sqrt ((symmMid γ σ s).1 ^ 2 + (symmMid γ σ s).2 ^ 2)
      / Real.sqrt (symmA γ σ s) := by
    rw [symmD, hnum, symmR, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_symmC]
    simp only [eucNorm, eucDot_self]
  have hlt : (symmMid γ σ s).1 ^ 2 + (symmMid γ σ s).2 ^ 2 < symmA γ σ s := by
    simp only [symmA]; linarith
  rw [hnorm, div_lt_one (Real.sqrt_pos.mpr hApos)]
  exact Real.sqrt_lt_sqrt hmid hlt

/-! ## The clamped data and the chart -/

/-- A fixed triple of configuration data at the diagonal point `σ₀` (`s = 0`), satisfying the side
conditions of the configuration piece; it is used wherever the clamped data is not the honest strip
data. -/
def tauBase (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (σ₀ : ℝ) :
    ℝ × ℂ × UnitAddCircle :=
  (symmR γ σ₀ 0, symmD γ σ₀ 0,
    circOf (symmE γ σ₀ 0) (symmE_norm γ σ₀ 0 (symmWC_zero_ne_zero hγ σ₀)))

lemma tauBase_pos (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ₀ : ℝ) : 0 < (tauBase hγ σ₀).1 :=
  symmR_pos hγne σ₀ 0

lemma tauBase_norm_le_one (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (σ₀ : ℝ) : ‖(tauBase hγ σ₀).2.1‖ ≤ 1 :=
  symmD_norm_le_one γ σ₀ 0

/-- The unit normalisation of the factorised direction: `circOf`'s argument.  It is `1` where the
direction vanishes and `z/‖z‖` elsewhere, hence has modulus one everywhere; on the set where `z` has
modulus one it is `z` itself. -/
def tauE (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (q : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  if (G q).2.2 = 0 then 1 else (G q).2.2 / (((‖(G q).2.2‖ : ℝ)) : ℂ)

lemma tauE_norm (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (q : EuclideanSpace ℝ (Fin 2)) :
    ‖tauE G q‖ = 1 := by
  rw [tauE]
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr h)]

/-- On the set where the factorised direction has unit modulus, `tauE` is that direction. -/
lemma tauE_eq_of_norm_eq_one {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {q : EuclideanSpace ℝ (Fin 2)} (h3 : ‖(G q).2.2‖ = 1) : tauE G q = (G q).2.2 := by
  have hne : (G q).2.2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at h3
    norm_num at h3
  rw [tauE, if_neg hne, h3]
  norm_num

/-- The `ℝ/ℤ`-valued third coordinate of the clamped data: `circOf` of the unit normalisation of the
factorised direction. -/
def tauS (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (q : EuclideanSpace ℝ (Fin 2)) :
    UnitAddCircle :=
  circOf (tauE G q) (tauE_norm G q)

lemma circleOf_tauS (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (q : EuclideanSpace ℝ (Fin 2)) :
    circleOf (tauS G q) = tauE G q :=
  circleOf_circOf _ _

/-- **The clamped configuration data of the `τ`-chart.**  Where the factorised data satisfies the
side conditions of the configuration piece (`r > 0`, `‖d‖ ≤ 1`) it is used as it stands; elsewhere
the fixed good triple `tauBase` is substituted, so that the map is globally defined and the side
conditions hold everywhere. -/
def tauData (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (σ₀ : ℝ)
    (q : EuclideanSpace ℝ (Fin 2)) : ℝ × ℂ × UnitAddCircle :=
  if h : 0 < (G q).1 ∧ ‖(G q).2.1‖ ≤ 1 then ((G q).1, (G q).2.1, tauS G q)
  else tauBase hγ σ₀

lemma tauData_eq_of_good (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (σ₀ : ℝ)
    {q : EuclideanSpace ℝ (Fin 2)} (h : 0 < (G q).1 ∧ ‖(G q).2.1‖ ≤ 1) :
    tauData hγ hγne G σ₀ q = ((G q).1, (G q).2.1, tauS G q) := by
  simp only [tauData, dif_pos h]

lemma tauData_pos (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (σ₀ : ℝ)
    (q : EuclideanSpace ℝ (Fin 2)) : 0 < (tauData hγ hγne G σ₀ q).1 := by
  rw [tauData]
  split_ifs with h
  · exact h.1
  · exact tauBase_pos hγ hγne σ₀

lemma tauData_norm_le_one (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (σ₀ : ℝ)
    (q : EuclideanSpace ℝ (Fin 2)) : ‖(tauData hγ hγne G σ₀ q).2.1‖ ≤ 1 := by
  rw [tauData]
  split_ifs with h
  · exact h.2
  · exact tauBase_norm_le_one hγ σ₀

/-- **The `τ`-chart of the configuration strip.** -/
def stripTauChart (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (σ₀ : ℝ) :
    EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun q => Quotient.mk'' (Sum.inl (⟨tauData hγ hγne G σ₀ q,
    tauData_pos hγ hγne G σ₀ q, tauData_norm_le_one hγ hγne G σ₀ q⟩ : ConfigPiece))


/-! ## The chart is smooth on the strip side -/

/-- The window of the `τ`-chart: `0 < τ < π²/4` (so that `√τ < π/2`, the range in which the divided
difference of the curve does not vanish). -/
def tauWindow : Set (EuclideanSpace ℝ (Fin 2)) :=
  {q | 0 < q 1 ∧ q 1 < (Real.pi / 2) ^ 2}

lemma tauWindow_isOpen : IsOpen tauWindow :=
  (isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)).inter
    (isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1) continuous_const)

/-- **The `τ`-chart is `C^∞` on the strip side.**  If `G` is a `C^∞` map reproducing the symmetric
data on the window `{0 < τ < π²}`, then the chart is `C^∞` (for `Work.Drive.cappingCharted`) on
`{0 < τ < π²/4}`; the restriction to `0 < τ < π²/4` keeps `√τ < π/2`, which is exactly the range in
which the divided difference of the curve does not vanish. -/
theorem contMDiffOn_stripTauChart (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    (hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G tauWindow)
    (hfac : ∀ q ∈ tauWindow, G q = symmData γ (q 0, Real.sqrt (q 1))) (σ₀ : ℝ) :
    letI := cappingCharted
    ContMDiffOn (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (stripTauChart hγ hγne G σ₀)
      tauWindow := by
  letI := cappingCharted
  have hcont1 : Continuous fun q : EuclideanSpace ℝ (Fin 2) => q 1 :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  intro q hq
  have hGq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G q :=
    hG.contDiffAt (tauWindow_isOpen.mem_nhds hq)
  have hfacq : G q = symmData γ (q 0, Real.sqrt (q 1)) := hfac q hq
  obtain ⟨hτpos, hτlt⟩ := hq
  -- the neighbourhood on which the honest branch of the clamped data is used
  have hN1 : ∀ᶠ q' in 𝓝 q, 0 < q' 1 :=
    (isOpen_lt continuous_const hcont1).mem_nhds hτpos
  have hN2 : ∀ᶠ q' in 𝓝 q, q' 1 < (Real.pi / 2) ^ 2 :=
    (isOpen_lt hcont1 continuous_const).mem_nhds hτlt
  have hN3 : ∀ᶠ q' in 𝓝 q, 0 < (G q').1 :=
    hGq.continuousAt.fst.preimage_mem_nhds ((isOpen_lt continuous_const continuous_id).mem_nhds (by
      rw [hfacq]
      exact symmR_pos hγne _ _))
  have hN4 : ∀ᶠ q' in 𝓝 q, ‖(G q').2.1‖ < 2 :=
    hGq.continuousAt.snd.fst.norm.preimage_mem_nhds
      ((isOpen_lt continuous_id continuous_const).mem_nhds (by
        rw [hfacq]
        exact lt_of_le_of_lt (symmD_norm_le_one γ _ _) (by norm_num)))
  have hN : ∀ᶠ q' in 𝓝 q, 0 < q' 1 ∧ q' 1 < (Real.pi / 2) ^ 2 ∧ 0 < (G q').1
      ∧ ‖(G q').2.1‖ < 2 := by
    filter_upwards [hN1, hN2, hN3, hN4] with q' a b c d
    exact ⟨a, b, c, d⟩
  have hge : ∀ᶠ q' in 𝓝 q,
      tauData hγ hγne G σ₀ q' = ((G q').1, (G q').2.1, tauS G q') := by
    filter_upwards [hN] with q' hq'
    obtain ⟨hτ1, hτ2, hG1, -⟩ := hq'
    exact tauData_eq_of_good hγ hγne G σ₀ ⟨hG1, by
      rw [hfac q' ⟨hτ1, hτ2⟩]
      exact symmD_norm_le_one γ (q' 0) (Real.sqrt (q' 1))⟩
  have hnorm3 : ∀ᶠ q' in 𝓝 q, ‖(G q').2.2‖ = 1 := by
    filter_upwards [hN] with q' hq'
    obtain ⟨hτ1, hτ2, -, -⟩ := hq'
    have hspi' : |Real.sqrt (q' 1)| < Real.pi / 2 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.pi / 2)]
      exact hτ2
    rw [hfac q' ⟨hτ1, hτ2⟩]
    exact symmE_norm γ (q' 0) (Real.sqrt (q' 1)) (symmWC_ne_zero_of_lt hγ hspi')
  have hg1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q' : EuclideanSpace ℝ (Fin 2) => (tauData hγ hγne G σ₀ q').1) q :=
    (hGq.fst).congr_of_eventuallyEq
      (show (fun q' : EuclideanSpace ℝ (Fin 2) => (tauData hγ hγne G σ₀ q').1) =ᶠ[𝓝 q]
          fun q' => (G q').1 from
        hge.mono (fun q' hq' => congrArg Prod.fst hq'))
  have hg2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q' : EuclideanSpace ℝ (Fin 2) => (tauData hγ hγne G σ₀ q').2.1) q :=
    ((hGq.snd).fst).congr_of_eventuallyEq
      (show (fun q' : EuclideanSpace ℝ (Fin 2) => (tauData hγ hγne G σ₀ q').2.1) =ᶠ[𝓝 q]
          fun q' => (G q').2.1 from
        hge.mono (fun q' hq' => congrArg (fun z => z.2.1) hq'))
  have hg3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q' : EuclideanSpace ℝ (Fin 2) => circleOf ((tauData hγ hγne G σ₀ q').2.2)) q :=
    ((hGq.snd).snd).congr_of_eventuallyEq
      (show (fun q' : EuclideanSpace ℝ (Fin 2) => circleOf ((tauData hγ hγne G σ₀ q').2.2)) =ᶠ[𝓝 q]
          fun q' => (G q').2.2 from by
        filter_upwards [hge, hnorm3] with q' h1 h2
        rw [congrArg (fun z => z.2.2) h1, circleOf_tauS, tauE_eq_of_norm_eq_one h2])
  exact (contMDiffAt_confPiece_mk (tauData hγ hγne G σ₀) q
    (contMDiffAt_iff_contDiffAt.mpr hg1) (contMDiffAt_iff_contDiffAt.mpr hg2)
    (contMDiffAt_iff_contDiffAt.mpr hg3)
    (tauData_pos hγ hγne G σ₀) (tauData_norm_le_one hγ hγne G σ₀)).contMDiffWithinAt

/-! ## The image of the chart on `τ = s²` is the configuration strip -/

/-- `circOf` depends only on its argument. -/
lemma circOf_congr {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (h : z = w) :
    circOf z hz = circOf w hw := by
  subst h
  exact congrArg (fun hh => circOf _ hh) (Subsingleton.elim hz hw)

/-- **On `τ = s²` the `τ`-chart is the strip chart.**  If the two endpoints `σ+s` and `σ-s` are
distinct *on the circle*, the `τ`-chart at `(σ, s²)` is `Work.Drive.stripChart` at the parameter
`(σ+s, σ-s)`, i.e. the class in the capping space of the configuration of that chord. -/
theorem stripTauChart_eq_stripChart (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    (hfac : ∀ q ∈ tauWindow, G q = symmData γ (q 0, Real.sqrt (q 1))) (σ₀ : ℝ) {σ s : ℝ}
    (hs0 : s ≠ 0) (hspi : |s| < Real.pi / 2)
    (hne : Circle.exp (σ + s) ≠ Circle.exp (σ - s)) :
    stripTauChart hγ hγne G σ₀ (mk2 σ (s ^ 2))
      = stripChart γ hγne 0 (mk2 (σ + s) (σ - s)) := by
  have hτpos : 0 < s ^ 2 := by positivity
  have hτlt : s ^ 2 < Real.pi ^ 2 := by
    have h2 : |s| ^ 2 < (Real.pi / 2) ^ 2 := by nlinarith [hspi, abs_nonneg s]
    rw [sq_abs] at h2
    nlinarith [Real.pi_pos]
  have hq0 : (mk2 σ (s ^ 2)) 0 = σ := mk2_apply_zero _ _
  have hq1 : (mk2 σ (s ^ 2)) 1 = s ^ 2 := mk2_apply_one _ _
  have hEq : G (mk2 σ (s ^ 2)) = symmData γ (σ, |s|) := by
    have hmem : mk2 σ (s ^ 2) ∈ tauWindow := by
      refine ⟨hτpos, ?_⟩
      have h1 : |s| < Real.pi / 2 := hspi
      nlinarith [hspi, abs_nonneg s, sq_abs s]
    rw [hfac _ hmem, hq0, hq1, Real.sqrt_sq_eq_abs]
  have hgood : 0 < (G (mk2 σ (s ^ 2))).1 ∧ ‖(G (mk2 σ (s ^ 2))).2.1‖ ≤ 1 := by
    rw [hEq]
    exact ⟨symmR_pos hγne σ |s|, symmD_norm_le_one γ σ |s|⟩
  have hnormE : ‖symmE γ σ |s|‖ = 1 :=
    symmE_norm γ σ |s| (symmWC_ne_zero_of_lt hγ (by rwa [abs_abs]))
  have hnormG : ‖(G (mk2 σ (s ^ 2))).2.2‖ = 1 := by rw [hEq]; exact hnormE
  -- the left-hand side, with the honest branch of the clamped data
  have htau : tauS G (mk2 σ (s ^ 2)) = circOf (symmE γ σ |s|) hnormE := by
    refine circleOf_injective ?_
    rw [circleOf_tauS, tauE_eq_of_norm_eq_one hnormG, congrArg (fun z => z.2.2) hEq,
      circleOf_circOf]
    simp only [symmData]
  have htriple : tauData hγ hγne G σ₀ (mk2 σ (s ^ 2))
      = (symmR γ σ |s|, symmD γ σ |s|, circOf (symmE γ σ |s|) hnormE) := by
    rw [tauData_eq_of_good hγ hγne G σ₀ hgood]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · exact (congrArg (fun z => z.1) hEq).trans rfl
    · exact (congrArg (fun z => z.2.1) hEq).trans rfl
    · exact htau
  have hL : stripTauChart hγ hγne G σ₀ (mk2 σ (s ^ 2))
      = Quotient.mk'' (Sum.inl (⟨(symmR γ σ |s|, symmD γ σ |s|, circOf (symmE γ σ |s|) hnormE),
          symmR_pos hγne σ |s|, symmD_norm_le_one γ σ |s|⟩ : ConfigPiece)) :=
    Quotient.sound (Or.inl (congrArg Sum.inl (Subtype.ext htriple)))
  -- the right-hand side, in the explicit form of `stripChart_eq_mk`
  have hR : stripChart γ hγne 0 (mk2 (σ + s) (σ - s))
      = Quotient.mk'' (Sum.inl (⟨((stripData γ (mk2 (σ + s) (σ - s))).1,
          (stripData γ (mk2 (σ + s) (σ - s))).2.1,
          (stripData γ (mk2 (σ + s) (σ - s))).2.2 + 0),
          stripData_pos hγne _, confOf_snd_norm_le_one _⟩ : ConfigPiece)) :=
    stripChart_eq_mk γ hγne 0 _
  rw [hL, hR, mk_inl_inj]
  have h1R : symmR γ σ |s| = symmR γ σ s := by
    by_cases h : 0 ≤ s
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), symmR_neg]
  have h1D : symmD γ σ |s| = symmD γ σ s := by
    by_cases h : 0 ≤ s
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), symmD_neg]
  have h1E : symmE γ σ |s| = symmE γ σ s := by
    by_cases h : 0 ≤ s
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h), symmE_neg hγ]
  have c1 : symmR γ σ |s| = (stripData γ (mk2 (σ + s) (σ - s))).1 := by
    rw [stripData_fst, h1R, symmR_eq_stripR]
  have c2 : symmD γ σ |s| = (stripData γ (mk2 (σ + s) (σ - s))).2.1 := by
    rw [stripData_snd, h1D, symmD_eq_stripD]
  have c3 : circOf (symmE γ σ |s|) hnormE
      = (stripData γ (mk2 (σ + s) (σ - s))).2.2 + 0 := by
    rw [add_zero, stripData_thd]
    simp only [mk2_apply_zero, mk2_apply_one]
    refine circleOf_injective ?_
    rw [circleOf_circOf, h1E, symmE_eq_chordUnitDir_sq hγ σ s hs0 (symmWC_ne_zero_of_lt hγ hspi),
      (contDiffOn_chordUnitDir γ hγ).2.1 (σ + s, σ - s) hne]
  exact Subtype.ext (Prod.ext c1 (Prod.ext c2 c3))

/-! ## The explicit factorised data -/

/-- Smoothness of the direction at a point where the divided difference does not vanish (the
hypothesis-free form of `Work.Drive.Neutral.contDiffAt_symmE`, which is the case `s = 0`). -/
lemma contDiffAt_symmE_of_ne (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {σ s : ℝ} (h : symmWC γ σ s ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => symmE γ q.1 q.2) (σ, s) := by
  have hwc := contDiff_symmWC hγ
  have hnorm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => ‖symmWC γ q.1 q.2‖) (σ, s) :=
    ContDiffAt.norm ℂ hwc.contDiffAt h
  have hdiv : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => (1 : ℝ) / ‖symmWC γ q.1 q.2‖) (σ, s) :=
    ContDiffAt.div (f := fun _ : ℝ × ℝ => (1 : ℝ)) contDiffAt_const hnorm
      (norm_ne_zero_iff.mpr h)
  have hmul : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : ℝ × ℝ => symmWC γ q.1 q.2 * (((1 : ℝ) / ‖symmWC γ q.1 q.2‖ : ℝ) : ℂ)) (σ, s) :=
    hwc.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp (σ, s) hdiv)
  simpa only [symmE] using hmul.pow 2

/-- **The explicit factorised data is `C^∞` on the window `{0 < τ < π²/4}`.**  This is the map
`(σ,τ) ↦ symmData γ (σ, √τ)`, whose smoothness is exactly the content of the even-factorisation lemma
for the configuration data (`Work.Drive.exists_contDiffOn_even_comp_sqrt`): it satisfies the
hypothesis `hfac` of `Work.Drive.Neutral.contMDiffOn_stripTauChart` by definition. -/
theorem contDiffOn_symmData_sqrt (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 2) => symmData γ (q 0, Real.sqrt (q 1)))
      {q : EuclideanSpace ℝ (Fin 2) | 0 < q 1 ∧ q 1 < (Real.pi / 2) ^ 2} := by
  intro q hq
  obtain ⟨hτpos, hτlt⟩ := hq
  have hspi : |Real.sqrt (q 1)| < Real.pi / 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.pi / 2)]
    exact hτlt
  have hpair : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q' : EuclideanSpace ℝ (Fin 2) => (q' 0, Real.sqrt (q' 1))) q := by
    have h0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q' : EuclideanSpace ℝ (Fin 2) => q' 0) q := by fun_prop
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q' : EuclideanSpace ℝ (Fin 2) => q' 1) q := by fun_prop
    have hsq : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q' : EuclideanSpace ℝ (Fin 2) => Real.sqrt (q' 1)) q :=
      (Real.contDiffAt_sqrt (ne_of_gt hτpos)).comp q h1
    exact h0.prodMk hsq
  have hsd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × ℝ => symmData γ z) (q 0, Real.sqrt (q 1)) := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => symmR γ z.1 z.2)
        (q 0, Real.sqrt (q 1)) := (contDiff_symmR hγ hγne).contDiffAt
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => symmD γ z.1 z.2)
        (q 0, Real.sqrt (q 1)) := (contDiff_symmD hγ hγne).contDiffAt
    have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => symmE γ z.1 z.2)
        (q 0, Real.sqrt (q 1)) :=
      contDiffAt_symmE_of_ne hγ (symmWC_ne_zero_of_lt hγ hspi)
    exact h1.prodMk (h2.prodMk h3)
  exact (hsd.comp q hpair).contDiffWithinAt.mono (Set.subset_univ _)

/-! ## The unconditional form of the chart -/

/-- **The `τ`-chart of the configuration strip, unconditionally.**  Taking the explicit factorised
data `q ↦ symmData γ (q 0, √(q 1))` (which is `C^∞` on the window by
`Work.Drive.Neutral.contDiffOn_symmData_sqrt`), the chart `Work.Drive.Neutral.stripTauChart` is

* `C^∞` for `Work.Drive.cappingCharted` on the window `{0 < τ < π²/4}`, and
* on `τ = s²` (with `0 < |s| < π/2` and the two endpoints distinct on the circle) it is the strip
  chart `Work.Drive.stripChart` at the parameter `(σ+s, σ-s)`, i.e. the class of the configuration
  of that chord. -/
theorem exists_stripTauChart (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ₀ : ℝ) :
    (letI := cappingCharted
     ContMDiffOn (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
       (stripTauChart hγ hγne (fun q : EuclideanSpace ℝ (Fin 2) => symmData γ (q 0, Real.sqrt (q 1)))
         σ₀) tauWindow) ∧
    (∀ σ s : ℝ, s ≠ 0 → |s| < Real.pi / 2 → Circle.exp (σ + s) ≠ Circle.exp (σ - s) →
      stripTauChart hγ hγne (fun q : EuclideanSpace ℝ (Fin 2) => symmData γ (q 0, Real.sqrt (q 1)))
          σ₀ (mk2 σ (s ^ 2))
        = stripChart γ hγne 0 (mk2 (σ + s) (σ - s))) :=
  ⟨contMDiffOn_stripTauChart hγ hγne (contDiffOn_symmData_sqrt hγ hγne) (fun q _ => rfl) σ₀,
   fun σ s hs0 hspi hne => stripTauChart_eq_stripChart hγ hγne (fun q _ => rfl) σ₀ hs0 hspi hne⟩

end

end Work.Drive.Neutral
