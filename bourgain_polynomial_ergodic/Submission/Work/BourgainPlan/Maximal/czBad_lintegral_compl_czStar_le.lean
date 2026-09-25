import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusCZDefs
import Submission.Work.BourgainPlan.Maximal.czBasic
import Submission.Work.BourgainPlan.Maximal.annulusSqfunDefs
import Submission.Work.BourgainPlan.Maximal.annulusBadPartBound
import Submission.Work.BourgainPlan.Maximal.ENNReal_sqrt_tsum_tsum_sq_le_general

/-!
# The `L¹` bound for the Calderón--Zygmund bad part outside `czStar`

Step (ii-e) of the annulus square-function assembly (`WINDOW_WEAK_TYPE_STATUS_S10.md` §10): for a
family `b` satisfying the bad-part estimate `AnnulusBadPartBound b`, the square function of the
Calderón--Zygmund *bad part* `czBad f σ c` of `f` at height `c` (`σ = ‖f‖ₑ`) is controlled outside
the enlargement `czStar σ c` of the maximal dyadic cells by the `L¹` mass of `f`:

  `∫⁻_{czStar σ c}ᶜ S_j (czBad f σ c) ≤ C ∫⁻ σ`,   `C` uniform in `j`, `f`, `σ`, `c`.

The proof is the classical one, and it uses **only** the bad-part hypothesis, never any smoothness
of the symbol family `b` (so nothing about `annulusK b m` beyond what `AnnulusBadPartBound`
provides is available).  This is the reason for the two features of the file:

* the *linearity* of the convolution over the cell decomposition is proved by a case split on
  `Integrable (fun y => K (x - y) · czBad y)`: in the integrable case `integral_tsum` gives the
  identity, in the non-integrable case the Bochner integral is `0` by definition (`integral_undef`)
  and the inequality is trivial;
* the *a.e. measurability* of `annulusSqfun b j g` for an a.e. measurable `g` is proved from the
  definition of `fourierInv` as a Bochner integral: if `b m` is integrable the inverse Fourier
  transform is a parametrised integral (Fubini), and otherwise every integral in its definition is
  `0` (`fourierIntegral_convergent_iff`), so the kernel vanishes.

The per-cell estimate is `AnnulusBadPartBound` itself applied to the mean-zero cell piece
`czBadPiece f p`, whose `L¹` mass is at most twice the mass of `f` on the cell; summing over the
disjoint maximal cells and using `∫⁻ σ = ∫⁻ ‖f‖ₑ` finishes the proof.
-/

open MeasureTheory Set FourierTransform
open scoped ENNReal BigOperators Classical

namespace Work.BourgainPlan.Maximal

/-! ## 1. A.e. measurability of the annulus kernel, the convolution and the square function -/

/-- **The annulus kernel is a.e. measurable, for an arbitrary symbol family `b`.**  `annulusK b m`
is the inverse Fourier transform `𝓕⁻ (b m)`, i.e. the Bochner integral
`w ↦ ∫ v, 𝐞 ⟪v, w⟫ • b m v`.  If `b m` is integrable this is a parametrised integral of a jointly
a.e. measurable function (Fubini), otherwise `fourierIntegral_convergent_iff` shows that *every*
integrand in the definition is non-integrable, so the integral is `0` and the kernel vanishes. -/
lemma aemeasurable_annulusK (b : ℤ → ℝ → ℂ) (m : ℤ) : AEMeasurable (annulusK b m) volume := by
  by_cases hb : Integrable (b m) volume
  · have hbm : AEMeasurable (b m) volume := hb.aemeasurable
    have hcont : Continuous (fun p : ℝ × ℝ => ((𝐞 (inner ℝ p.2 p.1) : Circle) : ℂ)) :=
      continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_inner.comp (continuous_snd.prodMk continuous_fst)))
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => ((𝐞 (inner ℝ p.2 p.1) : Circle) : ℂ) * b m p.2)
        (volume.prod volume) :=
      hcont.aestronglyMeasurable.mul
        ((hbm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).aestronglyMeasurable)
    have hres : AEStronglyMeasurable
        (fun w : ℝ => ∫ v, ((𝐞 (inner ℝ v w) : Circle) : ℂ) * b m v) volume :=
      hjoint.integral_prod_right'
    refine hres.aemeasurable.congr ?_
    filter_upwards with w
    rw [annulusK, Real.fourierInv_eq]
    apply integral_congr_ae
    filter_upwards with v
    rw [Circle.smul_def, smul_eq_mul]
  · have hzero : annulusK b m = fun _ => 0 := by
      funext w
      rw [annulusK, Real.fourierInv_eq, integral_undef]
      intro hint
      refine hb ((Real.fourierIntegral_convergent_iff (f := b m) (-w)).mp ?_)
      simpa using hint
    rw [hzero]
    exact aemeasurable_const

/-- **The annulus convolution of an a.e. measurable function is a.e. measurable.**  The integrand
`(x, y) ↦ K (x - y) * g y` is jointly a.e. measurable by
`AEStronglyMeasurable.convolution_integrand` (which is where the quasi-invariance of
`(x, y) ↦ x - y` is proved), and Fubini gives the a.e. measurability of the parametrised
integral. -/
lemma aemeasurable_annulusConv (b : ℤ → ℝ → ℂ) (m : ℤ) {g : ℝ → ℂ}
    (hg : AEMeasurable g volume) (hK : AEMeasurable (annulusK b m) volume) :
    AEMeasurable (annulusConv b m g) volume := by
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => annulusK b m (p.1 - p.2) * g p.2)
      (volume.prod volume) := by
    have h := (hg.aestronglyMeasurable).convolution_integrand
      (L := ContinuousLinearMap.mul ℝ ℂ) (hK.aestronglyMeasurable)
    refine h.congr ?_
    filter_upwards with p
    rw [ContinuousLinearMap.mul_apply', mul_comm]
  exact (hjoint.integral_prod_right').aemeasurable

/-- **The annulus square function of an a.e. measurable function is a.e. measurable.** -/
lemma aemeasurable_annulusSqfun (b : ℤ → ℝ → ℂ) (j : ℤ) {g : ℝ → ℂ}
    (hg : AEMeasurable g volume) : AEMeasurable (annulusSqfun b j g) volume := by
  have hconv : ∀ m : ℤ, AEMeasurable (annulusConv b m g) volume := fun m =>
    aemeasurable_annulusConv b m hg (aemeasurable_annulusK b m)
  have hsq : AEMeasurable (fun x => ∑' n : ℤ, ‖annulusConv b (j + n) g x‖ₑ ^ (2 : ℝ))
      volume :=
    AEMeasurable.tsum fun n => (hconv (j + n)).enorm.pow_const (2 : ℝ)
  exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hsq

/-- A single Calderón--Zygmund cell piece is a.e. measurable. -/
lemma aemeasurable_czBadPiece (f : ℝ → ℂ) (hf : AEMeasurable f volume) (p : ℤ × ℤ) :
    AEMeasurable (czBadPiece f p) volume := by
  have h : czBadPiece f p = (dyCell p.1 p.2).indicator (fun x => f x - czCellAvgC f p) := by
    funext x
    rw [Set.indicator_apply]
    by_cases hx : x ∈ dyCell p.1 p.2
    · rw [czBadPiece_of_mem f p hx, if_pos hx]
    · rw [czBadPiece_of_notMem f p hx, if_neg hx]
  rw [h]
  exact (hf.sub aemeasurable_const).indicator (dyCell_measurable _ _)

/-! ## 2. Elementary consequences of the disjointness of the maximal cells -/

/-- Summing an `ℝ≥0∞`-valued function over all indices where it is `0` off a set is the same as
summing over the set. -/
lemma tsum_ite_mem_eq_tsum_subtype {ι : Type*} [Countable ι] (s : Set ι) (A : ι → ℝ≥0∞) :
    (∑' i : ι, (if i ∈ s then A i else 0)) = ∑' i : s, A i.1 := by
  rw [tsum_subtype]
  exact tsum_congr fun i => by
    by_cases h : i ∈ s
    · rw [Set.indicator_of_mem h, if_pos h]
    · rw [Set.indicator_of_notMem h, if_neg h]

lemma lwtOm_eq_iUnion_subtype (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) :
    lwtOm σ c = ⋃ p : {p : ℤ × ℤ // p ∈ czMax σ c}, dyCell p.1.1 p.1.2 := by
  ext x
  simp only [lwtOm, Set.mem_iUnion, Subtype.exists, exists_prop]

/-- The `σ`-integral over the Calderón--Zygmund set is the sum of the integrals over the maximal
cells. -/
lemma lintegral_lwtOm_eq_tsum_cells (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (F : ℝ → ℝ≥0∞) :
    ∫⁻ x in lwtOm σ c, F x
      = ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, ∫⁻ x in dyCell p.1.1 p.1.2, F x := by
  rw [lwtOm_eq_iUnion_subtype σ c]
  exact lintegral_iUnion
    (fun p : {p : ℤ × ℤ // p ∈ czMax σ c} => dyCell_measurable p.1.1 p.1.2)
    (lwtOm_iUnion_disjoint σ c) F

/-- The square function of the zero function vanishes. -/
lemma annulusSqfun_zero (b : ℤ → ℝ → ℂ) (j : ℤ) (x : ℝ) :
    annulusSqfun b j (fun _ => 0) x = 0 := by
  simp [annulusSqfun, annulusConv]

/-- The cell pieces of the Calderón--Zygmund bad part, indexed by *all* dyadic cells (the pieces
of the non-maximal cells are `0`). -/
noncomputable def czBadCellFun (f : ℝ → ℂ) (σ : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (p : ℤ × ℤ) : ℝ → ℂ :=
  fun y => if p ∈ czMax σ c then czBadPiece f p y else 0

lemma czBadCellFun_of_mem {f : ℝ → ℂ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {p : ℤ × ℤ}
    (hp : p ∈ czMax σ c) : czBadCellFun f σ c p = czBadPiece f p := by
  funext y
  simp only [czBadCellFun, if_pos hp]

lemma czBadCellFun_of_notMem {f : ℝ → ℂ} {σ : ℝ → ℝ≥0∞} {c : ℝ≥0∞} {p : ℤ × ℤ}
    (hp : p ∉ czMax σ c) : czBadCellFun f σ c p = 0 := by
  funext y
  simp only [czBadCellFun, if_neg hp]
  rfl

lemma annulusSqfun_czBadCellFun_of_notMem (b : ℤ → ℝ → ℂ) (j : ℤ) (f : ℝ → ℂ) (σ : ℝ → ℝ≥0∞)
    (c : ℝ≥0∞) {p : ℤ × ℤ} (hp : p ∉ czMax σ c) (x : ℝ) :
    annulusSqfun b j (czBadCellFun f σ c p) x = 0 := by
  rw [czBadCellFun_of_notMem hp]; exact annulusSqfun_zero b j x

/-! ## 3. Linearity of the convolution over the cell decomposition -/

/-- **Linearity of `annulusConv` over the Calderón--Zygmund decomposition.**  The bad part is the
sum of its cell pieces, so the convolution at `x` is the sum of the convolutions — provided the
whole integrand is integrable.  If it is not, the Bochner integral is `0` by definition and the
inequality holds trivially; this is the only place where the (otherwise unusable) definitional
convention `∫ = 0` for non-integrable functions is needed. -/
lemma enorm_annulusConv_czBad_le_tsum (b : ℤ → ℝ → ℂ) (m : ℤ) (f : ℝ → ℂ) (σ : ℝ → ℝ≥0∞)
    (c : ℝ≥0∞) (x : ℝ) :
    ‖annulusConv b m (czBad f σ c) x‖ₑ
      ≤ ∑' p : ℤ × ℤ, ‖annulusConv b m (czBadCellFun f σ c p) x‖ₑ := by
  let u : ℝ → ℂ := fun y => annulusK b m (x - y) * czBad f σ c y
  by_cases hint : Integrable u volume
  · have hkey : annulusConv b m (czBad f σ c) x = ∑' p : ℤ × ℤ, annulusConv b m (czBadCellFun f σ c p) x := by
      have h1 : (fun y => u y) = fun y => ∑' p : ℤ × ℤ, annulusK b m (x - y) * czBadCellFun f σ c p y := by
        funext y
        show annulusK b m (x - y) * czBad f σ c y = _
        rw [show czBad f σ c y = ∑' p : ℤ × ℤ, czBadCellFun f σ c p y from rfl, tsum_mul_left]
      have h2 : ∫ y, u y = ∫ y, ∑' p : ℤ × ℤ, annulusK b m (x - y) * czBadCellFun f σ c p y := by
        rw [h1]
      rw [show annulusConv b m (czBad f σ c) x = ∫ y, u y from rfl, h2]
      refine integral_tsum (fun p => ?_) ?_
      · by_cases hp : p ∈ czMax σ c
        · have hind : (fun y => annulusK b m (x - y) * czBadCellFun f σ c p y)
              = (dyCell p.1 p.2).indicator u := by
            funext y
            by_cases hy : y ∈ dyCell p.1 p.2
            · rw [Set.indicator_of_mem hy]
              have hgy : czBadCellFun f σ c p y = czBad f σ c y := by
                rw [czBadCellFun_of_mem hp, czBadPiece_of_mem f p hy,
                  ← czBad_of_mem_cell hp hy]
              rw [hgy]
            · rw [Set.indicator_of_notMem hy, czBadCellFun_of_mem hp,
                czBadPiece_of_notMem f p hy, mul_zero]
          rw [hind]
          exact hint.aestronglyMeasurable.indicator (dyCell_measurable p.1 p.2)
        · have hz : (fun y => annulusK b m (x - y) * czBadCellFun f σ c p y) = fun _ => 0 := by
            funext y
            simp [czBadCellFun_of_notMem hp]
          rw [hz]
          exact aestronglyMeasurable_const
      · have hterm : ∀ p : ℤ × ℤ,
            ∫⁻ a, ‖annulusK b m (x - a) * czBadCellFun f σ c p a‖ₑ
              = if p ∈ czMax σ c then ∫⁻ a in dyCell p.1 p.2, ‖u a‖ₑ else 0 := by
          intro p
          by_cases hp : p ∈ czMax σ c
          · rw [if_pos hp]
            have hfun : (fun a => ‖annulusK b m (x - a) * czBadCellFun f σ c p a‖ₑ)
                = (dyCell p.1 p.2).indicator (fun a => ‖u a‖ₑ) := by
              funext a
              by_cases ha : a ∈ dyCell p.1 p.2
              · rw [Set.indicator_of_mem ha]
                congr 1
                rw [czBadCellFun_of_mem hp, czBadPiece_of_mem f p ha, ← czBad_of_mem_cell hp ha]
              · rw [Set.indicator_of_notMem ha, czBadCellFun_of_mem hp,
                  czBadPiece_of_notMem f p ha, mul_zero, enorm_zero]
            rw [hfun, lintegral_indicator (dyCell_measurable p.1 p.2)]
          · rw [if_neg hp]
            have hfun : (fun a => ‖annulusK b m (x - a) * czBadCellFun f σ c p a‖ₑ)
                = fun _ => 0 := by
              funext a
              simp [czBadCellFun_of_notMem hp]
            rw [hfun, lintegral_zero]
        rw [tsum_congr hterm,
          tsum_ite_mem_eq_tsum_subtype (czMax σ c) (fun p => ∫⁻ a in dyCell p.1 p.2, ‖u a‖ₑ),
          ← lintegral_iUnion
            (fun q : {p : ℤ × ℤ // p ∈ czMax σ c} => dyCell_measurable q.1.1 q.1.2)
            (lwtOm_iUnion_disjoint σ c) (fun a => ‖u a‖ₑ),
          ← lwtOm_eq_iUnion_subtype σ c]
        have hEq : ∫⁻ a in lwtOm σ c, ‖u a‖ₑ = ∫⁻ a, ‖u a‖ₑ := by
          rw [← lintegral_indicator (measurableSet_lwtOm σ c) (fun a => ‖u a‖ₑ)]
          refine lintegral_congr fun a => ?_
          by_cases ha : a ∈ lwtOm σ c
          · rw [Set.indicator_of_mem ha]
          · rw [Set.indicator_of_notMem ha]
            have : u a = 0 := by
              show annulusK b m (x - a) * czBad f σ c a = 0
              rw [czBad_of_notMem ha, mul_zero]
            rw [this, enorm_zero]
        rw [hEq]
        exact (hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral).ne
    rw [hkey]
    exact enorm_tsum_le_tsum_enorm
  · have hz : annulusConv b m (czBad f σ c) x = 0 := by
      show (∫ y, u y) = 0
      exact integral_undef hint
    rw [hz, enorm_zero]
    exact bot_le

/-! ## 4. The pointwise Minkowski (triangle) inequality over the cells -/

/-- **The square function of the bad part is dominated by the sum of the square functions of its
cell pieces.**  This is the `ℓ²` triangle inequality applied to the vector
`(annulusConv b (j+n) (czBad f σ c) x)_n`, whose components are the sums over the cells. -/
lemma annulusSqfun_czBad_le_tsum (b : ℤ → ℝ → ℂ) (j : ℤ) (f : ℝ → ℂ) (σ : ℝ → ℝ≥0∞)
    (c : ℝ≥0∞) (x : ℝ) :
    annulusSqfun b j (czBad f σ c) x
      ≤ ∑' p : {p : ℤ × ℤ // p ∈ czMax σ c}, annulusSqfun b j (czBadPiece f p.1) x := by
  have hcell : annulusSqfun b j (czBad f σ c) x
      ≤ ∑' p : ℤ × ℤ, annulusSqfun b j (czBadCellFun f σ c p) x := by
    show (∑' n : ℤ, ‖annulusConv b (j + n) (czBad f σ c) x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ ∑' p : ℤ × ℤ, annulusSqfun b j (czBadCellFun f σ c p) x
    refine le_trans (ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun n =>
      ENNReal.rpow_le_rpow (enorm_annulusConv_czBad_le_tsum b (j + n) f σ c x)
        (by norm_num)) (by norm_num)) ?_
    exact ENNReal_sqrt_tsum_tsum_sq_le_general
      (fun n p => ‖annulusConv b (j + n) (czBadCellFun f σ c p) x‖ₑ)
  have hsplit : ∀ p : ℤ × ℤ, annulusSqfun b j (czBadCellFun f σ c p) x
      = (if p ∈ czMax σ c then annulusSqfun b j (czBadCellFun f σ c p) x else 0) := by
    intro p
    by_cases hp : p ∈ czMax σ c
    · rw [if_pos hp]
    · rw [if_neg hp]
      exact annulusSqfun_czBadCellFun_of_notMem b j f σ c hp x
  calc annulusSqfun b j (czBad f σ c) x
      ≤ ∑' p : ℤ × ℤ, annulusSqfun b j (czBadCellFun f σ c p) x := hcell
    _ = ∑' p : ℤ × ℤ,
          (if p ∈ czMax σ c then annulusSqfun b j (czBadCellFun f σ c p) x else 0) :=
        tsum_congr hsplit
    _ = ∑' q : {p : ℤ × ℤ // p ∈ czMax σ c}, annulusSqfun b j (czBadCellFun f σ c q.1) x :=
        tsum_ite_mem_eq_tsum_subtype (czMax σ c)
          (fun p => annulusSqfun b j (czBadCellFun f σ c p) x)
    _ = ∑' q : {p : ℤ × ℤ // p ∈ czMax σ c}, annulusSqfun b j (czBadPiece f q.1) x :=
        tsum_congr fun q => by rw [czBadCellFun_of_mem q.2]

/-! ## 5. The `L¹` mass of a cell piece -/

/-- **The `L¹` mass of a Calderón--Zygmund cell piece.**  On its own dyadic cell the piece is
`f - ⨏ f`, so its mass is at most `∫_cell ‖f‖ + vol(cell)·‖⨏ f‖ ≤ 2 ∫_cell ‖f‖` (Jensen). -/
lemma czBadPiece_lintegral_le (f : ℝ → ℂ) (p : ℤ × ℤ) :
    ∫⁻ x, ‖czBadPiece f p x‖ₑ ≤ 2 * ∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ := by
  have h1 : ∀ x, ‖czBadPiece f p x‖ₑ
      ≤ (dyCell p.1 p.2).indicator (fun x => ‖f x‖ₑ + ‖czCellAvgC f p‖ₑ) x := by
    intro x
    by_cases hx : x ∈ dyCell p.1 p.2
    · rw [Set.indicator_of_mem hx, czBadPiece_of_mem f p hx]
      exact enorm_sub_le
    · rw [Set.indicator_of_notMem hx, czBadPiece_of_notMem f p hx, enorm_zero]
  have hvol : volume (dyCell p.1 p.2) = ENNReal.ofReal ((2 : ℝ) ^ p.1) := dyCell_volume_eq p.1 p.2
  have h2 : ∫⁻ x in dyCell p.1 p.2, (‖f x‖ₑ + ‖czCellAvgC f p‖ₑ)
      = (∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ) + ‖czCellAvgC f p‖ₑ * volume (dyCell p.1 p.2) := by
    rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  have h3 : ‖czCellAvgC f p‖ₑ * volume (dyCell p.1 p.2) ≤ ∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ p.1 := zpow_two_pos p.1
    calc ‖czCellAvgC f p‖ₑ * volume (dyCell p.1 p.2)
        ≤ (ENNReal.ofReal (((2 : ℝ) ^ p.1)⁻¹)
            * ∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ) * volume (dyCell p.1 p.2) :=
          mul_le_mul_left (czCellAvgC_enorm_le f p) _
      _ = (ENNReal.ofReal (((2 : ℝ) ^ p.1)⁻¹)
            * ∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ) * ENNReal.ofReal ((2 : ℝ) ^ p.1) := by rw [hvol]
      _ = ∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ := by
          rw [ofReal_zpow_inv, mul_assoc,
            mul_comm (∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ) (ENNReal.ofReal ((2 : ℝ) ^ p.1)),
            ← mul_assoc,
            ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top,
            one_mul]
  calc ∫⁻ x, ‖czBadPiece f p x‖ₑ
      ≤ ∫⁻ x, (dyCell p.1 p.2).indicator (fun x => ‖f x‖ₑ + ‖czCellAvgC f p‖ₑ) x :=
        lintegral_mono h1
    _ = ∫⁻ x in dyCell p.1 p.2, (‖f x‖ₑ + ‖czCellAvgC f p‖ₑ) :=
        lintegral_indicator (dyCell_measurable p.1 p.2) _
    _ = (∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ) + ‖czCellAvgC f p‖ₑ * volume (dyCell p.1 p.2) := h2
    _ ≤ (∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ) + ∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ := add_le_add le_rfl h3
    _ = 2 * ∫⁻ x in dyCell p.1 p.2, ‖f x‖ₑ := by rw [two_mul]

/-- **The cell piece of the Calderón--Zygmund decomposition is `L¹`.** -/
lemma czBadPiece_memLp_one {f : ℝ → ℂ} (hf : MeasureTheory.MemLp f 1 MeasureTheory.volume)
    (p : ℤ × ℤ) :
    MeasureTheory.MemLp (czBadPiece f p) 1 MeasureTheory.volume := by
  have h1 : czBadPiece f p = (dyCell p.1 p.2).indicator (fun x => f x - czCellAvgC f p) := by
    funext x
    rw [Set.indicator_apply]
    by_cases hx : x ∈ dyCell p.1 p.2
    · rw [czBadPiece_of_mem f p hx, if_pos hx]
    · rw [czBadPiece_of_notMem f p hx, if_neg hx]
  rw [memLp_one_iff_integrable, h1, integrable_indicator_iff (dyCell_measurable p.1 p.2)]
  haveI : IsFiniteMeasure (volume.restrict (dyCell p.1 p.2)) :=
    ⟨by rw [Measure.restrict_apply_univ, dyCell_volume_eq]; exact ENNReal.ofReal_lt_top⟩
  exact (memLp_one_iff_integrable.mp hf).integrableOn.sub (integrable_const _)

/-! ## 6. The bad-part estimate -/

theorem czBad_lintegral_compl_czStar_le (b : ℤ → ℝ → ℂ)
    (hBad : Work.BourgainPlan.Maximal.AnnulusBadPartBound b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℤ) (f : ℝ → ℂ) (σ : ℝ → ENNReal) (c : ENNReal),
      MeasureTheory.MemLp f 1 MeasureTheory.volume →
      (∀ x : ℝ, σ x = ‖f x‖ₑ) →
      ∫⁻ x in (Work.BourgainPlan.Maximal.czStar σ c)ᶜ,
          Work.BourgainPlan.Maximal.annulusSqfun b j (Work.BourgainPlan.Maximal.czBad f σ c) x
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, σ x := by
  obtain ⟨Cb, hCb, hbad⟩ := hBad
  refine ⟨2 * Cb, by positivity, ?_⟩
  intro j f σ c hf hσ
  by_cases htop : ∫⁻ x : ℝ, σ x = ⊤
  · have hne : ENNReal.ofReal (2 * Cb) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    rw [htop, ENNReal.mul_top hne]
    exact le_top
  · have hfin : ∫⁻ x : ℝ, σ x < ⊤ := lt_top_iff_ne_top.mpr htop
    have hfae : AEMeasurable f volume := hf.aemeasurable
    have hfint : Integrable f volume := memLp_one_iff_integrable.mp hf
    have hmeas : ∀ q : {p : ℤ × ℤ // p ∈ czMax σ c},
        AEMeasurable (annulusSqfun b j (czBadPiece f q.1)) volume :=
      fun q => aemeasurable_annulusSqfun b j (aemeasurable_czBadPiece f hfae q.1)
    have hton : ∫⁻ x in (czStar σ c)ᶜ, (∑' q : {p : ℤ × ℤ // p ∈ czMax σ c},
          annulusSqfun b j (czBadPiece f q.1) x)
        = ∑' q : {p : ℤ × ℤ // p ∈ czMax σ c},
            ∫⁻ x in (czStar σ c)ᶜ, annulusSqfun b j (czBadPiece f q.1) x :=
      lintegral_tsum (fun q => (hmeas q).restrict)
    have hcell : ∀ q : {p : ℤ × ℤ // p ∈ czMax σ c},
        ∫⁻ x in (czStar σ c)ᶜ, annulusSqfun b j (czBadPiece f q.1) x
          ≤ ENNReal.ofReal Cb * ∫⁻ x : ℝ, ‖czBadPiece f q.1 x‖ₑ := by
      intro q
      refine le_trans (lintegral_mono_set (fun x hx => czStar_compl hx q.2)) ?_
      exact hbad j q.1.1 q.1.2 (czBadPiece f q.1) (czBadPiece_memLp_one hf q.1)
        (fun x hx => czBadPiece_of_notMem f q.1 hx)
        (by rw [setIntegral_eq_integral_of_forall_compl_eq_zero
              (fun x hx => czBadPiece_of_notMem f q.1 hx)]
            exact czBadPiece_integral_eq_zero hfint q.1)
    have hmass : ∀ q : {p : ℤ × ℤ // p ∈ czMax σ c},
        ENNReal.ofReal Cb * ∫⁻ x : ℝ, ‖czBadPiece f q.1 x‖ₑ
          ≤ ENNReal.ofReal Cb * (2 * ∫⁻ x in dyCell q.1.1 q.1.2, ‖f x‖ₑ) :=
      fun q => mul_le_mul_right (czBadPiece_lintegral_le f q.1) _
    have hsum : (∑' q : {p : ℤ × ℤ // p ∈ czMax σ c},
          ENNReal.ofReal Cb * (2 * ∫⁻ x in dyCell q.1.1 q.1.2, ‖f x‖ₑ))
        = ENNReal.ofReal Cb * (2 * ∫⁻ x in lwtOm σ c, ‖f x‖ₑ) := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      rw [ENNReal.tsum_mul_left, lintegral_lwtOm_eq_tsum_cells]
    have hfin2 : ∫⁻ x in lwtOm σ c, ‖f x‖ₑ ≤ ∫⁻ x : ℝ, σ x := by
      calc ∫⁻ x in lwtOm σ c, ‖f x‖ₑ ≤ ∫⁻ x : ℝ, ‖f x‖ₑ := setLIntegral_le_lintegral _ _
        _ = ∫⁻ x : ℝ, σ x := lintegral_congr fun x => (hσ x).symm
    calc ∫⁻ x in (czStar σ c)ᶜ, annulusSqfun b j (czBad f σ c) x
        ≤ ∫⁻ x in (czStar σ c)ᶜ, (∑' q : {p : ℤ × ℤ // p ∈ czMax σ c},
            annulusSqfun b j (czBadPiece f q.1) x) :=
          lintegral_mono fun x => annulusSqfun_czBad_le_tsum b j f σ c x
      _ = ∑' q : {p : ℤ × ℤ // p ∈ czMax σ c},
            ∫⁻ x in (czStar σ c)ᶜ, annulusSqfun b j (czBadPiece f q.1) x := hton
      _ ≤ ∑' q : {p : ℤ × ℤ // p ∈ czMax σ c},
            ENNReal.ofReal Cb * ∫⁻ x : ℝ, ‖czBadPiece f q.1 x‖ₑ := ENNReal.tsum_le_tsum hcell
      _ ≤ ∑' q : {p : ℤ × ℤ // p ∈ czMax σ c},
            ENNReal.ofReal Cb * (2 * ∫⁻ x in dyCell q.1.1 q.1.2, ‖f x‖ₑ) :=
          ENNReal.tsum_le_tsum hmass
      _ = ENNReal.ofReal Cb * (2 * ∫⁻ x in lwtOm σ c, ‖f x‖ₑ) := hsum
      _ ≤ ENNReal.ofReal Cb * (2 * ∫⁻ x : ℝ, σ x) := by
          exact mul_le_mul_right (mul_le_mul_right hfin2 2) _
      _ = ENNReal.ofReal (2 * Cb) * ∫⁻ x : ℝ, σ x := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          ring

end Work.BourgainPlan.Maximal
