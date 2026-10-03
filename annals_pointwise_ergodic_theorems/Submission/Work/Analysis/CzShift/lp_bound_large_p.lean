import Mathlib
import Submission.Work.Analysis.CzShift.czOp_adjoint_pairing
import Submission.Work.Analysis.CzShift.lp_bound_small_p
import Submission.Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound
import Submission.Port.Aesm

/-!
# The `L^p` bound, `2 < p < ∞`, for finite sums of shifted convolution operators

Appendix B of Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. **195** (2022): a finite sum of convolution operators whose
kernel family satisfies

* an `L²` bound `‖T‖_{2→2} ≤ A₂` (`hL2`), and
* the off-diagonal ("Hörmander") condition `hoff` with constant `Ak`,

is bounded on `L^p(ℝ;H)` for *every* `1 < p < ∞`, with norm controlled by `C_p (A₂² + Ak + 1)`.

The case `1 < p < 2` is the Calderón--Zygmund/Marcinkiewicz theorem
(`Work.Analysis.CzShift.lp_bound_small_p`, imported below as
`lp_bound_small_p_provider`); the case `2 < p < ∞` is obtained from it by duality, applied to
the *formal adjoint* family `adjKernel K`, `adjSigns ε`:

* `czOp_adjoint_pairing_conj` (Fubini) identifies `czOp D (adjKernel K) (adjSigns ε)` as the
  `L²`-adjoint of `czOp D K ε`;
* `adjoint_l2_bound` transfers the `L²` bound to the adjoint;
* `hoff_adjKernel` transfers the off-diagonal condition (substituting `x ↦ -x`);
* `enorm_integral_inner_le_eLpNorm_mul` is Hölder's inequality for the `H`-valued pairing;
* `Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound` is the standard norming-function duality
  `‖h‖_{L^p} ≤ E` from `|∫ ⟪h, g⟫| ≤ E ‖g‖_{L^{p'}}` for all integrable `g`.
-/

namespace Work.Analysis.CzShift

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

set_option autoImplicit false

/-! ## Hölder conjugacy and Hölder's inequality for the `H`-valued pairing -/

/-- The dual exponent `p / (p - 1)` is Hölder-conjugate to `p` for `1 < p`. -/
theorem holderConjugate_div {p : ℝ} (hp : 1 < p) : Real.HolderConjugate p (p / (p - 1)) := by
  rw [Real.holderConjugate_iff]
  refine ⟨hp, ?_⟩
  have h2 : p - 1 ≠ 0 := ne_of_gt (by linarith)
  have h1 : p ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The `enorm` of an inner product is at most the product of the `enorm`s. -/
theorem enorm_inner_le_mul {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v : H) : ‖inner ℂ u v‖ₑ ≤ ‖u‖ₑ * ‖v‖ₑ := by
  calc ‖inner ℂ u v‖ₑ = ENNReal.ofReal ‖inner ℂ u v‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (‖u‖ * ‖v‖) := ENNReal.ofReal_le_ofReal (norm_inner_le_norm u v)
    _ = ENNReal.ofReal ‖u‖ * ENNReal.ofReal ‖v‖ := ENNReal.ofReal_mul (norm_nonneg u)
    _ = ‖u‖ₑ * ‖v‖ₑ := by rw [ofReal_norm, ofReal_norm]

/-- **Hölder's inequality for the `H`-valued pairing**: for Hölder-conjugate `p, q` and
a.e. strongly measurable `F, G`,
`‖∫ x, ⟪F x, G x⟫‖ₑ ≤ (∫⁻ ‖F‖^p)^{1/p} (∫⁻ ‖G‖^q)^{1/q} = ‖F‖_{L^p} ‖G‖_{L^q}`. -/
theorem enorm_integral_inner_le_eLpNorm_mul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {p q : ℝ} (hpq : p.HolderConjugate q)
    {F G : ℝ → H} (hF : AEStronglyMeasurable F volume) (hG : AEStronglyMeasurable G volume) :
    ‖∫ x, inner ℂ (F x) (G x) ∂volume‖ₑ
      ≤ eLpNorm F (ENNReal.ofReal p) volume * eLpNorm G (ENNReal.ofReal q) volume := by
  have hp1 : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hq0 : 0 < q := by
    have hinv : p⁻¹ + q⁻¹ = 1 := (Real.holderConjugate_iff.mp hpq).2
    have hpinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    have : 0 < q⁻¹ := by linarith
    exact inv_pos.mp this
  calc ‖∫ x, inner ℂ (F x) (G x) ∂volume‖ₑ
      ≤ ∫⁻ x, ‖inner ℂ (F x) (G x)‖ₑ ∂volume := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ‖F x‖ₑ * ‖G x‖ₑ ∂volume :=
        lintegral_mono fun x => enorm_inner_le_mul _ _
    _ ≤ (∫⁻ x, ‖F x‖ₑ ^ p ∂volume) ^ (1 / p) * (∫⁻ x, ‖G x‖ₑ ^ q ∂volume) ^ (1 / q) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hF.enorm hG.enorm
    _ = eLpNorm F (ENNReal.ofReal p) volume * eLpNorm G (ENNReal.ofReal q) volume := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hp0)
              ENNReal.ofReal_ne_top,
            eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hq0)
              ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0.le]

/-! ## Measurability and boundedness of `czOp` -/

/-- `(x, y) ↦ K (x - y)` is a.e. strongly measurable for the product measure. -/
theorem aestronglyMeasurable_sub_prod {K : ℝ → ℂ} (hK : AEStronglyMeasurable K volume) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => K (p.1 - p.2)) (volume.prod volume) := by
  obtain ⟨h, hh, heq⟩ := hK
  refine ⟨fun p => h (p.1 - p.2), hh.comp_measurable (measurable_fst.sub measurable_snd), ?_⟩
  exact (quasiMeasurePreserving_sub_of_right_invariant volume volume).ae_eq heq

/-- `y ↦ K (x - y)` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_sub_left {K : ℝ → ℂ} (hK : AEStronglyMeasurable K volume) (x : ℝ) :
    AEStronglyMeasurable (fun y : ℝ => K (x - y)) volume := by
  obtain ⟨h, hh, heq⟩ := hK
  refine ⟨fun y => h (x - y), hh.comp_measurable (measurable_const.sub measurable_id), ?_⟩
  exact (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae_eq heq

/-- The formal adjoint `x ↦ conj (K (-x))` of an a.e. strongly measurable kernel is a.e. strongly
measurable. -/
theorem aestronglyMeasurable_adjKernel {ι : Type*} {K : ι → ℝ → ℂ} {i : ι}
    (hK : AEStronglyMeasurable (K i) volume) : AEStronglyMeasurable (adjKernel K i) volume := by
  obtain ⟨h, hh, heq⟩ := hK
  refine ⟨fun x => star (h (-x)),
    continuous_star.comp_stronglyMeasurable (hh.comp_measurable measurable_neg), ?_⟩
  filter_upwards [(quasiMeasurePreserving_neg_of_right_invariant volume).ae heq] with x hx
  exact congrArg star hx

/-- `czOp D K ε f` is a.e. strongly measurable for integrable `f` and a.e. strongly measurable
kernels `K i`, `i ∈ D`. -/
theorem czOp_aestronglyMeasurable {ι : Type*} {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (hKmeas : ∀ i ∈ D, AEStronglyMeasurable (K i) volume)
    {f : ℝ → H} (hf : Integrable f volume) :
    AEStronglyMeasurable (czOp D K ε f) volume := by
  have hterm : ∀ i ∈ D,
      AEStronglyMeasurable (fun x : ℝ => ∫ y, K i (x - y) • f y ∂volume) volume := by
    intro i hi
    exact ((aestronglyMeasurable_sub_prod (hKmeas i hi)).smul
      hf.aestronglyMeasurable.comp_snd).integral_prod_right'
  have hsum : AEStronglyMeasurable
      (∑ i ∈ D, fun x : ℝ => ε i • ∫ y, K i (x - y) • f y ∂volume) volume :=
    Finset.aestronglyMeasurable_sum D fun i hi => (hterm i hi).const_smul (ε i)
  convert hsum using 1
  funext x
  simp only [czOp, Finset.sum_apply]

/-- `czOp D K ε f` is bounded (uniformly in `x`) for integrable `f` and pointwise bounded
kernels. -/
theorem norm_czOp_le {ι : Type*} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ)
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    {f : ℝ → H} (hf : Integrable f volume) :
    ∃ B : ℝ, ∀ x, ‖czOp D K ε f x‖ ≤ B := by
  classical
  have hchoice : ∀ i : ι, ∃ C : ℝ, i ∈ D → ∀ x, ‖K i x‖ ≤ C := by
    intro i
    by_cases hi : i ∈ D
    · obtain ⟨C, hC⟩ := hKbdd i hi
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose C hC using hchoice
  refine ⟨∑ i ∈ D, ‖ε i‖ * (C i * ∫ x, ‖f x‖), fun x => ?_⟩
  have hbnd : ∀ i ∈ D, ‖∫ y, K i (x - y) • f y ∂volume‖ ≤ C i * ∫ y, ‖f y‖ := by
    intro i hi
    calc ‖∫ y, K i (x - y) • f y ∂volume‖
        ≤ ∫ y, C i * ‖f y‖ ∂volume := by
          refine norm_integral_le_of_norm_le (f := fun y => K i (x - y) • f y)
            (hf.norm.const_mul (C i)) ?_
          filter_upwards with y
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right (hC i hi (x - y)) (norm_nonneg _)
      _ = C i * ∫ y, ‖f y‖ ∂volume := integral_const_mul _ _
  calc ‖czOp D K ε f x‖ = ‖∑ i ∈ D, ε i • ∫ y, K i (x - y) • f y ∂volume‖ := rfl
    _ ≤ ∑ i ∈ D, ‖ε i • ∫ y, K i (x - y) • f y ∂volume‖ := norm_sum_le _ _
    _ = ∑ i ∈ D, ‖ε i‖ * ‖∫ y, K i (x - y) • f y ∂volume‖ := by
        refine Finset.sum_congr rfl fun i _ => norm_smul _ _
    _ ≤ ∑ i ∈ D, ‖ε i‖ * (C i * ∫ y, ‖f y‖) :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_left (hbnd i hi) (norm_nonneg _)

/-! ## The off-diagonal condition transfers to the adjoint family -/

/-- A set integral of the reflection `f (-x)` over a reflection-invariant set equals the set
integral of `f`. -/
theorem lintegral_neg_comp {f : ℝ → ℝ≥0∞} {S : Set ℝ} (hSmeas : MeasurableSet S)
    (hS : ∀ x, x ∈ S ↔ -x ∈ S) :
    ∫⁻ x in S, f (-x) ∂volume = ∫⁻ x in S, f x ∂volume := by
  have hpt : ∀ x : ℝ, S.indicator (fun x => f (-x)) x = (S.indicator f) (-x) := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hS x).mp hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      intro h
      exact hx ((hS x).mpr h)
  rw [← lintegral_indicator hSmeas (fun x => f (-x)), ← lintegral_indicator hSmeas f]
  simp_rw [hpt]
  exact lintegral_neg_eq_self (S.indicator f)

/-- The off-diagonal (Hörmander) condition of the kernel family `K` transfers to the formal
adjoint family `adjKernel K`, with the same constant: substitute `x ↦ -x`. -/
theorem hoff_adjKernel {ι : Type*} (D : Finset ι) (K : ι → ℝ → ℂ) (Ak : ℝ)
    (hoff : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖K i (x - y) - K i x‖ ≤ ENNReal.ofReal Ak) :
    ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
      ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖adjKernel K i (x - y) - adjKernel K i x‖ ≤ ENNReal.ofReal Ak := by
  intro L hL y hy
  have hSmeas : MeasurableSet {x : ℝ | 50 * L ≤ |x|} :=
    measurableSet_le measurable_const measurable_abs
  have hS : ∀ x : ℝ, x ∈ {x : ℝ | 50 * L ≤ |x|} ↔ -x ∈ {x : ℝ | 50 * L ≤ |x|} := by
    intro x
    simp only [Set.mem_ofPred_eq, abs_neg]
  have hmain : ∀ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖adjKernel K i (x - y) - adjKernel K i x‖
      = ∫⁻ x in {x : ℝ | 50 * L ≤ |x|}, ENNReal.ofReal ‖K i (x - (-y)) - K i x‖ := by
    intro i _
    rw [← lintegral_neg_comp (S := {x : ℝ | 50 * L ≤ |x|}) hSmeas hS
      (f := fun u => ENNReal.ofReal ‖adjKernel K i (u - y) - adjKernel K i u‖)]
    refine lintegral_congr fun x => ?_
    have hsub : adjKernel K i (-x - y) - adjKernel K i (-x) = star (K i (x + y) - K i x) := by
      rw [adjKernel_apply, adjKernel_apply,
        show -(-x - y) = x + y by ring, show -(-x) = x by ring]
      exact (map_sub (starRingEnd ℂ) (K i (x + y)) (K i x)).symm
    rw [hsub, norm_star, show x - (-y) = x + y by ring]
  calc ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
        ENNReal.ofReal ‖adjKernel K i (x - y) - adjKernel K i x‖
      = ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
          ENNReal.ofReal ‖K i (x - (-y)) - K i x‖ := Finset.sum_congr rfl hmain
    _ ≤ ENNReal.ofReal Ak := hoff L hL (-y) (by rw [abs_neg]; exact hy)

/-! ## The `L²` bound transfers to the adjoint family -/

/-- The `L²` bound for `czOp D K ε` transfers to its formal adjoint
`czOp D (adjKernel K) (adjSigns ε)` with the same constant. -/
theorem adjoint_l2_bound {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (A2 : ℝ) (hA2 : 0 < A2)
    (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1)
    (hKmeas : ∀ i ∈ D, AEStronglyMeasurable (K i) volume)
    (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
    (hL2 : ∀ f : ℝ → H, Integrable f volume → MemLp f 2 volume →
      eLpNorm (czOp D K ε f) 2 volume ≤ ENNReal.ofReal A2 * eLpNorm f 2 volume) :
    ∀ g : ℝ → H, Integrable g volume →
      eLpNorm (czOp D (adjKernel K) (adjSigns ε) g) 2 volume
        ≤ ENNReal.ofReal A2 * eLpNorm g 2 volume := by
  have hKmeas' : ∀ i ∈ D, AEStronglyMeasurable (adjKernel K i) volume :=
    fun i hi => aestronglyMeasurable_adjKernel (hKmeas i hi)
  have hKbdd' : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖adjKernel K i x‖ ≤ C := by
    intro i hi
    obtain ⟨C, hC⟩ := hKbdd i hi
    exact ⟨C, fun x => by rw [adjKernel_apply, norm_star]; exact hC (-x)⟩
  intro g hg
  by_cases hgtop : eLpNorm g 2 volume = ⊤
  · rw [hgtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hA2)]
    exact le_top
  have hE : ENNReal.ofReal A2 * eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgtop
  have hpair : ∀ φ : ℝ → H, Integrable φ volume →
      ‖∫ x, inner ℂ (czOp D (adjKernel K) (adjSigns ε) g x) (φ x) ∂volume‖ₑ
        ≤ (ENNReal.ofReal A2 * eLpNorm g 2 volume)
            * eLpNorm φ (ENNReal.ofReal (2 / (2 - 1))) volume := by
    intro φ hφ
    have hswap := czOp_adjoint_pairing_conj (H := H) D (adjKernel K) (adjSigns ε) hKmeas' hKbdd' g φ hg hφ
    have hKK : czOp (H := H) D (adjKernel (adjKernel K)) (adjSigns (adjSigns ε)) = czOp (H := H) D K ε := by
      congr 1
      · funext i x
        simp only [adjKernel_apply, neg_neg, star_star]
      · funext i
        simp only [adjSigns_apply, star_star]
    rw [hswap, hKK, show (2 : ℝ) / (2 - 1) = 2 by norm_num]
    calc ‖∫ x, inner ℂ (g x) (czOp D K ε φ x) ∂volume‖ₑ
        ≤ eLpNorm g 2 volume * eLpNorm (czOp D K ε φ) 2 volume := by
          simpa only [ENNReal.ofReal_ofNat] using
            enorm_integral_inner_le_eLpNorm_mul (p := 2) (q := 2)
              (by rw [Real.holderConjugate_iff]; norm_num)
              hg.aestronglyMeasurable (czOp_aestronglyMeasurable D K ε hKmeas hφ)
      _ ≤ eLpNorm g 2 volume * (ENNReal.ofReal A2 * eLpNorm φ 2 volume) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          by_cases hφtop : eLpNorm φ 2 volume = ⊤
          · rw [hφtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hA2)]
            exact le_top
          · exact hL2 φ hφ (lt_top_iff_ne_top.mpr hφtop)
      _ = (ENNReal.ofReal A2 * eLpNorm g 2 volume) * eLpNorm φ (ENNReal.ofReal 2) volume := by
          rw [ENNReal.ofReal_ofNat]
          ac_rfl
  have hmain := Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound
    (czOp D (adjKernel K) (adjSigns ε) g) one_lt_two
    (czOp_aestronglyMeasurable D (adjKernel K) (adjSigns ε) hKmeas' hg)
    (norm_czOp_le D (adjKernel K) (adjSigns ε) hKbdd' hg)
    (ENNReal.ofReal A2 * eLpNorm g 2 volume) hE hpair
  simpa only [ENNReal.ofReal_ofNat] using hmain

/-! ## The small-exponent (`1 < p < 2`) case

The Calderón--Zygmund/Marcinkiewicz bound for `1 < p < 2` is proved in this workspace as
`Work.Analysis.CzShift.weak_type_one_of_hoff` (weak type `(1,1)`, constant
`24 A₂² + 4 Ak + 100`) followed by Marcinkiewicz interpolation
(`Work.Analysis.CzShift.lp_bound_small_p`).  We record it here in the form needed below. -/
theorem lp_bound_small_p_provider {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (Ak A2 : ℝ)
      (hAk : 0 ≤ Ak) (hA2 : 0 < A2) (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1)
      (hKmeas : ∀ i ∈ D, MeasureTheory.AEStronglyMeasurable (K i) MeasureTheory.volume)
      (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
      (hoff : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
        ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ENNReal.ofReal ‖K i (x - y) - K i x‖ ≤ ENNReal.ofReal Ak)
      (hL2 : ∀ f : ℝ → H, MeasureTheory.Integrable f →
        MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D K ε f) 2 MeasureTheory.volume
          ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2 MeasureTheory.volume),
      ∀ f : ℝ → H, MeasureTheory.Integrable f →
        MeasureTheory.eLpNorm (czOp D K ε f) (ENNReal.ofReal p) MeasureTheory.volume
          ≤ ENNReal.ofReal (C * (A2 ^ 2 + Ak + 1))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume :=
  lp_bound_small_p hp1 hp2

/-! ## The main theorem: `L^p` for `2 < p < ∞` -/

/-- **The `L^p` bound for `2 < p < ∞`** for a finite sum of convolution operators with bounded
kernels, by duality from the case `1 < p < 2` applied to the adjoint family
`K* i u = conj (K i (-u))`, which satisfies the same size, off-diagonal and `L²` bounds.

The adjoint of `czOp D K ε` is `czOp D K* (fun i => conj (ε i))`, so duality gives
`‖czOp D K ε‖_{L^p → L^p} = ‖czOp D K* ε̄‖_{L^{p'} → L^{p'}}` for `p' = p/(p-1)`, and the
`p' < 2` case is `Work.Analysis.CzShift.lp_bound_small_p`. -/
theorem lp_bound_large_p {p : ℝ} (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (D : Finset ι) (K : ι → ℝ → ℂ) (ε : ι → ℂ) (Ak A2 : ℝ)
      (hAk : 0 ≤ Ak) (hA2 : 0 < A2) (hε : ∀ i ∈ D, ‖ε i‖ ≤ 1)
      (hKmeas : ∀ i ∈ D, MeasureTheory.AEStronglyMeasurable (K i) MeasureTheory.volume)
      (hKbdd : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖K i x‖ ≤ C)
      (hoff : ∀ L : ℝ, 0 < L → ∀ y : ℝ, |y| ≤ L / 2 →
        ∑ i ∈ D, ∫⁻ x in {x : ℝ | 50 * L ≤ |x|},
            ENNReal.ofReal ‖K i (x - y) - K i x‖ ≤ ENNReal.ofReal Ak)
      (hL2 : ∀ f : ℝ → H, MeasureTheory.Integrable f →
        MeasureTheory.MemLp f 2 MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D K ε f) 2 MeasureTheory.volume
          ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2 MeasureTheory.volume),
      ∀ f : ℝ → H, MeasureTheory.Integrable f →
        MeasureTheory.eLpNorm (czOp D K ε f) (ENNReal.ofReal p) MeasureTheory.volume
          ≤ ENNReal.ofReal (C * (A2 ^ 2 + Ak + 1))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume := by
  have hp1 : 1 < p := by linarith
  have hp1' : (0 : ℝ) < p - 1 := by linarith
  have hp'1 : 1 < p / (p - 1) := by rw [lt_div_iff₀ hp1']; linarith
  have hp'2 : p / (p - 1) < 2 := by rw [div_lt_iff₀ hp1']; linarith
  obtain ⟨C', hC'pos, hC'⟩ := lp_bound_small_p_provider hp'1 hp'2
  refine ⟨C', hC'pos, ?_⟩
  intro ι H _ _ _ D K ε Ak A2 hAk hA2 hε hKmeas hKbdd hoff hL2 f hf
  have hKmeas' : ∀ i ∈ D, AEStronglyMeasurable (adjKernel K i) volume :=
    fun i hi => aestronglyMeasurable_adjKernel (hKmeas i hi)
  have hKbdd' : ∀ i ∈ D, ∃ C : ℝ, ∀ x, ‖adjKernel K i x‖ ≤ C := by
    intro i hi
    obtain ⟨C, hC⟩ := hKbdd i hi
    exact ⟨C, fun x => by rw [adjKernel_apply, norm_star]; exact hC (-x)⟩
  have hε' : ∀ i ∈ D, ‖adjSigns ε i‖ ≤ 1 := fun i hi => by
    rw [norm_adjSigns]; exact hε i hi
  have hoff' := hoff_adjKernel D K Ak hoff
  have hL2' := adjoint_l2_bound D K ε A2 hA2 hε hKmeas hKbdd hL2
  have hsmall : ∀ g : ℝ → H, Integrable g volume →
      eLpNorm (czOp D (adjKernel K) (adjSigns ε) g) (ENNReal.ofReal (p / (p - 1))) volume
        ≤ ENNReal.ofReal (C' * (A2 ^ 2 + Ak + 1))
            * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume :=
    hC' D (adjKernel K) (adjSigns ε) Ak A2 hAk hA2 hε' hKmeas' hKbdd' hoff'
      (fun f hf _ => hL2' f hf)
  by_cases hftop : eLpNorm f (ENNReal.ofReal p) volume = ⊤
  · rw [hftop, ENNReal.mul_top
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : (0 : ℝ) < C' * (A2 ^ 2 + Ak + 1)))]
    exact le_top
  · refine Commons.Analysis.Lp.eLpNorm_le_of_pairing_bound _ hp1
      (czOp_aestronglyMeasurable D K ε hKmeas hf)
      (norm_czOp_le D K ε hKbdd hf)
      (ENNReal.ofReal (C' * (A2 ^ 2 + Ak + 1)) * eLpNorm f (ENNReal.ofReal p) volume)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hftop) ?_
    intro g hg
    rw [czOp_adjoint_pairing_conj (H := H) D K ε hKmeas hKbdd f g hf hg]
    calc ‖∫ x, inner ℂ (f x) (czOp D (adjKernel K) (adjSigns ε) g x) ∂volume‖ₑ
        ≤ eLpNorm f (ENNReal.ofReal p) volume
            * eLpNorm (czOp D (adjKernel K) (adjSigns ε) g) (ENNReal.ofReal (p / (p - 1)))
                volume :=
          enorm_integral_inner_le_eLpNorm_mul (holderConjugate_div hp1)
            hf.aestronglyMeasurable
            (czOp_aestronglyMeasurable D (adjKernel K) (adjSigns ε) hKmeas' hg)
      _ ≤ eLpNorm f (ENNReal.ofReal p) volume
            * (ENNReal.ofReal (C' * (A2 ^ 2 + Ak + 1))
                * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume) :=
          mul_le_mul_of_nonneg_left (hsmall g hg) zero_le
      _ = (ENNReal.ofReal (C' * (A2 ^ 2 + Ak + 1)) * eLpNorm f (ENNReal.ofReal p) volume)
            * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume := by
          ac_rfl

end

end Work.Analysis.CzShift
