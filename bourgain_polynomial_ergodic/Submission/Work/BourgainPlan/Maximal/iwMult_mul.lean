import Mathlib
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.mikhlin_multiplier_lift
import Submission.Work.BourgainPlan.Maximal.memLp_comp_iwRep
import Submission.Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Work.Thm52.integrable_circleLift

namespace Work.BourgainPlan.Maximal

open MeasureTheory FourierTransform Filter
open scoped FourierTransform ENNReal Topology

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-!
# Products of `IWMult` symbols

`IWMult r ψ A` (`Maximal/iw_superset.lean`) says that the compactly supported lift
`Thm52.circleLift ψ` is an `L^{2r}(ℝ)`-multiplier with norm `≤ A`, tested on integrable inputs:

`∀ g, Integrable g → ∫⁻ x, ‖𝓕⁻ (circleLift ψ · 𝓕 g) x‖ₑ ^ (2r) ≤ A^{2r} ∫⁻ x, ‖g x‖ₑ ^ (2r)`.

For *measurable* symbols this is a genuine operator-norm bound, and multiplier norms are
submultiplicative; the pointwise product is therefore again an `IWMult`, with the product of the
constants.

## Layout of the proof

* §1 basic facts about the fundamental-domain lift (`circleLift`): multiplicativity, a.e. strong
  measurability and a.e. boundedness coming from `MemLp ψ ⊤` on the circle;
* §2 the multiplier form `multForm m g = 𝓕⁻ (m · 𝓕 g)` and the identification of `IWMult` with the
  bound on `multForm`;
* §3 `L²`-facts: Plancherel on `L¹ ∩ L²`, and the continuity of multiplication by an a.e. bounded
  symbol on `L²`;
* §4 the core of the argument: for an input `g ∈ L¹ ∩ L²`, multiply the `L²`-class of
  `h = 𝓕⁻ (m₁ · 𝓕 g)` by `m₂` in `L²` and read the result back off in `L^q`, using an
  a.e.-convergent subsequence and Fatou;
* §5 pass from `L¹ ∩ L²` inputs to all integrable inputs by truncation and Fatou;
* §6 assemble the target statement.
-/

/-! ## 1. The fundamental-domain lift -/

/-- **The lift is multiplicative**: on the fundamental domain both sides are the pointwise product
of the values on the circle, and off it both sides vanish. -/
lemma circleLift_mul (ψ₁ ψ₂ : Circ → ℂ) :
    Thm52.circleLift (fun ξ => ψ₁ ξ * ψ₂ ξ)
      = fun x : ℝ => Thm52.circleLift ψ₁ x * Thm52.circleLift ψ₂ x := by
  funext x
  by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Thm52.circleLift_of_mem hx, Thm52.circleLift_of_mem hx, Thm52.circleLift_of_mem hx]
  · rw [Thm52.circleLift_of_notMem hx, Thm52.circleLift_of_notMem hx,
      Thm52.circleLift_of_notMem hx, zero_mul]

/-- The covering map restricted to the fundamental domain, followed by the negation of the circle,
is measure preserving onto the (normalised) Haar measure of the circle. -/
lemma measurePreserving_neg_coe :
    MeasurePreserving (fun x : ℝ => -(x : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
      (AddCircle.haarAddCircle (T := 1)) := by
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle (T := 1) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  have hmk := AddCircle.measurePreserving_mk (T := 1) (-(1 / 2 : ℝ))
  rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num] at hmk
  have hneg : MeasurePreserving (fun y : AddCircle (1 : ℝ) => -y)
      (volume : Measure (AddCircle (1 : ℝ))) (volume : Measure (AddCircle (1 : ℝ))) :=
    Measure.measurePreserving_neg _
  have h : MeasurePreserving (fun x : ℝ => -(x : AddCircle (1 : ℝ)))
      (volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) (volume : Measure (AddCircle (1 : ℝ))) :=
    hneg.comp hmk
  rwa [hvol] at h

/-- The lift is the indicator of the fundamental domain applied to the lifted function. -/
lemma circleLift_eq_indicator (ψ : Circ → ℂ) :
    Thm52.circleLift ψ = (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
      (fun x : ℝ => ψ (-(x : AddCircle (1 : ℝ)))) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Set.indicator_of_mem hx, Thm52.circleLift_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Thm52.circleLift_of_notMem hx]

/-- The pullback of a circle function along the negated covering map is a.e. strongly measurable on
the fundamental domain. -/
lemma aestronglyMeasurable_neg_coe {ψ : Circ → ℂ}
    (hψ : AEStronglyMeasurable ψ (AddCircle.haarAddCircle (T := 1))) :
    AEStronglyMeasurable (fun x : ℝ => ψ (-(x : AddCircle (1 : ℝ))))
      (volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))) :=
  hψ.comp_measurePreserving measurePreserving_neg_coe

/-- **A.e. boundedness of the lift of a circle `L^∞` function.** -/
lemma exists_ae_bound_circleLift {ψ : Circ → ℂ}
    (hψ : MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x : ℝ ∂volume, ‖Thm52.circleLift ψ x‖ ≤ B := by
  have htop : essSup (fun y => ‖ψ y‖ₑ) (AddCircle.haarAddCircle (T := 1)) < ⊤ := by
    have h := hψ.eLpNorm_lt_top
    rwa [eLpNorm_exponent_top hψ.aestronglyMeasurable, eLpNormEssSup_eq_essSup_enorm] at h
  set B : ℝ := (essSup (fun y => ‖ψ y‖ₑ) (AddCircle.haarAddCircle (T := 1))).toReal with hBdef
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hB : ∀ᵐ (y : AddCircle (1 : ℝ)) ∂(AddCircle.haarAddCircle (T := 1)),
      ‖ψ y‖ₑ ≤ ENNReal.ofReal B := by
    rw [hBdef, ENNReal.ofReal_toReal htop.ne]
    exact ae_le_essSup ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
  have hB' : ∀ᵐ (x : ℝ) ∂(volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))),
      ‖ψ (-(x : AddCircle (1 : ℝ)))‖ ≤ B := by
    filter_upwards [Measure.QuasiMeasurePreserving.ae (f := fun x : ℝ => -(x : AddCircle (1 : ℝ)))
      measurePreserving_neg_coe.quasiMeasurePreserving hB] with x hx
    exact (ENNReal.ofReal_le_ofReal_iff hB0).mp (by rwa [← ofReal_norm] at hx)
  refine ⟨B, hB0, ?_⟩
  rw [circleLift_eq_indicator]
  have h1 : ∀ᵐ x ∂(volume.restrict (Set.Ioc (-(1 / 2 : ℝ)) (1 / 2))),
      ‖(Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)).indicator
        (fun x : ℝ => ψ (-(x : AddCircle (1 : ℝ)))) x‖ ≤ B := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc, hB'] with x hxs hx
    rwa [Set.indicator_of_mem hxs]
  exact ((ae_restrict_iff' measurableSet_Ioc).mp h1).mono fun x hx => by
    by_cases hmem : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
    · exact hx hmem
    · rw [Set.indicator_of_notMem hmem, norm_zero]; exact hB0

/-- The lift of a circle `L^∞` function is a.e. strongly measurable on `ℝ`. -/
lemma aestronglyMeasurable_circleLift {ψ : Circ → ℂ}
    (hψ : MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1))) :
    AEStronglyMeasurable (Thm52.circleLift ψ) volume := by
  rw [circleLift_eq_indicator]
  exact (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
    (aestronglyMeasurable_neg_coe hψ.aestronglyMeasurable)

/-! ## 2. The multiplier form -/

/-- The action of the multiplier with symbol `m` on an integrable function `g`, in the `L¹`-form
used by `IWMult`: `𝓕⁻ (m · 𝓕 g)`. -/
def multForm (m g : ℝ → ℂ) : ℝ → ℂ := 𝓕⁻ (fun ξ => m ξ * 𝓕 g ξ)

lemma multForm_def (m g : ℝ → ℂ) : multForm m g = 𝓕⁻ (fun ξ => m ξ * 𝓕 g ξ) := rfl

/-- `IWMult` is exactly the `L^q`-bound for the multiplier form of the lift. -/
lemma iwMult_iff_multForm {r : ℕ} {ψ : Circ → ℂ} {A : ℝ} :
    IWMult r ψ A ↔ ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖multForm (Thm52.circleLift ψ) g x‖ₑ ^ (2 * (r : ℝ)) ≤
        ENNReal.ofReal (A ^ (2 * (r : ℝ))) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 * (r : ℝ)) :=
  Iff.rfl

/-! ## 3. `L²`-facts -/

/-- The inverse Fourier transform of an `L¹ ∩ L²` function is `L²` (Plancherel). -/
lemma memLp_fourierInv_of_memLp_one_two {f : ℝ → ℂ} (h1 : MemLp f 1 volume)
    (h2 : MemLp f 2 volume) : MemLp (𝓕⁻ f) 2 volume :=
  MemLp.ae_eq (Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv h1 h2)
    (Lp.memLp (𝓕⁻ (MemLp.toLp f h2)))

/-- The Fourier transform of an `L¹ ∩ L²` function is `L²` (Plancherel). -/
lemma memLp_fourier_of_memLp_one_two {f : ℝ → ℂ} (h1 : MemLp f 1 volume)
    (h2 : MemLp f 2 volume) : MemLp (𝓕 f) 2 volume :=
  MemLp.ae_eq (Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp h1 h2)
    (Lp.memLp (𝓕 (MemLp.toLp f h2)))

/-- The `L²` Fourier transform of `𝓕⁻ θ` is `θ` (as `L²` classes), for `θ ∈ L¹ ∩ L²`. -/
lemma fourier_toLp_fourierInv {θ : ℝ → ℂ} (h1 : MemLp θ 1 volume) (h2 : MemLp θ 2 volume) :
    𝓕 (MemLp.toLp (𝓕⁻ θ) (memLp_fourierInv_of_memLp_one_two h1 h2)) = MemLp.toLp θ h2 := by
  have hL2 := memLp_fourierInv_of_memLp_one_two h1 h2
  have hae : (𝓕⁻ θ) =ᵐ[volume]
      ((𝓕⁻ (MemLp.toLp θ h2) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    (Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv h1 h2).symm
  have heq : MemLp.toLp (𝓕⁻ θ) hL2 = 𝓕⁻ (MemLp.toLp θ h2) := by
    rw [MemLp.toLp_congr hL2 (Lp.memLp _) hae, Lp.toLp_coeFn]
  rw [heq, FourierInvPair.fourier_fourierInv_eq]

/-- A pointwise bound for the inverse Fourier transform: `‖𝓕⁻ f x‖ ≤ ∫ y, ‖f y‖`. -/
lemma norm_fourierInv_le (f : ℝ → ℂ) (x : ℝ) : ‖𝓕⁻ f x‖ ≤ ∫ y : ℝ, ‖f y‖ := by
  rw [Real.fourierInv_eq']
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h1 : ‖Complex.exp (↑(2 * Real.pi * inner ℝ y x) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  simp only [norm_smul, h1, one_mul]

/-- **Multiplication by an a.e. bounded symbol is bounded on `L²`.** -/
lemma eLpNorm_mul_le_of_ae_bound {m f : ℝ → ℂ} {B : ℝ}
    (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) :
    eLpNorm (fun x => m x * f x) 2 volume ≤ ENNReal.ofReal B * eLpNorm f 2 volume := by
  by_cases hf : AEStronglyMeasurable f volume
  · exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hme.mul hf)
      (hmb.mono fun x hx => by
        show ‖m x * f x‖ ≤ B * ‖f x‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)) 2
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    by_cases hB : 0 < B
    · rw [ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hB)]; exact le_top
    · have h0 : (fun x => m x * f x) =ᵐ[volume] 0 := by
        filter_upwards [hmb] with x hx
        have : m x = 0 := norm_le_zero_iff.mp (hx.trans (not_lt.mp hB))
        simp [this]
      rw [eLpNorm_congr_ae h0, eLpNorm_zero]; exact zero_le

/-- The `MemLp` proof attached to the definition of `lpMulBdd`. -/
lemma memLp_mul_lpBdd {m : ℝ → ℂ} {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (Y : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun ξ : ℝ => m ξ * (Y : ℝ → ℂ) ξ) 2 volume :=
  MemLp.of_le_mul (c := B) (Lp.memLp Y) (hme.mul (Lp.memLp Y).aestronglyMeasurable)
    (hmb.mono fun x hx => by
      show ‖m x * (Y : ℝ → ℂ) x‖ ≤ B * ‖(Y : ℝ → ℂ) x‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- **The `L²`-multiplier operator** with symbol `m` (a.e. bounded by `B`). -/
def lpMulBdd (m : ℝ → ℂ) {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (Y : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  𝓕⁻ (MemLp.toLp (fun ξ : ℝ => m ξ * (Y : ℝ → ℂ) ξ) (memLp_mul_lpBdd hme hmb Y))

/-- The `L²` inverse Fourier transform is an isometry (enorm form). -/
lemma enorm_fourierInv_lp (Y : Lp ℂ 2 (volume : Measure ℝ)) : ‖𝓕⁻ Y‖ₑ = ‖Y‖ₑ := by
  show ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm Y‖ₑ = ‖Y‖ₑ
  rw [← ofReal_norm, ← ofReal_norm]
  exact congrArg ENNReal.ofReal ((Lp.fourierTransformₗᵢ ℝ ℂ).symm.norm_map Y)

/-- The difference of two `lpMulBdd` values. -/
lemma lpMulBdd_sub {m : ℝ → ℂ} {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (Y Y' : Lp ℂ 2 (volume : Measure ℝ)) :
    lpMulBdd m hme hmb Y - lpMulBdd m hme hmb Y'
      = 𝓕⁻ (MemLp.toLp ((fun ξ : ℝ => m ξ * (Y : ℝ → ℂ) ξ) - fun ξ : ℝ => m ξ * (Y' : ℝ → ℂ) ξ)
          ((memLp_mul_lpBdd hme hmb Y).sub (memLp_mul_lpBdd hme hmb Y'))) := by
  have hms : ∀ A B : Lp ℂ 2 (volume : Measure ℝ),
      𝓕⁻ A - 𝓕⁻ B = 𝓕⁻ (A - B) := fun A B =>
    (LinearIsometryEquiv.map_sub (Lp.fourierTransformₗᵢ ℝ ℂ).symm A B).symm
  rw [lpMulBdd, lpMulBdd, hms, MemLp.toLp_sub]

/-- The `L²`-multiplier operator is Lipschitz with constant `B`. -/
lemma norm_lpMulBdd_sub {m : ℝ → ℂ} {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (Y Y' : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖lpMulBdd m hme hmb Y - lpMulBdd m hme hmb Y'‖ₑ ≤
      ENNReal.ofReal B * ‖Y - Y'‖ₑ := by
  have hLHS : ‖lpMulBdd m hme hmb Y - lpMulBdd m hme hmb Y'‖ₑ
      = eLpNorm ((fun ξ : ℝ => m ξ * (Y : ℝ → ℂ) ξ) - fun ξ : ℝ => m ξ * (Y' : ℝ → ℂ) ξ)
          2 volume := by
    rw [lpMulBdd_sub hme hmb Y Y', enorm_fourierInv_lp]
    exact Lp.enorm_toLp _
  rw [hLHS]
  have hle : eLpNorm ((fun ξ : ℝ => m ξ * (Y : ℝ → ℂ) ξ) - fun ξ : ℝ => m ξ * (Y' : ℝ → ℂ) ξ)
      2 volume ≤ ENNReal.ofReal B * eLpNorm ((Y : ℝ → ℂ) - (Y' : ℝ → ℂ)) 2 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := B)
      ((hme.mul (Lp.aestronglyMeasurable Y)).sub (hme.mul (Lp.aestronglyMeasurable Y'))) ?_ 2
    filter_upwards [hmb] with ξ hξ
    show ‖m ξ * (Y : ℝ → ℂ) ξ - m ξ * (Y' : ℝ → ℂ) ξ‖
      ≤ B * ‖(Y : ℝ → ℂ) ξ - (Y' : ℝ → ℂ) ξ‖
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _)
  refine hle.trans (le_of_eq ?_)
  congr 1
  exact (eLpNorm_congr_ae (Lp.coeFn_sub Y Y').symm).trans (Lp.enorm_def (Y - Y')).symm

/-- Real form of the Lipschitz bound for the `L²`-multiplier operator. -/
lemma norm_lpMulBdd_sub_le {m : ℝ → ℂ} {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (hB : 0 ≤ B) (Y Y' : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖lpMulBdd m hme hmb Y - lpMulBdd m hme hmb Y'‖ ≤ B * ‖Y - Y'‖ := by
  have h := norm_lpMulBdd_sub hme hmb Y Y'
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hB] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (norm_nonneg _))).mp h

/-- Continuity of the `L²`-multiplier operator. -/
lemma tendsto_lpMulBdd {m : ℝ → ℂ} {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (hB : 0 ≤ B) {ι : Type*} {l : Filter ι}
    {Y : ι → Lp ℂ 2 (volume : Measure ℝ)} {Z : Lp ℂ 2 (volume : Measure ℝ)}
    (hY : Tendsto Y l (𝓝 Z)) :
    Tendsto (fun i => lpMulBdd m hme hmb (Y i)) l (𝓝 (lpMulBdd m hme hmb Z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hY ⊢
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => norm_lpMulBdd_sub_le hme hmb hB (Y i) Z) ?_
  simpa only [mul_zero] using hY.const_mul B

/-! ## 4. The core: inputs in `L¹ ∩ L²` -/

/-- Truncation of a function to the compact interval `Icc (-k) k`. -/
def truncLp (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ := (Set.Icc (-(k : ℝ)) (k : ℝ)).indicator f

@[simp] lemma truncLp_of_mem {f : ℝ → ℂ} {k : ℕ} {x : ℝ}
    (hx : x ∈ Set.Icc (-(k : ℝ)) (k : ℝ)) : truncLp f k x = f x :=
  Set.indicator_of_mem hx f

@[simp] lemma truncLp_of_notMem {f : ℝ → ℂ} {k : ℕ} {x : ℝ}
    (hx : x ∉ Set.Icc (-(k : ℝ)) (k : ℝ)) : truncLp f k x = 0 :=
  Set.indicator_of_notMem hx f

lemma norm_truncLp_le (f : ℝ → ℂ) (k : ℕ) (x : ℝ) : ‖truncLp f k x‖ ≤ ‖f x‖ := by
  by_cases hx : x ∈ Set.Icc (-(k : ℝ)) (k : ℝ)
  · rw [truncLp_of_mem hx]
  · rw [truncLp_of_notMem hx, norm_zero]
    exact norm_nonneg _

lemma truncLp_memLp {f : ℝ → ℂ} {p : ℝ≥0∞} (hf : MemLp f p volume) (k : ℕ) :
    MemLp (truncLp f k) p volume := by
  exact (eLpNorm_mono (hf.aestronglyMeasurable.indicator measurableSet_Icc)
    (fun x => norm_truncLp_le f k x)).trans_lt hf.eLpNorm_lt_top

/-- A bounded compactly supported measurable function is integrable. -/
lemma integrable_truncLp {f : ℝ → ℂ} {C : ℝ} (hf : AEStronglyMeasurable f volume)
    (hb : ∀ x : ℝ, ‖f x‖ ≤ C) (k : ℕ) : Integrable (truncLp f k) volume := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hb 0)
  have hvol : volume (Set.Icc (-(k : ℝ)) (k : ℝ)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hind : Integrable ((Set.Icc (-(k : ℝ)) (k : ℝ)).indicator (fun _ : ℝ => C)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const hvol (by simp))
  refine Integrable.mono' hind (hf.indicator measurableSet_Icc) ?_
  filter_upwards with x
  by_cases hx : x ∈ Set.Icc (-(k : ℝ)) (k : ℝ)
  · rw [Set.indicator_of_mem hx, truncLp_of_mem hx]
    exact hb x
  · rw [Set.indicator_of_notMem hx, truncLp_of_notMem hx, norm_zero]

/-- `∫⁻ ‖f‖ₑ^2` is finite for an `L²` function. -/
lemma lintegral_enorm_sq_ne_top {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ)) ≠ ⊤ := by
  have hint : Integrable (fun x : ℝ => ‖f x‖ ^ (2 : ℝ)) volume :=
    hf.integrable_norm_rpow (by norm_num) (by norm_num)
  have hpt : ∀ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖f x‖ ^ (2 : ℝ)) := by
    intro x
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), ofReal_norm]
  have h1 : (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ))
      = ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ (2 : ℝ)) := by
    rw [lintegral_congr hpt]
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)).symm
  rw [h1]
  exact ENNReal.ofReal_ne_top

/-- **The truncations of an `L²` function converge to it in `L²`.** -/
lemma tendsto_eLpNorm_truncLp_sub {h : ℝ → ℂ} (hh2 : MemLp h 2 volume) :
    Tendsto (fun k : ℕ => eLpNorm (truncLp h k - h) 2 volume) atTop (𝓝 0) := by
  have hbound : (∫⁻ x : ℝ, ‖h x‖ₑ ^ (2 : ℝ)) ≠ ⊤ := lintegral_enorm_sq_ne_top hh2
  have hlim : Tendsto (fun k : ℕ => ∫⁻ x : ℝ, ‖truncLp h k x - h x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    have hmain := MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (F := fun k x => ‖truncLp h k x - h x‖ₑ ^ (2 : ℝ)) (f := fun _ => (0 : ℝ≥0∞))
      (bound := fun x => ‖h x‖ₑ ^ (2 : ℝ)) (fun k => ?_) (fun k => ?_) hbound ?_
    · simpa using hmain
    · exact (((truncLp_memLp hh2 k).sub hh2).aemeasurable).enorm.pow_const (2 : ℝ)
    · filter_upwards with x
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      by_cases hx : x ∈ Set.Icc (-(k : ℝ)) (k : ℝ)
      · rw [truncLp_of_mem hx, sub_self, enorm_zero]
        exact bot_le
      · rw [truncLp_of_notMem hx]
        simp
    · filter_upwards with x
      have hev : ∀ᶠ k : ℕ in atTop,
          ‖truncLp h k x - h x‖ₑ ^ (2 : ℝ) = (0 : ℝ≥0∞) := by
        filter_upwards [eventually_ge_atTop ⌈|x|⌉₊] with k hk
        have hx : x ∈ Set.Icc (-(k : ℝ)) (k : ℝ) := by
          rw [Set.mem_Icc]
          have hkx : |x| ≤ (k : ℝ) := le_trans (Nat.le_ceil |x|) (by exact_mod_cast hk)
          exact abs_le.mp hkx
        rw [truncLp_of_mem hx, sub_self, enorm_zero]
        simp
      exact Tendsto.congr' (hev.mono fun k hk => hk.symm) tendsto_const_nhds
  have h2 : Tendsto (fun k : ℕ =>
      (∫⁻ x : ℝ, ‖truncLp h k x - h x‖ₑ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) atTop (𝓝 0) := by
    have hzero : (0 : ℝ≥0∞) ^ ((1 : ℝ) / 2) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    have := (ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0 |>.comp hlim
    rwa [hzero] at this
  refine Filter.Tendsto.congr' ?_ h2
  filter_upwards with k
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    ((truncLp_memLp hh2 k).sub hh2).aestronglyMeasurable]
  norm_num

/-- `m · v ∈ L¹ ∩ L²` for `m` a.e. bounded (by `B`) and `v ∈ L¹ ∩ L²`. -/
lemma memLp_bdd_mul_one_two {m v : ℝ → ℂ} {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (hv1 : MemLp v 1 volume) (hv2 : MemLp v 2 volume) :
    MemLp (fun ξ : ℝ => m ξ * v ξ) 1 volume ∧
      MemLp (fun ξ : ℝ => m ξ * v ξ) 2 volume := by
  have key : ∀ {p : ℝ≥0∞}, MemLp v p volume → MemLp (fun ξ : ℝ => m ξ * v ξ) p volume := by
    intro p hv
    exact MemLp.of_le_mul (c := B) hv (hme.mul hv.aestronglyMeasurable)
      (hmb.mono fun ξ hξ => by
        show ‖m ξ * v ξ‖ ≤ B * ‖v ξ‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _))
  exact ⟨key hv1, key hv2⟩

/-- `m · 𝓕 u ∈ L¹ ∩ L²` for `m` integrable and a.e. bounded and `u ∈ L¹ ∩ L²`. -/
lemma memLp_bdd_mul_fourier {m u : ℝ → ℂ} {B : ℝ} (hmi : Integrable m volume)
    (hme : AEStronglyMeasurable m volume) (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B)
    (hu1 : MemLp u 1 volume) (hu2 : MemLp u 2 volume) :
    MemLp (fun ξ : ℝ => m ξ * 𝓕 u ξ) 1 volume ∧
      MemLp (fun ξ : ℝ => m ξ * 𝓕 u ξ) 2 volume := by
  have hF2 : MemLp (𝓕 u) 2 volume := memLp_fourier_of_memLp_one_two hu1 hu2
  have hFm : AEStronglyMeasurable (𝓕 u) volume :=
    (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier hu1).aestronglyMeasurable
  have hFb : ∀ᵐ x ∂volume, ‖𝓕 u x‖ ≤ ∫ y : ℝ, ‖u y‖ :=
    Filter.Eventually.of_forall fun x => Commons.Analysis.CalderonZygmund.norm_fourier_le u x
  have h2 : MemLp (fun ξ : ℝ => m ξ * 𝓕 u ξ) 2 volume :=
    MemLp.of_le_mul (c := B) hF2 (hme.mul hFm) (hmb.mono fun ξ hξ => by
      show ‖m ξ * 𝓕 u ξ‖ ≤ B * ‖𝓕 u ξ‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hξ (norm_nonneg _))
  have h1 : MemLp (fun ξ : ℝ => m ξ * 𝓕 u ξ) 1 volume :=
    memLp_one_iff_integrable.mpr
      ((hmi.bdd_mul hFm hFb).congr (Filter.Eventually.of_forall fun ξ => mul_comm _ _))
  exact ⟨h1, h2⟩

/-- `multForm m u` is `L²` whenever `m` is integrable and a.e. bounded and `u ∈ L¹ ∩ L²`. -/
lemma memLp_multForm {m u : ℝ → ℂ} {B : ℝ} (hmi : Integrable m volume)
    (hme : AEStronglyMeasurable m volume) (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B)
    (hu1 : MemLp u 1 volume) (hu2 : MemLp u 2 volume) : MemLp (multForm m u) 2 volume := by
  obtain ⟨h1, h2⟩ := memLp_bdd_mul_fourier hmi hme hmb hu1 hu2
  rw [multForm]
  exact memLp_fourierInv_of_memLp_one_two h1 h2

/-- The `L²` inverse Fourier transform of an `L¹ ∩ L²` class is the class of the inverse Fourier
integral. -/
lemma fourierInv_toLp_eq {θ : ℝ → ℂ} (h1 : MemLp θ 1 volume) (h2 : MemLp θ 2 volume) :
    𝓕⁻ (MemLp.toLp θ h2) = MemLp.toLp (𝓕⁻ θ) (memLp_fourierInv_of_memLp_one_two h1 h2) := by
  have h := congrArg 𝓕⁻ (fourier_toLp_fourierInv h1 h2)
  rw [FourierPair.fourierInv_fourier_eq] at h
  exact h.symm

/-- The inverse Fourier transform only depends on the a.e. class of its argument. -/
lemma fourierInv_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) : 𝓕⁻ f = 𝓕⁻ g := by
  funext x
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  refine integral_congr_ae (h.mono fun ξ hξ => ?_)
  simp only [Pi.smul_apply, hξ]

/-- **The `L²`-multiplier operator on the Fourier side**: for an integrable, a.e. bounded symbol `m`
and `u ∈ L¹ ∩ L²`, the `L²`-operator with symbol `m`, applied to the `L²`-class of `𝓕 u`, is a.e. the
multiplier form `multForm m u = 𝓕⁻ (m · 𝓕 u)`. -/
lemma lpMulBdd_fourier_toLp_ae {m u : ℝ → ℂ} {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (hmi : Integrable m volume)
    (hu1 : MemLp u 1 volume) (hu2 : MemLp u 2 volume) :
    (fun x : ℝ => (lpMulBdd m hme hmb (𝓕 (MemLp.toLp u hu2)) : ℝ → ℂ) x)
      =ᵐ[volume] multForm m u := by
  have hcoe : (↑↑((𝓕 (MemLp.toLp u hu2) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[volume] (fun ξ => 𝓕 u ξ) :=
    Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp hu1 hu2
  have hae : (fun ξ : ℝ =>
        m ξ * (↑↑((𝓕 (MemLp.toLp u hu2) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ) =ᵐ[volume]
      (fun ξ : ℝ => m ξ * 𝓕 u ξ) :=
    hcoe.mono fun ξ hξ => by
      show m ξ * (↑↑((𝓕 (MemLp.toLp u hu2) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ
        = m ξ * 𝓕 u ξ
      rw [hξ]
  obtain ⟨hm1, hm2⟩ := memLp_bdd_mul_fourier hmi hme hmb hu1 hu2
  have hZ1 : MemLp (fun ξ : ℝ =>
      m ξ * (↑↑((𝓕 (MemLp.toLp u hu2) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ) 1 volume :=
    MemLp.ae_eq hae.symm hm1
  have hZ2 : MemLp (fun ξ : ℝ =>
      m ξ * (↑↑((𝓕 (MemLp.toLp u hu2) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ) 2 volume :=
    MemLp.ae_eq hae.symm hm2
  have hEqLp : MemLp.toLp (fun ξ : ℝ =>
        m ξ * (↑↑((𝓕 (MemLp.toLp u hu2) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ)
        (memLp_mul_lpBdd hme hmb (𝓕 (MemLp.toLp u hu2)))
      = MemLp.toLp (fun ξ : ℝ =>
        m ξ * (↑↑((𝓕 (MemLp.toLp u hu2) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ) hZ2 :=
    MemLp.toLp_congr _ _ Filter.EventuallyEq.rfl
  have hmain : (fun x : ℝ => (lpMulBdd m hme hmb (𝓕 (MemLp.toLp u hu2)) : ℝ → ℂ) x)
      =ᵐ[volume] 𝓕⁻ (fun ξ : ℝ =>
        m ξ * (↑↑((𝓕 (MemLp.toLp u hu2) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ) := by
    rw [lpMulBdd, hEqLp]
    exact (Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hZ1 hZ2).trans
      (Filter.Eventually.of_forall fun x => rfl)
  refine hmain.trans ?_
  refine (Filter.EventuallyEq.of_eq (fourierInv_congr_ae hae)).trans ?_
  filter_upwards with x
  rw [multForm]

/-- The a.e. class of the `L²`-operator with symbol `m` applied to the class of an `L¹ ∩ L²`
function `θ`. -/
lemma lpMulBdd_toLp_ae {m θ : ℝ → ℂ} {B : ℝ} (hme : AEStronglyMeasurable m volume)
    (hmb : ∀ᵐ x ∂volume, ‖m x‖ ≤ B) (hmi : Integrable m volume)
    (hθ1 : MemLp θ 1 volume) (hθ2 : MemLp θ 2 volume) :
    (fun x : ℝ => (lpMulBdd m hme hmb (MemLp.toLp θ hθ2) : ℝ → ℂ) x)
      =ᵐ[volume] 𝓕⁻ (fun ξ : ℝ => m ξ * θ ξ) := by
  have hZ : (↑↑(MemLp.toLp θ hθ2) : ℝ → ℂ) =ᵐ[volume] θ := MemLp.coeFn_toLp hθ2
  have hae : (fun ξ : ℝ => m ξ * (↑↑(MemLp.toLp θ hθ2) : ℝ → ℂ) ξ) =ᵐ[volume]
      (fun ξ : ℝ => m ξ * θ ξ) := hZ.mono fun ξ hξ => by
        show m ξ * (↑↑(MemLp.toLp θ hθ2) : ℝ → ℂ) ξ = m ξ * θ ξ
        rw [hξ]
  obtain ⟨hm1, hm2⟩ := memLp_bdd_mul_one_two hme hmb hθ1 hθ2
  have hZ1 : MemLp (fun ξ : ℝ => m ξ * (↑↑(MemLp.toLp θ hθ2) : ℝ → ℂ) ξ) 1 volume :=
    MemLp.ae_eq hae.symm hm1
  have hZ2 : MemLp (fun ξ : ℝ => m ξ * (↑↑(MemLp.toLp θ hθ2) : ℝ → ℂ) ξ) 2 volume :=
    MemLp.ae_eq hae.symm hm2
  have hEqLp : MemLp.toLp (fun ξ : ℝ => m ξ * (↑↑(MemLp.toLp θ hθ2) : ℝ → ℂ) ξ)
        (memLp_mul_lpBdd hme hmb (MemLp.toLp θ hθ2))
      = MemLp.toLp (fun ξ : ℝ => m ξ * (↑↑(MemLp.toLp θ hθ2) : ℝ → ℂ) ξ) hZ2 :=
    MemLp.toLp_congr _ _ Filter.EventuallyEq.rfl
  have hmain : (fun x : ℝ => (lpMulBdd m hme hmb (MemLp.toLp θ hθ2) : ℝ → ℂ) x)
      =ᵐ[volume] 𝓕⁻ (fun ξ : ℝ => m ξ * (↑↑(MemLp.toLp θ hθ2) : ℝ → ℂ) ξ) := by
    rw [lpMulBdd, hEqLp]
    exact (Commons.Analysis.Fourier.fourierInv_toLp_ae_eq_fourierInv hZ1 hZ2).trans
      (Filter.Eventually.of_forall fun x => rfl)
  exact hmain.trans (Filter.EventuallyEq.of_eq (fourierInv_congr_ae hae))

/-- **The core of the multiplicativity argument.**  If the symbols `m₁`, `m₂` (integrable, a.e.
bounded and measurable) satisfy the `L^q`-bound on integrable inputs (`q ≥ 0`), then the product
symbol does on inputs that are also `L²`. -/
lemma multForm_mul_l2 {q : ℝ} (hq : 0 ≤ q) {m₁ m₂ : ℝ → ℂ} {A₁ A₂ B₁ B₂ : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hm₁i : Integrable m₁ volume) (hm₂i : Integrable m₂ volume)
    (hm₁m : AEStronglyMeasurable m₁ volume) (hm₂m : AEStronglyMeasurable m₂ volume)
    (hm₁b : ∀ᵐ x ∂volume, ‖m₁ x‖ ≤ B₁) (hm₂b : ∀ᵐ x ∂volume, ‖m₂ x‖ ≤ B₂)
    (H₁ : ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖multForm m₁ g x‖ₑ ^ q ≤ ENNReal.ofReal (A₁ ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q)
    (H₂ : ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖multForm m₂ g x‖ₑ ^ q ≤ ENNReal.ofReal (A₂ ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q)
    {g : ℝ → ℂ} (hg₁ : Integrable g) (hg₂ : MemLp g 2 volume) :
    ∫⁻ x : ℝ, ‖multForm (fun ξ => m₁ ξ * m₂ ξ) g x‖ₑ ^ q
      ≤ ENNReal.ofReal ((A₁ * A₂) ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
  have hB₂ : 0 ≤ B₂ := by
    obtain ⟨x, hx⟩ := (hm₂b.mono fun x hx => le_trans (norm_nonneg _) hx :
      ∀ᵐ x ∂volume, (0 : ℝ) ≤ B₂).exists
    exact hx
  have hg1 : MemLp g 1 volume := memLp_one_iff_integrable.mpr hg₁
  have hmul_int : Integrable (fun ξ : ℝ => m₁ ξ * m₂ ξ) volume :=
    (hm₁i.bdd_mul hm₂m hm₂b).congr (Filter.Eventually.of_forall fun ξ => mul_comm _ _)
  have hmul_m : AEStronglyMeasurable (fun ξ : ℝ => m₁ ξ * m₂ ξ) volume := hm₁m.mul hm₂m
  have hmul_b : ∀ᵐ x ∂volume, ‖m₁ x * m₂ x‖ ≤ B₁ * B₂ := by
    filter_upwards [hm₁b, hm₂b] with x h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  let θ : ℝ → ℂ := fun ξ => m₁ ξ * 𝓕 g ξ
  have hθ1 : MemLp θ 1 volume := (memLp_bdd_mul_fourier hm₁i hm₁m hm₁b hg1 hg₂).1
  have hθ2 : MemLp θ 2 volume := (memLp_bdd_mul_fourier hm₁i hm₁m hm₁b hg1 hg₂).2
  let h : ℝ → ℂ := 𝓕⁻ θ
  have hh2 : MemLp h 2 volume := memLp_fourierInv_of_memLp_one_two hθ1 hθ2
  have hhbdd : ∀ x : ℝ, ‖h x‖ ≤ ∫ y : ℝ, ‖θ y‖ := fun x => norm_fourierInv_le θ x
  have hh_meas : AEStronglyMeasurable h volume := by
    have hcont : Continuous h :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        Commons.Analysis.Fourier.continuous_neg_innerₗ (memLp_one_iff_integrable.mp hθ1)
    exact hcont.aestronglyMeasurable
  have hH₁ : ∫⁻ x : ℝ, ‖h x‖ₑ ^ q ≤ ENNReal.ofReal (A₁ ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q :=
    H₁ g hg₁
  have hφ2 : ∀ k : ℕ, MemLp (truncLp h k) 2 volume := fun k => truncLp_memLp hh2 k
  have hφint : ∀ k : ℕ, Integrable (truncLp h k) volume :=
    fun k => integrable_truncLp hh_meas hhbdd k
  have hφq : ∀ k : ℕ, ∫⁻ x : ℝ, ‖truncLp h k x‖ₑ ^ q ≤ ∫⁻ x : ℝ, ‖h x‖ₑ ^ q := by
    intro k
    refine lintegral_mono fun x => ?_
    refine ENNReal.rpow_le_rpow ?_ hq
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_truncLp_le h k x)
  have hH₂ : ∀ k : ℕ, ∫⁻ x : ℝ, ‖multForm m₂ (truncLp h k) x‖ₑ ^ q
      ≤ ENNReal.ofReal (A₂ ^ q) * ∫⁻ x : ℝ, ‖h x‖ₑ ^ q := by
    intro k
    exact (H₂ (truncLp h k) (hφint k)).trans (mul_le_mul' le_rfl (hφq k))
  have hφLp : Tendsto (fun k : ℕ => MemLp.toLp (truncLp h k) (hφ2 k)) atTop
      (𝓝 (MemLp.toLp h hh2)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun k => truncLp h k) hφ2 h hh2).mpr
      (tendsto_eLpNorm_truncLp_sub hh2)
  have hF : Tendsto (fun k : ℕ => 𝓕 (MemLp.toLp (truncLp h k) (hφ2 k))) atTop
      (𝓝 (MemLp.toLp θ hθ2)) := by
    have h1 : Tendsto (fun k : ℕ => 𝓕 (MemLp.toLp (truncLp h k) (hφ2 k))) atTop
        (𝓝 (𝓕 (MemLp.toLp h hh2))) :=
      (((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.tendsto _).comp hφLp)
    rwa [fourier_toLp_fourierInv hθ1 hθ2] at h1
  have hMconv : Tendsto
      (fun k : ℕ => lpMulBdd m₂ hm₂m hm₂b (𝓕 (MemLp.toLp (truncLp h k) (hφ2 k))))
      atTop (𝓝 (lpMulBdd m₂ hm₂m hm₂b (MemLp.toLp θ hθ2))) :=
    tendsto_lpMulBdd hm₂m hm₂b hB₂ hF
  have hTI : TendstoInMeasure volume (fun k x => multForm m₂ (truncLp h k) x) atTop
      (fun x => multForm (fun ξ => m₁ ξ * m₂ ξ) g x) := by
    refine TendstoInMeasure.congr (fun k => ?_) ?_ (tendstoInMeasure_of_tendsto_Lp hMconv)
    · exact lpMulBdd_fourier_toLp_ae hm₂m hm₂b hm₂i (memLp_one_iff_integrable.mpr (hφint k)) (hφ2 k)
    · refine (lpMulBdd_toLp_ae hm₂m hm₂b hm₂i hθ1 hθ2).trans ?_
      refine (Filter.EventuallyEq.of_eq (fourierInv_congr_ae (f := fun ξ => m₂ ξ * θ ξ)
        (g := fun ξ => m₁ ξ * m₂ ξ * 𝓕 g ξ) ?_)).trans ?_
      · filter_upwards with ξ
        show m₂ ξ * θ ξ = m₁ ξ * m₂ ξ * 𝓕 g ξ
        rw [show θ ξ = m₁ ξ * 𝓕 g ξ from rfl]
        ring
      · exact Filter.Eventually.of_forall fun x => rfl
  obtain ⟨ns, hns, hae⟩ := hTI.exists_seq_tendsto_ae
  have hpt : (fun x : ℝ => ‖multForm (fun ξ => m₁ ξ * m₂ ξ) g x‖ₑ ^ q)
      =ᵐ[volume] fun x : ℝ => liminf
        (fun i : ℕ => ‖multForm m₂ (truncLp h (ns i)) x‖ₑ ^ q) atTop := by
    filter_upwards [hae] with x hx
    exact (((ENNReal.continuous_rpow_const (y := q)).tendsto (‖multForm
      (fun ξ => m₁ ξ * m₂ ξ) g x‖ₑ)).comp ((continuous_enorm.tendsto _).comp hx)).liminf_eq.symm
  calc ∫⁻ x : ℝ, ‖multForm (fun ξ => m₁ ξ * m₂ ξ) g x‖ₑ ^ q
      = ∫⁻ x : ℝ, liminf (fun i : ℕ => ‖multForm m₂ (truncLp h (ns i)) x‖ₑ ^ q) atTop :=
        lintegral_congr_ae hpt
    _ ≤ liminf (fun i : ℕ => ∫⁻ x : ℝ, ‖multForm m₂ (truncLp h (ns i)) x‖ₑ ^ q) atTop :=
        lintegral_liminf_le' fun i => (((memLp_multForm hm₂i hm₂m hm₂b
          (memLp_one_iff_integrable.mpr (hφint (ns i))) (hφ2 (ns i))).aestronglyMeasurable
            ).aemeasurable).enorm.pow_const q
    _ ≤ ENNReal.ofReal (A₂ ^ q) * ∫⁻ x : ℝ, ‖h x‖ₑ ^ q := by
        refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall fun _ => by simp⟩ ?_
        intro b hb
        obtain ⟨i, hi⟩ := hb.exists
        exact hi.trans (hH₂ (ns i))
    _ ≤ ENNReal.ofReal (A₂ ^ q) * (ENNReal.ofReal (A₁ ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q) :=
        mul_le_mul' le_rfl hH₁
    _ = ENNReal.ofReal ((A₁ * A₂) ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
        rw [Real.mul_rpow hA₁ hA₂, ENNReal.ofReal_mul (Real.rpow_nonneg hA₁ q), ← mul_assoc,
          mul_comm (ENNReal.ofReal (A₂ ^ q)) (ENNReal.ofReal (A₁ ^ q)), mul_assoc]


/-! ## 5. From `L¹ ∩ L²` inputs to all integrable inputs -/

/-- Bounded integrable functions are `L²`. -/
lemma memLp_two_of_integrable_of_bound {f : ℝ → ℂ} {C : ℝ} (hf : Integrable f volume)
    (hb : ∀ x : ℝ, ‖f x‖ ≤ C) : MemLp f 2 volume := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  refine (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mpr ?_
  have hb' : ∀ x : ℝ, ‖f x‖ₑ ≤ ENNReal.ofReal C := fun x => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hb x)
  have hpt : ∀ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal C * ‖f x‖ₑ ^ (1 : ℝ) := by
    intro x
    rw [ENNReal.rpow_one]
    by_cases h0 : ‖f x‖ₑ = 0
    · rw [h0, ENNReal.zero_rpow_of_pos (by norm_num)]
      simp
    · rw [ENNReal.rpow_two, pow_two]
      exact mul_le_mul_left (hb' x) _
  have h1 : (∫⁻ x : ℝ, ‖f x‖ₑ ^ (1 : ℝ)) < ⊤ := by
    rw [lintegral_congr fun x => ENNReal.rpow_one (‖f x‖ₑ),
      ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
  refine (lintegral_mono hpt).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1

/-- One-sided value truncation: `min 1 (n / ‖g x‖) • g x`; it is bounded by `n` and by `‖g x‖`,
agrees with `g` where `‖g x‖ ≤ n`, and converges to `g` pointwise. -/
noncomputable def truncBdd (g : ℝ → ℂ) (n : ℕ) : ℝ → ℂ :=
  fun x => ((min 1 ((n : ℝ) / ‖g x‖) : ℝ) : ℂ) * g x

lemma norm_truncBdd_le (g : ℝ → ℂ) (n : ℕ) (x : ℝ) : ‖truncBdd g n x‖ ≤ ‖g x‖ := by
  have hc0 : 0 ≤ min 1 ((n : ℝ) / ‖g x‖) := le_min (by norm_num) (by positivity)
  calc ‖truncBdd g n x‖ = min 1 ((n : ℝ) / ‖g x‖) * ‖g x‖ := by
        rw [truncBdd, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
    _ ≤ 1 * ‖g x‖ := mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
    _ = ‖g x‖ := one_mul _

lemma norm_truncBdd_le' (g : ℝ → ℂ) (n : ℕ) (x : ℝ) : ‖truncBdd g n x‖ ≤ (n : ℝ) := by
  by_cases hpos : (0 : ℝ) < ‖g x‖
  · have hc0 : 0 ≤ min 1 ((n : ℝ) / ‖g x‖) := le_min (by norm_num) (by positivity)
    calc ‖truncBdd g n x‖ = min 1 ((n : ℝ) / ‖g x‖) * ‖g x‖ := by
          rw [truncBdd, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
      _ ≤ ((n : ℝ) / ‖g x‖) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ = (n : ℝ) := div_mul_cancel₀ _ hpos.ne'
  · have h0 : ‖g x‖ = 0 := le_antisymm (not_lt.mp hpos) (norm_nonneg _)
    have hg0 : g x = 0 := norm_eq_zero.mp h0
    rw [truncBdd, hg0, mul_zero, norm_zero]
    exact Nat.cast_nonneg n

lemma aestronglyMeasurable_truncBdd {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) (n : ℕ) :
    AEStronglyMeasurable (truncBdd g n) volume := by
  have h1 : Measurable (fun t : ℝ => ((min 1 ((n : ℝ) / t) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_const.min (measurable_const.div measurable_id))
  exact ((h1.comp_aemeasurable hg.aemeasurable.norm).aestronglyMeasurable).mul hg

lemma tendsto_truncBdd (g : ℝ → ℂ) (x : ℝ) :
    Tendsto (fun n : ℕ => truncBdd g n x) atTop (𝓝 (g x)) := by
  have hev : ∀ᶠ n : ℕ in atTop, truncBdd g n x = g x := by
    filter_upwards [eventually_ge_atTop ⌈‖g x‖⌉₊] with n hn
    have hn' : ‖g x‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil ‖g x‖) (by exact_mod_cast hn)
    by_cases hpos : (0 : ℝ) < ‖g x‖
    · have h1 : 1 ≤ (n : ℝ) / ‖g x‖ := (le_div_iff₀ hpos).mpr (by linarith)
      rw [truncBdd, min_eq_left h1, Complex.ofReal_one, one_mul]
    · have h0 : ‖g x‖ = 0 := le_antisymm (not_lt.mp hpos) (norm_nonneg _)
      have hg0 : g x = 0 := norm_eq_zero.mp h0
      rw [truncBdd, hg0, norm_zero, div_zero, min_eq_right (by norm_num), Complex.ofReal_zero,
        zero_mul]
  exact Tendsto.congr' (hev.mono fun n hn => hn.symm) tendsto_const_nhds

/-- The multiplier form of an integrable, a.e. strongly measurable symbol applied to an `L¹`
function is a.e. strongly measurable. -/
lemma aestronglyMeasurable_multForm {m u : ℝ → ℂ} (hmi : Integrable m volume)
    (hm : AEStronglyMeasurable m volume) (hu1 : MemLp u 1 volume) :
    AEStronglyMeasurable (multForm m u) volume := by
  have hFu : AEStronglyMeasurable (𝓕 u) volume :=
    (Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier hu1).aestronglyMeasurable
  have hFb : ∀ᵐ x ∂volume, ‖𝓕 u x‖ ≤ ∫ y : ℝ, ‖u y‖ :=
    Filter.Eventually.of_forall fun x => Commons.Analysis.CalderonZygmund.norm_fourier_le u x
  have hInt : Integrable (fun ξ : ℝ => m ξ * 𝓕 u ξ) volume :=
    (hmi.bdd_mul hFu hFb).congr (Filter.Eventually.of_forall fun ξ => mul_comm _ _)
  have hcont : Continuous (𝓕⁻ (fun ξ : ℝ => m ξ * 𝓕 u ξ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      Commons.Analysis.Fourier.continuous_neg_innerₗ hInt
  rw [multForm]
  exact hcont.aestronglyMeasurable

/-- **The `L^q`-bound for a multiplier form, known on `L¹ ∩ L²` inputs, extends to all integrable
inputs** (`q ≥ 0`). -/
lemma multForm_bound_of_l2 {q : ℝ} (hq : 0 ≤ q) {m : ℝ → ℂ} {A : ℝ}
    (hA : 0 ≤ A) (hm : AEStronglyMeasurable m volume) (hmi : Integrable m volume)
    (hcore : ∀ g : ℝ → ℂ, Integrable g → MemLp g 2 volume →
      ∫⁻ x : ℝ, ‖multForm m g x‖ₑ ^ q ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q) :
    ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖multForm m g x‖ₑ ^ q ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
  intro g hg
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (truncBdd g n) volume :=
    fun n => aestronglyMeasurable_truncBdd hg.aestronglyMeasurable n
  have hint : ∀ n : ℕ, Integrable (truncBdd g n) volume := fun n =>
    Integrable.mono' hg.norm (hmeas n) (Filter.Eventually.of_forall fun x => norm_truncBdd_le g n x)
  have hL2 : ∀ n : ℕ, MemLp (truncBdd g n) 2 volume := fun n =>
    memLp_two_of_integrable_of_bound (hint n) (norm_truncBdd_le' g n)
  have hqbound : ∀ n : ℕ, ∫⁻ x : ℝ, ‖truncBdd g n x‖ₑ ^ q ≤ ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
    intro n
    refine lintegral_mono fun x => ?_
    refine ENNReal.rpow_le_rpow ?_ hq
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_truncBdd_le g n x)
  have hbound : ∀ n : ℕ, ∫⁻ x : ℝ, ‖multForm m (truncBdd g n) x‖ₑ ^ q
      ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := fun n =>
    (hcore (truncBdd g n) (hint n) (hL2 n)).trans (mul_le_mul' le_rfl (hqbound n))
  -- pointwise convergence of the Fourier transforms
  have h𝓕 : ∀ ξ : ℝ, Tendsto (fun n : ℕ => 𝓕 (truncBdd g n) ξ) atTop (𝓝 (𝓕 g ξ)) := by
    intro ξ
    rw [show (fun n : ℕ => 𝓕 (truncBdd g n) ξ) = fun n : ℕ => ∫ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • truncBdd g n v from
        funext fun n => Real.fourier_eq' _ _]
    rw [Real.fourier_eq']
    refine tendsto_integral_of_dominated_convergence (fun y : ℝ => ‖g y‖) (fun n => ?_) hg.norm
      (fun n => ?_) ?_
    · have hphase : Continuous (fun v : ℝ =>
          Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I)) :=
        Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul
          (continuous_id.inner continuous_const))).mul continuous_const)
      exact (hphase.measurable.aestronglyMeasurable).mul (hmeas n)
    · filter_upwards with y
      have h1 : ‖Complex.exp (↑(-2 * Real.pi * inner ℝ y ξ) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [smul_eq_mul, norm_mul, h1, one_mul]
      exact norm_truncBdd_le g n y
    · filter_upwards with y
      exact (tendsto_truncBdd g y).const_smul _
  have hinner : ∀ ξ : ℝ, Tendsto (fun n : ℕ => m ξ * 𝓕 (truncBdd g n) ξ) atTop
      (𝓝 (m ξ * 𝓕 g ξ)) := fun ξ => (h𝓕 ξ).const_mul _
  -- pointwise convergence of the multiplier forms
  have hconv : ∀ x : ℝ, Tendsto (fun n : ℕ => multForm m (truncBdd g n) x) atTop
      (𝓝 (multForm m g x)) := by
    intro x
    have hfun : (fun n : ℕ => multForm m (truncBdd g n) x) = fun n : ℕ => ∫ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • (m ξ * 𝓕 (truncBdd g n) ξ) := by
      funext n
      rw [multForm, Real.fourierInv_eq']
    have hlim : multForm m g x = ∫ ξ : ℝ,
        Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) • (m ξ * 𝓕 g ξ) := by
      rw [multForm, Real.fourierInv_eq']
    rw [hfun, hlim]
    refine tendsto_integral_of_dominated_convergence (fun ξ : ℝ => ‖m ξ‖ * ∫ y : ℝ, ‖g y‖)
      (fun n => ?_) ((hmi.norm).mul_const _) (fun n => ?_) ?_
    · have hphase : Continuous (fun ξ : ℝ =>
          Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I)) :=
        Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul
          (continuous_id.inner continuous_const))).mul continuous_const)
      exact (hphase.measurable.aestronglyMeasurable).mul
        (hm.mul ((Commons.Analysis.Fourier.BoundaryLayer.measurable_fourier
          (memLp_one_iff_integrable.mpr (hint n))).aestronglyMeasurable))
    · filter_upwards with ξ
      have h1 : ‖Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I)‖ = 1 := by
        rw [Complex.norm_exp]
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [smul_eq_mul, norm_mul, h1, one_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (Commons.Analysis.CalderonZygmund.norm_fourier_le _ ξ).trans
        (integral_mono_ae (hint n).norm hg.norm
          (Filter.Eventually.of_forall fun y => norm_truncBdd_le g n y))
    · filter_upwards with ξ
      exact (hinner ξ).const_smul _
  -- the Fatou inequality for the lower integral
  have hpt : (fun x : ℝ => ‖multForm m g x‖ₑ ^ q)
      =ᵐ[volume] fun x : ℝ => liminf (fun n : ℕ => ‖multForm m (truncBdd g n) x‖ₑ ^ q) atTop := by
    filter_upwards [Filter.Eventually.of_forall hconv] with x hx
    exact (((ENNReal.continuous_rpow_const (y := q)).tendsto (‖multForm m g x‖ₑ)).comp
      ((continuous_enorm.tendsto _).comp hx)).liminf_eq.symm
  calc ∫⁻ x : ℝ, ‖multForm m g x‖ₑ ^ q
      = ∫⁻ x : ℝ, liminf (fun n : ℕ => ‖multForm m (truncBdd g n) x‖ₑ ^ q) atTop :=
        lintegral_congr_ae hpt
    _ ≤ liminf (fun n : ℕ => ∫⁻ x : ℝ, ‖multForm m (truncBdd g n) x‖ₑ ^ q) atTop :=
        lintegral_liminf_le' fun n =>
          (((aestronglyMeasurable_multForm hmi hm (memLp_one_iff_integrable.mpr (hint n))
            ).aemeasurable).enorm.pow_const q)
    _ ≤ ENNReal.ofReal (A ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
        refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall fun _ => by simp⟩ ?_
        intro b hb
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hbound n)


/-! ## 6. The abstract multiplicativity theorem -/

/-- **Products of multiplier symbols**: if `m₁`, `m₂` are (a.e. bounded, measurable) symbols whose
multiplier forms satisfy the `L^q`-bound with constants `A₁`, `A₂` on integrable inputs, then the
pointwise product satisfies it with constant `A₁ · A₂`. -/
theorem multForm_mul_bound {q : ℝ} (hq : 0 ≤ q) {m₁ m₂ : ℝ → ℂ} {A₁ A₂ B₁ B₂ : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hm₁i : Integrable m₁ volume) (hm₂i : Integrable m₂ volume)
    (hm₁m : AEStronglyMeasurable m₁ volume) (hm₂m : AEStronglyMeasurable m₂ volume)
    (hm₁b : ∀ᵐ x ∂volume, ‖m₁ x‖ ≤ B₁) (hm₂b : ∀ᵐ x ∂volume, ‖m₂ x‖ ≤ B₂)
    (H₁ : ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖multForm m₁ g x‖ₑ ^ q ≤ ENNReal.ofReal (A₁ ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q)
    (H₂ : ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖multForm m₂ g x‖ₑ ^ q ≤ ENNReal.ofReal (A₂ ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q) :
    ∀ g : ℝ → ℂ, Integrable g →
      ∫⁻ x : ℝ, ‖multForm (fun ξ => m₁ ξ * m₂ ξ) g x‖ₑ ^ q
        ≤ ENNReal.ofReal ((A₁ * A₂) ^ q) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ q := by
  intro g hg
  have hcore : ∀ u : ℝ → ℂ, Integrable u → MemLp u 2 volume →
      ∫⁻ x : ℝ, ‖multForm (fun ξ => m₁ ξ * m₂ ξ) u x‖ₑ ^ q
        ≤ ENNReal.ofReal ((A₁ * A₂) ^ q) * ∫⁻ x : ℝ, ‖u x‖ₑ ^ q :=
    fun u hu₁ hu₂ => multForm_mul_l2 hq hA₁ hA₂ hm₁i hm₂i hm₁m hm₂m hm₁b hm₂b H₁ H₂ hu₁ hu₂
  have hmul : Integrable (fun ξ : ℝ => m₁ ξ * m₂ ξ) volume :=
    (hm₁i.bdd_mul hm₂m hm₂b).congr
      (Filter.Eventually.of_forall fun ξ => mul_comm (m₂ ξ) (m₁ ξ))
  exact multForm_bound_of_l2 hq (mul_nonneg hA₁ hA₂) (hm₁m.mul hm₂m) hmul hcore g hg

/-! ## 7. The target statement -/

/-- **Products of `IWMult` symbols.** `IWMult r ψ A` (`Maximal/iw_superset.lean`) says that the
compactly supported lift `circleLift ψ` is an `L^{2r}(ℝ)`-multiplier with norm `≤ A`, tested on
integrable inputs.  For *measurable* symbols (here `MemLp ⊤` w.r.t. the Haar measure of the circle)
this is a genuine operator-norm bound, and multiplier norms are submultiplicative, so the pointwise
product is again an `IWMult` with the product of the constants.

The measurability hypothesis is not cosmetic: `IWMult` quantifies over *all* circle functions and
Mathlib's Bochner integral vanishes on non-integrable inputs, so a non-measurable `ψ` satisfies
`IWMult r ψ 0` vacuously; two such symbols can multiply to a visible one (e.g.
`(1 - ½·1_B)` and `(1 + 1_B)` for a Bernstein set `B`, whose product is `1`), which would make the
bare product statement false.  With `MemLp ⊤` both symbols are a.e. bounded and measurable, the
integrands are honest, and the conclusion is the genuine product of two bounded multipliers. -/
theorem iwMult_mul {r : ℕ} {ψ₁ ψ₂ : Work.BourgainPlan.IonescuWainger.Circle → ℂ} {A₁ A₂ : ℝ}
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hψ₁ : MeasureTheory.MemLp ψ₁ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (hψ₂ : MeasureTheory.MemLp ψ₂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (h₁ : Work.BourgainPlan.Maximal.IWMult r ψ₁ A₁)
    (h₂ : Work.BourgainPlan.Maximal.IWMult r ψ₂ A₂) :
    Work.BourgainPlan.Maximal.IWMult r (fun ξ => ψ₁ ξ * ψ₂ ξ) (A₁ * A₂) := by
  rw [iwMult_iff_multForm, circleLift_mul]
  intro g hg
  obtain ⟨B₁, _, hB₁⟩ := exists_ae_bound_circleLift hψ₁
  obtain ⟨B₂, _, hB₂⟩ := exists_ae_bound_circleLift hψ₂
  exact multForm_mul_bound (q := 2 * (r : ℝ)) (by positivity) hA₁ hA₂
    (Work.Thm52.integrable_circleLift hψ₁) (Work.Thm52.integrable_circleLift hψ₂)
    (aestronglyMeasurable_circleLift hψ₁) (aestronglyMeasurable_circleLift hψ₂) hB₁ hB₂
    (iwMult_iff_multForm.mp h₁) (iwMult_iff_multForm.mp h₂) g hg

end

end Work.BourgainPlan.Maximal
