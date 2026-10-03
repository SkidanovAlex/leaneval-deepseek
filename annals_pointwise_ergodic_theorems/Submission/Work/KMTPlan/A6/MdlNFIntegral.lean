/-
# Swapping the interval integral with the double `tsum` of the normal form (area A6)

This module proves `Work.KMTPlan.A6.MdlNFIntegral`, together with the elementary Fubini/Young
lemmas it rests on.  The normal form

  `mdlNF K κ κ' F G x = ∑'_p ∑'_z (κ z₁ κ' z₂) K (p₁-z₁) (p₂-z₂) F (x-p₁) G (x-p₂)`

(`Work.KMTPlan.A6.mdlNF`, `MdlDecayHighLow`) is the shape in which the composition of a bilinear
convolution operator with two linear convolutions is written, and the model operators of
Krause--Mirek--Tao §6 are its `t`-integrals against a weight `w` (`Work.KMTAreas.A7.Btwist`,
`mdlPart`).  The main lemma is the Fubini step that lets one exchange that `t`-integral with the
two series, which is what makes the model estimate of §6 computable coefficient by coefficient.

## The proof

Everything is dominated: `‖w t‖ ≤ Cw` on `(1/2, 1]`, `‖κ t i‖ ≤ a i` and `‖κ' t i‖ ≤ a' i` with
`a`, `a' ∈ ℓ¹(ℤ)`, `‖F‖ ≤ CF`, `‖G‖ ≤ CG` pointwise, and `‖K‖ ∈ ℓ¹(ℤ²)`.  Hence the family

  `mdlMajorant a a' K CF CG (p, z) = (a z₁ · a' z₂) · (‖K (p₁-z₁) (p₂-z₂)‖ · CF · CG)`

is a summable majorant of the whole fourfold family — its summability is the elementary Young
inequality for the convolution `ℓ¹ ⋆ ℓ¹ ⊆ ℓ¹` (`mdl_conv_majorant_summable`), proved by the
reindexing `(p, z) ↦ (p - z, z)` of `(ℤ²)²`, a bijection, so that the assumptions on `K` and on
`a ⊗ a'` become *independent* variables.  Two tensor manipulations are then legitimate:

* the defining iterated sum of `mdlNF` may be flattened to a single sum over `(ℤ²) × (ℤ²)`
  (`mdlNF_eq_tsum_prod`, via `Summable.tsum_prod`), and it may be multiplied by `w t` termwise
  (`tsum_mul_left`);
* the interval integral of that single sum may be exchanged with the sum
  (`mdl_intervalIntegral_tsum_swap`, proved from `integral_tsum_of_summable_integral_norm` by
  converting the interval integral into an integral against `volume.restrict (Ioc (1/2) 1)`).

Finally the constant `mdlKFG K F G x p z = K (p₁-z₁) (p₂-z₂) F (x-p₁) G (x-p₂)` is pulled out of
the `t`-integral (`intervalIntegral.integral_mul_const`) and the single sum over `(ℤ²) × (ℤ²)` is
unfolded back into the iterated sum (`Summable.tsum_prod`), which is the right-hand side.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDecayDefs

set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory

noncomputable section

/-! ## The objects of the statement -/

/-- The constant of the `(p, z)`-term of the normal form:
`K (p₁-z₁) (p₂-z₂) · F (x-p₁) · G (x-p₂)`. -/
def mdlKFG (K : ℤ → ℤ → ℂ) (F G : ℤ → ℂ) (x : ℤ) (p z : ℤ × ℤ) : ℂ :=
  K (p.1 - z.1) (p.2 - z.2) * F (x - p.1) * G (x - p.2)

/-- The `t`-integral of the coefficient `w t · κ t z₁ · κ' t z₂`: the coefficient of
`mdlKFG K F G x p z` on the right-hand side of `MdlNFIntegral`. -/
def mdlCoeff (w : ℝ → ℂ) (κ κ' : ℝ → ℤ → ℂ) (z : ℤ × ℤ) : ℂ :=
  ∫ t in (1/2 : ℝ)..1, w t * (κ t z.1 * κ' t z.2)

/-- The summable majorant of the fourfold family: `(a z₁ · a' z₂) · (‖K (p₁-z₁) (p₂-z₂)‖ · CF · CG)`. -/
def mdlMajorant (a a' : ℤ → ℝ) (K : ℤ → ℤ → ℂ) (CF CG : ℝ)
    (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℝ :=
  (a q.2.1 * a' q.2.2) * (‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG)

/-- The integrand of the `t`-integral of the normal form: `w t` times the summand of `mdlNF`. -/
def mdlNFIntegrand (w : ℝ → ℂ) (K : ℤ → ℤ → ℂ) (κ κ' : ℝ → ℤ → ℂ) (F G : ℤ → ℂ) (x : ℤ)
    (t : ℝ) (p : ℤ × ℤ) (z : ℤ × ℤ) : ℂ :=
  w t * ((κ t z.1 * κ' t z.2) * mdlKFG K F G x p z)

/-! ## The Fubini engine: interval integrals against series -/

/-- **Swapping an interval integral with a countable `tsum` under a summable majorant.**  If the
family `i ↦ f · i` is a.e. strongly measurable, and `‖f t i‖ ≤ b i` on the interval `[1/2, 1]` for
a summable `b`, then the interval integral of `∑' i, f t i` is the `tsum` of the interval
integrals.

The proof converts the interval integral into the integral against `volume.restrict (Ioc (1/2) 1)`
(`intervalIntegral.integral_of_le`), where the bound `b` holds almost everywhere
(`MeasureTheory.ae_restrict_mem`), and applies
`MeasureTheory.integral_tsum_of_summable_integral_norm`: each `f · i` is integrable by
`Integrable.mono'` against the constant `b i` (the restricted measure is finite), and
`∫ t, ‖f t i‖ ≤ (μ Set.univ) * b i` is summable because `b` is. -/
theorem mdl_intervalIntegral_tsum_swap {ι : Type*} [Countable ι]
    (f : ℝ → ι → ℂ) (b : ι → ℝ) (hb : Summable b)
    (hm : ∀ i, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => f t i) MeasureTheory.volume)
    (hbnd : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i, ‖f t i‖ ≤ b i) :
    (∫ t in (1/2 : ℝ)..1, ∑' i, f t i) = ∑' i, ∫ t in (1/2 : ℝ)..1, f t i := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (1/2 : ℝ) 1) with hμ
  have hfin : MeasureTheory.IsFiniteMeasure μ := ⟨by
    rw [hμ, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num⟩
  have hconst : ∀ c : ℝ, MeasureTheory.Integrable (fun _ : ℝ => c) μ :=
    fun c => MeasureTheory.integrable_const_iff.mpr (Or.inr hfin)
  have hbdae : ∀ᵐ t ∂μ, ∀ i, ‖f t i‖ ≤ b i := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht i
    exact hbnd t (Set.Ioc_subset_Icc_self ht) i
  have hFint : ∀ i, MeasureTheory.Integrable (fun t => f t i) μ := by
    intro i
    refine MeasureTheory.Integrable.mono' (hconst (b i)) ?_ ?_
    · exact (hm i).mono_measure (MeasureTheory.Measure.restrict_le_self)
    · filter_upwards [hbdae] with t ht
      exact ht i
  have hle : (1/2 : ℝ) ≤ 1 := by norm_num
  have hkey : ∀ g : ℝ → ℂ, (∫ t in (1/2 : ℝ)..1, g t) = ∫ t, g t ∂μ := by
    intro g
    rw [intervalIntegral.integral_of_le hle]
  simp only [hkey]
  refine (MeasureTheory.integral_tsum_of_summable_integral_norm (μ := μ) hFint ?_).symm
  have hint : ∀ i, (∫ t, ‖f t i‖ ∂μ) ≤ μ.real Set.univ * b i := by
    intro i
    have h1 : ∀ᵐ t ∂μ, ‖f t i‖ ≤ b i := hbdae.mono (fun t ht => ht i)
    calc ∫ t, ‖f t i‖ ∂μ ≤ ∫ t, b i ∂μ :=
          MeasureTheory.integral_mono_ae (hFint i).norm (hconst (b i)) h1
      _ = μ.real Set.univ * b i := by rw [MeasureTheory.integral_const]; simp
  exact Summable.of_nonneg_of_le (fun i => MeasureTheory.integral_nonneg fun t => norm_nonneg _)
    hint (hb.mul_left _)

/-! ## The elementary `ℓ¹`-Young inequality for the fourfold convolution -/

/-- **Summability of the convolution majorant.**  If `‖K‖ ∈ ℓ¹(ℤ²)` and `a`, `a' ∈ ℓ¹(ℤ)` are
nonnegative, then `mdlMajorant a a' K CF CG` is summable: it is (a multiple of) the family
`‖K‖ ⋆ (a ⊗ a')`, whose summability follows from the product structure of `ℓ¹` after the change of
variables `(p, z) ↦ (p - z, z)` of `(ℤ²)²` (a bijection, so Fubini for series applies). -/
theorem mdl_conv_majorant_summable {K : ℤ → ℤ → ℂ} {a a' : ℤ → ℝ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (ha : Summable a) (ha' : Summable a')
    (ha0 : ∀ i : ℤ, 0 ≤ a i) (ha0' : ∀ i : ℤ, 0 ≤ a' i) (CF CG : ℝ) :
    Summable (mdlMajorant a a' K CF CG) := by
  have haa : Summable fun u : ℤ × ℤ => a u.1 * a' u.2 :=
    Summable.mul_of_nonneg ha ha' ha0 ha0'
  have hjoint : Summable fun z : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K z.1.1 z.1.2‖ * (a z.2.1 * a' z.2.2) :=
    Summable.mul_of_nonneg hK haa (fun _ => norm_nonneg _)
      (fun u => mul_nonneg (ha0 _) (ha0' _))
  have hConv : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      (a q.2.1 * a' q.2.2) * ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ := by
    refine ((Equiv.summable_iff Work.A7.ModelApproxCore_aux.kernCompSubEquiv).mpr hjoint).congr
      (fun q => ?_)
    simp only [Function.comp_apply, Work.A7.ModelApproxCore_aux.kernCompSubEquiv, Equiv.coe_fn_mk,
      Prod.fst_sub, Prod.snd_sub]
    ring
  exact (hConv.mul_left (CF * CG)).congr (fun q => by rw [mdlMajorant]; ring)

/-! ## The flattening of the normal form, and the pointwise bounds -/

/-- **The normal form as a single sum over `(ℤ²) × (ℤ²)`.**  For summable `κ`, `κ'` (in `ℓ¹(ℤ)`),
bounded `F`, `G` and `‖K‖ ∈ ℓ¹(ℤ²)`, the defining iterated sum of `mdlNF` may be flattened. -/
theorem mdlNF_eq_tsum_prod {K : ℤ → ℤ → ℂ} {κ κ' F G : ℤ → ℂ} {CF CG : ℝ}
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hκ : Summable fun i : ℤ => ‖κ i‖) (hκ' : Summable fun i : ℤ => ‖κ' i‖) (x : ℤ) :
    mdlNF K κ κ' F G x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), (κ q.2.1 * κ' q.2.2) * mdlKFG K F G x q.1 q.2 := by
  have hCF : 0 ≤ CF := le_trans (norm_nonneg (F 0)) (hF 0)
  have hCG : 0 ≤ CG := le_trans (norm_nonneg (G 0)) (hG 0)
  have hκκ' : Summable fun u : ℤ × ℤ => ‖κ u.1‖ * ‖κ' u.2‖ :=
    Summable.mul_of_nonneg hκ hκ' (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hjoint : Summable fun z : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K z.1.1 z.1.2‖ * (‖κ z.2.1‖ * ‖κ' z.2.2‖) :=
    Summable.mul_of_nonneg hK hκκ' (fun _ => norm_nonneg _)
      (fun u => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hreindex : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * (‖κ q.2.1‖ * ‖κ' q.2.2‖) := by
    refine ((Equiv.summable_iff Work.A7.ModelApproxCore_aux.kernCompSubEquiv).mpr hjoint).congr
      (fun q => ?_)
    simp only [Function.comp_apply, Work.A7.ModelApproxCore_aux.kernCompSubEquiv, Equiv.coe_fn_mk,
      Prod.fst_sub, Prod.snd_sub]
  have hmaj : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      (‖κ q.2.1‖ * ‖κ' q.2.2‖) * (‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG) :=
    (hreindex.mul_left (CF * CG)).congr (fun q => by ring)
  have hS : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      (κ q.2.1 * κ' q.2.2) * mdlKFG K F G x q.1 q.2 := by
    refine Summable.of_norm_bounded hmaj (fun q => ?_)
    have h1 : ‖κ q.2.1 * κ' q.2.2‖ ≤ ‖κ q.2.1‖ * ‖κ' q.2.2‖ := le_of_eq (norm_mul _ _)
    have h2 : ‖mdlKFG K F G x q.1 q.2‖ ≤ ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG := by
      rw [mdlKFG, norm_mul, norm_mul]
      gcongr
      · exact hF _
      · exact hG _
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [mdlNF]
  exact hS.tsum_prod.symm

/-- **The pointwise bound on a single summand of the flattened normal form.**  The product of the
two convolution coefficients and the constant `mdlKFG K F G x p z` is dominated by
`mdlMajorant a a' K CF CG (p, z)`, where `a`, `a'` bound the two coefficient sequences and `CF`,
`CG` bound `F`, `G`. -/
theorem mdl_summand_norm_le {K : ℤ → ℤ → ℂ} {F G : ℤ → ℂ} {CF CG : ℝ}
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    {κ κ' : ℤ → ℂ} {a a' : ℤ → ℝ} (ha0 : ∀ i : ℤ, 0 ≤ a i) (ha0' : ∀ i : ℤ, 0 ≤ a' i)
    (hκ : ∀ i : ℤ, ‖κ i‖ ≤ a i) (hκ' : ∀ i : ℤ, ‖κ' i‖ ≤ a' i) (x : ℤ) (p z : ℤ × ℤ) :
    ‖(κ z.1 * κ' z.2) * mdlKFG K F G x p z‖ ≤ mdlMajorant a a' K CF CG (p, z) := by
  have hCF : 0 ≤ CF := le_trans (norm_nonneg (F 0)) (hF 0)
  have hCG : 0 ≤ CG := le_trans (norm_nonneg (G 0)) (hG 0)
  have h1 : ‖κ z.1 * κ' z.2‖ ≤ a z.1 * a' z.2 := by
    rw [norm_mul]
    exact mul_le_mul (hκ z.1) (hκ' z.2) (norm_nonneg _) (ha0 z.1)
  have h2 : ‖mdlKFG K F G x p z‖ ≤ ‖K (p.1 - z.1) (p.2 - z.2)‖ * CF * CG := by
    rw [mdlKFG, norm_mul, norm_mul]
    gcongr
    · exact hF _
    · exact hG _
  rw [mdlMajorant, norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (ha0 _) (ha0' _))

/-- **The size of the `t`-integral of a coefficient.**  On `(1/2, 1]` the integrand
`w t · κ t z₁ · κ' t z₂` is bounded by the constant `Cw · a z₁ · a' z₂`, so its interval integral
is bounded by the same constant (`norm_integral_le_of_norm_le_const` and `|1 - 1/2| = 1/2 ≤ 1`). -/
theorem mdl_coeff_intervalIntegral_bound {w : ℝ → ℂ} {Cw : ℝ}
    (hw : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ‖w t‖ ≤ Cw) (hCw : 0 ≤ Cw)
    {κ κ' : ℝ → ℤ → ℂ} {a a' : ℤ → ℝ} (ha0 : ∀ i : ℤ, 0 ≤ a i) (ha0' : ∀ i : ℤ, 0 ≤ a' i)
    (hκ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ, ‖κ t i‖ ≤ a i)
    (hκ' : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ, ‖κ' t i‖ ≤ a' i) (z : ℤ × ℤ) :
    ‖mdlCoeff w κ κ' z‖ ≤ Cw * (a z.1 * a' z.2) := by
  have hle : (1/2 : ℝ) ≤ 1 := by norm_num
  have hbd : ∀ t ∈ Set.uIoc (1/2 : ℝ) 1,
      ‖w t * (κ t z.1 * κ' t z.2)‖ ≤ Cw * (a z.1 * a' z.2) := by
    intro t ht
    rw [Set.uIoc_of_le hle] at ht
    rw [norm_mul, norm_mul]
    exact mul_le_mul (hw t (Set.Ioc_subset_Icc_self ht))
      (mul_le_mul (hκ t (Set.Ioc_subset_Icc_self ht) z.1)
        (hκ' t (Set.Ioc_subset_Icc_self ht) z.2) (norm_nonneg _) (ha0 z.1))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCw
  rw [mdlCoeff]
  calc ‖∫ t in (1/2 : ℝ)..1, w t * (κ t z.1 * κ' t z.2)‖
      ≤ (Cw * (a z.1 * a' z.2)) * |1 - 1/2| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = (Cw * (a z.1 * a' z.2)) * (1/2) := by norm_num
    _ ≤ Cw * (a z.1 * a' z.2) :=
        mul_le_of_le_one_right (mul_nonneg hCw (mul_nonneg (ha0 _) (ha0' _)))
          (by norm_num)

/-! ## The main theorem -/

/-- Swapping the interval integral with the double `tsum` of the normal form `mdlNF`. -/
theorem MdlNFIntegral (K : ℤ → ℤ → ℂ) (F G : ℤ → ℂ) {CF CG : ℝ}
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (w : ℝ → ℂ) {Cw : ℝ} (hw : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ‖w t‖ ≤ Cw)
    (hwm : MeasureTheory.AEStronglyMeasurable w MeasureTheory.volume)
    (κ κ' : ℝ → ℤ → ℂ) (a a' : ℤ → ℝ) (ha : Summable a) (ha' : Summable a')
    (hκ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ, ‖κ t i‖ ≤ a i)
    (hκ' : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ, ‖κ' t i‖ ≤ a' i)
    (hmκ : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => κ t i) MeasureTheory.volume)
    (hmκ' : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable (fun t : ℝ => κ' t i) MeasureTheory.volume)
    (x : ℤ) :
    (∫ t in (1/2 : ℝ)..1, w t * Work.KMTPlan.A6.mdlNF K (κ t) (κ' t) F G x)
      = ∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ,
          (∫ t in (1/2 : ℝ)..1, w t * (κ t z.1 * κ' t z.2))
            * (K (p.1 - z.1) (p.2 - z.2) * F (x - p.1) * G (x - p.2)) := by
  have hI : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hle : (1/2 : ℝ) ≤ 1 := by norm_num
  have hCw : 0 ≤ Cw := le_trans (norm_nonneg _) (hw (1/2) hI)
  have hCF : 0 ≤ CF := le_trans (norm_nonneg (F 0)) (hF 0)
  have hCG : 0 ≤ CG := le_trans (norm_nonneg (G 0)) (hG 0)
  have ha0 : ∀ i : ℤ, 0 ≤ a i := fun i => le_trans (norm_nonneg _) (hκ (1/2) hI i)
  have ha0' : ∀ i : ℤ, 0 ≤ a' i := fun i => le_trans (norm_nonneg _) (hκ' (1/2) hI i)
  -- the summable majorant
  have hBsum : Summable (mdlMajorant a a' K CF CG) :=
    mdl_conv_majorant_summable hK ha ha' ha0 ha0' CF CG
  -- the pointwise identity on the interval
  have hpt : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      w t * Work.KMTPlan.A6.mdlNF K (κ t) (κ' t) F G x
        = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), mdlNFIntegrand w K κ κ' F G x t q.1 q.2 := by
    intro t ht
    have hκt : Summable fun i : ℤ => ‖κ t i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hκ t ht i) ha
    have hκt' : Summable fun i : ℤ => ‖κ' t i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hκ' t ht i) ha'
    rw [mdlNF_eq_tsum_prod hF hG hK hκt hκt' x, ← tsum_mul_left]
    rfl
  -- a.e. strong measurability of the integrand
  have hmeas : ∀ q : (ℤ × ℤ) × (ℤ × ℤ),
      MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => mdlNFIntegrand w K κ κ' F G x t q.1 q.2) MeasureTheory.volume := by
    intro q
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => κ t q.2.1 * κ' t q.2.2) MeasureTheory.volume :=
      (hmκ q.2.1).mul (hmκ' q.2.2)
    have h2 : MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => (κ t q.2.1 * κ' t q.2.2) * mdlKFG K F G x q.1 q.2) MeasureTheory.volume :=
      h1.mul MeasureTheory.aestronglyMeasurable_const
    show MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => w t * ((κ t q.2.1 * κ' t q.2.2) * mdlKFG K F G x q.1 q.2)) MeasureTheory.volume
    exact hwm.mul h2
  -- the majorant bound, including the factor `‖w t‖ ≤ Cw`
  have hbound : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ q : (ℤ × ℤ) × (ℤ × ℤ),
      ‖mdlNFIntegrand w K κ κ' F G x t q.1 q.2‖ ≤ Cw * mdlMajorant a a' K CF CG q := by
    intro t ht q
    have h1 : ‖w t‖ * ‖(κ t q.2.1 * κ' t q.2.2) * mdlKFG K F G x q.1 q.2‖
        ≤ Cw * mdlMajorant a a' K CF CG q :=
      mul_le_mul (hw t ht)
        (mdl_summand_norm_le hF hG ha0 ha0' (fun i => hκ t ht i) (fun i => hκ' t ht i)
          x q.1 q.2)
        (norm_nonneg _) hCw
    simpa only [mdlNFIntegrand, norm_mul] using h1
  -- the integral/`tsum` exchange
  have hM : (∫ t in (1/2 : ℝ)..1,
        ∑' q : (ℤ × ℤ) × (ℤ × ℤ), mdlNFIntegrand w K κ κ' F G x t q.1 q.2)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          ∫ t in (1/2 : ℝ)..1, mdlNFIntegrand w K κ κ' F G x t q.1 q.2 :=
    mdl_intervalIntegral_tsum_swap (fun t q => mdlNFIntegrand w K κ κ' F G x t q.1 q.2)
      (fun q => Cw * mdlMajorant a a' K CF CG q) (hBsum.mul_left Cw) hmeas hbound
  -- summability of the family obtained after pulling the constants out
  have hGsum : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      mdlCoeff w κ κ' q.2 * mdlKFG K F G x q.1 q.2 := by
    refine Summable.of_norm_bounded (hBsum.mul_left Cw) (fun q => ?_)
    have h2 : ‖mdlKFG K F G x q.1 q.2‖ ≤ ‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG := by
      rw [mdlKFG, norm_mul, norm_mul]
      gcongr
      · exact hF _
      · exact hG _
    rw [norm_mul]
    calc ‖mdlCoeff w κ κ' q.2‖ * ‖mdlKFG K F G x q.1 q.2‖
        ≤ (Cw * (a q.2.1 * a' q.2.2)) * (‖K (q.1.1 - q.2.1) (q.1.2 - q.2.2)‖ * CF * CG) :=
          mul_le_mul (mdl_coeff_intervalIntegral_bound hw hCw ha0 ha0' hκ hκ' q.2) h2
            (norm_nonneg _) (mul_nonneg hCw (mul_nonneg (ha0 _) (ha0' _)))
      _ = Cw * mdlMajorant a a' K CF CG q := by rw [mdlMajorant]; ring
  -- the `t`-integral of the integrand at a fixed pair is the coefficient times the constant
  have hterm : ∀ p z : ℤ × ℤ, (∫ t in (1/2 : ℝ)..1, mdlNFIntegrand w K κ κ' F G x t p z)
      = mdlCoeff w κ κ' z * mdlKFG K F G x p z := by
    intro p z
    rw [show (∫ t in (1/2 : ℝ)..1, mdlNFIntegrand w K κ κ' F G x t p z)
        = ∫ t in (1/2 : ℝ)..1, (fun t => w t * (κ t z.1 * κ' t z.2)) t
            * mdlKFG K F G x p z from
      intervalIntegral.integral_congr (fun t _ => by simp only [mdlNFIntegrand]; ring)]
    rw [intervalIntegral.integral_mul_const, mdlCoeff]
  -- the three rewritings of the left-hand side
  have hL : (∫ t in (1/2 : ℝ)..1, w t * Work.KMTPlan.A6.mdlNF K (κ t) (κ' t) F G x)
      = ∫ t in (1/2 : ℝ)..1,
          ∑' q : (ℤ × ℤ) × (ℤ × ℤ), mdlNFIntegrand w K κ κ' F G x t q.1 q.2 :=
    intervalIntegral.integral_congr (fun t ht => by
      rw [Set.uIcc_of_le hle] at ht
      exact hpt t ht)
  have hT : (∑' q : (ℤ × ℤ) × (ℤ × ℤ),
        ∫ t in (1/2 : ℝ)..1, mdlNFIntegrand w K κ κ' F G x t q.1 q.2)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ), mdlCoeff w κ κ' q.2 * mdlKFG K F G x q.1 q.2 :=
    tsum_congr (fun q => hterm q.1 q.2)
  show (∫ t in (1/2 : ℝ)..1, w t * Work.KMTPlan.A6.mdlNF K (κ t) (κ' t) F G x)
      = ∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ, mdlCoeff w κ κ' z * mdlKFG K F G x p z
  exact hL.trans (hM.trans (hT.trans hGsum.tsum_prod))

end

end Work.KMTPlan.A6
