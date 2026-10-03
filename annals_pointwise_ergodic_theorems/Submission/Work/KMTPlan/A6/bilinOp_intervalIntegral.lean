/-
# Interchanging the `t`-integral with a bilinear convolution (`intervalIntegral_bilinOp`)

Let `K : ℤ → ℤ → ℂ` be an `ℓ¹(ℤ²)` bilinear kernel, `f, g : ℤ → ℂ` bounded functions and
`κ, κ' : ℝ → ℤ → ℂ` two `t`-families of `ℓ¹(ℤ)` kernels, summable uniformly on `(1/2, 1]`.
Writing `convOp` for the linear convolution operator with kernel `κ` and `bilinOp` for the bilinear
convolution operator with kernel `K` (`Work.KMTAreas.A7.ModelOps`), the theorem says that the
`t`-integral of the bilinear convolution of the two *convolved* functions is the bilinear
convolution with the `t`-integral of the *composed* kernel:

  `∫_{1/2}^1 B_K(T_{κ_t} f, T_{κ'_t} g) dt = B_{∫_{1/2}^1 kernComp K κ_t κ'_t dt}(f, g)`.

This is the "interchange of the `t`-integral with the bilinear convolution" used in §6 of
Krause--Mirek--Tao (`mod-approx`): the model column `mdlPart` is the `t`-integral of a twisted
bilinear multiplier applied to two height-exact pieces, and the reduction to a single bilinear
convolution operator on the pair `(f, g)` is exactly this identity (see
`Submission/Work/KMTPlan/A6/KmodDefs.lean`, `ModApproxErrCoreExact.lean` and
`NOTES_A6_SymToolbox_ROUTE.md`).

The proof has two ingredients.

* *Functional calculus* (`Work.A7.ModelApproxCore_kernelComp`, PROVED): for each `t ∈ (1/2,1]`,
  `bilinOp K (convOp (κ t) f) (convOp (κ' t) g) = bilinOp (kernComp K (κ t) (κ' t)) f g`.  The
  identity is only available at the points where `κ t`, `κ' t` are `ℓ¹`; since these points have
  full measure in `(1/2,1]`, the two integrands agree a.e. and their interval integrals coincide.
* *Fubini for the `t`-integral against the double `tsum` over `ℤ × ℤ`
  (`bilinOp_kernel_intervalIntegral` below): for an abstract kernel family `L`, if each
  `t ↦ L t a b` is a.e. measurable and `∑'_{p : ℤ×ℤ} ∫⁻ t, ‖L t p.1 p.2‖ₑ < ∞`, then
  `bilinOp (fun a b => ∫_t L t a b) f g x = ∫_t bilinOp (L t) f g x`.
  The proof applies `MeasureTheory.integral_tsum` twice (once for each `ℤ`-sum), the finiteness
  hypotheses being derived from the single `∑'_{p : ℤ×ℤ}` finiteness by Tonelli
  (`ENNReal.tsum_prod'`) and the elementary bounds `‖f‖ ≤ C_f`, `‖g‖ ≤ C_g`.

The two concrete inputs for the kernel family `L t = kernComp K (κ t) (κ' t)` are supplied by
`Work.KMTPlan.A6.aemeasurable_kernComp` (measurability) and
`Work.KMTPlan.A6.tsum_lintegral_enorm_kernComp_ne_top` (finiteness, via the `ℓ¹` Young inequality
`tsum_norm_kernComp_le` and Tonelli).
-/
import Mathlib
import Submission.Work.A7.ModelApproxCore_kernelComp
import Submission.Work.KMTPlan.A6.aemeasurable_kernComp
import Submission.Work.KMTPlan.A6.tsum_lintegral_enorm_kernComp_ne_top

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- **Fubini for a bilinear convolution over `[1/2,1]`.**

For a `t`-family of bilinear kernels `L`, two bounded functions `f`, `g` and a point `x`, if
* every section `t ↦ L t a b` is a.e. measurable on `(1/2,1]`, and
* `∑'_{p : ℤ × ℤ} ∫⁻ t, ‖L t p.1 p.2‖ₑ ∂(volume.restrict (Ioc (1/2) 1)) ≠ ⊤`,

then the interval integral of `bilinOp (L t) f g x` equals `bilinOp` applied to the kernel obtained
by integrating `L` in `t`.  The proof is two applications of `MeasureTheory.integral_tsum`, one for
each of the two `ℤ`-sums in the definition of `bilinOp`; the finiteness hypotheses needed there are
derived from the single hypothesis by Tonelli and the bounds `‖f‖ ≤ Cf`, `‖g‖ ≤ Cg`. -/
theorem bilinOp_kernel_intervalIntegral (L : ℝ → ℤ → ℤ → ℂ) (f g : ℤ → ℂ) (Cf Cg : ℝ) (x : ℤ)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hm : ∀ a b : ℤ, AEMeasurable (fun t : ℝ => L t a b)
      (volume.restrict (Set.Ioc (1/2:ℝ) 1)))
    (hfin : (∑' p : ℤ × ℤ, ∫⁻ t, ‖L t p.1 p.2‖ₑ
      ∂(volume.restrict (Set.Ioc (1/2:ℝ) 1))) ≠ ⊤) :
    Work.KMTAreas.A7.bilinOp (fun a b => ∫ t in (1/2:ℝ)..1, L t a b) f g x
      = ∫ t in (1/2:ℝ)..1, Work.KMTAreas.A7.bilinOp (L t) f g x := by
  classical
  have h12 : (1/2 : ℝ) ≤ 1 := by norm_num
  set μ : Measure ℝ := volume.restrict (Set.Ioc (1/2:ℝ) 1) with hμ
  set H : ℝ → ℤ → ℤ → ℂ := fun t a b => L t a b * f (x - a) * g (x - b) with hH
  set Cf₀ : NNReal := ⟨Cf, hCf⟩ with hCf₀
  set Cg₀ : NNReal := ⟨Cg, hCg⟩ with hCg₀
  have hf₀ : ∀ y : ℤ, ‖f y‖ₑ ≤ (Cf₀ : ENNReal) := by
    intro y
    have h1 : ‖f y‖₊ ≤ Cf₀ := by rw [hCf₀]; exact_mod_cast hf y
    rw [enorm_eq_nnnorm]; exact ENNReal.coe_le_coe.mpr h1
  have hg₀ : ∀ y : ℤ, ‖g y‖ₑ ≤ (Cg₀ : ENNReal) := by
    intro y
    have h1 : ‖g y‖₊ ≤ Cg₀ := by rw [hCg₀]; exact_mod_cast hg y
    rw [enorm_eq_nnnorm]; exact ENNReal.coe_le_coe.mpr h1
  -- the elementary bound on the modulus of the summands
  have hHnorm : ∀ (t : ℝ) (a b : ℤ), ‖H t a b‖ₑ
      ≤ ((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) * ‖L t a b‖ₑ := by
    intro t a b
    have h1 : ‖f (x - a)‖ₑ ≤ (Cf₀ : ENNReal) := hf₀ (x - a)
    have h2 : ‖g (x - b)‖ₑ ≤ (Cg₀ : ENNReal) := hg₀ (x - b)
    have h3 : ‖H t a b‖ₑ = ‖L t a b‖ₑ * ‖f (x - a)‖ₑ * ‖g (x - b)‖ₑ := by
      simp only [H, enorm_mul, mul_assoc]
    rw [h3]
    calc ‖L t a b‖ₑ * ‖f (x - a)‖ₑ * ‖g (x - b)‖ₑ
        ≤ ‖L t a b‖ₑ * (Cf₀ : ENNReal) * (Cg₀ : ENNReal) := by
          refine mul_le_mul ?_ h2 bot_le bot_le
          exact mul_le_mul le_rfl h1 bot_le bot_le
      _ = ((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) * ‖L t a b‖ₑ := by ring
  have hCc_ne : ((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  -- measurability of the summands and of the partial sums
  have hHm : ∀ a b : ℤ, AEMeasurable (fun t : ℝ => H t a b) μ := by
    intro a b
    have := (hm a b).mul_const (f (x - a) * g (x - b))
    simpa [H, mul_assoc] using this
  have hHsm : ∀ a b : ℤ, AEStronglyMeasurable (fun t : ℝ => H t a b) μ :=
    fun a b => (hHm a b).aestronglyMeasurable
  -- the `∑'_{a,b}` form of the finiteness hypothesis
  have hfin' : (∑' a : ℤ, ∑' b : ℤ, ∫⁻ t, ‖L t a b‖ₑ ∂μ) ≠ ⊤ := by
    have h := hfin
    rw [hμ] at h
    rwa [ENNReal.tsum_prod'] at h
  -- finiteness of the inner (`b`) sums, needed for the second `integral_tsum`
  have hinner : ∀ a : ℤ, (∑' b : ℤ, ∫⁻ t, ‖H t a b‖ₑ ∂μ) ≠ ⊤ := by
    intro a
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hCc_ne hfin') ?_
    calc (∑' b : ℤ, ∫⁻ t, ‖H t a b‖ₑ ∂μ)
        ≤ ∑' b : ℤ, (((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) * ∫⁻ t, ‖L t a b‖ₑ ∂μ) := by
          refine ENNReal.tsum_le_tsum (fun b => ?_)
          calc ∫⁻ t, ‖H t a b‖ₑ ∂μ
              ≤ ∫⁻ t, (((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) * ‖L t a b‖ₑ) ∂μ :=
                lintegral_mono (fun t => hHnorm t a b)
            _ = ((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) * ∫⁻ t, ‖L t a b‖ₑ ∂μ :=
                lintegral_const_mul' _ _ hCc_ne
      _ = ((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) * (∑' b : ℤ, ∫⁻ t, ‖L t a b‖ₑ ∂μ) :=
          ENNReal.tsum_mul_left
      _ ≤ ((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) *
            (∑' a : ℤ, ∑' b : ℤ, ∫⁻ t, ‖L t a b‖ₑ ∂μ) := by
          refine mul_le_mul le_rfl ?_ bot_le bot_le
          exact ENNReal.le_tsum (f := fun a : ℤ => ∑' b : ℤ, ∫⁻ t, ‖L t a b‖ₑ ∂μ) a
  have htsum_sm : ∀ a : ℤ, AEStronglyMeasurable (fun t : ℝ => ∑' b : ℤ, H t a b) μ := by
    intro a
    exact (AEMeasurable.tsum (fun b => hHm a b)).aestronglyMeasurable
  -- finiteness of the outer (`a`) sums, needed for the first `integral_tsum`
  have houter : (∑' a : ℤ, ∫⁻ t, ‖∑' b : ℤ, H t a b‖ₑ ∂μ) ≠ ⊤ := by
    have hle : (∑' a : ℤ, ∫⁻ t, ‖∑' b : ℤ, H t a b‖ₑ ∂μ)
        ≤ ((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) *
            (∑' a : ℤ, ∑' b : ℤ, ∫⁻ t, ‖L t a b‖ₑ ∂μ) := by
      calc (∑' a : ℤ, ∫⁻ t, ‖∑' b : ℤ, H t a b‖ₑ ∂μ)
          ≤ ∑' a : ℤ, ∫⁻ t, (∑' b : ℤ, ‖H t a b‖ₑ) ∂μ := by
            refine ENNReal.tsum_le_tsum (fun a => ?_)
            exact lintegral_mono (fun t => enorm_tsum_le_tsum_enorm)
        _ = ∑' a : ℤ, ∑' b : ℤ, ∫⁻ t, ‖H t a b‖ₑ ∂μ := by
            refine tsum_congr (fun a => ?_)
            exact lintegral_tsum (fun b => (hHm a b).enorm)
        _ ≤ ∑' a : ℤ, ∑' b : ℤ,
              (((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) * ∫⁻ t, ‖L t a b‖ₑ ∂μ) := by
            refine ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b => ?_))
            calc ∫⁻ t, ‖H t a b‖ₑ ∂μ
                ≤ ∫⁻ t, (((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) * ‖L t a b‖ₑ) ∂μ :=
                  lintegral_mono (fun t => hHnorm t a b)
              _ = _ := lintegral_const_mul' _ _ hCc_ne
        _ = ((Cf₀ : ENNReal) * (Cg₀ : ENNReal)) *
              (∑' a : ℤ, ∑' b : ℤ, ∫⁻ t, ‖L t a b‖ₑ ∂μ) := by
            simp only [ENNReal.tsum_mul_left]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hCc_ne hfin') hle
  -- the two applications of `integral_tsum`
  have key : (∫ t, ∑' a : ℤ, ∑' b : ℤ, H t a b ∂μ)
      = ∑' a : ℤ, ∑' b : ℤ, ∫ t, H t a b ∂μ := by
    rw [integral_tsum (f := fun a t => ∑' b : ℤ, H t a b) (fun a => htsum_sm a) houter]
    refine tsum_congr (fun a => ?_)
    exact integral_tsum (f := fun b t => H t a b) (fun b => hHsm a b) (hinner a)
  -- the integral of the bilinear operator, as an iterated integral against `μ`
  have hLHS : Work.KMTAreas.A7.bilinOp (fun a b => ∫ t in (1/2:ℝ)..1, L t a b) f g x
      = ∑' a : ℤ, ∑' b : ℤ, ∫ t, H t a b ∂μ := by
    rw [Work.KMTAreas.A7.bilinOp]
    refine tsum_congr (fun a => tsum_congr (fun b => ?_))
    rw [intervalIntegral.integral_of_le h12]
    rw [show H = fun t a b => L t a b * f (x - a) * g (x - b) from hH]
    rw [integral_mul_const, integral_mul_const]
  have hpt : ∀ t : ℝ, (∑' a : ℤ, ∑' b : ℤ, H t a b)
      = Work.KMTAreas.A7.bilinOp (L t) f g x := by
    intro t
    rw [show H = fun t a b => L t a b * f (x - a) * g (x - b) from hH]
    simp only [Work.KMTAreas.A7.bilinOp]
  calc Work.KMTAreas.A7.bilinOp (fun a b => ∫ t in (1/2:ℝ)..1, L t a b) f g x
      = ∑' a : ℤ, ∑' b : ℤ, ∫ t, H t a b ∂μ := hLHS
    _ = ∫ t, ∑' a : ℤ, ∑' b : ℤ, H t a b ∂μ := key.symm
    _ = ∫ t, Work.KMTAreas.A7.bilinOp (L t) f g x ∂μ := by
        refine integral_congr_ae ?_
        exact Filter.Eventually.of_forall hpt
    _ = ∫ t in (1/2:ℝ)..1, Work.KMTAreas.A7.bilinOp (L t) f g x := by
        rw [intervalIntegral.integral_of_le h12]

/-- **The `t`-integral of a bilinear convolution is the bilinear convolution with the `t`-integral
of the kernel.**  See the module docstring. -/
theorem bilinOp_intervalIntegral (K : ℤ → ℤ → ℂ) (κ κ' : ℝ → ℤ → ℂ) (f g : ℤ → ℂ)
    (BK B1 B2 Cf Cg : ℝ) (x : ℤ)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hKb : (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) ≤ BK)
    (hκ : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, Summable fun j : ℤ => ‖κ t j‖)
    (hκ' : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, Summable fun j : ℤ => ‖κ' t j‖)
    (hκb : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, (∑' j : ℤ, ‖κ t j‖) ≤ B1)
    (hκb' : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, (∑' j : ℤ, ‖κ' t j‖) ≤ B2)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hBK : 0 ≤ BK) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hmκ : ∀ j : ℤ, AEMeasurable (fun t : ℝ => κ t j) volume)
    (hmκ' : ∀ j : ℤ, AEMeasurable (fun t : ℝ => κ' t j) volume) :
    (∫ t in (1 / 2 : ℝ)..1,
        Work.KMTAreas.A7.bilinOp K (Work.KMTAreas.A7.convOp (κ t) f)
          (Work.KMTAreas.A7.convOp (κ' t) g) x)
      = Work.KMTAreas.A7.bilinOp
          (fun a b => ∫ t in (1 / 2 : ℝ)..1,
            Work.KMTAreas.A7.kernComp K (κ t) (κ' t) a b) f g x := by
  have h12 : (1/2 : ℝ) ≤ 1 := by norm_num
  -- on `(1/2,1]` the integrand is the bilinear operator of the composed kernel
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1/2:ℝ) 1)),
      (fun t : ℝ => Work.KMTAreas.A7.bilinOp K (Work.KMTAreas.A7.convOp (κ t) f)
        (Work.KMTAreas.A7.convOp (κ' t) g) x) t
      = (fun t : ℝ => Work.KMTAreas.A7.bilinOp (Work.KMTAreas.A7.kernComp K (κ t) (κ' t))
          f g x) t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    exact (Work.A7.ModelApproxCore_kernelComp (K := K) (κ := κ t) (κ' := κ' t)
      (u := f) (v := g) hK (hκ t ht) (hκ' t ht) hf hg x).symm
  calc (∫ t in (1 / 2 : ℝ)..1,
        Work.KMTAreas.A7.bilinOp K (Work.KMTAreas.A7.convOp (κ t) f)
          (Work.KMTAreas.A7.convOp (κ' t) g) x)
      = ∫ t in (1/2 : ℝ)..1,
          Work.KMTAreas.A7.bilinOp (Work.KMTAreas.A7.kernComp K (κ t) (κ' t)) f g x := by
        rw [intervalIntegral.integral_of_le h12, intervalIntegral.integral_of_le h12]
        exact MeasureTheory.integral_congr_ae hae
    _ = Work.KMTAreas.A7.bilinOp
          (fun a b => ∫ t in (1 / 2 : ℝ)..1,
            Work.KMTAreas.A7.kernComp K (κ t) (κ' t) a b) f g x :=
        (bilinOp_kernel_intervalIntegral (fun t a b => Work.KMTAreas.A7.kernComp K (κ t) (κ' t) a b)
          f g Cf Cg x hf hg hCf hCg
          (fun a b => aemeasurable_kernComp K κ κ' a b hK hκ hκ' hmκ hmκ')
          (tsum_lintegral_enorm_kernComp_ne_top K κ κ' BK B1 B2 hK hKb hκ hκ'
            hκb hκb' hBK hB1 hB2 hmκ hmκ')).symm

end

end Work.KMTPlan.A6
