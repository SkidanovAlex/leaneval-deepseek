/-
# Bridge lemma: `L₁₂dens(𝓛_Γ f) ∈ L¹((0,∞))`

The requested lemma `L12densLGamma` is the `hint3` input of the `L₁₂`-zero-mode chapter:
the density of `𝓛_Γ f` is integrable, given the corresponding facts for `f` and for the
angular moment of `∂_z f`.

The whole content is the expansion

  `L₁₂dens(𝓛_Γ f)(s) = L₁₂dens f (s) + Kav(∂_z f)(s) - 2 L₁₂dens f (s)/(1+s)
      - 2 L₁₂(f)(s)/(1+s)²`

(`Kav(∂_z f)(s) = ∫_θ K θ ∂_z f(s,θ)`), valid for every `s > 0` for which the angular
slices of `f` and of `∂_z f` are integrable, plus the termwise integrability of the right
hand side:

* `L₁₂dens f ∈ L¹` is a hypothesis (`hintL2`);
* `Kav(∂_z f) ∈ L¹` is a hypothesis (`hmd`);
* `|L₁₂dens f|/(1+s) ≤ |L₁₂dens f|` and `|L₁₂(f)(s)| ≤ ∫_0^∞ |L₁₂dens f|` so that the last
  two terms are dominated by a multiple of `|L₁₂dens f|` resp. of `(1+s)^{-2}`.

The two ingredients for the pointwise identity are
* `integrableOn_slice_of_SmoothOpen_HkMem` (`SmoothOpen F` + `HkMem α 4 F` give the
  angular slice integrability of the density integrand of `f`), and
* the a.e. angular slice integrability of `∂_z f` (Fubini from `hint`).

`SmoothOpen`/`HkMem` are used *only* there; the `L¹` bookkeeping uses just `hintL2`,
`hmd` and the definition of `L₁₂`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FM.Core
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.Coercivity.CommutZAux
import Submission.Work.Spaces.CAux.integrableOn_GamK
import Submission.Work.Coercivity.Basic
import Submission.Work.FTS.LocData.HkSqAux.integrableOn_and_integral_Ici_oneAdd_rpow_neg_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero.Bridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The a.e. angular-slice integrability of `∂_z f` -/

/-- For almost every `r > 0` the angular slice `θ ↦ K(θ)·∂_z f(r,θ)` is integrable on
`Iθ`.  This is the a.e.-slice form of the joint integrability hypothesis `hint`
(Fubini on the product `(0,∞) × Iθ`). -/
theorem ae_integrableOn_K_pz_of_hint {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ)) :
    ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.pz f r θ)
        Work.Spaces.Iθ := by
  have h := hint
  rw [MeasureTheory.IntegrableOn, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    ← Measure.prod_restrict] at h
  filter_upwards [h.prod_right_ae] with r hr
  simpa [Work.Spaces.Iθ, MeasureTheory.IntegrableOn, Function.uncurry] using hr

/-! ## Two elementary integral identities -/

/-- The angular normalisation: `∫_{Iθ} K(θ)Γ(θ) dθ = c(α)`. -/
theorem integral_K_Gam_eq_c_bridge (α : ℝ) :
    ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ = Work.Spaces.c α := by
  simp only [Work.Spaces.c]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- Additivity of a set integral over a sum of four functions. -/
theorem setIntegral_add_four_bridge {s : Set ℝ} {a b c d : ℝ → ℝ}
    (ha : MeasureTheory.IntegrableOn a s) (hb : MeasureTheory.IntegrableOn b s)
    (hc : MeasureTheory.IntegrableOn c s) (hd : MeasureTheory.IntegrableOn d s) :
    (∫ x in s, (a x + b x + c x + d x))
      = (∫ x in s, a x) + (∫ x in s, b x) + (∫ x in s, c x) + (∫ x in s, d x) := by
  have h1 : (∫ x in s, a x) + (∫ x in s, b x) = (∫ x in s, a x + b x) :=
    (MeasureTheory.integral_add ha hb).symm
  have h2 : (∫ x in s, a x + b x) + (∫ x in s, c x) = (∫ x in s, a x + b x + c x) :=
    (MeasureTheory.integral_add (ha.add hb) hc).symm
  have h3 : (∫ x in s, a x + b x + c x) + (∫ x in s, d x)
      = (∫ x in s, a x + b x + c x + d x) :=
    (MeasureTheory.integral_add ((ha.add hb).add hc) hd).symm
  rw [← h3, ← h2, ← h1]

/-! ## The density identity, a.e. in `r` -/

/-- **The density of `𝓛_Γ f` along the radial variable**, for almost every `r > 0`, in
terms of the density of `f`, the angular moment of `∂_z f` and the tail integral
`L₁₂(f)(r) = ∫_r^∞ L₁₂dens f`.  This is the identity on which the `L¹`-statement rests. -/
theorem L12dens_LGamma_ae_bridge {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ / r)
        Work.Spaces.Iθ) :
    (fun r : ℝ => Work.Construction.L12dens (Work.Coercivity.LGamma α f) r)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
    (fun r : ℝ => Work.Construction.L12dens f r
      + (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
      - 2 * Work.Construction.L12dens f r / (1 + r)
      - 2 * Work.Coercivity.L12f f r / (1 + r) ^ 2) := by
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  have hGK : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ * Work.Spaces.Gam α θ) Work.Spaces.Iθ := by
    simpa only [mul_comm] using Work.Spaces.CAux.integrableOn_GamK α hα
  filter_upwards [ae_integrableOn_K_pz_of_hint hint,
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hpz hr
  have hrpos : 0 < r := hr
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have h1r : (1 : ℝ) + r ≠ 0 := by positivity
  -- the four elementary pieces of the density of `𝓛_Γ f`
  set g1 : ℝ → ℝ := fun θ => Work.Spaces.K θ * f r θ / r with hg1
  set g2 : ℝ → ℝ := fun θ => Work.Spaces.K θ * Work.Spaces.pz f r θ with hg2
  set g3 : ℝ → ℝ := fun θ => (-2 / (1 + r)) * g1 θ with hg3
  set g4 : ℝ → ℝ :=
    fun θ => (-(2 * Work.Coercivity.L12f f r / (Work.Spaces.c α * (1 + r) ^ 2)))
      * (Work.Spaces.K θ * Work.Spaces.Gam α θ) with hg4
  have h1 : MeasureTheory.IntegrableOn g1 Work.Spaces.Iθ := hslice r hrpos
  have h2 : MeasureTheory.IntegrableOn g2 Work.Spaces.Iθ := hpz
  have h3 : MeasureTheory.IntegrableOn g3 Work.Spaces.Iθ := by
    rw [hg3]; exact h1.const_mul _
  have h4 : MeasureTheory.IntegrableOn g4 Work.Spaces.Iθ := by
    rw [hg4]; exact hGK.const_mul _
  -- pointwise expansion of the density integrand
  have hpt : ∀ θ : ℝ,
      Work.Spaces.K θ * Work.Coercivity.LGamma α f r θ / r = (g1 + g2 + g3 + g4) θ := by
    intro θ
    simp only [hg1, hg2, hg3, hg4, Pi.add_apply, Work.Coercivity.LGamma, Work.Coercivity.L,
      Work.Spaces.Dz]
    field_simp
    ring
  -- the density is the integral of the four pieces
  have hG : Work.Construction.L12dens (Work.Coercivity.LGamma α f) r
      = ∫ θ in Work.Spaces.Iθ, (g1 + g2 + g3 + g4) θ := by
    rw [show Work.Construction.L12dens (Work.Coercivity.LGamma α f) r
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Coercivity.LGamma α f r θ / r
        from rfl]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => hpt θ)
  -- split the integral into the four pieces
  have hsplit : (∫ θ in Work.Spaces.Iθ, (g1 + g2 + g3 + g4) θ)
      = (∫ θ in Work.Spaces.Iθ, g1 θ) + (∫ θ in Work.Spaces.Iθ, g2 θ)
        + (∫ θ in Work.Spaces.Iθ, g3 θ) + (∫ θ in Work.Spaces.Iθ, g4 θ) :=
    setIntegral_add_four_bridge h1 h2 h3 h4
  -- value of each piece
  have hu1 : (∫ θ in Work.Spaces.Iθ, g1 θ) = Work.Construction.L12dens f r := by
    rw [hg1]; rfl
  have hu2 : (∫ θ in Work.Spaces.Iθ, g2 θ)
      = ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ := by
    rw [hg2]
  have hu3 : (∫ θ in Work.Spaces.Iθ, g3 θ)
      = (-2 / (1 + r)) * Work.Construction.L12dens f r := by
    have h3' : (∫ θ in Work.Spaces.Iθ, g3 θ)
        = (-2 / (1 + r)) * (∫ θ in Work.Spaces.Iθ, g1 θ) := by
      rw [hg3]; exact MeasureTheory.integral_const_mul _ _
    rw [h3', hu1]
  have hu4 : (∫ θ in Work.Spaces.Iθ, g4 θ)
      = (-(2 * Work.Coercivity.L12f f r / (Work.Spaces.c α * (1 + r) ^ 2)))
        * Work.Spaces.c α := by
    have h4' : (∫ θ in Work.Spaces.Iθ, g4 θ)
        = (-(2 * Work.Coercivity.L12f f r / (Work.Spaces.c α * (1 + r) ^ 2)))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.Gam α θ) := by
      rw [hg4]; exact MeasureTheory.integral_const_mul _ _
    rw [h4', integral_K_Gam_eq_c_bridge]
  -- assemble
  have hmain : Work.Construction.L12dens (Work.Coercivity.LGamma α f) r
      = Work.Construction.L12dens f r
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
        - 2 * Work.Construction.L12dens f r / (1 + r)
        - 2 * Work.Coercivity.L12f f r / (1 + r) ^ 2 := by
    rw [hG, hsplit, hu1, hu2, hu3, hu4]
    field_simp
    ring
  exact hmain

/-! ## Termwise `L¹`-bookkeeping -/

/-- The transformed term `r ↦ A r/(1+r)` is integrable as soon as `A ∈ L¹((0,∞))`. -/
theorem integrableOn_div_oneAdd_of_integrableOn {A : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun r : ℝ => A r / (1 + r)) (Set.Ioi 0) := by
  have hinv : AEStronglyMeasurable (fun r : ℝ => (1 + r)⁻¹)
      (volume.restrict (Set.Ioi 0)) :=
    (ContinuousOn.inv₀ (by fun_prop : ContinuousOn (fun r : ℝ => 1 + r) (Set.Ioi 0))
      (fun r hr => by have h := Set.mem_Ioi.mp hr; positivity)).aestronglyMeasurable
        measurableSet_Ioi
  refine hA.norm.mono' ?_ ?_
  · have hmem : AEStronglyMeasurable (A * fun r : ℝ => (1 + r)⁻¹)
        (volume.restrict (Set.Ioi 0)) := hA.aestronglyMeasurable.mul hinv
    refine hmem.congr ?_
    filter_upwards with r
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun r hr => ?_
    have hrpos : 0 < r := hr
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + r)]
    exact div_le_self (abs_nonneg _) (by linarith : (1 : ℝ) ≤ 1 + r)

/-- `(1+r)^{-2}` is integrable on `(0,∞)`: the two summands of the splitting
`(0,∞) = (0,1] ∪ (1,∞)` are handled by boundedness on a finite interval resp. by the
tail `r ↦ r^{-2}`. -/
theorem integrableOn_oneAdd_rpow_neg_two_Ioi_zero :
    MeasureTheory.IntegrableOn (fun r : ℝ => (1 + r) ^ (-2 : ℝ)) (Set.Ioi 0) := by
  have hbase : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Ici 0) := by
    have hunion : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ici 0 := by
      ext z
      simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
      constructor
      · rintro (⟨h1, h2⟩ | h) <;> linarith
      · intro h'
        rcases lt_or_ge z 1 with hz | hz
        · exact Or.inl ⟨h', le_of_lt hz⟩
        · exact Or.inr hz
    have hIcc : MeasureTheory.IntegrableOn (fun z : ℝ => (1 + z) ^ (-2 : ℝ)) (Set.Icc 0 1) := by
      refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ 1 ?_
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      · refine ((continuousOn_const.add continuousOn_id).rpow_const ?_).aestronglyMeasurable
          measurableSet_Icc
        intro z hz
        exact Or.inl (by simp only [Pi.add_apply, id_eq]; linarith [hz.1])
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hz.1]) _)]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hz.1]) (by norm_num)
    have hInt :=
      (Work.FTS.LocData.HkSqAux.integrableOn_and_integral_Ici_oneAdd_rpow_neg_two 1 one_pos).1
    rw [← hunion]; exact hIcc.union hInt
  exact hbase.mono_set (fun x hx => Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hx)))

/-- The tail-integral term `r ↦ (∫_r^∞ A)/(1+r)²` is integrable as soon as
`A ∈ L¹((0,∞))`: the tail is bounded by `∫_0^∞ |A|` and `(1+r)^{-2}` is integrable. -/
theorem integrableOn_Ioi_integral_div_quad_of_integrableOn {A : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun r : ℝ => (∫ s in Set.Ioi r, A s) / (1 + r) ^ 2)
      (Set.Ioi 0) := by
  set M : ℝ := ∫ s in Set.Ioi 0, ‖A s‖ with hM
  have hAbs : MeasureTheory.IntegrableOn (fun s : ℝ => ‖A s‖) (Set.Ioi 0) := hA.norm
  -- the tail is bounded by `M`
  have hbd : ∀ r ∈ Set.Ioi (0 : ℝ), ‖∫ s in Set.Ioi r, A s‖ ≤ M := by
    intro r hr
    have hrpos : 0 < r := hr
    have hmono : (∫ s in Set.Ioi r, ‖A s‖) ≤ M := by
      rw [hM]
      exact MeasureTheory.setIntegral_mono_set hAbs
        (ae_of_all _ fun s => norm_nonneg _)
        (ae_of_all _ fun s hs => lt_of_lt_of_le hrpos (le_of_lt (Set.mem_Ioi.mp hs)))
    calc ‖∫ s in Set.Ioi r, A s‖ = ‖∫ s, A s ∂(volume.restrict (Set.Ioi r))‖ := rfl
      _ ≤ ∫ s, ‖A s‖ ∂(volume.restrict (Set.Ioi r)) :=
          MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi r)) A
      _ = ∫ s in Set.Ioi r, ‖A s‖ := rfl
      _ ≤ M := hmono
  -- the majorant `M(1+r)^{-2}`
  have hIntDomR : MeasureTheory.IntegrableOn (fun r : ℝ => (1 + r) ^ (-2 : ℝ)) (Set.Ioi 0) :=
    integrableOn_oneAdd_rpow_neg_two_Ioi_zero
  have hIntDomAux : MeasureTheory.IntegrableOn
      (fun r : ℝ => M * (1 + r) ^ (-2 : ℝ)) (Set.Ioi 0) :=
    MeasureTheory.Integrable.const_mul hIntDomR M
  have hIntDom : MeasureTheory.IntegrableOn (fun r : ℝ => M / (1 + r) ^ 2) (Set.Ioi 0) := by
    refine hIntDomAux.congr_fun_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hpos : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
    rw [div_eq_mul_inv, Real.rpow_neg hpos.le, Real.rpow_ofNat]
  refine hIntDom.mono' ?_ ?_
  · have hcont : ContinuousOn (fun r => ∫ s in Set.Ioi r, A s) (Set.Ioi 0) :=
      hA.continuousOn_Ici_primitive_Ioi.mono Set.Ioi_subset_Ici_self
    have h1 : AEStronglyMeasurable (fun r => ∫ s in Set.Ioi r, A s)
        (volume.restrict (Set.Ioi 0)) := hcont.aestronglyMeasurable measurableSet_Ioi
    have hinv : AEStronglyMeasurable (fun r : ℝ => ((1 + r) ^ 2)⁻¹)
        (volume.restrict (Set.Ioi 0)) :=
      (ContinuousOn.inv₀ (by fun_prop : ContinuousOn (fun r : ℝ => (1 + r) ^ 2) (Set.Ioi 0))
        (fun r hr => by have h := Set.mem_Ioi.mp hr; positivity)).aestronglyMeasurable
          measurableSet_Ioi
    have hmem : AEStronglyMeasurable
        ((fun r => ∫ s in Set.Ioi r, A s) * fun r : ℝ => ((1 + r) ^ 2)⁻¹)
        (volume.restrict (Set.Ioi 0)) := h1.mul hinv
    refine hmem.congr ?_
    filter_upwards with r
    simp only [Pi.mul_apply, div_eq_mul_inv]
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun r hr => ?_
    have hpos : (0 : ℝ) < 1 + r := by linarith [Set.mem_Ioi.mp hr]
    have hsq : (0 : ℝ) < (1 + r) ^ 2 := by positivity
    have h1 : ‖(∫ s in Set.Ioi r, A s) / (1 + r) ^ 2‖
        = ‖∫ s in Set.Ioi r, A s‖ / (1 + r) ^ 2 := by
      rw [norm_div, Real.norm_of_nonneg hsq.le]
    rw [h1]
    exact div_le_div_of_nonneg_right (hbd r hr) hsq.le

/-! ## The requested bridge lemma -/

theorem L12densLGamma {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (hint : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Work.Spaces.pz f p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ))
    (hintL2 : MeasureTheory.IntegrableOn (Work.Construction.L12dens f) (Set.Ioi 0))
    (hmd : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
      (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn
      (Work.Construction.L12dens (Work.Coercivity.LGamma α f)) (Set.Ioi 0) := by
  -- the angular slices of the density integrand of `f` are integrable, for every `r > 0`
  have hslice : ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * f r θ / r)
        Work.Spaces.Iθ :=
    fun r hr => Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hsm hmem hr
  have hae := L12dens_LGamma_ae_bridge hα hα1 hint hslice
  have h3' : MeasureTheory.IntegrableOn
      (fun r : ℝ => 2 * (Work.Construction.L12dens f r / (1 + r))) (Set.Ioi 0) :=
    (integrableOn_div_oneAdd_of_integrableOn hintL2).const_mul 2
  have h3 : MeasureTheory.IntegrableOn
      (fun r : ℝ => 2 * Work.Construction.L12dens f r / (1 + r)) (Set.Ioi 0) := by
    refine h3'.congr_fun_ae ?_
    filter_upwards with r
    ring
  have h4' : MeasureTheory.IntegrableOn
      (fun r : ℝ => 2 * ((∫ s in Set.Ioi r, Work.Construction.L12dens f s) / (1 + r) ^ 2))
      (Set.Ioi 0) :=
    (integrableOn_Ioi_integral_div_quad_of_integrableOn
      (A := Work.Construction.L12dens f) hintL2).const_mul 2
  have h4 : MeasureTheory.IntegrableOn
      (fun r : ℝ => 2 * Work.Coercivity.L12f f r / (1 + r) ^ 2) (Set.Ioi 0) := by
    refine h4'.congr_fun_ae ?_
    filter_upwards with r
    simp only [div_eq_mul_inv, Work.Coercivity.L12f, Work.FM.L12,
      Work.Construction.L12dens]
    ring
  have hSum : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Construction.L12dens f r
        + (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * Work.Spaces.pz f r θ)
        - 2 * Work.Construction.L12dens f r / (1 + r)
        - 2 * Work.Coercivity.L12f f r / (1 + r) ^ 2) (Set.Ioi 0) :=
    ((hintL2.add hmd).sub h3).sub h4
  exact hSum.congr_fun_ae hae.symm

end Work.FTS.StrongEps.EpsZero.Bridge
