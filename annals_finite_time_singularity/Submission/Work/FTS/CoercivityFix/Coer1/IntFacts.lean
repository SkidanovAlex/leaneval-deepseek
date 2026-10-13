/-
# The integrability bundle `IntPkg` for `RegQ α 2 f`

This file proves that every integrand occurring in the four coercivity estimates of the clean
operator `Lhat` is `IntegrableOn` the quadrant, for `f ∈ RegQ α 2` — i.e. it constructs
`Work.FTS.CoercivityFix.Coer1.IntPkg α f` (`IntPkg_Q`).

The sources of integrability are:

* the summands of `HkIntegrand α 2 f` (`f ∈ ℋ²` gives their joint integrability by domination,
  `Work.Spaces.sq_le_HkIntegrand_z` / `_mixed`);
* the monotonicity of the angular weight (`sig_eta_le_sig_gam_Iθ`, `one_le_sig_eta_ae`), which
  turns the `γ`-weighted squares into the `η`-weighted and plain ones;
* the products of two `L²`-blocks (`integrableOn_mul_of_sq_Q`, from `2|ab| ≤ a² + b²`, with the
  a.e. strong measurability supplied by continuity on the open quadrant);
* multiplication by the bounded function `1/(1+z)` (`integrableOn_div_one_add_Q`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Coer1.Defs
import Submission.Work.FTS.CoercivityFix.Coer1.HkSqOne
import Submission.Work.FTS.CoercivityFix.Coer1.zIBP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Tools -/

theorem iz_prod_restrict : (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)
    = (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]

theorem iz_ae_restrict : (MeasureTheory.volume.restrict Work.Spaces.Iz)
    = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · have h : Work.Spaces.Iz \ Set.Ioi 0 = {0} := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, Work.Spaces.Iz,
        Set.mem_Ici, not_lt]
      constructor
      · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
      · rintro rfl; exact ⟨le_refl 0, le_refl 0⟩
    rw [h, Real.volume_singleton]
  · have h : Set.Ioi (0 : ℝ) \ Work.Spaces.Iz = ∅ := by
      rw [Work.Spaces.Iz, Set.sdiff_eq_empty]
      exact Set.Ioi_subset_Ici_self
    rw [h, MeasureTheory.measure_empty]

/-- The elementary `2|ab| ≤ a² + b²`, weighted by `ρ ≥ 0`. -/
theorem two_abs_mul_le (a b ρ : ℝ) (hρ : 0 ≤ ρ) :
    2 * (|a * b| * ρ) ≤ a ^ 2 * ρ + b ^ 2 * ρ := by
  have h : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
    rw [abs_mul, ← sq_abs a, ← sq_abs b]
    nlinarith [sq_nonneg (|a| - |b|)]
  nlinarith [h, hρ]

/-- `|abρ| ≤ a²ρ + b²ρ` for `ρ ≥ 0`. -/
theorem abs_mul_mul_le (a b ρ : ℝ) (hρ : 0 ≤ ρ) : |a * b * ρ| ≤ a ^ 2 * ρ + b ^ 2 * ρ := by
  have h := two_abs_mul_le a b ρ hρ
  have h1 : 0 ≤ a ^ 2 * ρ := mul_nonneg (sq_nonneg a) hρ
  have h2 : 0 ≤ b ^ 2 * ρ := mul_nonneg (sq_nonneg b) hρ
  rw [abs_mul, abs_of_nonneg hρ]
  linarith [h, h1, h2]

/-- Lifting an a.e. statement in the angle to the product measure on the quadrant. -/
theorem ae_prod_snd_mem {t : Set ℝ} (ht : MeasurableSet t)
    (h : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ t) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p.2 ∈ t :=
  ((MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (s := Set.univ ×ˢ t) (MeasurableSet.univ.prod ht)).mpr
    (Filter.Eventually.of_forall fun _ => h.mono
      (fun y hy => ⟨Set.mem_univ _, hy⟩))).mono (fun p hp => hp.2)

/-- Lifting an a.e. statement in the radial variable to the product measure on the quadrant. -/
theorem ae_prod_fst_mem {s : Set ℝ} (hs : MeasurableSet s)
    (h : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ s) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      p.1 ∈ s :=
  ((MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
    (s := s ×ˢ Set.univ) (hs.prod MeasurableSet.univ)).mpr
    (h.mono (fun z hz => Filter.Eventually.of_forall
      (fun θ => ⟨hz, Set.mem_univ θ⟩)))).mono (fun p hp => hp.1)

theorem ae_prod_fst_pos :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 < p.1 := by
  have h1 : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Set.Ioi (0 : ℝ) := by
    rw [iz_ae_restrict]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  exact ae_prod_fst_mem (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi h1

theorem ae_prod_snd_mem_Ioo :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Set.Ioo 0 (π / 2) :=
  ae_prod_snd_mem measurableSet_Ioo ae_restrict_Iθ_mem_Ioo

/-- Clairaut for a `SmoothQuad` function on the open quadrant. -/
theorem contDiffAt_smoothQuad_two {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
  (hsq.contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
    ⟨by simp only [Set.mem_Ioi]; linarith, hθ⟩)).of_le (by simp [Work.Stability.smoothOrder])

/-- `D_z` and `D_θ` commute almost everywhere on the quadrant. -/
theorem ae_Dz_Dth_comm {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      Work.Spaces.Dz (Work.Spaces.Dth f) p.1 p.2
        = Work.Spaces.Dth (Work.Spaces.Dz f) p.1 p.2 :=
  (ae_prod_fst_pos.and ae_prod_snd_mem_Ioo).mono
    (fun p hp => Work.Spaces.Dz_Dth_comm (contDiffAt_smoothQuad_two hsq hp.1 hp.2))

/-- Sum of two `IntegrableOn` functions on the quadrant. -/
theorem integrableOn_add_Q {g h : Fn}
    (hg : MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hh : MeasureTheory.IntegrableOn (Function.uncurry h) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => g z θ + h z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn]
  exact (hg.add hh).congr (Filter.Eventually.of_forall (fun p => by
    rcases p with ⟨z, θ⟩; rfl))

/-- Multiplication of an `IntegrableOn` function on the quadrant by the bounded factor
`1/(1+z)`. -/
theorem integrableOn_div_one_add_Q {g : Fn}
    (hg : MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => g z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn]
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Function.uncurry g p * (1 + p.1)⁻¹)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    hg.aestronglyMeasurable.mul
      (((measurable_const.add measurable_fst).inv).aestronglyMeasurable)
  have hae : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)), 0 ≤ p.1 :=
    (MeasureTheory.ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)).mono
      (fun p hp => hp.1)
  have hmain : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Function.uncurry g p * (1 + p.1)⁻¹)
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    refine hg.norm.mono' haesm ?_
    filter_upwards [hae] with p hp1
    rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + p.1)⁻¹)]
    calc ‖Function.uncurry g p‖ * (1 + p.1)⁻¹
        ≤ ‖Function.uncurry g p‖ * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [inv_le_one₀ (by linarith : (0 : ℝ) < 1 + p.1)]
          linarith
      _ = ‖Function.uncurry g p‖ := mul_one _
  refine hmain.congr (Filter.Eventually.of_forall (fun p => ?_))
  rcases p with ⟨z, θ⟩
  rfl

/-- The product of two `L²`-blocks is integrable (`2|ab| ≤ a² + b²`); the a.e. strong
measurability of the product comes from continuity on the open quadrant. -/
theorem integrableOn_mul_of_sq_Q {ρ φ ψ : Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2 * ψ p.1 p.2 * ρ p.1 p.2) Qd)
    (hρ : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => φ z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => ψ z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => φ z θ * ψ z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn]
  have hmaj : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (φ p.1 p.2 ^ 2 * ρ p.1 p.2 + ψ p.1 p.2 ^ 2 * ρ p.1 p.2))
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    (h1.add h2).congr (Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, θ⟩; rfl))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (Function.uncurry (fun z θ => φ z θ * ψ z θ * ρ z θ))
      ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
    have h := Work.Spaces.aesm_of_continuousOn_Qd _ hcont
    rwa [iz_prod_restrict] at h
  refine hmaj.mono' haesm ?_
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc) |>.mono
      (fun p hp => hp.2)
  filter_upwards [hmem] with p hp
  have := abs_mul_mul_le (φ p.1 p.2) (ψ p.1 p.2) (ρ p.1 p.2) (hρ p.1 p.2 hp)
  rwa [Function.uncurry_apply_pair, Real.norm_eq_abs]

/-- Each summand of the `ℋ^k`-integrand, squared and weighted, is jointly integrable. -/
theorem joint_of_le_HkIntegrand (α : ℝ) (k : ℕ) {f A : Fn} (hm : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => (A p.1 p.2) ^ 2) Qd)
    (hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (A z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => (A z θ) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hI2 := i2Mem_sq_of_le α k hm hcont hle
  have hAE : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun z θ => (A z θ) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (A z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hI2.1
  have hjoint := (Work.Spaces.integrable_prod_of_iterated (fun z θ => sq_nonneg _) hAE hslice
    hI2.2).1
  rw [MeasureTheory.IntegrableOn, ← iz_prod_restrict]
  exact hjoint

/-- Domination of an integrand by another whose a.e. bound is known, with the minorant
continuous on the open quadrant. -/
theorem integrableOn_of_le_Q {g h : Fn} (hcont : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) Qd)
    (hh : MeasureTheory.IntegrableOn (Function.uncurry h) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hle : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)), |g p.1 p.2| ≤ h p.1 p.2) :
    MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hh' : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact hh
  have haesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry g)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hcont
  have hle' : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ‖Function.uncurry g p‖ ≤ h p.1 p.2 := by
    filter_upwards [hle] with p hp
    rwa [Function.uncurry_apply_pair, Real.norm_eq_abs]
  have hmain := hh'.mono' haesm hle'
  rw [MeasureTheory.IntegrableOn, ← iz_prod_restrict]
  exact hmain

/-- An `IntegrableOn` function on the quadrant has integrable `θ`-slices for a.e. angle. -/
theorem ae_slice_of_integrableOn {g : Fn}
    (hg : MeasureTheory.IntegrableOn (Function.uncurry g) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable (fun z => g z θ) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hg' : MeasureTheory.Integrable (Function.uncurry g)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [iz_prod_restrict]; exact hg
  exact hg'.prod_left_ae

/-! ## Continuity of the blocks on the open quadrant -/

/-- The weight `w²` (no angular factor) is continuous on the open quadrant. -/
theorem continuousOn_w2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2)
      = fun p : ℝ × ℝ => ((1 + p.1) ^ 2 / p.1 ^ 2) ^ 2 := by
    funext p; rfl
  rw [hfun]
  exact (ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))).pow 2

theorem continuousOn_Rho (β : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Rho β p.1 p.2) Qd := by
  have hsinpos : ∀ p ∈ Qd, 0 < Real.sin (2 * p.2) :=
    fun p hp =>
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2) Qd :=
    continuousOn_w2
  have hsig : ContinuousOn (fun p : ℝ × ℝ => sig β p.2) Qd := by
    have hfun : (fun p : ℝ × ℝ => sig β p.2)
        = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-β) := by
      funext p; rfl
    rw [hfun]
    exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
      |>.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  have hfun : (fun p : ℝ × ℝ => Rho β p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1 ^ 2 * sig β p.2 := rfl
  rw [hfun]
  exact hw.mul hsig

theorem continuousOn_DzIter_Q {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i f p.1 p.2) Qd :=
  ((Work.FTS.LocData.contDiffOn_DzIter (Work.FTS.LocData.isOpen_quadU) hsq i).continuousOn).mono
    (fun p hp => by
      simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩)

theorem continuousOn_mixed_Q {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) Qd :=
  ((Work.FTS.LocData.contDiffOn_mixed (Work.FTS.LocData.isOpen_quadU) hsq j i).continuousOn).mono
    (fun p hp => by
      simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩)

theorem continuousOn_f_Q {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Qd :=
  hsq.continuousOn.mono
    (fun p hp => by
      simp only [Qd, Work.Spaces.quadU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2.1, hp.2.2⟩)

/-- The weight `Rho β` is nonnegative on the closed angular interval. -/
theorem Rho_nonneg (β : ℝ) : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ Rho β z θ :=
  fun z θ hθ => by
    rw [Rho, sig]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_nonneg_of_mem_Iθ hθ) _)

theorem w2_nonneg : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ Work.Spaces.w z ^ 2 :=
  fun _ _ _ => sq_nonneg _

/-! ## The weighted squares -/

/-- The squared `D_z`-blocks with the `η`-weight. -/
theorem sq_DzEta (α : ℝ) {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f)
    (hm : Work.Spaces.HkMem α 2 f) (i : ℕ) (hi : i ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := joint_of_le_HkIntegrand α 2 hm (continuousOn_Dz_wdiv hsq i)
    (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_z α 2 f z θ i hi)
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair] at hp ⊢
  rw [mul_pow, sig_div_sq_Iθ Work.Spaces.eta (by rw [Work.Spaces.eta]; norm_num) z θ hp.2]
  rfl

/-- The squared mixed blocks with the `γ`-weight. -/
theorem sq_MixedGam (α : ℝ) (hα : 0 < α) {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f)
    (hm : Work.Spaces.HkMem α 2 f) (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Rho (Work.Spaces.gam α) z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := joint_of_le_HkIntegrand α 2 hm (continuousOn_mixed_Wt α hsq j i)
    (fun z _ θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 2 f z θ i j hi hij)
  refine h.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair] at hp ⊢
  rw [mul_pow, Wt_sq_self_Iθ α z θ hα hp.2]
  rfl

/-- The `η`-weight is dominated by the `γ`-weight on the *whole* closed angular interval. -/
theorem sig_eta_le_sig_gam_Iθ (α : ℝ) (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    sig Work.Spaces.eta θ ≤ sig (Work.Spaces.gam α) θ := by
  rcases eq_or_lt_of_le (sin_nonneg_of_mem_Iθ hθ) with h | h
  · simp only [sig]
    rw [← h, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : -(Work.Spaces.eta) ≠ 0),
      Real.zero_rpow (show -(Work.Spaces.gam α) ≠ 0 by
        have : 0 < Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
        linarith)]
  · refine sig_eta_le_sig_gam α hα ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · exfalso
        rw [← h0, mul_zero, Real.sin_zero] at h
        exact lt_irrefl 0 h
      · exact h0
    · rcases eq_or_lt_of_le hθ.2 with h0 | h0
      · exfalso
        rw [h0, show (2 : ℝ) * (π / 2) = π by ring, Real.sin_pi] at h
        exact lt_irrefl 0 h
      · exact h0

/-- The `η`-weight is dominated by the `γ`-weight. -/
theorem Rho_eta_le_Rho_gam (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Rho Work.Spaces.eta z θ ≤ Rho (Work.Spaces.gam α) z θ := by
  simp only [Rho, sig]
  exact mul_le_mul_of_nonneg_left (sig_eta_le_sig_gam_Iθ α hα hθ) (sq_nonneg _)

/-- The plain radial weight is dominated by the `η`-weight on the open interval. -/
theorem w2_le_Rho_eta (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z ^ 2 ≤ Rho Work.Spaces.eta z θ := by
  have h := mul_le_mul_of_nonneg_left (one_le_sig_eta hθ) (sq_nonneg (Work.Spaces.w z))
  simpa only [Rho, sig, mul_one] using h

/-- The plain radial weight is dominated by the `γ`-weight on the open interval. -/
theorem w2_le_Rho_gam (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.w z ^ 2 ≤ Rho (Work.Spaces.gam α) z θ :=
  le_trans (w2_le_Rho_eta z θ hθ)
    (Rho_eta_le_Rho_gam α hα z θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)

/-- The squared mixed blocks with the `η`-weight (dominated by the `γ`-weight). -/
theorem sq_MixedEta (α : ℝ) (hα : 0 < α) {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f)
    (hm : Work.Spaces.HkMem α 2 f) (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := sq_MixedGam α hα hsq hm i j hi hij
  refine integrableOn_of_le_Q ((continuousOn_mixed_Q hsq j i).pow 2 |>.mul (continuousOn_Rho _))
    h ?_
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ :=
    ae_prod_snd_mem measurableSet_Icc (MeasureTheory.ae_restrict_mem measurableSet_Icc)
  filter_upwards [hmem] with p hp
  rcases p with ⟨z, θ⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Rho_nonneg _ z θ hp)]
  exact mul_le_mul_of_nonneg_left (Rho_eta_le_Rho_gam α hα z θ hp)
    (sq_nonneg (Work.Spaces.mixed j i f z θ))

/-- The squared `D_z`-blocks with the plain radial weight. -/
theorem sq_DzOne (α : ℝ) {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f)
    (hm : Work.Spaces.HkMem α 2 f) (i : ℕ) (hi : i ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := sq_DzEta α hsq hm i hi
  refine integrableOn_of_le_Q ((continuousOn_DzIter_Q hsq i).pow 2 |>.mul continuousOn_w2) h ?_
  refine (ae_prod_snd_mem measurableSet_Ioo ae_restrict_Iθ_mem_Ioo).mono (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (w2_le_Rho_eta z θ hp)
    (sq_nonneg (Work.Spaces.DzIter i f z θ))

/-- The squared mixed blocks with the plain radial weight. -/
theorem sq_MixedOne (α : ℝ) (hα : 0 < α) {f : Fn} (hsq : Work.FTS.LocData.SmoothQuad f)
    (hm : Work.Spaces.HkMem α 2 f) (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 2) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := sq_MixedGam α hα hsq hm i j hi hij
  refine integrableOn_of_le_Q ((continuousOn_mixed_Q hsq j i).pow 2 |>.mul continuousOn_w2) h ?_
  refine (ae_prod_snd_mem measurableSet_Ioo ae_restrict_Iθ_mem_Ioo).mono (fun p hp => ?_)
  rcases p with ⟨z, θ⟩
  rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left (w2_le_Rho_gam α hα z θ hp)
    (sq_nonneg (Work.Spaces.mixed j i f z θ))

/-! ## The `𝓛`- and transport pairings -/

/-- The `𝓛`-pairing `𝓛u·u·ρ` is integrable as soon as `u²ρ` and `(D_zu)²ρ` are. -/
theorem intL_of {u : Fn} {ρ : Fn} (hu : Work.FTS.LocData.SmoothQuad u)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Qd)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hsq : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hdz : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hcross : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_mul_of_sq_Q (((continuousOn_mixed_Q hu 1 0).mul (continuousOn_f_Q hu)).mul hρc)
      hρnn hdz hsq
  have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := integrableOn_add_Q hsq hcross
  have h3 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ) / (1 + z))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_div_one_add_Q hsq
  have h4 := h3.const_mul (-2)
  have h5 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (u z θ ^ 2 * ρ z θ + Work.Spaces.Dz u z θ * u z θ * ρ z θ)
        + (-2) * ((u z θ ^ 2 * ρ z θ) / (1 + z)))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_add_Q h1 h4
  refine h5.congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Work.Coercivity.L]
  ring

/-- The transport pairing `D_θu·u·ρ/(1+z)` is integrable as soon as `u²ρ` and `(D_θu)²ρ` are. -/
theorem intTr_of {u : Fn} {ρ : Fn} (hu : Work.FTS.LocData.SmoothQuad u)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Qd)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hsq : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => u z θ ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hth : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth u z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * ρ z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hcross : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    integrableOn_mul_of_sq_Q (((continuousOn_mixed_Q hu 0 1).mul (continuousOn_f_Q hu)).mul hρc)
      hρnn hth hsq
  exact integrableOn_div_one_add_Q hcross

/-- The pointwise identity behind `ZIBP.intDeriv`. -/
theorem deriv_zw_sq_eq_Q {u : Fn} (hu : Work.FTS.LocData.SmoothQuad u) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    deriv (fun z' => z' * (u z' θ * Work.Spaces.w z') ^ 2) z
      = 2 * (Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2)
        - (u z θ * Work.Spaces.w z) ^ 2 := by
  have h1 := deriv_zw_sq_Q hu hz hθ
  have h2 := l_self_w_sq_Q hu hz hθ
  linarith [h1, h2]

/-- The `ZIBP` package, from the boundary limits and the integrability of `(u w)²` and
`𝓛u·u·w²`. -/
theorem zibp_of {u : Fn} (hu : Work.FTS.LocData.SmoothQuad u)
    (hbd0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0))
    (hbdT : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (u z θ * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0))
    (hSq : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (u z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    ZIBP u := by
  refine ⟨hu, hbd0, hbdT, ?_, ?_⟩
  · refine (ae_slice_of_integrableOn hSq).mono (fun θ hθ => ?_)
    rw [MeasureTheory.IntegrableOn, ← iz_ae_restrict]
    exact hθ
  · refine (((ae_slice_of_integrableOn hL).and (ae_slice_of_integrableOn hSq)).and
      ae_restrict_Iθ_mem_Ioo) |>.mono (fun θ hθ => ?_)
    obtain ⟨⟨hLθ, hSqθ⟩, hθIoo⟩ := hθ
    have h1 : MeasureTheory.IntegrableOn
        (fun z => Work.Coercivity.L u z θ * u z θ * Work.Spaces.w z ^ 2) (Set.Ioi 0) := by
      rw [MeasureTheory.IntegrableOn, ← iz_ae_restrict]; exact hLθ
    have h2 : MeasureTheory.IntegrableOn (fun z => (u z θ * Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
      rw [MeasureTheory.IntegrableOn, ← iz_ae_restrict]; exact hSqθ
    have h3 := (h1.const_mul 2).sub h2
    refine MeasureTheory.IntegrableOn.congr_fun h3 (fun z hz => ?_) measurableSet_Ioi
    exact (deriv_zw_sq_eq_Q hu hz hθIoo).symm

/-- `Lhat u · u · ρ` is integrable when `𝓛u·u·ρ` and the transport pairing are. -/
theorem intLhat_of {u : Fn} {ρ : Fn}
    (hL : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.L u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hT : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.Lhat u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hL.sub hT).congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Pi.sub_apply, Work.FTS.CoercivityFix.Lhat]
  ring

/-- The `η`-weighted transport pairing of `u` (in the `wip` normalisation) is integrable as soon
as the corresponding `hint` is. -/
theorem intTransport_of {u : Fn} {ρ : Fn}
    (hint : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth u z θ * u z θ * ρ z θ / (1 + z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Coercivity.Transport u z θ * u z θ * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hint.const_mul 3).congr (MeasureTheory.ae_restrict_of_forall_mem
    (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Work.Coercivity.Transport]
  ring

/-- The `D_z`-commutator defect `Ê₂f·D_zf·ρ` is integrable, from the pointwise bound
`|Ê₂f| ≤ (2|f| + 3|D_θf|)/4` and the three weighted squares. -/
theorem intE2hat_of {f : Fn} {ρ : Fn}
    (hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2
      * Work.Spaces.Dz f p.1 p.2 * ρ p.1 p.2) Qd)
    (hρnn : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ ^ 2 * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dz f z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (h3 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.Dth f z θ) ^ 2 * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
        * Work.Spaces.Dz f z θ * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hmaj : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (f z θ ^ 2 / 4 + 5 * (Work.Spaces.Dz f z θ) ^ 2 / 8
        + 3 * (Work.Spaces.Dth f z θ) ^ 2 / 8) * ρ z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have ha : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        (f z θ ^ 2 / 4) * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (h1.const_mul (1 / 4)).congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => by
          rcases p with ⟨z, θ⟩; simp only [Function.uncurry_apply_pair]; ring))
    have hb : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        (5 * (Work.Spaces.Dz f z θ) ^ 2 / 8) * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (h2.const_mul (5 / 8)).congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => by
          rcases p with ⟨z, θ⟩; simp only [Function.uncurry_apply_pair]; ring))
    have hc : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        (3 * (Work.Spaces.Dth f z θ) ^ 2 / 8) * ρ z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
      (h3.const_mul (3 / 8)).congr (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => by
          rcases p with ⟨z, θ⟩; simp only [Function.uncurry_apply_pair]; ring))
    refine (integrableOn_add_Q ha (integrableOn_add_Q hb hc)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem (measurableSet_Ici.prod measurableSet_Icc)
      (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair]
    ring
  refine integrableOn_of_le_Q hcont hmaj ?_
  have hmem : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)), p.2 ∈ Work.Spaces.Iθ :=
    ae_prod_snd_mem measurableSet_Icc (MeasureTheory.ae_restrict_mem measurableSet_Icc)
  filter_upwards [hmem, ae_prod_fst_pos] with p hp hzpos
  rcases p with ⟨z, θ⟩
  have hE2 := Work.FTS.CoercivityFix.E2hat_abs_le f (z := z) (θ := θ) (le_of_lt hzpos)
  have hf2 : 0 ≤ f z θ ^ 2 := sq_nonneg _
  have hd2 : 0 ≤ (Work.Spaces.Dz f z θ) ^ 2 := sq_nonneg _
  have ht2 : 0 ≤ (Work.Spaces.Dth f z θ) ^ 2 := sq_nonneg _
  have hρ := hρnn z θ hp
  have h1' : |f z θ| * |Work.Spaces.Dz f z θ| ≤ (f z θ ^ 2 + (Work.Spaces.Dz f z θ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|f z θ| - |Work.Spaces.Dz f z θ|), sq_abs (f z θ),
      sq_abs (Work.Spaces.Dz f z θ)]
  have h2' : |Work.Spaces.Dth f z θ| * |Work.Spaces.Dz f z θ|
      ≤ ((Work.Spaces.Dth f z θ) ^ 2 + (Work.Spaces.Dz f z θ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|Work.Spaces.Dth f z θ| - |Work.Spaces.Dz f z θ|),
      sq_abs (Work.Spaces.Dth f z θ), sq_abs (Work.Spaces.Dz f z θ)]
  have hkey : |Work.FTS.CoercivityFix.E2hat f z θ * Work.Spaces.Dz f z θ|
      ≤ f z θ ^ 2 / 4 + 5 * (Work.Spaces.Dz f z θ) ^ 2 / 8
        + 3 * (Work.Spaces.Dth f z θ) ^ 2 / 8 := by
    calc |Work.FTS.CoercivityFix.E2hat f z θ * Work.Spaces.Dz f z θ|
        = |Work.FTS.CoercivityFix.E2hat f z θ| * |Work.Spaces.Dz f z θ| := abs_mul _ _
      _ ≤ ((2 * |f z θ| + 3 * |Work.Spaces.Dth f z θ|) / 4) * |Work.Spaces.Dz f z θ| := by
          refine mul_le_mul_of_nonneg_right hE2 (abs_nonneg _)
      _ = (2 * |f z θ| * |Work.Spaces.Dz f z θ| / 4)
            + (3 * |Work.Spaces.Dth f z θ| * |Work.Spaces.Dz f z θ| / 4) := by ring
      _ ≤ (2 * ((f z θ ^ 2 + (Work.Spaces.Dz f z θ) ^ 2) / 2) / 4)
            + (3 * ((Work.Spaces.Dth f z θ) ^ 2 + (Work.Spaces.Dz f z θ) ^ 2) / 2 / 4) := by
          have e1 : 2 * |f z θ| * |Work.Spaces.Dz f z θ|
              = 2 * (|f z θ| * |Work.Spaces.Dz f z θ|) := by ring
          have e2 : 3 * |Work.Spaces.Dth f z θ| * |Work.Spaces.Dz f z θ|
              = 3 * (|Work.Spaces.Dth f z θ| * |Work.Spaces.Dz f z θ|) := by ring
          rw [e1, e2]
          have := mul_le_mul_of_nonneg_left h1' (show (0:ℝ) ≤ 2 by norm_num)
          have := mul_le_mul_of_nonneg_left h2' (show (0:ℝ) ≤ 3 by norm_num)
          linarith
      _ = f z θ ^ 2 / 4 + 5 * (Work.Spaces.Dz f z θ) ^ 2 / 8
            + 3 * (Work.Spaces.Dth f z θ) ^ 2 / 8 := by ring
  rw [abs_mul, abs_of_nonneg hρ]
  calc |Work.FTS.CoercivityFix.E2hat f z θ * Work.Spaces.Dz f z θ| * ρ z θ
      ≤ (f z θ ^ 2 / 4 + 5 * (Work.Spaces.Dz f z θ) ^ 2 / 8
          + 3 * (Work.Spaces.Dth f z θ) ^ 2 / 8) * ρ z θ :=
        mul_le_mul_of_nonneg_right hkey hρ
    _ = _ := rfl

/-- **The integrability bundle for `f ∈ RegQ α 2`.** -/
theorem IntPkg_Q (α : ℝ) (hα : 0 < α) {f : Fn} (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    IntPkg α f := by
  obtain ⟨hsq, hm, hb⟩ := hf
  have hsqE : ∀ i ≤ 2, MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := fun i hi => sq_DzEta α hsq hm i hi
  have hsqME : ∀ i j, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Rho Work.Spaces.eta z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    fun i j hi hij => sq_MixedEta α hα hsq hm i j hi hij
  have hsqMG : ∀ i j, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2
        * Rho (Work.Spaces.gam α) z θ)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    fun i j hi hij => sq_MixedGam α hα hsq hm i j hi hij
  have hsqO : ∀ i ≤ 2, MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.DzIter i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := fun i hi => sq_DzOne α hsq hm i hi
  have hsqMO : ∀ i j, 1 ≤ i → i + j ≤ 2 → MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (Work.Spaces.mixed j i f z θ) ^ 2 * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    fun i j hi hij => sq_MixedOne α hα hsq hm i j hi hij
  -- the `𝓛`-pairings
  have hLf_eta := intL_of hsq (continuousOn_Rho _) (Rho_nonneg _)
    (hsqE 0 (by norm_num)) (hsqE 1 (by norm_num))
  have hLDz_eta := intL_of (Work.FTS.LocData.SmoothQuad.DzIter hsq 1) (continuousOn_Rho _)
    (Rho_nonneg _) (hsqE 1 (by norm_num)) (hsqE 2 (by norm_num))
  have hLDth_gam := intL_of (Work.FTS.LocData.SmoothQuad.DthIter hsq 1) (continuousOn_Rho _)
    (Rho_nonneg _) (hsqMG 1 0 (by norm_num) (by norm_num))
    (hsqMG 1 1 (by norm_num) (by norm_num))
  have hLf_one := intL_of hsq continuousOn_w2 w2_nonneg
    (hsqO 0 (by norm_num)) (hsqO 1 (by norm_num))
  have hLDz_one := intL_of (Work.FTS.LocData.SmoothQuad.DzIter hsq 1) continuousOn_w2
    w2_nonneg (hsqO 1 (by norm_num)) (hsqO 2 (by norm_num))
  have hLDth_one := intL_of (Work.FTS.LocData.SmoothQuad.DthIter hsq 1) continuousOn_w2
    w2_nonneg (hsqMO 1 0 (by norm_num) (by norm_num))
    (hsqMO 1 1 (by norm_num) (by norm_num))
  -- the transport pairings
  have hintf_eta := intTr_of hsq (continuousOn_Rho _) (Rho_nonneg _)
    (hsqE 0 (by norm_num)) (hsqME 1 0 (by norm_num) (by norm_num))
  have hthDz : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      (Work.Spaces.Dth (Work.Spaces.Dz f) z θ) ^ 2 * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have hae : (Function.uncurry (fun z θ =>
          (Work.Spaces.mixed 1 1 f z θ) ^ 2 * Rho Work.Spaces.eta z θ))
        =ᵐ[MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)]
        (Function.uncurry (fun z θ =>
          (Work.Spaces.Dth (Work.Spaces.Dz f) z θ) ^ 2 * Rho Work.Spaces.eta z θ)) := by
      have h := ae_Dz_Dth_comm hsq
      rw [iz_prod_restrict] at h
      filter_upwards [h] with p hp
      show (Work.Spaces.Dz (Work.Spaces.Dth f) p.1 p.2) ^ 2 * Rho Work.Spaces.eta p.1 p.2
        = (Work.Spaces.Dth (Work.Spaces.Dz f) p.1 p.2) ^ 2 * Rho Work.Spaces.eta p.1 p.2
      rw [hp]
    exact (hsqME 1 1 (by norm_num) (by norm_num)).congr hae
  have hintDz_eta := intTr_of (Work.FTS.LocData.SmoothQuad.DzIter hsq 1) (continuousOn_Rho _)
    (Rho_nonneg _) (hsqE 1 (by norm_num)) hthDz
  have hintDth_gam := intTr_of (Work.FTS.LocData.SmoothQuad.DthIter hsq 1)
    (continuousOn_Rho _) (Rho_nonneg _) (hsqMG 1 0 (by norm_num) (by norm_num))
    (hsqMG 2 0 (by norm_num) (by norm_num))
  have hintf_one := intTr_of hsq continuousOn_w2 w2_nonneg
    (hsqO 0 (by norm_num)) (hsqMO 1 0 (by norm_num) (by norm_num))
  -- the `Lhat`-pairing and the `Ê₂`-pairing
  have hLhat := intLhat_of hLDz_eta (intTransport_of hintDz_eta)
  have hE2 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.FTS.CoercivityFix.E2hat f z θ
        * Work.Spaces.Dz f z θ * Rho Work.Spaces.eta z θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    refine intE2hat_of ?_ (Rho_nonneg _) (hsqE 0 (by norm_num)) (hsqE 1 (by norm_num))
      (hsqME 1 0 (by norm_num) (by norm_num))
    have hE2c : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2) Qd := by
      have hnum : ContinuousOn (fun p : ℝ × ℝ => 2 * p.1 * f p.1 p.2
          + 3 * p.1 * Work.Spaces.Dth f p.1 p.2) Qd :=
        (((continuousOn_const.mul continuousOn_fst).mul (continuousOn_f_Q hsq)).add
          ((continuousOn_const.mul continuousOn_fst).mul (continuousOn_mixed_Q hsq 0 1)))
      have hden : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2) Qd :=
        (continuousOn_const.add continuousOn_fst).pow 2
      have hfun : (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.E2hat f p.1 p.2)
          = fun p : ℝ × ℝ => (2 * p.1 * f p.1 p.2 + 3 * p.1 * Work.Spaces.Dth f p.1 p.2)
              / (1 + p.1) ^ 2 := by
        funext p; rfl
      rw [hfun]
      exact hnum.div hden (fun p hp => pow_ne_zero 2 (by
        intro hc
        have h1 : (0 : ℝ) < p.1 := hp.1
        linarith))
    exact (hE2c.mul (continuousOn_mixed_Q hsq 1 0)).mul (continuousOn_Rho _)
  -- the `z`-integration-by-parts packages
  have hasm0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 0 0 (by norm_num)).1 θ hθ).1
  have hasmT0 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (f z θ * Work.Spaces.w z) ^ 2) Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 0 0 (by norm_num)).1 θ hθ).2
  have hasm1 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 0 1 (by norm_num)).1 θ hθ).1
  have hasmT1 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 0 1 (by norm_num)).1 θ hθ).2
  have hasm2 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dth f z θ * Work.Spaces.w z) ^ 2)
        (𝓝[>] 0) (𝓝 0) :=
    fun θ hθ => ((hb 1 0 (by norm_num)).1 θ hθ).1
  have hasmT2 : ∀ θ ∈ Set.Ioo 0 (π / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.Dth f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (𝓝 0) :=
    fun θ hθ => ((hb 1 0 (by norm_num)).1 θ hθ).2
  refine ⟨hsqE, hsqME, hsqMG, hsqO, hsqMO, hLf_eta, hLDz_eta, hLDth_gam, hLf_one,
    hLhat, hE2, hintf_eta, hintDz_eta, hintDth_gam, hintf_one, ?_, ?_, ?_⟩
  · -- `ZIBP f`
    refine zibp_of hsq hasm0 hasmT0 ?_ hLf_one
    refine (hsqO 0 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
    ring
  · -- `ZIBP (D_z f)`
    refine zibp_of (Work.FTS.LocData.SmoothQuad.DzIter hsq 1) hasm1 hasmT1 ?_ hLDz_one
    refine (hsqO 1 (by norm_num)).congr (MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    ring
  · -- `ZIBP (D_θ f)`
    refine zibp_of (Work.FTS.LocData.SmoothQuad.DthIter hsq 1) hasm2 hasmT2 ?_ hLDth_one
    refine (hsqMO 1 0 (by norm_num) (by norm_num)).congr
      (MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ici.prod measurableSet_Icc) (fun p hp => ?_))
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
      Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
    ring

end Work.FTS.CoercivityFix.Coer1
