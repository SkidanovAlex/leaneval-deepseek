import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.H2.T2Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- The five order-`4` `g`-derivatives appearing in the "top" (order `5`) terms of the
pairing `(f D_z g, g)_{ℋ⁴}`: `D_z^4 g`, `D_z^3 D_θ g`, `D_z^2 D_θ^2 g`, `D_z D_θ^3 g`,
`D_θ^4 g`. -/
def Thard (g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  match k.val with
  | 0 => fun z θ => Spaces.mixed 4 0 g z θ
  | 1 => fun z θ => Spaces.mixed 3 1 g z θ
  | 2 => fun z θ => Spaces.mixed 2 2 g z θ
  | 3 => fun z θ => Spaces.mixed 1 3 g z θ
  | _ => fun z θ => Spaces.mixed 0 4 g z θ

/-- The angular weight of the top terms: `sin(2θ)^{-η}` for the `D_z`-slot (`k = 0`) and
`sin(2θ)^{-γ}` for the mixed slots (`k ≥ 1`). -/
def sghard (α : ℝ) (k : Fin 5) : ℝ → ℝ :=
  match k.val with
  | 0 => fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.eta))
  | _ => fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α))

/-- The "hard" part of the pairing integrand `H4PairInt α (f D_z g) g`: the five terms in
which all five derivatives fall on `g`. -/
def Hhard (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  f z θ * z * (∑ k : Fin 5, Spaces.pz (Thard g k) z θ * Thard g k z θ
    * (Spaces.w z) ^ 2 * sghard α k θ)

/-- The "easy" part of the pairing integrand: everything except the five order-five terms. -/
def Heasy (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  H4PairInt α (fun z θ => f z θ * Spaces.Dz g z θ) g z θ - Hhard α f g z θ


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.Spaces.CurrySmooth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The `z`-partial derivative is the Fréchet derivative in the direction `(1,0)`. -/
theorem pz_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    pz G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (1, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact (h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv

/-- The `θ`-partial derivative is the Fréchet derivative in the direction `(0,1)`. -/
theorem pth_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    pth G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (0, 1) := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  exact (h.hasFDerivAt.comp_hasDerivAt θ hcurve).deriv

theorem differentiableAt_curry_left {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    DifferentiableAt ℝ (fun z' => G z' θ) z := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact (h.hasFDerivAt.comp_hasDerivAt z hcurve).differentiableAt

theorem differentiableAt_curry_right {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    DifferentiableAt ℝ (fun θ' => G z θ') θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  exact (h.hasFDerivAt.comp_hasDerivAt θ hcurve).differentiableAt

/-- The `z`-partial of a function smooth on an open set is smooth on that set. -/
theorem contDiffOn_uncurry_pz {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (pz G)) V := by
  have hchain : ∀ p ∈ V, pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact pz_eq_fderiv ((h.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ⊤ (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := ⊤) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ ⊤
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- The `θ`-partial of a function smooth on an open set is smooth on that set. -/
theorem contDiffOn_uncurry_pth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (pth G)) V := by
  have hchain : ∀ p ∈ V, pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact pth_eq_fderiv ((h.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ⊤ (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := ⊤) hV.uniqueDiffOn le_rfl
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ ⊤
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.DthIter_contDiffAt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

/-- `D_θ` preserves `C^∞`-regularity at a point. -/
theorem Dth_contDiffAt {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hg : ContDiffAt ℝ ⊤ (Function.uncurry g) (z, θ)) :
    ContDiffAt ℝ ⊤ (Function.uncurry (Dth g)) (z, θ) := by
  have h1 : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (z, θ) := by
    fun_prop
  have h2 := contDiffAt_deriv_slice hg
  exact h1.mul h2

/-- Every iterate of `D_θ` preserves `C^∞`-regularity at a point. -/
theorem DthIter_contDiffAt (f : ℝ → ℝ → ℝ) (j : ℕ) {z θ : ℝ}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter j f)) (z, θ) := by
  induction j with
  | zero => simpa using h
  | succ n ih => simpa using Dth_contDiffAt ih

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.HardyTheta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Elementary `rpow` identities -/

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

/-- `x ^ ((2 - γ)/2) * x ^ ((γ - 2)/2) = 1` for `x > 0`. -/
private lemma rpow_half_mul_half (x γ : ℝ) (hx : 0 < x) :
    x ^ ((2 - γ) / 2) * x ^ ((γ - 2) / 2) = 1 := by
  rw [← Real.rpow_add hx, show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero]

/-! ## The core Hardy inequality on the angular interval -/

/-- If `h` is continuous on `[0,θ] ⊆ [0,π/2]` and `h(s)² sin(2s)^{2-γ}` is integrable on
`[0,π/2]`, then `(∫₀^θ h)² ≤ (∫_Iθ h² sin(2s)^{2-γ}) · 100/(γ-1)`.

This is the Cauchy–Schwarz / Hardy step: split `h = (h sin^{(2-γ)/2}) · sin^{(γ-2)/2}`,
square the Hölder inequality and control the singular weight by `sin_two_rpow`. -/
private theorem core (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (h : ℝ → ℝ) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ π / 2)
    (hcont : ContinuousOn h (Set.Icc 0 θ))
    (hint : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) Iθ) :
    (∫ s in (0 : ℝ)..θ, h s) ^ 2 ≤
      (∫ s in Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) * (100 / (gam α - 1)) := by
  have hγ1 : 1 < gam α := one_lt_gam hα
  have hγ2 : gam α ≤ 11 / 10 := by rw [gam]; linarith
  have hp1 : -1 < gam α - 2 := by linarith
  have hp0 : gam α - 2 ≤ 0 := by linarith
  -- positivity of sin(2·) on (0,θ), nonnegativity on Iθ
  have hsinpos : ∀ s ∈ Set.Ioo (0 : ℝ) θ, 0 < Real.sin (2 * s) := by
    intro s hs
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) ?_
    linarith [hs.2, hθ1, Real.pi_pos]
  have hsinIθ : ∀ x ∈ Iθ, 0 ≤ Real.sin (2 * x) := by
    intro x hx
    have h1 : 0 ≤ 2 * x := by linarith [hx.1]
    have h2 : 2 * x ≤ Real.pi := by linarith [hx.2, Real.pi_pos]
    exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2
  have hsub : Set.Ioo (0 : ℝ) θ ⊆ Iθ := by
    intro x hx
    simp only [Iθ, Set.mem_Icc]
    exact ⟨le_of_lt hx.1, le_trans hx.2.le hθ1⟩
  have hae_sub : Set.Ioo (0 : ℝ) θ ≤ᵐ[volume] Iθ :=
    Filter.Eventually.of_forall (fun x hx => hsub hx)
  have hmIθ : MeasurableSet Iθ := by
    simp only [Iθ]
    exact measurableSet_Icc
  have hFnn : 0 ≤ᵐ[volume.restrict Iθ]
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) :=
    (MeasureTheory.ae_restrict_iff' hmIθ).2
      (Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIθ x hx) _))
  have hSnn : 0 ≤ᵐ[volume.restrict Iθ] (fun s => (Real.sin (2 * s)) ^ (gam α - 2)) :=
    (MeasureTheory.ae_restrict_iff' hmIθ).2
      (Filter.Eventually.of_forall fun x hx => Real.rpow_nonneg (hsinIθ x hx) _)
  -- integrability of the integrand over (0,θ)
  have hIntF : MeasureTheory.IntegrableOn
      (fun s => (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) (Set.Ioo (0 : ℝ) θ) :=
    hint.mono_set hsub
  -- measurability of the two Cauchy–Schwarz factors
  have hcont_sin : ContinuousOn (fun s : ℝ => Real.sin (2 * s)) (Set.Ioo (0 : ℝ) θ) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hsm_h : AEMeasurable h (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (hcont.mono Set.Ioo_subset_Icc_self).aemeasurable measurableSet_Ioo
  have hsm_s : AEMeasurable (fun s : ℝ => (Real.sin (2 * s)) ^ ((2 - gam α) / 2))
      (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (hcont_sin.rpow_const fun x hx => Or.inl (ne_of_gt (hsinpos x hx))).aemeasurable
      measurableSet_Ioo
  have hsm_s2 : AEMeasurable (fun s : ℝ => (Real.sin (2 * s)) ^ ((gam α - 2) / 2))
      (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (hcont_sin.rpow_const fun x hx => Or.inl (ne_of_gt (hsinpos x hx))).aemeasurable
      measurableSet_Ioo
  -- the integrability of the two squares
  have eq_v2 : Set.EqOn
      (fun x => ((Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2)
      (fun x => (Real.sin (2 * x)) ^ (gam α - 2)) (Set.Ioo (0 : ℝ) θ) := by
    intro x hx
    dsimp only
    rw [rpow_sq _ _ (hsinpos x hx), show 2 * ((gam α - 2) / 2) = gam α - 2 by ring]
  have eq_u2 : Set.EqOn
      (fun x => (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) ^ 2)
      (fun x => (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α)) (Set.Ioo (0 : ℝ) θ) := by
    intro x hx
    dsimp only
    rw [mul_pow, rpow_sq _ _ (hsinpos x hx), show 2 * ((2 - gam α) / 2) = 2 - gam α by ring]
  have hInt_v2 : MeasureTheory.IntegrableOn
      (fun x => ((Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2) (Set.Ioo (0 : ℝ) θ) :=
    ((sin_two_rpow (gam α - 2) hp1 hp0).1.mono_set hsub).congr_fun eq_v2.symm
      measurableSet_Ioo
  have hInt_u2 : MeasureTheory.IntegrableOn
      (fun x => (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) ^ 2) (Set.Ioo (0 : ℝ) θ) :=
    hIntF.congr_fun eq_u2.symm measurableSet_Ioo
  have hu_mem : MeasureTheory.MemLp
      (fun x => h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) 2
      (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hsm_h.mul hsm_s).aestronglyMeasurable).2 hInt_u2
  have hv_mem : MeasureTheory.MemLp (fun x => (Real.sin (2 * x)) ^ ((gam α - 2) / 2)) 2
      (volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hsm_s2.aestronglyMeasurable).2 hInt_v2
  have hcs := cs_integral hu_mem hv_mem
  -- identify the three integrals
  have e1 : (∫ x in Set.Ioo (0 : ℝ) θ,
        (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) * (Real.sin (2 * x)) ^ ((gam α - 2) / 2))
      = ∫ x in Set.Ioo (0 : ℝ) θ, h x := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_assoc, rpow_half_mul_half _ _ (hsinpos x hx), mul_one]
  have e2 : (∫ x in Set.Ioo (0 : ℝ) θ,
        (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [mul_pow, rpow_sq _ _ (hsinpos x hx), show 2 * ((2 - gam α) / 2) = 2 - gam α by ring]
  have e3 : (∫ x in Set.Ioo (0 : ℝ) θ, ((Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    rw [rpow_sq _ _ (hsinpos x hx), show 2 * ((gam α - 2) / 2) = gam α - 2 by ring]
  have key : (∫ x in Set.Ioo (0 : ℝ) θ, h x) ^ 2 ≤
      (∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α))
        * (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2)) := by
    calc (∫ x in Set.Ioo (0 : ℝ) θ, h x) ^ 2
        = (∫ x in Set.Ioo (0 : ℝ) θ,
            (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2))
              * (Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2 := by rw [e1]
      _ ≤ (∫ x in Set.Ioo (0 : ℝ) θ, (h x * (Real.sin (2 * x)) ^ ((2 - gam α) / 2)) ^ 2)
            * (∫ x in Set.Ioo (0 : ℝ) θ,
                ((Real.sin (2 * x)) ^ ((gam α - 2) / 2)) ^ 2) := hcs
      _ = (∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α))
            * (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2)) := by rw [e2, e3]
  -- the monotonicity and the explicit bound for the weight
  have hA : (∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α))
      ≤ ∫ s in Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) :=
    MeasureTheory.setIntegral_mono_set hint hFnn hae_sub
  have hB : (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2))
      ≤ 100 / (gam α - 1) := by
    have h1 : (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2))
        ≤ ∫ s in Iθ, (Real.sin (2 * s)) ^ (gam α - 2) :=
      MeasureTheory.setIntegral_mono_set (sin_two_rpow (gam α - 2) hp1 hp0).1 hSnn hae_sub
    have h2 : (∫ s in Iθ, (Real.sin (2 * s)) ^ (gam α - 2))
        ≤ 100 / ((gam α - 2) + 1) := (sin_two_rpow (gam α - 2) hp1 hp0).2
    have h3 : 100 / ((gam α - 2) + 1) = 100 / (gam α - 1) := by ring_nf
    exact h1.trans (h2.trans (le_of_eq h3))
  have hA0 : 0 ≤ ∫ s in Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) :=
    MeasureTheory.setIntegral_nonneg hmIθ
      (fun x hx => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIθ x hx) _))
  have hB0 : 0 ≤ ∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun x hx => Real.rpow_nonneg (hsinIθ x (hsub hx)) _)
  have hIoo : (∫ x in Set.Ioo (0 : ℝ) θ, h x) = ∫ s in (0 : ℝ)..θ, h s := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hθ0]
  calc (∫ s in (0 : ℝ)..θ, h s) ^ 2
      = (∫ x in Set.Ioo (0 : ℝ) θ, h x) ^ 2 := by rw [hIoo]
    _ ≤ (∫ x in Set.Ioo (0 : ℝ) θ, (h x) ^ 2 * (Real.sin (2 * x)) ^ (2 - gam α))
          * (∫ x in Set.Ioo (0 : ℝ) θ, (Real.sin (2 * x)) ^ (gam α - 2)) := key
    _ ≤ (∫ s in Iθ, (h s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α)) * (100 / (gam α - 1)) :=
        mul_le_mul hA hB hB0 hA0


theorem HardyTheta (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ) (z : ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hz : 0 ≤ z) (h0 : g z 0 = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (g z θ) ^ 2 ≤
      (100 / (Work.Spaces.gam α - 1)) * ∫ s in Work.Spaces.Iθ,
        (Work.Spaces.pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - Work.Spaces.gam α) := by
  intro θ hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hpth := pth_integral g z hsm hz θ ⟨hθ0, hθ1⟩
  have hFTC : (∫ s in (0 : ℝ)..θ, pth g z s) = g z θ := by
    rw [hpth.1, h0, sub_zero]
  have hmain := core α hα hα1 (fun s => pth g z s) θ hθ0 hθ1 hpth.2 hint
  rw [hFTC] at hmain
  calc (g z θ) ^ 2
      ≤ (∫ s in Iθ, (pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α))
          * (100 / (gam α - 1)) := hmain
    _ = (100 / (gam α - 1)) * ∫ s in Iθ,
          (pth g z s) ^ 2 * (Real.sin (2 * s)) ^ (2 - gam α) := by ring

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.HkMem_mixed_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false
private lemma DzIter_add_hkm (i b : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter (i + b) f = DzIter i (DzIter b f) := by
  induction i with
  | zero => simp
  | succ n ih => rw [Nat.succ_add, DzIter_succ, ih, DzIter_succ]

/-- `DzIter` passes through `mixed` on the left. -/
private lemma DzIter_mixed_hkm (i b a : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter i (mixed b a f) = mixed (i + b) a f := by
  simp only [mixed]; rw [DzIter_add_hkm]

/-- Pointwise domination of the `H²`-integrand of `mixed b a g` by the `H⁴`-integrand of `g`,
for `a + b ≤ 2`.  Each term of the former is (a square whose base is) a weighted mixed
derivative of `g` of total order `≤ 4`; the index sets match up and the weights are dominated. -/
private lemma HkIntegrand_mixed_le_aux (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd g) (b a : ℕ) (hab : a + b ≤ 2) (z θ : ℝ) (hz : z ∈ Iz)
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 2 (mixed b a g) z θ ≤ HkIntegrand α 4 g z θ := by
  have hb2 : b ≤ 2 := by omega
  have ha2 : a ≤ 2 := by omega
  set H : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2) with hH
  set W : ℝ := Wt α z θ with hW
  -- Index convention: a pair `x = (p, q)` records `p = D_θ`-order and `q = D_z`-order.
  set T : ℕ × ℕ → ℝ := fun x =>
    if x.1 = 0 then (DzIter x.2 g z θ * H) ^ 2 else (mixed x.2 x.1 g z θ * W) ^ 2 with hT
  set S1 : Finset (ℕ × ℕ) := (Finset.range 3).image (fun i => (a, i + b)) with hS1def
  set S2 : Finset (ℕ × ℕ) := ((Finset.range 3 ×ˢ Finset.range 3).filter
      (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2)).image (fun x => (x.1 + a, x.2 + b))
    with hS2def
  set R1 : Finset (ℕ × ℕ) := (Finset.range 5).image (fun q => ((0 : ℕ), q)) with hR1def
  set R2 : Finset (ℕ × ℕ) := (Finset.range 5 ×ˢ Finset.range 5).filter
      (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 4) with hR2def
  have hTnn : ∀ x, 0 ≤ T x := by
    rintro ⟨x1, x2⟩; simp only [hT]; split <;> exact sq_nonneg _
  -- The first sum of `HkIntegrand α 4 g` sits on the index set `R1`.
  have hR1 : (∑ x ∈ R1, T x) = ∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2 := by
    rw [hR1def]
    have hinj : Set.InjOn (fun q : ℕ => ((0 : ℕ), q)) (↑(Finset.range 5) : Set ℕ) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image (f := T) hinj]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp only [hT]; simp
  -- The second sum of `HkIntegrand α 4 g` sits on the index set `R2`.
  have hR2 : (∑ x ∈ R2, T x)
      = ∑ p ∈ Finset.range 5, ∑ q ∈ Finset.range 5,
          (if 1 ≤ p ∧ p + q ≤ 4 then (mixed q p g z θ * W) ^ 2 else 0) := by
    rw [hR2def, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    simp only [hT]
    by_cases hc : 1 ≤ p ∧ p + q ≤ 4
    · rw [if_pos hc, if_pos hc, if_neg (by omega : ¬ p = 0)]
    · rw [if_neg hc, if_neg hc]
  -- The first sum of `HkIntegrand α 2 (mixed b a g)` is dominated on `S1`.
  have hS1 : (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2) ≤ ∑ x ∈ S1, T x := by
    rw [hS1def]
    have hinj : Set.InjOn (fun i : ℕ => (a, i + b)) (↑(Finset.range 3) : Set ℕ) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image (f := T) hinj]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [DzIter_mixed_hkm i b a g]
    simp only [hT]
    by_cases ha : a = 0
    · subst ha; rw [if_pos rfl]; simp [mixed]
    · rw [if_neg ha]
      have hHW : H ^ 2 ≤ W ^ 2 := by rw [hH, hW]; exact H_le_Wt α hα z θ hz hθ
      nlinarith [hHW, sq_nonneg (mixed (i + b) a g z θ)]
  -- The second sum of `HkIntegrand α 2 (mixed b a g)` equals the sum on `S2`.
  have hS2a : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      = ∑ x ∈ (Finset.range 3 ×ˢ Finset.range 3).filter
            (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2),
          T (x.1 + a, x.2 + b) := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp only
    by_cases hc : 1 ≤ i ∧ i + j ≤ 2
    · rw [if_pos hc, if_pos hc]
      simp only [hT]
      rw [if_neg (by omega : ¬ i + a = 0)]
      rw [mixed_comm g hsm j i b a z θ hz hθ]
    · rw [if_neg hc, if_neg hc]
  have hS2b : (∑ x ∈ (Finset.range 3 ×ˢ Finset.range 3).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2), T (x.1 + a, x.2 + b))
      = ∑ x ∈ S2, T x := by
    rw [hS2def]
    have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.1 + a, x.2 + b))
        (↑((Finset.range 3 ×ˢ Finset.range 3).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2)) : Set (ℕ × ℕ)) := by
      intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.add_right_cancel h.1) (Nat.add_right_cancel h.2)
    rw [Finset.sum_image (f := T) hinj]
  have hS2 : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      = ∑ x ∈ S2, T x := hS2a.trans hS2b
  -- `S1` and `S2` are disjoint, and so are `R1` and `R2`.
  have hdisjS : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hS1def, Finset.mem_image] at hx1
    obtain ⟨i, _, rfl⟩ := hx1
    rw [hS2def, Finset.mem_image] at hx2
    obtain ⟨y, hy, hxy⟩ := hx2
    rw [Finset.mem_filter] at hy
    simp only [Prod.mk.injEq] at hxy
    have hy1 : 1 ≤ y.1 := hy.2.1
    omega
  have hdisjR : Disjoint R1 R2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hR1def, Finset.mem_image] at hx1
    obtain ⟨q, _, rfl⟩ := hx1
    rw [hR2def, Finset.mem_filter] at hx2
    have h := hx2.2.1
    simp only [] at h
    omega
  -- Every index of `S1 ∪ S2` is an index of `R1 ∪ R2`.
  have hsub : S1 ∪ S2 ⊆ R1 ∪ R2 := by
    intro x hx
    rw [Finset.mem_union] at hx ⊢
    rcases hx with hx | hx
    · rw [hS1def, Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.mem_range] at hi
      by_cases ha : a = 0
      · left
        rw [hR1def, Finset.mem_image]
        exact ⟨i + b, by rw [Finset.mem_range]; omega, by simp [ha]⟩
      · right
        rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        dsimp only
        refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rw [hS2def, Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
      right
      rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      dsimp only
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  have hLHSunfold : HkIntegrand α 2 (mixed b a g) z θ
      = (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0) := by
    simp [HkIntegrand, ← hH, ← hW]
  have hRHSunfold : HkIntegrand α 4 g z θ
      = (∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * W) ^ 2 else 0) := by
    simp [HkIntegrand, ← hH, ← hW]
  have hstep1 : (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      ≤ ∑ x ∈ S1 ∪ S2, T x := by
    rw [hS2, Finset.sum_union hdisjS]
    linarith [hS1]
  have hstep2 : (∑ x ∈ S1 ∪ S2, T x)
      ≤ (∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * W) ^ 2 else 0) := by
    rw [← hR1, ← hR2, ← Finset.sum_union hdisjR]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hTnn x)
  rw [hLHSunfold, hRHSunfold]
  exact le_trans hstep1 hstep2


/-! ## The open set on which joint continuity holds -/

/-- The open set `(0,∞) × (0,π/2)` on which the integrand is jointly continuous. -/
private def U_prv : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)

private lemma isOpen_U_prv : IsOpen U_prv := isOpen_Ioi.prod isOpen_Ioo

private lemma U_subset_nbhU : U_prv ⊆ nbhU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))

/-- `sin (2θ)` is positive for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) : 0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-! ## Continuity of the individual weight factors -/

private lemma contOn_slice_sinpow (p : ℝ) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Ioo 0 (π/2)) :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
    (fun θ hθ => Or.inl (ne_of_gt (sin_two_pos hθ)))

private lemma contOn_slice_H (z : ℝ) :
    ContinuousOn (fun θ : ℝ => w z / (Real.sin (2 * θ)) ^ (eta / 2)) (Set.Ioo 0 (π/2)) :=
  continuousOn_const.div (contOn_slice_sinpow (eta / 2))
    (fun θ hθ => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos hθ) _))

private lemma contOn_slice_Wt (α z : ℝ) :
    ContinuousOn (fun θ : ℝ => Wt α z θ) (Set.Ioo 0 (π/2)) := by
  simp only [Wt, wTheta]
  exact continuousOn_const.mul (contOn_slice_sinpow (-(gam α / 2)))

private lemma contOn_uncurry_sinpow (p : ℝ) :
    ContinuousOn (fun y : ℝ × ℝ => (Real.sin (2 * y.2)) ^ p) U_prv :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun y hy => Or.inl (ne_of_gt (sin_two_pos hy.2)))

private lemma contOn_uncurry_w : ContinuousOn (fun y : ℝ × ℝ => w y.1) U_prv := by
  simp only [w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun y hy => ?_)
  exact pow_ne_zero 2 (ne_of_gt hy.1)

private lemma contOn_uncurry_H :
    ContinuousOn (fun y : ℝ × ℝ => w y.1 / (Real.sin (2 * y.2)) ^ (eta / 2)) U_prv :=
  contOn_uncurry_w.div (contOn_uncurry_sinpow (eta / 2))
    (fun y hy => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos hy.2) _))

private lemma contOn_uncurry_Wt (α : ℝ) :
    ContinuousOn (fun y : ℝ × ℝ => Wt α y.1 y.2) U_prv := by
  simp only [Wt, wTheta]
  exact contOn_uncurry_w.mul (contOn_uncurry_sinpow (-(gam α / 2)))

/-! ## Continuity of the slices of an iterated derivative, and of the integrand -/

private lemma contOn_slice {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) {z : ℝ} (hz : z ∈ Iz) :
    ContinuousOn (fun θ : ℝ => f z θ) (Set.Ioo 0 (π/2)) := by
  have hz' : (-1 : ℝ) < z := by rw [Iz, Set.mem_Ici] at hz; linarith
  have hpair : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Ioo (-1) (π / 2 + 1)) := by
    fun_prop
  have hmaps : MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo (-1) (π / 2 + 1)) nbhU :=
    fun θ hθ => ⟨hz', hθ⟩
  exact (h.comp hpair hmaps).continuousOn.mono
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))

private lemma contOn_uncurry {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ContinuousOn (fun y : ℝ × ℝ => f y.1 y.2) U_prv := h.continuousOn.mono U_subset_nbhU

private lemma contOn_slice_HkIntegrand (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f)
    {z : ℝ} (hz : z ∈ Iz) :
    ContinuousOn (fun θ : ℝ => HkIntegrand α k f z θ) (Set.Ioo 0 (π/2)) := by
  simp only [HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · apply continuousOn_finsetSum
    intro i _
    exact ((contOn_slice (SmoothNbhd.DzIter h i) hz).mul (contOn_slice_H z)).pow 2
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    split_ifs with hc
    · exact ((contOn_slice (SmoothNbhd.DzIter (SmoothNbhd.DthIter h i) j) hz).mul
        (contOn_slice_Wt α z)).pow 2
    · exact continuousOn_const

private lemma contOn_uncurry_HkIntegrand (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ContinuousOn (fun y : ℝ × ℝ => HkIntegrand α k f y.1 y.2) U_prv := by
  simp only [HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · apply continuousOn_finsetSum
    intro i _
    exact ((contOn_uncurry (SmoothNbhd.DzIter h i)).mul contOn_uncurry_H).pow 2
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    split_ifs with hc
    · exact ((contOn_uncurry (SmoothNbhd.DzIter (SmoothNbhd.DthIter h i) j)).mul
        (contOn_uncurry_Wt α)).pow 2
    · exact continuousOn_const

/-! ## The half-open intervals have the same measure as their interiors -/

private lemma measurableSet_Iz : MeasurableSet Iz := measurableSet_Ici
private lemma measurableSet_Iθ : MeasurableSet Iθ := measurableSet_Icc

private lemma restrict_Iz_eq : volume.restrict Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Iz : Set ℝ) = Set.Ici 0 from rfl, Set.Ici_sdiff_Ioi, Set.Icc_self]
    exact measure_singleton 0
  · rw [show (Iz : Set ℝ) = Set.Ici 0 from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioi_subset_Ici_self, measure_empty]

private lemma restrict_Iθ_eq : volume.restrict Iθ = volume.restrict (Set.Ioo 0 (π/2)) := by
  apply Measure.restrict_congr_set
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [show (Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.Icc_sdiff_Ioo_same (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)]
    rw [Set.insert_eq]
    exact measure_union_null (measure_singleton 0) (measure_singleton _)
  · rw [show (Iθ : Set ℝ) = Set.Icc 0 (π/2) from rfl,
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, measure_empty]

/-! ## Measurability of the integrand -/

private lemma aestronglyMeasurable_slice (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f)
    {z : ℝ} (hz : z ∈ Iz) :
    AEStronglyMeasurable (fun θ : ℝ => HkIntegrand α k f z θ) (volume.restrict Iθ) := by
  have hmeas : AEMeasurable (fun θ : ℝ => HkIntegrand α k f z θ)
      (volume.restrict (Set.Ioo 0 (π/2))) :=
    (contOn_slice_HkIntegrand α k h hz).aemeasurable isOpen_Ioo.measurableSet
  rw [restrict_Iθ_eq]
  exact hmeas.aestronglyMeasurable

private lemma aestronglyMeasurable_uncurry (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    AEStronglyMeasurable (fun y : ℝ × ℝ => HkIntegrand α k f y.1 y.2)
      ((volume.restrict Iz).prod (volume.restrict Iθ)) := by
  rw [restrict_Iz_eq, restrict_Iθ_eq]
  have hUc : ((volume.restrict (Set.Ioi (0 : ℝ))).prod
      (volume.restrict (Set.Ioo 0 (π/2)))) U_prvᶜ = 0 := by
    rw [Measure.prod_restrict, Measure.restrict_apply (isOpen_U_prv.measurableSet.compl)]
    change (volume.prod volume) (U_prvᶜ ∩ U_prv) = 0
    rw [Set.compl_inter_self, measure_empty]
  have hae : ∀ᵐ y ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod
      (volume.restrict (Set.Ioo 0 (π/2)))), y ∈ U_prv := by
    rw [ae_iff]
    exact hUc
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  exact (contOn_uncurry_HkIntegrand α k h).aestronglyMeasurable isOpen_U_prv.measurableSet

/-! ## Assembly: `HkMem` transfers from `g` to its mixed derivatives -/

theorem HkMem_mixed_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g)
    (b a : ℕ) (hab : a + b ≤ 2) :
    Work.Spaces.HkMem α 2 (Work.Spaces.mixed b a g) := by
  have hsm' : SmoothNbhd (mixed b a g) := SmoothNbhd.DzIter (SmoothNbhd.DthIter hsm a) b
  have hle : ∀ z ∈ Iz, ∀ θ ∈ Iθ,
      HkIntegrand α 2 (mixed b a g) z θ ≤ HkIntegrand α 4 g z θ :=
    fun z hz θ hθ => HkIntegrand_mixed_le_aux α hα g hsm b a hab z θ hz hθ
  have hslice : ∀ z ∈ Iz, AEStronglyMeasurable
      (fun θ : ℝ => HkIntegrand α 2 (mixed b a g) z θ) (volume.restrict Iθ) :=
    fun z hz => aestronglyMeasurable_slice α 2 hsm' hz
  constructor
  · intro z hz
    refine Integrable.mono' (hmem.1 z hz) (hslice z hz) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iθ] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (HkIntegrand_nonneg α 2 (mixed b a g) z θ)]
    exact hle z hz θ hθ
  · refine Integrable.mono' hmem.2
      (aestronglyMeasurable_uncurry α 2 hsm').integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Iz] with z hz
    have hnn : 0 ≤ ∫ θ in Iθ, HkIntegrand α 2 (mixed b a g) z θ :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Iθ
        (fun θ _ => HkIntegrand_nonneg α 2 (mixed b a g) z θ))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact integral_mono_of_nonneg
      (ae_restrict_of_forall_mem measurableSet_Iθ
        (fun θ _ => HkIntegrand_nonneg α 2 (mixed b a g) z θ))
      (hmem.1 z hz)
      (ae_restrict_of_forall_mem measurableSet_Iθ (fun θ hθ => hle z hz θ hθ))

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.HkSq_mixed_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- Composition of iterates of `D_z`. -/
private lemma DzIter_add_hk (i b : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter (i + b) f = DzIter i (DzIter b f) := by
  induction i with
  | zero => simp
  | succ n ih => rw [Nat.succ_add, DzIter_succ, ih, DzIter_succ]

/-- `DzIter` passes through `mixed` on the left. -/
private lemma DzIter_mixed_hk (i b a : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter i (mixed b a f) = mixed (i + b) a f := by
  simp only [mixed]; rw [DzIter_add_hk]

/-- Pointwise domination of the `H²`-integrand of `mixed b a g` by the `H⁴`-integrand of `g`,
for `a + b ≤ 2`.  Each term of the former is (a square whose base is) a weighted mixed
derivative of `g` of total order `≤ 4`; the index sets match up and the weights are dominated. -/
private lemma HkIntegrand_mixed_le (α : ℝ) (hα : 0 < α) (g : ℝ → ℝ → ℝ)
    (hsm : SmoothNbhd g) (b a : ℕ) (hab : a + b ≤ 2) (z θ : ℝ) (hz : z ∈ Iz)
    (hθ : θ ∈ Iθ) :
    HkIntegrand α 2 (mixed b a g) z θ ≤ HkIntegrand α 4 g z θ := by
  have hb2 : b ≤ 2 := by omega
  have ha2 : a ≤ 2 := by omega
  set H : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2) with hH
  set W : ℝ := Wt α z θ with hW
  -- Index convention: a pair `x = (p, q)` records `p = D_θ`-order and `q = D_z`-order.
  set T : ℕ × ℕ → ℝ := fun x =>
    if x.1 = 0 then (DzIter x.2 g z θ * H) ^ 2 else (mixed x.2 x.1 g z θ * W) ^ 2 with hT
  set S1 : Finset (ℕ × ℕ) := (Finset.range 3).image (fun i => (a, i + b)) with hS1def
  set S2 : Finset (ℕ × ℕ) := ((Finset.range 3 ×ˢ Finset.range 3).filter
      (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2)).image (fun x => (x.1 + a, x.2 + b))
    with hS2def
  set R1 : Finset (ℕ × ℕ) := (Finset.range 5).image (fun q => ((0 : ℕ), q)) with hR1def
  set R2 : Finset (ℕ × ℕ) := (Finset.range 5 ×ˢ Finset.range 5).filter
      (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 4) with hR2def
  have hTnn : ∀ x, 0 ≤ T x := by
    rintro ⟨x1, x2⟩; simp only [hT]; split <;> exact sq_nonneg _
  -- The first sum of `HkIntegrand α 4 g` sits on the index set `R1`.
  have hR1 : (∑ x ∈ R1, T x) = ∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2 := by
    rw [hR1def]
    have hinj : Set.InjOn (fun q : ℕ => ((0 : ℕ), q)) (↑(Finset.range 5) : Set ℕ) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image (f := T) hinj]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    simp only [hT]; simp
  -- The second sum of `HkIntegrand α 4 g` sits on the index set `R2`.
  have hR2 : (∑ x ∈ R2, T x)
      = ∑ p ∈ Finset.range 5, ∑ q ∈ Finset.range 5,
          (if 1 ≤ p ∧ p + q ≤ 4 then (mixed q p g z θ * W) ^ 2 else 0) := by
    rw [hR2def, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    simp only [hT]
    by_cases hc : 1 ≤ p ∧ p + q ≤ 4
    · rw [if_pos hc, if_pos hc, if_neg (by omega : ¬ p = 0)]
    · rw [if_neg hc, if_neg hc]
  -- The first sum of `HkIntegrand α 2 (mixed b a g)` is dominated on `S1`.
  have hS1 : (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2) ≤ ∑ x ∈ S1, T x := by
    rw [hS1def]
    have hinj : Set.InjOn (fun i : ℕ => (a, i + b)) (↑(Finset.range 3) : Set ℕ) := by
      intro x _ y _ h; simpa using h
    rw [Finset.sum_image (f := T) hinj]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [DzIter_mixed_hk i b a g]
    simp only [hT]
    by_cases ha : a = 0
    · subst ha; rw [if_pos rfl]; simp [mixed]
    · rw [if_neg ha]
      have hHW : H ^ 2 ≤ W ^ 2 := by rw [hH, hW]; exact H_le_Wt α hα z θ hz hθ
      nlinarith [hHW, sq_nonneg (mixed (i + b) a g z θ)]
  -- The second sum of `HkIntegrand α 2 (mixed b a g)` equals the sum on `S2`.
  have hS2a : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      = ∑ x ∈ (Finset.range 3 ×ˢ Finset.range 3).filter
            (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2),
          T (x.1 + a, x.2 + b) := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp only
    by_cases hc : 1 ≤ i ∧ i + j ≤ 2
    · rw [if_pos hc, if_pos hc]
      simp only [hT]
      rw [if_neg (by omega : ¬ i + a = 0)]
      rw [mixed_comm g hsm j i b a z θ hz hθ]
    · rw [if_neg hc, if_neg hc]
  have hS2b : (∑ x ∈ (Finset.range 3 ×ˢ Finset.range 3).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2), T (x.1 + a, x.2 + b))
      = ∑ x ∈ S2, T x := by
    rw [hS2def]
    have hinj : Set.InjOn (fun x : ℕ × ℕ => (x.1 + a, x.2 + b))
        (↑((Finset.range 3 ×ˢ Finset.range 3).filter
          (fun x : ℕ × ℕ => 1 ≤ x.1 ∧ x.1 + x.2 ≤ 2)) : Set (ℕ × ℕ)) := by
      intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.add_right_cancel h.1) (Nat.add_right_cancel h.2)
    rw [Finset.sum_image (f := T) hinj]
  have hS2 : (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
        (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      = ∑ x ∈ S2, T x := hS2a.trans hS2b
  -- `S1` and `S2` are disjoint, and so are `R1` and `R2`.
  have hdisjS : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hS1def, Finset.mem_image] at hx1
    obtain ⟨i, _, rfl⟩ := hx1
    rw [hS2def, Finset.mem_image] at hx2
    obtain ⟨y, hy, hxy⟩ := hx2
    rw [Finset.mem_filter] at hy
    simp only [Prod.mk.injEq] at hxy
    have hy1 : 1 ≤ y.1 := hy.2.1
    omega
  have hdisjR : Disjoint R1 R2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [hR1def, Finset.mem_image] at hx1
    obtain ⟨q, _, rfl⟩ := hx1
    rw [hR2def, Finset.mem_filter] at hx2
    have h := hx2.2.1
    simp only [] at h
    omega
  -- Every index of `S1 ∪ S2` is an index of `R1 ∪ R2`.
  have hsub : S1 ∪ S2 ⊆ R1 ∪ R2 := by
    intro x hx
    rw [Finset.mem_union] at hx ⊢
    rcases hx with hx | hx
    · rw [hS1def, Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Finset.mem_range] at hi
      by_cases ha : a = 0
      · left
        rw [hR1def, Finset.mem_image]
        exact ⟨i + b, by rw [Finset.mem_range]; omega, by simp [ha]⟩
      · right
        rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        dsimp only
        refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rw [hS2def, Finset.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
      right
      rw [hR2def, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      dsimp only
      refine ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  have hLHSunfold : HkIntegrand α 2 (mixed b a g) z θ
      = (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0) := by
    simp [HkIntegrand, ← hH, ← hW]
  have hRHSunfold : HkIntegrand α 4 g z θ
      = (∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * W) ^ 2 else 0) := by
    simp [HkIntegrand, ← hH, ← hW]
  have hstep1 : (∑ i ∈ Finset.range 3, (DzIter i (mixed b a g) z θ * H) ^ 2)
        + (∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3,
            (if 1 ≤ i ∧ i + j ≤ 2 then (mixed j i (mixed b a g) z θ * W) ^ 2 else 0))
      ≤ ∑ x ∈ S1 ∪ S2, T x := by
    rw [hS2, Finset.sum_union hdisjS]
    linarith [hS1]
  have hstep2 : (∑ x ∈ S1 ∪ S2, T x)
      ≤ (∑ i ∈ Finset.range 5, (DzIter i g z θ * H) ^ 2)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i g z θ * W) ^ 2 else 0) := by
    rw [← hR1, ← hR2, ← Finset.sum_union hdisjR]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hTnn x)
  rw [hLHSunfold, hRHSunfold]
  exact le_trans hstep1 hstep2

theorem HkSq_mixed_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hmem : Work.Spaces.HkMem α 4 g)
    (b a : ℕ) (hab : a + b ≤ 2) :
    Work.Spaces.HkSq α 2 (Work.Spaces.mixed b a g) ≤ Work.Spaces.HkSq α 4 g := by
  simp only [HkSq]
  apply setIntegral_mono_of_nonneg
  · intro z _
    exact integral_nonneg fun θ => HkIntegrand_nonneg α 2 (mixed b a g) z θ
  · intro z hz
    apply setIntegral_mono_of_nonneg
    · intro θ _
      exact HkIntegrand_nonneg α 2 (mixed b a g) z θ
    · intro θ hθ
      exact HkIntegrand_mixed_le α hα g hsm b a hab z θ hz hθ
    · exact hmem.1 z hz
  · exact hmem.2

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.ProductTools =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- `g` is square integrable over the domain in the iterated sense: every angular
slice is integrable and the resulting function of `z` is integrable on `[0,∞)`. -/
def L2Mem (g : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Iz, IntegrableOn (fun θ => (g z θ) ^ 2) Iθ) ∧
    IntegrableOn (fun z => ∫ θ in Iθ, (g z θ) ^ 2) Iz


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.SinMinBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

#check @Real.rpow_le_one
#check @Real.mul_rpow
#check @Real.inv_rpow
#check @Real.rpow_add
#check @Real.rpow_le_rpow_of_nonpos
#check @Real.rpow_neg
#check @Real.mul_le_sin


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.c_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-!
# Bounds for the normalisation constant `c(α)`

`c α = ∫ θ in Iθ, Γ(θ)K(θ) dθ` is the normalisation constant of Elgindi's paper
(`c = ∫₀^{π/2} Γ(θ)K(θ) dθ`, with `Γ(θ) = (sin θ cos²θ)^{α/3}` and
`K(θ) = 3 sin θ cos²θ`).  The paper only ever uses the coarse range
`1/10 ≤ c(α) ≤ 10`, which is what we establish here for `0 < α ≤ 1`.

The integrand is `3 (sin θ cos²θ)^{1 + α/3}`; on `[0, π/2]` the base
`u = sin θ cos²θ` lies in `[0,1]` and the exponent `1 + α/3 ∈ (1, 4/3]`, so the
integrand is squeezed between `0` and `3` (upper bound) and is bounded below by
`3 (1/4)^{4/3} ≥ 2/5` on the sub-interval `[π/6, π/4]`, where `u ≥ 1/4` (lower
bound: `(1/4)^{4/3} ≥ 2/15` since `(2/15)³ = 8/3375 ≤ 1/256 = (1/4)⁴`).
-/

/-- Pointwise bounds for the integrand of `c`: on the domain `Iθ` the product
`Γ(θ)K(θ)` takes values in `[0,3]`. -/
theorem gamK_bounds (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Iθ) :
    0 ≤ Gam α θ * K θ ∧ Gam α θ * K θ ≤ 3 := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have ht0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 (by positivity)
  have ht1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc1 : Real.cos θ ^ 2 ≤ 1 := by
      have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
      simpa using h
    have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
    have h := mul_le_mul hs1 hc1 hc0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hα3 : 0 ≤ α / 3 := by linarith
  have hGam0 : 0 ≤ Gam α θ := by
    rw [Gam]; exact Real.rpow_nonneg ht0 _
  have hGam1 : Gam α θ ≤ 1 := by
    rw [Gam]; exact Real.rpow_le_one ht0 ht1 hα3
  have hKθ : K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) := by rw [K]; ring
  have hK0 : 0 ≤ K θ := by rw [hKθ]; exact mul_nonneg (by norm_num) ht0
  have hK1 : K θ ≤ 3 := by rw [hKθ]; linarith
  exact ⟨mul_nonneg hGam0 hK0, by nlinarith [hGam0, hGam1, hK0, hK1]⟩

/-- Lower bound for the integrand of `c` on the sub-interval `[π/6, π/4]`:
there `u = sin θ cos²θ ≥ 1/4`, whence
`Γ(θ)K(θ) = 3 u^{1+α/3} ≥ 3 u^{4/3} ≥ 3 (1/4)^{4/3} ≥ 2/5`. -/
theorem gamK_lower (α θ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Icc (π/6) (π/4)) : (2 : ℝ) / 5 ≤ Gam α θ * K θ := by
  have hsin : (1/2 : ℝ) ≤ Real.sin θ := by
    have h1 : Real.sin (π/6) ≤ Real.sin θ :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]) hθ.1
    rwa [Real.sin_pi_div_six] at h1
  have hcos2 : (1/2 : ℝ) ≤ Real.cos θ ^ 2 := by
    have h1 : Real.cos (π/4) ≤ Real.cos θ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [Real.pi_pos]) hθ.2
    rw [Real.cos_pi_div_four] at h1
    have hsq : (√2/2)^2 = (1/2 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have h2 : (√2/2)^2 ≤ (Real.cos θ)^2 := pow_le_pow_left₀ (by positivity) h1 2
    linarith [h2, hsq]
  have hsin0 : (0 : ℝ) ≤ Real.sin θ := le_trans (by norm_num) hsin
  have ht_ge : (1/4 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 := mul_le_mul hsin hcos2 (by norm_num : (0 : ℝ) ≤ 1/2) hsin0
    rw [show (1/2 : ℝ) * (1/2) = 1/4 by norm_num] at h1
    exact h1
  have ht_pos : (0 : ℝ) < Real.sin θ * Real.cos θ ^ 2 := by linarith
  have ht_le1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc : Real.cos θ ^ 2 ≤ 1 := by
      have := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ); simpa using this
    have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
    have h1 := mul_le_mul hs hc hc0 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h1
  have ht_nonneg : (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := le_of_lt ht_pos
  have hprod : Gam α θ * K θ = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (α/3 + 1) := by
    rw [Gam, K, Real.rpow_add' ht_nonneg (by positivity : α/3 + 1 ≠ 0), Real.rpow_one]
    ring
  have hexp : (Real.sin θ * Real.cos θ ^ 2)^((4:ℝ)/3)
      ≤ (Real.sin θ * Real.cos θ ^ 2)^(α/3 + 1) :=
    Real.rpow_le_rpow_of_exponent_ge ht_pos ht_le1 (by linarith)
  have hbase : (1/4 : ℝ)^((4:ℝ)/3) ≤ (Real.sin θ * Real.cos θ ^ 2)^((4:ℝ)/3) :=
    Real.rpow_le_rpow (by norm_num) ht_ge (by norm_num)
  have hnum : (2 : ℝ)/5 ≤ 3 * (1/4 : ℝ)^(4/3 : ℝ) := by
    have h : ((8 : ℝ)/15) ≤ (1/4 : ℝ)^(1/3 : ℝ) := by
      have hbase' : ((8 : ℝ)/15) ^ ((3:ℕ):ℝ) ≤ (1/4 : ℝ) := by
        rw [Real.rpow_natCast]; norm_num
      have hle : (((8 : ℝ)/15) ^ ((3:ℕ):ℝ))^(1/3:ℝ) ≤ (1/4 : ℝ)^(1/3:ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase' (by norm_num)
      have hsimp : (((8 : ℝ)/15) ^ ((3:ℕ):ℝ))^(1/3:ℝ) = (8 : ℝ)/15 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8/15) ((3:ℕ):ℝ) (1/3),
            show (((3:ℕ):ℝ) * (1/3:ℝ)) = 1 by norm_num, Real.rpow_one]
      rwa [hsimp] at hle
    have h4 : (1/4 : ℝ)^(4/3 : ℝ) = (1/4 : ℝ) * (1/4 : ℝ)^(1/3 : ℝ) := by
      rw [show ((4 : ℝ)/3) = 1 + 1/3 by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 1/4) 1 (1/3), Real.rpow_one]
    nlinarith [h, h4]
  rw [hprod]
  linarith [hnum, hbase, hexp]

theorem c_bounds (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) / 10 ≤ Work.Spaces.c α ∧ Work.Spaces.c α ≤ 10 := by
  have h_int : IntegrableOn (fun θ : ℝ => Gam α θ * K θ) Iθ :=
    CAux.integrableOn_GamK α hα
  have h_nonneg : ∀ᵐ θ ∂(volume.restrict Iθ), (0 : ℝ) ≤ Gam α θ * K θ := by
    rw [Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun θ hθ => (gamK_bounds α θ hα hθ).1
  have hvolθ : volume.real Iθ = π / 2 := by
    rw [Iθ, MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hvolS : volume.real (Set.Icc (π/6) (π/4)) = π / 12 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hsub : Set.Icc (π/6) (π/4) ⊆ Iθ := fun θ hθ =>
    ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  have hst : Set.Icc (π/6) (π/4) ≤ᵐ[volume] Iθ := by
    filter_upwards with θ hθ
    exact hsub hθ
  have hfin : volume (Set.Icc (π/6) (π/4)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  constructor
  · have hge : (2 : ℝ)/5 * volume.real (Set.Icc (π/6) (π/4))
        ≤ ∫ θ in Set.Icc (π/6) (π/4), Gam α θ * K θ :=
      MeasureTheory.setIntegral_ge_of_const_le_real measurableSet_Icc hfin
        (fun θ hθ => gamK_lower α θ hα hα1 hθ) (h_int.mono_set hsub)
    have hle : ∫ θ in Set.Icc (π/6) (π/4), Gam α θ * K θ
        ≤ ∫ θ in Iθ, Gam α θ * K θ :=
      MeasureTheory.setIntegral_mono_set h_int h_nonneg hst
    have hnum : (1 : ℝ)/10 ≤ (2 : ℝ)/5 * volume.real (Set.Icc (π/6) (π/4)) := by
      rw [hvolS]; linarith [Real.pi_gt_three]
    calc (1 : ℝ)/10 ≤ (2 : ℝ)/5 * volume.real (Set.Icc (π/6) (π/4)) := hnum
      _ ≤ ∫ θ in Set.Icc (π/6) (π/4), Gam α θ * K θ := hge
      _ ≤ ∫ θ in Iθ, Gam α θ * K θ := hle
      _ = Work.Spaces.c α := rfl
  · have hle3 : ∫ θ in Iθ, Gam α θ * K θ ≤ ∫ θ in Iθ, (3 : ℝ) :=
      MeasureTheory.setIntegral_mono_on h_int
        (MeasureTheory.integrableOn_const (by rw [Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        measurableSet_Icc (fun θ hθ => (gamK_bounds α θ hα hθ).2)
    have hconst : ∫ θ in Iθ, (3 : ℝ) = 3 * (π/2) := by
      rw [MeasureTheory.setIntegral_const, hvolθ, smul_eq_mul]; ring
    calc Work.Spaces.c α = ∫ θ in Iθ, Gam α θ * K θ := rfl
      _ ≤ ∫ θ in Iθ, (3 : ℝ) := hle3
      _ = 3 * (π/2) := hconst
      _ ≤ 10 := by linarith [Real.pi_le_four]

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.factor_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The `(z+1)^m`-weighted bound for `∂_z^m D_θ^i f`, `m + i ≤ 4`:

`|(z+1)^m ∂_z^m D_θ^i f| ≤ |f|_𝒲 · (1 if i = 0, else (α+sin 2θ) sin(2θ)^{α/5})`.

For `i = 0` this is `WlInf_z_bound`; for `i ≥ 1` it is `(z+1)^m` times
`pz_Dth_sup_bound`, the factor `(1+z)^{-m}` cancelling. -/
theorem factor_bound (α : ℝ) (hα : 0 < α) (h : ℝ → ℝ → ℝ) (hmem : Work.Spaces.WlInfMem α 4 h)
    (m i : ℕ) (hm : m ≤ 4) (hi : 1 ≤ i → m + i ≤ 4) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |(z + 1) ^ m * Work.Spaces.pzIter m (Work.Spaces.DthIter i h) z θ| ≤
      Work.Spaces.WlInf α 4 h *
        (if i = 0 then 1 else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  rcases eq_or_ne i 0 with hi0 | hi0
  · -- `i = 0`: this is the radial bound `WlInf_z_bound`.
    subst hi0
    simpa using WlInf_z_bound α 4 h hmem m hm z θ hz hθ
  · -- `i ≥ 1`: multiply the unweighted angular bound by `(z+1)^m`.
    have hz0 : (0 : ℝ) ≤ z := hz
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hzpow : (0 : ℝ) < (z + 1) ^ m := pow_pos hz1 m
    have hne : (z + 1) ^ m ≠ 0 := ne_of_gt hzpow
    have hi1 : 1 ≤ i := by omega
    have hle : m + i ≤ 4 := hi hi1
    have hb := pz_Dth_sup_bound α hα 4 h hmem i m hi1 hle z θ hz hθ
    rw [if_neg hi0]
    calc |(z + 1) ^ m * pzIter m (DthIter i h) z θ|
        = (z + 1) ^ m * |pzIter m (DthIter i h) z θ| := by
          rw [abs_mul, abs_of_pos hzpow]
      _ ≤ (z + 1) ^ m * (WlInf α 4 h / (z + 1) ^ m
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt hzpow)
      _ = WlInf α 4 h * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
          rw [← mul_assoc, mul_div_cancel₀ _ hne]

end Work.Spaces
end
end
