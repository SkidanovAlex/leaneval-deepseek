/-
Copyright: work module for the Elgindi finite-time singularity project.

# Measurability of `|F · Ψ|` and of its weighted angular integral

For a smooth (`Work.Spaces.SmoothNbhd`) solution `Ψ` of the elliptic law
`Work.Elliptic.bslOp α Ψ = F` on the open quadrant (`Work.Elliptic.IsBslSol`), the source `F`
is only defined through the equation, so it is *not* a priori measurable.  On the open quadrant
`Q = (0,∞) × (0,π/2)` however `F` agrees with `bslOp α Ψ`, which is continuous there because
`Ψ` is smooth on a neighbourhood of the closed quadrant and `Real.tan` is smooth on `Q`
(`0 < θ < π/2`).  Since `Q` differs from `Iz ×ˢ Iθ` by a null set, this identifies `F` almost
everywhere with a continuous function.

The lemma proved here is the measurability input that the elliptic estimates of
§'Elliptic Regularity Estimates' need in order to speak about `|F Ψ|` as an integrand:
`p ↦ |F p.1 p.2 · Ψ p.1 p.2|` is a.e. strongly measurable for the product of the restrictions of
Lebesgue measure to `Iz` and `Iθ`, and the weighted angular slice
`z ↦ w(z)² ∫_θ |F z θ · Ψ z θ| dθ` is a.e. strongly measurable for the restricted measure on
`Iz`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Auxiliary lemmas -/

/-- The open quadrant `(0,∞) × (0,π/2)` is contained in the neighbourhood
`Work.Spaces.U = (-1,∞) × (-1,π/2+1)` on which `SmoothNbhd` gives smoothness. -/
theorem Q0_subset_U :
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) ⊆ Work.Spaces.U :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
    (Set.Ioo_subset_Ioo (by norm_num) (by linarith [Real.pi_pos]))

/-- `Work.Spaces.pzIter` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_uncurry_pzIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (k : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pzIter k G)) V := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Work.Spaces.pzIter_succ]; exact Work.Spaces.contDiffOn_uncurry_pz hV ih

/-- `Work.Spaces.pthIter` preserves `C^∞`-smoothness on an open set. -/
theorem contDiffOn_uncurry_pthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (k : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pthIter k G)) V := by
  induction k with
  | zero => simpa using h
  | succ k ih => rw [Work.Spaces.pthIter_succ]; exact Work.Spaces.contDiffOn_uncurry_pth hV ih

/-- The angular coefficient `(z,θ) ↦ tan θ · Ψ z θ` is smooth on the open quadrant when `Ψ` is
smooth on a neighbourhood of the closed quadrant: the only singularities of `Real.tan` are the
poles `θ = π/2 + kπ`, and `0 < θ < π/2` keeps us away from all of them. -/
theorem contDiffOn_tan_mul_Q0 {Ψ : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd Ψ) :
    ContDiffOn ℝ ⊤ (Function.uncurry fun z θ => Real.tan θ * Ψ z θ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hΨ : ContDiffOn ℝ ⊤ (Function.uncurry Ψ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := hsm.mono Q0_subset_U
  have htan : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.tan p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Real.tan p.2)
        = fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2 := by
      funext p; exact Real.tan_eq_sin_div_cos p.2
    rw [hfun]
    refine ContDiffOn.div ?_ ?_ ?_
    · exact (Real.contDiff_sin.comp contDiff_snd).contDiffOn
    · exact (Real.contDiff_cos.comp contDiff_snd).contDiffOn
    · intro p hp
      rw [Set.mem_prod] at hp
      obtain ⟨-, h0, h1⟩ := hp
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  exact htan.mul hΨ

/-- **Continuity of `bslOp` on the open quadrant.**  If `Ψ` is smooth on a neighbourhood of the
closed quadrant, then the elliptic operator `Work.Elliptic.bslOp α Ψ` is continuous on the open
quadrant `(0,∞) × (0,π/2)`. -/
theorem continuousOn_bslOp_Q0 (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
  have hQ0 : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hΨ : ContDiffOn ℝ ⊤ (Function.uncurry Ψ)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := hsm.mono Q0_subset_U
  have hA : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (contDiffOn_uncurry_pzIter hQ0 hΨ 2).continuousOn
  have hB : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (Work.Spaces.contDiffOn_uncurry_pz hQ0 hΨ).continuousOn
  have hC : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 Ψ p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (contDiffOn_uncurry_pthIter hQ0 hΨ 2).continuousOn
  have hD : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    (Work.Spaces.contDiffOn_uncurry_pth hQ0 (contDiffOn_tan_mul_Q0 hsm)).continuousOn
  have hE : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := hΨ.continuousOn
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero]
  fun_prop

/-! ## The main lemma -/

theorem aesm_F_mul_Psi_of_sol (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (hsol : Work.Elliptic.IsBslSol α F Ψ) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => |F p.1 p.2 * Ψ p.1 p.2|)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
      ∧ MeasureTheory.AEStronglyMeasurable
          (fun z => (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, |F z θ * Ψ z θ|)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  -- the product measure is the restriction of the planar Lebesgue measure to the open quadrant
  have hIz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hIθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprodae : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) :=
    MeasureTheory.Measure.set_prod_ae_eq hIz hIθ
  have hμeq : (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact MeasureTheory.Measure.restrict_congr_set hprodae
  have haeQ : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
      (volume.restrict Work.Spaces.Iθ)), p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [hμeq]
    exact MeasureTheory.ae_restrict_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  -- on the quadrant, `F` agrees with the continuous function `bslOp α Ψ`
  have hFeq : (fun p : ℝ × ℝ => F p.1 p.2)
      =ᵐ[((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => Work.Elliptic.bslOp α Ψ p.1 p.2) := by
    filter_upwards [haeQ] with p hp
    rw [Set.mem_prod] at hp
    obtain ⟨hz, hθ0, hθ1⟩ := hp
    exact (hsol.1 p.1 hz p.2 hθ0 hθ1).symm
  -- hence `|F · Ψ|` is a.e. equal to a continuous function
  have hgood_cont : ContinuousOn
      (fun p : ℝ × ℝ => |Work.Elliptic.bslOp α Ψ p.1 p.2 * Ψ p.1 p.2|)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (π / 2)) := by
    refine (continuousOn_bslOp_Q0 α Ψ hsm).mul ?_ |>.abs
    exact (hsm.mono Q0_subset_U).continuousOn
  have hgood : AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Work.Elliptic.bslOp α Ψ p.1 p.2 * Ψ p.1 p.2|)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hgood_cont
  have habs : (fun p : ℝ × ℝ => |F p.1 p.2 * Ψ p.1 p.2|)
      =ᵐ[((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => |Work.Elliptic.bslOp α Ψ p.1 p.2 * Ψ p.1 p.2|) := by
    filter_upwards [hFeq] with p hp
    rw [hp]
  refine ⟨hgood.congr habs.symm, ?_⟩
  -- the angular slice is a.e. strongly measurable by Fubini for Bochner integrals
  have hint : AEStronglyMeasurable
      (fun z : ℝ => ∫ θ, |F z θ * Ψ z θ| ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
      (hgood.congr habs.symm)
  -- and multiplication by the (a.e. continuous) weight `w²` preserves this
  have hwcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have h1 : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi (0 : ℝ)) :=
      ((continuousOn_const (c := (1 : ℝ))).add continuousOn_id).pow 2 |>.div
        (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    exact h1.pow 2
  have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    rw [MeasureTheory.Measure.restrict_congr_set hIz]
    exact hwcont.aestronglyMeasurable measurableSet_Ioi
  exact hw.mul hint

end Work.FTS.EllipticEst
