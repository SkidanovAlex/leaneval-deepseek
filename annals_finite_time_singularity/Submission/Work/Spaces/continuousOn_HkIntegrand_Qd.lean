import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.H2.T2Aesm
import Submission.Work.Spaces.MixedMulDefs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

noncomputable section

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## The open quadrant of the statement

The requested continuity holds on the open quadrant `(0,∞) × (0,π/2)`, where the
weights `w` and `W = w · sin(2θ)^{-γ/2}` are finite and continuous and where the
iterated derivatives of `F` are smooth (since this quadrant is contained in the
`quadU = (-1,∞) × (0,π/2)` on which `F` is assumed `C^∞`). -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
private def Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π/2)

private lemma Qd_subset_quadU : Qd ⊆ quadU :=
  Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num : (-1 : ℝ) ≤ 0)) subset_rfl

/-- `sin (2θ) > 0` for `θ ∈ (0, π/2)`. -/
private lemma sin_two_pos_Qd {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π/2)) : 0 < Real.sin (2 * θ) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-! ## Smoothness of the iterated operators on `quadU` -/

/-- `D_z` preserves `C^∞`-regularity on the open set `quadU`. -/
theorem contDiffOn_uncurry_Dz_of_quadU {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) quadU) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Dz G)) quadU := by
  have hpz := contDiffOn_uncurry_pz isOpen_quadU h
  have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => p.1 * Function.uncurry (pz G) p) quadU :=
    contDiffOn_fst.mul hpz
  refine h1.congr ?_
  intro p hp
  rfl

/-- `D_θ` preserves `C^∞`-regularity on the open set `quadU`. -/
theorem contDiffOn_uncurry_Dth_of_quadU {G : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) quadU) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Dth G)) quadU := by
  have hpth := contDiffOn_uncurry_pth isOpen_quadU h
  have hsin : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) quadU :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have h1 : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (pth G) p)
      quadU := hsin.mul hpth
  refine h1.congr ?_
  intro p hp
  rfl

/-- Every iterate of `D_z` preserves `C^∞`-regularity on `quadU`. -/
theorem contDiffOn_uncurry_DzIter_of_quadU (G : ℝ → ℝ → ℝ)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) quadU) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (DzIter n G)) quadU := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [DzIter_succ]
      exact contDiffOn_uncurry_Dz_of_quadU ih

/-- Every iterate of `D_θ` preserves `C^∞`-regularity on `quadU`. -/
theorem contDiffOn_uncurry_DthIter_of_quadU (G : ℝ → ℝ → ℝ)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) quadU) (n : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (DthIter n G)) quadU := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
      rw [DthIter_succ]
      exact contDiffOn_uncurry_Dth_of_quadU ih

/-- The mixed operator `D_z^j D_θ^i` preserves `C^∞`-regularity on `quadU`. -/
theorem contDiffOn_uncurry_mixed_of_quadU (G : ℝ → ℝ → ℝ)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) quadU) (j i : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (mixed j i G)) quadU :=
  contDiffOn_uncurry_DzIter_of_quadU (DthIter i G)
    (contDiffOn_uncurry_DthIter_of_quadU G h i) j

/-! ## Continuity of the iterated derivatives on the open quadrant -/

private lemma continuousOn_DzIter_Qd (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) quadU) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => DzIter i F p.1 p.2) Qd :=
  ((contDiffOn_uncurry_DzIter_of_quadU F hF i).continuousOn).mono Qd_subset_quadU

private lemma continuousOn_mixed_Qd (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) quadU) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => mixed j i F p.1 p.2) Qd :=
  ((contDiffOn_uncurry_mixed_of_quadU F hF j i).continuousOn).mono Qd_subset_quadU

/-! ## Continuity of the weights on the open quadrant -/

private lemma continuousOn_w_Qd : ContinuousOn (fun p : ℝ × ℝ => w p.1) Qd := by
  simp only [w]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => ?_)
  exact pow_ne_zero 2 (ne_of_gt hp.1)

private lemma continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd :=
  ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun _p hp => Or.inl (ne_of_gt (sin_two_pos_Qd hp.2)))

private lemma continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Wt α p.1 p.2) Qd := by
  simp only [Wt, wTheta]
  exact continuousOn_w_Qd.mul (continuousOn_sinpow_Qd (-(gam α / 2)))

private lemma continuousOn_wdivsin_Qd :
    ContinuousOn (fun p : ℝ × ℝ => w p.1 / (Real.sin (2 * p.2)) ^ (eta / 2)) Qd :=
  continuousOn_w_Qd.div (continuousOn_sinpow_Qd (eta / 2))
    (fun _p hp => ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos_Qd hp.2) _))

/-! ## The integrand is continuous on the open quadrant -/

theorem continuousOn_HkIntegrand_Qd (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : ContDiffOn ℝ ⊤ (Function.uncurry F) Work.Spaces.quadU) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  change ContinuousOn (fun p : ℝ × ℝ => HkIntegrand α k F p.1 p.2) Qd
  simp only [HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi => ?_)
    exact (((continuousOn_DzIter_Qd F hF i).mul continuousOn_wdivsin_Qd).pow 2)
  · refine continuousOn_finsetSum (Finset.range (k + 1)) (fun i hi =>
      continuousOn_finsetSum (Finset.range (k + 1)) (fun j hj => ?_))
    split_ifs with h
    · exact ((continuousOn_mixed_Qd F hF j i).mul (continuousOn_Wt_Qd α)).pow 2
    · exact continuousOn_const

end

end Work.Spaces
