/-
Copyright: work module for the Elgindi finite-time singularity project.

# The box around the support, the vanishing off the support, and the smoothness of the halves

* `existsBoxQ0Aux`: a compact subset of the open quadrant is contained in the *open* rectangle
  spanned by two points `a ≤ b` of the quadrant;
* `supportVanishAux`: off the topological support of `g`, the function and its two first
  partial derivatives vanish;
* `contDiffOnPairAux`: the two halves `pairRad`, `pairAng` of the divergence form are `C¹` on
  the open quadrant when `Φ, φ` are `C^∞` there;
* `pairRad_eq_zero_off_tsupport`, `pairAng_eq_zero_off_tsupport`: consequently both halves of
  the divergence form vanish off `tsupport φ` (their boundary values on the rectangle vanish).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.EllipticEst.Assembly.PairDefs
import Submission.Work.EllipticEst.Assembly.PairAuxBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem existsBoxQ0Aux {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ a b : ℝ × ℝ, a ≤ b ∧ 0 < a.1 ∧ 0 < a.2 ∧ b.2 < π / 2 ∧
      K ⊆ Set.Ioo a.1 b.1 ×ˢ Set.Ioo a.2 b.2 := by
  rcases K.eq_empty_or_nonempty with hK0 | hne
  · subst hK0
    refine ⟨(1, 1), (2, 3 / 2), ?_, by norm_num, by norm_num, by linarith [Real.pi_gt_three], ?_⟩
    · constructor <;> norm_num
    · intro x hx; exact absurd hx (Set.notMem_empty x)
  · obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨q, hqK, hqmax⟩ := hK.exists_isMaxOn hne continuous_fst.continuousOn
    obtain ⟨r, hrK, hrmin⟩ := hK.exists_isMinOn hne continuous_snd.continuousOn
    obtain ⟨s, hsK, hsmax⟩ := hK.exists_isMaxOn hne continuous_snd.continuousOn
    have hp1 : 0 < p.1 := (Work.FTS.EllipticEst.mem_Q0.mp (hsub hpK)).1
    have hq1 : 0 < q.1 := (Work.FTS.EllipticEst.mem_Q0.mp (hsub hqK)).1
    have hr2 : 0 < r.2 := (Work.FTS.EllipticEst.mem_Q0.mp (hsub hrK)).2.1
    have hs2 : s.2 < π / 2 := (Work.FTS.EllipticEst.mem_Q0.mp (hsub hsK)).2.2
    have hpq : p.1 ≤ q.1 := hpmin hqK
    have hrs : r.2 ≤ s.2 := hrmin hsK
    refine ⟨(p.1 / 2, r.2 / 2), (2 * q.1, (π / 2 + s.2) / 2), ?_, ?_, ?_, ?_, ?_⟩
    · constructor <;> linarith
    · linarith
    · linarith
    · linarith
    · intro x hx
      have hx1 : p.1 ≤ x.1 := hpmin hx
      have hx1' : x.1 ≤ q.1 := hqmax hx
      have hx2 : r.2 ≤ x.2 := hrmin hx
      have hx2' : x.2 ≤ s.2 := hsmax hx
      rw [Set.mem_prod]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem supportVanishAux {g : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry g)) :
    g x.1 x.2 = 0 ∧ Work.Spaces.pz g x.1 x.2 = 0 ∧ Work.Spaces.pth g x.1 x.2 = 0 := by
  obtain ⟨U, V, hUo, hVo, hxU, hxV, hzero⟩ := exists_isOpen_local_zero_of_notMem_tsupport hx
  refine ⟨hzero x.1 hxU x.2 hxV, ?_, ?_⟩
  · have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.1] (fun z => g z x.2) := by
      filter_upwards [hUo.mem_nhds hxU] with z hz
      exact (hzero z hz x.2 hxV).symm
    exact ((hs.deriv_eq).symm.trans (deriv_const x.1 0))
  · have hs : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x.2] (fun θ => g x.1 θ) := by
      filter_upwards [hVo.mem_nhds hxV] with θ hθ
      exact (hzero x.1 hxU θ hθ).symm
    exact ((hs.deriv_eq).symm.trans (deriv_const x.2 0))

theorem contDiffOnPairAux {α : ℝ} {Φ φ : ℝ → ℝ → ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen Φ) (hφ : Work.FTS.EllipticEst.SmoothOpen φ) :
    ContDiffOn ℝ 1 (Work.EllipticEst.Assembly.pairRad α Φ φ) Work.FTS.EllipticEst.Q0
      ∧ ContDiffOn ℝ 1 (Work.EllipticEst.Assembly.pairAng α Φ φ) Work.FTS.EllipticEst.Q0 := by
  have hrpow : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => x.1 ^ (pairBeta α + 2))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.contDiffOn_iff.mpr fun x hx =>
      (Real.contDiffAt_rpow_const_of_ne (p := pairBeta α + 2)
        (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hx).1)).comp x contDiffAt_fst
  have hrpow1 : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => x.1 ^ pairBeta α)
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.contDiffOn_iff.mpr fun x hx =>
      (Real.contDiffAt_rpow_const_of_ne (p := pairBeta α)
        (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hx).1)).comp x contDiffAt_fst
  have hcos : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Real.cos x.2) Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hφ0 : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => φ x.1 x.2) Work.FTS.EllipticEst.Q0 :=
    hφ.forall 1
  have hΦ0 : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Φ x.1 x.2) Work.FTS.EllipticEst.Q0 :=
    hΦ.forall 1
  have hpzφ : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Work.Spaces.pz φ x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hφ.pz).forall 1
  have hpzΦ : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Work.Spaces.pz Φ x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hΦ.pz).forall 1
  have hpthφ : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Work.Spaces.pth φ x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hφ.pth).forall 1
  have hpthΦ : ContDiffOn ℝ 1 (fun x : ℝ × ℝ => Work.Spaces.pth Φ x.1 x.2)
      Work.FTS.EllipticEst.Q0 := (hΦ.pth).forall 1
  constructor
  · refine (((contDiffOn_const (c := α ^ 2)).mul hrpow).mul hcos).mul ?_
    exact (hpzφ.mul hΦ0).sub (hpzΦ.mul hφ0)
  · exact (hrpow1.mul hcos).mul ((hpthφ.mul hΦ0).sub (hpthΦ.mul hφ0))

theorem pairRad_eq_zero_off_tsupport {α : ℝ} {Φ φ : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry φ)) : pairRad α Φ φ x = 0 := by
  obtain ⟨h1, h2, -⟩ := supportVanishAux (g := φ) hx
  simp only [pairRad_apply]
  rw [h1, h2]
  ring

theorem pairAng_eq_zero_off_tsupport {α : ℝ} {Φ φ : ℝ → ℝ → ℝ} {x : ℝ × ℝ}
    (hx : x ∉ tsupport (Function.uncurry φ)) : pairAng α Φ φ x = 0 := by
  obtain ⟨h1, -, h3⟩ := supportVanishAux (g := φ) hx
  simp only [pairAng_apply]
  rw [h1, h3]
  ring


end Work.EllipticEst.Assembly
