import Submission.Work.Mori.Defs
import Submission.Work.Mori.eq_const_of_holomorphicOnX_norm_eq
import Submission.HolomorphicLog

/-!
# A global holomorphic conjugate gives a periodic argument

`Work.Mori.hasArg_of_holomorphic_conjugate`: if `G : X → ℂ` is holomorphic and nowhere zero and
`F : X → ℂ` is a global holomorphic conjugate of `log ‖G‖` (`(F y).re = log ‖G y‖`), then along every
continuous `1`-periodic curve `f` of `X` the curve `t ↦ G (f t)` has a periodic argument
(`Commons.Topology.Winding.HasArg`).

Reason: `W := G · exp (-F)` is holomorphic with constant modulus `1`, hence constant; writing that
constant as `exp (i c)`, the function `H := F + i c` is a global holomorphic *logarithm* of `G`, and
`t ↦ (H (f t)).im` is the required periodic argument.

This is the `data → argument` half of `Work.Mori.hasArg_comp_of_holomorphic_of_subsingleton`, with the
conjugate supplied by the caller instead of being produced by the challenge hypothesis; it is what
turns a vanishing argument-period homomorphism into a contradiction
(`Work.Mori.argumentPeriodHom_ne_zero`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Mori

/-- **A global holomorphic conjugate of `log ‖G‖` makes the argument of `G` single-valued along every
loop.** -/
theorem hasArg_of_holomorphic_conjugate {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {G F : X → ℂ} (hG : Submission.HolomorphicOnX G Set.univ) (hGne : ∀ y : X, G y ≠ 0)
    (hF : Submission.HolomorphicOnX F Set.univ) (hre : ∀ y : X, (F y).re = Real.log ‖G y‖)
    {f : ℝ → X} (hf : Continuous f) (hfper : ∀ t : ℝ, f (t + 1) = f t) :
    Commons.Topology.Winding.HasArg (fun t : ℝ => G (f t)) 0 := by
  -- `W = G · exp (-F)` is holomorphic with constant modulus `1`
  have hneg₀ : Submission.HolomorphicOnX (fun y : X => (0 : ℂ) - F y) Set.univ :=
    (Submission.holomorphicOnX_const (0 : ℂ)).sub hF
  have hneg : Submission.HolomorphicOnX (fun y : X => -(F y)) Set.univ := by
    have hfun : (fun y : X => (0 : ℂ) - F y) = fun y : X => -(F y) := by
      funext y; simp
    rwa [hfun] at hneg₀
  have hW : Submission.HolomorphicOnX (fun y => G y * Complex.exp (-(F y))) Set.univ :=
    hG.mul hneg.cexp
  have hWnorm : ∀ y : X, ‖G y * Complex.exp (-(F y))‖ = 1 := by
    intro y
    have hpos : 0 < ‖G y‖ := norm_pos_iff.mpr (hGne y)
    rw [Complex.norm_mul, Complex.norm_exp, Complex.neg_re, hre y, Real.exp_neg, Real.exp_log hpos]
    field_simp
  let W₀ : ℂ := G (Classical.arbitrary X) * Complex.exp (-(F (Classical.arbitrary X)))
  have hWnorm₀ : ‖W₀‖ = 1 := hWnorm (Classical.arbitrary X)
  have hWconst : ∀ y : X, G y * Complex.exp (-(F y)) = W₀ := fun y => by
    show G y * Complex.exp (-(F y))
      = G (Classical.arbitrary X) * Complex.exp (-(F (Classical.arbitrary X)))
    exact eq_const_of_holomorphicOnX_norm_eq hW hWnorm (Classical.arbitrary X) y
  -- `H := F + i·arg W₀` is a global holomorphic logarithm of `G`
  have hW₀arg : W₀ = Complex.exp ((Complex.arg W₀ : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I W₀
    rw [hWnorm₀] at h
    simpa using h.symm
  have hHexp : ∀ y : X, Complex.exp (F y + (Complex.arg W₀ : ℂ) * Complex.I) = G y := by
    intro y
    calc Complex.exp (F y + (Complex.arg W₀ : ℂ) * Complex.I)
        = Complex.exp (F y) * Complex.exp ((Complex.arg W₀ : ℂ) * Complex.I) := by
          rw [Complex.exp_add]
      _ = Complex.exp (F y) * W₀ := by rw [← hW₀arg]
      _ = Complex.exp (F y) * (G y * Complex.exp (-(F y))) := by rw [← hWconst y]
      _ = G y := by
          have hexp : Complex.exp (F y) * Complex.exp (-(F y)) = 1 := by
            rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
          calc Complex.exp (F y) * (G y * Complex.exp (-(F y)))
              = G y * (Complex.exp (F y) * Complex.exp (-(F y))) := by ring
            _ = G y * 1 := by rw [hexp]
            _ = G y := by ring
  refine ⟨fun t : ℝ => (F (f t)).im + Complex.arg W₀,
    (Complex.continuous_im.comp (hF.continuous.comp hf)).add continuous_const, ?_, ?_⟩
  · intro t
    simp only [hfper t]
  · intro t
    rw [sub_zero]
    show G (f t) = (‖G (f t)‖ : ℂ)
      * Complex.exp ((((F (f t)).im + Complex.arg W₀ : ℝ) : ℂ) * Complex.I)
    have hsplit : Complex.exp (F (f t) + (Complex.arg W₀ : ℂ) * Complex.I)
        = ((Real.exp (F (f t) + (Complex.arg W₀ : ℂ) * Complex.I).re : ℝ) : ℂ)
          * Complex.exp (((F (f t) + (Complex.arg W₀ : ℂ) * Complex.I).im : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.re_add_im (F (f t) + (Complex.arg W₀ : ℂ) * Complex.I)]
      rw [Complex.exp_add, ← Complex.ofReal_exp]
    rw [← hHexp (f t), Complex.norm_exp, hsplit]
    have him : (F (f t) + (Complex.arg W₀ : ℂ) * Complex.I).im
        = (F (f t)).im + Complex.arg W₀ := by
      simp [Complex.add_im, Complex.mul_im]
    rw [him]

end Work.Mori
