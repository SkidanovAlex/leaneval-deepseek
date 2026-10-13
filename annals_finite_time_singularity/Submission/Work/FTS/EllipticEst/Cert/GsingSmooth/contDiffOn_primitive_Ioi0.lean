import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cert.GsingSmooth

/-- Smoothness of a primitive on an open set: if `f` has derivative `g` at every point of an
open set `s` and `g` is `C^m` on `s` for every `m`, then `f` is `C^m` on `s` for every `m`.

This is the inductive step of the fundamental theorem of calculus: `deriv f` agrees with `g`
on `s`, so it inherits all the differentiability of `g`, and
`contDiffOn_succ_iff_deriv_of_isOpen` upgrades `C^n` of `deriv f` to `C^{n+1}` of `f`. -/
private lemma contDiffOn_of_hasDerivAt {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasDerivAt f (g x) x) (hg : ∀ m : ℕ, ContDiffOn ℝ m g s) :
    ∀ m : ℕ, ContDiffOn ℝ m f s := by
  have hderiv : ∀ x ∈ s, deriv f x = g x := fun x hx => (hf x hx).deriv
  have hdiff : DifferentiableOn ℝ f s :=
    fun x hx => (hf x hx).differentiableAt.differentiableWithinAt
  have hgm : ∀ m : ℕ, ContDiffOn ℝ m (deriv f) s :=
    fun m => (hg m).congr (fun x hx => hderiv x hx)
  intro m
  induction m with
  | zero => simpa using (contDiffOn_zero (𝕜 := ℝ) (f := f) (s := s)).mpr hdiff.continuousOn
  | succ m _ =>
      have h : ContDiffOn ℝ (((m : ℕ) : WithTop ℕ∞) + 1) f s :=
        (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (f := f) (s := s)
          (n := ((m : ℕ) : WithTop ℕ∞)) hs).2
          ⟨hdiff, fun hn => absurd hn (by simp), hgm m⟩
      simpa using h

theorem contDiffOn_primitive_Ioi0 (g : ℝ → ℝ)
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Set.Ioi 0))
    (hloc : ∀ z ∈ Set.Ioi (0 : ℝ), IntervalIntegrable g MeasureTheory.volume 0 z) :
    ∀ m : ℕ, ContDiffOn ℝ m (fun u : ℝ => ∫ x in (0 : ℝ)..u, g x) (Set.Ioi 0) := by
  refine contDiffOn_of_hasDerivAt isOpen_Ioi ?_ hg
  intro u hu
  have hc : ContinuousOn g (Set.Ioi (0 : ℝ)) := contDiffOn_zero.mp (hg 0)
  exact intervalIntegral.integral_hasDerivAt_right (hloc u hu)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi u hu)
    (hc.continuousAt (isOpen_Ioi.mem_nhds hu))

end Work.FTS.EllipticEst.Cert.GsingSmooth
