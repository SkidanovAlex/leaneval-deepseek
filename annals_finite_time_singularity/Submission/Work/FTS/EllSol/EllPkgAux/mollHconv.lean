import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.EllSol.EllPkgAux

/-- **Change of variables in the double convolution.**  The reflection `x ↦ a - x` of `ℝ`
preserves Lebesgue measure, so the double iterated integral of the mollifying kernel `k`
against a datum `H` can be written with the arguments of `H` reflected.  This is the passage
between the two orders in which the two-dimensional convolution is written. -/
theorem integral_reflect_pair (k : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (a b : ℝ) :
    (∫ t' : ℝ, k (a - t') * (∫ s : ℝ, k (b - s) * H t' s))
      = ∫ u : ℝ, ∫ v : ℝ, k u * k v * H (a - u) (b - v) := by
  have hinner : ∀ t' : ℝ, (∫ s : ℝ, k (b - s) * H t' s) = ∫ v : ℝ, k v * H t' (b - v) := by
    intro t'
    simpa using (MeasureTheory.integral_sub_left_eq_self
        (fun v : ℝ => k v * H t' (b - v)) MeasureTheory.volume b)
  have hstep1 : (∫ t' : ℝ, k (a - t') * (∫ s : ℝ, k (b - s) * H t' s))
      = ∫ t' : ℝ, k (a - t') * (∫ v : ℝ, k v * H t' (b - v)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
    simp only [hinner t']
  rw [hstep1]
  have hstep2 : (∫ t' : ℝ, k (a - t') * (∫ v : ℝ, k v * H t' (b - v)))
      = ∫ u : ℝ, k u * (∫ v : ℝ, k v * H (a - u) (b - v)) := by
    simpa using (MeasureTheory.integral_sub_left_eq_self
        (fun u : ℝ => k u * (∫ v : ℝ, k v * H (a - u) (b - v))) MeasureTheory.volume a)
  rw [hstep2]
  have hpt : ∀ u : ℝ, k u * (∫ v : ℝ, k v * H (a - u) (b - v))
      = ∫ v : ℝ, k u * k v * H (a - u) (b - v) := by
    intro u
    rw [← MeasureTheory.integral_const_mul (k u) (fun v : ℝ => k v * H (a - u) (b - v))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    ring
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)

theorem mollHconv (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) (hderiv : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ) (Real.log z) = Work.Spaces.Dz (Work.Spaces.pth G) z θ) (hid : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ = ∫ t' : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (Real.log z - t') * (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t' s)) (hlim : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → Filter.Tendsto (fun t : ℝ => ∫ u : ℝ, ∫ v : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t u * Work.FTS.EllSol.EllPkgAux.sKerd t v * Work.FTS.EllSol.EllPkgAux.Hxyc G (Real.log z - u) (θ - v)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv (fun x' => deriv (fun y' => Work.FTS.EllSol.EllPkgAux.Hxyc G x' y') θ) (Real.log z)))) : ∀ z : ℝ, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), Filter.Tendsto (fun n : ℕ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Filter.atTop (nhds ((Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)) := by
  intro z hz
  -- The endpoints of `Iθ = [0, π/2]` are null, so almost everywhere `θ` lies in the open
  -- interval where both `hlim` and `hderiv` are available.
  have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))),
      θ ∈ Set.Ioo 0 (Real.pi / 2)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null (t := ({(0 : ℝ), Real.pi / 2} : Set ℝ)) ?_ ?_
    · intro θ hθ
      simp only [Set.mem_ofPred_eq, not_imp, Set.mem_Icc, Set.mem_Ioo, not_and_or,
        not_lt] at hθ
      obtain ⟨⟨h1, h2⟩, h3⟩ := hθ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases h3 with h3 | h3
      · exact Or.inl (le_antisymm h3 h1)
      · exact Or.inr (le_antisymm h2 h3)
    · exact Set.Finite.measure_zero (Set.Finite.insert _ (Set.finite_singleton _)) _
  filter_upwards [hae] with θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- Along the diagonal sequence the double mollification is *exactly* the double convolution
  -- appearing in `hlim`.
  have hkey : ∀ n : ℕ,
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G
          (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ
        = ∫ u : ℝ, ∫ v : ℝ,
            Work.FTS.EllSol.EllPkgAux.sKerd (Work.FTS.EllSol.EllPkgAux.tseq n) u
              * Work.FTS.EllSol.EllPkgAux.sKerd (Work.FTS.EllSol.EllPkgAux.tseq n) v
              * Work.FTS.EllSol.EllPkgAux.Hxyc G (Real.log z - u) (θ - v) := by
    intro n
    rw [hid (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq_pos n)
      (Work.FTS.EllSol.EllPkgAux.tseq_le_half n) z hz θ hθIθ]
    exact integral_reflect_pair (Work.FTS.EllSol.EllPkgAux.sKerd
      (Work.FTS.EllSol.EllPkgAux.tseq n)) (Work.FTS.EllSol.EllPkgAux.Hxyc G)
      (Real.log z) θ
  have hseq : Filter.Tendsto Work.FTS.EllSol.EllPkgAux.tseq Filter.atTop
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨Work.FTS.EllSol.EllPkgAux.tendsto_tseq,
      Filter.Eventually.of_forall fun n => Work.FTS.EllSol.EllPkgAux.tseq_pos n⟩
  have hcomp := (hlim z hz θ hθ.1 hθ.2).comp hseq
  rw [hderiv z hz θ hθ.1 hθ.2] at hcomp
  have hconv : Filter.Tendsto (fun n : ℕ =>
      Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G
        (Work.FTS.EllSol.EllPkgAux.tseq n) (Work.FTS.EllSol.EllPkgAux.tseq n))) z θ)
      Filter.atTop (nhds (Work.Spaces.Dz (Work.Spaces.pth G) z θ)) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hkey n).symm) hcomp
  exact (hconv.pow 2).mul_const (Work.FTS.EllipticEst.thEta θ)

end Work.FTS.EllSol.EllPkgAux
