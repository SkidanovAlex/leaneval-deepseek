import Submission.Work.Mori.PeriodHom
import Submission.Commons.Topology.Covering.section_of_monodromy_eq_self_weak

/-!
# Vanishing period ⟹ a global holomorphic conjugate

`Work.Mori.exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero` is
`Submission.exists_holomorphicOnX_re_of_harmonic` with its hypothesis
`Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)` replaced by the weaker (and in practice more
useful) hypothesis that the *period homomorphism of `u` itself* vanishes:

* `Work.Mori.conjPeriodHomOf hu x = 0` ⟹ all periods vanish
  (`Submission.conjPeriod`), ⟹ the monodromy of the conjugate étale space fixes the fibre point
  (`Submission.monodromy_eq_conjFiberShift`), ⟹ there is a global section
  (`Commons.Topology.Covering.section_of_monodromy_eq_self_weak`), ⟹ `y ↦ u y + i σ y` is global
  holomorphic with real part `u`.

Only the first step differs from the library's proof; the rest is that proof verbatim.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set

namespace Work.Mori

/-- **Vanishing period ⟹ a global holomorphic conjugate.** -/
theorem exists_holomorphic_conjugate_of_conjPeriodHomOf_eq_zero
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {u : X → ℝ}
    (hu : Submission.HarmonicOnX u Set.univ) (x : X) (hzero : conjPeriodHomOf hu x = 0) :
    ∃ F : X → ℂ, Submission.HolomorphicOnX F Set.univ ∧ ∀ y, (F y).re = u y := by
  letI : TopologicalSpace (X × ℝ) := Submission.conjTopology u
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := X)
  have cov : IsCoveringMap (Prod.fst : X × ℝ → X) := Submission.isCoveringMap_fst_conjTopology hu
  have hshift : ∀ c : ℝ, Continuous (Submission.conjShift (X := X) c) :=
    fun c => Submission.continuous_conjShift c
  have hper : ∀ γ : FundamentalGroup X x,
      Submission.conjPeriod x (Submission.conjFiberPt x 0) cov γ = 0 := by
    intro γ
    have h0 : Submission.conjPeriodHom x (Submission.conjFiberPt x 0) cov hshift = 0 := hzero
    have := congrFun (congrArg (fun f : Additive (FundamentalGroup X x) →+ ℝ =>
      (f : Additive (FundamentalGroup X x) → ℝ)) h0) (Additive.ofMul γ)
    simpa [Submission.conjPeriodHom, Submission.conjPeriod] using this
  have hmono : ∀ γ : FundamentalGroup X x,
      cov.monodromy γ (Submission.conjFiberPt x 0) = Submission.conjFiberPt x 0 := by
    intro γ
    rw [Submission.monodromy_eq_conjFiberShift cov x (Submission.conjFiberPt x 0) γ, hper γ]
    refine Subtype.ext (Prod.ext rfl ?_)
    simp [Submission.conjFiberShift, Submission.conjFiberPt]
  obtain ⟨σ, hσ0, hσp⟩ :=
    Commons.Topology.Covering.section_of_monodromy_eq_self_weak cov (x, 0) (fun γ => hmono γ)
  refine ⟨fun y => (u y : ℂ) + Complex.I * (σ y).2, ?_, ?_⟩
  · intro y _
    obtain ⟨B, G, hB, hyB, hG, hreG⟩ := Submission.exists_conjData hu y
    set t : ℝ := (σ y).2 - (G y).im with htdef
    set G' : X → ℂ := fun z => G z + Complex.I * (t : ℂ) with hG'def
    have hIre : (Complex.I * (t : ℂ)).re = 0 := by simp
    have hIim : (Complex.I * (t : ℂ)).im = t := by simp
    have hG're : ∀ z ∈ B, (G' z).re = u z := by
      intro z hz
      rw [hG'def, Complex.add_re, hreG z hz, hIre, add_zero]
    have hG'hol : Submission.HolomorphicOnX G' B := by
      rw [hG'def]
      exact (Submission.holomorphicOnX_add_const hG hreG (Complex.I * (t : ℂ))).1
    have hsym : σ y ∈ Submission.conjGraph B G' := by
      refine ⟨?_, ?_⟩
      · show (σ y).1 ∈ B
        rw [hσp y]; exact hyB
      · show (σ y).2 = (G' (σ y).1).im
        rw [hG'def, hσp y, Complex.add_im, hIim, htdef]
        ring
    have hnbhd : ∀ᶠ z in 𝓝 y, σ z ∈ Submission.conjGraph B G' :=
      (σ.continuous.continuousAt.eventually
        ((Submission.isOpen_conjGraph hB hG'hol hG're).mem_nhds hsym))
    have hev : (fun z : X => (u z : ℂ) + Complex.I * (σ z).2) =ᶠ[𝓝 y] G' := by
      filter_upwards [hnbhd] with z hz
      have hz2 : (σ z).2 = (G' z).im := by
        have h1 : (σ z).1 ∈ B ∧ (σ z).2 = (G' (σ z).1).im := hz
        rw [hσp z] at h1
        exact h1.2
      have hzB : z ∈ B := by rw [← hσp z]; exact hz.1
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, add_zero]
        rw [hG're z hzB]
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          Complex.ofReal_re, Complex.ofReal_im, zero_add]
        rw [hz2]
    rw [Submission.HolomorphicOnXAt]
    have hcyt : ((chartAt ℂ y) y) ∈ (chartAt ℂ y).target :=
      (chartAt ℂ y).map_source (mem_chart_source ℂ y)
    have hyc : (chartAt ℂ y).symm ((chartAt ℂ y) y) = y :=
      (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hcont : ContinuousAt (chartAt ℂ y).symm ((chartAt ℂ y) y) :=
      (chartAt ℂ y).continuousAt_symm hcyt
    have hev2 : (fun z : X => (u z : ℂ) + Complex.I * (σ z).2)
        =ᶠ[𝓝 ((chartAt ℂ y).symm ((chartAt ℂ y) y))] G' := by
      rw [hyc]; exact hev
    have hev' : ((fun z : X => (u z : ℂ) + Complex.I * (σ z).2) ∘ (chartAt ℂ y).symm)
        =ᶠ[𝓝 ((chartAt ℂ y) y)] (G' ∘ (chartAt ℂ y).symm) :=
      hcont.eventually hev2
    exact AnalyticAt.congr (hG'hol y hyB) hev'.symm
  · intro y
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_one, mul_zero, sub_zero, zero_mul, add_zero]

end Work.Mori
