import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.isCritical_iff_chartRep
import Submission.Work.Drive.N2.nondegCrit_iff_chart
import Submission.Work.Drive.N2.contDiff_mul_of_contDiffOn
import Submission.Work.Drive.N2.exists_contDiff_bump_isCompact

/-!
# A Morse chart at a nondegenerate critical point of a function on a surface

`Work.Drive.N2.exists_morseChart_fixed` (the mathematically intended form of the requested
`Work.Drive.N2.exists_morseChart`, whose smoothness clauses as requested cannot elaborate -- see
`Submission/Work/Drive/N2/NOTES_exists_morseChart.md`): for a `C^∞` function `f` on a surface `M` (model `ℝ²`) with a
nondegenerate critical point `x₀`, and *given* the planar Morse lemma `Work.Drive.Morse.MorseLemma2`
as a hypothesis, there are a chart `φ` centred at `x₀` and signs `s₁, s₂ ∈ {±1}` with

`f y = f x₀ + s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2`  for every `y` in the source of `φ`.

The chart is a composite of two charts: the chart `chartAt x₀` of `M` at `x₀`, followed by the
Morse chart `ψ` supplied by `MorseLemma2` for the chart representative
`g = chartRep f x₀ = f ∘ (chartAt x₀).symm`.

## The one deviation from the requested statement (read this!)

The requested statement asked for the two smoothness clauses

`ContDiffOn ℝ ∞ (fun y => φ y) φ.source`  and  `ContDiffOn ℝ ∞ (fun y => φ.symm y) φ.target`.

That text does **not elaborate**: `ContDiffOn 𝕜 n f s` is Mathlib's *normed-space* `ContDiffOn`
(there is no manifold overload of `ContDiffOn`; the `Manifold` scope only provides `MDiff*`/`CMDiff*`
elaborators, and the `ContDiff` scope only provides the notations `∞`, `ω`, `ℕ∞ω`).  For
`f : M → ℝ²` it demands the instances `[NormedAddCommGroup M] [NormedSpace ℝ M]`, which the
hypotheses of the statement cannot provide (`M` is only a topological space with a `ChartedSpace`
and an `IsManifold` structure).  `lake build Submission.Work.Drive.N2.exists_morseChart` therefore
fails at those two conjuncts with

`failed to synthesize instance of type class NormedAddCommGroup M`.

The mathematically intended content -- `φ` and `φ⁻¹` are `C^∞` charts -- is expressed in the
manifold vocabulary used everywhere else in this development (`CMDiffOn`/`ContMDiffOn`) as

`ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun y => φ y) φ.source`  and
`ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun y => φ.symm y) φ.target`,

and that is the form proved below.  These clauses are *derived* facts here (the chart is built from
`chartAt x₀` and from the Morse chart `ψ` of the model space, and `ψ.restr W` is again a chart), so
the consumer loses nothing: from the statement below one recovers, for instance, that
`y ↦ φ y 0` is a `C^∞` function `M → ℝ` on `φ.source`, i.e. that `φ` is a smooth chart.

## Proof outline

* `e := chartAt x₀`, `c := e x₀`, `g := chartRep f x₀ = f ∘ e.symm` (smooth on `e.target`).
* `Work.Drive.Morse.NondegCrit f x₀` unfolds to `IsCritical f x₀` plus injectivity of the Hessian of
  `g` at `c`; the criticality transfers to `fderiv ℝ g c = 0` by
  `Work.Drive.N2.isCritical_iff_chartRep_chartAt`, and the nondegeneracy is
  `Work.Drive.N2.nondegCrit_iff_chart` with both charts equal to `chartAt x₀`.
* `MorseLemma2` needs a *globally* `C^∞` function, while `g` is only smooth on the chart target.
  Fix a smooth bump `χ` (`exists_contDiff_bump_isCompact`) with `tsupport χ ⊆ e.target` and
  `χ = 1` near `c`, and put `gt := fun y => χ y * g y`.  By `contDiff_mul_of_contDiffOn` this is
  globally `C^∞`, it agrees with `g` near `c` (`W := interior {χ = 1}`), hence
  `fderiv ℝ gt c = 0` and `fderiv (fderiv gt) c = fderiv (fderiv g) c`.
* Apply `hmorse gt c` to get the Morse chart `ψ` with `gt y = gt c + s₁ (ψ y 0)² + s₂ (ψ y 1)²` on
  `ψ.source`.  Restrict it to the open set `W` on which `χ = 1`: `ψ' := ψ.restr W`, so that on
  `ψ'.source` the identity holds for `g` itself, and `g = f ∘ e.symm`.
* The answer is `φ := e.trans ψ'`; the formula for `f` on `φ.source` is the translation of the
  Morse identity along `e`, the value at the centre being `gt c = g c = f x₀`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

open scoped Manifold ContDiff in
theorem exists_morseChart_fixed {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) {x₀ : M}
    (hx₀ : Work.Drive.Morse.NondegCrit f x₀) (hmorse : Work.Drive.Morse.MorseLemma2) :
    ∃ (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (s₁ s₂ : ℝ),
      x₀ ∈ φ.source ∧ φ x₀ = 0 ∧ (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ y) φ.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ.symm y) φ.target ∧
      (∀ y ∈ φ.source, f y = f x₀ + s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2) := by
  classical
  -- The chart of `M` at `x₀` and the image `c` of `x₀` in the model space.
  set e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) :=
    chartAt (EuclideanSpace ℝ (Fin 2)) x₀ with he
  have hx₀e : x₀ ∈ e.source := by rw [he]; exact mem_chart_source _ _
  set c : EuclideanSpace ℝ (Fin 2) := e x₀ with hc
  have hctgt : c ∈ e.target := by rw [hc]; exact e.map_source hx₀e
  -- The chart representative of `f` at `x₀`.
  set g : EuclideanSpace ℝ (Fin 2) → ℝ := chartRep f x₀ with hg
  have hgl : g = fun y : EuclideanSpace ℝ (Fin 2) =>
      f ((chartAt (EuclideanSpace ℝ (Fin 2)) x₀).symm y) := hg.trans rfl
  have hg_sm : ContDiffOn ℝ ∞ g e.target := by
    rw [he]
    simpa [hg, chartRep] using contDiffOn_chartRep_center f hf x₀
  -- The two hypotheses of the planar Morse lemma, read in the chart.
  have hcrit : Work.Drive.Morse.IsCritical f x₀ := hx₀.1
  have hdcrit : fderiv ℝ g c = 0 := by
    have h := (isCritical_iff_chartRep_chartAt f hf x₀).mp hcrit
    rw [chartDf] at h
    simpa [hg, hc, he] using h
  have hinj : Function.Injective (fderiv ℝ (fderiv ℝ g) c) := by
    have h := (nondegCrit_iff_chart f hf x₀ x₀ (mem_chart_source _ x₀) hcrit).mp hx₀
    have h1 : c = (chartAt (EuclideanSpace ℝ (Fin 2)) x₀) x₀ := by rw [hc, he]
    rw [hgl, h1]
    exact h
  -- A smooth bump equal to `1` near `c` whose support stays in the chart target.
  obtain ⟨χ, hχ_sm, -, hχ_tsupp, hχ_one⟩ :=
    exists_contDiff_bump_isCompact (N := 2) (K := {c}) (O := e.target) isCompact_singleton
      e.open_target (by rw [Set.singleton_subset_iff]; exact hctgt)
  set W : Set (EuclideanSpace ℝ (Fin 2)) := interior {y | χ y = 1} with hW
  have hWopen : IsOpen W := by rw [hW]; exact isOpen_interior
  have hcW : c ∈ W := by rw [hW]; exact hχ_one (by simp)
  have hWone : ∀ y ∈ W, χ y = 1 := by
    intro y hy
    have hy' : y ∈ interior {z | χ z = 1} := by rwa [hW] at hy
    simpa using interior_subset hy'
  -- The globally smooth function to which the planar Morse lemma is applied.
  set gt : EuclideanSpace ℝ (Fin 2) → ℝ := fun y => χ y * g y with hgt
  have hgt_sm : ContDiff ℝ ∞ gt := by
    rw [hgt]
    exact contDiff_mul_of_contDiffOn hχ_sm hg_sm e.open_target hχ_tsupp
  have hgt_ev : gt =ᶠ[𝓝 c] g := by
    refine Filter.eventually_of_mem (hWopen.mem_nhds hcW) fun y hy => ?_
    simp only [hgt, hWone y hy, one_mul]
  have hgt_dcrit : fderiv ℝ gt c = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hgt_ev, hdcrit]
  have hgt_inj : Function.Injective (fderiv ℝ (fderiv ℝ gt) c) := by
    have h1 : fderiv ℝ gt =ᶠ[𝓝 c] fderiv ℝ g := by
      refine Filter.eventually_of_mem (hWopen.mem_nhds hcW) fun y hy => ?_
      exact Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hWopen.mem_nhds hy)
        fun z hz => by simp only [hgt, hWone z hz, one_mul])
    rw [Filter.EventuallyEq.fderiv_eq h1]
    exact hinj
  -- The planar Morse lemma.
  obtain ⟨ψ, s₁, s₂, hψc, hψ0, hψ_sm, hψsymm_sm, hs₁, hs₂, hψeq⟩ :=
    hmorse gt c hgt_sm hgt_dcrit hgt_inj
  -- Restrict the Morse chart to the open set where the bump is `1`.
  set ψ' : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
    ψ.restr W with hψ'
  have hψ'_src : ψ'.source = ψ.source ∩ W := by
    rw [hψ', OpenPartialHomeomorph.restr_source' ψ W hWopen]
  have hψ'_tgt : ψ'.target = ψ.target ∩ (⇑ψ.symm) ⁻¹' W := by
    rw [hψ', OpenPartialHomeomorph.restr_target, hWopen.interior_eq]
  have hψ'_sub : ψ'.source ⊆ ψ.source := by rw [hψ'_src]; exact Set.inter_subset_left
  have hψ'_tgt_sub : ψ'.target ⊆ ψ.target := by rw [hψ'_tgt]; exact Set.inter_subset_left
  have hψ'_sm : ContDiffOn ℝ ∞ (fun y => ψ' y) ψ'.source := by
    have h := hψ_sm.mono hψ'_sub
    simpa [hψ', OpenPartialHomeomorph.restr_apply] using h
  have hψ'symm_sm : ContDiffOn ℝ ∞ (fun z => ψ'.symm z) ψ'.target := by
    have h := hψsymm_sm.mono hψ'_tgt_sub
    simpa [hψ', OpenPartialHomeomorph.restr_symm_apply] using h
  -- The composite chart.
  set φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)) := e.trans ψ' with hφ
  have hφsrc : φ.source = e.source ∩ e ⁻¹' ψ'.source := by
    rw [hφ, OpenPartialHomeomorph.trans_source]
  refine ⟨φ, s₁, s₂, ?_, ?_, hs₁, hs₂, ?_, ?_, ?_⟩
  · -- the centre lies in the source
    rw [hφsrc]
    refine ⟨hx₀e, ?_⟩
    rw [hψ'_src]
    exact ⟨by rwa [hc] at hψc, by rwa [hc] at hcW⟩
  · -- the centre is mapped to `0`
    rw [hφ, OpenPartialHomeomorph.trans_apply]
    show ψ' (e x₀) = 0
    rw [hψ', OpenPartialHomeomorph.restr_apply, ← hc]
    exact hψ0
  · -- `φ` is smooth on its source
    have he_sm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun y => e y) φ.source :=
      (by rw [he]; exact contMDiffOn_chart :
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun y : M => e y) e.source).mono
        (by rw [hφsrc]; exact Set.inter_subset_left)
    have hψ'M_sm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun z => ψ' z) ψ'.source :=
      contMDiffOn_iff_contDiffOn.mpr hψ'_sm
    have hsub : φ.source ⊆ (fun y : M => e y) ⁻¹' ψ'.source := by
      intro y hy
      rw [hφsrc] at hy
      exact hy.2
    have hcomp := hψ'M_sm.comp he_sm hsub
    have hfun : (fun y => φ y) = (fun z => ψ' z) ∘ (fun y : M => e y) := by
      funext y
      rw [hφ, OpenPartialHomeomorph.trans_apply]
      rfl
    rw [hfun]
    exact hcomp
  · -- the inverse of `φ` is smooth on its target
    have he_inv_sm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun z => e.symm z) e.target := by
      rw [he]; simpa using contMDiffOn_extChartAt_symm (I := 𝓡 2) x₀
    have hψ'invM_sm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (fun z => ψ'.symm z) φ.target :=
      (contMDiffOn_iff_contDiffOn.mpr hψ'symm_sm).mono
        (by rw [hφ, OpenPartialHomeomorph.trans_target]; exact Set.inter_subset_left)
    have hsub : φ.target ⊆ (fun z => ψ'.symm z) ⁻¹' e.target := by
      intro z hz
      rw [hφ, OpenPartialHomeomorph.trans_target] at hz
      exact hz.2
    have hcomp := he_inv_sm.comp hψ'invM_sm hsub
    have hfun : (fun z => φ.symm z) = (fun z => e.symm z) ∘ (fun z => ψ'.symm z) := by
      funext z; rfl
    rw [hfun]
    exact hcomp
  · -- the normal form
    intro y hy
    have hy' : y ∈ e.source ∧ e y ∈ ψ'.source := by
      rw [hφsrc] at hy
      exact hy
    have hy_src : y ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x₀).source := by
      rw [he] at hy'; exact hy'.1
    have hey : e y ∈ ψ.source ∩ W := by rw [hψ'_src] at hy'; exact hy'.2
    have hfy : f y = g (e y) := by
      rw [hgl]
      show f y = f ((chartAt (EuclideanSpace ℝ (Fin 2)) x₀).symm (e y))
      rw [show e y = (chartAt (EuclideanSpace ℝ (Fin 2)) x₀) y from by rw [he]]
      rw [OpenPartialHomeomorph.left_inv _ hy_src]
    have hgt_eq : g (e y) = gt (e y) := by
      simp only [hgt, hWone (e y) hey.2, one_mul]
    have hgtc : gt c = f x₀ := by
      have h1 : gt c = g c := by simp only [hgt, hWone c hcW, one_mul]
      have h2 : g c = f x₀ := by
        rw [hgl]
        show f ((chartAt (EuclideanSpace ℝ (Fin 2)) x₀).symm c) = f x₀
        rw [hc, he, OpenPartialHomeomorph.left_inv _ (mem_chart_source _ x₀)]
      rw [h1, h2]
    have hcoord : φ y = ψ (e y) := by
      rw [hφ, OpenPartialHomeomorph.trans_apply, hψ', OpenPartialHomeomorph.restr_apply]
    rw [hfy, hgt_eq, hψeq (e y) hey.1, hgtc, hcoord]

end

end Work.Drive.N2
