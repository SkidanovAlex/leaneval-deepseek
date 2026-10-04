import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.QkDef
import Submission.Work.Diff.STE.B3.contDiff_lamCoeff_seriesFun
import Submission.Work.Diff.STE.B3.bump_expansion_fixed
import Submission.Work.Diff.STE.B3.closure_Omega_goodSet
import Submission.Work.Diff.STE.B3.goodSet_smooth_noT2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: smoothness of the chart components of `Qk D k h`

`Qk D k h` (`B3/QkDef.lean`) is the section whose `i`-th component function is the Fourier
multiplier with symbol `λ(m)^k` (`λ` = symbol of the flat Laplacian) applied to the periodised
localised component `D.Rper i h a b`.  Explicitly

`Qk D k h = Σ_i D.Rstar i (Λ^k (Rper i h))`.

This file proves that whenever the chart components `D.R i h a b` of `h` are `C^∞`, so are the
chart components `D.R i (Qk D k h) a b` of `Qk D k h` — the regularity hypothesis needed by the
Fourier estimate of Layer B3 for `Qk`.

**Route.**

* `D.R` is additive in the section (`B3Data.R` multiplies the chart matrix of the section by the
  fixed weight `ψ i √(dens i)`), so

  `D.R i (Σ_j Rstar j (u j)) a b = Σ_j D.R i (Rstar j (u j)) a b`   (pointwise),

  and it suffices to treat each summand `D.R i (Rstar j (u j)) a b` separately.
* The multiplier family `Λ^k (Rper i f)` is `C^∞` — exactly
  `Work.Diff.STE.B3.contDiff_lamCoeff_seriesFun`.
* For the reconstruction, the *bump expansion* `Work.Diff.STE.B3.bump_expansion_fixed` rewrites

  `D.R i (D.Rstar j u) a b z = (Σ_{cd} G_{cd} z · u_{cd} (tMapFun D j i z)).re`

  *for every* family `u`, with `G_{cd}` smooth and supported in `goodSet D j i`, the open set on
  which the chart transition `tMapFun D j i = coord_i ∘ pt_j` is `C^∞`
  (`Work.Diff.STE.B3.goodSet_smooth_noT2`).  The localisation is what makes the identity
  independent of the junk values of the partial charts: on the support of `G_{cd}` the transition is
  the genuine chart change.
* So each summand is smooth as soon as the `u_{cd}` are (`contDiff_comp_tMapFun` below, the copy of
  the same elementary argument as `Work.Diff.STE.Lead.contDiff_comp_tMapFun`).

Everything is proved without `[T2Space M]` / `[I.Boundaryless]`: the Layer B3 data forces `M` to be
Hausdorff (`Work.Diff.STE.B3.t2Space_of_B3Data`, used inside `closure_Omega_goodSet`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators Topology
open Filter

namespace Work.Diff.STE.B3.SymCalcStep2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **A smooth function supported in `goodSet`, composed with the chart transition, is smooth.**

`tMapFun D i j = coord_i ∘ pt_j` is `C^∞` on the open set `goodSet D i j` (and junk elsewhere), but
the factor `G` vanishes off its topological support, which lies in `goodSet`. -/
lemma contDiff_comp_tMapFun
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (G : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGgood : tsupport G ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)
    (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z => G z * u (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport G
  · have hgs := goodSet_smooth_noT2 (I := I) (M := M) D i j
    have hT : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z :=
      hgs.2.1.contDiffAt (hgs.1.mem_nhds (hGgood hz))
    exact (hG.contDiffAt).mul (hu.contDiffAt.comp z hT)
  · have hev : G =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hz
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with w hw
    rw [hw, zero_mul]

/-- **The chart components of a finite sum of reconstructions are smooth** whenever the coefficient
families are: `D.R i (Σ_j Rstar j (u j)) a b` is `C^∞` if every `u j c d` is. -/
lemma R_Rstar_sum_contDiff
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (u : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hu : ∀ (j : ι₀) (c d : Fin (Module.finrank ℝ E)), ContDiff ℝ (⊤ : ℕ∞) (u j c d))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (D.R i (∑ j : ι₀, D.Rstar j (u j)) a b) := by
  -- `R` is additive in the section, so the composite splits into a finite sum
  have hpt : ∀ z, D.R i (∑ j : ι₀, D.Rstar j (u j)) a b z
      = ∑ j : ι₀, D.R i (D.Rstar j (u j)) a b z := fun z => by
    simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Finset.sum_apply, sum_apply,
      Finset.mul_sum]
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ j : ι₀, D.R i (D.Rstar j (u j)) a b z) := by
    refine ContDiff.sum fun j _ => ?_
    -- the bump expansion of the single reconstruction
    obtain ⟨G, hGsm, _hGsupp, _hGcomp, hGgood, hid⟩ :=
      Work.Diff.STE.B3.bump_expansion_fixed (I := I) (M := M) D j i a b
        (Work.Diff.STE.B3.closure_Omega_goodSet (I := I) (M := M) D j i)
        ((goodSet_smooth_noT2 (I := I) (M := M) D j i).1)
        (fun c d => (goodSet_smooth_noT2 (I := I) (M := M) D j i).2.2 a b c d)
    have hUc : ∀ c d : Fin (Module.finrank ℝ E),
        ContDiff ℝ (⊤ : ℕ∞) (fun z => ((u j c d z : ℝ) : ℂ)) := fun c d =>
      Complex.ofRealCLM.contDiff.comp (hu j c d)
    have hGs : ContDiff ℝ (⊤ : ℕ∞)
        (fun z => ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          G c d z *
            ((u j c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D j i z) : ℝ) : ℂ)) := by
      refine ContDiff.sum fun c _ => ?_
      refine ContDiff.sum fun d _ => ?_
      exact contDiff_comp_tMapFun (I := I) (M := M) D j i (G c d) (hGsm c d) (hGgood c d) _
        (hUc c d)
    have hre0 := (Complex.reCLM.contDiff).comp hGs
    have hre : ContDiff ℝ (⊤ : ℕ∞)
        (fun z => (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          G c d z *
            ((u j c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D j i z) : ℝ) : ℂ)).re) := by
      convert hre0 using 1
      funext z
      rfl
    convert hre using 1
    funext z
    have hz := hid (u j) z
    rw [← hz, Complex.ofReal_re]
  convert hsum using 1
  funext z
  exact hpt z

theorem R_Qk_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (f : Work.Diff.STE.Bil (I := I) (M := M))
    (hf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b)) :
    ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Work.Diff.STE.B3.Qk D k f) a b) := by
  intro i a b
  -- `Qk D k f` *is* the finite sum of reconstructions it is defined as
  refine R_Rstar_sum_contDiff (I := I) (M := M) D
    (fun (j : ι₀) (c d : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ) =>
      (Work.Diff.STE.seriesFun (fun m : Fin (Module.finrank ℝ E) → ℤ =>
        ((Work.Diff.STE.B3.lamSym (E := E) m ^ k : ℝ) : ℂ) *
          Work.Diff.STE.fourierCoeff (D.Rper j f c d) m) z).re) ?_ i a b
  intro j c d
  -- the multiplier family `Λ^k (Rper j f c d)` is `C^∞`
  have hF := Work.Diff.STE.B3.contDiff_lamCoeff_seriesFun (I := I) (M := M) D k f j c d
    (hf j c d)
  have h1 := (Complex.reCLM.contDiff).comp hF
  convert h1 using 1
  funext z
  rfl

end Work.Diff.STE.B3.SymCalcStep2
