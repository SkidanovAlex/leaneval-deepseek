import Mathlib
import Submission.Work.Diff.STE.B3.BNorm_J_le_uniform
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.Lead.J_tendsto
import Submission.Work.Diff.STE.Lead.Gal.hasDerivAt_galE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

open Filter Set
open scoped BigOperators

/-! ## Two `T2Space`-free copies of smoothness lemmas about the Friedrichs mollifier

The chain `ENormB ≤ BNorm ≤ BNorm ≤ ENormB` of `galE_J_bounded` needs the smoothness of the chart
components of `D.J ρ ε h` (`Work.Diff.STE.Lead.R_J_contDiff`, in `Lead/J_tendsto.lean`).  That
lemma is stated in a section carrying `[T2Space M] [I.Boundaryless] [CompactSpace M]`, which the
target statement does not have.  Lean keeps *instance-implicit* section variables in the signature
even when the proof does not use them, so the three lemmas below are literal copies of the ones in
`Lead/J_tendsto.lean` (with the same proofs) freed of those three hypotheses. -/

/-- A smooth coefficient composed with the chart transition is smooth: the transition is only
smooth on the open set `goodSet`, which contains the `tsupport` of the coefficient.  (Copy of
`Work.Diff.STE.Lead.contDiff_comp_tMapFun`, without the unused section instances.) -/
lemma contDiff_comp_tMapFun_noInst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (G : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGgood : tsupport G ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)
    (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z => G z * u (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport G
  · have hT : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z :=
      ((Work.Diff.STE.B3.goodSet_smooth_noT2 (I := I) (M := M) D i j).2.1).contDiffAt
        ((Work.Diff.STE.B3.goodSet_smooth_noT2 (I := I) (M := M) D i j).1.mem_nhds (hGgood hz))
    exact (hG.contDiffAt).mul (hu.contDiffAt.comp z hT)
  · have hev : G =ᶠ[nhds z] (fun _ => (0 : ℂ)) := notMem_tsupport_iff_eventuallyEq.mp hz
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with w hw
    rw [hw, zero_mul]

/-- The Friedrichs truncation `STruncR ρ ε f` of a smooth function supported in the open cube is
smooth.  (Copy of `Work.Diff.STE.Lead.contDiff_STruncR`.) -/
lemma contDiff_STruncR_noInst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (ε : ℝ)
    (f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hρ : ∀ y, ‖ρ y‖ ≤ 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => Work.Diff.STE.B3Data.STruncR ρ ε f z) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (⇑Complex.reCLM ∘ (Work.Diff.STE.STruncC ρ ε f : (Fin (Module.finrank ℝ E) → ℝ) → ℂ)) :=
    (Complex.reCLM.contDiff).comp
      (Work.Diff.STE.B3.STruncC_contDiff_periodic ρ hρ ε f hf hfsupp).1
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => (Work.Diff.STE.STruncC ρ ε f z).re) := by
    convert h1 using 1
    funext z
    rfl
  simpa only [Work.Diff.STE.B3Data.STruncR, Work.Diff.STE.STruncC, Complex.ofReal_re] using h2

/-- **The chart components of `J ρ ε h` are smooth** whenever those of `h` are.  (Copy of
`Work.Diff.STE.Lead.R_J_contDiff`, without the unused section instances.) -/
lemma R_J_contDiff_noInst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (D.R i h c d))
    (hρ : ∀ y : Fin (Module.finrank ℝ E) → ℝ, ‖ρ y‖ ≤ 1)
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (D.R j (D.J ρ ε h) a b) := by
  have hJeq : D.J ρ ε h = ∑ i : ι₀, D.Rstar i (Work.Diff.STE.B3.truncComp D ρ ε h i) := by
    rw [Work.Diff.STE.B3Data.J]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
  rw [hJeq]
  have hpt : ∀ z, D.R j (∑ i : ι₀, D.Rstar i (Work.Diff.STE.B3.truncComp D ρ ε h i)) a b z
      = ∑ i : ι₀, D.R j (D.Rstar i (Work.Diff.STE.B3.truncComp D ρ ε h i)) a b z := fun z => by
    simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Finset.sum_apply, sum_apply,
      Finset.mul_sum]
  have hsum0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun z => ∑ i : ι₀, D.R j (D.Rstar i (Work.Diff.STE.B3.truncComp D ρ ε h i)) a b z) := by
    refine ContDiff.sum fun i _ => ?_
    obtain ⟨G, hGsm, hGsupp, hGcomp, hGgood, hid⟩ :=
      Work.Diff.STE.B3.bump_expansion_fixed D i j a b (Work.Diff.STE.B3.closure_Omega_goodSet D i j)
        ((Work.Diff.STE.B3.goodSet_smooth_noT2 D i j).1)
        (fun c d => (Work.Diff.STE.B3.goodSet_smooth_noT2 D i j).2.2 a b c d)
    have hsm2 : ∀ c d, ContDiff ℝ (⊤ : ℕ∞)
        (fun z => ((Work.Diff.STE.B3.truncComp D ρ ε h i c d z : ℝ) : ℂ)) := fun c d =>
      Complex.ofRealCLM.contDiff.comp (by
        have h2 : ContDiff ℝ (⊤ : ℕ∞)
            (⇑Complex.reCLM ∘ (Work.Diff.STE.STruncC ρ ε (D.R i h c d) :
              (Fin (Module.finrank ℝ E) → ℝ) → ℂ)) :=
          (Complex.reCLM.contDiff).comp (Work.Diff.STE.B3.STruncC_contDiff_periodic ρ hρ ε
            (D.R i h c d) (hsm i c d) (Work.Diff.STE.B3.R_support_cube D h i c d)).1
        convert h2 using 1
        funext z
        rfl)
    have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ c, ∑ d, G c d z *
        ((Work.Diff.STE.B3.truncComp D ρ ε h i c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) : ℝ) : ℂ)) := by
      refine ContDiff.sum fun c _ => ContDiff.sum fun d _ => ?_
      exact contDiff_comp_tMapFun_noInst (I := I) (M := M) D i j (G c d) (hGsm c d)
        (hGgood c d) _ (hsm2 c d)
    have hre0 : ContDiff ℝ (⊤ : ℕ∞) (⇑Complex.reCLM ∘ (fun z => ∑ c, ∑ d, G c d z *
        ((Work.Diff.STE.B3.truncComp D ρ ε h i c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) : ℝ) : ℂ))) :=
      (Complex.reCLM.contDiff).comp hsum
    have hre : ContDiff ℝ (⊤ : ℕ∞) (fun z => (∑ c, ∑ d, G c d z *
        ((Work.Diff.STE.B3.truncComp D ρ ε h i c d
          (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) : ℝ) : ℂ)).re) := by
      convert hre0 using 1
      funext z
      rfl
    convert hre using 1
    funext z
    have hz := hid (Work.Diff.STE.B3.truncComp D ρ ε h i) z
    rw [← hz, Complex.ofReal_re]
  convert hsum0 using 1
  funext z
  exact hpt z

/-- **`ε`-uniform boundedness of the Friedrichs mollifier `D.J ρ ε` in the physical energy.**
`D.ENormB k` is the physical `Hᵏ` energy of a section (`B3/BNorm_ENormB_equiv.lean`), `D.J ρ ε` the
chartwise mollifier (`B3/Comp.lean`).  Claim: there is a constant `C` — depending only on `D`, `k`
and the `ε`-free bound `‖ρ‖ ≤ 1` — such that for every `ε ∈ (0,1]` and every section `h` with `C^∞`
localised components,

  `D.ENormB k (D.J ρ ε h) ≤ C * (D.ENormB k h + D.ENormB 0 h)`.

PROOF ROUTE (all ingredients proved, sorry-free):
* `Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic` (∃C outside the ∀f, so uniform): for `C^∞`,
  `1`-periodic `f`, `ENormSq k f ≤ C₁ * CSq k (fourierCoeff f)`.  Summed over the components
  (`i,a,b`) this gives `D.ENormB k (D.J ρ ε h) ≤ C₁ * D.BNorm k (D.J ρ ε h)`, provided the
  components of `D.J ρ ε h` are `C^∞` and `1`-periodic.  For that smoothness use
  `Work.Diff.STE.Lead.R_J_contDiff` (`Lead/J_tendsto.lean`, sorry-free), which derives
  `ContDiff ⊤ (D.R i (D.J ρ ε h) a b)` from `ContDiff ⊤ (D.R i h a b)` and `‖ρ‖ ≤ 1` alone (no
  support hypothesis `hρ0` needed); `Rper_contDiff_periodic_of_R_contDiff` gives periodicity.
* `Work.Diff.STE.B3.BNorm_J_le_uniform`: `D.BNorm k (D.J ρ ε h) ≤ C₂ * D.BNorm k h` with `C₂`
  independent of `ε ∈ (0,1]` (hypotheses `‖ρ‖ ≤ 1` and `finrank ℝ E < 2 * k`).
* `Work.Diff.STE.B3.BNorm_le_ENormB` (uniform in the component via `Work.Diff.STE.CSq_le_ENormSq`):
  `D.BNorm k h ≤ C₃ * (D.ENormB k h + D.ENormB 0 h)`; the needed `ContDiff ℝ k` of the periodised
  components follows from the hypothesis `ContDiff ℝ ⊤ (D.R i h a b)`.

Then `C := C₁ * C₂ * C₃` is `ε`-free and uniform in `h`.
(Consumer: `Work.Diff.STE.Lead.Gal.galE_apriori`, to bound the energy of the foreground
`u~ = D.J ρ ε (galState …)` by `C * galE`.) -/
theorem galE_J_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (hk : Module.finrank ℝ E < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
          (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)) →
          D.ENormB k (D.J ρ ε h) ≤ C * (D.ENormB k h + D.ENormB 0 h) := by
  classical
  obtain ⟨C₁, hC₁nn, hC₁⟩ :=
    Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := Fin (Module.finrank ℝ E)) k
  obtain ⟨C₂, hC₂nn, hC₂⟩ := Work.Diff.STE.B3.BNorm_J_le_uniform D ρ hρ k hk
  obtain ⟨C₃, hC₃nn, hC₃⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C₁ * C₂ * C₃, by positivity, ?_⟩
  intro ε hε hε1 h hsm
  -- Step A: the physical energy of `J ρ ε h` is controlled by its Fourier-side norm.
  have hA : D.ENormB k (D.J ρ ε h) ≤ C₁ * D.BNorm k (D.J ρ ε h) := by
    rw [Work.Diff.STE.B3Data.ENormB, Work.Diff.STE.B3Data.BNorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have hcomp : ContDiff ℝ (⊤ : ℕ∞) (D.R i (D.J ρ ε h) a b) :=
      R_J_contDiff_noInst D ρ h hsm hρ i a b ε
    obtain ⟨hcd, hper⟩ :=
      Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (D.J ρ ε h) a b hcomp
    exact hC₁ (D.Rper i (D.J ρ ε h) a b) hcd hper
  -- Step B: the Fourier-side norm of `J ρ ε h` is controlled by that of `h`, uniformly in `ε`.
  have hB : D.BNorm k (D.J ρ ε h) ≤ C₂ * D.BNorm k h := hC₂ ε hε hε1 h hsm
  -- Step C: the Fourier-side norm of `h` is controlled by its physical energy.
  have hC : D.BNorm k h ≤ C₃ * (D.ENormB k h + D.ENormB 0 h) := by
    have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
          ≤ C₃ * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
            + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
      intro i a b
      obtain ⟨hcd, hper⟩ := Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b
        (hsm i a b)
      exact hC₃ (D.Rper i h a b) (hcd.of_le (by
        show ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)) hper
    have hsum : D.BNorm k h ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
        ∑ b : Fin (Module.finrank ℝ E),
          C₃ * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
            + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum fun b _ => hterm i a b
    have hsplit : (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E),
          ∑ b : Fin (Module.finrank ℝ E),
          C₃ * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
            + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)))
        = C₃ * (D.ENormB k h + D.ENormB 0 h) := by
      simp only [Work.Diff.STE.B3Data.ENormB, Finset.sum_add_distrib, ← Finset.mul_sum]
    rwa [hsplit] at hsum
  calc D.ENormB k (D.J ρ ε h) ≤ C₁ * D.BNorm k (D.J ρ ε h) := hA
    _ ≤ C₁ * (C₂ * D.BNorm k h) := mul_le_mul_of_nonneg_left hB hC₁nn
    _ ≤ C₁ * (C₂ * (C₃ * (D.ENormB k h + D.ENormB 0 h))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC hC₂nn) hC₁nn
    _ = (C₁ * C₂ * C₃) * (D.ENormB k h + D.ENormB 0 h) := by ring

end Work.Diff.STE.Lead.Gal
