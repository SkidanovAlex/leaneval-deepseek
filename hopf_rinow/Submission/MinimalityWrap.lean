import Submission.ModelMinimality
import Mathlib

/-!
# Radial geodesics minimise length among curves in the normal image (generic wrapper)

Task: prove the final theorem `Submission.Model.radial_minimality` below (fill in its placeholder proof).

## Setup

Fix a C^3 metric family `g : E → Bilin E`, base point `x₀ : E`, maps `exp inv : E → E` and sets
`U V : Set E`.  The radial coordinate is `F z := Real.sqrt ((g x₀) (inv z) (inv z))`.  Let
`mgSpeed g x u := Real.sqrt ((g x) u u)` and `mgLength g σ a b := ∫ t in a..b, mgSpeed g (σ t) (deriv σ t)`
(as defined in `Submission.ModelMinimality`).

**Claim**: if `0 ∈ U`, `inv (exp v) = v` for `v ∈ U`, `exp 0 = x₀`, `x₀ ∈ V`,
`F` is continuous on `V`, differentiable on `V \ {x₀}`, and satisfies the **radial bound**
`‖(fderiv ℝ F y) X‖ ≤ mgSpeed g y X` for all `y ∈ V`, `y ≠ x₀` and all `X`, then for every
`v ∈ U` and every `C¹` curve `c : ℝ → E` (C¹ on an open set containing `[0,1]`) with
`c 0 = x₀`, `c 1 = exp v`, staying inside `V` on `[0,1]`, we have
`Real.sqrt ((g x₀) v v) ≤ mgLength g c 0 1`.

## Proof route

1. If `v = 0` the left side is `0 ≤ mgLength` (the integrand `mgSpeed` is a square root, hence
   nonnegative; use `intervalIntegral.integral_nonneg`).
2. Assume `v ≠ 0`.  Let `Z := {s ∈ Icc 0 1 | c s = x₀}` (nonempty since `0 ∈ Z`, and `1 ∉ Z` by
   injectivity-style hypothesis `hinj`).  Since `c` is continuous on `[0,1]`, `Z` is closed and
   bounded; put `a := sSup Z`.  Then `a ∈ Z` (`IsClosed.sSup_mem`), `a < 1`, and
   `c s ≠ x₀` for all `s ∈ (a, 1]`.  Hence `F` is differentiable along `c` on `(a, 1)` and
   `F (c s) ∈ ...`.
3. On `(a, 1)`, by the chain rule and the radial bound (with `X := deriv c s`):
   `|deriv (F∘c) s| ≤ mgSpeed g (c s) (deriv c s) =: φ s`.  Apply the FTC-2 lemma
   `intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le` on `[a, 1]` (or the wrapper
   `ftc_sub_le` if available) to get
   `F (c 1) - F (c a) ≤ ∫ x in a..1, φ x`.
4. `F (c a) = F x₀ = 0` and `F (c 1) = F (exp v) = Real.sqrt ((g x₀) v v)`.  Since `φ ≥ 0`,
   `∫ x in a..1 φ x ≤ ∫ x in 0..1 φ x = mgLength g c 0 1`.

Do NOT change the statement of `radial_minimality`.  No placeholder proofs may remain.
-/
open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Filter
open MeasureTheory intervalIntegral

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- Radial coordinate with the local inverse. -/
def radialCoord (g : E → Bilin E) (x₀ : E) (inv : E → E) (z : E) : ℝ :=
  Real.sqrt ((g x₀) (inv z) (inv z))

lemma mgSpeed_continuous_pair (g : E → Bilin E) (hg : Continuous g) :
    Continuous (fun z : E × E => mgSpeed g z.1 z.2) := by
  have h1 : Continuous (fun z : E × E => (g z.1) z.2) := by
    exact Continuous.clm_apply (hg.comp continuous_fst) continuous_snd
  have h2 : Continuous (fun z : E × E => ((g z.1) z.2) z.2) := by
    exact Continuous.clm_apply h1 continuous_snd
  -- mgSpeed g z.1 z.2 = sqrt (((g z.1) z.2) z.2)
  have h3 : Continuous (fun z : E × E => Real.sqrt (((g z.1) z.2) z.2)) :=
    Real.continuous_sqrt.comp h2
  convert h3 using 2 <;> rfl

theorem radial_minimality (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) {exp inv : E → E} {U V : Set E}
    (hExp0 : exp 0 = x₀) (h0U : (0 : E) ∈ U)
    (hUinv : ∀ v ∈ U, inv (exp v) = v)
    (hinj : ∀ v ∈ U, exp v = x₀ → v = 0)
    (hVx0 : x₀ ∈ V)
    (hFcont : ContinuousOn (radialCoord g x₀ inv) V)
    (hFdiff : ∀ y ∈ V, y ≠ x₀ → DifferentiableAt ℝ (radialCoord g x₀ inv) y)
    (hFb : ∀ y ∈ V, y ≠ x₀ → ∀ X : E,
       ‖(fderiv ℝ (radialCoord g x₀ inv) y) X‖ ≤ mgSpeed g y X) :
    ∀ v ∈ U, ∀ c : ℝ → E,
      c 0 = x₀ → c 1 = exp v →
      (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
      (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ V) →
      Real.sqrt ((g x₀) v v) ≤ mgLength g c 0 1 := by
  intro v hvinU c hc0 hc1 hcO hcV
  rcases hcO with ⟨O, hOopen, hOIcc, hcC1⟩
  let F : E → ℝ := radialCoord g x₀ inv
  by_cases hv0 : v = 0
  · subst v
    have hg00 : (g x₀) 0 0 = 0 := by simp
    rw [hg00, Real.sqrt_zero]
    dsimp [mgLength]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun u hu => Real.sqrt_nonneg _)
  · -- main case
    let Z : Set ℝ := {s | s ∈ Icc (0 : ℝ) 1 ∧ c s = x₀}
    have hcdiffO : DifferentiableOn ℝ c O := hcC1.differentiableOn (by norm_num)
    have hcContO : ContinuousOn c O := hcdiffO.continuousOn
    have hcAt (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ContinuousAt c s := by
      exact hcContO.continuousAt (hOopen.mem_nhds (hOIcc hs))
    have hZnonempty : Z.Nonempty := by
      refine ⟨0, ?_⟩
      simp [Z, hc0]
    have hZclosed : IsClosed Z := by
      refine ⟨?_⟩
      rw [isOpen_iff_mem_nhds]
      intro s hs
      by_cases hs01 : s ∈ Icc (0 : ℝ) 1
      · have hcne : c s ≠ x₀ := by
          intro heq
          exact hs ⟨hs01, heq⟩
        have hnhds : c ⁻¹' ({x₀}ᶜ) ∈ 𝓝 s := by
          exact (hcAt s hs01).preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hcne)
        refine mem_of_superset hnhds ?_
        intro t ht tZ
        exact ht tZ.2
      · have hmem : s ∈ (Icc (0 : ℝ) 1)ᶜ := by simpa using hs01
        have hnhds : (Icc (0 : ℝ) 1)ᶜ ∈ 𝓝 s := isClosed_Icc.isOpen_compl.mem_nhds hmem
        refine mem_of_superset hnhds ?_
        intro t ht tZ
        exact ht tZ.1
    let a : ℝ := sSup Z
    have hZbd : BddAbove Z := ⟨1, by intro s hs; exact hs.1.2⟩
    have haZ : a ∈ Z := IsClosed.csSup_mem hZclosed hZnonempty hZbd
    have ha0 : 0 ≤ a := haZ.1.1
    have ha1 : a ≤ 1 := haZ.1.2
    have hca : c a = x₀ := haZ.2
    have hc1ne : c 1 ≠ x₀ := by
      intro heq
      exact hv0 (hinj v hvinU (by rw [← hc1]; exact heq))
    have h1notZ : (1 : ℝ) ∉ Z := by
      intro h1Z
      exact hc1ne h1Z.2
    have ha1lt : a < 1 := by
      refine lt_of_le_of_ne ha1 ?_
      intro haeq1
      exact h1notZ (by simpa [haeq1] using haZ)
    have hne_gt (x : ℝ) (hx : x ∈ Ioo a 1) : c x ≠ x₀ := by
      intro heq
      have hx01 : x ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact le_of_lt (lt_of_le_of_lt ha0 hx.1)
        · exact le_of_lt hx.2
      have hxZ : x ∈ Z := ⟨hx01, heq⟩
      have hxle : x ≤ a := le_csSup hZbd hxZ
      exact (not_lt_of_ge hxle) hx.1
    -- F-specific hypothesis restatements
    have hFcontF : ContinuousOn F V := by simpa [F] using hFcont
    have hFdiffF (y : E) (hyV : y ∈ V) (hyne : y ≠ x₀) : DifferentiableAt ℝ F y := by
      simpa [F] using hFdiff y hyV hyne
    have hFbF (y : E) (hyV : y ∈ V) (hyne : y ≠ x₀) (X : E) :
        ‖(fderiv ℝ F y) X‖ ≤ mgSpeed g y X := by
      simpa [F] using hFb y hyV hyne X
    -- differentiability of c at points of O
    have hcCAt (x : ℝ) (hx : x ∈ O) : ContDiffAt ℝ 1 c x := hcC1.contDiffAt (hOopen.mem_nhds hx)
    have hcdiffAt (x : ℝ) (hx : x ∈ O) : DifferentiableAt ℝ c x :=
      (hcCAt x hx).differentiableAt (by norm_num)
    -- derivative of c is continuous on O
    have hderivContWithinO : ContinuousOn (derivWithin c O) O := by
      have hiff := contDiffOn_one_iff_derivWithin (𝕜 := ℝ) (s := O) (f := c) hOopen.uniqueDiffOn
      exact hiff.mp hcC1 |>.2
    have hderivContO : ContinuousOn (deriv c) O :=
      hderivContWithinO.congr (fun x hx => (derivWithin_of_isOpen hOopen hx).symm)
    -- the metric speed along c is continuous on O
    let φ : ℝ → ℝ := fun s => mgSpeed g (c s) (deriv c s)
    let g' : ℝ → ℝ := fun s => (fderiv ℝ F (c s)) (deriv c s)
    have hφcontO : ContinuousOn φ O := by
      have hpair : ContinuousOn (fun s => (c s, deriv c s)) O :=
        ContinuousOn.prodMk hcContO hderivContO
      have hspd : Continuous (fun z : E × E => mgSpeed g z.1 z.2) :=
        mgSpeed_continuous_pair g hg.continuous
      refine hspd.comp_continuousOn hpair |>.congr ?_
      intro s hs
      rfl
    have hsubA01 : Icc a 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha0 (le_refl 1)
    have hx01 (x : ℝ) (hx : x ∈ Ioo a 1) : x ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact le_of_lt (lt_of_le_of_lt ha0 hx.1)
      · exact le_of_lt hx.2
    have hxO (x : ℝ) (hx : x ∈ Ioo a 1) : x ∈ O := hOIcc (hx01 x hx)
    have hcContIccA : ContinuousOn c (Icc a 1) := hcContO.mono (Subset.trans hsubA01 hOIcc)
    have hmaps : MapsTo c (Icc a 1) V := by
      intro s hs
      exact hcV s (hsubA01 hs)
    have hFcContA : ContinuousOn (fun s => F (c s)) (Icc a 1) := hFcontF.comp hcContIccA hmaps
    have hφcontA : ContinuousOn φ (Icc a 1) := hφcontO.mono (Subset.trans hsubA01 hOIcc)
    have hφcont01 : ContinuousOn φ (Icc 0 1) := hφcontO.mono hOIcc
    have hφintA : IntegrableOn φ (Icc a 1) :=
      ContinuousOn.integrableOn_compact (μ := volume) (K := Icc a 1) isCompact_Icc hφcontA
    -- derivative of h = F ∘ c and the radial bound on (a, 1)
    have hderval (x : ℝ) (hx : x ∈ Ioo a 1) : HasDerivAt (fun s => F (c s)) (g' x) x := by
      have hyV : c x ∈ V := hcV x (hx01 x hx)
      have hyne : c x ≠ x₀ := hne_gt x hx
      have hFder : HasFDerivAt F (fderiv ℝ F (c x)) (c x) := (hFdiffF (c x) hyV hyne).hasFDerivAt
      have hcder : HasDerivAt c (deriv c x) x := (hcdiffAt x (hxO x hx)).hasDerivAt
      change HasDerivAt (fun s => F (c s)) (g' x) x
      exact hFder.comp_hasDerivAt x hcder
    have hφbound (x : ℝ) (hx : x ∈ Ioo a 1) : g' x ≤ φ x := by
      have hyV : c x ∈ V := hcV x (hx01 x hx)
      have hyne : c x ≠ x₀ := hne_gt x hx
      have hbnd := hFbF (c x) hyV hyne (deriv c x)
      dsimp [g', φ]
      have hw : ‖(fderiv ℝ F (c x)) (deriv c x)‖ = |(fderiv ℝ F (c x)) (deriv c x)| := by rfl
      exact le_trans (le_abs_self _) (by simpa [hw] using hbnd)
    have hderivIoo (x : ℝ) (hx : x ∈ Ioo a 1) :
        HasDerivWithinAt (fun s => F (c s)) (g' x) (Ioi x) x :=
      (hderval x hx).hasDerivWithinAt
    have hFTC := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
      (a := a) (b := 1) (g := fun s => F (c s)) (g' := g') (φ := φ) ha1 hFcContA hderivIoo hφintA hφbound
    -- endpoint values of F
    have hinvx0 : inv x₀ = 0 := by
      rw [← hExp0]
      exact hUinv (0 : E) h0U
    have hFx0 : F x₀ = 0 := by
      dsimp [F, radialCoord]
      rw [hinvx0]
      simp
    have hFc1 : F (c 1) = Real.sqrt ((g x₀) v v) := by
      dsimp [F, radialCoord]
      rw [hc1]
      rw [hUinv v hvinU]
    have hFcA : F (c a) = 0 := by
      rw [hca, hFx0]
    have hFTCl : Real.sqrt ((g x₀) v v) ≤ ∫ y in a..1, φ y := by
      simpa [hFc1, hFcA] using hFTC
    -- monotone comparison of the integrals
    have hφnonneg (s : ℝ) : 0 ≤ φ s := by
      dsimp [φ, mgSpeed]
      exact Real.sqrt_nonneg _
    have hφint01 : IntervalIntegrable φ volume (0 : ℝ) 1 :=
      ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (a := 0) (b := 1) (by norm_num) hφcont01
    have hmono : (∫ y in a..1, φ y) ≤ ∫ y in (0 : ℝ)..1, φ y := by
      exact intervalIntegral.integral_mono_interval (μ := volume) (a := a) (b := 1) (c := 0) (d := 1)
        ha0 ha1 (le_refl (1 : ℝ)) (Eventually.of_forall hφnonneg) hφint01
    calc
      Real.sqrt ((g x₀) v v) ≤ ∫ y in a..1, φ y := hFTCl
      _ ≤ ∫ y in (0 : ℝ)..1, φ y := hmono
      _ = mgLength g c 0 1 := rfl

end
end Submission.Model
