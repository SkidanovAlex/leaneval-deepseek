/-
# `Work.FTS.GalLimit.Closure.phi_HQo` — the Galerkin test functions lie in `HQo α 4`

The Galerkin test functions of the design (`Work.FTS.GalLimit.CcBasis`) are globally `C^∞` and
supported in a compact rectangle `[a,b] × [δ, π/2-δ]` with `0 < a < b`, `0 < δ` — i.e. *strictly
inside* the open quadrant `(0,∞) × (0,π/2)`.  Hence every iterated derivative `D_z^j D_θ^i (φ k)`
is supported in that same rectangle, so that

* the `ℋ⁴`-integrand `HkIntegrand α 4 (φ k)` vanishes off the rectangle, where all the singular
  weights `w(z) = (1+z)²/z²`, `sin(2θ)^{-η/2}`, `sin(2θ)^{-γ/2}` would otherwise be evaluated;
* on the rectangle the integrand is continuous (the weights are continuous, because
  `z ≥ a > 0` and `sin(2θ) ≥ sin(2δ) > 0`) and therefore bounded, since the rectangle is compact.

Together with the trivial `SmoothOpen` (a globally `C^∞` function is `C^∞` on the open quadrant)
this gives `HQo α 4 (φ k) = SmoothOpen (φ k) ∧ HkMem α 4 (φ k)` — with **no restriction on `α`**,
which is the point of the lemma: the `α ≤ 1`-restricted bounds of the chapter
(`Work.Spaces.HkIntegrand_bound`, `HkMemSmoothCompact`) are *not* used, precisely because the
support stays away from the two angular endpoints of the quadrant.

The proof is assembled from the generic pieces proved above `phi_HQo`:

* `DzIter_eq_zero_of_isOpen_z`, `DthIter_eq_zero_of_isOpen_th` — a function vanishing in a
  neighbourhood of `z` (resp. of `θ`) has all its `D_z`- (resp. `D_θ`-) iterates vanishing there
  (the higher regularity is free: `deriv` of a function which is *eventually* zero is zero);
* `dzIter_eq_zero_of_suppIn`, `mixed_eq_zero_of_suppIn`, `HkIntegrand_eq_zero_of_suppIn` — the
  transport of the support hypothesis to the integrand;
* `exists_bound_HkIntegrand_of_suppIn` — the bound on the rectangle, by compactness;
* `hkMem_of_suppIn` — `HkMem α k` by domination (`Work.FTS.LocData.HkMem_of_majorant`) with the
  global majorant `‖HkIntegrand‖ ≤ M·1_{z ≤ b}` making the `z`-integral finite.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.GalLimit.Defs
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.Spaces.SmoothCompact_HkMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalLimit.Closure

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Globally `C^∞` functions: `SmoothOpen` and `SmoothQuad` -/

/-- A function which is globally `C^∞` is `C^∞` on the open quadrant. -/
theorem smoothOpen_of_contDiff {f : ℝ → ℝ → ℝ}
    (h : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    Work.FTS.EllipticEst.SmoothOpen f :=
  h.contDiffOn.mono (Set.subset_univ _)

/-- A function which is globally `C^∞` is `C^∞` on the open half-strip `z > -1, 0 < θ < π/2`. -/
theorem smoothQuad_of_contDiff {f : ℝ → ℝ → ℝ}
    (h : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) :
    Work.FTS.LocData.SmoothQuad f :=
  h.contDiffOn.mono (Set.subset_univ _)

/-! ## Vanishing of the iterated derivatives on a neighbourhood

A function which vanishes in a (one-sided-agnostic) neighbourhood of the foot of the derivative
has vanishing derivative there; iterating, this is the only smoothness input needed to transport a
support condition to `D_z^j D_θ^i f`. -/

/-- If `f · θ` vanishes on a neighbourhood `U` of `z`, then every `D_z`-iterate of `f` vanishes
at `(z,θ)`. -/
theorem DzIter_eq_zero_of_isOpen_z {f : ℝ → ℝ → ℝ} :
    ∀ (k : ℕ) (U : Set ℝ) (z θ : ℝ), IsOpen U → z ∈ U → (∀ z' ∈ U, f z' θ = 0) →
      Work.Spaces.DzIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => intro U z θ _ hzU h; exact h z hzU
  | succ k ih =>
      intro U z θ hU hzU h
      rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      have hp : Work.Spaces.pz (Work.Spaces.DzIter k f) z θ = 0 := by
        rw [Work.Spaces.pz]
        have hev : (fun z' => Work.Spaces.DzIter k f z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
          filter_upwards [hU.mem_nhds hzU] with z' hz'
          exact ih U z' θ hU hz' h
        rw [hev.deriv_eq, deriv_const]
      rw [hp, mul_zero]

/-- If `f z ·` vanishes on a neighbourhood `U` of `θ`, then every `D_θ`-iterate of `f` vanishes
at `(z,θ)`. -/
theorem DthIter_eq_zero_of_isOpen_th {f : ℝ → ℝ → ℝ} :
    ∀ (k : ℕ) (U : Set ℝ) (z θ : ℝ), IsOpen U → θ ∈ U → (∀ θ' ∈ U, f z θ' = 0) →
      Work.Spaces.DthIter k f z θ = 0 := by
  intro k
  induction k with
  | zero => intro U z θ _ hθU h; exact h θ hθU
  | succ k ih =>
      intro U z θ hU hθU h
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      have hp : Work.Spaces.pth (Work.Spaces.DthIter k f) z θ = 0 := by
        rw [Work.Spaces.pth]
        have hev : (fun θ' => Work.Spaces.DthIter k f z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
          filter_upwards [hU.mem_nhds hθU] with θ' hθ'
          exact ih U z θ' hU hθ' h
        rw [hev.deriv_eq, deriv_const]
      rw [hp, mul_zero]

/-! ## Support of the iterated derivatives

`SuppIn f a b δ` is `Work.FTS.GalBasis.SuppIn`: `f` vanishes off the closed box
`[a,b] × [δ, π/2-δ]`.  It is exactly the support clause of `CcBasis`. -/

/-- Every `D_z`-iterate of a function supported in `[a,b] × [δ,π/2-δ]` vanishes off that box. -/
theorem dzIter_eq_zero_of_suppIn {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0)
    {z θ : ℝ} (h : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) (k : ℕ) :
    Work.Spaces.DzIter k f z θ = 0 := by
  rcases h with h | h
  · exact DzIter_eq_zero_of_isOpen_z k _ z θ isClosed_Icc.isOpen_compl h
      (fun z' hz' => hSupp z' θ (Or.inl hz'))
  · exact DzIter_eq_zero_of_isOpen_z k Set.univ z θ isOpen_univ (Set.mem_univ z)
      (fun z' _ => hSupp z' θ (Or.inr h))

/-- Every mixed derivative `D_z^j D_θ^i` of a function supported in `[a,b] × [δ,π/2-δ]` vanishes
off that box. -/
theorem mixed_eq_zero_of_suppIn {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0)
    {z θ : ℝ} (h : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) (j i : ℕ) :
    Work.Spaces.mixed j i f z θ = 0 := by
  rw [Work.Spaces.mixed]
  rcases h with h | h
  · -- `z` outside: `f` vanishes on the whole `θ`-line through `z'`, for every `z'` off the box
    refine DzIter_eq_zero_of_isOpen_z j _ z θ isClosed_Icc.isOpen_compl h (fun z' hz' => ?_)
    exact DthIter_eq_zero_of_isOpen_th i Set.univ z' θ isOpen_univ (Set.mem_univ θ)
      (fun θ' _ => hSupp z' θ' (Or.inl hz'))
  · refine DzIter_eq_zero_of_isOpen_z j Set.univ z θ isOpen_univ (Set.mem_univ z)
      (fun z' _ => DthIter_eq_zero_of_isOpen_th i _ z' θ isClosed_Icc.isOpen_compl h
        (fun θ' hθ' => hSupp z' θ' (Or.inr hθ')))

/-- The `ℋ^k`-integrand of a function supported in `[a,b] × [δ,π/2-δ]` vanishes off that box
(every summand carries a derivative factor). -/
theorem HkIntegrand_eq_zero_of_suppIn (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0)
    {z θ : ℝ} (h : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have h1 : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ *
      (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [dzIter_eq_zero_of_suppIn hSupp h i]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
      else 0) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [ite_eq_left hc, mixed_eq_zero_of_suppIn hSupp h j i]; ring
      · rw [ite_eq_right hc]
  rw [Work.Spaces.HkIntegrand, h1, h2, add_zero]

/-! ## The pointwise bound on the box -/

/-- On the whole plane, the `ℋ^k`-integrand of a function supported in `[a,b] × [δ,π/2-δ]`
(`0 < a`, `0 < δ`, `f` smooth on the open quadrant) is bounded by a constant.  Off the box it
vanishes, and on the box it is continuous on a compact set: there `z ≥ a > 0` and
`sin(2δ) ≤ sin(2θ)`, so the weights `w` and `sin(2θ)^{-η/2}`, `sin(2θ)^{-γ/2}` are finite and
continuous. -/
theorem exists_bound_HkIntegrand_of_suppIn (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hsmooth : Work.FTS.LocData.SmoothQuad f)
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z θ : ℝ, Work.Spaces.HkIntegrand α k f z θ ≤ M := by
  have hcont := Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k f hsmooth
  have hbox_sub : Set.Icc a b ×ˢ Set.Icc δ (π / 2 - δ) ⊆ Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) := by
    intro p hp
    rw [Set.mem_prod] at hp
    obtain ⟨hz, hθ⟩ := hp
    rw [Set.mem_Icc] at hz hθ
    rw [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
    exact ⟨by linarith [hz.1], by linarith [hθ.1], by linarith [hθ.2]⟩
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image (hcont.mono hbox_sub)
  have hMbdd : ∀ p ∈ Set.Icc a b ×ˢ Set.Icc δ (π / 2 - δ),
      Work.Spaces.HkIntegrand α k f p.1 p.2 ≤ M := fun p hp =>
    hM (Set.mem_image_of_mem (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) hp)
  refine ⟨max M 0, le_max_right _ _, fun z θ => ?_⟩
  by_cases hmem : (z, θ) ∈ Set.Icc a b ×ˢ Set.Icc δ (π / 2 - δ)
  · exact le_trans (hMbdd (z, θ) hmem) (le_max_left _ _)
  · have hoff : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ) := by
      by_contra hc
      push Not at hc
      exact hmem (Set.mem_prod.mpr ⟨hc.1, hc.2⟩)
    rw [HkIntegrand_eq_zero_of_suppIn α k hSupp hoff]
    exact le_max_right _ _

/-! ## Membership in `ℋ^k` -/

/-- **A smooth function supported in a compact box strictly inside the open quadrant lies in
`ℋ^k`, for every `α`.**  Domination by the global constant on the box `[0,b] × [0,π/2]`, which is
integrable in `z` because it is supported in the finite-measure set `[0,b]`. -/
theorem hkMem_of_suppIn (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} {a b δ : ℝ}
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hsmooth : Work.FTS.LocData.SmoothQuad f)
    (hSupp : ∀ z θ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ)) → f z θ = 0) :
    Work.Spaces.HkMem α k f := by
  obtain ⟨M, hMnn, hM⟩ := exists_bound_HkIntegrand_of_suppIn α k ha hδ hsmooth hSupp
  have hbb : (0 : ℝ) < b := lt_trans ha hab
  -- the majorant: the constant `M` on the box `[0,b] × [0,π/2]`, zero beyond
  set Maj : ℝ → ℝ → ℝ := fun z _ => if z ∈ Set.Icc (0 : ℝ) b then M else 0 with hMaj
  have hunfold : ∀ z θ : ℝ, Maj z θ = if z ∈ Set.Icc (0 : ℝ) b then M else 0 := by
    intro z θ; simp only [hMaj]
  have hIntθ : ∀ z : ℝ, (∫ θ in Work.Spaces.Iθ, Maj z θ)
      = if z ∈ Set.Icc (0 : ℝ) b then M * (π / 2) else 0 := by
    intro z
    by_cases hz : z ∈ Set.Icc (0 : ℝ) b
    · have hfun : (fun θ : ℝ => Maj z θ) = fun _ => M := by
        funext θ; rw [hunfold z θ, ite_eq_left hz]
      rw [hfun, setIntegral_const, Work.Spaces.volume_real_Iθ, ite_eq_left hz, smul_eq_mul]
      ring
    · have hfun : (fun θ : ℝ => Maj z θ) = fun _ => (0 : ℝ) := by
        funext θ; rw [hunfold z θ, ite_eq_right hz]
      rw [hfun, integral_zero, ite_eq_right hz]
  have hslice : ∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => Maj z θ) Work.Spaces.Iθ := by
    intro z hz
    by_cases hb : z ∈ Set.Icc (0 : ℝ) b
    · have hfun : (fun θ : ℝ => Maj z θ) = fun _ => M := by
        funext θ; rw [hunfold z θ, ite_eq_left hb]
      rw [hfun]
      exact integrableOn_const (C := M) Work.Spaces.volume_Iθ_lt_top.ne
    · have hfun : (fun θ : ℝ => Maj z θ) = fun _ => (0 : ℝ) := by
        funext θ; rw [hunfold z θ, ite_eq_right hb]
      rw [hfun]
      exact integrableOn_zero
  have hzint : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Maj z θ) Work.Spaces.Iz := by
    rw [show (fun z => ∫ θ in Work.Spaces.Iθ, Maj z θ)
        = fun z => if z ∈ Set.Icc (0 : ℝ) b then M * (π / 2) else 0 from funext hIntθ]
    have h1 : IntegrableOn (fun z => if z ∈ Set.Icc (0 : ℝ) b then M * (π / 2) else 0)
        (Set.Icc 0 b) :=
      IntegrableOn.congr_fun
        (integrableOn_const (C := M * (π / 2))
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        (fun z hz => by rw [ite_eq_left hz]) measurableSet_Icc
    have h2 : IntegrableOn (fun z => if z ∈ Set.Icc (0 : ℝ) b then M * (π / 2) else 0)
        (Set.Ioi b) :=
      IntegrableOn.congr_fun integrableOn_zero (fun z hz => by
        have hz' : ¬ (z ∈ Set.Icc (0 : ℝ) b) := fun hc => absurd hc.2 (not_le.mpr hz)
        rw [ite_eq_right hz']) measurableSet_Ioi
    refine (h1.union h2).mono_set ?_
    intro z hz
    by_cases h : z ≤ b
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr (lt_of_not_ge h)
  refine Work.FTS.LocData.HkMem_of_majorant α k
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k f hsmooth) hslice hzint ?_
  intro z hz θ hθ
  by_cases hb : z ∈ Set.Icc (0 : ℝ) b
  · rw [hunfold z θ, ite_eq_left hb]
    exact hM z θ
  · have hzb : b < z := by
      rcases lt_or_ge b z with h | h
      · exact h
      · exact absurd ⟨hz, h⟩ hb
    have hoff : z ∉ Set.Icc a b ∨ θ ∉ Set.Icc δ (π / 2 - δ) :=
      Or.inl fun hc => absurd hc.2 (not_le.mpr hzb)
    rw [HkIntegrand_eq_zero_of_suppIn α k hSupp hoff, hunfold z θ, ite_eq_right hb]

/-! ## The target -/

theorem phi_HQo {α : ℝ} {φ : ℕ → Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.GalLimit.CcBasis φ) (k : ℕ) : Work.FTS.VocabO.HQo α 4 (φ k) := by
  obtain ⟨a, b, ha, hab, δ, hδ, hsm, hsupp⟩ := hC k
  exact ⟨smoothOpen_of_contDiff hsm,
    hkMem_of_suppIn α 4 ha hab hδ (smoothQuad_of_contDiff hsm) hsupp⟩

end Work.FTS.GalLimit.Closure
