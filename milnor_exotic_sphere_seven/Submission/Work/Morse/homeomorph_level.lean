import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology

namespace Work.Morse

open Set Function

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Along an integral curve of `v` inside the strip `{a < f < b}`, where `df v = 1`, the value of
`f` increases at speed one. -/
lemma hasDerivAt_flow {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} {v : (x : M) → TangentSpace (𝓡 n) x}
    (hv : ∀ x, a < f x → f x < b → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (v x) = 1)
    {Φ : ℝ → M → M} (hΦint : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v)
    {x : M} {u : ℝ} (hu : a < f (Φ u x)) (hu' : f (Φ u x) < b) :
    HasDerivAt (fun u ↦ f (Φ u x)) 1 u := by
  have hmd : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (Φ u x) := hf.mdifferentiableAt (by simp)
  have hd := (hmd.hasMFDerivAt).comp u (hΦint x u)
  have hlin : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (Φ u x)
      ∘SL ((1 : ℝ →L[ℝ] ℝ).smulRight (v (Φ u x))) = (1 : ℝ →L[ℝ] ℝ) := by
    apply ContinuousLinearMap.ext
    intro a
    show (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f (Φ u x)) (a • v (Φ u x)) = (1 : ℝ →L[ℝ] ℝ) a
    rw [map_smul, hv (Φ u x) hu hu']
    change a • (1 : ℝ) = (1 : ℝ →L[ℝ] ℝ) a
    simp
  have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u ↦ f (Φ u x)) u (1 : ℝ →L[ℝ] ℝ) :=
    hd.congr_mfderiv hlin
  have h3 : HasFDerivAt (fun u ↦ f (Φ u x)) (1 : ℝ →L[ℝ] ℝ) u := h2.hasFDerivAt
  simpa using (hasFDerivAt_iff_hasDerivAt.mp h3)

/-- If the straight line of values `f x + u` stays inside the strip for `u` between `0` and `t`,
then the flow moves `x` to the level `f x + t`. -/
lemma flow_level_shift {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} {v : (x : M) → TangentSpace (𝓡 n) x}
    (hv : ∀ x, a < f x → f x < b → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (v x) = 1)
    {Φ : ℝ → M → M} (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦint : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v)
    (hΦcont : Continuous (Function.uncurry Φ))
    {x : M} {t : ℝ} (hseg : ∀ u ∈ uIcc 0 t, a < f x + u ∧ f x + u < b) :
    f (Φ t x) = f x + t := by
  have hcontΦ : Continuous fun u : ℝ ↦ Φ u x :=
    hΦcont.comp (continuous_id.prodMk continuous_const)
  have hcontf : Continuous fun u : ℝ ↦ f (Φ u x) := hf.continuous.comp hcontΦ
  let A : Set ℝ := (fun u : ℝ ↦ f (Φ u x)) ⁻¹' Ioo a b
  let k : ℝ → ℝ := fun u ↦ f (Φ u x) - u - f x
  have hAopen : IsOpen A := isOpen_Ioo.preimage hcontf
  have hcontk : Continuous k := (hcontf.sub continuous_id).sub continuous_const
  have hderiv : ∀ u ∈ A, HasDerivAt k 0 u := by
    intro u hu
    have hu' : a < f (Φ u x) ∧ f (Φ u x) < b := by simpa [A] using hu
    have h1 := hasDerivAt_flow (n := n) hf hv hΦint hu'.1 hu'.2
    have h3 : HasDerivAt (fun u ↦ f (Φ u x) - u - f x) 0 u := by
      simpa using (h1.sub (hasDerivAt_id u)).sub_const (f x)
    simpa only [k] using h3
  have hopen : IsOpen (A ∩ k ⁻¹' ({0} : Set ℝ)) :=
    hAopen.isOpen_inter_preimage_of_deriv_eq_zero
      (fun u hu ↦ (hderiv u hu).differentiableAt.differentiableWithinAt)
      (fun u hu ↦ (hderiv u hu).deriv) {0}
  have hcopen : IsOpen (k ⁻¹' ({0} : Set ℝ)ᶜ) := isOpen_compl_singleton.preimage hcontk
  have hdisj : Disjoint (A ∩ k ⁻¹' ({0} : Set ℝ)) (k ⁻¹' ({0} : Set ℝ)ᶜ) := by
    rw [Set.disjoint_left]
    intro u hu hu'
    exact hu' hu.2
  have hcover : uIcc 0 t ⊆ (A ∩ k ⁻¹' ({0} : Set ℝ)) ∪ k ⁻¹' ({0} : Set ℝ)ᶜ := by
    intro u hu
    by_cases h : k u = 0
    · left
      refine ⟨?_, h⟩
      have hsu := hseg u hu
      have hk : f (Φ u x) = f x + u := by simp only [k] at h; linarith
      change f (Φ u x) ∈ Ioo a b
      simpa [mem_Ioo, hk] using hsu
    · right
      simpa using h
  rcases (isPreconnected_uIcc (a := (0 : ℝ)) (b := t)).subset_or_subset hopen hcopen hdisj
    hcover with hsub | hsub
  · have hkt : k t = 0 := (hsub right_mem_uIcc).2
    simp only [k] at hkt
    linarith
  · have h0 : k 0 = 0 := by simp only [k, hΦ0 x]; ring
    have hne : k 0 ≠ 0 := by
      have := hsub left_mem_uIcc
      simpa using this
    exact absurd h0 hne

/-- Composing a level map of `ℝ` fixing the complement of the strip `(a,b)` with the flow gives a
map which shifts the level function `f` by that level map. -/
lemma f_flowMap {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} {v : (x : M) → TangentSpace (𝓡 n) x}
    (hv : ∀ x, a < f x → f x < b → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (v x) = 1)
    {Φ : ℝ → M → M} (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦint : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v)
    (hΦcont : Continuous (Function.uncurry Φ))
    {ψ : ℝ → ℝ}
    (hψa : ∀ s, s ≤ a → ψ s = s) (hψb : ∀ s, b ≤ s → ψ s = s)
    (hψstrip : ∀ s, a < s → s < b → a < ψ s ∧ ψ s < b) :
    ∀ x, f (Φ (ψ (f x) - f x) x) = ψ (f x) := by
  intro x
  rcases lt_trichotomy (f x) b with hb | hb | hb
  · rcases le_or_gt (f x) a with ha | ha
    · have h : ψ (f x) = f x := hψa (f x) ha
      rw [h, sub_self, hΦ0 x]
    · have hs := hψstrip (f x) ha hb
      have hseg : ∀ u ∈ uIcc 0 (ψ (f x) - f x), a < f x + u ∧ f x + u < b := by
        intro u hu
        rcases le_total (ψ (f x) - f x) 0 with h | h
        · rw [uIcc_of_ge h, mem_Icc] at hu
          exact ⟨by linarith [hu.1, hs.1], by linarith [hu.2, hb]⟩
        · rw [uIcc_of_le h, mem_Icc] at hu
          exact ⟨by linarith [hu.1, ha], by linarith [hu.2, hs.2]⟩
      have h := flow_level_shift (n := n) hf hv hΦ0 hΦint hΦcont hseg
      linarith
  · have h : ψ (f x) = f x := hψb (f x) (le_of_eq hb.symm)
    rw [h, sub_self, hΦ0 x]
  · have h : ψ (f x) = f x := hψb (f x) (le_of_lt hb)
    rw [h, sub_self, hΦ0 x]

/-- Let `f` be smooth, `Φ` a jointly continuous flow of a vector field `v` with `df(v) = 1` on the
open strip `{a < f < b}`, and `ψ : ℝ ≃ₜ ℝ` a level homeomorphism with `ψ s ≤ s` fixing `(-∞,a]`
and `[b,∞)`. Then there is a homeomorphism of `M` conjugating `f` to `ψ ∘ f`. -/
theorem homeomorph_level {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b)
    {v : (x : M) → TangentSpace (𝓡 n) x}
    (hv : ∀ x, a < f x → f x < b → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (v x) = 1)
    {Φ : ℝ → M → M} (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦint : ∀ x, IsMIntegralCurve (fun t ↦ Φ t x) v)
    (hΦsmul : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hΦcont : Continuous (Function.uncurry Φ))
    {ψ : ℝ ≃ₜ ℝ} (hψle : ∀ s, ψ s ≤ s)
    (hψa : ∀ s ≤ a, ψ s = s) (hψb : ∀ s ≥ b, ψ s = s) :
    ∃ H : M ≃ₜ M, ∀ x, f (H x) = ψ (f x) := by
  have hψstrip : ∀ s, a < s → s < b → a < ψ s ∧ ψ s < b := by
    intro s hs1 hs2
    constructor
    · by_contra h
      push Not at h
      have hfix : ψ (ψ s) = ψ s := hψa (ψ s) h
      have hs : s = ψ s := ψ.injective hfix.symm
      linarith
    · by_contra h
      push Not at h
      have hfix : ψ (ψ s) = ψ s := hψb (ψ s) h
      have hs : s = ψ s := ψ.injective hfix.symm
      linarith
  have hσa : ∀ s, s ≤ a → ψ.symm s = s := by
    intro s hs
    refine ψ.injective ?_
    rw [Homeomorph.apply_symm_apply, hψa s hs]
  have hσb : ∀ s, b ≤ s → ψ.symm s = s := by
    intro s hs
    refine ψ.injective ?_
    rw [Homeomorph.apply_symm_apply, hψb s hs]
  have hσstrip : ∀ s, a < s → s < b → a < ψ.symm s ∧ ψ.symm s < b := by
    intro s hs1 hs2
    constructor
    · by_contra h
      push Not at h
      have hfix : ψ.symm (ψ.symm s) = ψ.symm s := hσa (ψ.symm s) h
      have hs : s = ψ.symm s := (ψ.symm).injective hfix.symm
      linarith
    · by_contra h
      push Not at h
      have hfix : ψ.symm (ψ.symm s) = ψ.symm s := hσb (ψ.symm s) h
      have hs : s = ψ.symm s := (ψ.symm).injective hfix.symm
      linarith
  let Kψ : M → M := fun x ↦ Φ (ψ (f x) - f x) x
  let Kσ : M → M := fun x ↦ Φ (ψ.symm (f x) - f x) x
  have hKψcont : Continuous Kψ := by
    have h1 : Continuous fun x : M ↦ (ψ (f x) - f x, x) :=
      ((ψ.continuous.comp hf.continuous).sub hf.continuous).prodMk continuous_id
    exact hΦcont.comp h1
  have hKσcont : Continuous Kσ := by
    have h1 : Continuous fun x : M ↦ (ψ.symm (f x) - f x, x) :=
      ((ψ.symm.continuous.comp hf.continuous).sub hf.continuous).prodMk continuous_id
    exact hΦcont.comp h1
  have hKψf : ∀ x, f (Kψ x) = ψ (f x) :=
    f_flowMap (n := n) hf hv hΦ0 hΦint hΦcont hψa hψb hψstrip
  have hKσf : ∀ x, f (Kσ x) = ψ.symm (f x) :=
    f_flowMap (n := n) hf hv hΦ0 hΦint hΦcont hσa hσb hσstrip
  have hleft : ∀ x, Kσ (Kψ x) = x := by
    intro x
    have h1 : f (Kψ x) = ψ (f x) := hKψf x
    show Φ (ψ.symm (f (Kψ x)) - f (Kψ x)) (Kψ x) = x
    rw [h1, Homeomorph.symm_apply_apply]
    show Φ (f x - ψ (f x)) (Φ (ψ (f x) - f x) x) = x
    rw [← hΦsmul (f x - ψ (f x)) (ψ (f x) - f x) x]
    rw [show f x - ψ (f x) + (ψ (f x) - f x) = 0 by ring, hΦ0 x]
  have hright : ∀ x, Kψ (Kσ x) = x := by
    intro x
    have h1 : f (Kσ x) = ψ.symm (f x) := hKσf x
    show Φ (ψ (f (Kσ x)) - f (Kσ x)) (Kσ x) = x
    rw [h1, Homeomorph.apply_symm_apply]
    show Φ (f x - ψ.symm (f x)) (Φ (ψ.symm (f x) - f x) x) = x
    rw [← hΦsmul (f x - ψ.symm (f x)) (ψ.symm (f x) - f x) x]
    rw [show f x - ψ.symm (f x) + (ψ.symm (f x) - f x) = 0 by ring, hΦ0 x]
  exact ⟨⟨⟨Kψ, Kσ, hleft, hright⟩, hKψcont, hKσcont⟩, hKψf⟩

end Work.Morse
