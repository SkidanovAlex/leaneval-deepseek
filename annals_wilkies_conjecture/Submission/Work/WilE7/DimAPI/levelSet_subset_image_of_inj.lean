import Mathlib
import Submission.Work.WilE7.Auxiliary.levelSetEqNearOfKerLe
import Submission.Work.WilE7.DimAPI.fderiv_gamma_mem_ker
import Submission.Work.WilE7.DimAPI.bij_comp_projection
import Submission.Work.WilE7.DimAPI.image_mem_nhds_of_hasStrictFDerivAt_bijective

namespace Work.WilE7.DimAPI

open Filter Topology
open scoped Topology

/-- **The level set of a submersion near `p` is covered by the image of an injective
parametrisation of the same dimension.**

Let `g : ℝⁿ → ℝᵏ` be analytic with `(fderiv ℝ g p).range = ⊤` (a submersion at `p`), and let
`γ : E → ℝⁿ` be analytic at `0` with `γ 0 = p`, with `fderiv ℝ γ 0` injective and
`finrank ℝ (fderiv ℝ g p).ker = finrank ℝ E`.  If `g ∘ γ` is constantly `g p` near `0`, then
every `z` with `g z = g p` sufficiently close to `p` is of the form `γ s` for `s` arbitrarily
close to `0`.

This is the local statement that an injective analytic parametrisation of the right dimension
fills up the level set of a submersion.  The proof uses the implicit-function-theorem chart of
the level set (`Work.WilE7.Aux.levelSetChart`), together with the inverse function theorem
applied to the composite `s ↦ C (γ s - p)`, where `C` is a projection onto `ker (fderiv ℝ g p)`. -/
theorem levelSet_subset_image_of_inj {n k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (g : (Fin n → ℝ) → (Fin k → ℝ)) (p : Fin n → ℝ)
    (hg : ∀ y, AnalyticAt ℝ g y) (hsurj : (fderiv ℝ g p).range = ⊤)
    {γ : E → (Fin n → ℝ)} (hγ0 : γ 0 = p) (hγan : AnalyticAt ℝ γ 0)
    (hγinj : Function.Injective (fderiv ℝ γ 0))
    (hdim : Module.finrank ℝ (fderiv ℝ g p).ker = Module.finrank ℝ E)
    (hlevel : ∀ᶠ s in nhds (0 : E), g (γ s) = g p) :
    ∀ A ∈ nhds (0 : E), ∃ O ∈ nhds p,
      ∀ z ∈ O, g z = g p → ∃ s ∈ A, γ s = z := by
  -- The differential of `γ` at `0` maps into the kernel of the differential of `g` at `p`:
  -- differentiate `g ∘ γ ≡ g p`.
  have hTker : ∀ v, (fderiv ℝ γ 0) v ∈ (fderiv ℝ g p).ker :=
    fderiv_gamma_mem_ker (hg p) hγ0 hγan hlevel
  -- `W` is the tangent space of the level set, `C` a continuous projection onto it.
  let W : Submodule ℝ (Fin n → ℝ) := (fderiv ℝ g p).ker
  have hcompC : W.ClosedComplemented := by
    simpa [W] using (fderiv ℝ g p).ker_closedComplemented_of_finiteDimensional_range
  let C : (Fin n → ℝ) →L[ℝ] W := Classical.choose hcompC
  have hC : ∀ x : W, C ↑x = x := Classical.choose_spec hcompC
  -- Shift `g` to vanish at `p` and chart its level set.
  let f : (Fin n → ℝ) → (Fin k → ℝ) := fun y => g y - g p
  have hfd : fderiv ℝ f p = fderiv ℝ g p := by
    simpa only [f] using fderiv_sub_const (g p)
  have hfanal : AnalyticAt ℝ f p := by
    have h : AnalyticAt ℝ (fun y : Fin n → ℝ => g y - g p) p := (hg p).sub analyticAt_const
    simpa only [f] using h
  have hfp : f p = 0 := by simp [f]
  have hkerEq : (fderiv ℝ f p).ker = W := by rw [hfd]
  have hsurjF : (fderiv ℝ f p).range = ⊤ := by rw [hfd]; exact hsurj
  obtain ⟨γc, V, U, _hVopen, hUopen, _h0V, hpU, _hγc0, _hγccont, _hγcU, hγcC, _hγczero,
    hγcsurj⟩ :=
    Work.WilE7.Aux.levelSetChart f p W C hC hfanal.hasStrictFDerivAt hfp hkerEq hsurjF
  -- The parametrisation of the level set composed with the projection onto `W`.
  let Φ : E → W := fun s => C (γ s - p)
  have hΦstrict : HasStrictFDerivAt Φ (C.comp (fderiv ℝ γ 0)) 0 := by
    have h1 : HasStrictFDerivAt (fun s : E => γ s - p) (fderiv ℝ γ 0) 0 :=
      hγan.hasStrictFDerivAt.sub_const p
    have h2 : HasStrictFDerivAt (fun x : Fin n → ℝ => C x) C ((fun s : E => γ s - p) 0) :=
      C.hasStrictFDerivAt
    have h3 := h2.comp 0 h1
    simpa [Φ] using h3
  have hΦanal : AnalyticAt ℝ Φ 0 := by
    have h1 : AnalyticAt ℝ (fun s : E => γ s - p) 0 := hγan.sub analyticAt_const
    have h2 : AnalyticAt ℝ (fun x : Fin n → ℝ => C x) ((fun s : E => γ s - p) 0) :=
      C.analyticAt _
    have h3 : AnalyticAt ℝ ((fun x : Fin n → ℝ => C x) ∘ (fun s : E => γ s - p)) 0 :=
      AnalyticAt.comp h2 h1
    simpa [Φ, Function.comp_def] using h3
  -- Its differential at `0` is `C ∘ fderiv γ 0`, a bijection `E → W` by the dimension count.
  have hED : Module.finrank ℝ E = Module.finrank ℝ W := hdim.symm
  have hbij : Function.Bijective (fderiv ℝ Φ 0) := by
    have hderiv : fderiv ℝ Φ 0 = C.comp (fderiv ℝ γ 0) := hΦstrict.hasFDerivAt.fderiv
    rw [hderiv]
    exact bij_comp_projection W C hC (fderiv ℝ γ 0) hTker hγinj hED
  have hΦ0 : Φ 0 = 0 := by simp [Φ, hγ0]
  have hsurjΦ : ∀ A ∈ 𝓝 (0:E), Φ '' A ∈ 𝓝 (Φ 0) :=
    image_mem_nhds_of_hasStrictFDerivAt_bijective hΦanal.hasStrictFDerivAt hbij
  -- Assembly.
  intro A hA
  obtain ⟨S, hSsub, hSopen, hS0⟩ := eventually_nhds_iff.mp hlevel
  have hS_mem : S ∈ 𝓝 (0:E) := hSopen.mem_nhds hS0
  have hpU_nhds : U ∈ 𝓝 p := hUopen.mem_nhds hpU
  have hS2_mem : γ ⁻¹' U ∈ 𝓝 (0:E) :=
    hγan.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hpU_nhds)
  let A' : Set E := A ∩ S ∩ γ ⁻¹' U
  have hA'_mem : A' ∈ 𝓝 (0:E) := Filter.inter_mem (Filter.inter_mem hA hS_mem) hS2_mem
  have hΦA'_mem : Φ '' A' ∈ 𝓝 (0 : W) := by
    have h := hsurjΦ A' hA'_mem
    rwa [hΦ0] at h
  refine ⟨U ∩ {y : Fin n → ℝ | C (y - p) ∈ Φ '' A'}, ?_, ?_⟩
  · have hcont : ContinuousAt (fun y : Fin n → ℝ => C (y - p)) p :=
      (C.continuous.comp (continuous_id.sub continuous_const)).continuousAt
    have hpre : (fun y : Fin n → ℝ => C (y - p)) ⁻¹' (Φ '' A') ∈ 𝓝 p := by
      have hmem : Φ '' A' ∈ 𝓝 ((fun y : Fin n → ℝ => C (y - p)) p) := by
        simpa using hΦA'_mem
      exact hcont.preimage_mem_nhds hmem
    exact Filter.inter_mem hpU_nhds hpre
  · intro z hz hgz
    obtain ⟨hzU, hzC⟩ := hz
    have hfz : f z = 0 := by simp [f, hgz]
    -- chart `z` in the level set
    obtain ⟨v, hvV, hvz⟩ := hγcsurj z hzU hfz
    have hv : v = C (z - p) := by rw [← hγcC v hvV, hvz]
    have hvA' : v ∈ Φ '' A' := by rw [hv]; exact hzC
    obtain ⟨s, hsA', hsv⟩ := hvA'
    have hsA : s ∈ A := hsA'.1.1
    have hsS : s ∈ S := hsA'.1.2
    have hsU : γ s ∈ U := hsA'.2
    have hfs : f (γ s) = 0 := by simp [f, hSsub s hsS]
    -- chart `γ s` in the level set and compare coordinates
    obtain ⟨v', hv'V, hv'eq⟩ := hγcsurj (γ s) hsU hfs
    have hv' : v' = C (γ s - p) := by rw [← hγcC v' hv'V, hv'eq]
    have hv'v : v' = v := by rw [hv']; exact hsv
    refine ⟨s, hsA, ?_⟩
    calc γ s = γc v' := hv'eq.symm
      _ = γc v := by rw [hv'v]
      _ = z := hvz

end Work.WilE7.DimAPI
