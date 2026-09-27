import Mathlib

namespace Work.Drive

/-- Two surjective-onto-`ℝ³` linear maps out of `ℝ⁴` with the same kernel induce the *same*
injectivity-and-vanishing behaviour on any family of three subspaces of `ℝ⁴`:
the infimum of the images vanishes simultaneously, and the restricted maps are simultaneously
injective.  The mechanism is that `f = φ ∘ g` for an injective endomorphism `φ` of `ℝ³`
(equivalently: the two maps differ by an automorphism of the target). -/
theorem sameKernel_transfer
    (f g : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hker : f.ker = g.ker) (hf : Function.Surjective f)
    (S : Fin 3 → Submodule ℝ (EuclideanSpace ℝ (Fin 4))) :
    ((⨅ k, Submodule.map f (S k)) = ⊥ ↔ (⨅ k, Submodule.map g (S k)) = ⊥) ∧
      ((∀ k, Function.Injective (f.comp (S k).subtype)) ↔
        (∀ k, Function.Injective (g.comp (S k).subtype))) := by
  -- Step 1: `g` is surjective as well.
  have hg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 := LinearMap.finrank_range_add_finrank_ker g
    have hfr : f.range = ⊤ := LinearMap.range_eq_top.mpr hf
    have hk : Module.finrank ℝ ↥f.ker = Module.finrank ℝ ↥g.ker := by rw [hker]
    have heq : Module.finrank ℝ ↥g.range = Module.finrank ℝ ↥f.range := by omega
    rw [heq, hfr]
    simp
  -- Step 2: build the injective `φ` with `f = φ ∘ g`.
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.mpr hg)
  have hgs : ∀ y, g (s y) = y := by
    intro y
    have h := congrArg
      (fun l : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) => l y) hs
    simpa using h
  let φ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := f.comp s
  have hf_apply : ∀ x, f x = φ (g x) := by
    intro x
    show f x = f (s (g x))
    have hmem : s (g x) - x ∈ g.ker := by
      rw [LinearMap.mem_ker]
      simp [hgs (g x)]
    rw [← hker] at hmem
    rw [LinearMap.mem_ker] at hmem
    have h0 : f (s (g x)) - f x = 0 := by simpa [map_sub] using hmem
    exact (sub_eq_zero.mp h0).symm
  have hf_eq : f = φ.comp g := LinearMap.ext hf_apply
  have hφinj : Function.Injective φ := by
    intro y y' hyy'
    obtain ⟨x, rfl⟩ := hg y
    obtain ⟨x', rfl⟩ := hg y'
    rw [← hf_apply x, ← hf_apply x'] at hyy'
    have hmem : x - x' ∈ f.ker := by
      rw [LinearMap.mem_ker]
      have h0 : f x - f x' = 0 := sub_eq_zero.mpr hyy'
      simpa [map_sub] using h0
    rw [hker] at hmem
    rw [LinearMap.mem_ker] at hmem
    have h0 : g x - g x' = 0 := by simpa [map_sub] using hmem
    exact sub_eq_zero.mp h0
  constructor
  · -- images: `map f (S k) = map φ (map g (S k))`, so the infima correspond through `φ`.
    have hmapk : ∀ k, Submodule.map φ (Submodule.map g (S k)) = Submodule.map f (S k) := by
      intro k
      rw [← Submodule.map_comp g φ (S k), ← hf_eq]
    have hinf : Submodule.map φ (⨅ k, Submodule.map g (S k)) = ⨅ k, Submodule.map f (S k) := by
      rw [Submodule.map_iInf φ hφinj]
      exact iInf_congr hmapk
    have hkerφ : φ.ker = ⊥ := LinearMap.ker_eq_bot.mpr hφinj
    have key : ∀ X : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Submodule.map φ X = ⊥ → X = ⊥ := by
      intro X hX
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h1 : φ x ∈ Submodule.map φ X := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      rw [hX] at h1
      have h2 : φ x = 0 := (Submodule.mem_bot ℝ).mp h1
      have h3 : x ∈ φ.ker := LinearMap.mem_ker.mpr h2
      rw [hkerφ] at h3
      exact (Submodule.mem_bot ℝ).mp h3
    constructor
    · intro h
      exact key _ (by rw [hinf]; exact h)
    · intro h
      rw [← hinf, h]
      simp
  · -- injectivity of the restrictions: it is exactly `S k ∩ ker = ⊥`.
    constructor
    · intro h k x y hxy
      have hxy' : g (x : EuclideanSpace ℝ (Fin 4)) = g (y : EuclideanSpace ℝ (Fin 4)) := by
        simpa using hxy
      refine h k ?_
      have hmem : (x : EuclideanSpace ℝ (Fin 4)) - (y : EuclideanSpace ℝ (Fin 4)) ∈ g.ker := by
        rw [LinearMap.mem_ker]
        have h0 : g (x : EuclideanSpace ℝ (Fin 4)) - g (y : EuclideanSpace ℝ (Fin 4)) = 0 :=
          sub_eq_zero.mpr hxy'
        simpa [map_sub] using h0
      rw [← hker] at hmem
      rw [LinearMap.mem_ker] at hmem
      have h0 : f (x : EuclideanSpace ℝ (Fin 4)) - f (y : EuclideanSpace ℝ (Fin 4)) = 0 := by
        simpa [map_sub] using hmem
      have hfxy : f (x : EuclideanSpace ℝ (Fin 4)) = f (y : EuclideanSpace ℝ (Fin 4)) :=
        sub_eq_zero.mp h0
      simpa using hfxy
    · intro h k x y hxy
      have hxy' : f (x : EuclideanSpace ℝ (Fin 4)) = f (y : EuclideanSpace ℝ (Fin 4)) := by
        simpa using hxy
      refine h k ?_
      have hmem : (x : EuclideanSpace ℝ (Fin 4)) - (y : EuclideanSpace ℝ (Fin 4)) ∈ f.ker := by
        rw [LinearMap.mem_ker]
        have h0 : f (x : EuclideanSpace ℝ (Fin 4)) - f (y : EuclideanSpace ℝ (Fin 4)) = 0 :=
          sub_eq_zero.mpr hxy'
        simpa [map_sub] using h0
      rw [hker] at hmem
      rw [LinearMap.mem_ker] at hmem
      have h0 : g (x : EuclideanSpace ℝ (Fin 4)) - g (y : EuclideanSpace ℝ (Fin 4)) = 0 := by
        simpa [map_sub] using hmem
      have hgxy : g (x : EuclideanSpace ℝ (Fin 4)) = g (y : EuclideanSpace ℝ (Fin 4)) :=
        sub_eq_zero.mp h0
      simpa using hgxy

end Work.Drive
