import Mathlib
import Submission.Work.Whitney.PushDefs

/-!
# Gluing an ambient push into a modified immersion

`Work.Whitney.HasAmbientPushData` records the *target-side* ("cut and paste") form of the Whitney
push: an open collar `W₀ ⊆ W`, an open set `O ⊇ f '' frontier W₀` on which a diffeomorphism `ψ` of
`ℝ^{2n}` (with inverse `σ`) is the identity, and the *placement* conditions saying that `ψ` moves
the sheet over `W₀` off the image of everything outside `W₀` (up to the parts coming from `W₀`
itself), and off the two double point values `f p₂`, `f q₂`.

This file proves the gluing step: such data produce the conclusion of
`Work.Whitney.exists_manifold_push`, i.e. the collar data `HasManifoldCollarData`.  The modified
map is

  `i y = if y ∈ W₀ then ψ (f y) else f y`,

which is well defined and smooth because `ψ` is the identity on the open neighbourhood `O` of
`f '' frontier W₀`.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

variable {n : ℕ}

section RightInverse

/-- The manifold derivative of a smooth self-map of `ℝ^N` having a smooth inverse is injective. -/
theorem injective_mfderiv_of_rightInverse {N : ℕ}
    {ψ σ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)}
    (hψ : ContMDiff (𝓡 N) (𝓡 N) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hσ : ContMDiff (𝓡 N) (𝓡 N) ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hleft : ∀ y, σ (ψ y) = y) (x : EuclideanSpace ℝ (Fin N)) :
    Function.Injective (mfderiv (𝓡 N) (𝓡 N) ψ x) := by
  have hσd : MDifferentiableAt (𝓡 N) (𝓡 N) σ (ψ x) :=
    (hσ (ψ x)).mdifferentiableAt (by simp)
  have hψd : MDifferentiableAt (𝓡 N) (𝓡 N) ψ x := (hψ x).mdifferentiableAt (by simp)
  have hcomp : mfderiv (𝓡 N) (𝓡 N) (fun y => σ (ψ y)) x
      = (mfderiv (𝓡 N) (𝓡 N) σ (ψ x)).comp (mfderiv (𝓡 N) (𝓡 N) ψ x) :=
    mfderiv_comp x hσd hψd
  have hid : mfderiv (𝓡 N) (𝓡 N) (fun y => σ (ψ y)) x
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 N) x) := by
    rw [show (fun y => σ (ψ y)) = id from funext hleft, mfderiv_id]
  have hchain : (mfderiv (𝓡 N) (𝓡 N) σ (ψ x)).comp (mfderiv (𝓡 N) (𝓡 N) ψ x)
      = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 N) x) := hcomp.symm.trans hid
  have hleft' : ∀ v : TangentSpace (𝓡 N) x,
      v = (mfderiv (𝓡 N) (𝓡 N) σ (ψ x)) ((mfderiv (𝓡 N) (𝓡 N) ψ x) v) := by
    intro v
    have h := congrArg
      (fun L : TangentSpace (𝓡 N) x →L[ℝ] TangentSpace (𝓡 N) x => L v) hchain
    exact h.symm
  intro a b hab
  have h2 := congrArg (mfderiv (𝓡 N) (𝓡 N) σ (ψ x)) hab
  exact (hleft' a).trans (h2.trans (hleft' b).symm)

end RightInverse

section Glue

/-- **The gluing step.**  The ambient push data (a diffeomorphism of the target which is the
identity near `f '' frontier W₀`, with the placement properties) produce the collar data: the map
`i = ψ ∘ f` on `W₀` and `f` outside is a smooth immersion, injective on `W₀`, agreeing with `f`
outside `W₀`, whose image on `W₀` only meets `f '' W₀` inside `f '' W₀` and misses the two double
point values. -/
theorem collarData_of_ambientPushData {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hdata : HasAmbientPushData f W p₁ p₂ q₁ q₂) :
    HasManifoldCollarData f W p₁ p₂ q₁ q₂ := by
  classical
  obtain ⟨W₀, O, ψ, σ, hW₀o, hW₀W, hp₂, hq₂, hp₁, hq₁, hOo, hOfr, hOid, hleft, hright,
    hψc, hσc, hplace, hne₁, hne₂⟩ := hdata
  have hinjψ : Function.Injective ψ := fun x y h => by
    have h2 := congrArg σ h
    rwa [hleft x, hleft y] at h2
  have hfj : Set.InjOn f W₀ := by
    intro x hx y hy hxy
    rcases hclean x y (hW₀W hx) (hW₀W hy) hxy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exact absurd (h1 ▸ hx) hp₁
    · exact absurd (h2 ▸ hy) hp₁
    · exact absurd (h1 ▸ hx) hq₁
    · exact absurd (h2 ▸ hy) hq₁
  let i : M → EuclideanSpace ℝ (Fin (2 * n)) := fun y => if y ∈ W₀ then ψ (f y) else f y
  have hiW : ∀ y ∈ W₀, i y = ψ (f y) := by intro y hy; simp only [i, if_pos hy]
  have hinW : ∀ y ∉ W₀, i y = f y := by intro y hy; simp only [i, if_neg hy]
  have hψne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hfcont : Continuous f := hf.continuous
  refine ⟨W₀, i, hW₀o, hW₀W, hp₂, hq₂, hp₁, hq₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness of `i`
    intro y
    by_cases hy : y ∈ W₀
    · have hcomp : ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ψ (f z)) y :=
        (hψc (f y)).comp y (hf y)
      exact hcomp.congr_of_eventuallyEq (by
        filter_upwards [hW₀o.mem_nhds hy] with z hz
        exact hiW z hz)
    · by_cases hyO : f y ∈ O
      · refine (hf y).congr_of_eventuallyEq ?_
        filter_upwards [(hfcont.continuousAt).preimage_mem_nhds (hOo.mem_nhds hyO)] with z hz
        by_cases hzW : z ∈ W₀
        · rw [hiW z hzW, hOid (f z) hz]
        · rw [hinW z hzW]
      · have hcl : y ∉ closure W₀ := by
          intro h
          have h' : y ∈ interior W₀ ∪ frontier W₀ := by
            rw [← closure_eq_interior_union_frontier]; exact h
          rcases h' with h' | h'
          · rw [hW₀o.interior_eq] at h'; exact hy h'
          · exact hyO (hOfr ⟨y, h', rfl⟩)
        refine (hf y).congr_of_eventuallyEq ?_
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with z hz
        exact hinW z (fun h => hz (subset_closure h))
  · -- `i` is an immersion
    intro y
    by_cases hy : y ∈ W₀
    · have hev : i =ᶠ[𝓝 y] (fun z => ψ (f z)) := by
        filter_upwards [hW₀o.mem_nhds hy] with z hz
        rw [hiW z hz]
      rw [hev.mfderiv_eq]
      have hψd : MDifferentiableAt (𝓡 (2 * n)) (𝓡 (2 * n)) ψ (f y) :=
        (hψc (f y)).mdifferentiableAt hψne
      have hfd : MDifferentiableAt (𝓡 n) (𝓡 (2 * n)) f y := (hf y).mdifferentiableAt hψne
      rw [show (fun z => ψ (f z)) = (ψ ∘ f) from rfl, mfderiv_comp y hψd hfd]
      intro a b hab
      exact himm y (injective_mfderiv_of_rightInverse hψc hσc hleft (f y) hab)
    · by_cases hyO : f y ∈ O
      · have hev : i =ᶠ[𝓝 y] f := by
          filter_upwards [(hfcont.continuousAt).preimage_mem_nhds (hOo.mem_nhds hyO)] with z hz
          by_cases hzW : z ∈ W₀
          · rw [hiW z hzW, hOid (f z) hz]
          · rw [hinW z hzW]
        rw [hev.mfderiv_eq]
        exact himm y
      · have hcl : y ∉ closure W₀ := by
          intro h
          have h' : y ∈ interior W₀ ∪ frontier W₀ := by
            rw [← closure_eq_interior_union_frontier]; exact h
          rcases h' with h' | h'
          · rw [hW₀o.interior_eq] at h'; exact hy h'
          · exact hyO (hOfr ⟨y, h', rfl⟩)
        have hev : i =ᶠ[𝓝 y] f := by
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hcl] with z hz
          exact hinW z (fun h => hz (subset_closure h))
        rw [hev.mfderiv_eq]
        exact himm y
  · -- injectivity on `W₀`
    intro x hx y hy hxy
    rw [hiW x hx, hiW y hy] at hxy
    exact hfj hx hy (hinjψ hxy)
  · -- agreement outside `W₀`
    exact hinW
  · -- placement
    have himg : i '' W₀ = ψ '' (f '' W₀) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, (hiW x hx).symm⟩
      · rintro ⟨w, ⟨x, hx, rfl⟩, hz⟩
        exact ⟨x, hx, (hiW x hx).trans hz⟩
    rw [himg]
    exact hplace
  · rw [show i '' W₀ = ψ '' (f '' W₀) from (by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, (hiW x hx).symm⟩
      · rintro ⟨w, ⟨x, hx, rfl⟩, hz⟩
        exact ⟨x, hx, (hiW x hx).trans hz⟩)]
    exact hne₁
  · rw [show i '' W₀ = ψ '' (f '' W₀) from (by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨f x, ⟨x, hx, rfl⟩, (hiW x hx).symm⟩
      · rintro ⟨w, ⟨x, hx, rfl⟩, hz⟩
        exact ⟨x, hx, (hiW x hx).trans hz⟩)]
    exact hne₂

end Glue

end Work.Whitney
