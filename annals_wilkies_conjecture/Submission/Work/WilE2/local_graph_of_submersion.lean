import Mathlib

namespace Work.WilE2

open scoped Topology ContDiff
open Filter

/-- Local graph (implicit function) theorem for a submersion.

If `g : (Fin p → ℝ) → (Fin k → ℝ) → (Fin k → ℝ)` is `C¹` at `(u₀, v₀)`, vanishes there, and its
partial differential in the second variable is invertible, then near `u₀` the zero set of `g` is
the graph of a `C¹` function `φ`, and locally this graph is unique. -/
theorem local_graph_of_submersion {p k : ℕ}
    (g : (Fin p → ℝ) → (Fin k → ℝ) → (Fin k → ℝ)) (u₀ : Fin p → ℝ) (v₀ : Fin k → ℝ)
    (hg : ContDiffAt ℝ 1 (Function.uncurry g) (u₀, v₀)) (hg0 : g u₀ v₀ = 0)
    (hinv : (fderiv ℝ (Function.uncurry g) (u₀, v₀) ∘L
        ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin k → ℝ)).IsInvertible) :
    ∃ (φ : (Fin p → ℝ) → (Fin k → ℝ)) (A : Set (Fin p → ℝ)) (B : Set (Fin k → ℝ)),
      IsOpen A ∧ IsOpen B ∧ u₀ ∈ A ∧ v₀ ∈ B ∧ ContDiffOn ℝ 1 φ A ∧ φ u₀ = v₀ ∧
      (∀ u ∈ A, g u (φ u) = 0) ∧
      (∀ u ∈ A, ∀ v ∈ B, g u v = 0 → v = φ u) := by
  have hn : (1 : ℕ∞ω) ≠ 0 := by simp
  -- The implicit function provided by the (Mathlib) implicit function theorem.
  let ψ : (Fin p → ℝ) → (Fin k → ℝ) := hg.implicitFunction hn hinv
  have hψ0 : ψ u₀ = v₀ := hg.implicitFunction_apply_self hn hinv
  have hψcd : ContDiffAt ℝ 1 ψ u₀ := hg.contDiffAt_implicitFunction hn hinv
  -- it solves the equation eventually …
  have hI1 : ∀ᶠ x in 𝓝 u₀, Function.uncurry g (x, ψ x) = Function.uncurry g (u₀, v₀) :=
    hg.eventually_apply_implicitFunction hn hinv
  -- … and it is the unique such function, eventually.
  have hI2 : ∀ᶠ v in 𝓝 (u₀, v₀),
      (Function.uncurry g v = Function.uncurry g (u₀, v₀) ↔ ψ v.1 = v.2) :=
    hg.eventually_apply_eq_iff_implicitFunction hn hinv
  -- Extract an open neighbourhood on which `ψ` satisfies the equation.
  obtain ⟨A₁, hA₁sub, hA₁o, hu₀A₁⟩ := mem_nhds_iff.1 hI1
  -- Extract an open neighbourhood on which `ψ` is `C¹`.
  obtain ⟨s₂, hs₂mem_raw, hs₂cd⟩ :=
    (contDiffWithinAt_iff_contDiffOn_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).1
      (hψcd : ContDiffWithinAt ℝ 1 ψ Set.univ u₀)
  have hs₂mem : s₂ ∈ 𝓝 u₀ := by simpa using hs₂mem_raw
  obtain ⟨A₂, hA₂sub, hA₂o, hu₀A₂⟩ := mem_nhds_iff.1 hs₂mem
  have hA₂cd : ContDiffOn ℝ 1 ψ A₂ := hs₂cd.mono hA₂sub
  -- Extract the uniqueness neighbourhood and split it as a product of open sets.
  obtain ⟨t, ht_sub, ht_o, ht_mem⟩ := mem_nhds_iff.1 hI2
  obtain ⟨A₃, B, hA₃o, hBo, hu₀A₃, hv₀B, hA₃B⟩ :=
    isOpen_prod_iff.1 ht_o u₀ v₀ ht_mem
  refine ⟨ψ, (A₁ ∩ A₂) ∩ A₃, B, (hA₁o.inter hA₂o).inter hA₃o, hBo,
    ⟨⟨hu₀A₁, hu₀A₂⟩, hu₀A₃⟩, hv₀B, ?_, hψ0, ?_, ?_⟩
  · exact ContDiffOn.mono hA₂cd (fun x hx => hx.1.2)
  · intro u hu
    have h1 : g u (ψ u) = g u₀ v₀ := hA₁sub hu.1.1
    rw [hg0] at h1
    exact h1
  · intro u hu v hv hgv
    have hmem : (u, v) ∈ A₃ ×ˢ B := ⟨hu.2, hv⟩
    have hiff : (g u v = g u₀ v₀ ↔ ψ u = v) := ht_sub (hA₃B hmem)
    have hleft : g u v = g u₀ v₀ := by rw [hgv, hg0]
    exact (hiff.mp hleft).symm

end Work.WilE2
