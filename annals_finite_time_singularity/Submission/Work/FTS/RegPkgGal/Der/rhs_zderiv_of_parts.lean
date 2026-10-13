import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.R5Slot
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.RegPkgGal.Der.ak_hasDerivAt_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

set_option maxHeartbeats 1600000

theorem rhs_zderiv_of_parts {α S : ℝ} {g Φ : Work.FTS.RegPkgGal.Fam} {N₁ N₂ N₃ N₄ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hL : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => -(Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z' θ)) d z ∧ |d| ≤ N₁)
    (hN₀ : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ N₂)
    (hN : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z' θ) d z ∧ |d| ≤ N₃)
    (hNs : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d z ∧ |d| ≤ N₄)
    (hmb : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |Work.Construction.mubar
        (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice g τ))
        (Work.Construction.N (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ))| ≤ M) :
    ∃ Nc : ℝ, 0 ≤ Nc ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) g τ z' θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z' θ) d z ∧ |d| ≤ Nc := by
  obtain ⟨M, hM0, hM⟩ := hmb
  have ha : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have ha1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  refine ⟨|N₁| + |N₂| + |N₃| + |N₄| + 20 * M, by positivity, ?_⟩
  intro τ hτ θ hθ z hz
  obtain ⟨d₁, hd₁, hb₁⟩ := hL τ hτ θ hθ z hz
  obtain ⟨d₂, hd₂, hb₂⟩ := hN₀ τ hτ θ hθ z hz
  obtain ⟨d₃, hd₃, hb₃⟩ := hN τ hτ θ hθ z hz
  obtain ⟨d₄, hd₄, hb₄⟩ := hNs τ hτ θ hθ z hz
  obtain ⟨dA, hdA, hbA⟩ := ak_hasDerivAt_bound ha ha1 hθ hz
  set c : ℝ := Work.Construction.mubar
      (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ))
      (Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) with hcdef
  have hcM : |c| ≤ M := by rw [hcdef]; exact hM τ hτ
  have hslice : Work.FTS.Galerkin.slice g τ = Work.FTS.Regularity.gSlice g τ := rfl
  have hdec : ∀ z' : ℝ, Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ g τ z' θ
      = (-c) * Work.Construction.AK (Work.FTS.Regularity.pExp α) z' θ
        + Work.Construction.N0 (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
            (Work.FTS.Regularity.gSlice g τ) z' θ
        + Work.Construction.N (Work.FTS.Regularity.pExp α)
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
            (Work.FTS.Regularity.gSlice Φ τ) z' θ
        + Work.Construction.Nstar (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
            (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
            (Work.FTS.Regularity.gSlice g τ) z' θ := by
    intro z'
    rw [hcdef]
    rfl
  refine ⟨d₁ + ((-c) * dA + d₂ + d₃ + d₄), ?_, ?_⟩
  · have e2 : HasDerivAt (fun z' => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d₂ z := hd₂
    have e3 : HasDerivAt (fun z' => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z' θ) d₃ z := hd₃
    have e4 : HasDerivAt (fun z' => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ g τ)
        (Work.FTS.Regularity.gSlice g τ) z' θ) d₄ z := hd₄
    have e5 : HasDerivAt (fun z' => (-c) * Work.Construction.AK (Work.FTS.Regularity.pExp α) z' θ)
        ((-c) * dA) z := hdA.const_mul (-c)
    have hall := hd₁.add (((e5.add e2).add e3).add e4)
    convert hall using 1
    · funext z'
      simp only [Pi.add_apply, Work.FTS.Galerkin.dynLin, hslice, hdec z']
  · have h1 : |d₁| ≤ |N₁| := le_trans hb₁ (le_abs_self N₁)
    have h2 : |d₂| ≤ |N₂| := le_trans hb₂ (le_abs_self N₂)
    have h3 : |d₃| ≤ |N₃| := le_trans hb₃ (le_abs_self N₃)
    have h4 : |d₄| ≤ |N₄| := le_trans hb₄ (le_abs_self N₄)
    have hmul : |(-c) * dA| ≤ 20 * M := by
      rw [abs_mul, abs_neg]
      calc |c| * |dA| ≤ M * 20 := mul_le_mul hcM hbA (abs_nonneg _) hM0
        _ = 20 * M := by ring
    have ht1 := abs_add_le ((-c) * dA) d₂
    have ht2 := abs_add_le (((-c) * dA) + d₂) d₃
    have ht3 := abs_add_le ((((-c) * dA) + d₂) + d₃) d₄
    have ht0 := abs_add_le d₁ (((((-c) * dA) + d₂) + d₃) + d₄)
    linarith [abs_nonneg d₁, abs_nonneg d₂, abs_nonneg d₃, abs_nonneg d₄,
      abs_nonneg ((-c) * dA), ht0, ht1, ht2, ht3, h1, h2, h3, h4, hmul]

end Work.FTS.RegPkgGal.Der
