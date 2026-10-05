import Mathlib
import Submission.Work.RPB.B3.UniformInverseAux
import Submission.Work.RPB.B5.slabGlobalExtendPeriodic
import Submission.Work.RPB.B5.slabDerivBounds
import Submission.Work.RPB.B5.slabMonoExistsUnique
import Submission.Work.RPB.B5.slabInverseContDiffOn

open Set Filter
open scoped Topology ContDiff

set_option autoImplicit false

namespace Work.RPB.B5

noncomputable section

/-- Auxiliary packaging: `invFiber f ε₀ σ` is the classically chosen preimage of `σ` under `f`
on the interval `(-ε₀, ε₀)`, or `0` if there is none.  It manifestly depends only on the function
`f`, which is what makes `inverseR` invariant under manipulations of the parameters that do not
change the fibre `ρ ↦ S τ t ρ`. -/
private def invFiber (f : ℝ → ℝ) (ε₀ σ : ℝ) : ℝ := by
  classical
  exact if h : ∃ ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ f ρ = σ then Classical.choose h else 0

/-- `inverseR S ε₀ τ t σ` is by construction `invFiber` applied to the fibre `ρ ↦ S τ t ρ`. -/
private theorem inverseR_eq_invFiber (S : ℝ → ℝ → ℝ → ℝ) (ε₀ τ t σ : ℝ) :
    Work.RPB.B3.inverseR S ε₀ τ t σ = invFiber (fun ρ : ℝ => S τ t ρ) ε₀ σ := rfl

/-- `2π`-periodicity of `inverseR` in the `t`-variable: for a family periodic in `t`, the fibre
`ρ ↦ S τ t ρ` is unchanged by `t ↦ t + 2π`, hence so is `inverseR`. -/
theorem inverseR_periodic (S : ℝ → ℝ → ℝ → ℝ) (ε₀ : ℝ)
    (hper : ∀ τ t ρ, S τ (t + 2 * Real.pi) ρ = S τ t ρ) (τ t σ : ℝ) :
    Work.RPB.B3.inverseR S ε₀ τ (t + 2 * Real.pi) σ
      = Work.RPB.B3.inverseR S ε₀ τ t σ := by
  have hf : (fun ρ : ℝ => S τ (t + 2 * Real.pi) ρ) = (fun ρ : ℝ => S τ t ρ) :=
    funext (hper τ t)
  rw [inverseR_eq_invFiber, inverseR_eq_invFiber, hf]

/-- **Uniform local inversion of a `C⁸`-family `(τ,t,ρ) ↦ S τ t ρ` on the slab
`[0,1] × ℝ × (-ρ₀,ρ₀)`, periodic in `t`, with a two-sided inverse.**

This is the strengthening of `slabUniformInverse` that additionally records that the inverse
`rho` is `2π`-periodic in `t` (for *every* `τ`, using only that the fibre is unchanged by the
shift) and that it is also a *right* inverse: `rho τ t (S τ t ρ) = ρ` for `ρ ∈ (-ε,ε)`.  The
latter is deduced from the strict monotonicity of the slice `ρ ↦ S τ t ρ` on `(-ε₀,ε₀)` together
with the agreement of the globalized `S'` with `S` near `ρ = 0`. -/
theorem slabUniformInverseStrong (S : ℝ → ℝ → ℝ → ℝ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hS : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
        (Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hper : ∀ τ t ρ, S τ (t + 2 * Real.pi) ρ = S τ t ρ)
    (h0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, S τ t 0 = 0)
    (hδ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, 0 < deriv (fun ρ => S τ t ρ) 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ₀ ∧ ∃ rho : ℝ → ℝ → ℝ → ℝ,
      ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => rho z.1 z.2.1 z.2.2)
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ε) ε) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, rho τ t 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ σ ∈ Set.Ioo (-ε) ε,
        rho τ t σ ∈ Set.Ioo (-ρ₀) ρ₀) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ σ ∈ Set.Ioo (-ε) ε,
        S τ t (rho τ t σ) = σ) ∧
      (∀ τ t σ, rho τ (t + 2 * Real.pi) σ = rho τ t σ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ε) ε,
        rho τ t (S τ t ρ) = ρ) := by
  obtain ⟨S', hS'8, hS'per, hS'0, hS'agree⟩ := slabGlobalExtendPeriodic S ρ₀ hρ₀ hS hper h0
  -- Derivative positivity at `ρ = 0` for the globalized family, on `[0,1]`.
  have hS'δ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, 0 < deriv (fun ρ => S' τ t ρ) 0 := by
    intro τ hτ t
    have hmem : Set.Ioo (-(ρ₀ / 2)) (ρ₀ / 2) ∈ nhds (0 : ℝ) :=
      isOpen_Ioo.mem_nhds (by constructor <;> linarith)
    have hev : (fun ρ => S' τ t ρ) =ᶠ[nhds (0 : ℝ)] (fun ρ => S τ t ρ) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Set.Ioo (-(ρ₀ / 2)) (ρ₀ / 2), hmem, fun ρ hρ => by
        rw [Set.mem_Ioo] at hρ
        exact hS'agree τ hτ t ρ (by rw [abs_lt]; exact hρ)⟩
    rw [hev.deriv_eq]
    exact hδ τ hτ t
  obtain ⟨ε₀', hε₀', δ, hδ0, M, hM0, hbound⟩ := slabDerivBounds S' hS'8 hS'per hS'δ
  -- Shrink the positivity radius so that `(-ε₀,ε₀) ⊆ (-ρ₀/2, ρ₀/2)`, where `S' = S`.
  set ε₀ : ℝ := min ε₀' (ρ₀ / 2) with hε₀def
  have hε₀0 : 0 < ε₀ := lt_min hε₀' (by linarith)
  have hε₀le : ε₀ ≤ ε₀' := min_le_left _ _
  have hε₀le2 : ε₀ ≤ ρ₀ / 2 := min_le_right _ _
  have hbound' : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Icc (-ε₀) ε₀,
      δ ≤ deriv (fun ρ => S' τ t ρ) ρ ∧ |deriv (fun ρ => S' τ t ρ) ρ| ≤ M := by
    intro τ hτ t ρ hρ
    exact hbound τ hτ t ρ ⟨le_trans (neg_le_neg hε₀le) hρ.1, le_trans hρ.2 hε₀le⟩
  have hderivfn : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Icc (-ε₀) ε₀,
      δ ≤ deriv (fun ρ => S' τ t ρ) ρ := fun τ hτ t ρ hρ => (hbound' τ hτ t ρ hρ).1
  have hM := slabMonoExistsUnique S' hS'8 hS'0 δ ε₀ hδ0 hε₀0 hderivfn
  have hcover : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ σ ∈ Set.Ioo (-(δ*ε₀)) (δ*ε₀),
      ∃! ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S' τ t ρ = σ :=
    fun τ hτ t σ hσ => (hM τ hτ t).2.2.2 σ (abs_lt.mpr hσ)
  have hderivne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ε₀) ε₀,
      deriv (fun ρ => S' τ t ρ) ρ ≠ 0 := by
    intro τ hτ t ρ hρ
    have h := (hbound' τ hτ t ρ (Set.Ioo_subset_Icc_self hρ)).1
    intro hc; rw [hc] at h; linarith
  have hcd := slabInverseContDiffOn S' hS'8 ε₀ δ hε₀0 hδ0 hderivne hcover
  -- The uniform interval, also capped by `ε₀` (for the right-inverse identity) and by `ρ₀ / 2`.
  set ε : ℝ := min (δ * ε₀) (min (ρ₀ / 2) ε₀) with hεdef
  have hεpos : 0 < ε := lt_min (mul_pos hδ0 hε₀0) (lt_min (by linarith) hε₀0)
  have hεle : ε ≤ ρ₀ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle2 : ε ≤ δ * ε₀ := min_le_left _ _
  have hεle3 : ε ≤ ε₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ε, hεpos, le_trans hεle (by linarith), ?_⟩
  refine ⟨fun τ t σ => Work.RPB.B3.inverseR S' ε₀ τ t σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    refine hcd.mono ?_
    intro z hz
    have hz' := hz
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, Set.mem_Ioo, true_and] at hz'
    exact Set.mem_prod.mpr ⟨hz'.1, Set.mem_prod.mpr
      ⟨trivial, Set.Ioo_subset_Ioo (by linarith [hεle2]) (by linarith [hεle2]) hz'.2⟩⟩
  · -- vanishes at zero
    intro τ hτ t
    refine Work.RPB.B3.inverseR_eq (S := S') (ε₀ := ε₀) (τ := τ) (t := t)
      (σ := 0) (ρ := 0) ⟨by linarith, by linarith⟩ (hS'0 τ t) ?_
    intro ρ' hρ' hS'ρ'
    have hmono := (hM τ hτ t).1
    have h0mem : (0 : ℝ) ∈ Set.Icc (-ε₀) ε₀ := ⟨by linarith, by linarith⟩
    exact hmono.injOn (Set.Ioo_subset_Icc_self hρ') h0mem (by rw [hS'ρ', hS'0 τ t])
  · -- value bound `rho ∈ (-ρ₀, ρ₀)`
    intro τ hτ t σ hσ
    have hσlt : |σ| < δ * ε₀ := lt_of_lt_of_le (abs_lt.mpr hσ) hεle2
    have hex : ∃ ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S' τ t ρ = σ :=
      ExistsUnique.exists ((hM τ hτ t).2.2.2 σ hσlt)
    exact Set.Ioo_subset_Ioo (by linarith [hε₀le2]) (by linarith [hε₀le2])
      (Work.RPB.B3.inverseR_spec hex).1
  · -- left inverse property `S τ t (rho τ t σ) = σ`
    intro τ hτ t σ hσ
    have hσlt : |σ| < δ * ε₀ := lt_of_lt_of_le (abs_lt.mpr hσ) hεle2
    have hex : ∃ ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S' τ t ρ = σ :=
      ExistsUnique.exists ((hM τ hτ t).2.2.2 σ hσlt)
    obtain ⟨hmem, heq⟩ := Work.RPB.B3.inverseR_spec hex
    rw [← hS'agree τ hτ t _ (by
      rw [abs_lt]
      exact ⟨by linarith [hmem.1, hε₀le2], by linarith [hmem.2, hε₀le2]⟩)]
    exact heq
  · -- periodicity in `t`, for every `τ`
    intro τ t σ
    exact inverseR_periodic S' ε₀ hS'per τ t σ
  · -- right inverse property `rho τ t (S τ t ρ) = ρ`
    intro τ hτ t ρ hρ
    have hρabs : |ρ| < ρ₀ / 2 := by
      rw [abs_lt]
      exact ⟨by linarith [hρ.1, hεle], by linarith [hρ.2, hεle]⟩
    have hρmem : ρ ∈ Set.Ioo (-ε₀) ε₀ := by
      rw [abs_lt] at hρabs
      exact ⟨by linarith [hρ.1, hεle3], by linarith [hρ.2, hεle3]⟩
    have hSρ : S' τ t ρ = S τ t ρ := hS'agree τ hτ t ρ hρabs
    refine Work.RPB.B3.inverseR_eq (S := S') (ε₀ := ε₀) (τ := τ) (t := t)
      (σ := S τ t ρ) (ρ := ρ) hρmem hSρ ?_
    intro ρ' hρ' hS'ρ'
    have hmono := (hM τ hτ t).1
    exact hmono.injOn (Set.Ioo_subset_Icc_self hρ') (Set.Ioo_subset_Icc_self hρmem)
      (by rw [hS'ρ', hSρ])

end

end Work.RPB.B5
