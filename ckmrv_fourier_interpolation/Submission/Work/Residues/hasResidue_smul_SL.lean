import Mathlib
import Submission.Work.Residues.Poles
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold
open Filter
open scoped Topology

open Work.Kernels

/-! ## The cross-ratio identity for `jFun` and `nFun`

`nFun γ ζ = aζ + b` and `jFun γ ζ = cζ + d` are the numerator and denominator of the Möbius
transformation attached to `γ ∈ SL(2,ℤ)`.  Since `ad - bc = det γ = 1`, the standard cross
ratio identity

  `nFun γ ζ * jFun γ η - nFun γ η * jFun γ ζ = ζ - η`

holds; it is the algebraic source of `d(γ•τ)/dτ = j(γ,τ)^{-2}`. -/

/-- **Cross-ratio identity.**  For `γ ∈ SL(2,ℤ)`,
`nFun γ ζ * jFun γ η - nFun γ η * jFun γ ζ = ζ - η`. -/
lemma nFun_mul_jFun_sub (γ : SL(2,ℤ)) (ζ η : ℂ) :
    nFun γ ζ * jFun γ η - nFun γ η * jFun γ ζ = ζ - η := by
  rw [nFun_apply, jFun_apply, nFun_apply, jFun_apply]
  have hdet : (γ 0 0 : ℂ) * (γ 1 1 : ℂ) - (γ 0 1 : ℂ) * (γ 1 0 : ℂ) = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    have h' := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at h'
    simpa using h'
  linear_combination hdet * (ζ - η)

/-- The Möbius action on `ℍ` satisfies the cross-ratio identity
`γ•ζ - γ•η = (ζ - η) / (j(γ,ζ) j(γ,η))`. -/
lemma coe_smul_sub (γ : SL(2,ℤ)) (ζ η : ℍ) :
    ((γ • ζ : ℍ) : ℂ) - ((γ • η : ℍ) : ℂ)
      = ((ζ : ℂ) - (η : ℂ)) / (jFun γ (ζ : ℂ) * jFun γ (η : ℂ)) := by
  rw [coe_smul_eq γ ζ, coe_smul_eq γ η]
  have h1 := jFun_ne_zero γ ζ
  have h2 := jFun_ne_zero γ η
  rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
  rw [mul_comm (jFun γ (ζ:ℂ)) (nFun γ (η:ℂ)), nFun_mul_jFun_sub]

/-- **Residues are transported by the Möbius action of `SL(2,ℤ)`.**  If `f` has residue `c`
at `γ • z`, then the slashed function `τ ↦ j(γ,τ)^{-k} f (γ • τ)` has residue
`j(γ,z)^{2-k}·c` at `z`: the factor of automorphy contributes `j(γ,z)^{-k}`, and the
substitution `σ = γ•τ` contributes `j(γ,z)^{2}` because `d(γ•τ)/dτ = j(γ,τ)^{-2}`. -/
theorem hasResidue_smul_SL {f : ℍ → ℂ} {z : ℍ} {c : ℂ} (γ : SL(2,ℤ)) (k : ℤ)
    (h : Work.Residues.HasResidue f (γ • z) c) :
    Work.Residues.HasResidue
      (fun τ : ℍ => (Work.Kernels.jFun γ (τ : ℂ)) ^ (-k) * f (γ • τ)) z
      ((Work.Kernels.jFun γ (z : ℂ)) ^ (2 - k) * c) := by
  rw [HasResidue] at h ⊢
  have hL : jFun γ (z : ℂ) ≠ 0 := jFun_ne_zero γ z
  -- the action `τ ↦ γ • τ` maps `𝓝[≠] z` to `𝓝[≠] (γ • z)`
  have hΦ : Tendsto (fun τ : ℍ => γ • τ) (𝓝[≠] z) (𝓝[≠] (γ • z)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun τ : ℍ => γ • τ) := by
        simpa using continuous_const_smul (glOf γ)
      exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hh => hτ (MulAction.injective γ hh)
  -- `(γ•τ - γ•z) f (γ•τ) → c`
  have hA : Tendsto (fun τ : ℍ => (((γ • τ : ℍ) : ℂ) - ((γ • z : ℍ) : ℂ)) * f (γ • τ))
      (𝓝[≠] z) (𝓝 c) := h.comp hΦ
  -- `j(γ,τ)^{1-k} → j(γ,z)^{1-k}`
  have hB : Tendsto (fun τ : ℍ => jFun γ (τ : ℂ) ^ (1 - k)) (𝓝[≠] z)
      (𝓝 (jFun γ (z : ℂ) ^ (1 - k))) := by
    have hcont : Continuous (fun τ : ℍ => jFun γ (τ : ℂ)) := by
      simp only [jFun_apply]; fun_prop
    have h1 : Tendsto (fun τ : ℍ => jFun γ (τ : ℂ)) (𝓝[≠] z) (𝓝 (jFun γ (z : ℂ))) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact h1.zpow₀ (1 - k) (Or.inl hL)
  have hG : Tendsto (fun τ : ℍ => jFun γ (z : ℂ) * (jFun γ (τ : ℂ) ^ (1 - k)
      * ((((γ • τ : ℍ) : ℂ) - ((γ • z : ℍ) : ℂ)) * f (γ • τ))))
      (𝓝[≠] z) (𝓝 (jFun γ (z : ℂ) * (jFun γ (z : ℂ) ^ (1 - k) * c))) :=
    (hB.mul hA).const_mul _
  -- pointwise rewriting of the integrand using the cross-ratio identity
  have hF_eq : (fun τ : ℍ => ((τ : ℂ) - (z : ℂ)) * (jFun γ (τ : ℂ) ^ (-k) * f (γ • τ)))
      = fun τ : ℍ => jFun γ (z : ℂ) * (jFun γ (τ : ℂ) ^ (1 - k)
          * ((((γ • τ : ℍ) : ℂ) - ((γ • z : ℍ) : ℂ)) * f (γ • τ))) := by
    funext τ
    rw [show ((τ : ℂ) - (z : ℂ))
        = ((((γ • τ : ℍ) : ℂ) - ((γ • z : ℍ) : ℂ)) * (jFun γ (τ : ℂ) * jFun γ (z : ℂ))) by
      rw [coe_smul_sub γ τ z, div_mul_cancel₀ _ (mul_ne_zero (jFun_ne_zero γ τ) hL)]]
    have hzpow : jFun γ (τ : ℂ) * jFun γ (τ : ℂ) ^ (-k) = jFun γ (τ : ℂ) ^ (1 - k) := by
      have h2 : jFun γ (τ : ℂ) ^ ((1 : ℤ) + (-k))
          = jFun γ (τ : ℂ) ^ (1 : ℤ) * jFun γ (τ : ℂ) ^ (-k) :=
        zpow_add₀ (jFun_ne_zero γ τ) 1 (-k)
      rw [zpow_one] at h2
      rw [show (1 : ℤ) + (-k) = 1 - k by ring] at h2
      exact h2.symm
    rw [← hzpow]
    ring
  rw [hF_eq]
  have htarget : jFun γ (z : ℂ) * (jFun γ (z : ℂ) ^ (1 - k) * c)
      = jFun γ (z : ℂ) ^ (2 - k) * c := by
    rw [show (2 : ℤ) - k = 1 + (1 - k) by ring, zpow_add₀ hL, zpow_one]
    ring
  rw [← htarget]
  exact hG

end Work.Residues
