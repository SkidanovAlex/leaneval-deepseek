import Mathlib
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.Residues.ResidueOrbit
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Residues.AfunPlus_neg_one
import Submission.Work.Residues.AfunMinus_neg_one
import Submission.Work.Asymptotics.EpolyWindowE_pole

namespace Work.CKFinal.LineDecay

open UpperHalfPlane
open Filter
open scoped Topology Manifold

namespace KhatSecondResidue

open Work.Kernels

/-- **The cleared form of the second-variable kernel.**  For `ζ` with `j ζ ≠ j τ` the cleared
kernel factors as `K̂^{Clear}(τ,ζ) = Δ(τ)Δ(ζ)^e (j τ - j ζ) K̂(τ,ζ)`, hence

  `K̂(τ,ζ)·(j ζ - j τ) = - K̂^{Clear}(τ,ζ) / (Δ(τ)Δ(ζ)^e)`.

The right hand side, extended by that formula, is holomorphic in `ζ` on all of `ℍ` because the
cleared kernel is.  So if it *vanishes* at a point `z₀` of the `SL(2,ℤ)`-orbit of `τ` with
`j'(z₀) ≠ 0`, the residue of `ζ ↦ K̂(τ,ζ)` at `z₀` is zero: it equals
`(-K̂^{Clear}(τ,z₀)/(Δ(τ)Δ(z₀)^e)) / j'(z₀)`. -/
lemma khat_snd_residue (ℓ : LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ)
    {z₀ : ℍ} (hj : jInvariantFun z₀ = jInvariantFun τ)
    (hz₀ : Work.Residues.jprime z₀ ≠ 0) (hzero : KhatClear ℓ d τ z₀ = 0) :
    Work.Residues.HasResidue (fun ζ : ℍ => Khat ℓ d τ ζ) z₀ 0 := by
  have hAdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun ζ : ℍ => -(KhatClear ℓ d τ ζ / (DeltaFun τ * DeltaFun ζ ^ Work.Residues.dpow d)))
      z₀ := by
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun ζ : ℍ => KhatClear ℓ d τ ζ) z₀ :=
      (KernelClear_growth_z ℓ d hd τ).2.1 z₀
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (fun ζ : ℍ => DeltaFun τ * DeltaFun ζ ^ Work.Residues.dpow d) z₀ :=
      mdifferentiableAt_const.mul ((ClassicalFacts.DeltaFun_mem_InP.1 z₀).pow _)
    exact (h1.div h2 (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z₀)))).neg
  have hmain := Work.Residues.hasResidue_of_cleared (f := fun ζ : ℍ => Khat ℓ d τ ζ)
    (A := fun ζ : ℍ => -(KhatClear ℓ d τ ζ / (DeltaFun τ * DeltaFun ζ ^ Work.Residues.dpow d)))
    (z := τ) (z₀ := z₀) (c := Work.Residues.jprime z₀) hAdiff hj
    (Work.Residues.tendsto_slope_jprime z₀) hz₀ ?_
  · have hval : -(KhatClear ℓ d τ z₀ / (DeltaFun τ * DeltaFun z₀ ^ Work.Residues.dpow d))
        / Work.Residues.jprime z₀ = 0 := by
      rw [hzero]; simp
    rwa [hval] at hmain
  · filter_upwards [self_mem_nhdsWithin,
      (Work.Residues.tendsto_slope_jprime z₀).eventually (eventually_ne_nhds hz₀)]
      with ζ _ hζne
    have hslope : (jInvariantFun ζ - jInvariantFun z₀) / ((ζ : ℂ) - (z₀ : ℂ)) ≠ 0 := hζne
    have hjnz : jInvariantFun ζ - jInvariantFun z₀ ≠ 0 := by
      intro h0; exact hslope (by rw [h0, zero_div])
    have hne : jInvariantFun τ ≠ jInvariantFun ζ := fun h0 => hjnz (by rw [hj, h0, sub_self])
    have hD : DeltaFun τ * DeltaFun ζ ^ Work.Residues.dpow d ≠ 0 :=
      mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
        (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero ζ))
    rw [Work.Asymptotics.KhatClear_eq_growthPrefactor_mul ℓ d hd hne, ← neg_div, eq_div_iff hD]
    simp only [growthPrefactor, Work.Residues.dpow]
    ring

end KhatSecondResidue

open KhatSecondResidue

/-- **The second-variable residue of `K̂` vanishes on the `T`-orbit of `τ`.**  For fixed `τ` with
`j'(τ) ≠ 0`, the kernel `ζ ↦ K̂^{(d)}(τ,ζ)` has residue `0` both at the diagonal point `ζ = τ`
and at `ζ = τ + 1 = Tτ`.

Both points lie on the `SL(2,ℤ)`-orbit of `τ`, so the *cleared* kernel
`K̂^{Clear}(τ,ζ) = Δ(τ)Δ(ζ)^e(jτ - jζ)K̂(τ,ζ)` is the holomorphic function whose value at the
pole, divided by `j'`, is the residue (CKMRV Theorem 4.9(3), here in the second variable:
`Work.Residues.hasResidue_of_cleared`).  The vanishing of the residues is thus the vanishing of
the cleared kernel, `KhatClear_self_zero` and `KhatClear_vadd_neg_one_zero` respectively: the two
pole residues of `K_+` and `K_-` cancel in the difference `K̂ = (K_+ - K_-)/2`.  This is the
`T`-orbit analogue of `Work.Residues.hasResidue_Khat_second`, which handles `ζ = T⁻¹τ`. -/
theorem Khat_second_residue (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : Work.Residues.jprime τ ≠ 0) :
    (Work.Residues.HasResidue (fun ζ : UpperHalfPlane => Work.Kernels.Khat ℓ d τ ζ) τ 0)
      ∧ (Work.Residues.HasResidue (fun ζ : UpperHalfPlane => Work.Kernels.Khat ℓ d τ ζ)
          ((1 : ℝ) +ᵥ τ) 0) := by
  refine ⟨?_, ?_⟩
  · exact khat_snd_residue ℓ d hd τ rfl hτ (Work.Asymptotics.KhatClear_self_zero ℓ d hd τ)
  · refine khat_snd_residue ℓ d hd τ
      (Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ) ?_ ?_
    · rw [Work.Residues.jprime_vadd_one]; exact hτ
    · exact Work.Asymptotics.KhatClear_vadd_neg_one_zero ℓ d hd τ

end Work.CKFinal.LineDecay
