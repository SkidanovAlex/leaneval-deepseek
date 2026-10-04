import Mathlib
import Submission.Work.Diff.EXT.JetTowerDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `IsTowerInf` is preserved by `fderivWithin`

If a function `G : ℝ × E → Z` on a set `s` is divisible on `s` by every power `z ↦ z.1 ^ N` of the
time coordinate, with a `C^∞` quotient on `s` (the notion `Work.Diff.EXT.IsTowerInf`), then the
same holds for `z ↦ fderivWithin ℝ G s z`.

The proof is a direct computation.  Fix `N` and use the hypothesis to write `G = z.1 ^ (N+1) • Ψ`
on `s` with `Ψ` smooth on `s`.  The product rule for `fderivWithin` (which needs no interiority,
only `UniqueDiffWithinAt`, and holds at *every* point of `s`) gives

`fderivWithin G s z = z.1 ^ (N+1) • fderivWithin Ψ s z + (fderivWithin (z.1 ^ (N+1)) s z).smulRight (Ψ z)`,

while `fderivWithin (z.1 ^ (N+1)) s z = ((N+1) * z.1 ^ N) • fst`.  The factor `z.1 ^ N` can then be
taken out of both summands, so that

`fderivWithin G s z = z.1 ^ N • Ψ' z`,  `Ψ' z = z.1 • fderivWithin Ψ s z + ((N+1) • fst).smulRight (Ψ z)`.

Finally `Ψ'` is `C^∞` on `s`: it is a sum of the smooth function `z ↦ fderivWithin Ψ s z`
(`ContDiffOn.fderivWithin`, `UniqueDiffOn` being the hypothesis `hs`) times `z ↦ z.1`, and of the
smooth function `z ↦ Ψ z` composed with the continuous linear map `smulRightL ((N+1) • fst)`.
-/

open scoped ContDiff

namespace Work.Diff.EXT

theorem IsTowerInf_fderivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {s : Set (ℝ × E)} (hs : UniqueDiffOn ℝ s) {G : ℝ × E → Z}
    (hG : Work.Diff.EXT.IsTowerInf s G) :
    Work.Diff.EXT.IsTowerInf s (fun z => fderivWithin ℝ G s z) := by
  intro N
  obtain ⟨Ψ, hΨ, hΨeq⟩ := hG (N + 1)
  refine ⟨fun z => z.1 • fderivWithin ℝ Ψ s z +
      (ContinuousLinearMap.smulRightL ℝ (ℝ × E) Z ((N + 1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ E))
        (Ψ z), ?_, ?_⟩
  · -- smoothness of the quotient
    have hfst : ContDiffOn ℝ (((⊤ : ℕ∞)) : ℕ∞ω) (fun z : ℝ × E => z.1) s :=
      contDiff_fst.contDiffOn
    have hd : ContDiffOn ℝ (((⊤ : ℕ∞)) : ℕ∞ω) (fun z : ℝ × E => fderivWithin ℝ Ψ s z) s :=
      hΨ.fderivWithin hs le_rfl
    exact (ContDiffOn.smul hfst hd).add
      ((ContinuousLinearMap.contDiff _).fun_comp_contDiffOn hΨ)
  · -- the pointwise factorisation
    intro z hz
    have hxs : UniqueDiffWithinAt ℝ s z := hs z hz
    have hf : DifferentiableWithinAt ℝ Ψ s z :=
      (hΨ.differentiableOn (by simp)) z hz
    have hc : DifferentiableWithinAt ℝ (fun y : ℝ × E => y.1 ^ (N + 1)) s z := by fun_prop
    have hprod : fderivWithin ℝ (fun y : ℝ × E => y.1 ^ (N + 1) • Ψ y) s z
        = z.1 ^ (N + 1) • fderivWithin ℝ Ψ s z
          + (fderivWithin ℝ (fun y : ℝ × E => y.1 ^ (N + 1)) s z).smulRight (Ψ z) :=
      fderivWithin_fun_smul hxs hc hf
    have hpow : fderivWithin ℝ (fun y : ℝ × E => y.1 ^ (N + 1)) s z
        = (((N + 1 : ℕ) : ℝ) * z.1 ^ N) • (ContinuousLinearMap.fst ℝ ℝ E) := by
      have h1 : DifferentiableWithinAt ℝ (fun y : ℝ × E => y.1) s z :=
        (hasFDerivWithinAt_fst (𝕜 := ℝ) (p := z) (s := s)).differentiableWithinAt
      rw [show (fun y : ℝ × E => y.1 ^ (N + 1)) = (fun y : ℝ × E => y.1) ^ (N + 1) from rfl]
      rw [fderivWithin_pow hxs (N + 1) h1]
      have h2 : fderivWithin ℝ (fun y : ℝ × E => y.1) s z = ContinuousLinearMap.fst ℝ ℝ E :=
        fderivWithin_fst hxs
      rw [h2, Nat.add_sub_cancel, nsmul_eq_mul]
    show fderivWithin ℝ G s z = z.1 ^ N •
      (z.1 • fderivWithin ℝ Ψ s z +
        (ContinuousLinearMap.smulRightL ℝ (ℝ × E) Z ((N + 1 : ℝ) • ContinuousLinearMap.fst ℝ ℝ E))
          (Ψ z))
    rw [fderivWithin_congr' (f₁ := G) (f := fun y : ℝ × E => y.1 ^ (N + 1) • Ψ y)
      (fun y hy => hΨeq y hy) hz, hprod, hpow]
    apply ContinuousLinearMap.ext_iff.mpr
    intro v
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_add, smul_smul,
      pow_succ, ContinuousLinearMap.smulRightL_apply_apply, smul_eq_mul]
    module

end Work.Diff.EXT
