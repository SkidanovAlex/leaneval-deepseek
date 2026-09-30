import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.finrank_lieSubDefs
import Submission.Work.BW.finrank_ker_mLie
import Submission.Work.BW.finrank_ker_comp_of_surjective
import Submission.Work.BW.map_lieCons_ker_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Dimension of the Lie algebra of `G' = G_a^ε × ker 𝒵`

`lieSub N ρ ε M ⊂ ℂ^{N+1} = Lie G` is the Lie algebra of the algebraic subgroup
`G' = G_a^ε × ker 𝒵 ⊂ G = G_a × G_m^N` cut out by the `ρ` characters whose exponent matrix is the
`ρ × N` integer matrix `M` (rows `ℚ`-linearly independent):

`lieSub N ρ ε M = (if ε then ⊤ else {v 0 = 0}) ⊓ ⋂ⱼ ker (∑ᵢ Mⱼᵢ vᵢ)`.

Since the character forms only involve the `G_m`-coordinates, and the rows of `M` are
independent over `ℚ` (hence over `ℂ`, by base change), they cut out a subspace of codimension `ρ`
in `ℂ^N`; the extra `G_a`-coordinate contributes `1` exactly when `ε = true`. Hence

`finrank ℂ (lieSub N ρ ε M) = N + 1 - ((if ε then 0 else 1) + ρ)`.
-/

namespace Work.BW

/-- The matrix–vector map `mLie M : ℂ^N → ℂ^ρ` is surjective when the rows of `M` are
`ℚ`-linearly independent: its kernel has dimension `N - ρ`, so its range has dimension `ρ`, which
is the whole target. -/
lemma mLie_surjective {N ρ : ℕ} (hρN : ρ ≤ N) (M : Fin ρ → Fin N → ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) :
    Function.Surjective (mLie M) := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_of_finrank_eq ?_
  have hrn := LinearMap.finrank_range_add_finrank_ker (mLie M)
  rw [finrank_ker_mLie hρN M hM] at hrn
  have hdim : Module.finrank ℂ (Fin N → ℂ) = N := by simp
  rw [hdim] at hrn
  have hdimρ : Module.finrank ℂ (Fin ρ → ℂ) = ρ := by simp
  rw [hdimρ]
  omega

theorem finrank_lieSub {N ρ : ℕ} (hρN : ρ ≤ N) (M : Fin ρ → Fin N → ℤ)
    (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ))) (ε : Bool) :
    Module.finrank ℂ (lieSub N ρ ε M) = N + 1 - ((if ε then 0 else 1) + ρ) := by
  have hker := finrank_ker_mLie hρN M hM
  have hsurj := mLie_surjective hρN M hM
  cases ε with
  | false =>
    -- `lieCons` identifies `ker (mLie M)` with `lieSub N ρ false M` inside `ℂ^{N+1}`
    have hlie : lieSub N ρ false M = (LinearMap.ker (mLie M)).map (lieCons N) := by
      rw [lieSub_eq_inf_ker_comp M false, map_lieCons_ker_eq M]
      simp
    rw [show Module.finrank ℂ (lieSub N ρ false M)
          = Module.finrank ℂ ((LinearMap.ker (mLie M)).map (lieCons N)) from
        congrArg (fun s : Submodule ℂ (Fin (N + 1) → ℂ) => Module.finrank ℂ s) hlie,
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (lieCons N)
        (lieCons_injective N) (LinearMap.ker (mLie M)))).symm, hker]
    have hif : (if (false : Bool) then (0 : ℕ) else 1) = 1 := by simp
    rw [hif]
    omega
  | true =>
    -- the `G_a`-coordinate is free, so `lieSub N ρ true M = ker (mLie M ∘ lieTail N)`
    have hlie : lieSub N ρ true M = LinearMap.ker ((mLie M).comp (lieTail N)) := by
      rw [lieSub_eq_inf_ker_comp M true]
      simp
    rw [show Module.finrank ℂ (lieSub N ρ true M)
          = Module.finrank ℂ (LinearMap.ker ((mLie M).comp (lieTail N))) from
        congrArg (fun s : Submodule ℂ (Fin (N + 1) → ℂ) => Module.finrank ℂ s) hlie,
      finrank_ker_comp_of_surjective (lieTail N) (mLie M) (lieTail_surjective N) hsurj]
    have hif : (if (true : Bool) then (0 : ℕ) else 1) = 0 := by simp
    have hfV : Module.finrank ℂ (Fin (N + 1) → ℂ) = N + 1 := by simp
    have hfρ : Module.finrank ℂ (Fin ρ → ℂ) = ρ := by simp
    rw [hfV, hfρ, hif]
    omega

end Work.BW
