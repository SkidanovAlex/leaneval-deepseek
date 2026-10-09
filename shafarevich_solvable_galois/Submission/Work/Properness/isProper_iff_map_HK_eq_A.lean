import Mathlib
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Properness

/-- **Properness is `ψ(H_K) = A`** (the mathematical content, stated under the strict
`autoImplicit = false` option of this project).

A lift `ψ : H →* E` (i.e. `π ∘ ψ = ρ`) is surjective if and only if it maps the kernel
`H_K = ker ρ` onto the kernel `A = ker π`.

`(⇒)` `ψ(H_K) ≤ A` always holds (`Setup.map_HK_le_A`); since `ψ` is surjective and
`H_K = ker ρ = ker (π ∘ ψ) = ψ⁻¹(A)`, surjectivity gives
`A = ψ(ψ⁻¹ A) = ψ(H_K)`.

`(⇐)` Given `e ∈ E`, choose `h₀ ∈ H` with `ρ h₀ = π e` (possible since `ρ` is onto); then
`e * (ψ h₀)⁻¹ ∈ ker π = A = ψ(H_K)`, say `e * (ψ h₀)⁻¹ = ψ k` with `k ∈ H_K`; hence
`ψ (k * h₀) = e`. -/
theorem isProper_iff_map_HK_eq_A_aux.{u, v, w} {S : Work.Properness.Setup.{u, v, w}}
    (ψ : S.Lift) : S.IsProper ψ ↔ S.HK.map ψ.1 = S.A := by
  have hpi : ∀ h : S.H, S.π (ψ.1 h) = S.ρ h := fun h => by
    have h2 : S.π.comp ψ.1 = S.ρ := ψ.2
    rw [← MonoidHom.comp_apply, h2]
  constructor
  · intro hsurj
    refine le_antisymm (S.map_HK_le_A ψ) ?_
    intro a ha
    obtain ⟨h, hh⟩ := hsurj a
    exact ⟨h, by show S.ρ h = 1; rw [← hpi h, hh]; exact ha, hh⟩
  · intro hmap e
    obtain ⟨h0, hh0⟩ := S.ρ_surj (S.π e)
    have hmem : e * (ψ.1 h0)⁻¹ ∈ S.A := by
      show S.π (e * (ψ.1 h0)⁻¹) = 1
      rw [map_mul, map_inv, hpi, hh0, mul_inv_cancel]
    obtain ⟨k, _hk, hkval⟩ := (le_of_eq hmap.symm) hmem
    refine ⟨k * h0, ?_⟩
    rw [map_mul, hkval]
    group

set_option autoImplicit true
set_option linter.unusedVariables false

/-- **Properness is `ψ(H_K) = A`**, statement exactly as requested.

Note on the universe annotations `{u v w : Universe}` (the requester's): `Universe` is not a Lean 4
identifier, so it is auto-bound, and the binders `u v w` are term variables of that auto-bound type
which do not occur in the statement (the universe levels of `Setup.{u, v, w}` are the auto-bound
*levels* of the same names).  Consequently they are not inferrable: use
`isProper_iff_map_HK_eq_A (Universe := _) (u := _) (v := _) (w := _) ψ`, or — better — the
identically stated, strictly-checked `isProper_iff_map_HK_eq_A_aux ψ` above, whose statement under
the project's `autoImplicit = false` is `Setup.{u,v,w} → S.Lift → (…)`. -/
theorem isProper_iff_map_HK_eq_A {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (ψ : S.Lift) : S.IsProper ψ ↔ S.HK.map ψ.1 = S.A :=
  isProper_iff_map_HK_eq_A_aux ψ

end Work.Properness
