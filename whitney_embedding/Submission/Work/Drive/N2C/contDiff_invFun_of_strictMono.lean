import Mathlib

/-!
# Smoothness of the inverse of a strictly monotone `C^∞` real function

If `θ : ℝ → ℝ` is strictly monotone, surjective, `C^∞` and has nowhere vanishing derivative,
then `θ` is a bijection, its inverse `Function.invFun θ` is continuous, and the inverse function
theorem shows that it is `C^∞` as well: at each point `y = θ a` the local inverse produced by
`ContDiffAt.to_localInverse` (an `OpenPartialHomeomorph` inverse) agrees on a neighbourhood of `y`
with `Function.invFun θ`, because both are left inverses of the injective map `θ`.
-/

namespace Work.Drive.N2C

open Set Filter
open scoped Topology

theorem contDiff_invFun_of_strictMono {θ : ℝ → ℝ} (hm : StrictMono θ) (hsurj : Function.Surjective θ)
    (hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ) (h0 : ∀ x, deriv θ x ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.invFun θ) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨a, ha⟩ := hsurj y
  rw [← ha]
  -- `θ` has invertible strict derivative at `a`, since `deriv θ a ≠ 0`.
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv θ a) (h0 a))
  have hsta : HasStrictFDerivAt θ (e : ℝ →L[ℝ] ℝ) a :=
    (hcd.hasStrictDerivAt hn).hasStrictFDerivAt_equiv (h0 a)
  have hfa : HasFDerivAt θ (e : ℝ →L[ℝ] ℝ) a := hsta.hasFDerivAt
  -- the inverse function theorem: the local inverse of `θ` is `C^∞` at `θ a`
  have hloc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (hcd.contDiffAt.localInverse hfa hn) (θ a) :=
    hcd.contDiffAt.to_localInverse hfa hn
  -- `Function.invFun θ` is a left inverse of the injective map `θ`
  have hg : ∀ᶠ x in 𝓝 a, Function.invFun θ (θ x) = x :=
    Filter.Eventually.of_forall fun x => Function.leftInverse_invFun hm.injective x
  -- hence it agrees with the local inverse near `θ a`
  have heq : ∀ᶠ z in 𝓝 (θ a), Function.invFun θ z = (hcd.contDiffAt.localInverse hfa hn) z :=
    hsta.localInverse_unique hg
  exact hloc.congr_of_eventuallyEq heq

end Work.Drive.N2C
