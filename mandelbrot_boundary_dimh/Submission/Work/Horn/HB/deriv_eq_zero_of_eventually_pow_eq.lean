import Mathlib

namespace Work.Horn.HB

/-- **A critical point of `g` is forced by a non-trivial power relation.**

If `Ψ` is analytic at `a` with `Ψ a = 0`, `g a = v`, `(Ψ z)^d = φ (g z)` for `z` near `a` with
`d ≥ 2`, and `φ` has non-zero derivative at `v = g a`, then `g` is critical at `a`.

Proof.  Since `Ψ a = 0` and `Ψ` is differentiable at `a`, the map `z ↦ (Ψ z)^d` is differentiable
at `a` with derivative `d · Ψ a ^ (d-1) · deriv Ψ a = 0` (here `d - 1 ≥ 1`).  As it agrees with
`φ ∘ g` near `a`, the chain rule gives `deriv φ v * deriv g a = 0`; since `deriv φ v ≠ 0`, we get
`deriv g a = 0`. -/
theorem deriv_eq_zero_of_eventually_pow_eq {Ψ φ g : ℂ → ℂ} {a v : ℂ} {d : ℕ}
    (hΨ : AnalyticAt ℂ Ψ a) (hΨ0 : Ψ a = 0) (hga : g a = v)
    (hφ : DifferentiableAt ℂ φ v) (hg : DifferentiableAt ℂ g a)
    (hne : deriv φ v ≠ 0) (hd : 1 < d)
    (heq : Filter.Eventually (fun z => (Ψ z) ^ d = φ (g z)) (nhds a)) :
    deriv g a = 0 := by
  have hΨdiff : DifferentiableAt ℂ Ψ a := hΨ.differentiableAt
  -- the map `z ↦ Ψ z ^ d` is differentiable at `a` with derivative `0`
  have hpow : HasDerivAt (fun z => Ψ z ^ d) ((d : ℂ) * Ψ a ^ (d - 1) * deriv Ψ a) a :=
    hΨdiff.hasDerivAt.pow d
  have hzero : Ψ a ^ (d - 1) = 0 := by
    rw [hΨ0]
    exact zero_pow (by omega)
  have hderiv_pow : deriv (fun z => Ψ z ^ d) a = 0 := by
    rw [hpow.deriv, hzero]
    ring
  -- chain rule for `φ ∘ g`
  have hchain : deriv (φ ∘ g) a = deriv φ v * deriv g a := by
    have hφ' : DifferentiableAt ℂ φ (g a) := by rwa [hga]
    have h := deriv_comp a hφ' hg
    rwa [hga] at h
  -- `φ ∘ g` agrees with `z ↦ Ψ z ^ d` near `a`, so it has the same derivative there
  have heq'' : (fun z => Ψ z ^ d) =ᶠ[nhds a] (fun z => φ (g z)) := heq
  have heq' : (φ ∘ g) =ᶠ[nhds a] (fun z => Ψ z ^ d) := heq''.symm
  have hz : deriv (φ ∘ g) a = 0 := by
    rw [heq'.deriv_eq, hderiv_pow]
  have hmul : deriv φ v * deriv g a = 0 := hchain.symm.trans hz
  exact (mul_eq_zero.mp hmul).resolve_left hne

end Work.Horn.HB
