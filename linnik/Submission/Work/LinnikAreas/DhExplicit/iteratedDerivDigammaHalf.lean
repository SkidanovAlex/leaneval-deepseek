import Mathlib

/-!
# The iterated derivative of `z ↦ ψ(z/2)`

We prove the chain-rule identity for the digamma function `ψ = Complex.digamma` along the
scaling `z ↦ z / 2`:

`(d/dz)^n ψ(z/2) |_{z=s} = (1/2)^n ψ^{(n)}(s/2)`   for `Re s > 0`.

The point `s/2` lies in the open right half-plane `U = {z | 0 < Re z}`, on which `Γ` is
holomorphic and non-vanishing, so that `ψ = logDeriv Γ = Γ'/Γ` is analytic there.  The claim is
then the general within-set chain rule `iteratedDerivWithin_comp_const_smul` for the scaling
`z ↦ (1/2) * z` (which maps `U` into itself), combined with the identification of the
within-set iterated derivative with the ordinary one (both `U` and the relevant points such as
`s/2` lie in `U` where `ψ` is `C^n`).
-/

open scoped Topology

namespace Work.LinnikAreas.DhExplicit

theorem iteratedDerivDigammaHalf (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv n (fun z : ℂ => Complex.digamma (z / 2)) s
      = (1 / 2 : ℂ) ^ n * iteratedDeriv n Complex.digamma (s / 2) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hUdef
  have hUo : IsOpen U := by rw [hUdef]; exact isOpen_lt continuous_const Complex.continuous_re
  have hUud : UniqueDiffOn ℂ U := hUo.uniqueDiffOn
  have hsU : s ∈ U := by rw [hUdef]; exact hs
  -- the scaling `z ↦ z/2` maps the right half-plane into itself
  have hmaps : Set.MapsTo (fun z : ℂ => (1/2 : ℂ) * z) U U := by
    intro z hz
    have hz' : 0 < z.re := by rw [hUdef] at hz; exact hz
    show 0 < ((1/2 : ℂ) * z).re
    have hre : ((1/2 : ℂ) * z).re = (1/2) * z.re := by simp [Complex.mul_re]
    rw [hre]; linarith
  have hs2U : s / 2 ∈ U := by
    have h : (1/2 : ℂ) * s = s / 2 := by ring
    rw [← h]; exact hmaps hsU
  -- `Γ` is differentiable, hence analytic, on `U`
  have hGdiff : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    have hz' : 0 < z.re := by rw [hUdef] at hz; exact hz
    have hzm : ∀ m : ℕ, z ≠ -↑m := by
      intro m h
      have hre : z.re = -(m : ℝ) := by rw [h]; simp
      rw [hre] at hz'
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact (Complex.differentiableAt_Gamma z hzm).differentiableWithinAt
  have hGan : AnalyticOnNhd ℂ Complex.Gamma U := hGdiff.analyticOnNhd hUo
  have hGne : ∀ z ∈ U, Complex.Gamma z ≠ 0 := by
    intro z hz; rw [hUdef] at hz; exact Complex.Gamma_ne_zero_of_re_pos hz
  -- so is `ψ = logDeriv Γ = Γ'/Γ`
  have hAnal : AnalyticOnNhd ℂ Complex.digamma U := by
    have h := hGan.deriv.div hGan hGne
    rw [Complex.digamma_def]
    exact h.congr hUo (fun z _ => by rw [logDeriv_apply])
  have hcd : ContDiffOn ℂ (n : WithTop ℕ∞) Complex.digamma U :=
    hAnal.analyticOn.contDiffOn hUud
  -- the within-set chain rule for the scaling `z ↦ (1/2) * z`
  have key := iteratedDerivWithin_comp_const_smul hsU hUud hcd (1/2 : ℂ) hmaps
  have hfun : (fun x : ℂ => Complex.digamma ((1/2) * x))
      = (fun z : ℂ => Complex.digamma (z / 2)) := by
    funext z; congr 1; ring
  rw [hfun] at key
  -- identify within-set derivatives with ordinary ones
  have hsplit : ContDiffAt ℂ (n : WithTop ℕ∞) (fun z : ℂ => Complex.digamma (z / 2)) s := by
    have h1 : ContDiffAt ℂ (n : WithTop ℕ∞) Complex.digamma (s / 2) :=
      hcd.contDiffAt (hUo.mem_nhds hs2U)
    have h2 : ContDiffAt ℂ (n : WithTop ℕ∞) (fun z : ℂ => z / 2) s := by fun_prop
    exact h1.comp s h2
  rw [iteratedDerivWithin_eq_iteratedDeriv hUud hsplit hsU] at key
  have hright : iteratedDerivWithin n Complex.digamma U ((1/2) * s)
      = iteratedDeriv n Complex.digamma (s / 2) := by
    have h1 : ContDiffAt ℂ (n : WithTop ℕ∞) Complex.digamma ((1/2) * s) :=
      hcd.contDiffAt (hUo.mem_nhds (hmaps hsU))
    rw [iteratedDerivWithin_eq_iteratedDeriv hUud h1 (hmaps hsU)]
    congr 1
    ring
  rw [hright] at key
  simpa using key

end Work.LinnikAreas.DhExplicit
