import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- The coordinate bijection `ℤ × ℤ ≃ ℤ[i]`. -/
def gaussEquiv : ℤ × ℤ ≃ GaussianInt where
  toFun p := ⟨p.1, p.2⟩
  invFun z := (z.re, z.im)
  left_inv p := by ext <;> rfl
  right_inv z := by ext <;> rfl

lemma gnorm_mk_cast (a b : ℤ) :
    ((gnorm (⟨a, b⟩ : GaussianInt) : ℕ) : ℝ) = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
  have h := gnorm_cast_eq (⟨a, b⟩ : GaussianInt)
  have h2 : (((gnorm (⟨a, b⟩ : GaussianInt) : ℕ) : ℤ) : ℝ) = ((a ^ 2 + b ^ 2 : ℤ) : ℝ) := by
    rw [h]
  push_cast at h2
  exact h2

lemma summable_gaussian_iff (E : GaussianInt → ℝ) :
    Summable E ↔ Summable (fun p : ℤ × ℤ => E ⟨p.1, p.2⟩) := by
  constructor
  · intro h
    exact h.comp_injective gaussEquiv.injective
  · intro h
    exact (Equiv.summable_iff gaussEquiv (f := E)).mp h

lemma summable_gnorm_exp (u : ℝ) (hu : 0 < u) :
    Summable (fun z : GaussianInt => Real.exp (-(Real.pi * u * (gnorm z : ℝ)))) := by
  rw [summable_gaussian_iff]
  have hc : 0 < Real.pi * u := by positivity
  have hbase := Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add (c := Real.pi * u) hc 0 0
  refine hbase.congr (fun p => ?_)
  rw [pow_zero, mul_one, zero_mul, add_zero, neg_mul]
  congr 1
  rw [gnorm_mk_cast]

lemma exp_theta_eq (u : ℝ) (n : ℕ) :
    Complex.exp (-Real.pi * u * (n : ℝ)) = Complex.exp (-(Real.pi * u * n)) := by
  congr 1
  push_cast
  ring

lemma norm_exp_theta (u : ℝ) (z : GaussianInt) :
    ‖Complex.exp (-Real.pi * u * (gnorm z : ℝ))‖ = Real.exp (-(Real.pi * u * ↑(gnorm z))) := by
  rw [Complex.norm_exp]; simp

/-- **The spherical theta series is the generating function of the Hecke eigenvalues**:
`Θ(u) = Σ_{z primary} ψ(z)e^{-πu|z|²} = Σ_n λ(n)e^{-πun}`.  Grouping the (absolutely convergent,
thanks to `‖χ‖ ≤ 1`) sum over the primary `z` by their norm `n = |z|²` produces exactly the Hecke
eigenvalue `λ(n) = Σ_{|z|²=n, primary} ψ(z)` of (16.30); this is the identity through which the
Mellin transform of the theta series becomes the Hecke `L`-function,
`∫_0^∞Θ(u)u^{s-1}du = Γ(s)π^{-s}L(s,ψ)`.

The bound `hchi : ∀ z, ‖chi z‖ ≤ 1` is essential: without it the `z`-sum need not be summable
(and `tsum` would return `0`), while the right-hand side can still converge to a nonzero value. -/
theorem thetaSph_eq_tsum_heckeLam (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (u : ℝ) (hu : 0 < u) :
    thetaSph chi k u = ∑' n : ℕ, heckeLam chi k n * Complex.exp (-(Real.pi * u * n)) := by
  classical
  have hE := summable_gnorm_exp u hu
  set f : GaussianInt → ℂ := fun z =>
    if IsPrimary z then psi chi k z * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0 with hf
  have hfsum : Summable f := by
    refine Summable.of_norm_bounded hE (fun z => ?_)
    change ‖(if IsPrimary z then psi chi k z * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0)‖ ≤
      Real.exp (-(Real.pi * u * ↑(gnorm z)))
    by_cases hz : IsPrimary z
    · rw [if_pos hz, norm_mul, norm_exp_theta]
      exact mul_le_of_le_one_left (Real.exp_nonneg _) (norm_psi_le_one chi k hchi z)
    · rw [if_neg hz, norm_zero]
      exact Real.exp_nonneg _
  have htheta : thetaSph chi k u = ∑' z : GaussianInt, f z := rfl
  rw [htheta, ← (hfsum.hasSum.tsum_fiberwise (gnorm : GaussianInt → ℕ)).tsum_eq]
  refine tsum_congr (fun n => ?_)
  rw [_root_.tsum_subtype (gnorm ⁻¹' {n}) f]
  have hstep1 : (∑' z : GaussianInt, (gnorm ⁻¹' {n}).indicator f z)
      = ∑' z : GaussianInt,
          (if IsPrimary z ∧ gnorm z = n then
            psi chi k z * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0) := by
    refine tsum_congr (fun z => ?_)
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hf]
    by_cases hp : IsPrimary z <;> by_cases hg : gnorm z = n <;> simp [hp, hg]
  rw [hstep1]
  set S : Finset GaussianInt := (gBox (n : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = n) with hS
  have hbound0 : ∀ z ∉ S,
      (if IsPrimary z ∧ gnorm z = n then
        psi chi k z * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0) = 0 := by
    intro z hz
    rw [if_neg]
    intro h
    apply hz
    rw [hS, Finset.mem_filter]
    refine ⟨?_, h⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hz0 : z = 0 := by
        have h1 : z.re ^ 2 + z.im ^ 2 = 0 := by
          have h2' := gnorm_cast_eq z
          rw [h.2] at h2'
          simpa using h2'.symm
        have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
        have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
        exact Zsqrtd.ext hre him
      rw [hz0]
      rw [mem_gBox_iff]
      simp
    · exact mem_gBox_of_gnorm_le (by exact_mod_cast hn) (by rw [h.2])
  rw [tsum_eq_sum (s := S) hbound0]
  have hSval : ∀ z ∈ S, IsPrimary z ∧ gnorm z = n := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    exact hz.2
  have h2 : ∀ z ∈ S, psi chi k z * Complex.exp (-Real.pi * u * (gnorm z : ℝ))
      = psi chi k z * Complex.exp (-(Real.pi * u * n)) := by
    intro z hz
    rw [(hSval z hz).2, exp_theta_eq]
  trans ∑ z ∈ S, psi chi k z * Complex.exp (-(Real.pi * u * n))
  · refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [if_pos (hSval z hz), h2 z hz]
  rw [← Finset.sum_mul]
  rw [show (∑ z ∈ S, psi chi k z) = heckeLam chi k n from by rw [hS]; rfl]

end
end Work.FIArea5.S16Hecke
