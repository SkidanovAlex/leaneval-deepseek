import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.Kser_gp_bounds
import Submission.Work.BMF.Kser_eq_LSeries_logMul
import Submission.Work.BMF.mrlas.differentiableOn_gp
import Submission.Work.BMF.mrlas.tendsto_sum_deriv_gp_div_gp
import Submission.Work.BMF.mrlas.tendstoLocallyUniformlyOn_eulerProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Kser f = -LSeries f * Psi f` on `Re s > 1`

For a multiplicative `f : ℕ → ℂ` with `f 1 = 1` and `‖f n‖ ≤ 1`, and `s` with `Re s > 1`,

`Σ_n f n log n n^{-s} = Kser f s = -(LSeries f s) * Psi f s`,

i.e. the logarithmic derivative `-G'/G` of the Dirichlet series `G = LSeries f` is the
log-derivative `Psi f = Σ_p g_p'/g_p` of its Euler product `G = ∏_p g_p`.

The proof compares the derivatives of the finite Euler products `P_N(z) = ∏_{p < N} g_p(z)`
in two ways.  On the one hand `P_N` is a finite product of the holomorphic local factors, so by
`deriv (LSeries f) s = -Kser f s` (Mathlib's `LSeries_deriv`) and the locally uniform Euler
product `P_N → LSeries f` (`tendstoLocallyUniformlyOn_eulerProduct`) together with Weierstrass'
theorem for locally uniformly convergent holomorphic functions, `P_N'(s) → deriv (LSeries f) s`.
On the other hand the logarithmic-derivative product rule gives
`P_N'(s) = P_N(s) · Σ_{p<N} g_p'(s)/g_p(s)`, where `P_N(s) → LSeries f s`
(`TendstoLocallyUniformlyOn.tendsto_at`) and `Σ_{p<N} g_p'/g_p → Psi f s`
(`tendsto_sum_deriv_gp_div_gp`).  Uniqueness of the limit in `ℂ` yields
`deriv (LSeries f) s = LSeries f s * Psi f s`, and the claim follows by rewriting
`deriv (LSeries f) s = -Kser f s`.
-/

namespace Work.BMF.mrlas

open Filter

/-- Logarithmic derivative of a finite product of complex functions: if every factor is
differentiable at `s` and non-zero there, then
`(∏_{p ∈ S} u p)'(s) = (∏_{p ∈ S} u p s) · Σ_{p ∈ S} u p'(s)/u p s`. -/
lemma deriv_finset_prod_logDeriv (S : Finset ℕ) (u : ℕ → ℂ → ℂ) (s : ℂ)
    (hd : ∀ p ∈ S, DifferentiableAt ℂ (u p) s) (hne : ∀ p ∈ S, u p s ≠ 0) :
    deriv (fun z : ℂ => ∏ p ∈ S, u p z) s =
      (∏ p ∈ S, u p s) * ∑ p ∈ S, deriv (u p) s / u p s := by
  have hprod_ne : (∏ p ∈ S, u p s) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  have h := logDeriv_prod (s := S) (f := u) (x := s) hne hd
  rw [logDeriv_apply] at h
  have h2 : (∑ p ∈ S, logDeriv (u p) s) = ∑ p ∈ S, deriv (u p) s / u p s :=
    Finset.sum_congr rfl (fun p _ => logDeriv_apply (u p) s)
  rw [h2] at h
  have hfun : (∏ p ∈ S, u p) = fun z : ℂ => ∏ p ∈ S, u p z := by
    funext z
    exact Finset.prod_apply z S (fun p => u p)
  rw [hfun] at h
  exact ((div_eq_iff hprod_ne).mp h).trans (mul_comm _ _)

/-- On `Re s > 1`, the logarithmic derivative of the Dirichlet series `LSeries f` equals
`LSeries f s * Psi f s`: `Psi f` is the logarithmic derivative of the Euler product of `f`. -/
theorem deriv_LSeries_eq_mul_Psi (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hb : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    deriv (LSeries f) s = LSeries f s * Work.BMF.Psi f s := by
  have hUopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ {z : ℂ | 1 < z.re} := hs
  -- the finite Euler products converge locally uniformly to `LSeries f`
  have hLU : TendstoLocallyUniformlyOn
      (fun N : ℕ => fun z : ℂ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p z)
      (LSeries f) atTop {z : ℂ | 1 < z.re} :=
    tendstoLocallyUniformlyOn_eulerProduct f hf1 hmul hb
  -- each finite Euler product is holomorphic on the half-plane
  have hdiff : ∀ᶠ N : ℕ in atTop, DifferentiableOn ℂ
      (fun z : ℂ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p z) {z : ℂ | 1 < z.re} := by
    filter_upwards with N
    refine (DifferentiableOn.finsetProd (u := N.primesBelow)
      (f := fun p (z : ℂ) => Work.BMF.gp f p z) (fun p hp => ?_)).congr (fun z _ => ?_)
    · exact differentiableOn_gp f hb (Nat.mem_primesBelow.mp hp).2
    · simp only [Finset.prod_apply]
  -- Weierstrass: the derivatives converge to the derivative of the limit at `s`
  have hderiv : Tendsto
      (fun N : ℕ => deriv (fun z : ℂ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p z) s)
      atTop (nhds (deriv (LSeries f) s)) :=
    (hLU.deriv hdiff hUopen).tendsto_at hsU
  -- logarithmic-derivative product rule for the finite Euler products
  have hrule : ∀ N : ℕ,
      deriv (fun z : ℂ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p z) s =
        (∏ p ∈ N.primesBelow, Work.BMF.gp f p s) *
          ∑ p ∈ N.primesBelow, deriv (Work.BMF.gp f p) s / Work.BMF.gp f p s := by
    intro N
    refine deriv_finset_prod_logDeriv _ _ _ (fun p hp => ?_) (fun p hp => ?_)
    · exact (differentiableOn_gp f hb (Nat.mem_primesBelow.mp hp).2).differentiableAt
        (hUopen.mem_nhds hsU)
    · exact Work.BMF.gp_ne_zero f hf1 hb (σ := (1 + s.re) / 2) (by linarith) p
        (Nat.mem_primesBelow.mp hp).2 (by linarith)
  -- the summed logarithmic derivatives converge to `Psi f s`
  have hA : Tendsto
      (fun N : ℕ => ∑ p ∈ N.primesBelow, deriv (Work.BMF.gp f p) s / Work.BMF.gp f p s)
      atTop (nhds (Work.BMF.Psi f s)) := tendsto_sum_deriv_gp_div_gp f hf1 hb hs
  -- the finite Euler products converge at `s`
  have hP : Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, Work.BMF.gp f p s)
      atTop (nhds (LSeries f s)) := hLU.tendsto_at hsU
  -- compare the two limits of the sequence of derivatives
  have hprod : Tendsto (fun N : ℕ =>
        (∏ p ∈ N.primesBelow, Work.BMF.gp f p s) *
          ∑ p ∈ N.primesBelow, deriv (Work.BMF.gp f p) s / Work.BMF.gp f p s)
      atTop (nhds (LSeries f s * Work.BMF.Psi f s)) := hP.mul hA
  exact tendsto_nhds_unique hderiv
    (hprod.congr' (Eventually.of_forall (fun N => (hrule N).symm)))

/-- `Kser f s = -LSeries f s * Psi f s` for multiplicative `1`-bounded `f : ℕ → ℂ` with
`f 1 = 1` and `Re s > 1`. -/
theorem Kser_eq_neg_LSeries_mul_Psi (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) (hb : ∀ n, ‖f n‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Work.BMF.Kser f s = -(LSeries f s) * Work.BMF.Psi f s := by
  have habsc : LSeries.abscissaOfAbsConv f < (s.re : EReal) :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => hb n⟩)
      (EReal.coe_lt_coe_iff.mpr hs)
  have hder : deriv (LSeries f) s = -Work.BMF.Kser f s := by
    rw [LSeries_deriv habsc, Work.BMF.Kser_eq_LSeries_logMul]
  have hmain := deriv_LSeries_eq_mul_Psi f hf1 hmul hb hs
  have h1 : -Work.BMF.Kser f s = LSeries f s * Work.BMF.Psi f s := hder.symm.trans hmain
  have h2 : Work.BMF.Kser f s = -(LSeries f s * Work.BMF.Psi f s) := by
    rw [← h1, neg_neg]
  rw [neg_mul, h2]

end Work.BMF.mrlas
