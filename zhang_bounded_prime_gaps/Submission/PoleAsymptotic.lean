import Mathlib
import Submission.ZetaWN
import Submission.ZetaRatio

open scoped BigOperators Topology
open Filter

/-!
# P8 Lemma 4.1: the pole asymptotics of `ζ_WN` at the points `1 + z`

P8 (41) needs the simple-pole behaviour of the modified zeta at arguments
`1 + z` with `z = (1+iξ)/log x → 0`.  Since `ζ_q` (q = WN) has a simple pole
at `s = 1` with residue `φ(q)/q` (`zetaWN_residue_one`, `Submission.ZetaWN`),
the asymptotic is:

    z · ζ_q(1 + z)  →  φ(q)/q            (z → 0, z ≠ 0)      -- zetaWN_pole_z
    ζ_q(1+z)·z·q/φ(q) → 1                (z → 0, z ≠ 0)      -- zetaWN_pole_ratio_one

and along the sieve's points `z(x) := (1+iξ)/log x`, `x → ∞` (fixed real ξ):

    ζ_q(1 + z(x)) · z(x) · q/φ(q)  →  1                       -- zetaWN_log_asymptotic

which is P8's display `ζ_WN(1 + (1+iξ)/log x) = (1+o(1))·B·φ(N)/((1+iξ)·N)`
once `q = WN`, `(W,N) = 1` and `B := φ(W)/W·log x` are substituted (the
algebraic identification is a field/`totient_mul` step).  A fully *uniform*
version over `|ξ| ≤ √log x` additionally needs a local quantitative estimate
of `(s−1)ζ(s)` near `s = 1`; the pointwise (per fixed ξ) statements below
are the kernel that uniformity will multiply out from.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The residue at the shifted pole: `z·ζ_q(1+z) → φ(q)/q` as `z → 0`, `z ≠ 0`. -/
theorem zetaWN_pole_z (q : ℕ) (hq : q ≠ 0) :
    Tendsto (fun z : ℂ => z * zetaWN q (1 + z)) (𝓝[≠] 0)
      (𝓝 ((q.totient : ℂ) / (q : ℂ))) := by
  have h := zetaWN_residue_one q hq
  -- reparametrize s ↦ 1 + z: (𝓝[≠] 0) maps into (𝓝[≠] 1)
  have hz : Tendsto (fun z : ℂ => 1 + z) (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : Continuous (fun z : ℂ => 1 + z) := (continuous_const.add continuous_id)
    simpa using hc.tendsto 0
  have hz2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), 1 + z ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    intro h1z
    exact hz (add_left_cancel (a := (1 : ℂ)) (b := z) (c := (0 : ℂ))
      (by simpa using h1z.trans (by simp : (1 : ℂ) = 1 + 0)))
  have hcomp := h.comp (tendsto_nhdsWithin_iff.mpr ⟨hz, hz2⟩)
  convert hcomp using 1
  ext z
  simp [Function.comp_def]

/-- Multiplicative pole form: `ζ_q(1+z)·z·q/φ(q) → 1` as `z → 0`, `z ≠ 0`. -/
theorem zetaWN_pole_ratio_one (q : ℕ) (hq : q ≠ 0) :
    Tendsto (fun z : ℂ => zetaWN q (1 + z) * z * ((q : ℂ) / (q.totient : ℂ)))
      (𝓝[≠] 0) (𝓝 1) := by
  have hz := zetaWN_pole_z q hq
  have hconst : Tendsto (fun _ : ℂ => ((q : ℂ) / (q.totient : ℂ))) (𝓝[≠] 0)
      (𝓝 ((q : ℂ) / (q.totient : ℂ))) := tendsto_const_nhds
  have hprod := hz.mul hconst
  have hval : ((q.totient : ℂ) / (q : ℂ)) * ((q : ℂ) / (q.totient : ℂ)) = 1 := by
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    have hφ0 : (q.totient : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
    field_simp [hq0, hφ0]
  simpa [hval, mul_assoc, mul_comm, mul_left_comm] using hprod

/-- `(1+iξ)/log x` — the sieve's approach path to the pole (`x : ℕ` the
scale, `ξ : ℝ` the Fourier variable). -/
noncomputable def logZ (ξ : ℝ) (x : ℕ) : ℂ :=
  ((1 : ℂ) + ξ * Complex.I) / (Real.log (x : ℝ) : ℂ)

/-- Along the path `z(x) = (1+iξ)/log x`, `x → ∞` (fixed real `ξ`):
`ζ_q(1+z(x))·z(x)·q/φ(q) → 1`. -/
theorem zetaWN_log_asymptotic (q : ℕ) (hq : q ≠ 0) (ξ : ℝ) :
    Tendsto (fun x : ℕ => zetaWN q (1 + logZ ξ x) * logZ ξ x *
        ((q : ℂ) / (q.totient : ℂ))) atTop (𝓝 1) := by
  classical
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvR : Tendsto (fun x : ℕ => (Real.log (x : ℝ))⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hlog
  have hcst : Tendsto (fun x : ℕ => ((Real.log (x : ℝ))⁻¹ : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hinvR
    simpa [Function.comp_def] using h
  let c : ℂ := (1 : ℂ) + ξ * Complex.I
  have hc0 : c ≠ 0 := by
    intro h
    have hre : c.re = 0 := congrArg Complex.re h
    dsimp [c] at hre
    norm_num [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re] at hre
  have hZ0 : Tendsto (fun x : ℕ => logZ ξ x) atTop (𝓝 (0 : ℂ)) := by
    have hmain : Tendsto (fun x : ℕ => c * ((Real.log (x : ℝ))⁻¹ : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      simpa using (Tendsto.const_mul c hcst)
    -- logZ ξ x = c / ((log x) : ℂ) = c · (((log x) : ℂ)⁻¹) = c · ((log x)⁻¹ : ℂ)
    simpa [logZ, div_eq_mul_inv, Complex.ofReal_inv] using hmain
  have hZne : ∀ᶠ x in atTop, logZ ξ x ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    dsimp [logZ]
    have hlogx : (Real.log (x : ℝ) : ℂ) ≠ 0 := by
      have hpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
      exact_mod_cast (ne_of_gt hpos)
    exact div_ne_zero hc0 hlogx
  have hcomp := (zetaWN_pole_ratio_one q hq).comp (tendsto_nhdsWithin_iff.mpr ⟨hZ0, hZne⟩)
  simpa [Function.comp_def] using hcomp



/-- **P8's display of the pole asymptotic.**  For coprime `W, N ≠ 0`
(`q = W·N`), `B(x) := φ(W)/W · log x`, and fixed real `ξ`,

    ζ_{WN}(1 + (1+iξ)/log x) · (1+iξ)·N / (B(x)·φ(N))  →  1   (x → ∞)

i.e. `ζ_{WN}(1+(1+iξ)/log x) = (1+o(1))·B(x)·φ(N)/((1+iξ)·N)` (P8 (41)). -/
theorem zetaWN_log_asymptotic_p8 (W N : ℕ) (hW : W ≠ 0) (hN : N ≠ 0)
    (hcop : W.Coprime N) (ξ : ℝ) :
    Tendsto (fun x : ℕ =>
        zetaWN (W * N) (1 + logZ ξ x) * ((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
          ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ)))
      atTop (𝓝 1) := by
  classical
  have hq : W * N ≠ 0 := mul_ne_zero hW hN
  have hmain := zetaWN_log_asymptotic (W * N) hq ξ
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hlogx : (Real.log (x : ℝ) : ℂ) ≠ 0 := by
    have hpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
    exact_mod_cast (ne_of_gt hpos)
  have hWc : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hφW : (W.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hW)).ne'
  have hφN : (N.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)).ne'
  have hφmul : ((W * N).totient : ℂ) = (W.totient : ℂ) * (N.totient : ℂ) := by
    rw [Nat.totient_mul hcop, Nat.cast_mul]
    -- scalar identity (no ζ involved):  z·q/φ(q) = c·N/(B·φ(N))  (B := φ(W)/W·L)
  have hscalar :
      logZ ξ x * (((W * N : ℕ) : ℂ) / ((W * N).totient : ℂ)) =
        ((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
          ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ)) := by
    dsimp [logZ]
    rw [hφmul]
    field_simp [hlogx, hWc, hNc, hφW, hφN]
    rw [Nat.cast_mul]
    ring
  calc
    zetaWN (W * N) (1 + logZ ξ x) * logZ ξ x *
          (((W * N : ℕ) : ℂ) / ((W * N).totient : ℂ))
        = zetaWN (W * N) (1 + logZ ξ x) *
            (logZ ξ x * (((W * N : ℕ) : ℂ) / ((W * N).totient : ℂ))) := by ring
    _ = zetaWN (W * N) (1 + logZ ξ x) * (((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
          ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ))) := by
            rw [hscalar]
    _ = zetaWN (W * N) (1 + logZ ξ x) * ((1 : ℂ) + ξ * Complex.I) * (N : ℂ) /
          ((((W.totient : ℂ) / (W : ℂ)) * (Real.log (x : ℝ) : ℂ)) * (N.totient : ℂ)) := by ring


end Commons.NumberTheory.MaynardSieve
