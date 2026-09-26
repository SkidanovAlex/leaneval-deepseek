/-
# Quantitative cusp bounds on the funnel and on the contour

This file collects the *explicit-constant* estimates needed by the funnel tail expansion
`Work.Asymptotics.funnelKernelTail` and its four halves (`KPlus_funnel_tail_eight`, ...).

The four halves of `funnelKernelTail` (`KPlus_funnel_tail_eight`, `KPlus_funnel_tail_twentyfour`,
`KMinus_funnel_tail_eight`, `KMinus_funnel_tail_twentyfour`) are proved by expanding each of
`Work.Residues.KPlus_eight_decomposition`, `Work.Residues.KMinus8_eq`, `Work.Asymptotics.
UpsilonPlus24_eq` and `Work.Residues.KMinus24_eq` term by term on the contour `z = it`, using
`Δ(z) j(z) = E₄(z)³` and the geometric series

  `1/(Δ(z)(j τ - j z)) = -(1/E₄(z)³) · (1-ρ)⁻¹`,  `ρ = Δ(z) j τ / E₄(z)³ = j τ / j(z)`,

which converges because `‖ρ‖ ≤ 1/2` on the region.  Since `E₄`, `E₆`, `E₈`, `E₁₀`, `Δ`, `E₂ˢ`
have cusp expansions in *even* powers of `E = e^{πiz}` (`q = E²`), the expansion of `K₊` contains
only integer powers `q^k`; the model `Compact.Gplus d` is *defined* in the cancelled form (so
the `z²`-terms cancel by `ring`), and every remainder is `O(q (scale τ)^N (1+t)^M)`.  The
expansion of `K₋` also contains the *half-integer* orders `E^{-1} = e^{πt}` and `E = e^{-πt}`
(through `𝓛`, `W`, `U²-V²`); the `E^{-1}`-coefficients cancel identically (CKMRV's `𝒢_{-1,j}=0`),
while the `E`-coefficients are of size `e^{2π Im τ} e^{-πt}` and cancel against each other using
the near-identity `ψ₄(τ) = ψ₂(τ) E₆(τ)/E₄(τ) + O(q_τ (scale τ)^N)` (which is a consequence of
`ξ₄ = ξ₂ E₆/E₄ + O(q_τ)`, `(ξ₄|S) + (ξ₂|S) E₆/E₄ = O(E_τ)` and `U = V + W`).  The left-over
terms are `O(q + e^{-πt} scale^N) ⊆ O((scale τ)^N (1+t)^M e^{-π(t - Im τ)})`.

**Why explicit constants are needed.**  The funnel has `scale τ ≍ |τ|` only *polynomial*, so it
cannot absorb the exponential factor `e^{2π Im τ}` coming from `j(τ)`: that factor must cancel
against `q_z = e^{2πiz}`.  Concretely one needs the *uniform* divisor bound

  `‖Δ(it)(jτ - j(it))‖ ≥ 1/16`  for `τ ∈ 𝒟`, `2 ≤ Im τ`, `t ≥ Im τ + 1`,

with *no* `τ`-dependent threshold (the existing `growthPrefactor_lower_atTop` has such a
threshold, coming from `C e^{-2πt}‖jτ‖ ≤ 1/16`).  It is obtained from the three explicit bounds

* `‖Δ(τ)‖ ≥ (1/2) e^{-2π Im τ}` for `Im τ ≥ 2` (the *sharp* form of `DeltaFun_lower`, which
  only gives `(1/2)^24`: see `tprod_one_sub_pow_ge` above, which turns the elementary product
  estimate `∏(1-aₙ) ≥ 1 - Σaₙ` into the sharp one),
* `‖E₄(τ)‖ ≤ 3/2` and `‖E₄(w)‖ ≥ 1/2` for `Im w ≥ 3` (from the `q`-expansion of `E₄` with the
  explicit coefficient bound `240·m⁴`, following the proof of
  `Work.Residues.E4FunSecondOrder` but keeping the constant `240·Σ m⁴|q|^{m-1} ≤ 240·48`
  explicit; the lossy existential constants of `E4Fun_decay` cannot be compared with `e^{-6π}`),
* `‖Δ(it)‖ ≤ e^{-2πt}` for `t ≥ 1` (this is `Work.Asymptotics.DeltaFun_imagAxis_atTop`, whose
  constants are already explicit).

These give `‖j τ‖ ≤ 6.75 e^{2π Im τ}` (from `j = E₄³/Δ`), `‖j(it)‖ ≥ e^{2π t}/8` and hence
`‖Δ(it)jτ‖ ≤ e^{-2πt}·6.75 e^{2π Im τ} ≤ 6.75 e^{-2π} ≤ 1/16`, so that
`‖Δ(it)(jτ - j(it))‖ ≥ ‖E₄(it)³‖ - ‖Δ(it)jτ‖ ≥ 1/8 - 1/16 = 1/16` provided `E₄(it)` is close
to `1`.  The remaining building blocks are `Work.Residues.E4FunSecondOrder` (and the analogous
`E6`, `E2`, `Δ` expansions) for the `O(q)` remainders, `Work.Kernels.TildeFacts.E2S_eq` for
`E₂ˢ(z) = E₂(z) - 6i/(πz)`, and the elementary bounds `E2Fun_bound`, `E4Fun_bound`,
`E6Fun_bound` for the `τ`-atoms.

Once `‖Δ(z)(jτ-jz)‖ ≥ 1/16` is available, each half is a term-by-term estimate: writing
`T_j = (τ-atom)_j (z-atom)_j /(Δ(z)(jτ-jz))` and `mod_j` for the corresponding model term, one
has `K - model = c·Σ_j (T_j - mod_j)` with
`T₁ - mod₁ = A(τ)(φ̃₀(z) - z²) = 0`,
`‖T₃ - mod₃‖ ≤ |τE₆(τ)| z² · C q`, `‖T₄ - mod₄‖ ≤ 2|φ₀E₄(τ)| z² · C q` (using
`E₈(z)E₂ˢ(z)²/(Δ(z)J) = -E₂ˢ(z)²/(E₄(z)(1-ρ))` and the expansions of `E₂ˢ`, `E₄`, `E₆`), and
`‖T₂‖ ≤ C (scale τ)^N t² e^{-2π(t - Im τ)}`; the factor `e^{2π Im τ}` of
`(E₁₄/Δ)(τ) = j(τ)E₆(τ)/E₄(τ)` is exactly balanced by `e^{-2πt} ≤ e^{-2π(t-Im τ)}`, which is
the reason for the exponent `π` in the target's right-hand side (the *true* rate being `2π`).
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.jInvariantFun_cusp_second
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Topology

noncomputable section

/-! ## An infinite-product lower bound -/

/-- `∏' (1 - aₙ) ≥ 1 - Σ' aₙ` for `0 ≤ aₙ ≤ 1` with `Σ' aₙ < 1`. -/
lemma tprod_one_sub_ge_one_sub_tsum {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1)
    (hsum : Summable a) (hsum_le : ∑' n, a n ≤ 1) :
    1 - ∑' n, a n ≤ ∏' n, (1 - a n) := by
  have hmult : Multipliable (fun n : ℕ => 1 + (-a n)) :=
    Real.multipliable_one_add_of_summable hsum.neg
  have hlim : Filter.Tendsto (fun N : ℕ => ∏ n ∈ Finset.range N, (1 + (-a n))) Filter.atTop
      (nhds (∏' n, (1 + (-a n)))) := hmult.hasProd.tendsto_prod_nat
  have h1 : Filter.Tendsto (fun N : ℕ => (1 : ℝ) - ∑ n ∈ Finset.range N, a n) Filter.atTop
      (nhds (1 - ∑' n, a n)) := tendsto_const_nhds.sub hsum.hasSum.tendsto_sum_nat
  have hfin : ∀ N : ℕ,
      (1 : ℝ) - ∑ n ∈ Finset.range N, a n ≤ ∏ n ∈ Finset.range N, (1 + (-a n)) := by
    intro N
    have h := one_sub_sum_le_prod_one_sub (Finset.range N) a
      (fun i _ => ha0 i) (fun i _ => ha1 i)
    have heq : (∏ n ∈ Finset.range N, (1 - a n))
        = ∏ n ∈ Finset.range N, (1 + (-a n)) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rwa [heq] at h
  have h3 : 1 - ∑' n, a n ≤ ∏' n, (1 + (-a n)) :=
    le_of_tendsto_of_tendsto h1 hlim (Filter.Eventually.of_forall hfin)
  have h4 : (∏' n, (1 + (-a n))) = ∏' n, (1 - a n) := tprod_congr (fun n => by ring)
  rwa [h4] at h3

/-- `∏' (1 - r^{n+1}) ≥ 1 - 2 r` for `0 ≤ r ≤ 1/2`. -/
lemma tprod_one_sub_pow_ge {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    1 - 2 * r ≤ ∏' n : ℕ, (1 - r ^ (n + 1)) := by
  have ha0 : ∀ n : ℕ, 0 ≤ r ^ (n + 1) := fun n => pow_nonneg hr0 _
  have ha1 : ∀ n : ℕ, r ^ (n + 1) ≤ 1 := fun n => pow_le_one₀ hr0 (by linarith : r ≤ 1)
  have hsum : Summable (fun n : ℕ => r ^ (n + 1)) := by
    have h0 : Summable (fun n : ℕ => r * r ^ n) :=
      (summable_geometric_of_lt_one hr0 (by linarith : r < 1)).mul_left r
    refine h0.congr (fun n => ?_)
    rw [pow_succ]; ring
  have htsum : ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := by
    have h0 : (fun n : ℕ => r ^ (n + 1)) = fun n : ℕ => r * r ^ n := by
      funext n; rw [pow_succ]; ring
    rw [h0, tsum_mul_left, tsum_geometric_of_lt_one hr0 (by linarith : r < 1)]
    ring
  have hle : ∑' n : ℕ, r ^ (n + 1) ≤ 1 := by
    rw [htsum, div_le_one (by linarith : (0 : ℝ) < 1 - r)]
    linarith
  have h := tprod_one_sub_ge_one_sub_tsum ha0 ha1 hsum hle
  rw [htsum] at h
  have h2r : r / (1 - r) ≤ 2 * r := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - r)]
    nlinarith [hr0, hr]
  linarith

/-- `∏' (1 - q^{n+1}) ≥ 1/2` for `0 ≤ q ≤ 1/4`. -/
lemma eta_product_lower {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ ∏' n : ℕ, (1 - q ^ (n + 1)) := by
  have ha0 : ∀ n : ℕ, 0 ≤ q ^ (n + 1) := fun n => pow_nonneg hq0 _
  have ha1 : ∀ n : ℕ, q ^ (n + 1) ≤ 1 := fun n => pow_le_one₀ hq0 (by linarith : q ≤ 1)
  have hsum : Summable (fun n : ℕ => q ^ (n + 1)) := by
    have h0 : Summable (fun n : ℕ => q * q ^ n) :=
      (summable_geometric_of_lt_one hq0 (by linarith : q < 1)).mul_left q
    refine h0.congr (fun n => ?_)
    rw [pow_succ]; ring
  have htsum : ∑' n : ℕ, q ^ (n + 1) = q / (1 - q) := by
    have h0 : (fun n : ℕ => q ^ (n + 1)) = fun n : ℕ => q * q ^ n := by
      funext n; rw [pow_succ]; ring
    rw [h0, tsum_mul_left, tsum_geometric_of_lt_one hq0 (by linarith : q < 1)]
    ring
  have hle : ∑' n : ℕ, q ^ (n + 1) ≤ 1 := by
    rw [htsum, div_le_one (by linarith : (0 : ℝ) < 1 - q)]
    linarith
  have h := tprod_one_sub_ge_one_sub_tsum ha0 ha1 hsum hle
  rw [htsum] at h
  have hhalf : q / (1 - q) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - q)]
    linarith
  linarith



/-! ## Elementary facts on the contour `z = i t` -/

lemma im_of_coe_eq {z : UpperHalfPlane} {t : ℝ} (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    z.im = t := by
  have h := congrArg Complex.im hz
  simp [UpperHalfPlane.coe_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at h
  linarith [h]

lemma norm_qParamFun_of_im {z : UpperHalfPlane} {t : ℝ} (hz : z.im = t) :
    ‖Work.Kernels.qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
  rw [Work.Asymptotics.norm_qParamFun, hz]

lemma norm_Ept_of_im {z : UpperHalfPlane} {t : ℝ} (hz : z.im = t) :
    ‖Work.Residues.Ept z‖ = Real.exp (-(Real.pi * t)) := by
  rw [Work.Residues.norm_Ept, hz]

/-- `phitVec z 0 = z²`, `phitVec z 1 = z² E₂ˢ(z)`, `phitVec z 2 = z² E₂ˢ(z)²`. -/
lemma phitVec_zero (z : UpperHalfPlane) : Work.Kernels.phitVec z 0 = (z : ℂ) ^ 2 := rfl

/-! ## The model in cancelled form -/

/-- `Compact.Gplus 8` in the "cancelled" form: the `z²`-coefficient is
`E₆τ - 2φ₀E₄ + 2φ₀E₄ - E₆τ = 0`. -/
lemma Gplus8_eq (τ z : UpperHalfPlane) :
    Compact.Gplus 8 τ z
      = ((36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I)⁻¹ *
        (((τ : ℂ) * Work.Kernels.E6Fun τ - 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ)
            * (z : ℂ) ^ 2
         + 2 * Work.Kernels.phi0 τ * Work.Kernels.E4Fun τ * (z : ℂ)
            * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ))
         - (τ : ℂ) * Work.Kernels.E6Fun τ
            * ((z : ℂ) - 6 * Complex.I / (Real.pi : ℂ)) ^ 2) := by
  rw [Compact.Gplus]
  simp only [if_true]
  unfold Compact.Gplus8 Compact.phi1 Work.Kernels.phi0
  have h2 : (Real.pi : ℂ) ^ (-2 : ℤ) = ((Real.pi : ℂ) ^ 2)⁻¹ := by
    rw [show (-2 : ℤ) = -((2 : ℤ)) by norm_num, zpow_neg, zpow_ofNat]
  rw [h2]
  field_simp
  ring_nf
  have hI3 : Complex.I ^ 3 = - Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_one, Complex.I_sq]; ring
  rw [Complex.I_sq, hI3]
  ring


end

end Work.Asymptotics
