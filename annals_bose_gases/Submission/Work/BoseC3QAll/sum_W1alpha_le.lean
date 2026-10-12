import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseC3QAll.PH_subset_PHq_sub
import Submission.Work.BoseC3QAll.kernel_coef_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseC3QAll.sum_W1alpha_le`

The bound on the `P_H`-sum of the `k`-weights `Ŵ₁(k)α_k` that the `Q₃⁽²⁾`/`Q₃⁽³⁾`
constant part (and the `kA3` remainder of `Q₃⁽⁴⁾`) needs:

`Σ_{k∈P_H} |Ŵ₁(k)α_k| ≤ 2ρ_z K₀ a ℓ³`.

## The proof

`α` is derived (`Q3Env.alpha = alphaCoef 𝒜 ℬ`), so on `P_H^q`

* `‖k‖ ≥ 1/(4K_Ha) > 0`, hence `𝒜_k ≥ ‖k‖²/2 > 0` (`Q3KernelFSAll.A_ge`), and
* `|α_k| ≤ |ℬ_k|/𝒜_k = ρ_z|Ŵ₁(k)|/𝒜_k ≤ 2ρ_z|Ŵ₁(k)|/‖k‖²`
  (`abs_alphaCoef_le` and `Q3KernelFSAll.B_eq`).

Hence

`Σ_{k∈P_H} |Ŵ₁(k)α_k| ≤ 2ρ_z Σ_{k∈P_H} Ŵ₁(k)²/‖k‖² ≤ 2ρ_z Σ_{k∈P_H^q} Ŵ₁(k)²/‖k‖²`,

the last sum being larger because every summand is nonnegative and
`P_H ⊆ P_H^q` (`PH_subset_PHq`).  Multiplying the lattice bound
`Q3KernelFSAll.sum_W1sq` (`ℓ⁻³Σ_{P_H^q} Ŵ₁²/‖k‖² ≤ K₀a`) by `ℓ³ > 0` gives exactly
`2ρ_zK₀aℓ³`.

No diluteness is needed: the threshold `t₀` is a positive constant and the
hypothesis `hv.t ≤ t₀` is simply not used (the scale separation behind it is
what makes the *statements* of the other estimates meaningful, not this bound).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseC3QAll

open Work.BoseB7

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The pointwise bound behind `sum_W1alpha_le`: on `P_H ⊆ P_H^q` the squeezing
parameter is dominated by `2ρ_z|Ŵ₁(k)|/‖k‖²`. -/
lemma abs_W1_mul_alpha_le (K₀ : ℝ)
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hK : Q3KernelFSAll K₀ F T E) (hv : FSParamsView E)
    {k : Mode} (hk : k ∈ F.PHset E) :
    |E.W1 k * E.alpha k| ≤ 2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
  have hrho_nn : 0 ≤ E.rho := (rho_pos E hv).le
  have hq : F.PHq E.KH E.aScat k :=
    PH_subset_PHq F E hv k (Finset.mem_filter.mp hk).2
  have hcutpos : 0 < 1 / (4 * E.KH * E.aScat) := by
    have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one hv.one_le_KH
    have ha : 0 < E.aScat := hv.a_pos
    positivity
  have hRpos : 0 < ‖F.kmom k‖ := lt_of_lt_of_le hcutpos hq
  have hR2pos : 0 < ‖F.kmom k‖ ^ 2 / 2 := div_pos (pow_pos hRpos 2) (by norm_num)
  have hApos : 0 < E.A k := lt_of_lt_of_le hR2pos (hK.A_ge k hq)
  have hαle : |E.alpha k| ≤ |E.B k| / E.A k := by
    have := abs_alphaCoef_le (A := E.A k) (B := E.B k) hApos
    simpa only [Q3Env.alpha] using this
  have hsq : |E.W1 k| * |E.W1 k| = E.W1 k ^ 2 := by rw [← pow_two, sq_abs, pow_two]
  calc |E.W1 k * E.alpha k| = |E.W1 k| * |E.alpha k| := abs_mul _ _
    _ ≤ |E.W1 k| * (|E.B k| / E.A k) := mul_le_mul_of_nonneg_left hαle (abs_nonneg _)
    _ = E.rho * E.W1 k ^ 2 / E.A k := by
        rw [hK.B_eq k, abs_mul, abs_of_nonneg hrho_nn,
          show |E.W1 k| * (E.rho * |E.W1 k| / E.A k)
            = E.rho * (|E.W1 k| * |E.W1 k|) / E.A k by ring, hsq]
    _ ≤ E.rho * E.W1 k ^ 2 / (‖F.kmom k‖ ^ 2 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hrho_nn (sq_nonneg _)) hR2pos (hK.A_ge k hq)
    _ = 2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by ring

/-- **The `P_H`-sum of the `k`-weights `Ŵ₁(k)α_k` is at most `2ρ_zK₀aℓ³`.**

The proof is in the module docstring: the pointwise bound
`abs_W1_mul_alpha_le`, the extension of the sum from `P_H` to the larger
nonnegative region `P_H^q` (`PH_subset_PHq`), and the lattice bound
`Q3KernelFSAll.sum_W1sq` multiplied by `ℓ³`. -/
lemma sum_abs_W1_alpha_le (K₀ : ℝ)
    (F : FockData Mode) (T : TildeData F) (E : Q3Env Mode)
    (hK : Q3KernelFSAll K₀ F T E) (hv : FSParamsView E) :
    ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| ≤ 2 * E.rho * K₀ * E.aScat * E.ell ^ 3 := by
  have hell : 0 < E.ell := ell_pos E hv
  have hell3 : 0 ≤ E.ell ^ 3 := (pow_pos hell 3).le
  have hrho_nn : 0 ≤ E.rho := (rho_pos E hv).le
  have hsub : F.PHset E ⊆ (excited Mode).filter (F.PHq E.KH E.aScat) := by
    intro k hk
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hk).1, PH_subset_PHq F E hv k (Finset.mem_filter.mp hk).2⟩
  have hsumsq := hK.sum_W1sq
  have hinv : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add hell]
    norm_num
  have h4 : E.ell ^ 3 *
      (E.ell ^ (-(3 : ℝ)) * ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
        (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) ≤ E.ell ^ 3 * (K₀ * E.aScat) :=
    mul_le_mul_of_nonneg_left hsumsq hell3
  have h5 : (∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
      (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) ≤ K₀ * E.aScat * E.ell ^ 3 := by
    have h6 := h4
    rw [← mul_assoc, hinv, one_mul] at h6
    calc (∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)) ≤ E.ell ^ 3 * (K₀ * E.aScat) := h6
      _ = K₀ * E.aScat * E.ell ^ 3 := by ring
  calc ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k|
      ≤ ∑ k ∈ F.PHset E, 2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) :=
        Finset.sum_le_sum fun k hk => abs_W1_mul_alpha_le K₀ F T E hK hv hk
    _ = 2 * E.rho * ∑ k ∈ F.PHset E, (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * E.rho * ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hrho_nn)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ 2 * E.rho * (K₀ * E.aScat * E.ell ^ 3) :=
        mul_le_mul_of_nonneg_left h5 (mul_nonneg (by norm_num) hrho_nn)
    _ = 2 * E.rho * K₀ * E.aScat * E.ell ^ 3 := by ring

theorem sum_W1alpha_le (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseC3QAll.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → Work.BoseC3QAll.Q3KernelFSAll K₀ F T E →
        ∑ k ∈ F.PHset E, |E.W1 k * E.alpha k| ≤ 2 * E.rho * E.aScat * K₀ * E.ell ^ 3 := by
  refine ⟨1, one_pos, ?_⟩
  intro Mode _ _ _ F T E hv _ hK
  simpa only [mul_assoc, mul_left_comm, mul_comm] using sum_abs_W1_alpha_le K₀ F T E hK hv

end Work.BoseC3QAll
