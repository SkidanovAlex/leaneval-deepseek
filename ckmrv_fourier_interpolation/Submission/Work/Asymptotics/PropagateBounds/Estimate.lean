/-
# Elementary estimates for the growth propagation

Auxiliary quantitative lemmas for `Work.Asymptotics.bound_of_propagates`.
-/
import Mathlib
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Kernels.SlashDefs
import Submission.Work.Kernels.SlashBounds.jFun_bound_upper
import Submission.Work.Kernels.SlashBounds.jFun_bound_inv
import Submission.Work.Kernels.SlashBounds.nFun_bound
import Submission.Work.Asymptotics.PropagateBounds.Defs
import Submission.Work.Asymptotics.DomainD

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

variable {s : ℝ}

lemma one_add_nonneg (hs : 0 ≤ s) : 0 ≤ 1 + s := by linarith

lemma one_add_pos (hs : 0 ≤ s) : 0 < 1 + s := by linarith

/-- `(1+s)^N` is monotone in `N` for `s ≥ 0`. -/
lemma one_add_rpow_le_rpow {a b : ℝ} (h : a ≤ b) (hs : 0 ≤ s) :
    (1 + s) ^ a ≤ (1 + s) ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by linarith) h

/-- Raising a bound `X ≤ D (1+s)^E` to a power `β ≥ 0`. -/
lemma pow_le_pow_of_le {X D E β : ℝ} (hX : 0 ≤ X) (hD : 0 ≤ D) (hs : 0 ≤ s) (hβ : 0 ≤ β)
    (h : X ≤ D * (1 + s) ^ E) :
    X ^ β ≤ D ^ β * (1 + s) ^ (β * E) := by
  have hbase : (0:ℝ) ≤ 1 + s := one_add_nonneg hs
  have h2 : (D * (1 + s) ^ E) ^ β = D ^ β * (1 + s) ^ (E * β) := by
    rw [Real.mul_rpow hD (Real.rpow_nonneg hbase E), Real.rpow_mul hbase E β]
  calc X ^ β ≤ (D * (1 + s) ^ E) ^ β := Real.rpow_le_rpow hX h hβ
    _ = D ^ β * (1 + s) ^ (E * β) := h2
    _ = D ^ β * (1 + s) ^ (β * E) := by rw [mul_comm E β]

/-- **Substitution.**  If `0 ≤ K ≤ D (1+s)^E` then `(1+K)^n ≤ (1+D)^n (1+s)^(n*E)`. -/
lemma one_add_pow_le {K D E n : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D) (hs : 0 ≤ s) (hE : 0 ≤ E)
    (hn : 0 ≤ n) (h : K ≤ D * (1 + s) ^ E) :
    (1 + K) ^ n ≤ (1 + D) ^ n * (1 + s) ^ (n * E) := by
  have hbase : (1:ℝ) ≤ 1 + s := by linarith
  have h1E : (1:ℝ) ≤ (1 + s) ^ E := Real.one_le_rpow hbase hE
  have h3 : 1 + D * (1 + s) ^ E ≤ (1 + D) * (1 + s) ^ E := by nlinarith
  have hbase' : (0:ℝ) ≤ 1 + K := by linarith
  have hle1 : 1 + K ≤ 1 + D * (1 + s) ^ E := by linarith
  have h4 : (1 + K) ^ n ≤ ((1 + D) * (1 + s) ^ E) ^ n :=
    Real.rpow_le_rpow hbase' (le_trans hle1 h3) hn
  have hD1 : (0:ℝ) ≤ 1 + D := by linarith
  have hs0 : (0:ℝ) ≤ 1 + s := by linarith
  have h5 : ((1 + D) * (1 + s) ^ E) ^ n = (1 + D) ^ n * (1 + s) ^ (E * n) := by
    rw [Real.mul_rpow hD1 (Real.rpow_nonneg hs0 E), Real.rpow_mul hs0 E n]
  calc (1 + K) ^ n ≤ ((1 + D) * (1 + s) ^ E) ^ n := h4
    _ = (1 + D) ^ n * (1 + s) ^ (E * n) := h5
    _ = (1 + D) ^ n * (1 + s) ^ (n * E) := by rw [mul_comm E n]

/-- The matrix entries of `γ ∈ SL(2,ℤ)` are bounded by the Frobenius norm. -/
lemma abs_entry_le_Frob (γ : SL(2,ℤ)) (i j : Fin 2) : |(((γ i j : ℤ) : ℝ))| ≤ Frob γ := by
  have hsum : (((γ i j : ℤ) : ℝ)) ^ 2 ≤ ((γ 0 0 : ℤ) : ℝ) ^ 2 + ((γ 0 1 : ℤ) : ℝ) ^ 2
      + ((γ 1 0 : ℤ) : ℝ) ^ 2 + ((γ 1 1 : ℤ) : ℝ) ^ 2 := by
    fin_cases i <;> fin_cases j <;> simp <;>
      nlinarith [sq_nonneg (((γ 0 0 : ℤ) : ℝ)), sq_nonneg (((γ 0 1 : ℤ) : ℝ)),
        sq_nonneg (((γ 1 0 : ℤ) : ℝ)), sq_nonneg (((γ 1 1 : ℤ) : ℝ))]
  rw [Frob, ← Real.sqrt_sq (abs_nonneg (((γ i j : ℤ) : ℝ))), sq_abs]
  exact Real.sqrt_le_sqrt hsum

/-- `‖j(γ,τ)‖ ≤ 2 * Frob γ * (1 + ‖(τ:ℂ)‖)`. -/
lemma jFun_norm_le (γ : SL(2,ℤ)) (τ : ℍ) :
    ‖jFun γ (τ : ℂ)‖ ≤ 2 * Frob γ * (1 + ‖(τ : ℂ)‖) := by
  have hc : ‖(((γ 1 0 : ℤ) : ℂ))‖ ≤ Frob γ := by
    simpa [Complex.norm_intCast] using abs_entry_le_Frob γ 1 0
  have hd : ‖(((γ 1 1 : ℤ) : ℂ))‖ ≤ Frob γ := by
    simpa [Complex.norm_intCast] using abs_entry_le_Frob γ 1 1
  have hF := Frob_nonneg γ
  have hz : (0:ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have h1 : ‖(((γ 1 0 : ℤ) : ℂ)) * (τ : ℂ) + (((γ 1 1 : ℤ) : ℂ))‖
      ≤ ‖(((γ 1 0 : ℤ) : ℂ))‖ * ‖(τ : ℂ)‖ + ‖(((γ 1 1 : ℤ) : ℂ))‖ := by
    simpa [norm_mul] using norm_add_le ((((γ 1 0 : ℤ) : ℂ)) * (τ : ℂ)) (((γ 1 1 : ℤ) : ℂ))
  have h2 : ‖(((γ 1 0 : ℤ) : ℂ))‖ * ‖(τ : ℂ)‖ + ‖(((γ 1 1 : ℤ) : ℂ))‖
      ≤ 2 * Frob γ * (1 + ‖(τ : ℂ)‖) := by nlinarith
  rw [jFun_apply]
  linarith

/-- `‖n(γ,τ)‖ ≤ 2 * Frob γ * (1 + ‖(τ:ℂ)‖)`. -/
lemma nFun_norm_le (γ : SL(2,ℤ)) (τ : ℍ) :
    ‖nFun γ (τ : ℂ)‖ ≤ 2 * Frob γ * (1 + ‖(τ : ℂ)‖) := by
  have ha : ‖(((γ 0 0 : ℤ) : ℂ))‖ ≤ Frob γ := by
    simpa [Complex.norm_intCast] using abs_entry_le_Frob γ 0 0
  have hb : ‖(((γ 0 1 : ℤ) : ℂ))‖ ≤ Frob γ := by
    simpa [Complex.norm_intCast] using abs_entry_le_Frob γ 0 1
  have hF := Frob_nonneg γ
  have hz : (0:ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  have h1 : ‖(((γ 0 0 : ℤ) : ℂ)) * (τ : ℂ) + (((γ 0 1 : ℤ) : ℂ))‖
      ≤ ‖(((γ 0 0 : ℤ) : ℂ))‖ * ‖(τ : ℂ)‖ + ‖(((γ 0 1 : ℤ) : ℂ))‖ := by
    simpa [norm_mul] using norm_add_le ((((γ 0 0 : ℤ) : ℂ)) * (τ : ℂ)) (((γ 0 1 : ℤ) : ℂ))
  have h2 : ‖(((γ 0 0 : ℤ) : ℂ))‖ * ‖(τ : ℂ)‖ + ‖(((γ 0 1 : ℤ) : ℂ))‖
      ≤ 2 * Frob γ * (1 + ‖(τ : ℂ)‖) := by nlinarith
  rw [nFun_apply]
  linarith


section ContinuityAndGrowth

/-- `scale` is continuous. -/
private lemma continuous_scale : Continuous fun τ : ℍ => scale τ := by
  have h1 : Continuous fun τ : ℍ => (τ.im)⁻¹ :=
    UpperHalfPlane.continuous_im.inv₀ (fun τ => ne_of_gt τ.im_pos)
  have h2 : Continuous fun τ : ℍ => ‖(τ : ℂ)‖ :=
    continuous_norm.comp UpperHalfPlane.continuous_coe
  have h3 : Continuous fun τ : ℍ => (1:ℝ) + (τ.im)⁻¹ + ‖(τ : ℂ)‖ :=
    (continuous_const.add h1).add h2
  simpa [scale] using h3

/-- `(scale τ) ^ N` is continuous. -/
lemma continuous_scale_rpow (N : ℝ) : Continuous fun τ : ℍ => (scale τ) ^ N := by
  have h3 : Continuous fun τ : ℍ => (1:ℝ) + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
    have h1 : Continuous fun τ : ℍ => (τ.im)⁻¹ :=
      UpperHalfPlane.continuous_im.inv₀ (fun τ => ne_of_gt τ.im_pos)
    have h2 : Continuous fun τ : ℍ => ‖(τ : ℂ)‖ :=
      continuous_norm.comp UpperHalfPlane.continuous_coe
    exact (continuous_const.add h1).add h2
  have h4 : Continuous fun τ : ℍ => ((1:ℝ) + (τ.im)⁻¹ + ‖(τ : ℂ)‖) ^ N :=
    h3.rpow_const (fun τ => Or.inl (by positivity))
  simpa [scale] using h4

/-- A scale bound on the open domain `𝒟` extends to its closure for continuous functions. -/
lemma closure_bound {f : ℍ → ℂ} (hf : Continuous f) {C Nf : ℝ}
    (h : ∀ τ ∈ DomainD, ‖f τ‖ ≤ C * (scale τ) ^ Nf) :
    ∀ τ ∈ closure DomainD, ‖f τ‖ ≤ C * (scale τ) ^ Nf := by
  have hS : IsClosed {τ : ℍ | ‖f τ‖ ≤ C * (scale τ) ^ Nf} :=
    isClosed_le hf.norm (continuous_const.mul (continuous_scale_rpow Nf))
  have hsub : DomainD ⊆ {τ : ℍ | ‖f τ‖ ≤ C * (scale τ) ^ Nf} := fun τ hτ => h τ hτ
  exact closure_minimal hsub hS

end ContinuityAndGrowth

section Bounds

/-- `‖j(γ,τ)‖ ^ k` is polynomially bounded in `1 + ‖γ‖` and `1 + scale τ`, for every integer `k`. -/
lemma jFun_zpow_le (k : ℤ) : ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
    ∀ (γ : SL(2,ℤ)) (τ : ℍ), ‖jFun γ (τ : ℂ)‖ ^ k ≤ C * (1 + Frob γ) ^ N * (1 + scale τ) ^ N := by
  rcases le_total k 0 with hk | hk
  · -- k ≤ 0: the exponent of `jFun_bound_inv`
    refine ⟨1, (k.natAbs : ℝ), by norm_num, Nat.cast_nonneg _, fun γ τ => ?_⟩
    have hm : k = -((k.natAbs : ℤ)) := Int.eq_neg_natAbs_of_nonpos hk
    have hJ0 : (0:ℝ) < ‖jFun γ (τ : ℂ)‖ := norm_pos_iff.mpr (jFun_ne_zero γ τ)
    have hs : (1:ℝ) ≤ scale τ := one_le_scale τ
    have h1inv : ‖jFun γ (τ : ℂ)‖⁻¹ ≤ scale τ := by
      refine le_trans (SlashBounds.jFun_bound_inv γ τ) ?_
      rw [scale]
      linarith [norm_nonneg ((τ : ℂ))]
    have hkey : ‖jFun γ (τ : ℂ)‖ ^ k = (‖jFun γ (τ : ℂ)‖⁻¹) ^ k.natAbs := by
      conv_lhs => rw [hm]
      rw [_root_.zpow_neg, zpow_natCast, inv_pow]
    rw [hkey]
    have h2 : (‖jFun γ (τ : ℂ)‖⁻¹) ^ k.natAbs ≤ (scale τ) ^ k.natAbs :=
      pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hJ0)) h1inv k.natAbs
    have h3 : (scale τ) ^ k.natAbs
        ≤ (1 + Frob γ) ^ (k.natAbs : ℝ) * (1 + scale τ) ^ (k.natAbs : ℝ) := by
      have h4 : (scale τ) ^ k.natAbs ≤ (1 + scale τ) ^ (k.natAbs : ℝ) := by
        rw [Real.rpow_natCast]
        exact pow_le_pow_left₀ (by linarith) (by linarith) k.natAbs
      have h5 : (1:ℝ) ≤ (1 + Frob γ) ^ (k.natAbs : ℝ) :=
        Real.one_le_rpow (by linarith [Frob_nonneg γ]) (Nat.cast_nonneg _)
      have h6 : (0:ℝ) ≤ (1 + scale τ) ^ (k.natAbs : ℝ) :=
        Real.rpow_nonneg (by linarith [one_le_scale τ]) _
      nlinarith [h4, h5, h6]
    calc (‖jFun γ (τ : ℂ)‖⁻¹) ^ k.natAbs ≤ (scale τ) ^ k.natAbs := h2
      _ ≤ (1 + Frob γ) ^ (k.natAbs : ℝ) * (1 + scale τ) ^ (k.natAbs : ℝ) := h3
      _ = 1 * (1 + Frob γ) ^ (k.natAbs : ℝ) * (1 + scale τ) ^ (k.natAbs : ℝ) := by ring
  · -- k ≥ 0: the exponent of `jFun_bound_upper`
    refine ⟨(2:ℝ) ^ k.natAbs, (k.natAbs : ℝ), by positivity, Nat.cast_nonneg _, fun γ τ => ?_⟩
    have hm : k = ((k.natAbs : ℕ) : ℤ) := (Int.natAbs_of_nonneg hk).symm
    have hF := Frob_nonneg γ
    have hJle : ‖jFun γ (τ : ℂ)‖ ≤ 2 * Frob γ * (1 + scale τ) := by
      refine le_trans (jFun_norm_le γ τ) ?_
      have h2 : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
      nlinarith
    have hkey : ‖jFun γ (τ : ℂ)‖ ^ k = ‖jFun γ (τ : ℂ)‖ ^ k.natAbs := by
      conv_lhs => rw [hm]
      rw [zpow_natCast]
    rw [hkey]
    have h2 : ‖jFun γ (τ : ℂ)‖ ^ k.natAbs ≤ (2 * Frob γ * (1 + scale τ)) ^ k.natAbs :=
      pow_le_pow_left₀ (norm_nonneg _) hJle k.natAbs
    have h3 : (2 * Frob γ * (1 + scale τ)) ^ k.natAbs
        = (2:ℝ) ^ k.natAbs * (Frob γ) ^ k.natAbs * (1 + scale τ) ^ k.natAbs := by
      rw [mul_pow, mul_pow, mul_assoc]
    have h4 : (Frob γ) ^ k.natAbs ≤ (1 + Frob γ) ^ (k.natAbs : ℝ) := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ hF (by linarith) k.natAbs
    have h5 : (1 + scale τ) ^ k.natAbs = (1 + scale τ) ^ (k.natAbs : ℝ) := by
      rw [Real.rpow_natCast]
    calc ‖jFun γ (τ : ℂ)‖ ^ k.natAbs ≤ (2 * Frob γ * (1 + scale τ)) ^ k.natAbs := h2
      _ = (2:ℝ) ^ k.natAbs * (Frob γ) ^ k.natAbs * (1 + scale τ) ^ k.natAbs := h3
      _ ≤ (2:ℝ) ^ k.natAbs * (1 + Frob γ) ^ (k.natAbs : ℝ) * (1 + scale τ) ^ k.natAbs := by
          apply mul_le_mul_of_nonneg_right _
            (pow_nonneg (by linarith [one_le_scale τ] : (0:ℝ) ≤ 1 + scale τ) _)
          exact mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (2:ℝ) ^ k.natAbs * (1 + Frob γ) ^ (k.natAbs : ℝ) * (1 + scale τ) ^ (k.natAbs : ℝ) := by
          rw [h5]

end Bounds


section PowerBounds

variable {E s y N : ℝ}

/-- If `1 ≤ E`, `1 ≤ 1+s` and `y ≤ E (1+s)^E`, then `y ^ N ≤ E ^ N (1+s)^(E*N)` for `N ≥ 0`. -/
lemma rpow_le_of_le_mul {y E s N : ℝ} (hy0 : 0 ≤ y) (hE : 1 ≤ E) (hs : 0 ≤ s) (hN : 0 ≤ N)
    (h : y ≤ E * (1 + s) ^ E) : y ^ N ≤ E ^ N * (1 + s) ^ (E * N) := by
  have hbase : (0:ℝ) ≤ 1 + s := le_trans zero_le_one (by linarith)
  have h1 : y ^ N ≤ (E * (1 + s) ^ E) ^ N := Real.rpow_le_rpow hy0 h hN
  have h2 : (E * (1 + s) ^ E) ^ N = E ^ N * (1 + s) ^ (E * N) := by
    rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hbase E), Real.rpow_mul hbase E N]
  calc y ^ N ≤ (E * (1 + s) ^ E) ^ N := h1
    _ = E ^ N * (1 + s) ^ (E * N) := h2

/-- `1 ≤ x` implies `1 ≤ x ^ N` for `N ≥ 0`. -/
lemma one_le_rpow' {x N : ℝ} (hx : 1 ≤ x) (hN : 0 ≤ N) : 1 ≤ x ^ N := Real.one_le_rpow hx hN

/-- If `0 ≤ y` and `y ≤ L` then `y ^ N ≤ L ^ N` for `N ≥ 0`. -/
lemma rpow_le_rpow' {y L N : ℝ} (hy : 0 ≤ y) (h : y ≤ L) (hN : 0 ≤ N) : y ^ N ≤ L ^ N :=
  Real.rpow_le_rpow hy h hN

end PowerBounds



section Absorb

/-- Absorbing slack in a bound of the shape `X ≤ C * E^m * (1+s)^M`. -/
lemma absorb {C E s X m M m' M' : ℝ} (hE : 1 ≤ E) (hs : 1 ≤ s) (hC : 0 ≤ C)
    (hm : m ≤ m') (hM : M ≤ M') (h : X ≤ C * E ^ m * (1 + s) ^ M) :
    X ≤ C * E ^ m' * (1 + s) ^ M' := by
  have hEm : E ^ m ≤ E ^ m' := Real.rpow_le_rpow_of_exponent_le hE hm
  have hsm : (1 + s) ^ M ≤ (1 + s) ^ M' :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hM
  have h2 : (0:ℝ) ≤ (1 + s) ^ M := Real.rpow_nonneg (by linarith) M
  have h3 : (0:ℝ) ≤ C * E ^ m' := mul_nonneg hC (Real.rpow_nonneg (le_trans zero_le_one hE) m')
  calc X ≤ C * E ^ m * (1 + s) ^ M := h
    _ ≤ C * E ^ m' * (1 + s) ^ M' :=
        mul_le_mul (mul_le_mul_of_nonneg_left hEm hC) hsm h2 h3

end Absorb


end Work.Asymptotics
