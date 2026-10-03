import Mathlib
import Submission.Work.Peluse.PET.sum_symIcc_shift_le
import Submission.Work.Peluse.PET.prod_norm_le_last

/-!
# Window control: from the size of the linear average to the window sum of the last function

The linear multilinear average of Peluse's §3,

`Λ = (N M)⁻¹ ∑_x F₀(x) ∑_{y ∈ [M]} ∏_{i = 1}^{m} F_i (x + c_i y)`,

being `≥ √γ` forces the *window sum* of the last function,

`∑_{x ∈ [-N,N]} ∑_{a ∈ c_m[M]} ‖F_m (x + a)‖`,

to be large: `√γ · N · |c_m[M]| ≤ ∑_{x ∈ [-N,N]} ∑_{a ∈ c_m[M]} ‖F_m (x + a)‖`.

The point is that the `y`-sum is exactly the `c_m[M]`-sum counted with multiplicity:
`y` alone is *not* injective into `c_m[M]` when `c_m = 0` (it is the constant map on `[M]`),
and this is precisely compensated by the cardinality `|c_m[M]| = 1` in that case.
-/

set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Peluse.WindowControl

/-- **Counting the `y`-sum against the arithmetic progression.**

For any `c : ℤ`, `M ≥ 1` and `φ : ℤ → ℝ`,
`|c[M]| · ∑_{y ∈ [M]} φ (c y) = M · ∑_{a ∈ c[M]} φ a`.

Indeed, if `c ≠ 0` the map `y ↦ c y` is injective and `|c[M]| = M`, so both sides are
`M · ∑_{a ∈ c[M]} φ a`; if `c = 0` then `c[M] = {0}`, `|c[M]| = 1`, and both sides are `M · φ 0`. -/
lemma card_arithIcc_mul_sum {M : ℕ} (hM : 0 < M) (c : ℤ) (φ : ℤ → ℝ) :
    ((Work.Peluse.arithIcc c M).card : ℝ) * ∑ y ∈ Finset.Icc 1 M, φ (c * (y : ℤ))
      = (M : ℝ) * ∑ a ∈ Work.Peluse.arithIcc c M, φ a := by
  have hcard : (Finset.Icc 1 M).card = M := by rw [Nat.card_Icc]; omega
  by_cases hc : c = 0
  · subst hc
    have hQ : Work.Peluse.arithIcc 0 M = ({0} : Finset ℤ) := by
      rw [Work.Peluse.arithIcc]
      ext a
      simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨n, _, rfl⟩; ring
      · intro ha
        refine ⟨1, by omega, ?_⟩
        rw [ha]; ring
    rw [hQ]
    simp only [Finset.card_singleton, Finset.sum_singleton, Nat.cast_one, one_mul]
    rw [show ∑ y ∈ Finset.Icc 1 M, φ (0 * (y : ℤ)) = ∑ _y ∈ Finset.Icc 1 M, φ 0 from
      Finset.sum_congr rfl (fun y _ => by rw [zero_mul])]
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  · have hinj : Set.InjOn (fun y : ℕ => c * (y : ℤ)) (↑(Finset.Icc 1 M) : Set ℕ) := by
      intro y1 _ y2 _ h
      exact_mod_cast mul_left_cancel₀ hc h
    have hQcard : (Work.Peluse.arithIcc c M).card = M := by
      rw [Work.Peluse.arithIcc, Finset.card_image_of_injOn hinj, hcard]
    rw [hQcard, Work.Peluse.arithIcc, Finset.sum_image (f := φ) hinj]

/-- **The linear average is bounded by the mean of the last function along its own shifts.**

`‖(N M)⁻¹ ∑_x F₀(x) ∑_{y ∈ [M]} ∏_{i=1}^m F_i (x + c_i y)‖
   ≤ (N M)⁻¹ ∑_{x ∈ [-N,N]} ∑_{y ∈ [M]} ‖F_m (x + c_m y)‖`

whenever all the `F_i` are `1`-bounded and supported in `[-N,N]`: the outer `tsum` is the finite sum
over the support of `F₀`, the product is dominated by its last factor (`prod_norm_le_last`), and the
factor `F₀` together with the normalisation `N⁻¹` is absorbed by the `1`-bound. -/
lemma norm_lambda_le_sum_shift {m : ℕ} (hm : 0 < m) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (c : Fin (m + 1) → ℤ) (F : Fin (m + 1) → ℤ → ℂ)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N) :
    ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖
      ≤ ((N : ℝ) * (M : ℝ))⁻¹ * ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
          ‖F ⟨m, Nat.lt_succ_self m⟩ (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ := by
  classical
  have htsum : (∑' x : ℤ, F 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ)))
      = ∑ x ∈ Work.Peluse.symIcc N, F 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ)) := by
    rw [tsum_eq_sum (s := Work.Peluse.symIcc N)]
    intro x hx
    have hxN : N < x.natAbs := lt_of_not_ge fun hle =>
      hx (Work.Peluse.PET.natAbs_le_iff_mem_symIcc.mpr hle)
    rw [hFs 0 x hxN, zero_mul]
  rw [htsum, norm_mul]
  have hnorm : ‖((N : ℂ) * (M : ℂ))⁻¹‖ = ((N : ℝ) * (M : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [hnorm]
  have hZ : ‖∑ x ∈ Work.Peluse.symIcc N, F 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖
      ≤ ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
          ‖F ⟨m, Nat.lt_succ_self m⟩ (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ := by
    calc ‖∑ x ∈ Work.Peluse.symIcc N, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖
        ≤ ∑ x ∈ Work.Peluse.symIcc N, ‖F 0 x *
            ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
            ‖F 0 x‖ * ‖∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ := by
          apply Finset.sum_le_sum
          intro x _
          calc ‖F 0 x * ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖
              = ‖F 0 x‖ * ‖∑ y ∈ Finset.Icc 1 M,
                  ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ := norm_mul _ _
            _ ≤ ‖F 0 x‖ * ∑ y ∈ Finset.Icc 1 M,
                  ‖∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ :=
                mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
            _ = ∑ y ∈ Finset.Icc 1 M,
                  ‖F 0 x‖ * ‖∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ := by
                rw [Finset.mul_sum]
      _ ≤ ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
            ‖F ⟨m, Nat.lt_succ_self m⟩ (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ := by
          apply Finset.sum_le_sum
          intro x _
          apply Finset.sum_le_sum
          intro y _
          calc ‖F 0 x‖ * ‖∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖
              = ‖F 0 x‖ * ∏ i : Fin m, ‖F i.succ (x + c i.succ * (y : ℤ))‖ := by
                rw [norm_prod Finset.univ]
            _ ≤ ‖F 0 x‖ * ‖F ⟨m, Nat.lt_succ_self m⟩
                  (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ :=
                mul_le_mul_of_nonneg_left
                  (Work.Peluse.PET.prod_norm_le_last hm c F hF x y) (norm_nonneg _)
            _ ≤ 1 * ‖F ⟨m, Nat.lt_succ_self m⟩
                  (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ :=
                mul_le_mul_of_nonneg_right (hF 0 x) (norm_nonneg _)
            _ = ‖F ⟨m, Nat.lt_succ_self m⟩
                  (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ := one_mul _
  exact mul_le_mul_of_nonneg_left hZ (by positivity)

theorem sqrtGamma_le_windowSum {m : ℕ} (hm : 0 < m) {c : Fin (m + 1) → ℤ} (hc0 : c 0 = 0)
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (F : Fin (m + 1) → ℤ → ℂ) {γ : ℝ} (hγ : 0 < γ)
    (hFbdd : ∀ i x, ‖F i x‖ ≤ 1) (hFsupp : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hcy : ∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ))
    (havg : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2) :
    Real.sqrt γ * (N : ℝ) * ((Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) M).card : ℝ)
      ≤ ∑ x ∈ Work.Peluse.symIcc N,
          ∑ a ∈ Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩) M,
            ‖F ⟨m, Nat.lt_succ_self m⟩ (x + a)‖ := by
  classical
  set cl : ℤ := c ⟨m, Nat.lt_succ_self m⟩ with hcl
  set Y : ℝ := ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
      ‖F ⟨m, Nat.lt_succ_self m⟩ (x + cl * (y : ℤ))‖ with hY
  set W : ℝ := ∑ x ∈ Work.Peluse.symIcc N, ∑ a ∈ Work.Peluse.arithIcc cl M,
      ‖F ⟨m, Nat.lt_succ_self m⟩ (x + a)‖ with hW
  have hsqrt : Real.sqrt γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
      ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ := by
    rw [Real.sqrt_le_left (norm_nonneg _)]
    exact havg
  have hnorm : ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
      ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖
        ≤ ((N : ℝ) * (M : ℝ))⁻¹ * Y := by
    rw [hY, hcl]
    exact norm_lambda_le_sum_shift hm hN hM c F hFbdd hFsupp
  have hWY : ((Work.Peluse.arithIcc cl M).card : ℝ) * Y = (M : ℝ) * W := by
    rw [hY, hW]
    rw [Finset.mul_sum]
    rw [show ∑ x ∈ Work.Peluse.symIcc N, ((Work.Peluse.arithIcc cl M).card : ℝ) *
          (∑ y ∈ Finset.Icc 1 M, ‖F ⟨m, Nat.lt_succ_self m⟩ (x + cl * (y : ℤ))‖)
        = ∑ x ∈ Work.Peluse.symIcc N, (M : ℝ) *
          (∑ a ∈ Work.Peluse.arithIcc cl M, ‖F ⟨m, Nat.lt_succ_self m⟩ (x + a)‖) from
        Finset.sum_congr rfl fun x _ => card_arithIcc_mul_sum hM cl
          (fun a => ‖F ⟨m, Nat.lt_succ_self m⟩ (x + a)‖)]
    rw [Finset.mul_sum]
  have hA_le : ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
      ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ * (N : ℝ)
        * ((Work.Peluse.arithIcc cl M).card : ℝ) ≤ W := by
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hQnn : (0 : ℝ) ≤ ((Work.Peluse.arithIcc cl M).card : ℝ) := by positivity
    have h1 : ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ * (N : ℝ)
            * ((Work.Peluse.arithIcc cl M).card : ℝ)
        ≤ (((N : ℝ) * (M : ℝ))⁻¹ * Y) * (N : ℝ)
            * ((Work.Peluse.arithIcc cl M).card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hNnn) hQnn
    have h2 : (((N : ℝ) * (M : ℝ))⁻¹ * Y) * (N : ℝ)
          * ((Work.Peluse.arithIcc cl M).card : ℝ) = W := by
      have hNne : (N : ℝ) ≠ 0 := by positivity
      have hMne : (M : ℝ) ≠ 0 := by positivity
      have hkey : Y * ((Work.Peluse.arithIcc cl M).card : ℝ) = (M : ℝ) * W := by
        rw [mul_comm]; exact hWY
      calc (((N : ℝ) * (M : ℝ))⁻¹ * Y) * (N : ℝ) * ((Work.Peluse.arithIcc cl M).card : ℝ)
          = (Y * ((Work.Peluse.arithIcc cl M).card : ℝ)) / (M : ℝ) := by
            rw [eq_div_iff hMne]
            field_simp
        _ = ((M : ℝ) * W) / (M : ℝ) := by rw [hkey]
        _ = W := by field_simp
    linarith [h1, h2]
  calc Real.sqrt γ * (N : ℝ) * ((Work.Peluse.arithIcc cl M).card : ℝ)
      ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ * (N : ℝ)
            * ((Work.Peluse.arithIcc cl M).card : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsqrt (by positivity))
          (by positivity)
    _ ≤ W := hA_le

end Work.Peluse.WindowControl
