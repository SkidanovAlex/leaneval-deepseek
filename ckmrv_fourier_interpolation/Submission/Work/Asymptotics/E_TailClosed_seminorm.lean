import Mathlib
import Submission.Work.Asymptotics.E_TailClosed

noncomputable section

open Work.Kernels

namespace Work.Asymptotics

/-- Explicit, uniform-constant version of `Work.Asymptotics.E_comp_quad_bounded_ge`.

If a family of shape constants `C : ℕ → ℝ` dominates the iterated derivatives of `J` on
`[x₀, ∞)` by `C j · (1 + |x|) · e^{-x}`, and `(n, cc, m, jj)` is a chain representation of
`s ↦ J(π s²)` (as produced by `Work.Asymptotics.E_exists_chain_repr_univ`), then on the region
`π r² ≥ x₀` the `r`-seminorms of `s ↦ J(π s²)` are bounded by `Bg · Σ_i ‖cc i‖ C (jj i)`, where
`Bg` bounds the universal Gaussian factor `(1+|r|)^{k+l}(1+πr²) e^{-πr²}`.

This is `E_comp_quad_bounded_ge` with the existential constant made explicit in the shape
constants `C`, which is what the moderate-growth bookkeeping needs. -/
lemma E_comp_quad_bound_of_shape {J : ℝ → ℂ} (k l : ℕ)
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (x₀ Bg : ℝ)
    (hJ' : ∀ j x, x₀ ≤ x → ‖iteratedDeriv j J x‖ ≤ C j * (1 + |x|) * Real.exp (-x))
    {n : ℕ} (cc : Fin n → ℂ) (m jj : Fin n → ℕ)
    (hBg : ∀ x : ℝ, (1 + |x|) ^ (k + l) * (1 + Real.pi * x ^ 2)
      * Real.exp (-(Real.pi * x ^ 2)) ≤ Bg)
    (hmle : ∀ i, m i ≤ l)
    (hrepr : ∀ x : ℝ, iteratedDeriv l (fun s : ℝ => J (Real.pi * s ^ 2)) x
      = ∑ i : Fin n, cc i * (x : ℂ) ^ (m i) * iteratedDeriv (jj i) J (Real.pi * x ^ 2))
    (r : ℝ) (hr : x₀ ≤ Real.pi * r ^ 2) :
    |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => J (Real.pi * s ^ 2)) r‖
      ≤ Bg * ∑ i : Fin n, ‖cc i‖ * C (jj i) := by
  rw [hrepr r]
  have hnorm : ∀ i : Fin n, ‖cc i * (r : ℂ) ^ (m i) * iteratedDeriv (jj i) J (Real.pi * r ^ 2)‖
      = ‖cc i‖ * |r| ^ (m i) * ‖iteratedDeriv (jj i) J (Real.pi * r ^ 2)‖ := by
    intro i
    rw [norm_mul, norm_mul, Complex.norm_pow, norm_ofReal_eq_abs]
  have hrnn : (0 : ℝ) ≤ Real.pi * r ^ 2 := by positivity
  have habs : |Real.pi * r ^ 2| = Real.pi * r ^ 2 := abs_of_nonneg hrnn
  calc |r| ^ k * ‖∑ i : Fin n, cc i * (r : ℂ) ^ (m i)
          * iteratedDeriv (jj i) J (Real.pi * r ^ 2)‖
      ≤ |r| ^ k * ∑ i : Fin n, ‖cc i * (r : ℂ) ^ (m i)
          * iteratedDeriv (jj i) J (Real.pi * r ^ 2)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ i : Fin n, |r| ^ k * (‖cc i‖ * |r| ^ (m i)
          * ‖iteratedDeriv (jj i) J (Real.pi * r ^ 2)‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hnorm i]
    _ ≤ ∑ i : Fin n, ‖cc i‖ * C (jj i) * Bg := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hZi := hJ' (jj i) (Real.pi * r ^ 2) hr
        rw [habs] at hZi
        have hpow : |r| ^ (k + m i) ≤ (1 + |r|) ^ (k + l) := by
          calc |r| ^ (k + m i) ≤ (1 + |r|) ^ (k + m i) :=
                pow_le_pow_left₀ (abs_nonneg r) (by linarith [abs_nonneg r]) _
            _ ≤ (1 + |r|) ^ (k + l) :=
                pow_le_pow_right₀ (by linarith [abs_nonneg r]) (by have := hmle i; omega)
        have hCnn : (0 : ℝ) ≤ C (jj i) := hC _
        calc |r| ^ k * (‖cc i‖ * |r| ^ (m i) * ‖iteratedDeriv (jj i) J (Real.pi * r ^ 2)‖)
            = ‖cc i‖ * (|r| ^ (k + m i)
                * ‖iteratedDeriv (jj i) J (Real.pi * r ^ 2)‖) := by
              rw [pow_add]; ring
          _ ≤ ‖cc i‖ * ((1 + |r|) ^ (k + l)
                * ‖iteratedDeriv (jj i) J (Real.pi * r ^ 2)‖) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
          _ ≤ ‖cc i‖ * ((1 + |r|) ^ (k + l)
                * (C (jj i) * (1 + Real.pi * r ^ 2) * Real.exp (-(Real.pi * r ^ 2)))) := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              exact mul_le_mul_of_nonneg_left hZi (by positivity)
          _ = ‖cc i‖ * C (jj i) * ((1 + |r|) ^ (k + l) * (1 + Real.pi * r ^ 2)
                * Real.exp (-(Real.pi * r ^ 2))) := by ring
          _ ≤ ‖cc i‖ * C (jj i) * Bg :=
              mul_le_mul_of_nonneg_left (hBg r) (mul_nonneg (norm_nonneg _) hCnn)
    _ = Bg * ∑ i : Fin n, ‖cc i‖ * C (jj i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring

theorem E_TailClosed_seminorm (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.KEpsilon (G i j))
    (N₀ : ℝ) (hN₀ : 0 ≤ N₀) (k l : ℕ) :
    ∃ c N : ℝ, 0 ≤ c ∧ 0 ≤ N ∧ ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
      (2 < r ^ 2 ∨ (G 1 0 w = 0 ∧ G 1 1 w = 0)) →
      (|r| ^ k) * ‖iteratedDeriv l (Work.Asymptotics.E_TailClosed G ((Work.Kernels.scale w) ^ N₀) w) r‖
        ≤ c * (Work.Kernels.scale w) ^ N := by
  obtain ⟨n, cc, m, jj, hmle, hjle, hrepr⟩ := E_exists_chain_repr_univ l
  obtain ⟨Bg, hBgnn, hBg⟩ := E_gauss_bound (k + l) 1
  have hBg' : ∀ x : ℝ, (1 + |x|) ^ (k + l) * (1 + Real.pi * x ^ 2)
      * Real.exp (-(Real.pi * x ^ 2)) ≤ Bg := by
    intro x; simpa only [pow_one] using hBg x
  obtain ⟨α00, N00, hα00, hN00, hb00⟩ :=
    (moderateGrowthOn_iff_scale KEpsilon (G 0 0)).mp (hG 0 0)
  obtain ⟨α01, N01, hα01, hN01, hb01⟩ :=
    (moderateGrowthOn_iff_scale KEpsilon (G 0 1)).mp (hG 0 1)
  obtain ⟨α10, N10, hα10, hN10, hb10⟩ :=
    (moderateGrowthOn_iff_scale KEpsilon (G 1 0)).mp (hG 1 0)
  obtain ⟨α11, N11, hα11, hN11, hb11⟩ :=
    (moderateGrowthOn_iff_scale KEpsilon (G 1 1)).mp (hG 1 1)
  set Ct : ℝ := 8 * 3 ^ l * (1 + 2 * Real.pi) * Real.exp (2 * Real.pi) + 1 with hCt
  set Atot : ℝ := α00 + α01 + α10 + α11 with hAtot
  set Nmx : ℝ := max (max N00 N01) (max N10 N11) with hNmx
  have hCt0 : 0 ≤ Ct := by rw [hCt]; positivity
  have hAtot0 : 0 ≤ Atot := by rw [hAtot]; linarith
  have hNmx0 : 0 ≤ Nmx := by
    rw [hNmx]
    exact le_trans hN00 (le_trans (le_max_left _ _) (le_max_left _ _))
  refine ⟨Bg * (∑ i : Fin n, ‖cc i‖) * Ct * Atot, N₀ * ((l : ℝ) + 1) + Nmx, ?_, ?_, ?_⟩
  · have hs : 0 ≤ ∑ i : Fin n, ‖cc i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg hBgnn hs) hCt0) hAtot0
  · have h1 : 0 ≤ N₀ * ((l : ℝ) + 1) := mul_nonneg hN₀ (by positivity)
    linarith
  · intro w hw r hcond
    have hs1 : (1 : ℝ) ≤ scale w := one_le_scale w
    have hspos : (0 : ℝ) < scale w := scale_pos w
    set B : ℝ := (scale w) ^ N₀ with hB
    have hB0 : 0 ≤ B := by rw [hB]; exact Real.rpow_nonneg hspos.le N₀
    have hB1 : 1 ≤ B := by rw [hB]; exact Real.one_le_rpow hs1 hN₀
    set Sw : ℝ := ‖G 0 0 w‖ + ‖G 0 1 w‖ + ‖G 1 0 w‖ + ‖G 1 1 w‖ with hSw
    have hSw0 : 0 ≤ Sw := by rw [hSw]; positivity
    have hle00 : (scale w) ^ N00 ≤ (scale w) ^ Nmx :=
      Real.rpow_le_rpow_of_exponent_le hs1
        (by rw [hNmx]; exact le_trans (le_max_left _ _) (le_max_left _ _))
    have hle01 : (scale w) ^ N01 ≤ (scale w) ^ Nmx :=
      Real.rpow_le_rpow_of_exponent_le hs1
        (by rw [hNmx]; exact le_trans (le_max_right _ _) (le_max_left _ _))
    have hle10 : (scale w) ^ N10 ≤ (scale w) ^ Nmx :=
      Real.rpow_le_rpow_of_exponent_le hs1
        (by rw [hNmx]; exact le_trans (le_max_left _ _) (le_max_right _ _))
    have hle11 : (scale w) ^ N11 ≤ (scale w) ^ Nmx :=
      Real.rpow_le_rpow_of_exponent_le hs1
        (by rw [hNmx]; exact le_trans (le_max_right _ _) (le_max_right _ _))
    have hSwNmx : Sw ≤ Atot * (scale w) ^ Nmx := by
      rw [hSw, hAtot]
      have g00 := hb00 w hw
      have g01 := hb01 w hw
      have g10 := hb10 w hw
      have g11 := hb11 w hw
      have hp00 : α00 * (scale w) ^ N00 ≤ α00 * (scale w) ^ Nmx :=
        mul_le_mul_of_nonneg_left hle00 hα00
      have hp01 : α01 * (scale w) ^ N01 ≤ α01 * (scale w) ^ Nmx :=
        mul_le_mul_of_nonneg_left hle01 hα01
      have hp10 : α10 * (scale w) ^ N10 ≤ α10 * (scale w) ^ Nmx :=
        mul_le_mul_of_nonneg_left hle10 hα10
      have hp11 : α11 * (scale w) ^ N11 ≤ α11 * (scale w) ^ Nmx :=
        mul_le_mul_of_nonneg_left hle11 hα11
      calc ‖G 0 0 w‖ + ‖G 0 1 w‖ + ‖G 1 0 w‖ + ‖G 1 1 w‖
          ≤ α00 * (scale w) ^ Nmx + α01 * (scale w) ^ Nmx
            + α10 * (scale w) ^ Nmx + α11 * (scale w) ^ Nmx := by linarith
        _ = (α00 + α01 + α10 + α11) * (scale w) ^ Nmx := by ring
    set C : ℕ → ℝ := fun j => E_shC j B * Sw with hCdef
    have hC0 : ∀ j, 0 ≤ C j := fun j => by
      rw [hCdef]; exact mul_nonneg (E_shC_nonneg j B hB0) hSw0
    have hrepr' : ∀ x : ℝ, iteratedDeriv l (fun s : ℝ => tcLambda G B w (Real.pi * s ^ 2)) x
        = ∑ i : Fin n, cc i * (x : ℂ) ^ (m i)
            * iteratedDeriv (jj i) (tcLambda G B w) (Real.pi * x ^ 2) :=
      fun x => hrepr (tcLambda G B w) (contDiff_tcLambda G B w) x
    have hEC : E_TailClosed G B w = fun s : ℝ => tcLambda G B w (Real.pi * s ^ 2) := by
      funext s; simp only [E_TailClosed]
    have key : |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => tcLambda G B w (Real.pi * s ^ 2)) r‖
        ≤ Bg * ∑ i : Fin n, ‖cc i‖ * C (jj i) := by
      rcases hcond with h2 | h0
      · have hr : 2 * Real.pi ≤ Real.pi * r ^ 2 := by
          have h := mul_lt_mul_of_pos_left h2 Real.pi_pos
          nlinarith [h]
        have hJ' : ∀ j x, 2 * Real.pi ≤ x →
            ‖iteratedDeriv j (tcLambda G B w) x‖ ≤ C j * (1 + |x|) * Real.exp (-x) := by
          intro j x hx
          rw [hCdef]
          exact E_tcLambda_shape G B w hB0 hB1 j x (Or.inr hx)
        have h := E_comp_quad_bound_of_shape k l C hC0 (2 * Real.pi) Bg hJ' cc m jj hBg'
          hmle hrepr' r hr
        exact h
      · have hr : (0 : ℝ) ≤ Real.pi * r ^ 2 := by positivity
        have hJ' : ∀ j x, (0 : ℝ) ≤ x →
            ‖iteratedDeriv j (tcLambda G B w) x‖ ≤ C j * (1 + |x|) * Real.exp (-x) := by
          intro j x hx
          rw [hCdef]
          exact E_tcLambda_shape G B w hB0 hB1 j x (Or.inl ⟨h0.1, h0.2, hx⟩)
        have h := E_comp_quad_bound_of_shape k l C hC0 0 Bg hJ' cc m jj hBg'
          hmle hrepr' r hr
        exact h
    have hBrw : B ^ (l + 1) = (scale w) ^ (N₀ * ((l : ℝ) + 1)) := by
      rw [hB, (Real.rpow_natCast ((scale w) ^ N₀) (l + 1)).symm,
        (Real.rpow_mul hspos.le N₀ ((l + 1 : ℕ) : ℝ)).symm]
      congr 1
      push_cast
      ring
    have hsum : ∑ i : Fin n, ‖cc i‖ * C (jj i)
        ≤ (∑ i : Fin n, ‖cc i‖) * (Ct * B ^ (l + 1) * Sw) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i _ => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hmono := E_shC_mono B hB1 (hjle i)
      have hle : E_shC l B ≤ Ct * B ^ (l + 1) := by rw [hCt]; exact E_shC_le l B hB1
      have hstep : E_shC (jj i) B * Sw ≤ (Ct * B ^ (l + 1)) * Sw :=
        mul_le_mul_of_nonneg_right (le_trans hmono hle) hSw0
      rw [hCdef]
      calc E_shC (jj i) B * Sw ≤ (Ct * B ^ (l + 1)) * Sw := hstep
        _ = Ct * B ^ (l + 1) * Sw := by ring
    have hBSw : B ^ (l + 1) * Sw ≤ Atot * (scale w) ^ (N₀ * ((l : ℝ) + 1) + Nmx) := by
      rw [hBrw]
      calc (scale w) ^ (N₀ * ((l : ℝ) + 1)) * Sw
          ≤ (scale w) ^ (N₀ * ((l : ℝ) + 1)) * (Atot * (scale w) ^ Nmx) :=
            mul_le_mul_of_nonneg_left hSwNmx (Real.rpow_nonneg hspos.le _)
        _ = Atot * ((scale w) ^ (N₀ * ((l : ℝ) + 1)) * (scale w) ^ Nmx) := by ring
        _ = Atot * (scale w) ^ (N₀ * ((l : ℝ) + 1) + Nmx) := by
            rw [Real.rpow_add hspos]
    rw [hEC]
    refine le_trans key ?_
    have h2 : Bg * ∑ i : Fin n, ‖cc i‖ * C (jj i)
        ≤ Bg * ((∑ i : Fin n, ‖cc i‖) * (Ct * B ^ (l + 1) * Sw)) :=
      mul_le_mul_of_nonneg_left hsum hBgnn
    have h3 : Bg * ((∑ i : Fin n, ‖cc i‖) * (Ct * B ^ (l + 1) * Sw))
        ≤ (Bg * (∑ i : Fin n, ‖cc i‖) * Ct * Atot)
          * (scale w) ^ (N₀ * ((l : ℝ) + 1) + Nmx) := by
      have hs : 0 ≤ ∑ i : Fin n, ‖cc i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
      have hC3 : 0 ≤ Bg * (∑ i : Fin n, ‖cc i‖) * Ct :=
        mul_nonneg (mul_nonneg hBgnn hs) hCt0
      calc Bg * ((∑ i : Fin n, ‖cc i‖) * (Ct * B ^ (l + 1) * Sw))
          = (Bg * (∑ i : Fin n, ‖cc i‖) * Ct) * (B ^ (l + 1) * Sw) := by ring
        _ ≤ (Bg * (∑ i : Fin n, ‖cc i‖) * Ct)
              * (Atot * (scale w) ^ (N₀ * ((l : ℝ) + 1) + Nmx)) :=
            mul_le_mul_of_nonneg_left hBSw hC3
        _ = (Bg * (∑ i : Fin n, ‖cc i‖) * Ct * Atot)
              * (scale w) ^ (N₀ * ((l : ℝ) + 1) + Nmx) := by ring
    exact le_trans h2 h3

end Work.Asymptotics
