import Mathlib.Tactic.NormNum.NatFactorial
import Submission.Commons.Analysis.MomentCurve.transversality_det

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.MomentCurve

open scoped BigOperators

/-- Exponent bookkeeping: `d^{i+1} · (d^e · c) = d^{i+1+e} · c`. -/
lemma pow_mul_pow_mul (d c : ℝ) (i e : ℕ) :
    d ^ (i + 1) * (d ^ e * c) = d ^ (i + 1 + e) * c := by
  rw [← mul_assoc, ← pow_add]

/-- **Taylor expansion of inner products against the moment curve.**

The vector `(⟪x, gam k c' m⟫)_m` is obtained from `(⟪x, gam k c m⟫)_m` by applying the
truncated exponential of the shift `c' - c`: for every `m`,
`⟪x, gam k c' m⟫ = ∑_{e ≤ k} (c'-c)^e / e! · ⟪x, gam k c (m+e)⟫`. -/
lemma gam_inner_taylor (k : ℕ) (c c' : ℝ) (x : Fin k → ℝ) (m : ℕ) :
    (∑ j : Fin k, x j * gam k c' m j)
      = ∑ e ∈ Finset.range (k + 1),
          ((c' - c) ^ e / (e.factorial : ℝ)) * (∑ j : Fin k, x j * gam k c (m + e) j) := by
  conv_lhs => rw [show c' = c + (c' - c) by ring]
  rw [gam_add]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Polar plates at nearby centres are comparable.**

Let `gam k c i` be the `i`-th derivative vector of the moment curve at `c` (its `j`-th coordinate
is `(j+1)^↓i * c^(j+1-i)`), so that `polarPlate(d,c) = {x | ∀ i, |⟪x, gam k c (i+1)⟫| ≤ d^{-(i+1)}}`.
Then there is a constant `ρ ≥ 1`, depending only on `k`, such that for `0 < d ≤ 1`,
`c, c' ∈ [0,1]` with `|c' - c| ≤ d`, and every `x : Fin k → ℝ`,

  `sup_{1 ≤ i ≤ k} d^i |⟪x, gam k c' i⟫| ≤ ρ * sup_{1 ≤ i ≤ k} d^i |⟪x, gam k c i⟫|`.

Equivalently: the two anisotropic gauge norms differ by at most a constant, so the polar plates
`polarPlate(d,c)` and `polarPlate(d,c')` are mutual constant multiples.  This is the geometric
input for GLYZ arXiv:1912.09798, Lemma A.1 `φ_I ∗ φ_J ≲ φ_J` (`J ⊆ I`): take `d = |I|`,
`c = c_I`, `c' = c_J`. -/
theorem gam_aniso_gauge_compare (k : ℕ) (hk : 1 ≤ k) :
    ∃ ρ : ℝ, 1 ≤ ρ ∧ ∀ (d c c' : ℝ), 0 < d → d ≤ 1 → c ∈ Set.Icc (0 : ℝ) 1 →
      c' ∈ Set.Icc (0 : ℝ) 1 → |c' - c| ≤ d → ∀ x : Fin k → ℝ,
      (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          (fun i : Fin k => d ^ (i.val + 1)
            * |∑ j : Fin k, x j * Commons.Analysis.MomentCurve.gam k c' (i.val + 1) j|)
        ≤ ρ * (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          (fun i : Fin k => d ^ (i.val + 1)
            * |∑ j : Fin k, x j * Commons.Analysis.MomentCurve.gam k c (i.val + 1) j|) := by
  refine ⟨∑ e ∈ Finset.range (k + 1), (1 : ℝ) / (e.factorial : ℝ), ?hρ, ?hmain⟩
  · -- the constant is at least `1` (the `e = 0` term)
    have h0 : (0 : ℕ) ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
    have hnn : ∀ e ∈ Finset.range (k + 1), (0 : ℝ) ≤ 1 / (e.factorial : ℝ) := by
      intro e _
      positivity
    calc (1 : ℝ) = (1 : ℝ) / (((0 : ℕ)).factorial : ℝ) := by norm_num
      _ ≤ ∑ e ∈ Finset.range (k + 1), (1 : ℝ) / (e.factorial : ℝ) :=
          Finset.single_le_sum hnn h0
  · intro d c c' hd hd1 hc hc' hcc x
    -- the weighted supremum of the reference centre
    set G : ℝ := (Finset.univ : Finset (Fin k)).sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      (fun i : Fin k => d ^ (i.val + 1)
        * |∑ j : Fin k, x j * gam k c (i.val + 1) j|) with hG
    have hG0 : 0 ≤ G := by
      rw [hG]
      exact le_trans (by positivity)
        (Finset.le_sup' _ (Finset.mem_univ (⟨0, hk⟩ : Fin k)))
    -- every weighted coordinate at the reference centre is bounded by `G`
    have hY : ∀ m : ℕ, 1 ≤ m →
        d ^ m * |∑ j : Fin k, x j * gam k c m j| ≤ G := by
      intro m hm
      by_cases hmk : m ≤ k
      · have hi : m - 1 < k := by omega
        have hb : (⟨m - 1, hi⟩ : Fin k) ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
        have hfm : (fun i : Fin k => d ^ (i.val + 1)
              * |∑ j : Fin k, x j * gam k c (i.val + 1) j|) (⟨m - 1, hi⟩ : Fin k)
            = d ^ m * |∑ j : Fin k, x j * gam k c m j| := by
          simp only [Nat.sub_add_cancel hm]
        rw [hG, ← hfm]
        exact Finset.le_sup'
          (f := fun i : Fin k => d ^ (i.val + 1)
            * |∑ j : Fin k, x j * gam k c (i.val + 1) j|) hb
      · have hz : (∑ j : Fin k, x j * gam k c m j) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          have hgj : gam k c m j = 0 := congrFun (gam_eq_zero k (by omega : k < m) c) j
          rw [hgj, mul_zero]
        rw [hz, abs_zero, mul_zero]
        exact hG0
    -- bound each weighted coordinate at the nearby centre
    have hbound : ∀ i : Fin k,
        d ^ (i.val + 1) * |∑ j : Fin k, x j * gam k c' (i.val + 1) j|
          ≤ (∑ e ∈ Finset.range (k + 1), (1 : ℝ) / (e.factorial : ℝ)) * G := by
      intro i
      rw [gam_inner_taylor k c c' x (i.val + 1)]
      have hnl : ∀ e : ℕ, e ∈ Finset.range (k + 1) →
          d ^ (i.val + 1)
              * |((c' - c) ^ e / (e.factorial : ℝ))
                  * (∑ j : Fin k, x j * gam k c (i.val + 1 + e) j)|
            ≤ (1 : ℝ) / (e.factorial : ℝ) * G := by
        intro e he
        have hfac : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast e.factorial_pos
        have hpow : |c' - c| ^ e ≤ d ^ e := pow_le_pow_left₀ (abs_nonneg _) hcc e
        have hYb := hY (i.val + 1 + e) (by omega)
        have hnonneg : (0 : ℝ) ≤ 1 / (e.factorial : ℝ) := by positivity
        rw [abs_mul, abs_div, abs_pow, abs_of_pos hfac]
        calc d ^ (i.val + 1) * (|c' - c| ^ e / (e.factorial : ℝ)
                * |∑ j : Fin k, x j * gam k c (i.val + 1 + e) j|)
            = (1 / (e.factorial : ℝ)) * (d ^ (i.val + 1)
                * (|c' - c| ^ e
                  * |∑ j : Fin k, x j * gam k c (i.val + 1 + e) j|)) := by
              ring
          _ ≤ (1 / (e.factorial : ℝ)) * (d ^ (i.val + 1)
                * (d ^ e * |∑ j : Fin k, x j * gam k c (i.val + 1 + e) j|)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hpow (abs_nonneg _)) (by positivity)) hnonneg
          _ = (1 / (e.factorial : ℝ))
                * (d ^ (i.val + 1 + e)
                    * |∑ j : Fin k, x j * gam k c (i.val + 1 + e) j|) := by
              rw [pow_mul_pow_mul]
          _ ≤ (1 / (e.factorial : ℝ)) * G := mul_le_mul_of_nonneg_left hYb hnonneg
          _ = (1 : ℝ) / (e.factorial : ℝ) * G := by ring
      calc d ^ (i.val + 1) * |∑ e ∈ Finset.range (k + 1),
              ((c' - c) ^ e / (e.factorial : ℝ))
                * (∑ j : Fin k, x j * gam k c (i.val + 1 + e) j)|
          ≤ d ^ (i.val + 1) * ∑ e ∈ Finset.range (k + 1),
              |((c' - c) ^ e / (e.factorial : ℝ))
                * (∑ j : Fin k, x j * gam k c (i.val + 1 + e) j)| := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.abs_sum_le_sum_abs _ _
        _ = ∑ e ∈ Finset.range (k + 1), d ^ (i.val + 1)
              * |((c' - c) ^ e / (e.factorial : ℝ))
                * (∑ j : Fin k, x j * gam k c (i.val + 1 + e) j)| := by
            rw [Finset.mul_sum]
        _ ≤ ∑ e ∈ Finset.range (k + 1), (1 : ℝ) / (e.factorial : ℝ) * G :=
            Finset.sum_le_sum hnl
        _ = (∑ e ∈ Finset.range (k + 1), (1 : ℝ) / (e.factorial : ℝ)) * G := by
            rw [Finset.sum_mul]
    have hfinal := Finset.sup'_le (s := (Finset.univ : Finset (Fin k)))
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
      (fun i : Fin k => d ^ (i.val + 1)
        * |∑ j : Fin k, x j * gam k c' (i.val + 1) j|)
      (fun i _ => hbound i)
    rwa [hG] at hfinal

end Commons.Analysis.MomentCurve