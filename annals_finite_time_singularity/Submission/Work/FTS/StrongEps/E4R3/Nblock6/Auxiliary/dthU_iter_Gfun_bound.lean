import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSinPow
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS.PhiStar.Psi0Aux.dthU_iter_elementary_bounds_repaired

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary

/-!
# The `D_θ`-iterates of `sin²·Γ` are dominated by `Γ·(α + B_i·sin²2θ)`

The operator is `D_θ φ = sin(2θ)·φ'` (`Work.Spaces.dthU`), and
`Γ(θ) = (sin θ cos²θ)^{α/3}` (`Work.Spaces.Gam`).  Given the Leibniz expansion of
`D_θ^i (sin²·Γ)` (`hlei`), the goal is the pointwise bound

`|D_θ^i (sin²·Γ) θ| ≤ Γ θ · (α·10⁵ + B_i·sin²(2θ))`,  `1 ≤ i ≤ 6`, `α ∈ (0,1]`, `θ ∈ Iθ`,

with constants `B_i` depending on `i` only.  This is the *α-weighted* form in which the
`i`-fold `D_θ`-derivative of `sin²·Γ` is controlled by `Γ` times a coefficient: the term of
the Leibniz sum on which all `i` derivatives fall on `Γ` carries the factor `α` (because
`D_θ^j Γ = α·T_j·Γ`, `j ≥ 1`), while every other term carries at least one derivative of
`sin²`, hence a factor `sin²(2θ)` (`dthUiter_sin_sq_iter`: `D_θ^j (sin²) θ =
cos²θ·sin²θ·R_{j-1}(cos²θ)` for `j ≥ 1`).

Consequently the *only* place where the coefficient `sin²(2θ)` is not available is the group
of terms with `j = 0` on `sin²`, i.e. the single term `r = 0` (all `i` derivatives on `Γ`),
and there the factor `α` of `D_θ^i Γ` is used instead — this is why the statement bounds by
`Γ·(α·10⁵ + B_i·sin²2θ)` and not by `Γ·B_i·sin²2θ` alone.

The endpoint `θ ∈ {0, π/2}` is harmless: `D_θ^i φ θ = sin(2θ)·(…) = 0` for `i ≥ 1`
(`dthU_iter_eq_zero_of_sin_eq_zero'`) while `Γ` vanishes there (`Gam_zero_left`,
`Gam_zero_right`), so both sides are `0`.
-/

/-- **Endpoint vanishing of the `D_θ`-iterates of `sin²`.**  For every `j ≥ 1` and every real
`θ`, `|D_θ^j (sin²) θ| ≤ 1095801216·sin²(2θ)`.  This is
`Work.FTS.PhiStar.Psi0Aux.dthUiter_sin_sq_iter` together with the coefficient bound
`∑_k |c_k| ≤ 1095801216` of the explicit polynomial `R_{j-1}`. -/
lemma abs_dthU_iter_sin_sq_le (j : ℕ) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) (θ : ℝ) :
    |Work.Spaces.dthU^[j] (fun t : ℝ => Real.sin t ^ 2) θ|
      ≤ 1095801216 * Real.sin (2 * θ) ^ 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i ≤ 6 := by omega
  rw [Work.FTS.PhiStar.Psi0Aux.dthUiter_sin_sq_iter i hi θ]
  have hb : |Polynomial.eval (Real.cos θ ^ 2) (Work.FTS.PhiStar.Psi0Aux.dthUiterPR i)|
      ≤ 1095801216 := by
    rw [Work.FTS.PhiStar.Psi0Aux.dthUiterPR_eval]
    exact le_trans
      (Work.FTS.PhiStar.Psi0Aux.dthUiter_abs_sum_pow_le _ _ _
        (sq_nonneg (Real.cos θ)) (Real.cos_sq_le_one θ))
      (Work.FTS.PhiStar.Psi0Aux.dthUiterPRcoef_sum_le i hi)
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ)),
    abs_of_nonneg (sq_nonneg (Real.sin θ))]
  have hcs : Real.cos θ ^ 2 * Real.sin θ ^ 2 = Real.sin (2 * θ) ^ 2 / 4 := by
    rw [Real.sin_two_mul]; ring
  calc Real.cos θ ^ 2 * Real.sin θ ^ 2
        * |Polynomial.eval (Real.cos θ ^ 2) (Work.FTS.PhiStar.Psi0Aux.dthUiterPR i)|
      = Real.sin (2 * θ) ^ 2 / 4
        * |Polynomial.eval (Real.cos θ ^ 2) (Work.FTS.PhiStar.Psi0Aux.dthUiterPR i)| := by rw [hcs]
    _ ≤ Real.sin (2 * θ) ^ 2 * 1095801216 :=
        mul_le_mul (by nlinarith [sq_nonneg (Real.sin (2 * θ))]) hb (abs_nonneg _) (sq_nonneg _)
    _ = 1095801216 * Real.sin (2 * θ) ^ 2 := by ring

/-- **The `Γ`-iterates are dominated by `100000·Γ`**  (`j ≤ 6`, `θ ∈ Iθ`, `0 < α ≤ 1`). -/
lemma abs_dthU_iter_Gam_le (j : ℕ) (hj : j ≤ 6) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[j] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ 100000 * Work.Spaces.Gam α θ := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    rw [Function.iterate_zero_apply,
      abs_of_nonneg (Work.Spaces.Gam_bounds α θ hα hθ).1]
    nlinarith [(Work.Spaces.Gam_bounds α θ hα hθ).1]
  · have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (j - 1) α θ'| ≤ 100000 :=
      fun θ' _ => Work.FTS.LocData6.Tfun_abs_le5 (j - 1) (by omega) α hα hα1 θ'
    have hkey := Work.Spaces.dthU_iter_Gam_abs_bound j h α hα 100000 hT θ hθ
    have hG := (Work.Spaces.Gam_bounds α θ hα hθ).1
    calc |Work.Spaces.dthU^[j] (fun t : ℝ => Work.Spaces.Gam α t) θ|
        ≤ α * 100000 * Work.Spaces.Gam α θ := hkey
      _ ≤ 100000 * Work.Spaces.Gam α θ := by nlinarith [hα, hα1, hG]

/-- **The `α`-weighted bound for the `Γ`-iterates**: for `j ≥ 1`, `D_θ^j Γ = α·T_{j-1}·Γ`
with `|T_{j-1}| ≤ 100000` on `Iθ`, hence `|D_θ^j Γ| ≤ α·100000·Γ`. -/
lemma abs_dthU_iter_Gam_le_alpha (j : ℕ) (hj1 : 1 ≤ j) (hj6 : j ≤ 6) (α : ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.dthU^[j] (fun t : ℝ => Work.Spaces.Gam α t) θ| ≤ α * 100000 * Work.Spaces.Gam α θ := by
  have hT : ∀ θ' ∈ Work.Spaces.Iθ, |Work.Spaces.Tfun (j - 1) α θ'| ≤ 100000 :=
    fun θ' _ => Work.FTS.LocData6.Tfun_abs_le5 (j - 1) (by omega) α hα hα1 θ'
  exact Work.Spaces.dthU_iter_Gam_abs_bound j hj1 α hα 100000 hT θ hθ

theorem dthU_iter_Gfun_bound
    (hlei : ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ i : ℕ, i ≤ 6 →
      Set.EqOn (Work.Spaces.dthU^[i] (fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ))
        (fun θ => ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
          (Work.Spaces.dthU^[r] (fun θ => Real.sin θ ^ 2) θ *
            Work.Spaces.dthU^[i - r] (fun θ => Work.Spaces.Gam α θ) θ))
        (Set.Ioo 0 (Real.pi / 2))) :
    ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
      ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.dthU^[i] (fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ) θ|
          ≤ Work.Spaces.Gam α θ * (α * 100000 + B i * (Real.sin (2 * θ)) ^ 2) := by
  refine ⟨fun i => 100000 * 1095801216 * ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ),
    fun i => ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) :=
      Finset.sum_nonneg fun r _ => Nat.cast_nonneg _
    exact mul_nonneg (mul_nonneg (by norm_num) (by norm_num)) h1
  · intro α hα i hi1 hi6 θ hθ
    have hα0 : 0 < α := hα.1
    have hα1 : α ≤ 1 := hα.2
    have hG0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα0 hθ).1
    by_cases hθm : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · -- The open interval: expand with the Leibniz rule and bound term by term.
      have heq : Work.Spaces.dthU^[i] (fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ) θ
          = ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
              (Work.Spaces.dthU^[r] (fun θ => Real.sin θ ^ 2) θ *
                Work.Spaces.dthU^[i - r] (fun θ => Work.Spaces.Gam α θ) θ) :=
        (hlei α hα i hi6) hθm
      -- separate the `r = 0` term (all derivatives on `Γ`)
      have hswap : (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) *
              (Work.Spaces.dthU^[r] (fun θ => Real.sin θ ^ 2) θ *
                Work.Spaces.dthU^[i - r] (fun θ => Work.Spaces.Gam α θ) θ))
          = (∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) *
              (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
                Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ))
            + (i.choose 0 : ℝ) *
              (Work.Spaces.dthU^[0] (fun θ => Real.sin θ ^ 2) θ *
                Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ) := by
        rw [Finset.sum_range_succ', Nat.sub_zero]
      have hZ : 0 ≤ Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2 :=
        mul_nonneg hG0 (sq_nonneg _)
      have hGj : ∀ j ≤ 6, |Work.Spaces.dthU^[j] (fun t : ℝ => Work.Spaces.Gam α t) θ|
          ≤ 100000 * Work.Spaces.Gam α θ := fun j hj => abs_dthU_iter_Gam_le j hj α hα0 hα1 hθ
      have hGi : |Work.Spaces.dthU^[i] (fun t : ℝ => Work.Spaces.Gam α t) θ|
          ≤ α * 100000 * Work.Spaces.Gam α θ := abs_dthU_iter_Gam_le_alpha i hi1 hi6 α hα0 hα1 hθ
      have hP0 : |(i.choose 0 : ℝ) *
            (Work.Spaces.dthU^[0] (fun θ => Real.sin θ ^ 2) θ *
              Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ)|
          ≤ α * 100000 * Work.Spaces.Gam α θ := by
        rw [Nat.choose_zero_right, Nat.cast_one, one_mul, abs_mul,
          Function.iterate_zero_apply, abs_of_nonneg (sq_nonneg (Real.sin θ))]
        calc Real.sin θ ^ 2 * |Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ|
            ≤ 1 * (α * 100000 * Work.Spaces.Gam α θ) :=
              mul_le_mul (Real.sin_sq_le_one θ) hGi (abs_nonneg _) (by norm_num)
          _ = α * 100000 * Work.Spaces.Gam α θ := by ring
      have hPr : ∀ r ∈ Finset.range i,
          |(i.choose (r + 1) : ℝ) *
            (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
              Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ)|
          ≤ ((i.choose (r + 1) : ℝ) * (1095801216 * 100000))
            * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2) := by
        intro r hr
        have hrlt : r < i := Finset.mem_range.mp hr
        have h1 : 1 ≤ r + 1 := by omega
        have h6 : r + 1 ≤ 6 := by omega
        have hj6 : i - (r + 1) ≤ 6 := by omega
        have hA := abs_dthU_iter_sin_sq_le (r + 1) h1 h6 θ
        have hG := hGj (i - (r + 1)) hj6
        have hc0 : (0 : ℝ) ≤ (i.choose (r + 1) : ℝ) := Nat.cast_nonneg _
        rw [abs_mul, abs_mul, abs_of_nonneg hc0]
        calc (i.choose (r + 1) : ℝ)
              * (|Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ|
                * |Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ|)
            ≤ (i.choose (r + 1) : ℝ)
              * ((1095801216 * Real.sin (2 * θ) ^ 2) * (100000 * Work.Spaces.Gam α θ)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul hA hG (abs_nonneg _) (by positivity)) hc0
          _ = ((i.choose (r + 1) : ℝ) * (1095801216 * 100000))
              * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2) := by ring
      have hle : (∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ))
          ≤ ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ) := by
        have h := Finset.sum_range_succ' (fun r : ℕ => (i.choose r : ℝ)) i
        have hc : (0 : ℝ) ≤ (i.choose 0 : ℝ) := Nat.cast_nonneg _
        linarith [h]
      calc |Work.Spaces.dthU^[i] (fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ) θ|
          = |(∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) *
                (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ))
              + (i.choose 0 : ℝ) *
                (Work.Spaces.dthU^[0] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ)| := by
              rw [heq, hswap]
        _ ≤ |∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) *
                (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ)|
              + |(i.choose 0 : ℝ) *
                (Work.Spaces.dthU^[0] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i] (fun θ => Work.Spaces.Gam α θ) θ)| := abs_add_le _ _
        _ ≤ (∑ r ∈ Finset.range i, |(i.choose (r + 1) : ℝ) *
                (Work.Spaces.dthU^[r + 1] (fun θ => Real.sin θ ^ 2) θ *
                  Work.Spaces.dthU^[i - (r + 1)] (fun θ => Work.Spaces.Gam α θ) θ)|)
              + α * 100000 * Work.Spaces.Gam α θ :=
              add_le_add (Finset.abs_sum_le_sum_abs _ _) hP0
        _ ≤ (∑ r ∈ Finset.range i, ((i.choose (r + 1) : ℝ) * (1095801216 * 100000))
                * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2))
              + α * 100000 * Work.Spaces.Gam α θ :=
              add_le_add (Finset.sum_le_sum hPr) le_rfl
        _ = ((∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) * (1095801216 * 100000))
                * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2))
              + α * 100000 * Work.Spaces.Gam α θ := by rw [Finset.sum_mul]
        _ ≤ ((100000 * 1095801216 * ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ))
                * (Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ 2))
              + α * 100000 * Work.Spaces.Gam α θ := by
              have h1 : (∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ) * (1095801216 * 100000))
                  ≤ 100000 * 1095801216 * (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) := by
                rw [← Finset.sum_mul]
                calc (∑ r ∈ Finset.range i, (i.choose (r + 1) : ℝ)) * (1095801216 * 100000)
                    ≤ (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) * (1095801216 * 100000) :=
                      mul_le_mul_of_nonneg_right hle (by norm_num)
                  _ = 100000 * 1095801216 * (∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ)) := by ring
              exact add_le_add (mul_le_mul_of_nonneg_right h1 hZ) le_rfl
        _ = Work.Spaces.Gam α θ * (α * 100000
              + (100000 * 1095801216 * ∑ r ∈ Finset.range (i + 1), (i.choose r : ℝ))
                * (Real.sin (2 * θ)) ^ 2) := by ring
    · -- The two endpoints, where both sides vanish.
      have hcases : θ = 0 ∨ θ = Real.pi / 2 := by
        rcases hθ with ⟨h0, h1⟩
        rcases lt_or_eq_of_le h0 with h0' | h0'
        · rcases lt_or_eq_of_le h1 with h1' | h1'
          · exact absurd ⟨h0', h1'⟩ hθm
          · exact Or.inr h1'
        · exact Or.inl h0'.symm
      rcases hcases with rfl | rfl
      · rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' _ hi1 (by simp), abs_zero,
          Work.Spaces.Gam_zero_left α (ne_of_gt hα0)]
        simp
      · rw [Work.Spaces.dthU_iter_eq_zero_of_sin_eq_zero' _ hi1
            (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]), abs_zero,
          Work.Spaces.Gam_zero_right α (ne_of_gt hα0)]
        simp

end Work.FTS.StrongEps.E4R3.Nblock6.Auxiliary
