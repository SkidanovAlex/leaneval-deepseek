import Mathlib
import Submission.Work.A7Hi2.RealScaleDefs

namespace Work.A7Hi2

/-- A uniform bound for the sampled dilation kernel: for a Schwartz kernel `K` bounded by `C`,
`‖(1/s)·K (j/s)‖ ≤ C/s`. -/
lemma norm_bumpKernR_le (K : SchwartzMap ℝ ℂ) {C : ℝ} (hC : ∀ x : ℝ, ‖K x‖ ≤ C)
    {s : ℝ} (hs : 1 ≤ s) (j : ℤ) : ‖bumpKernR K s j‖ ≤ C / s := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hns : ‖((1 : ℂ) / (s : ℂ))‖ = 1 / s := by
    rw [norm_div, norm_one, Complex.norm_of_nonneg (le_of_lt hs0)]
  unfold bumpKernR
  rw [norm_mul, hns]
  calc (1 / s) * ‖K ((j : ℝ) / s)‖ ≤ (1 / s) * C := by
        exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
    _ = C / s := by ring

/-- The difference kernel of two comparable dilations is bounded by `3C/σ` where `C` bounds `K`. -/
lemma norm_diffKernR_le (K : SchwartzMap ℝ ℂ) {C : ℝ} (hC : ∀ x : ℝ, ‖K x‖ ≤ C) (hC0 : 0 ≤ C)
    {σ ρ : ℝ} (hσ : 1 ≤ σ) (hρ : 1 ≤ ρ) (hc : σ ≤ 2 * ρ) (j : ℤ) :
    ‖diffKernR K σ ρ j‖ ≤ 3 * (C * (1 / σ)) := by
  have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le zero_lt_one hσ
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hle : σ / 2 ≤ ρ := by linarith
  have hratio : (1 : ℝ) / ρ ≤ 2 / σ := by
    have h := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < σ / 2) hle
    have he : (1 : ℝ) / (σ / 2) = 2 / σ := by
      field_simp
    linarith [h, he.le, he.ge]
  have h2 : C / ρ ≤ 2 * C / σ := by
    have hh : C * ((1 : ℝ) / ρ) ≤ C * (2 / σ) := mul_le_mul_of_nonneg_left hratio hC0
    have e1 : C * ((1 : ℝ) / ρ) = C / ρ := by ring
    have e2 : C * (2 / σ) = 2 * C / σ := by ring
    linarith [hh, e1.le, e1.ge, e2.le, e2.ge]
  have h1 : ‖bumpKernR K σ j‖ ≤ C / σ := norm_bumpKernR_le K hC hσ j
  have h3 : ‖bumpKernR K ρ j‖ ≤ C / ρ := norm_bumpKernR_le K hC hρ j
  have h4 : ‖diffKernR K σ ρ j‖ ≤ C / σ + C / ρ := by
    unfold diffKernR
    exact le_trans (norm_sub_le _ _) (add_le_add h1 h3)
  have h5 : C / σ + 2 * C / σ = 3 * (C * (1 / σ)) := by ring
  linarith [h4, h2, h5.le, h5.ge]

theorem linDiffKernR_size (K : SchwartzMap ℝ ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (z : ℤ),
      ‖linDiffKernR K σ ρ U ω z‖ ≤ B := by
  set C : ℝ := |(SchwartzMap.seminorm ℝ 0 0) K| with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact abs_nonneg _
  have hC : ∀ x : ℝ, ‖K x‖ ≤ C := by
    intro x
    rw [hCdef]
    exact le_trans (SchwartzMap.norm_le_seminorm ℝ K x) (le_abs_self _)
  refine ⟨6 * (C + 1), by linarith, ?_⟩
  intro σ ρ hσ1 hσ2 hρ1 hρ2 hcomp U ω z
  -- lacunarity: `2 ^ n ≤ σ n`
  have hpow : ∀ n : ℕ, (2 : ℝ) ^ n ≤ σ n := by
    intro n
    induction n with
    | zero => simpa using hσ1 0
    | succ n ih =>
        have h1 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
        rw [h1]
        linarith [hσ2 n, ih]
  -- the geometric bound
  have hsum : ∑ n ∈ U, (1 : ℝ) / σ n ≤ 2 := by
    have h1 : ∀ n ∈ U, (1 : ℝ) / σ n ≤ (1 / 2 : ℝ) ^ n := by
      intro n _
      have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      have h := one_div_le_one_div_of_le hpos (hpow n)
      simpa [one_div_pow] using h
    calc ∑ n ∈ U, (1 : ℝ) / σ n ≤ ∑ n ∈ U, (1 / 2 : ℝ) ^ n := Finset.sum_le_sum h1
      _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n :=
          Summable.sum_le_tsum U (fun i _ => by positivity)
            (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      _ = 2 := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
  -- per-term bound
  have hterm : ∀ n ∈ U, ‖diffKernR K (σ n) (ρ n) z‖ ≤ 3 * (C * (1 / σ n)) := by
    intro n _
    exact norm_diffKernR_le K hC hC0 (hσ1 n) (hρ1 n) (hcomp n).2 z
  have hmain : ‖linDiffKernR K σ ρ U ω z‖ ≤ 3 * C * ∑ n ∈ U, (1 : ℝ) / σ n := by
    show ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * diffKernR K (σ n) (ρ n) z‖ ≤
      3 * C * ∑ n ∈ U, (1 : ℝ) / σ n
    calc ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * diffKernR K (σ n) (ρ n) z‖
        ≤ ∑ n ∈ U, ‖Work.KMTAreas.ADev.bSign ω n * diffKernR K (σ n) (ρ n) z‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ U, ‖diffKernR K (σ n) (ρ n) z‖ := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_mul, Work.KMTAreas.ADev.norm_bSign, one_mul]
      _ ≤ ∑ n ∈ U, 3 * (C * (1 / σ n)) := Finset.sum_le_sum hterm
      _ = 3 * C * ∑ n ∈ U, (1 : ℝ) / σ n := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by ring
  have hfin : 3 * C * ∑ n ∈ U, (1 : ℝ) / σ n ≤ 6 * (C + 1) := by
    have h3C : (0 : ℝ) ≤ 3 * C := by linarith
    have h := mul_le_mul_of_nonneg_left hsum h3C
    linarith [h]
  linarith [hmain, hfin]

end Work.A7Hi2
