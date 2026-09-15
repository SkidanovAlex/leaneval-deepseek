import Mathlib
import Submission.Commons.Combinatorics.Transference.dual_inner_unorm
import Submission.Commons.Combinatorics.Transference.poly_lemma_abstract
import Submission.Commons.Combinatorics.Transference.Unorm_pow

namespace Commons.Combinatorics.Transference

set_option linter.unusedVariables false in
/-- **Green–Tao Lemma 7.3, lower bound on the dual correlation (residual form).**

`davg d F x` is the dual function `𝒟F(x) = |G|^{-d} ∑_h ∏_{ω ≠ 0} F(x + ω·h)` and
`Unorm d F` the Gowers `U^d` norm.  If `F` agrees with the residual
`f - 𝔼(f | P)` outside the exceptional set `Ω'`, the dual function is bounded by `M`,
`Q` refines the level sets of `𝒟F` at resolution `ε` (`hQcl`), and
`γ ≤ ‖F‖_{U^d}^{2^d}`, then

`|G|·γ - M ∑_{Ω'} |F| - ε ∑ |F| ≤ |∑_{x ∉ Ω'} (f(x) - 𝔼(f|P)(x)) · 𝔼(𝒟F | Q)(x)|`.

This is the estimate that extracts the non-Gowers-uniformity of `F` from the pairing of
the residual `f - 𝔼(f|P)` with the dual function, after replacing `𝒟F` by its average over
the `Q`-atom (which is legitimate at a cost of `ε ∑ |F|` by `hQcl`). -/
theorem dual_corr_lower {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d)
    (P Q : ZMod p → Finset (ZMod p)) (hQmem : ∀ x, x ∈ Q x)
    (Ω Ω' : Finset (ZMod p)) (hΩsub : Ω ⊆ Ω') (hΩ' : ∀ x ∈ Ω', Q x ⊆ Ω')
    (F f : ZMod p → ℝ) (hFx0 : ∀ x ∈ Ω, F x = 0)
    (hFxe : ∀ x, x ∉ Ω' → F x = f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y))
    {M ε γ : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hMb : ∀ x, |davg d F x| ≤ M)
    (hQcl : ∀ x y : ZMod p, y ∈ Q x → |davg d F y - davg d F x| ≤ ε)
    (hU : γ ≤ Unorm d F ^ (2 ^ d)) :
    (Fintype.card (ZMod p) : ℝ) * γ
      - M * (∑ y ∈ Ω', |F y|)
      - ε * (∑ y, |F y|)
      ≤ |∑ x ∈ Finset.univ \ Ω', (f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)) *
          (((Q x).card : ℝ)⁻¹ * (∑ z ∈ Q x, davg d F z))| := by
  classical
  set N : ℝ := (Fintype.card (ZMod p) : ℝ) with hNdef
  set Φ : ZMod p → ℝ := fun x => ((Q x).card : ℝ)⁻¹ * ∑ z ∈ Q x, davg d F z with hΦdef
  have hNnonneg : 0 ≤ N := by rw [hNdef]; positivity
  -- (0) `Φ` is `ε`-close to `davg d F`
  have hΦclose : ∀ x : ZMod p, |Φ x - davg d F x| ≤ ε := by
    intro x
    have hxmem : x ∈ Q x := hQmem x
    have hcardpos : 0 < (Q x).card := Finset.card_pos.mpr ⟨x, hxmem⟩
    have hcardposR : (0:ℝ) < ((Q x).card : ℝ) := by exact_mod_cast hcardpos
    have hinvnn : 0 ≤ ((Q x).card : ℝ)⁻¹ := inv_nonneg.mpr hcardposR.le
    have hrewrite : Φ x - davg d F x
        = ((Q x).card : ℝ)⁻¹ * ∑ z ∈ Q x, (davg d F z - davg d F x) := by
      simp only [hΦdef]
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [hrewrite, abs_mul, abs_of_nonneg hinvnn]
    calc ((Q x).card : ℝ)⁻¹ * |∑ z ∈ Q x, (davg d F z - davg d F x)|
        ≤ ((Q x).card : ℝ)⁻¹ * ∑ z ∈ Q x, |davg d F z - davg d F x| := by
          apply mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hinvnn
      _ ≤ ((Q x).card : ℝ)⁻¹ * ∑ z ∈ Q x, ε := by
          apply mul_le_mul_of_nonneg_left _ hinvnn
          apply Finset.sum_le_sum; intro z hz
          exact hQcl x z hz
      _ = ε := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
  -- (1) the full pairing is `N · ‖F‖^{2^d}`
  have huniv : ∑ x : ZMod p, F x * davg d F x = N * Unorm d F ^ (2 ^ d) := by
    rw [hNdef]; exact dual_inner_unorm hd F
  -- (2) the exceptional part is controlled by `M`
  have habs_sub_abs_le_abs_add : ∀ a b : ℝ, |a| - |b| ≤ |a + b| := by
    intro a b
    have h := abs_add_le (a + b) (-b)
    rw [add_neg_cancel_right, abs_neg] at h
    linarith
  have hΩ'bound : ∑ x ∈ Ω', F x * davg d F x ≤ M * ∑ x ∈ Ω', |F x| := by
    have h2 : |∑ x ∈ Ω', F x * davg d F x| ≤ M * ∑ x ∈ Ω', |F x| := by
      calc |∑ x ∈ Ω', F x * davg d F x|
          ≤ ∑ x ∈ Ω', |F x * davg d F x| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x ∈ Ω', |F x| * |davg d F x| := by simp_rw [abs_mul]
        _ ≤ ∑ x ∈ Ω', |F x| * M := by
            apply Finset.sum_le_sum; intro x _
            exact mul_le_mul_of_nonneg_left (hMb x) (abs_nonneg _)
        _ = (∑ x ∈ Ω', |F x|) * M := by rw [Finset.sum_mul]
        _ = M * ∑ x ∈ Ω', |F x| := by ring
    exact le_trans (le_abs_self _) h2
  have hsplit : ∑ x ∈ Finset.univ \ Ω', F x * davg d F x
      = (∑ x, F x * davg d F x) - ∑ x ∈ Ω', F x * davg d F x := by
    have h := Finset.sum_sdiff (f := fun x => F x * davg d F x) (Finset.subset_univ Ω')
    linarith
  have hA : N * γ - M * ∑ y ∈ Ω', |F y|
      ≤ |∑ x ∈ Finset.univ \ Ω', F x * davg d F x| := by
    have h4 : N * γ ≤ ∑ x, F x * davg d F x := by
      rw [huniv]
      exact mul_le_mul_of_nonneg_left hU hNnonneg
    have h6 : N * γ - M * ∑ y ∈ Ω', |F y|
        ≤ ∑ x ∈ Finset.univ \ Ω', F x * davg d F x := by
      rw [hsplit]; linarith
    exact le_trans h6 (le_abs_self _)
  -- (3) replacing `davg d F` by `Φ` on the complement
  have hB : |∑ x ∈ Finset.univ \ Ω', F x * (Φ x - davg d F x)| ≤ ε * ∑ y, |F y| := by
    calc |∑ x ∈ Finset.univ \ Ω', F x * (Φ x - davg d F x)|
        ≤ ∑ x ∈ Finset.univ \ Ω', |F x * (Φ x - davg d F x)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x ∈ Finset.univ \ Ω', |F x| * |Φ x - davg d F x| := by simp_rw [abs_mul]
      _ ≤ ∑ x ∈ Finset.univ \ Ω', |F x| * ε := by
          apply Finset.sum_le_sum; intro x _
          exact mul_le_mul_of_nonneg_left (hΦclose x) (abs_nonneg _)
      _ = (∑ x ∈ Finset.univ \ Ω', |F x|) * ε := by rw [Finset.sum_mul]
      _ = ε * ∑ x ∈ Finset.univ \ Ω', |F x| := by ring
      _ ≤ ε * ∑ y, |F y| := by
          apply mul_le_mul_of_nonneg_left _ hε.le
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
            (fun x _ _ => abs_nonneg _)
  have hdecomp : ∑ x ∈ Finset.univ \ Ω', F x * Φ x
      = ∑ x ∈ Finset.univ \ Ω', F x * davg d F x
        + ∑ x ∈ Finset.univ \ Ω', F x * (Φ x - davg d F x) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    ring
  have hmain : N * γ - M * (∑ y ∈ Ω', |F y|) - ε * (∑ y, |F y|)
      ≤ |∑ x ∈ Finset.univ \ Ω', F x * Φ x| := by
    have htri : |∑ x ∈ Finset.univ \ Ω', F x * davg d F x|
        - |∑ x ∈ Finset.univ \ Ω', F x * (Φ x - davg d F x)|
        ≤ |∑ x ∈ Finset.univ \ Ω', F x * Φ x| := by
      rw [hdecomp]
      exact habs_sub_abs_le_abs_add _ _
    linarith [hA, hB, htri]
  have hrhs : ∑ x ∈ Finset.univ \ Ω',
        (f x - ((P x).card : ℝ)⁻¹ * (∑ y ∈ P x, f y)) *
          (((Q x).card : ℝ)⁻¹ * (∑ z ∈ Q x, davg d F z))
      = ∑ x ∈ Finset.univ \ Ω', F x * Φ x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [← hFxe x hx.2]
  rw [hrhs]
  linarith [hmain]

end Commons.Combinatorics.Transference
