import Mathlib
import Submission.Work.FIArea6Road.TauHeartDefs

namespace Work.FIArea6Road

/-- **Sharp tail bound for the Fourier coefficients of `q`, over the complement of the
frequency window.**

For `θ ∈ (0,1]`, `L ≥ 1` and `s = Finset.Icc (−L) L`,
`Σ_{|ℓ| > L} |q̂(ℓ)| ≤ 2·10⁷/(πθL)`.

Route (all ingredients are proved except the bookkeeping):
`Summable.tsum_le_of_sum_le` reduces the subtype sum to the bound
`∑ ℓ ∈ u, ‖fcoef q ℓ‖ ≤ 2·10⁷/(πθL)` for every *finset* `u` of the complement subtype; such a `u`
is contained in `Finset.Icc (−M) M \ Finset.Icc (−L) L` for `M := u.sup (·.natAbs)` (after mapping
`u` into `ℤ` by `Subtype.val`), and there
`Work.FIArea5.S16.annulus_le` (even nonnegative weight) plus `Work.FIArea5.S16.sum_Ioo_bound`
give `∑ ≤ (1/2π)·10⁷·θ·2·(2/(θ²L)) = (2/π)·10⁷/(θL) ≤ 2·10⁷/(πθL)`, using
`Work.FIArea5.S16.fcoef_bound` pointwise. -/
theorem TauHeartFcoefTailSub (q : ℝ → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2) (L : ℕ) (hL : 1 ≤ L) :
    ∑' (ℓ : ↥(((Finset.Icc (-(L : ℤ)) (L : ℤ)) : Set ℤ))ᶜ), ‖Work.FIArea5.S16.fcoef q (ℓ : ℤ)‖
      ≤ 20000000 / (Real.pi * θ * (L : ℝ)) := by
  -- the frequency window `s = [-L, L]`, as a set
  set S : Set ℤ := (Finset.Icc (-(L : ℤ)) (L : ℤ) : Set ℤ) with hS
  -- absolute summability of the Fourier coefficients
  have hs : Summable (fun ℓ : ℤ => ‖Work.FIArea5.S16.fcoef q ℓ‖) :=
    (Work.FIArea5.S16.fcoef_summable q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2).norm
  -- reduce the `tsum` over the complement subtype to a uniform bound on finsets
  refine Summable.tsum_le_of_sum_le ?_ ?_
  · exact hs.subtype _
  · intro u
    -- the enclosing symmetric window `[-M, M]`
    set M : ℕ := u.sup (fun ℓ : ↥Sᶜ => ((ℓ : ℤ)).natAbs) with hM
    set A : ℝ := (1 / (2 * Real.pi)) * (10000000 * θ) with hA
    -- push the sum forward along the injection `Subtype.val`
    have hsumimage : ∑ i ∈ u, ‖Work.FIArea5.S16.fcoef q (i : ℤ)‖
        = ∑ k ∈ u.image (fun ℓ : ↥Sᶜ => (ℓ : ℤ)), ‖Work.FIArea5.S16.fcoef q k‖ :=
      (Finset.sum_image (f := fun k : ℤ => ‖Work.FIArea5.S16.fcoef q k‖)
        (g := fun ℓ : ↥Sᶜ => (ℓ : ℤ)) (Subtype.coe_injective.injOn)).symm
    -- every index of `u` sits in the annulus `L < |ℓ| ≤ M`
    have hsub : u.image (fun ℓ : ↥Sᶜ => (ℓ : ℤ))
        ⊆ (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨a, ha, rfl⟩ := hk
      rw [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]
        have h1 : ((a : ℤ).natAbs : ℤ) ≤ (M : ℤ) :=
          Int.ofNat_le.mpr (Finset.le_sup (f := fun ℓ : ↥Sᶜ => ((ℓ : ℤ)).natAbs) ha)
        have h2 : |(a : ℤ)| ≤ (M : ℤ) := by rwa [Int.abs_eq_natAbs]
        exact abs_le.mp h2
      · intro hmem
        exact a.2 (by simpa [hS] using hmem)
    have hb1 : ∑ k ∈ u.image (fun ℓ : ↥Sᶜ => (ℓ : ℤ)), ‖Work.FIArea5.S16.fcoef q k‖
        ≤ ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)),
            ‖Work.FIArea5.S16.fcoef q k‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => norm_nonneg _)
    -- pointwise bound by the even weight `A·(1+(θℓ)²)⁻¹`
    have hb2 : ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)),
          ‖Work.FIArea5.S16.fcoef q k‖
        ≤ ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)),
            A * (1 + (θ * (k : ℝ)) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro k _
      have hbk := Work.FIArea5.S16.fcoef_bound q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2 k
      calc ‖Work.FIArea5.S16.fcoef q k‖
          ≤ (1 / (2 * Real.pi)) * (10000000 * θ * (1 + (θ * (k : ℝ)) ^ 2)⁻¹) := hbk
        _ = A * (1 + (θ * (k : ℝ)) ^ 2)⁻¹ := by rw [hA]; ring
    have hGeven : Function.Even (fun ℓ : ℤ => A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) := by
      intro ℓ
      show A * (1 + (θ * ((-ℓ : ℤ) : ℝ)) ^ 2)⁻¹ = A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹
      rw [show (θ * ((-ℓ : ℤ) : ℝ)) = -(θ * (ℓ : ℝ)) by push_cast; ring, neg_sq]
    have hGnn : ∀ ℓ : ℤ, 0 ≤ A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ := fun ℓ => by positivity
    have hb3 := Work.FIArea5.S16.annulus_le L M
      (fun ℓ : ℤ => A * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹) hGeven hGnn
    have hb3e : (∑ n ∈ Finset.Ioo L (M + 1), A * (1 + (θ * (((n : ℤ)) : ℝ)) ^ 2)⁻¹)
        = ∑ n ∈ Finset.Ioo L (M + 1), A * (1 + (θ * (n : ℝ)) ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n _
      norm_num
    have hb4 : ∑ n ∈ Finset.Ioo L (M + 1), A * (1 + (θ * (n : ℝ)) ^ 2)⁻¹
        ≤ A * (2 / (θ ^ 2 * (L : ℝ))) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (Work.FIArea5.S16.sum_Ioo_bound L M θ hθ hL) (by positivity)
    have hb5 : 2 * (A * (2 / (θ ^ 2 * (L : ℝ)))) = 20000000 / (Real.pi * θ * (L : ℝ)) := by
      rw [hA]
      field_simp
      ring
    calc ∑ i ∈ u, ‖Work.FIArea5.S16.fcoef q (i : ℤ)‖
        = ∑ k ∈ u.image (fun ℓ : ↥Sᶜ => (ℓ : ℤ)), ‖Work.FIArea5.S16.fcoef q k‖ := hsumimage
      _ ≤ ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)),
            ‖Work.FIArea5.S16.fcoef q k‖ := hb1
      _ ≤ ∑ k ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)) \ (Finset.Icc (-(L : ℤ)) (L : ℤ)),
            A * (1 + (θ * (k : ℝ)) ^ 2)⁻¹ := hb2
      _ ≤ 2 * ∑ n ∈ Finset.Ioo L (M + 1), A * (1 + (θ * (((n : ℤ)) : ℝ)) ^ 2)⁻¹ := hb3
      _ = 2 * ∑ n ∈ Finset.Ioo L (M + 1), A * (1 + (θ * (n : ℝ)) ^ 2)⁻¹ := by rw [hb3e]
      _ ≤ 2 * (A * (2 / (θ ^ 2 * (L : ℝ)))) := mul_le_mul_of_nonneg_left hb4 (by norm_num)
      _ = 20000000 / (Real.pi * θ * (L : ℝ)) := hb5

end Work.FIArea6Road
