/-
# `Submission.Work.FITop4.Red5.assembly_helpers` — combinatorial helpers for `reduction_save`

* `fiber_sum_annM` — the reindexing `Σ_{m ∈ (M,2M]} Σ_{w : |w|² = m} F w = Σ_{w ∈ annM} F w`;
* `radial_pieces_flat` — the radial partition of `radial_partition_scale` *filtered* so that every
  surviving piece is supported inside `(N, 2N]` (no protrusion past `2N`).
-/
import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.radial_partition_scale
import Submission.Work.FITop4.Red5.angular_partition_le
import Submission.Work.FITop4.Red5.anFI_sum_eq_gauss
import Submission.Work.FITop4.Red5.Vocab

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Box membership from the norm -/

/-- A Gaussian integer of norm `m` lies in the box `gBox R` as soon as `m ≤ R²`. -/
lemma mem_gBox_of_norm_sq {w : GaussianInt} {m R : ℕ} (hw : Work.FIPlan.gnorm w = m)
    (hR : m ≤ R ^ 2) : w ∈ Work.FIPlan.gBox (R : ℤ) := by
  rw [mem_gBox_iff]
  have hco : w.re.natAbs ^ 2 + w.im.natAbs ^ 2 = m := natAbs_gnorm w m hw
  have hre : w.re.natAbs ≤ R := by
    have h : w.re.natAbs ^ 2 ≤ R ^ 2 := le_trans (by rw [← hco]; exact Nat.le_add_right _ _) hR
    rw [pow_two, pow_two] at h
    exact Nat.mul_self_le_mul_self_iff.mp h
  have him : w.im.natAbs ≤ R := by
    have h : w.im.natAbs ^ 2 ≤ R ^ 2 := le_trans (by rw [← hco]; exact Nat.le_add_left _ _) hR
    rw [pow_two, pow_two] at h
    exact Nat.mul_self_le_mul_self_iff.mp h
  have hreZ : (w.re.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast hre
  have himZ : (w.im.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast him
  constructor
  · simp only [Finset.mem_Icc]
    exact ⟨by
      have h1 : -(w.re) ≤ (w.re.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -w.re))
      linarith, by
      have h1 : w.re ≤ (w.re.natAbs : ℤ) := Int.le_natAbs (a := w.re)
      linarith⟩
  · simp only [Finset.mem_Icc]
    exact ⟨by
      have h1 : -(w.im) ≤ (w.im.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -w.im))
      linarith, by
      have h1 : w.im ≤ (w.im.natAbs : ℤ) := Int.le_natAbs (a := w.im)
      linarith⟩

/-- The `gnorm`-fibres of `gBox R` and `gBox m` agree as soon as `1 ≤ m ≤ R²`. -/
lemma gBox_filter_gnorm_eq' {m R : ℕ} (hm : 1 ≤ m) (hR : m ≤ R ^ 2) :
    (Work.FIPlan.gBox (R : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m)
      = (Work.FIPlan.gBox (m : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m) := by
  ext w
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨-, hw⟩
    exact ⟨mem_gBox_of_norm_sq hw (by
      calc m = m * 1 := (mul_one m).symm
        _ ≤ m * m := Nat.mul_le_mul_left m hm
        _ = m ^ 2 := (pow_two m).symm), hw⟩
  · rintro ⟨-, hw⟩
    exact ⟨mem_gBox_of_norm_sq hw hR, hw⟩

/-- **The `m`-fibre reindexing.**  For `Pa.M = A` (`A ≥ 1`), the sum over the Gaussian annulus
`annM Pa` is the sum over the dyadic `m`-window `(A, 2A]` of the sphere sums. -/
lemma annM_filter_gnorm_eq {Pa : Work.FITop.Params} {A m : ℕ} (hM : Pa.M = A) (hA : 1 ≤ A)
    (hm1 : A + 1 ≤ m) (hm2 : m ≤ 2 * A) :
    (Work.FITop3.annM Pa).filter (fun w => Work.FIPlan.gnorm w = m) = wSph m := by
  have hAm : A < m := by omega
  have hm1' : 1 ≤ m := by omega
  have hR2 : m ≤ (⌈Real.sqrt (4 * (A : ℝ))⌉₊) ^ 2 := by
    have hceil : Real.sqrt (4 * (A : ℝ)) ≤ ((⌈Real.sqrt (4 * (A : ℝ))⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have hsq : (4 * (A : ℝ)) ≤ ((⌈Real.sqrt (4 * (A : ℝ))⌉₊ : ℕ) : ℝ) ^ 2 := by
      calc (4 * (A : ℝ)) = (Real.sqrt (4 * (A : ℝ))) ^ 2 :=
            (Real.sq_sqrt (show (0 : ℝ) ≤ 4 * (A : ℝ) by positivity)).symm
        _ ≤ ((⌈Real.sqrt (4 * (A : ℝ))⌉₊ : ℕ) : ℝ) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hceil 2
    have hm2' : (m : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hm2
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    exact_mod_cast (le_trans (by linarith : (m : ℝ) ≤ 4 * (A : ℝ)) hsq)
  have hboxeq : Work.FIPlan.gBox (Work.FITop.radM Pa)
      = Work.FIPlan.gBox ((⌈Real.sqrt (4 * (A : ℝ))⌉₊ : ℕ) : ℤ) := by
    rw [Work.FITop.radM, hM]
  have hm2sq : m ≤ m ^ 2 := by
    calc m = m * 1 := (mul_one m).symm
      _ ≤ m * m := Nat.mul_le_mul_left m hm1'
      _ = m ^ 2 := (pow_two m).symm
  ext w
  constructor
  · intro hw
    rw [Finset.mem_filter, Work.FITop3.mem_annM, Work.FITop.boxM] at hw
    obtain ⟨⟨hbox, hlt, hle⟩, hgm⟩ := hw
    rw [wSph, Finset.mem_filter]
    exact ⟨mem_gBox_of_norm_sq hgm hm2sq, hgm⟩
  · intro hw
    rw [wSph, Finset.mem_filter] at hw
    obtain ⟨hboxm, hgm⟩ := hw
    rw [Finset.mem_filter, Work.FITop3.mem_annM, Work.FITop.boxM, hboxeq]
    exact ⟨⟨mem_gBox_of_norm_sq hgm hR2, by rw [hgm, hM]; exact_mod_cast hAm,
      by rw [hgm, hM]; exact_mod_cast hm2⟩, hgm⟩

/-- **The `m`-fibre reindexing.**  For `Pa.M = A` (`A ≥ 1`), the sum over the Gaussian annulus
`annM Pa` is the sum over the dyadic `m`-window `(A, 2A]` of the sphere sums. -/
lemma fiber_sum_annM {Pa : Work.FITop.Params} {A : ℕ} (hM : Pa.M = A) (hA : 1 ≤ A)
    (F : GaussianInt → ℝ) :
    (∑ w ∈ Work.FITop3.annM Pa, F w)
      = ∑ m ∈ Finset.Icc (A + 1) (2 * A), ∑ w ∈ wSph m, F w := by
  have hmaps : ∀ w ∈ Work.FITop3.annM Pa,
      Work.FIPlan.gnorm w ∈ Finset.Icc (A + 1) (2 * A) := by
    intro w hw
    obtain ⟨-, hlt, hle⟩ := Work.FITop3.mem_annM.mp hw
    rw [hM] at hlt hle
    have h1 : A < Work.FIPlan.gnorm w := by exact_mod_cast hlt
    simp only [Finset.mem_Icc]
    exact ⟨by omega, by exact_mod_cast hle⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps F
  rw [← hfib]
  refine Finset.sum_congr rfl ?_
  intro m hm
  rw [Finset.mem_Icc] at hm
  rw [annM_filter_gnorm_eq hM hA hm.1 hm.2]

/-! ## 2. The radial partition with no protrusion past `2N` -/

/-- **The flat radial partition.**  From `radial_partition_scale` keep only the pieces whose box
`(aᵢ, (1+θ)aᵢ]` does *not* protrude past `2N`.  Every surviving piece is then supported in
`(N, 2N]`, hence in the primary annulus `primAnn (2N)` used by the sieve step, which is exactly
what makes the Cauchy step against `boxN` legitimate.  The price is the two boundary strips
`(N, N+θN/2]` and `(2N-2θN, 2N]`, on which the partition only satisfies `∑ ≤ 1`. -/
theorem radial_pieces_flat (N : ℕ) (θ : ℝ) (hN : 1 ≤ N) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ (K : ℕ) (a : Fin K → ℝ) (P : Fin K → ℝ → ℝ) (R : Finset (Fin K)),
      (∀ i ∈ R, ContDiff ℝ 2 (P i)) ∧
      (∀ i ∈ R, ∀ u, 0 ≤ P i u) ∧ (∀ i ∈ R, ∀ u, P i u ≤ 1) ∧
      (∀ i ∈ R, ∀ u, P i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) ∧
      (∀ i ∈ R, (N : ℝ) ≤ a i ∧ a i ≤ 2 * (N : ℝ)) ∧
      (∀ i ∈ R, ∀ u, P i u ≠ 0 → u ≤ 2 * (N : ℝ)) ∧
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i ∈ R, P i u) ≤ 1) ∧
      (∀ u, (N : ℝ) + θ * (N : ℝ) / 2 < u → u ≤ 2 * (N : ℝ) - 2 * θ * (N : ℝ) →
        (∑ i ∈ R, P i u) = 1) ∧
      (∀ i ∈ R, ∀ j, j ≤ 2 → ∀ u,
        |iteratedDeriv j (P i) u| ≤ cMoll j * (θ * a i) ^ (-(j : ℝ))) ∧
      ((R.card : ℝ) ≤ 4 / θ + 4) := by
  obtain ⟨K, a, p, hcd, hp0, hp1, hsup, ha, hsum_le, hsum_eq, hder, hK⟩ :=
    radial_partition_scale N θ hN hθ0 hθ1
  refine ⟨K, a, p, Finset.univ.filter (fun i => (1 + θ) * a i ≤ 2 * (N : ℝ)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _; exact hcd i
  · intro i _; exact hp0 i
  · intro i _; exact hp1 i
  · intro i _; exact hsup i
  · intro i _; exact ha i
  · intro i hi u hu
    exact le_trans (hsup i u hu).2 (Finset.mem_filter.mp hi).2
  · intro u hu1 hu2
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hp0 i u)) (hsum_le u hu1 hu2)
  · -- the pieces outside `R` vanish below `2N - 2θN`
    intro u hu1 hu2
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hpos : (0 : ℝ) < 1 + θ := by linarith
    have hθ2 : 0 < θ ^ 2 := pow_pos hθ0 2
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hkey : 2 * (N : ℝ) - 2 * θ * (N : ℝ) < 2 * (N : ℝ) / (1 + θ) := by
      rw [lt_div_iff₀ hpos]
      ring_nf
      nlinarith [mul_pos hθ2 hNpos]
    have hcomplement : ∀ i ∈ (Finset.univ : Finset (Fin K)), i ∉
        Finset.univ.filter (fun i => (1 + θ) * a i ≤ 2 * (N : ℝ)) → p i u = 0 := by
      intro i _ hi
      by_contra hne
      have hgt : 2 * (N : ℝ) < (1 + θ) * a i := by
        by_contra hle
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, le_of_not_gt hle⟩)
      have hlt : 2 * (N : ℝ) / (1 + θ) < a i := by
        rw [div_lt_iff₀ hpos]; linarith [hgt]
      linarith [(hsup i u hne).1, hu2, hkey, hlt]
    rw [Finset.sum_subset (Finset.subset_univ _) hcomplement]
    exact hsum_eq u hu1 (by linarith [mul_pos hθ0 hNpos])
  · intro i _; exact hder i
  · have h1 : (Finset.univ.filter (fun i => (1 + θ) * a i ≤ 2 * (N : ℝ))).card ≤ K := by
      calc (Finset.univ.filter (fun i => (1 + θ) * a i ≤ 2 * (N : ℝ))).card
          ≤ (Finset.univ : Finset (Fin K)).card := Finset.card_le_univ _
        _ = K := Finset.card_fin K
    have h2 : (↑(Finset.univ.filter (fun i => (1 + θ) * a i ≤ 2 * (N : ℝ))).card : ℝ) ≤ (K : ℝ) :=
      by exact_mod_cast h1
    linarith [hK, h2]

end

end Work.FITop4.Red5
