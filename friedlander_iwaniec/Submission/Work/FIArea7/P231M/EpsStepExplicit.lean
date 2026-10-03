/-
# `Work.FIArea7.P231.multEps_inner_bound`

The reduction of *FI* §23 from the `K`-form of Prop. 21.4 to the `ε`-form of (23.4): given

* `hK`, the bound `‖K*(M,N)‖ ≤ Bound` for the coprimality-restricted bilinear form in the
  Jacobi–Kubota symbol (Prop. 21.4, `KStarBound`),
* `hexp`, the separated expansion (20.15)+(20.19) of the multiplier sign
  `2 ε(σ,wz)(σ.re,σ.im)_∞` as a series `Σ_k ĉ_k (w/|w|)^k (z/|z|)^k` with
  `Σ_k |ĉ_k| ≤ Cexp (log 2R)^4`,
* `hcard`, the strip point count with constant `Ccard`,

the `ε`-weighted double sum is bounded by `C (log(MN+2))^8 (Bound + M√N + √(MN))`, with a constant
depending only on `M, N, Bound, Cexp, Ccard, σ`.

The pairs `(w,z)` are split into the "good" ones (the room condition (20.18), where the expansion
of `ε` is available) and the "bad" ones (a thin strip, counted by `hcard`).  On the good ones the
expansion is summed over the (finite) set of pairs and the inner sums are recognised — after
twisting the coefficients by `(w/|w|)^k`, `(z/|z|)^k` — as the restricted bilinear form `K*` of
`hK`.
-/
import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.P231.multEps_vocab
import Submission.Work.FIArea7.P231M.Aux3

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary facts about `gnorm`, `gBox`, `epsUnit` and the symbols -/

private lemma gnorm_nonneg_int (z : GaussianInt) : (0 : ℤ) ≤ z.norm :=
  Zsqrtd.norm_nonneg (by norm_num) z

private lemma gnorm_cast_norm (z : GaussianInt) : (Work.FIPlan.gnorm z : ℝ) = (z.norm : ℝ) := by
  unfold Work.FIPlan.gnorm
  rw [← Int.cast_natCast, Int.natAbs_of_nonneg (gnorm_nonneg_int z)]

private lemma gnorm_eq_normSq (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = Complex.normSq z.toComplex := by
  rw [gnorm_cast_norm, GaussianInt.intCast_real_norm]

private lemma gnorm_eq_sq (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℝ) = ((z.re : ℤ) : ℝ) ^ 2 + ((z.im : ℤ) : ℝ) ^ 2 := by
  rw [gnorm_eq_normSq, Complex.normSq_apply, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im]
  ring

private lemma sq_norm_toComplex (z : GaussianInt) :
    ‖z.toComplex‖ ^ 2 = (Work.FIPlan.gnorm z : ℝ) := by
  rw [Complex.sq_norm, ← gnorm_eq_normSq]

private lemma gnorm_mul (z w : GaussianInt) :
    Work.FIPlan.gnorm (z * w) = Work.FIPlan.gnorm z * Work.FIPlan.gnorm w := by
  unfold Work.FIPlan.gnorm
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

/-- Membership in the box, in coordinates. -/
private lemma mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ z.re ∈ Finset.Icc (-R) R ∧ z.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hzp⟩
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    rw [← hzp]
    exact hp
  · rintro ⟨h1, h2⟩
    exact ⟨(z.re, z.im),
      by rw [Finset.product_eq_sprod, Finset.mem_product]; exact ⟨h1, h2⟩, rfl⟩

private lemma gBox_mono {R S : ℤ} (h : R ≤ S) : Work.FIPlan.gBox R ⊆ Work.FIPlan.gBox S := by
  intro z hz
  rw [mem_gBox_iff] at hz ⊢
  exact ⟨Finset.Icc_subset_Icc (neg_le_neg h) h hz.1,
         Finset.Icc_subset_Icc (neg_le_neg h) h hz.2⟩

private lemma mem_gBox_of_gnorm_le {z : GaussianInt} {N : ℕ} (h : Work.FIPlan.gnorm z ≤ N) :
    z ∈ Work.FIPlan.gBox (N : ℤ) :=
  gBox_mono (by exact_mod_cast h)
    (Work.FIArea7.mem_gBox_of_gnorm_eq (n := Work.FIPlan.gnorm z) rfl)

private lemma isPrimary_ne_zero {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) : z ≠ 0 := by
  intro hz
  have hre : z.re = 0 := by rw [hz]; rfl
  obtain ⟨k, hk⟩ := h.1
  rw [hre] at hk
  omega

private lemma epsUnit_norm {w : GaussianInt} (hw : w ≠ 0) : ‖epsUnit w‖ = 1 := by
  have hpos : (0 : ℝ) < ‖w.toComplex‖ :=
    norm_pos_iff.mpr (fun h => hw (GaussianInt.toComplex_eq_zero.mp h))
  rw [epsUnit, norm_div]
  have h1 : ‖(((‖w.toComplex‖ : ℝ)) : ℂ)‖ = ‖w.toComplex‖ := by
    rw [show ‖(((‖w.toComplex‖ : ℝ)) : ℂ)‖ = |‖w.toComplex‖| by simp,
      abs_of_nonneg hpos.le]
  rw [h1, div_self (ne_of_gt hpos)]

private lemma norm_multEps_le_one (s t : GaussianInt) :
    ‖((Work.FIArea7.MultEps s t : ℤ) : ℂ)‖ ≤ 1 := by
  rcases Work.FIArea7.multEps_eq_pm_one s t with h | h <;>
    rw [h] <;> norm_num [Complex.norm_intCast]

private lemma hilbertInf_sq (a b : ℤ) :
    ((Work.FIArea7.HilbertInf a b : ℤ) : ℂ) * ((Work.FIArea7.HilbertInf a b : ℤ) : ℂ) = 1 := by
  unfold Work.FIArea7.HilbertInf
  split_ifs <;> norm_num

private lemma hilbertInf_norm (a b : ℤ) :
    ‖((Work.FIArea7.HilbertInf a b : ℤ) : ℂ)‖ = 1 := by
  unfold Work.FIArea7.HilbertInf
  split_ifs <;> norm_num [Complex.norm_intCast]

private lemma epsRoomA_iff_epsRoomB_shift (R : ℕ) (σ w z : GaussianInt) :
    epsRoomA R σ w z ↔ epsRoomB R (σ * w) z := by
  have h1 : ‖(σ * w).toComplex‖ * ‖z.toComplex‖
      = ‖σ.toComplex‖ * ‖(w * z).toComplex‖ := by
    rw [GaussianInt.toComplex_mul, norm_mul, GaussianInt.toComplex_mul, norm_mul, mul_assoc]
  have h2 : |((((σ * w) * z).re : ℤ) : ℝ)| = |(((σ * (w * z)).re : ℤ) : ℝ)| := by
    rw [mul_assoc]
  unfold epsRoomA epsRoomB
  rw [h1, h2]

private lemma twist_norm_le_one {A : GaussianInt → ℂ} (hA1 : ∀ w, ‖A w‖ ≤ 1) (hA0 : A 0 = 0)
    (k : ℤ) (w : GaussianInt) : ‖A w * epsUnit w ^ k‖ ≤ 1 := by
  by_cases hw : w = 0
  · subst hw; simp [hA0]
  · rw [norm_mul, norm_zpow, epsUnit_norm hw, one_zpow, mul_one]
    exact hA1 w

private lemma twist_support {A : GaussianInt → ℂ} {P : GaussianInt → Prop}
    (hA : ∀ w, A w ≠ 0 → P w) (w : GaussianInt) (u : ℂ) (h : A w * u ≠ 0) : P w :=
  hA w (fun h0 => h (by rw [h0, zero_mul]))

/-! ## 1. The counting lemmas -/

/-- A finite set of Gaussian integers of norm `≤ M` has at most `25 M` elements (`M ≥ 1`). -/
private theorem card_gnorm_le : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℝ), 1 ≤ M → ∀ S : Finset GaussianInt,
    (∀ w ∈ S, (Work.FIPlan.gnorm w : ℝ) ≤ M) → ((S.card : ℝ) ≤ C * M) := by
  refine ⟨25, by norm_num, ?_⟩
  intro M hM S hS
  set K : ℕ := Nat.ceil (Real.sqrt M) with hK
  have hM0 : (0 : ℝ) < M := by linarith
  have hKceil : Real.sqrt M ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
  have habs : ∀ x : ℝ, x ^ 2 ≤ M → |x| ≤ (K : ℝ) := by
    intro x hx
    have h2 : |x| ≤ Real.sqrt M := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hx
    linarith
  have hsub : S ⊆ Work.FIPlan.gBox (K : ℤ) := by
    intro w hw
    rw [mem_gBox_iff, Finset.mem_Icc, Finset.mem_Icc]
    have h1 : (Work.FIPlan.gnorm w : ℝ) ≤ M := hS w hw
    have hsq := gnorm_eq_sq w
    have hre2 : ((w.re : ℤ) : ℝ) ^ 2 ≤ M := by nlinarith [sq_nonneg ((w.im : ℤ) : ℝ)]
    have him2 : ((w.im : ℤ) : ℝ) ^ 2 ≤ M := by nlinarith [sq_nonneg ((w.re : ℤ) : ℝ)]
    have hre := abs_le.mp (habs _ hre2)
    have him := abs_le.mp (habs _ him2)
    exact ⟨⟨by exact_mod_cast hre.1, by exact_mod_cast hre.2⟩,
           ⟨by exact_mod_cast him.1, by exact_mod_cast him.2⟩⟩
  have hcard_le : S.card ≤ (Work.FIPlan.gBox (K : ℤ)).card := Finset.card_le_card hsub
  have hgBox_card : (Work.FIPlan.gBox (K : ℤ)).card ≤ (2 * K + 1) * (2 * K + 1) := by
    unfold Work.FIPlan.gBox
    refine le_trans Finset.card_image_le ?_
    rw [Finset.product_eq_sprod, Finset.card_product]
    have hc : (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
      rw [Int.card_Icc]
      have h2 : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h2, Int.toNat_natCast]
    rw [hc]
  have hKle : (K : ℝ) ≤ Real.sqrt M + 1 := by
    have := Nat.ceil_lt_add_one (Real.sqrt_nonneg M)
    rw [hK]
    linarith
  have hsqrtM1 : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
  have h2K : (2 * (K : ℝ) + 1) ≤ 5 * Real.sqrt M := by nlinarith
  have hsq : (2 * (K : ℝ) + 1) ^ 2 ≤ 25 * M := by
    have h3 : (2 * (K : ℝ) + 1) ^ 2 ≤ (5 * Real.sqrt M) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2K 2
    have h4 : (5 * Real.sqrt M) ^ 2 = 25 * M := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hM0)]; norm_num
    linarith
  calc ((S.card : ℝ)) ≤ (((Work.FIPlan.gBox (K : ℤ)).card : ℕ) : ℝ) := by exact_mod_cast hcard_le
    _ ≤ (((2 * K + 1) * (2 * K + 1) : ℕ) : ℝ) := by exact_mod_cast hgBox_card
    _ = (2 * (K : ℝ) + 1) ^ 2 := by push_cast; ring
    _ ≤ 25 * M := hsq

/-- The failure of the room condition `|Re(wz)| ≥ |w||z|/R` puts `wz` into the thin strip
`|Re(wz)| R < |w||z|`, in the integral form used by the point count `hcard`. -/
private theorem strip_of_not_room (R : ℕ) (W z : GaussianInt) (h : ¬ epsRoomB R W z) :
    ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (Work.FIPlan.gnorm z) := by
  rw [epsRoomB] at h
  have hlt : (R : ℝ) * |(((W * z).re : ℤ) : ℝ)| < ‖W.toComplex‖ * ‖z.toComplex‖ :=
    not_le.mp h
  have hsq := pow_lt_pow_left₀ hlt
    (by positivity : (0 : ℝ) ≤ (R : ℝ) * |(((W * z).re : ℤ) : ℝ)|)
    (by norm_num : (2 : ℕ) ≠ 0)
  have hℝ : (((W * z).re : ℤ) : ℝ) ^ 2 * (R : ℝ) ^ 2
      < (Work.FIPlan.gnorm W : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
    calc (((W * z).re : ℤ) : ℝ) ^ 2 * (R : ℝ) ^ 2
        = ((R : ℝ) * |(((W * z).re : ℤ) : ℝ)|) ^ 2 := by rw [mul_pow, sq_abs]; ring
      _ < (‖W.toComplex‖ * ‖z.toComplex‖) ^ 2 := hsq
      _ = (Work.FIPlan.gnorm W : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
            rw [mul_pow, sq_norm_toComplex, sq_norm_toComplex]
  exact_mod_cast hℝ

/-- **The strip count.** For fixed `w ≠ 0` and `σ ≠ 0` the `z` of `gBox N'` with `|z|² ≤ N`
violating one of the two room conditions number at most `2 Ccard (√N' + N'/R)`. -/
private theorem bad_z_card_le {Ccard : ℝ}
    (hcard : ∀ (N' R : ℕ) (W : GaussianInt), 1 ≤ R → 1 ≤ N' → W ≠ 0 →
       ((((Work.FIPlan.gBox ((N' : ℤ))).filter (fun z => Work.FIPlan.gnorm z ≤ N' ∧
          ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (N' : ℤ))).card : ℝ))
        ≤ Ccard * (Real.sqrt (N' : ℝ) + (N' : ℝ) / (R : ℝ)))
    (hstrip : ∀ (R : ℕ) (W z : GaussianInt), ¬ epsRoomB R W z →
       ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (Work.FIPlan.gnorm z))
    {R N' : ℕ} (hR : 1 ≤ R) (hN' : 1 ≤ N') {N : ℝ} (hNN' : N ≤ (N' : ℝ))
    {w σ : GaussianInt} (hw : w ≠ 0) (hσw : σ * w ≠ 0) :
    ((epsBadZN N' N R w σ).card : ℝ) ≤ 2 * Ccard * (Real.sqrt (N' : ℝ) + (N' : ℝ) / (R : ℝ)) := by
  set S1 := (Work.FIPlan.gBox ((N' : ℤ))).filter (fun z => Work.FIPlan.gnorm z ≤ N' ∧
      ((w * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm w : ℤ) * (N' : ℤ)) with hS1
  set S2 := (Work.FIPlan.gBox ((N' : ℤ))).filter (fun z => Work.FIPlan.gnorm z ≤ N' ∧
      ((σ * w * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm (σ * w) : ℤ) * (N' : ℤ)) with hS2
  have hsub : epsBadZN N' N R w σ ⊆ S1 ∪ S2 := by
    intro z hz
    obtain ⟨hzbox, hzn, hzbad⟩ := Finset.mem_filter.mp hz
    have hzbad' : ¬ (epsRoomA R σ w z ∧ epsRoomB R w z) := hzbad
    have hzN' : Work.FIPlan.gnorm z ≤ N' := by exact_mod_cast (le_trans hzn hNN')
    rcases not_and_or.mp hzbad' with hA | hB
    · refine Finset.mem_union.mpr (Or.inr ?_)
      refine Finset.mem_filter.mpr ⟨hzbox, hzN', ?_⟩
      have hroom : ¬ epsRoomB R (σ * w) z :=
        fun hc => hA ((epsRoomA_iff_epsRoomB_shift R σ w z).mpr hc)
      have hst := hstrip R (σ * w) z hroom
      calc ((σ * w * z).re) ^ 2 * (R : ℤ) ^ 2
          < (Work.FIPlan.gnorm (σ * w) : ℤ) * (Work.FIPlan.gnorm z : ℤ) := hst
        _ ≤ (Work.FIPlan.gnorm (σ * w) : ℤ) * (N' : ℤ) := by
            exact_mod_cast Nat.mul_le_mul_left (Work.FIPlan.gnorm (σ * w)) hzN'
    · refine Finset.mem_union.mpr (Or.inl ?_)
      refine Finset.mem_filter.mpr ⟨hzbox, hzN', ?_⟩
      have hst := hstrip R w z hB
      calc ((w * z).re) ^ 2 * (R : ℤ) ^ 2
          < (Work.FIPlan.gnorm w : ℤ) * (Work.FIPlan.gnorm z : ℤ) := hst
        _ ≤ (Work.FIPlan.gnorm w : ℤ) * (N' : ℤ) := by
            exact_mod_cast Nat.mul_le_mul_left (Work.FIPlan.gnorm w) hzN'
  have h1 : (S1.card : ℝ) ≤ Ccard * (Real.sqrt (N' : ℝ) + (N' : ℝ) / (R : ℝ)) :=
    hcard N' R w hR hN' hw
  have h2 : (S2.card : ℝ) ≤ Ccard * (Real.sqrt (N' : ℝ) + (N' : ℝ) / (R : ℝ)) :=
    hcard N' R (σ * w) hR hN' hσw
  have h3 : ((epsBadZN N' N R w σ).card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := by
    have h4 : (epsBadZN N' N R w σ).card ≤ (S1 ∪ S2).card := Finset.card_le_card hsub
    have h5 := Finset.card_union_le S1 S2
    have h6 : ((epsBadZN N' N R w σ).card : ℝ) ≤ ((S1 ∪ S2).card : ℝ) := by exact_mod_cast h4
    have h7 : ((S1 ∪ S2).card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := by exact_mod_cast h5
    linarith
  linarith

/-- The number of *bad* live pairs is at most the number of live `w` (bounded by `hAcard`) times
the uniform per-`w` bound `Kz` on the bad `z`. -/
private theorem bad_pair_count_le {Cw M Kz N : ℝ} (hKz0 : 0 ≤ Kz)
    {Rw Rz : ℤ} {σ : GaussianInt} {R : ℕ} {A B : GaussianInt → ℂ}
    (hB : ∀ z, B z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N)
    (hAcard : ((((Work.FIPlan.gBox Rw).filter (fun w => A w ≠ 0)).card : ℝ)) ≤ Cw * M)
    (hKz : ∀ w : GaussianInt, A w ≠ 0 → ((epsBadZ Rz N R w σ).card : ℝ) ≤ Kz) :
    ((epsBadP Rw Rz σ R A B).card : ℝ) ≤ Cw * M * Kz := by
  set Wf : Finset GaussianInt := (Work.FIPlan.gBox Rw).filter (fun w => A w ≠ 0) with hWf
  have hsub : epsBadP Rw Rz σ R A B ⊆
      Wf.biUnion (fun w => (epsBadZ Rz N R w σ).image (fun z => (w, z))) := by
    intro p hp
    have hp1 : p ∈ epsLive Rw Rz A B := (Finset.mem_filter.mp hp).1
    have hbad : ¬ epsGood R σ p.1 p.2 := (Finset.mem_filter.mp hp).2
    have hp2 : p ∈ (Work.FIPlan.gBox Rw).product (Work.FIPlan.gBox Rz) :=
      (Finset.mem_filter.mp hp1).1
    have hsupp := (Finset.mem_filter.mp hp1).2
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp2
    have hzp' : p.2 ∈ epsBadZ Rz N R p.1 σ :=
      Finset.mem_filter.mpr ⟨hp2.2, hB p.2 hsupp.2.2, hbad⟩
    refine Finset.mem_biUnion.mpr ⟨p.1, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hp2.1, hsupp.2.1⟩
    · exact Finset.mem_image.mpr ⟨p.2, hzp', rfl⟩
  have hcard' : (epsBadP Rw Rz σ R A B).card ≤ ∑ w ∈ Wf, (epsBadZ Rz N R w σ).card := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans Finset.card_biUnion_le ?_
    refine Finset.sum_le_sum (fun w _ => ?_)
    exact le_of_eq (Finset.card_image_of_injOn
      (f := fun z => (w, z)) (fun a _ b _ hab => ((Prod.mk.injEq w a w b).mp hab).2))
  have hreal : ((epsBadP Rw Rz σ R A B).card : ℝ) ≤ (Wf.card : ℝ) * Kz := by
    calc ((epsBadP Rw Rz σ R A B).card : ℝ)
        ≤ ((∑ w ∈ Wf, (epsBadZ Rz N R w σ).card : ℕ) : ℝ) := by exact_mod_cast hcard'
      _ = ∑ w ∈ Wf, ((epsBadZ Rz N R w σ).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _w ∈ Wf, Kz := Finset.sum_le_sum (fun w hw => hKz w (Finset.mem_filter.mp hw).2)
      _ = (Wf.card : ℝ) * Kz := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ((epsBadP Rw Rz σ R A B).card : ℝ) ≤ (Wf.card : ℝ) * Kz := hreal
    _ ≤ (Cw * M) * Kz := mul_le_mul_of_nonneg_right hAcard hKz0
    _ = Cw * M * Kz := by ring

/-! ## 2. The two `Finset` identities -/

/-- The live-pair sum of the twisted summands is the coprimality-restricted `K`-form with the
coefficients twisted by `(w/|w|)^k`, `(z/|z|)^k`. -/
private theorem epsLive_sum_eq_KBilinStar (Rw Rz : ℤ) (A B : GaussianInt → ℂ) (k : ℤ) :
    (∑ p ∈ epsLive Rw Rz A B,
        A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) * (epsUnit p.1 ^ k * epsUnit p.2 ^ k))
      = Work.FIArea7.KBilinStar Rw Rz
          (fun w => A w * epsUnit w ^ k) (fun z => B z * epsUnit z ^ k) := by
  unfold epsLive Work.FIArea7.KBilinStar
  rw [Finset.sum_filter, Finset.product_eq_sprod, Finset.sum_product]
  refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun z _ => ?_))
  by_cases hcop : Work.FIPlan.GaussCoprime w z
  · by_cases hA : A w = 0
    · simp [hA]
    · by_cases hB : B z = 0
      · simp [hB]
      · have hA' : A w ≠ 0 := hA
        have hB' : B z ≠ 0 := hB
        rw [if_pos hcop, if_pos ⟨hcop, hA', hB'⟩]
        ring
  · simp [hcop]

/-- The `ε`-double sum splits into its good and bad part. -/
private theorem eps_key_split (Rw Rz : ℤ) (σ : GaussianInt) (R : ℕ) (A B : GaussianInt → ℂ) :
    (∑ p ∈ (Work.FIPlan.gBox Rw).product (Work.FIPlan.gBox Rz), epsKeySummand σ A B p)
      = (∑ p ∈ epsGoodP Rw Rz σ R A B, epsSummandP σ A B p)
        + (∑ p ∈ epsBadP Rw Rz σ R A B, epsSummandP σ A B p) := by
  have h1 : (∑ p ∈ (Work.FIPlan.gBox Rw).product (Work.FIPlan.gBox Rz),
        epsKeySummand σ A B p)
      = ∑ p ∈ ((Work.FIPlan.gBox Rw).product (Work.FIPlan.gBox Rz)).filter
          (fun p => Work.FIPlan.GaussCoprime p.1 p.2), epsSummandP σ A B p := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun p _ => by simp only [epsKeySummand])
  have h2 : (∑ p ∈ ((Work.FIPlan.gBox Rw).product (Work.FIPlan.gBox Rz)).filter
          (fun p => Work.FIPlan.GaussCoprime p.1 p.2), epsSummandP σ A B p)
      = ∑ p ∈ epsLive Rw Rz A B, epsSummandP σ A B p := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
    · intro p hp hpnot
      have h0 : A p.1 = 0 ∨ B p.2 = 0 := by
        by_contra h
        push_neg at h
        exact hpnot (Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2, h.1, h.2⟩)
      rcases h0 with h0 | h0
      · simp [epsSummandP, h0]
      · simp [epsSummandP, h0]
  have h3 : (∑ p ∈ epsLive Rw Rz A B, epsSummandP σ A B p)
      = (∑ p ∈ epsGoodP Rw Rz σ R A B, epsSummandP σ A B p)
        + (∑ p ∈ epsBadP Rw Rz σ R A B, epsSummandP σ A B p) := by
    simp only [epsGoodP, epsBadP]
    exact (Finset.sum_filter_add_sum_filter_not (s := epsLive Rw Rz A B)
      (p := fun p => epsGood R σ p.1 p.2) (f := fun p => epsSummandP σ A B p)).symm
  rw [h1, h2, h3]

/-! ## 3. The main theorem

Copy of `Work.FIArea7.P231.multEps_inner_bound` with the constant `C` hoisted outside the
quantifier over `σ` (the explicit constant produced by the proof, `1 + bound0/den`, does not
depend on `σ`). -/


/-! ## 0. The explicit constants of the `ε`-step -/

/-- The room parameter `R = ⌈√(MN)⌉ + 2` of the §23 argument. -/
def epsRoom (M N : ℝ) : ℕ := Nat.ceil (Real.sqrt (M * N)) + 2

lemma epsRoom_ge_two (M N : ℝ) : 2 ≤ epsRoom M N := by
  rw [epsRoom]
  omega

/-- `max 1 ⌈N⌉`. -/
def epsNprime (N : ℝ) : ℕ := max 1 (Nat.ceil N)

/-- The number of exceptional `z` per `w`. -/
def epsKz (Ccard M N : ℝ) : ℝ :=
  2 * Ccard * (Real.sqrt (epsNprime N) + (epsNprime N) / ((epsRoom M N : ℕ) : ℝ))

/-- The cost of the exceptional pairs. -/
def epsKbad (Cw M Ccard N : ℝ) : ℝ := Cw * M * epsKz Ccard M N

/-- The constant of the `ε`-step, with the logarithm of the room parameter already absorbed into
`log(MN+2)^4`. -/
def epsBound0 (Cw Cexp M Ccard N Bound : ℝ) : ℝ :=
  (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4
      * (Bound + epsKbad Cw M Ccard N)
    + epsKbad Cw M Ccard N

/-- The denominator of the `ε`-step, i.e. the shape of the final bound. -/
def epsDen (M N Bound : ℝ) : ℝ :=
  (Real.log (M * N + 2)) ^ 8 * (Bound + M * Real.sqrt N + Real.sqrt (M * N))

theorem epsStepUniformExplicit
    {M N : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N)
    {Bound Cexp Ccard Cw : ℝ} (hB : 0 ≤ Bound) (hCexp : 0 < Cexp) (hCcard : 0 < Ccard)
    (hCwpos : 0 < Cw)
    (hCw : ∀ (M' : ℝ), 1 ≤ M' → ∀ S : Finset GaussianInt,
      (∀ w ∈ S, (Work.FIPlan.gnorm w : ℝ) ≤ M') → ((S.card : ℝ) ≤ Cw * M'))
    (hK : ∀ (Rw Rz : ℤ) (A B : GaussianInt → ℂ),
       (∀ w, ‖A w‖ ≤ 1) → (∀ z, ‖B z‖ ≤ 1) →
       (∀ w, A w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
          (Work.FIPlan.gnorm w : ℝ) ≤ M) →
       (∀ z, B z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N) →
       ‖KBilinStar Rw Rz A B‖ ≤ Bound)
    (hexp : ∀ (σ : GaussianInt) (R : ℕ), 2 ≤ R → Work.FIPlan.IsPrimary σ →
       IsCoprime σ.re σ.im → σ.im ≠ 0 → ∃ ĉ : ℤ → ℂ,
       (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ Cexp * (Real.log (2 * R)) ^ 4) ∧
       ∀ w z : GaussianInt, Work.FIPlan.IsPrimary w → Work.FIPlan.IsPrimary z → w ≠ 0 → z ≠ 0 →
         ‖σ.toComplex‖ * ‖(w * z).toComplex‖ ≤ (R : ℝ) * |(((σ * (w * z)).re : ℤ) : ℝ)| →
         ‖w.toComplex‖ * ‖z.toComplex‖ ≤ (R : ℝ) * |(((w * z).re : ℤ) : ℝ)| →
         HasSum (fun k : ℤ => ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
                                   * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k))
           (2 * (MultEps σ (w * z) : ℂ) * (HilbertInf σ.re σ.im : ℂ)))
    (hcard : ∀ (N' R : ℕ) (W : GaussianInt), 1 ≤ R → 1 ≤ N' → W ≠ 0 →
       ((((Work.FIPlan.gBox ((N' : ℤ))).filter (fun z => Work.FIPlan.gnorm z ≤ N' ∧
          ((W * z).re) ^ 2 * (R : ℤ) ^ 2 < (Work.FIPlan.gnorm W : ℤ) * (N' : ℤ))).card : ℝ))
        ≤ Ccard * (Real.sqrt (N' : ℝ) + (N' : ℝ) / (R : ℝ)))
    :
    ∀ (σ : GaussianInt) (hσP : Work.FIPlan.IsPrimary σ)
      (hσc : IsCoprime σ.re σ.im) (hσi : σ.im ≠ 0)
      (Rw Rz : ℤ) (A B : GaussianInt → ℂ),
      (∀ w, ‖A w‖ ≤ 1) → (∀ z, ‖B z‖ ≤ 1) →
      (∀ w, A w ≠ 0 → Work.FIPlan.IsPrimary w ∧ IsCoprime w.re w.im ∧
         (Work.FIPlan.gnorm w : ℝ) ≤ M) →
      (∀ z, B z ≠ 0 → Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ N) →
      ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz, epsSummand σ A B w z‖
        ≤ Work.FIArea7.P231.epsDen M N Bound + Work.FIArea7.P231.epsBound0 Cw Cexp M Ccard N Bound := by
  classical
  set R : ℕ := Work.FIArea7.P231.epsRoom M N with hRdef
  have hR2 : 2 ≤ R := by rw [hRdef]; exact Work.FIArea7.P231.epsRoom_ge_two M N
  set N' : ℕ := max 1 (Nat.ceil N) with hN'def
  have hN'1 : 1 ≤ N' := le_max_left _ _
  have hNN' : N ≤ (N' : ℝ) := by
    have h1 : N ≤ (Nat.ceil N : ℝ) := Nat.le_ceil N
    have h2 : ((Nat.ceil N : ℕ) : ℝ) ≤ (N' : ℝ) := by
      rw [hN'def]; exact_mod_cast le_max_right 1 (Nat.ceil N)
    linarith
  set Kz : ℝ := 2 * Ccard * (Real.sqrt (N' : ℝ) + (N' : ℝ) / (R : ℝ)) with hKzdef
  have hKz0 : 0 ≤ Kz := by rw [hKzdef]; positivity
  set Kbad : ℝ := Cw * M * Kz with hKbaddef
  have hKbad0 : 0 ≤ Kbad := by
    rw [hKbaddef]
    exact mul_nonneg (by positivity) hKz0
  set bound0 : ℝ := (1 / 2) * Cexp * (Real.log (2 * R)) ^ 4 * (Bound + Kbad) + Kbad
    with hbound0def
  set den : ℝ := (Real.log (M * N + 2)) ^ 8 *
      (Bound + M * Real.sqrt N + Real.sqrt (M * N)) with hdendef
  have hbound0nn : 0 ≤ bound0 := by
    rw [hbound0def]
    have h1 : (0 : ℝ) ≤ (Real.log (2 * R)) ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ (1 / 2) * Cexp * (Real.log (2 * R)) ^ 4 * (Bound + Kbad) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hCexp)) h1) (by linarith)
    linarith
  have hden_pos : 0 < den := by
    rw [hdendef]
    have hlog : 0 < Real.log (M * N + 2) := Real.log_pos (by nlinarith)
    have h1 : 0 < (Real.log (M * N + 2)) ^ 8 := by positivity
    have h2 : 0 < Bound + M * Real.sqrt N + Real.sqrt (M * N) := by
      have h3 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
      have h4 : 0 < M * Real.sqrt N := by positivity
      have h5 : 0 ≤ Real.sqrt (M * N) := Real.sqrt_nonneg _
      linarith
    positivity
  intro σ hσP hσc hσi Rw Rz A B hA1 hB1 hAsup hBsup
  have hσne : σ ≠ 0 := by intro h; rw [h] at hσi; exact hσi rfl
  have hA0 : A 0 = 0 := by
    by_contra h; exact (isPrimary_ne_zero (hAsup 0 h).1) rfl
  have hB0 : B 0 = 0 := by
    by_contra h; exact (isPrimary_ne_zero (hBsup 0 h).1) rfl
  have hSprod : (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
        Work.FIArea7.epsSummand σ A B w z)
      = ∑ p ∈ (Work.FIPlan.gBox Rw).product (Work.FIPlan.gBox Rz),
          epsKeySummand σ A B p := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun z _ => ?_))
    simp only [Work.FIArea7.epsSummand, epsKeySummand, epsSummandP]
  set Sg : ℂ := ∑ p ∈ epsGoodP Rw Rz σ R A B, epsSummandP σ A B p with hSg
  set Sb : ℂ := ∑ p ∈ epsBadP Rw Rz σ R A B, epsSummandP σ A B p with hSb
  have hS : (∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
        Work.FIArea7.epsSummand σ A B w z) = Sg + Sb := by
    rw [hSprod, eps_key_split, ← hSg, ← hSb]
  -- the bad terms
  have hcard_le : ((epsBadP Rw Rz σ R A B).card : ℝ) ≤ Kbad := by
    have hB' : ∀ z, B z ≠ 0 → (Work.FIPlan.gnorm z : ℝ) ≤ N := fun z hz => (hBsup z hz).2
    have hAcard : ((((Work.FIPlan.gBox Rw).filter (fun w => A w ≠ 0)).card : ℝ)) ≤ Cw * M :=
      hCw M hM _ (fun w hw => (hAsup w (Finset.mem_filter.mp hw).2).2.2)
    have hKz' : ∀ w : GaussianInt, A w ≠ 0 → ((epsBadZ Rz N R w σ).card : ℝ) ≤ Kz := by
      intro w hwne
      have hw0 : w ≠ 0 := isPrimary_ne_zero (hAsup w hwne).1
      have hsub' : epsBadZ Rz N R w σ ⊆ epsBadZN N' N R w σ := by
        intro z hz
        obtain ⟨hzbox, hzn, hbad⟩ := Finset.mem_filter.mp hz
        have hzN' : Work.FIPlan.gnorm z ≤ N' := by exact_mod_cast (le_trans hzn hNN')
        exact Finset.mem_filter.mpr ⟨mem_gBox_of_gnorm_le hzN', hzn, hbad⟩
      have h1 : ((epsBadZ Rz N R w σ).card : ℝ) ≤ (epsBadZN N' N R w σ).card := by
        exact_mod_cast Finset.card_le_card hsub'
      have h2 := bad_z_card_le hcard strip_of_not_room (R := R) (N' := N')
        (by omega : 1 ≤ R) hN'1 hNN' hw0 (mul_ne_zero hσne hw0)
      rw [hKzdef]
      linarith
    have h3 := bad_pair_count_le hKz0 hB' hAcard hKz'
    rw [hKbaddef, hKzdef]
    exact h3
  have hSb_bound : ‖Sb‖ ≤ Kbad := by
    rw [hSb]
    have h1 : ∀ p ∈ epsBadP Rw Rz σ R A B, ‖epsSummandP σ A B p‖ ≤ 1 := by
      intro p hp
      have hsupp := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have hP1 := (hAsup p.1 hsupp.2.1).1
      have hP2 := (hBsup p.2 hsupp.2.2).1
      have hw0 := isPrimary_ne_zero hP1
      have hz0 := isPrimary_ne_zero hP2
      simp only [epsSummandP, norm_mul]
      have h2 := hA1 p.1
      have h3 := hB1 p.2
      have h4 := norm_multEps_le_one σ (p.1 * p.2)
      have h5 := Work.FIArea7.norm_JKSym_le_one (p.1 * p.2)
      have h6 : ‖A p.1‖ * ‖B p.2‖ ≤ 1 := mul_le_one₀ h2 (norm_nonneg _) h3
      have h7 : ‖((Work.FIArea7.MultEps σ (p.1 * p.2) : ℤ) : ℂ)‖ *
          ‖Work.FIArea7.JKSym (p.1 * p.2)‖ ≤ 1 := mul_le_one₀ h4 (norm_nonneg _) h5
      calc ‖A p.1‖ * ‖B p.2‖ * (‖((Work.FIArea7.MultEps σ (p.1 * p.2) : ℤ) : ℂ)‖ *
            ‖Work.FIArea7.JKSym (p.1 * p.2)‖)
          ≤ 1 * 1 := mul_le_mul h6 h7 (by positivity) (by norm_num)
        _ = 1 := by norm_num
    calc ‖∑ p ∈ epsBadP Rw Rz σ R A B, epsSummandP σ A B p‖
        ≤ ∑ p ∈ epsBadP Rw Rz σ R A B, ‖epsSummandP σ A B p‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ epsBadP Rw Rz σ R A B, (1 : ℝ) := Finset.sum_le_sum h1
      _ = ((epsBadP Rw Rz σ R A B).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ Kbad := hcard_le
  -- the good terms
  have hSg_bound : ‖Sg‖ ≤
      (1 / 2) * Cexp * (Real.log (2 * R)) ^ 4 * (Bound + Kbad) := by
    obtain ⟨ĉ, hcoeff, hHasSum⟩ := hexp σ R hR2 hσP hσc hσi
    set Hc : ℂ := ((Work.FIArea7.HilbertInf σ.re σ.im : ℤ) : ℂ) with hHcdef
    have hHcmul : Hc * Hc = 1 := hilbertInf_sq σ.re σ.im
    have hHcnorm : ‖Hc‖ = 1 := hilbertInf_norm σ.re σ.im
    have hHS : ∀ p ∈ epsGoodP Rw Rz σ R A B,
        HasSum (fun k : ℤ => ĉ k * (epsUnit p.1 ^ k * epsUnit p.2 ^ k))
          (2 * (Work.FIArea7.MultEps σ (p.1 * p.2) : ℂ) * Hc) := by
      intro p hp
      obtain ⟨hpL, hpG⟩ := Finset.mem_filter.mp hp
      have hsupp := (Finset.mem_filter.mp hpL).2
      have hP1 : Work.FIPlan.IsPrimary p.1 := (hAsup p.1 hsupp.2.1).1
      have hP2 : Work.FIPlan.IsPrimary p.2 := (hBsup p.2 hsupp.2.2).1
      exact hHasSum p.1 p.2 hP1 hP2 (isPrimary_ne_zero hP1) (isPrimary_ne_zero hP2)
        hpG.1 hpG.2
    have hHSm : ∀ p ∈ epsGoodP Rw Rz σ R A B,
        HasSum (fun k : ℤ => (A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2)) *
            (ĉ k * (epsUnit p.1 ^ k * epsUnit p.2 ^ k)))
          ((A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2)) *
            (2 * (Work.FIArea7.MultEps σ (p.1 * p.2) : ℂ) * Hc)) :=
      fun p hp => (hHS p hp).mul_left _
    have hsum := hasSum_sum hHSm
    have hcoeSum : Summable fun k : ℤ => ‖ĉ k‖ :=
      summable_of_sum_le (fun k => norm_nonneg _) hcoeff
    have hcoe_tsum : (∑' k : ℤ, ‖ĉ k‖) ≤ Cexp * (Real.log (2 * R)) ^ 4 :=
      Summable.tsum_le_of_sum_le hcoeSum hcoeff
    have hYb : ∀ k : ℤ, ‖∑ p ∈ epsGoodP Rw Rz σ R A B,
          A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
            (epsUnit p.1 ^ k * epsUnit p.2 ^ k)‖
        ≤ Bound + ((epsBadP Rw Rz σ R A B).card : ℝ) := by
      intro k
      have hKB : ‖Work.FIArea7.KBilinStar Rw Rz (fun w => A w * epsUnit w ^ k)
          (fun z => B z * epsUnit z ^ k)‖ ≤ Bound :=
        hK Rw Rz _ _ (fun w => twist_norm_le_one hA1 hA0 k w)
          (fun z => twist_norm_le_one hB1 hB0 k z)
          (fun w hw => twist_support hAsup w (epsUnit w ^ k) hw)
          (fun z hz => twist_support hBsup z (epsUnit z ^ k) hz)
      have hZb : ‖∑ p ∈ epsBadP Rw Rz σ R A B,
          A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
            (epsUnit p.1 ^ k * epsUnit p.2 ^ k)‖
          ≤ ((epsBadP Rw Rz σ R A B).card : ℝ) := by
        have h1 : ∀ p ∈ epsBadP Rw Rz σ R A B,
            ‖A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
              (epsUnit p.1 ^ k * epsUnit p.2 ^ k)‖ ≤ 1 := by
          intro p hp
          have hsupp := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          have hP1 := (hAsup p.1 hsupp.2.1).1
          have hP2 := (hBsup p.2 hsupp.2.2).1
          have hw0 := isPrimary_ne_zero hP1
          have hz0 := isPrimary_ne_zero hP2
          simp only [norm_mul, norm_zpow, epsUnit_norm hw0, epsUnit_norm hz0,
            one_zpow, mul_one]
          have h2 := hA1 p.1
          have h3 := hB1 p.2
          have h4 := Work.FIArea7.norm_JKSym_le_one (p.1 * p.2)
          have h5 : ‖A p.1‖ * ‖B p.2‖ ≤ 1 := mul_le_one₀ h2 (norm_nonneg _) h3
          calc ‖A p.1‖ * ‖B p.2‖ * ‖Work.FIArea7.JKSym (p.1 * p.2)‖
              ≤ 1 * 1 := mul_le_mul h5 h4 (norm_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        calc ‖∑ p ∈ epsBadP Rw Rz σ R A B,
              A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
                (epsUnit p.1 ^ k * epsUnit p.2 ^ k)‖
            ≤ ∑ p ∈ epsBadP Rw Rz σ R A B,
                ‖A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
                  (epsUnit p.1 ^ k * epsUnit p.2 ^ k)‖ := norm_sum_le _ _
          _ ≤ ∑ _p ∈ epsBadP Rw Rz σ R A B, (1 : ℝ) := Finset.sum_le_sum h1
          _ = ((epsBadP Rw Rz σ R A B).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hsplitL : (∑ p ∈ epsGoodP Rw Rz σ R A B,
            A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
              (epsUnit p.1 ^ k * epsUnit p.2 ^ k))
          + (∑ p ∈ epsBadP Rw Rz σ R A B,
            A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
              (epsUnit p.1 ^ k * epsUnit p.2 ^ k))
          = Work.FIArea7.KBilinStar Rw Rz (fun w => A w * epsUnit w ^ k)
              (fun z => B z * epsUnit z ^ k) := by
        rw [← epsLive_sum_eq_KBilinStar Rw Rz A B k]
        simp only [epsGoodP, epsBadP]
        exact Finset.sum_filter_add_sum_filter_not (s := epsLive Rw Rz A B)
          (p := fun p => epsGood R σ p.1 p.2)
          (f := fun p => A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
            (epsUnit p.1 ^ k * epsUnit p.2 ^ k))
      calc ‖∑ p ∈ epsGoodP Rw Rz σ R A B,
            A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
              (epsUnit p.1 ^ k * epsUnit p.2 ^ k)‖
          = ‖Work.FIArea7.KBilinStar Rw Rz (fun w => A w * epsUnit w ^ k)
              (fun z => B z * epsUnit z ^ k)
              - ∑ p ∈ epsBadP Rw Rz σ R A B,
                  A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
                    (epsUnit p.1 ^ k * epsUnit p.2 ^ k)‖ := by
            rw [← hsplitL, add_sub_cancel_right]
        _ ≤ ‖Work.FIArea7.KBilinStar Rw Rz (fun w => A w * epsUnit w ^ k)
              (fun z => B z * epsUnit z ^ k)‖
            + ‖∑ p ∈ epsBadP Rw Rz σ R A B,
                  A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
                    (epsUnit p.1 ^ k * epsUnit p.2 ^ k)‖ := norm_sub_le _ _
        _ ≤ Bound + ((epsBadP Rw Rz σ R A B).card : ℝ) := add_le_add hKB hZb
    set X : ℂ := ∑' k : ℤ, ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
        A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
          (epsUnit p.1 ^ k * epsUnit p.2 ^ k)) with hXdef
    have htsum_eq : X = (2 * Hc) * Sg := by
      have hLfun : (fun k : ℤ => ∑ p ∈ epsGoodP Rw Rz σ R A B,
            (A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2)) *
              (ĉ k * (epsUnit p.1 ^ k * epsUnit p.2 ^ k)))
          = (fun k : ℤ => ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
              A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
                (epsUnit p.1 ^ k * epsUnit p.2 ^ k))) := by
        funext k
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by ring)
      have hRval : (∑ p ∈ epsGoodP Rw Rz σ R A B,
            (A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2)) *
              (2 * (Work.FIArea7.MultEps σ (p.1 * p.2) : ℂ) * Hc))
          = (2 * Hc) * Sg := by
        rw [hSg, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun p _ => by simp only [epsSummandP]; ring)
      rw [hXdef, ← hLfun, hsum.tsum_eq, hRval]
    have hBc0 : 0 ≤ Bound + ((epsBadP Rw Rz σ R A B).card : ℝ) :=
      add_nonneg hB (Nat.cast_nonneg _)
    have hsumm1 : Summable fun k : ℤ =>
        ‖ĉ k‖ * (Bound + ((epsBadP Rw Rz σ R A B).card : ℝ)) := hcoeSum.mul_right _
    have hsumm_raw : Summable fun k : ℤ => ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
          A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
            (epsUnit p.1 ^ k * epsUnit p.2 ^ k)) :=
      Summable.of_norm_bounded
        (f := fun k : ℤ => ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
          A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
            (epsUnit p.1 ^ k * epsUnit p.2 ^ k))) hsumm1 (fun k => by
        change ‖ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
          A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
            (epsUnit p.1 ^ k * epsUnit p.2 ^ k))‖
          ≤ ‖ĉ k‖ * (Bound + ((epsBadP Rw Rz σ R A B).card : ℝ))
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hYb k) (norm_nonneg _))
    have hsumm2 : Summable fun k : ℤ => ‖ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
          A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
            (epsUnit p.1 ^ k * epsUnit p.2 ^ k))‖ := hsumm_raw.norm
    have hXbound : ‖X‖ ≤ (Cexp * (Real.log (2 * R)) ^ 4) *
        (Bound + ((epsBadP Rw Rz σ R A B).card : ℝ)) := by
      calc ‖X‖ = ‖∑' k : ℤ, ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
              A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
                (epsUnit p.1 ^ k * epsUnit p.2 ^ k))‖ := by rw [hXdef]
        _ ≤ ∑' k : ℤ, ‖ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
              A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
                (epsUnit p.1 ^ k * epsUnit p.2 ^ k))‖ := norm_tsum_le_tsum_norm hsumm2
        _ ≤ ∑' k : ℤ, ‖ĉ k‖ * (Bound + ((epsBadP Rw Rz σ R A B).card : ℝ)) :=
            Summable.tsum_le_tsum (fun k => by
              change ‖ĉ k * (∑ p ∈ epsGoodP Rw Rz σ R A B,
                A p.1 * B p.2 * Work.FIArea7.JKSym (p.1 * p.2) *
                  (epsUnit p.1 ^ k * epsUnit p.2 ^ k))‖
                ≤ ‖ĉ k‖ * (Bound + ((epsBadP Rw Rz σ R A B).card : ℝ))
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hYb k) (norm_nonneg _)) hsumm2 hsumm1
        _ = (∑' k : ℤ, ‖ĉ k‖) * (Bound + ((epsBadP Rw Rz σ R A B).card : ℝ)) :=
            tsum_mul_right
        _ ≤ (Cexp * (Real.log (2 * R)) ^ 4) *
              (Bound + ((epsBadP Rw Rz σ R A B).card : ℝ)) :=
            mul_le_mul_of_nonneg_right hcoe_tsum hBc0
    have hSgeq : Sg = (Hc / 2) * X := by
      have h : (Hc / 2) * X = Sg := by
        rw [htsum_eq]
        have h2 : (Hc / 2) * ((2 * Hc) * Sg) = (Hc * Hc) * Sg := by ring
        rw [h2, hHcmul, one_mul]
      exact h.symm
    calc ‖Sg‖ = ‖(Hc / 2) * X‖ := by rw [hSgeq]
      _ = (1 / 2) * ‖X‖ := by
          rw [norm_mul]
          have h2 : ‖Hc / 2‖ = 1 / 2 := by rw [norm_div, hHcnorm]; norm_num
          rw [h2]
      _ ≤ (1 / 2) * ((Cexp * (Real.log (2 * R)) ^ 4) *
            (Bound + ((epsBadP Rw Rz σ R A B).card : ℝ))) :=
          mul_le_mul_of_nonneg_left hXbound (by norm_num)
      _ ≤ (1 / 2) * ((Cexp * (Real.log (2 * R)) ^ 4) * (Bound + Kbad)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact add_le_add le_rfl hcard_le
      _ = (1 / 2) * Cexp * (Real.log (2 * R)) ^ 4 * (Bound + Kbad) := by ring
  have hS_goal : ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
        Work.FIArea7.epsSummand σ A B w z‖ ≤ bound0 := by
    rw [hS]
    calc ‖Sg + Sb‖ ≤ ‖Sg‖ + ‖Sb‖ := norm_add_le _ _
      _ ≤ (1 / 2) * Cexp * (Real.log (2 * R)) ^ 4 * (Bound + Kbad) + Kbad :=
          add_le_add hSg_bound hSb_bound
      _ = bound0 := by rw [hbound0def]
  have hb0 : bound0 ≤ Work.FIArea7.P231.epsBound0 Cw Cexp M Ccard N Bound := by
    have hlogR : Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))
        ≤ (1 + Real.log 4) * Real.log (M * N + 2) := by
      have h := Work.FIArea7.P231M.log_ceil_le (M := M) (N := N) hM hN
      simpa [Work.FIArea7.P231.epsRoom] using h
    have hlogR0 : (0 : ℝ) ≤ Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ)) := by
      have h1 : (1 : ℝ) ≤ 2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ) := by
        have h2 : (2 : ℝ) ≤ ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ) := by
          exact_mod_cast Work.FIArea7.P231.epsRoom_ge_two M N
        linarith
      exact Real.log_nonneg h1
    have hlog4 : (Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4
        ≤ (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 := by
      calc (Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4
          ≤ ((1 + Real.log 4) * Real.log (M * N + 2)) ^ 4 := pow_le_pow_left₀ hlogR0 hlogR 4
        _ = (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 := mul_pow _ _ 4
    have hcoef : (1 / 2) * Cexp * (Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4
        ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 := by
      have h := mul_le_mul_of_nonneg_left hlog4 (by positivity : (0:ℝ) ≤ (1/2) * Cexp)
      calc (1 / 2) * Cexp * (Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4
          = (1 / 2) * Cexp * ((Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4) := by ring
        _ ≤ (1 / 2) * Cexp * ((1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4) := h
        _ = (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 := by ring
    have hKbad0 : 0 ≤ Kbad := le_of_lt (by
      rw [hKbaddef, hKzdef]; positivity)
    have harg : 0 ≤ Bound + Kbad := by linarith
    have h1 : (1 / 2) * Cexp * (Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4
          * (Bound + Kbad) + Kbad
        ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 * (Bound + Kbad)
          + Kbad := by
      have h2 : (1 / 2) * Cexp * (Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4
            * (Bound + Kbad)
          ≤ (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 * (Bound + Kbad) := by
        have h3 : (1 / 2) * Cexp * (Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4
            * (Bound + Kbad)
            = ((1 / 2) * Cexp * (Real.log (2 * ((Work.FIArea7.P231.epsRoom M N : ℕ) : ℝ))) ^ 4)
              * (Bound + Kbad) := by ring
        have h4 : (1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4 * (Bound + Kbad)
            = ((1 / 2) * Cexp * (1 + Real.log 4) ^ 4 * (Real.log (M * N + 2)) ^ 4)
              * (Bound + Kbad) := by ring
        rw [h3, h4]
        exact mul_le_mul_of_nonneg_right hcoef harg
      linarith [h2]
    rw [hbound0def, Work.FIArea7.P231.epsBound0]
    exact h1
  have hden_nonneg : 0 ≤ Work.FIArea7.P231.epsDen M N Bound := by
    rw [Work.FIArea7.P231.epsDen]
    have h2 : (0 : ℝ) ≤ Bound + M * Real.sqrt N + Real.sqrt (M * N) := by
      have h3 : (0 : ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
      have h4 : (0 : ℝ) ≤ M * Real.sqrt N := by positivity
      have h5 : (0 : ℝ) ≤ Real.sqrt (M * N) := Real.sqrt_nonneg _
      linarith
    positivity
  calc ‖∑ w ∈ Work.FIPlan.gBox Rw, ∑ z ∈ Work.FIPlan.gBox Rz,
        Work.FIArea7.epsSummand σ A B w z‖
      ≤ bound0 := hS_goal
    _ ≤ Work.FIArea7.P231.epsBound0 Cw Cexp M Ccard N Bound := hb0
    _ ≤ Work.FIArea7.P231.epsDen M N Bound + Work.FIArea7.P231.epsBound0 Cw Cexp M Ccard N Bound :=
        le_add_of_nonneg_left hden_nonneg

end

end Work.FIArea7.P231
