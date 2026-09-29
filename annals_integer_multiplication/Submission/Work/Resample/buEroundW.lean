import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.buErow
import Submission.Work.ConvR.basic
import Submission.Work.Resample.egWSumm
import Submission.Work.Resample.egWtailNorm
import Submission.Work.Resample.egHsum
import Submission.Work.Resample.buWeightErr
import Submission.Work.Resample.buTdivKey
import Submission.Work.Resample.egMWtArith

set_option maxHeartbeats 1000000

namespace Work.Resample

open HvdH

/-! ## Helpers -/

lemma abs_le_of_natAbs_le {h : ℤ} {m : ℕ} (hh : h.natAbs ≤ m) : |h| ≤ (m : ℤ) := by
  rw [← Int.natCast_natAbs (n := h)]
  exact_mod_cast hh

lemma natAbs_le_of_abs_le {h : ℤ} {m : ℕ} (hh : |h| ≤ (m : ℤ)) : h.natAbs ≤ m := by
  have h2 : ((h.natAbs : ℕ) : ℤ) ≤ ((m : ℕ) : ℤ) := by rwa [Int.natCast_natAbs]
  exact_mod_cast h2

lemma natAbs_le_of_bounds {h : ℤ} {m : ℕ} (h1 : -((m : ℕ) : ℤ) ≤ h) (h2 : h ≤ ((m : ℕ) : ℤ)) :
    h.natAbs ≤ m :=
  natAbs_le_of_abs_le (abs_le.mpr ⟨h1, h2⟩)

lemma egHset_natAbs_le {m : ℕ} {h : ℤ} (hh : h ∈ egHset m) : h.natAbs ≤ m := by
  have hmem : h ∈ Finset.Icc (-((m : ℕ) : ℤ)) ((m : ℕ) : ℤ) := (Finset.mem_erase.mp hh).2
  exact natAbs_le_of_bounds (Finset.mem_Icc.mp hmem).1 (Finset.mem_Icc.mp hmem).2

lemma egHset_not_mem {m : ℕ} {h : ℤ} (hh : h ∉ egHset m) (h0 : h ≠ 0) : m < h.natAbs := by
  by_contra hcon
  simp only [not_lt] at hcon
  apply hh
  simp only [egHset, Finset.mem_erase, Finset.mem_Icc]
  exact ⟨h0, abs_le.mp (abs_le_of_natAbs_le hcon)⟩

/-- The converse of `Work.ConvR.norm_fxC_le_one`. -/
lemma inDisc_of_norm_fxC_le_one (p : ℕ) {z : ℤ × ℤ} (h : ‖HvdH.fxC p z‖ ≤ 1) :
    HvdH.inDisc p z := by
  have h1 : Complex.normSq ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) =
      (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2 := by
    simp [Complex.normSq_apply]; ring
  have h2 : Complex.normSq ((2 : ℂ) ^ p) = (4 : ℝ) ^ p := by
    rw [map_pow]
    have hh : Complex.normSq (2 : ℂ) = 4 := by norm_num
    rw [hh]
  have hsq : ‖HvdH.fxC p z‖ ^ 2 = ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / (4 : ℝ) ^ p := by
    rw [Complex.sq_norm,
      show HvdH.fxC p z = ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) * ((2 : ℂ) ^ p)⁻¹ from by
        rw [HvdH.fxC]; ring,
      map_mul, map_inv₀, h1, h2]
    ring
  have hs : ‖HvdH.fxC p z‖ ^ 2 ≤ 1 := by nlinarith [h, norm_nonneg (HvdH.fxC p z)]
  have h4 : (0 : ℝ) < (4 : ℝ) ^ p := by positivity
  have hle : ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤ (4 : ℝ) ^ p := by
    calc ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2)
        = ‖HvdH.fxC p z‖ ^ 2 * (4 : ℝ) ^ p := by
          rw [hsq]; field_simp
      _ ≤ 1 * (4 : ℝ) ^ p := mul_le_mul_of_nonneg_right hs h4.le
      _ = (4 : ℝ) ^ p := one_mul _
  have hcast : ((z.1 ^ 2 + z.2 ^ 2 : ℤ) : ℝ) ≤ (((4 : ℤ) ^ p) : ℝ) := by
    push_cast
    linarith [hle]
  exact_mod_cast hcast

/-! ## Local vocabulary -/

/-- The family `h ↦ egW(ℓ,h)·u((ℓ+h) mod s)` summed by one round of `Ẽ`. -/
noncomputable def buFam (s t α : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) (h : ℤ) : ℂ :=
  ((egW s t α (ℓ : ℤ) h : ℝ) : ℂ) * u (egIdx s hs ((ℓ : ℤ) + h))

/-- The defining equation of `buFam`, as a statement about the whole family. -/
lemma buFam_apply (s t α : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) :
    buFam s t α hs ℓ u
      = fun h => ((egW s t α (ℓ : ℤ) h : ℝ) : ℂ) * u (egIdx s hs ((ℓ : ℤ) + h)) := rfl

/-- The same family, killed at `h = 0`. -/
noncomputable def buFam0 (s t α : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) (h : ℤ) : ℂ :=
  if h = 0 then 0 else buFam s t α hs ℓ u h

/-- The discarded-tail family. -/
noncomputable def buTailF (s t α : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) (m : ℕ) (h : ℤ) : ℂ :=
  if m < h.natAbs then buFam s t α hs ℓ u h else 0

/-- The kept-window sum. -/
noncomputable def buSH (p α s t : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) : ℂ :=
  ∑ h ∈ egHset (egM p α), buFam s t α hs ℓ u h

/-- The discarded-tail sum. -/
noncomputable def buTL (p α s t : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) : ℂ :=
  ∑' h : ℤ, buTailF s t α hs ℓ u (egM p α) h

/-- The tabulated-weight sum. -/
noncomputable def buWtSum (p α s t : ℕ) (Wt : ℤ → ℤ → ℤ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) : ℂ :=
  ∑ h ∈ egHset (egM p α), (((Wt (ℓ : ℤ) h : ℝ) / (2 : ℝ) ^ p : ℝ) : ℂ)
    * u (egIdx s hs ((ℓ : ℤ) + h))

/-- The weight-rounding error sum. -/
noncomputable def buWErr (p α s t : ℕ) (Wt : ℤ → ℤ → ℤ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) : ℂ :=
  ∑ h ∈ egHset (egM p α),
    ((((Wt (ℓ : ℤ) h : ℝ) / (2 : ℝ) ^ p - egW s t α (ℓ : ℤ) h : ℝ)) : ℂ)
      * u (egIdx s hs ((ℓ : ℤ) + h))

/-- The row of `E` splits into the kept window plus the discarded tail. -/
lemma row_split (s t α p : ℕ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ)
    (hrowℓ : ((Emat s t α).mulVec u) ℓ = ∑' h : ℤ, buFam0 s t α hs ℓ u h)
    (hsumm : Summable (buFam s t α hs ℓ u)) :
    ((Emat s t α).mulVec u) ℓ = buSH p α s t hs ℓ u + buTL p α s t hs ℓ u := by
  rw [buSH, buTL]
  have hFsumm : Summable (buFam0 s t α hs ℓ u) :=
    Summable.of_norm_bounded hsumm.norm (fun h => by
      simp only [buFam0]; split_ifs with h0
      · simp
      · exact le_rfl)
  rw [hrowℓ, egHsum (egM p α) hFsumm]
  congr 1
  · refine Finset.sum_congr rfl fun h hh => ?_
    rw [buFam0, if_neg (Finset.ne_of_mem_erase hh)]
  · refine tsum_congr fun h => ?_
    rw [buTailF]
    by_cases hH : h ∈ egHset (egM p α)
    · rw [if_pos hH, if_neg (not_lt.mpr (egHset_natAbs_le hH))]
    · rw [if_neg hH]
      by_cases h0 : h = 0
      · rw [h0, buFam0, if_pos rfl]
        simp
      · rw [buFam0, if_neg h0, if_pos (egHset_not_mem hH h0)]

/-- Splitting the tabulated-weight sum into the rounding error and the true weights. -/
lemma wtSum_split (p α s t : ℕ) (Wt : ℤ → ℤ → ℤ) (hs : 0 < s) (ℓ : Fin s) (u : Fin s → ℂ) :
    buWtSum p α s t Wt hs ℓ u = buWErr p α s t Wt hs ℓ u + buSH p α s t hs ℓ u := by
  rw [buWtSum, buWErr, buSH, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [buFam]
  push_cast
  ring

/-- The total round-off identity for one round of `Ẽ` with tabulated weights. -/
lemma round_identity (p α s t : ℕ) (hs0 : 0 < s) (Wt : ℤ → ℤ → ℤ) (ℓ : Fin s)
    (v : Fin s → ℤ × ℤ) (y : Fin s → ℂ) (ρ : ℂ) (u : Fin s → ℂ)
    (hρeq : HvdH.fxC p (buRound Wt p α s t hs0 v ℓ) = buWtSum p α s t Wt hs0 ℓ u - ρ)
    (hrowl : ((Emat s t α).mulVec u) ℓ = buSH p α s t hs0 ℓ u + buTL p α s t hs0 ℓ u) :
    HvdH.fxC p (buRound Wt p α s t hs0 v ℓ) - (Emat s t α).mulVec y ℓ
      = buWErr p α s t Wt hs0 ℓ u + (Emat s t α).mulVec (u - y) ℓ
        - buTL p α s t hs0 ℓ u - ρ := by
  have hsub : (Emat s t α).mulVec (u - y) ℓ
      = (Emat s t α).mulVec u ℓ - (Emat s t α).mulVec y ℓ := by
    rw [Matrix.mulVec_sub]; rfl
  have hSHdecomp : buSH p α s t hs0 ℓ u
      = (Emat s t α).mulVec u ℓ - buTL p α s t hs0 ℓ u := by
    rw [hrowl]; ring
  rw [hsub, hρeq, wtSum_split, hSHdecomp]
  ring

/-- One step of the truncated Gaussian convolution with an ARBITRARY integer weight table `Wt` whose
entries are within `δ·2^{-p}` of the true weights `egW s t α ℓ h`, with `0 ≤ δ ≤ 4` (the bound on `δ`
is needed for the disc invariant; `buWt` is the computable table, with `δ = 4`).

NOTE (for the prover): `buRound` is `egERound` with `egWi` replaced by `Wt`. Write
`fxC p (buRound Wt x ℓ) = Σ_{h∈H} (Wt(ℓ,h)/2^p)·fxC p (x(ℓ+h)) - ρ` with `‖ρ‖ ≤ √2·2^{-p}`, and
`(E y) ℓ = Σ_{h≠0} egW(ℓ,h)·y(ℓ+h)` (`hrow`). Split the difference into four terms (weight rounding
`≤ 2m·δ·2^{-p}`; propagation `Σ_{h∈H} egW·(ξ-y)`, bounded with `‖E u‖ ≤ ‖u‖/2` from `ResMath1DProp`
plus the discarded tail; the discarded tail `≤ 3·2^{-p}` from `htail`; the `tdiv` remainder).
`inDisc` needs `|Σ_{h∈H}(Wt/2^p)ξ| ≤ |(E ξ)ℓ| + tail + 2mδ ≤ 1/2 + 8m·2^{-p} ≤ 1`. -/
theorem buEroundW (RM : HvdH.ResMath1DProp) (p α s t : ℕ) (hs : 2 ≤ s) (hs0 : 0 < s) (hst : s < t)
    (hcop : Nat.Coprime s t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1)
    (Wt : ℤ → ℤ → ℤ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 4)
    (hWt : ∀ (ℓ h : ℤ), h ∈ Work.Resample.egHset (Work.Resample.egM p α) →
      |((Wt ℓ h : ℝ) / (2 : ℝ) ^ p - Work.Resample.egW s t α ℓ h)| ≤ δ / (2 : ℝ) ^ p)
    (hrow : ∀ (ℓ : Fin s) (x : Fin s → ℂ),
      ((HvdH.Emat s t α).mulVec x) ℓ = ∑' h : ℤ, (if h = 0 then 0 else
          ((Work.Resample.egW s t α (ℓ : ℤ) h : ℝ) : ℂ) * x (Work.Resample.egIdx s hs0 ((ℓ : ℤ) + h))))
    (htail : ∀ ℓ : Fin s,
      ∑' h : ℤ, (if Work.Resample.egM p α < h.natAbs then |Work.Resample.egW s t α (ℓ : ℤ) h| else 0)
        ≤ 3 / (2 : ℝ) ^ p)
    (x : Fin s → ℤ × ℤ) (hx : ∀ ℓ, HvdH.inDisc p (x ℓ))
    (y : Fin s → ℂ) (hy : ∀ ℓ, ‖y ℓ‖ ≤ 1) (e : ℝ)
    (he : ∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (x ℓ) - y ℓ‖ ≤ e) :
    (∀ ℓ, HvdH.inDisc p (Work.Resample.buRound Wt p α s t hs0 x ℓ)) ∧
    (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (Work.Resample.buRound Wt p α s t hs0 x ℓ)
        - (HvdH.Emat s t α).mulVec y ℓ‖
        ≤ (2 * δ + 1) * (Work.Resample.egM p α) + 12 + (1 / 2) * e) := by
  have hα0 : 0 < α := by omega
  have hEnorm : ∀ u : Fin s → ℂ, ‖(HvdH.Emat s t α).mulVec u‖ ≤ 21 / 50 * ‖u‖ :=
    (RM s t α p hs hst hcop hα hαp hθ).2.2.1
  have he0 : 0 ≤ e := by
    have h := he ⟨0, hs0⟩
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ p * ‖HvdH.fxC p (x ⟨0, hs0⟩) - y ⟨0, hs0⟩‖ := by positivity
    linarith
  have hp2 : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hm0 : (0 : ℝ) ≤ (egM p α : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (egM p α : ℝ) := by
    have : 1 ≤ egM p α := by
      rw [egM]
      exact Nat.one_le_iff_ne_zero.mpr (by simp)
    exact_mod_cast this
  have hsqrt2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hdiv : ∀ a : ℝ, (2 : ℝ) ^ p * (a / (2 : ℝ) ^ p) = a := by
    intro a
    have hne : (2 : ℝ) ^ p ≠ 0 := ne_of_gt hp2
    field_simp
  have harith : (8 * (egM p α : ℝ) + 3 + Real.sqrt 2) / (2 : ℝ) ^ p ≤ 29 / 50 := by
    have h := egMWtArith p α hp hα
    rw [div_le_iff₀ hp2]
    nlinarith [h, hsqrt2, Real.sqrt_nonneg 2]
  have perℓ : ∀ ℓ : Fin s,
      (HvdH.inDisc p (buRound Wt p α s t hs0 x ℓ)) ∧
      ((2 : ℝ) ^ p * ‖HvdH.fxC p (buRound Wt p α s t hs0 x ℓ)
        - (HvdH.Emat s t α).mulVec y ℓ‖
        ≤ (2 * δ + 1) * (egM p α) + 12 + (1 / 2) * e) := by
    intro ℓ
    set u : Fin s → ℂ := fun j => HvdH.fxC p (x j) with hu
    have hu1 : ∀ j, ‖u j‖ ≤ 1 := fun j => by
      rw [hu]
      exact Work.ConvR.norm_fxC_le_one (hx j)
    have hsumm : Summable (buFam s t α hs0 ℓ u) := by
      rw [buFam_apply]
      exact (egWSumm s t α hs0 hst hα0 ℓ u).1
    obtain ⟨ρ, hρbound, hρeq0⟩ := buTdivKey Wt p α s t hs0 x ℓ
    have hρeq : HvdH.fxC p (buRound Wt p α s t hs0 x ℓ) = buWtSum p α s t Wt hs0 ℓ u - ρ := by
      rw [buWtSum]
      simpa only [hu] using hρeq0
    have hrowl : ((HvdH.Emat s t α).mulVec u) ℓ = buSH p α s t hs0 ℓ u + buTL p α s t hs0 ℓ u := by
      refine row_split s t α p hs0 ℓ u ?_ hsumm
      simpa only [buFam0, buFam] using hrow ℓ u
    have hid := round_identity p α s t hs0 Wt ℓ x y ρ u hρeq hrowl
    have hS1 : ‖buWErr p α s t Wt hs0 ℓ u‖ ≤ 2 * (egM p α : ℝ) * δ / (2 : ℝ) ^ p := by
      rw [buWErr]
      exact buWeightErr p (egM p α) s t α Wt δ ℓ hs0 u hδ0 (fun h hh => hWt (ℓ : ℤ) h hh) hu1
    have hprop : (2 : ℝ) ^ p * ‖(HvdH.Emat s t α).mulVec (u - y) ℓ‖ ≤ e / 2 := by
      have h1 : ‖(HvdH.Emat s t α).mulVec (u - y) ℓ‖ ≤ ‖(HvdH.Emat s t α).mulVec (u - y)‖ :=
        norm_le_pi_norm _ ℓ
      have h2 : ‖(HvdH.Emat s t α).mulVec (u - y)‖ ≤ 21 / 50 * ‖u - y‖ := hEnorm (u - y)
      have h3 : ∀ j, ‖(u - y) j‖ ≤ e / (2 : ℝ) ^ p := by
        intro j
        have huj : u j = HvdH.fxC p (x j) := by rw [hu]
        rw [Pi.sub_apply, huj, le_div_iff₀ hp2, mul_comm]
        exact he j
      have h4 : ‖u - y‖ ≤ e / (2 : ℝ) ^ p := by
        rw [pi_norm_le_iff_of_nonneg (by positivity)]
        exact h3
      have h5 : (2 : ℝ) ^ p * ‖(HvdH.Emat s t α).mulVec (u - y) ℓ‖
          ≤ (2 : ℝ) ^ p * (21 / 50 * (e / (2 : ℝ) ^ p)) := by
        apply mul_le_mul_of_nonneg_left _ hp2.le
        exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left h4 (by norm_num)))
      have h6 : (2 : ℝ) ^ p * (21 / 50 * (e / (2 : ℝ) ^ p)) = (21 / 50) * e := by
        have hne : (2 : ℝ) ^ p ≠ 0 := ne_of_gt hp2
        field_simp
      rw [h6] at h5
      linarith [h5, he0]
    have hgsumm : Summable (fun h : ℤ => if egM p α < h.natAbs then |egW s t α (ℓ : ℤ) h| else 0) := by
      refine Summable.of_nonneg_of_le (fun h => ?_) (fun h => ?_) (egWSumm s t α hs0 hst hα0 ℓ u).2
      · by_cases hh : egM p α < h.natAbs <;> simp [hh]
      · by_cases hh : egM p α < h.natAbs <;> simp [hh]
    have hTL : ‖buTL p α s t hs0 ℓ u‖ ≤ 3 / (2 : ℝ) ^ p := by
      rw [buTL]
      exact egWtailNorm s t α p hs0 (egM p α) ℓ u hgsumm (htail ℓ) hu1
    have hSH : ‖buSH p α s t hs0 ℓ u‖ ≤ 21 / 50 + 3 / (2 : ℝ) ^ p := by
      have hEu : ‖(HvdH.Emat s t α).mulVec u ℓ‖ ≤ 21 / 50 := by
        have h0 : ‖(HvdH.Emat s t α).mulVec u ℓ‖ ≤ ‖(HvdH.Emat s t α).mulVec u‖ :=
          norm_le_pi_norm _ ℓ
        have h1 : ‖(HvdH.Emat s t α).mulVec u‖ ≤ 21 / 50 * ‖u‖ := hEnorm u
        have h2 : ‖u‖ ≤ 1 := by
          rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
          exact hu1
        have h3 : 21 / 50 * ‖u‖ ≤ 21 / 50 := by linarith [h2]
        linarith [h0, h1, h3]
      have hdecomp : buSH p α s t hs0 ℓ u
          = (HvdH.Emat s t α).mulVec u ℓ - buTL p α s t hs0 ℓ u := by
        rw [hrowl]
        ring
      rw [hdecomp]
      calc ‖(HvdH.Emat s t α).mulVec u ℓ - buTL p α s t hs0 ℓ u‖
          ≤ ‖(HvdH.Emat s t α).mulVec u ℓ‖ + ‖buTL p α s t hs0 ℓ u‖ := norm_sub_le _ _
        _ ≤ 21 / 50 + 3 / (2 : ℝ) ^ p := by linarith [hEu, hTL]
    constructor
    · have hρn : ‖ρ‖ ≤ Real.sqrt 2 / (2 : ℝ) ^ p := by
        rw [le_div_iff₀ hp2]
        linarith [hρbound]
      have hid2 : HvdH.fxC p (buRound Wt p α s t hs0 x ℓ)
          = buWErr p α s t Wt hs0 ℓ u + buSH p α s t hs0 ℓ u - ρ := by
        rw [hρeq, wtSum_split]
      have hchain : ‖buWErr p α s t Wt hs0 ℓ u + buSH p α s t hs0 ℓ u - ρ‖
          ≤ 2 * (egM p α : ℝ) * δ / (2 : ℝ) ^ p + (21 / 50 + 3 / (2 : ℝ) ^ p)
            + Real.sqrt 2 / (2 : ℝ) ^ p := by
        have h1 := norm_sub_le (buWErr p α s t Wt hs0 ℓ u + buSH p α s t hs0 ℓ u) ρ
        have h2 := norm_add_le (buWErr p α s t Wt hs0 ℓ u) (buSH p α s t hs0 ℓ u)
        linarith [h1, h2, hS1, hSH, hρn]
      have hstep : 2 * (egM p α : ℝ) * δ / (2 : ℝ) ^ p ≤ 8 * (egM p α : ℝ) / (2 : ℝ) ^ p := by
        apply div_le_div_of_nonneg_right _ hp2.le
        nlinarith [hm0, hδ0, hδ]
      have hsum : 8 * (egM p α : ℝ) / (2 : ℝ) ^ p + 3 / (2 : ℝ) ^ p + Real.sqrt 2 / (2 : ℝ) ^ p
          = (8 * (egM p α : ℝ) + 3 + Real.sqrt 2) / (2 : ℝ) ^ p := by
        rw [← add_div, ← add_div]
      have hbunorm : ‖HvdH.fxC p (buRound Wt p α s t hs0 x ℓ)‖ ≤ 1 := by
        rw [hid2]
        linarith [hchain, hstep, hsum, harith]
      exact inDisc_of_norm_fxC_le_one p hbunorm
    · have hA : (2 : ℝ) ^ p * ‖buWErr p α s t Wt hs0 ℓ u‖ ≤ 2 * (egM p α : ℝ) * δ := by
        have h := mul_le_mul_of_nonneg_left hS1 hp2.le
        rw [hdiv] at h
        exact h
      have hC : (2 : ℝ) ^ p * ‖buTL p α s t hs0 ℓ u‖ ≤ 3 := by
        have h := mul_le_mul_of_nonneg_left hTL hp2.le
        rw [hdiv] at h
        exact h
      rw [hid]
      calc (2 : ℝ) ^ p * ‖buWErr p α s t Wt hs0 ℓ u
              + (HvdH.Emat s t α).mulVec (u - y) ℓ - buTL p α s t hs0 ℓ u - ρ‖
          ≤ (2 : ℝ) ^ p * (‖buWErr p α s t Wt hs0 ℓ u‖ + ‖(HvdH.Emat s t α).mulVec (u - y) ℓ‖
              + ‖buTL p α s t hs0 ℓ u‖ + ‖ρ‖) := by
            apply mul_le_mul_of_nonneg_left _ hp2.le
            have h1 := norm_sub_le (buWErr p α s t Wt hs0 ℓ u
              + (HvdH.Emat s t α).mulVec (u - y) ℓ - buTL p α s t hs0 ℓ u) ρ
            have h2 := norm_sub_le (buWErr p α s t Wt hs0 ℓ u
              + (HvdH.Emat s t α).mulVec (u - y) ℓ) (buTL p α s t hs0 ℓ u)
            have h3 := norm_add_le (buWErr p α s t Wt hs0 ℓ u) ((HvdH.Emat s t α).mulVec (u - y) ℓ)
            linarith
        _ = (2 : ℝ) ^ p * ‖buWErr p α s t Wt hs0 ℓ u‖
              + (2 : ℝ) ^ p * ‖(HvdH.Emat s t α).mulVec (u - y) ℓ‖
              + (2 : ℝ) ^ p * ‖buTL p α s t hs0 ℓ u‖ + (2 : ℝ) ^ p * ‖ρ‖ := by ring
        _ ≤ 2 * (egM p α : ℝ) * δ + e / 2 + 3 + Real.sqrt 2 := by
            linarith [hA, hprop, hC, hρbound]
        _ ≤ (2 * δ + 1) * (egM p α) + 12 + (1 / 2) * e := by
            nlinarith [hm1, hsqrt2]
  exact ⟨fun ℓ => (perℓ ℓ).1, fun ℓ => (perℓ ℓ).2⟩

end Work.Resample
