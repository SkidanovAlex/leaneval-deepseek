import Mathlib
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea1.fibre_count_l51
import Submission.Work.FIArea1.harm_sum_l51
import Submission.Work.FIArea1.count_ratio_l51
import Submission.Work.FIArea1.offdiag_tauaverage
import Submission.Work.FIArea1.offdiag_final_l51
import Submission.Work.FIArea1.L51Count
import Submission.Work.FIArea1.L51Local
import Submission.Work.FIArea2.congCount
import Submission.Work.FIArea1.l51_Nc_prod
import Submission.Work.FIArea1.boxZ_dvd_count_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le
import Submission.Work.FIArea2.area2_r3
import Submission.Work.FIArea2.exists_cForm_eq_iff
import Submission.Work.FIArea2.sum_gBox_eq_sum_congruences

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The truncation radius `C₀ = ⌈√(2√2·R·√(2N))⌉ = ⌈√(4·|R|·√N)⌉` for the square roots
`c` of `Re(wz)` with `w ∈ gBox R`, `z ∈ Zbox N`. -/
def C0l (R : ℤ) (N : ℝ) : ℕ := ⌈Real.sqrt (4 * (R.natAbs : ℝ) * Real.sqrt N)⌉₊

/-- `(C₀)^2 ≥ 4|R|√N`. -/
lemma C0l_sq_ge (R : ℤ) (N : ℝ) : 4 * (R.natAbs : ℝ) * Real.sqrt N ≤ (C0l R N : ℝ) ^ 2 := by
  have h : Real.sqrt (4 * (R.natAbs : ℝ) * Real.sqrt N) ≤ (C0l R N : ℝ) := by
    rw [C0l]; exact Nat.le_ceil _
  have hnn : (0:ℝ) ≤ Real.sqrt (4 * (R.natAbs : ℝ) * Real.sqrt N) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (4 * (R.natAbs : ℝ) * Real.sqrt N)) ^ 2 ≤ (C0l R N : ℝ)^2 :=
    pow_le_pow_left₀ hnn h 2
  rwa [Real.sq_sqrt (by positivity)] at hsq

/-- **The size of the parameterising square root.**  If `w ∈ gBox R` and `z ∈ Zbox N` and
`c² = Re(wz)`, then `|c| ≤ C₀`. -/
lemma abs_c_le_C0l {R : ℤ} {N : ℝ} (hR : 1 ≤ R) {w z : GaussianInt}
    (hw : w ∈ Work.FIPlan.gBox R) (hz : z ∈ Work.FIArea1.Zbox N) {c : ℤ}
    (hc : c ^ 2 = Work.FIPlan.cForm w z) : c.natAbs ≤ C0l R N := by
  have hR0 : (0:ℤ) ≤ R := by omega
  have hR0' : (0:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR0
  have hRn : (R.natAbs : ℝ) = (R:ℝ) := by
    rw [Nat.cast_natAbs]; simp [abs_of_nonneg hR0']
  have hgw : ((Work.FIPlan.gnorm w : ℝ)) ≤ 2 * (R:ℝ)^2 := by
    have h := Work.FIArea2.gnorm_le_of_mem_gBox hR0 hw
    have h' : ((Work.FIPlan.gnorm w : ℝ)) ≤ 2 * (((R.natAbs : ℤ) : ℝ))^2 := by exact_mod_cast h
    rwa [show (((R.natAbs:ℤ):ℝ)) = (R:ℝ) by rw [Int.cast_natCast]; exact hRn] at h'
  have hzmem := (Work.FIArea1.mem_Zbox_iff).mp hz
  have hgz : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * N := hzmem.2.2.2
  have hcs : ((Work.FIPlan.cForm w z : ℝ))^2
      ≤ ((Work.FIPlan.gnorm w : ℝ)) * ((Work.FIPlan.gnorm z : ℝ)) := by
    have h := Work.FIArea1.cForm_sq_le w z
    have h' : ((Work.FIPlan.cForm w z : ℤ) : ℝ)^2
        ≤ (((Work.FIPlan.gnorm w : ℤ) * (Work.FIPlan.gnorm z : ℤ) : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'; simpa using h'
  have hcR : (c:ℝ)^2 = (Work.FIPlan.cForm w z : ℝ) := by rw [← hc]; push_cast; ring
  have hgr : ((Work.FIPlan.gnorm w : ℝ)) * ((Work.FIPlan.gnorm z : ℝ))
      ≤ (2 * (R:ℝ)^2) * (2*N) :=
    mul_le_mul hgw hgz (by positivity) (by positivity)
  have hN0 : (0:ℝ) ≤ N := by linarith
  have hNsqrt : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0
  have hkey : ((Work.FIPlan.cForm w z : ℝ))^2 ≤ (2 * (R:ℝ) * Real.sqrt N)^2 := by
    nlinarith [hcs.trans hgr, hNsqrt]
  have hcabs : (Work.FIPlan.cForm w z : ℝ) ≤ 2 * (R:ℝ) * Real.sqrt N := by
    have h := Real.sqrt_le_sqrt hkey
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (by positivity)] at h
    exact le_trans (le_abs_self _) h
  have hc2 : (c:ℝ)^2 ≤ 4 * (R.natAbs:ℝ) * Real.sqrt N := by
    rw [hcR, hRn]
    calc (Work.FIPlan.cForm w z : ℝ) ≤ 2 * (R:ℝ) * Real.sqrt N := hcabs
      _ ≤ 4 * (R:ℝ) * Real.sqrt N := by nlinarith [Real.sqrt_nonneg N, hR0']
  have hfinal : (c:ℝ)^2 ≤ (C0l R N : ℝ)^2 := hc2.trans (C0l_sq_ge R N)
  have hthis : ((c.natAbs : ℕ) : ℝ) ≤ ((C0l R N : ℕ) : ℝ) := by
    have h1 : (((c.natAbs : ℕ) : ℝ)) = |(c:ℝ)| := by
      rw [Nat.cast_natAbs]; exact Int.cast_abs (a := c)
    rw [h1]
    calc |(c:ℝ)| = Real.sqrt ((c:ℝ)^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((C0l R N : ℝ)^2) := Real.sqrt_le_sqrt hfinal
      _ = (C0l R N : ℝ) := Real.sqrt_sq (by positivity)
  exact_mod_cast hthis


/-! ## The divided imaginary parts and the fibre count -/

/-- `s₁* = s₁/(s₁,s₂)`: the imaginary part divided by the common factor of the pair. -/
noncomputable def sS1 (s1 s2 : ℤ) : ℤ :=
  if 0 ≤ s1 then ((s1.natAbs / s1.natAbs.gcd s2.natAbs : ℕ) : ℤ)
  else -((s1.natAbs / s1.natAbs.gcd s2.natAbs : ℕ) : ℤ)

/-- `s₂* = s₂/(s₁,s₂)`. -/
noncomputable def sS2 (s1 s2 : ℤ) : ℤ :=
  if 0 ≤ s2 then ((s2.natAbs / s1.natAbs.gcd s2.natAbs : ℕ) : ℤ)
  else -((s2.natAbs / s1.natAbs.gcd s2.natAbs : ℕ) : ℤ)

/-- `Δ̃ = r₁s₂* - r₂s₁*`, the determinant divided by `(s₁,s₂)`. -/
noncomputable def dTil (r1 r2 s1 s2 : ℤ) : ℤ := r1 * sS2 s1 s2 - r2 * sS1 s1 s2

/-- `n* = c₁²s₂* - c₂²s₁*`, the imaginary part of the congruence divided by `(s₁,s₂)`. -/
noncomputable def nSt (c1 c2 s1 s2 : ℤ) : ℤ := c1^2 * sS2 s1 s2 - c2^2 * sS1 s1 s2

lemma sS1_mul (s1 s2 : ℤ) : (s1.natAbs.gcd s2.natAbs : ℤ) * sS1 s1 s2 = s1 := by
  rw [sS1]; split_ifs with h
  · rw [← Int.natCast_mul, Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
    exact Int.natAbs_of_nonneg h
  · rw [mul_neg, ← Int.natCast_mul, Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
    have h2 : (s1.natAbs : ℤ) = -s1 := by rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by linarith)
    linarith

lemma sS2_mul (s1 s2 : ℤ) : (s1.natAbs.gcd s2.natAbs : ℤ) * sS2 s1 s2 = s2 := by
  rw [sS2]; split_ifs with h
  · rw [← Int.natCast_mul, Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
    exact Int.natAbs_of_nonneg h
  · rw [mul_neg, ← Int.natCast_mul, Nat.mul_comm, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
    have h2 : (s2.natAbs : ℤ) = -s2 := by rw [← Int.natAbs_neg]; exact Int.natAbs_of_nonneg (by linarith)
    linarith

lemma sS1_natAbs (s1 s2 : ℤ) : (sS1 s1 s2).natAbs = s1.natAbs / s1.natAbs.gcd s2.natAbs := by
  rw [sS1]; split_ifs with h
  · rw [Int.natAbs_natCast]
  · rw [Int.natAbs_neg, Int.natAbs_natCast]

lemma sS2_natAbs (s1 s2 : ℤ) : (sS2 s1 s2).natAbs = s2.natAbs / s1.natAbs.gcd s2.natAbs := by
  rw [sS2]; split_ifs with h
  · rw [Int.natAbs_natCast]
  · rw [Int.natAbs_neg, Int.natAbs_natCast]

lemma sS_coprime (s1 s2 : ℤ) (h : 0 < s1.natAbs.gcd s2.natAbs) :
    Nat.Coprime (sS1 s1 s2).natAbs (sS2 s1 s2).natAbs := by
  rw [sS1_natAbs, sS2_natAbs]
  exact Nat.coprime_div_gcd_div_gcd h

lemma sS1_ne_zero {s1 s2 : ℤ} (h : s1 ≠ 0) : sS1 s1 s2 ≠ 0 := by
  intro h0
  have h1 : (sS1 s1 s2).natAbs = 0 := by rw [h0]; rfl
  rw [sS1_natAbs] at h1
  have hg := Nat.gcd_dvd_left s1.natAbs s2.natAbs
  have h2 : s1.natAbs = 0 := by
    have h3 := Nat.div_mul_cancel hg
    rw [h1, Nat.zero_mul] at h3
    exact h3.symm
  exact h (Int.natAbs_eq_zero.mp h2)

lemma dTil_eq (r1 r2 s1 s2 : ℤ) :
    r1 * s2 - r2 * s1 = (s1.natAbs.gcd s2.natAbs : ℤ) * dTil r1 r2 s1 s2 := by
  have h2 := sS2_mul s1 s2; have h1 := sS1_mul s1 s2
  rw [dTil, show r1 * s2 = r1 * ((s1.natAbs.gcd s2.natAbs : ℤ) * sS2 s1 s2) from by rw [h2],
      show r2 * s1 = r2 * ((s1.natAbs.gcd s2.natAbs : ℤ) * sS1 s1 s2) from by rw [h1]]
  ring

lemma nSt_eq (c1 c2 s1 s2 : ℤ) :
    c1^2 * s2 - c2^2 * s1 = (s1.natAbs.gcd s2.natAbs : ℤ) * nSt c1 c2 s1 s2 := by
  have h2 := sS2_mul s1 s2; have h1 := sS1_mul s1 s2
  rw [nSt, show c1^2 * s2 = c1^2 * ((s1.natAbs.gcd s2.natAbs : ℤ) * sS2 s1 s2) from by rw [h2],
      show c2^2 * s1 = c2^2 * ((s1.natAbs.gcd s2.natAbs : ℤ) * sS1 s1 s2) from by rw [h1]]
  ring

lemma Delta_mk (r1 s1 r2 s2 : ℤ) :
    Work.FIPlan.Delta (⟨r1,s1⟩ : GaussianInt) (⟨r2,s2⟩ : GaussianInt) = r1*s2 - r2*s1 := by
  rw [Work.FIPlan.Delta]; simp [Zsqrtd.star_mk, Zsqrtd.im_mul]; ring

lemma Delta_dvd_im {d : ℤ} {X : GaussianInt} (h : (d : GaussianInt) ∣ X) : d ∣ X.im := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.im, ?_⟩
  have hh := congrArg Zsqrtd.im hq
  simpa [Zsqrtd.im_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast] using hh

lemma im_congr (c1 c2 : ℤ) (z1 z2 : GaussianInt) :
    (((c1 : GaussianInt)^2 * z2 - (c2 : GaussianInt)^2 * z1).im)
      = c1^2 * z2.im - c2^2 * z1.im := by
  simp [pow_two, Zsqrtd.im_mul, Zsqrtd.im_sub, Zsqrtd.re_intCast, Zsqrtd.im_intCast]

/-- **The congruence implies the fibre divisibility.**  If `Δ(z₁,z₂) ∣ c₁²z₂ - c₂²z₁` in `ℤ[i]`
and `s₁,s₂` are not both zero, then `Δ̃ ∣ n*`. -/
lemma congr_imp_dTil_dvd {r1 s1 r2 s2 : ℤ} (hs : s1 ≠ 0 ∨ s2 ≠ 0) {c1 c2 : ℤ}
    (h : (Work.FIPlan.Delta (⟨r1,s1⟩:GaussianInt) (⟨r2,s2⟩:GaussianInt) : GaussianInt)
          ∣ (c1:GaussianInt)^2 * (⟨r2,s2⟩:GaussianInt) - (c2:GaussianInt)^2 * (⟨r1,s1⟩:GaussianInt)) :
    dTil r1 r2 s1 s2 ∣ nSt c1 c2 s1 s2 := by
  have hΔ : Work.FIPlan.Delta (⟨r1,s1⟩:GaussianInt) (⟨r2,s2⟩:GaussianInt) = r1*s2 - r2*s1 :=
    Delta_mk r1 s1 r2 s2
  rw [hΔ] at h
  have him := Delta_dvd_im h
  rw [im_congr] at him
  simp only at him
  have hg : 0 < s1.natAbs.gcd s2.natAbs := by
    rcases hs with h | h
    · exact Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr h)
    · exact Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.mpr h)
  rw [dTil_eq r1 r2 s1 s2, nSt_eq c1 c2 s1 s2] at him
  exact Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hg.ne') him


/-! ## Coordinates of `Zbox N` -/

lemma Zbox_re_mem {N : ℝ} {z : GaussianInt} (hz : z ∈ Work.FIArea1.Zbox N) :
    z.re ∈ Finset.Icc (-(Work.FIArea1.KZ N)) (Work.FIArea1.KZ N) :=
  (Work.FIArea2.mem_gBox_iff.mp (Work.FIArea1.mem_Zbox_iff.mp hz).1).1

lemma Zbox_im_mem {N : ℝ} {z : GaussianInt} (hz : z ∈ Work.FIArea1.Zbox N) :
    z.im ∈ Finset.Icc (-(Work.FIArea1.KZ N)) (Work.FIArea1.KZ N) :=
  (Work.FIArea2.mem_gBox_iff.mp (Work.FIArea1.mem_Zbox_iff.mp hz).1).2

/-- A primitive `z` with `|z|² > 1` has `Im z ≠ 0`. -/
lemma Zbox_im_ne_zero {N : ℝ} {z : GaussianInt} (hz : z ∈ Work.FIArea1.Zbox N)
    (hN : 2 ≤ N) : z.im ≠ 0 := by
  intro him
  have hzmem := (Work.FIArea1.mem_Zbox_iff).mp hz
  have hprim : Work.FIPlan.IsPrimitive z := hzmem.2.1
  have hgn : N < (Work.FIPlan.gnorm z : ℝ) := hzmem.2.2.1
  have hzde0 : z = (⟨z.re, 0⟩ : GaussianInt) := by
    rw [show z = (⟨z.re, z.im⟩ : GaussianInt) from rfl, him]
  have hcop : IsCoprime (⟨z.re,0⟩:GaussianInt) (⟨z.re,0⟩:GaussianInt) := by
    rw [Work.FIPlan.IsPrimitive] at hprim
    rw [hzde0] at hprim
    simpa [Zsqrtd.star_mk] using hprim
  have hu : IsUnit (⟨z.re, 0⟩ : GaussianInt) := isCoprime_self.mp hcop
  have h1 : Work.FIPlan.gnorm (⟨z.re, 0⟩ : GaussianInt) = 1 := by
    rw [Work.FIPlan.gnorm]; exact Zsqrtd.norm_eq_one_iff.mpr hu
  have h2 : Work.FIPlan.gnorm z = 1 := by rw [hzde0]; exact h1
  rw [h2] at hgn; norm_num at hgn; linarith


/-- Cardinality of the box `[-KZ,KZ]`. -/
lemma box_card (KZ : ℤ) (h : 0 ≤ KZ) : (Finset.Icc (-KZ) KZ).card = 2 * KZ.natAbs + 1 := by
  have hKZn : (KZ.natAbs : ℤ) = KZ := Int.natAbs_of_nonneg h
  have h1 : KZ + 1 - (-KZ) = ((2 * KZ.natAbs + 1 : ℕ) : ℤ) := by
    rw [show ((2 * KZ.natAbs + 1 : ℕ) : ℤ) = 2 * (KZ.natAbs : ℤ) + 1 by push_cast; ring, hKZn]
    ring
  rw [Int.card_Icc, h1, Int.toNat_natCast]

/-- **The `(r₁,r₂)`-fibre bound for a fixed `(s₁,s₂,c₁,c₂)`.**  Either `n* = 0` (in which case
the fibre is the whole box) or we may apply `fibre_count_l51`. -/
lemma fibre_card_le {KZ : ℤ} (hKZ : 0 ≤ KZ) {s1 s2 c1 c2 : ℤ}
    (hs1 : s1 ∈ (Finset.Icc (-KZ) KZ).erase 0)
    (hs2 : s2 ∈ (Finset.Icc (-KZ) KZ).erase 0) :
    (((Finset.Icc (-KZ) KZ).product (Finset.Icc (-KZ) KZ)).filter
        (fun r : ℤ×ℤ => r.1 * sS2 s1 s2 - r.2 * sS1 s1 s2 ≠ 0 ∧
              r.1 * sS2 s1 s2 - r.2 * sS1 s1 s2 ∣ nSt c1 c2 s1 s2)).card
      ≤ (if nSt c1 c2 s1 s2 = 0 then (2 * KZ.natAbs + 1) ^ 2
         else 2 * (nSt c1 c2 s1 s2).natAbs.divisors.card
                * (2 * KZ.natAbs / (sS1 s1 s2).natAbs + 1)) := by
  classical
  have hs1ne : s1 ≠ 0 := (Finset.mem_erase.mp hs1).1
  have hg : 0 < s1.natAbs.gcd s2.natAbs := Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hs1ne)
  have hKZeq : KZ = (KZ.natAbs : ℤ) := (Int.natAbs_of_nonneg hKZ).symm
  by_cases h : nSt c1 c2 s1 s2 = 0
  · rw [if_pos h]
    calc _ ≤ ((Finset.Icc (-KZ) KZ).product (Finset.Icc (-KZ) KZ)).card :=
          Finset.card_filter_le _ _
      _ = (2 * KZ.natAbs + 1) ^ 2 := by
          rw [show ((Finset.Icc (-KZ) KZ).product (Finset.Icc (-KZ) KZ)).card
                = (Finset.Icc (-KZ) KZ).card * (Finset.Icc (-KZ) KZ).card from
                Finset.card_product _ _, box_card KZ hKZ]
          ring
  · rw [if_neg h]
    have hfc := fibre_count_l51 KZ.natAbs (sS1 s1 s2) (sS2 s1 s2) (sS1_ne_zero hs1ne)
      (sS_coprime s1 s2 hg) (nSt c1 c2 s1 s2) h
    rw [← hKZeq] at hfc
    exact hfc


lemma mem_prod54 {α β : Type*} (s : Finset α) (t : Finset β) (p : α × β) :
    (p ∈ s.product t) ↔ (p.1 ∈ s ∧ p.2 ∈ t) := Finset.mem_product

lemma card_prod54 {α β : Type*} (s : Finset α) (t : Finset β) :
    (s.product t).card = s.card * t.card := Finset.card_product s t

lemma sum_prod54 {α β γ : Type*} [AddCommMonoid γ] (s : Finset α) (t : Finset β) (f : α×β → γ) :
    (∑ x ∈ s.product t, f x) = ∑ x ∈ s, ∑ y ∈ t, f (x,y) := Finset.sum_product s t f

/-- The set of square pairs `(c₁,c₂) ∈ Cb²` attached to a pair `(z₁,z₂)` with `Δ ≠ 0`. -/
noncomputable def Df54 (Cb : Finset ℤ) (z1 z2 : GaussianInt) : Finset (ℤ×ℤ) :=
  if Work.FIPlan.Delta z1 z2 = 0 then (∅ : Finset (ℤ×ℤ)) else
    (Cb.product Cb).filter (fun p : ℤ×ℤ =>
      (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1:GaussianInt)^2 * z2 - (p.2:GaussianInt)^2 * z1)

lemma Df54_eq (Cb : Finset ℤ) (z1 z2 : GaussianInt) :
    Df54 Cb z1 z2 = if Work.FIPlan.Delta z1 z2 = 0 then (∅ : Finset (ℤ×ℤ)) else
      (Cb.product Cb).filter (fun p : ℤ×ℤ =>
        (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1:GaussianInt)^2 * z2 - (p.2:GaussianInt)^2 * z1) :=
  rfl

lemma C0l_pos (R : ℤ) (N : ℝ) (hR : 1 ≤ R) (hN : 1 ≤ N) : 1 ≤ C0l R N := by
  have hRn : (R.natAbs : ℝ) = (R:ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs (a := R),
      abs_of_nonneg (by exact_mod_cast (le_trans (by norm_num : (0:ℤ) ≤ 1) hR) : (0:ℝ) ≤ (R:ℝ))]
  have hN1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hR' : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have h4 : (1:ℝ) ≤ 4 * (R.natAbs : ℝ) * Real.sqrt N := by
    rw [hRn]; nlinarith [hR', hN1]
  have h1 : (1:ℝ) ≤ Real.sqrt (4 * (R.natAbs : ℝ) * Real.sqrt N) := by
    calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (4 * (R.natAbs:ℝ) * Real.sqrt N) := Real.sqrt_le_sqrt h4
  have h2 : (1:ℝ) ≤ ((C0l R N : ℕ):ℝ) := by rw [C0l]; exact h1.trans (Nat.le_ceil _)
  exact_mod_cast h2

lemma KZ_natAbs (N : ℝ) : (Work.FIArea1.KZ N).natAbs = ⌈Real.sqrt (2 * N)⌉₊ := by
  rw [Work.FIArea1.KZ]
  exact Int.natAbs_natCast _

lemma KZ_le_four_C0l (R : ℤ) (N : ℝ) (hN : 2 ≤ N) (hRN : 2 * Real.sqrt N ≤ (R : ℝ)) :
    (Work.FIArea1.KZ N).natAbs ≤ 4 * C0l R N := by
  rw [KZ_natAbs, C0l]
  have hRn : (R.natAbs : ℝ) = (R:ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs (a := R),
      abs_of_nonneg (by linarith [hRN, Real.sqrt_nonneg N] : (0:ℝ) ≤ (R:ℝ))]
  have hsNsq : Real.sqrt N * Real.sqrt N = N := by
    rw [← pow_two, Real.sq_sqrt (by linarith : (0:ℝ) ≤ N)]
  have hkey : Real.sqrt (2*N) ≤ Real.sqrt (4 * (R.natAbs:ℝ) * Real.sqrt N) := by
    apply Real.sqrt_le_sqrt
    rw [hRn]; nlinarith [hRN, hsNsq, Real.sqrt_nonneg N]
  have hcast : (⌈Real.sqrt (2*N)⌉₊ : ℝ) ≤ 2 * Real.sqrt (2*N) := by
    have h1 := (Nat.ceil_lt_add_one (show (0:ℝ) ≤ Real.sqrt (2*N) by positivity)).le
    have h2 : (1:ℝ) ≤ Real.sqrt (2*N) := Real.one_le_sqrt.mpr (by linarith)
    linarith
  have h1 : 2 * Real.sqrt (2*N) ≤ 4 * ((⌈Real.sqrt (4 * (R.natAbs:ℝ) * Real.sqrt N)⌉₊ : ℕ) : ℝ) := by
    have h3 : Real.sqrt (4 * (R.natAbs:ℝ) * Real.sqrt N)
        ≤ ((⌈Real.sqrt (4 * (R.natAbs:ℝ) * Real.sqrt N)⌉₊ : ℕ):ℝ) := Nat.le_ceil _
    have h4 : Real.sqrt (2*N) ≤ 2 * Real.sqrt (4 * (R.natAbs:ℝ) * Real.sqrt N) := by
      nlinarith [hkey, Real.sqrt_nonneg (2*N), Real.sqrt_nonneg (4 * (R.natAbs:ℝ) * Real.sqrt N)]
    linarith
  exact_mod_cast (le_trans hcast h1)

/-! ## Auxiliary combinatorial lemmas for the count -/

/-- If `a ∈ [-K,K]` then `|a| ≤ |K|`. -/
lemma natAbs_le_natAbs_of_mem_Icc {K a : ℤ} (h : a ∈ Finset.Icc (-K) K) : a.natAbs ≤ K.natAbs := by
  rw [Finset.mem_Icc] at h
  rw [Int.natAbs_le_iff_sq_le]
  nlinarith [h.1, h.2]

/-- `n*` written with the factors commuted. -/
lemma nSt_comm (c1 c2 s1 s2 : ℤ) :
    nSt c1 c2 s1 s2 = sS2 s1 s2 * c1 ^ 2 - sS1 s1 s2 * c2 ^ 2 := by
  rw [nSt]; ring

/-- **A filtered product counted by fibres.**  The cardinality of `(A × B).filter P` is the sum
over `s ∈ A` of the cardinality of the `B`-fibre of `P` over `s`. -/
lemma card_filter_product {α β : Type*} (A : Finset α) (B : Finset β) (P : α × β → Prop)
    [DecidablePred P] :
    ((A.product B).filter P).card = ∑ s ∈ A, (B.filter (fun c => P (s, c))).card := by
  classical
  rw [show ((A.product B).filter P).card
        = ∑ q ∈ A.product B, (if P q then (1 : ℕ) else 0) from by
    rw [Finset.sum_boole]; rfl]
  rw [sum_prod54]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.sum_boole]; rfl

/-- The degenerate `n* = 0` counting set of `Work.FIArea1.count_ratio_l51`. -/
def CRset (K L : ℕ) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0).product
     ((Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0)).product
    ((Finset.Icc (-(L : ℤ)) (L : ℤ)).product (Finset.Icc (-(L : ℤ)) (L : ℤ)))).filter
    (fun q : (ℤ × ℤ) × (ℤ × ℤ) => q.2.1 ^ 2 * q.1.2 = q.2.2 ^ 2 * q.1.1)

theorem offdiag_count_l51 : ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (N : ℝ), 1 ≤ R → 2 ≤ N →
    2 * Real.sqrt N ≤ (R : ℝ) →
    (∑ w ∈ (Work.FIPlan.gBox R).erase 0, ∑ z1 ∈ Work.FIArea1.Zbox N,
        ∑ z2 ∈ Work.FIArea1.Zbox N,
        (if Work.FIPlan.Delta z1 z2 = 0 then 0
         else ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
            * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)))
      ≤ C * ((R.natAbs : ℝ) * N ^ ((3 : ℝ) / 2))
        * (Real.log (2 * ((R.natAbs : ℝ) + N + 2))) ^ 514 := by
  obtain ⟨C_tau, hCtau_pos, hCtau⟩ := Work.FIArea1.offdiag_tauaverage
  obtain ⟨C_h, hCh_pos, hCh⟩ := harm_sum_l51
  obtain ⟨C_r, hCr_pos, hCr⟩ := count_ratio_l51
  refine ⟨(2:ℝ)^540 * (C_tau + 1) * (C_h + 1) * (C_r + 1) + 2, by positivity, ?_⟩
  intro R N hR hN hRN
  classical
  have hR0 : (0:ℤ) ≤ R := by omega
  have hN0 : (0:ℝ) < N := by linarith
  set KZ : ℤ := Work.FIArea1.KZ N with hKZdef
  have hKZ0 : 0 ≤ KZ := by rw [hKZdef]; exact Work.FIArea1.KZ_nonneg N
  set C0 : ℕ := C0l R N with hC0def
  set Zb : Finset GaussianInt := Work.FIArea1.Zbox N with hZbdef
  set Cbox : Finset ℤ := Finset.Icc (-(C0:ℤ)) (C0:ℤ) with hCboxdef
  set Box : Finset ℤ := Finset.Icc (-KZ) KZ with hBoxdef
  set Sbox : Finset ℤ := Box.erase 0 with hSboxdef
  set Big : Finset ((GaussianInt × GaussianInt) × (ℤ×ℤ)) :=
    ((Zb.product Zb).product (Cbox.product Cbox)).filter (fun q =>
      Work.FIPlan.Delta q.1.1 q.1.2 ≠ 0 ∧
        (Work.FIPlan.Delta q.1.1 q.1.2 : GaussianInt) ∣
          (q.2.1 : GaussianInt)^2 * q.1.2 - (q.2.2 : GaussianInt)^2 * q.1.1) with hBigdef
  have hBigcard : (Big.card : ℝ) = ∑ z1 ∈ Zb, ∑ z2 ∈ Zb, ((Df54 Cbox z1 z2).card : ℝ) := by
    have hfib : ∀ z ∈ Zb.product Zb, (Big.filter (fun q => q.1 = z)).card = (Df54 Cbox z.1 z.2).card := by
      intro z hz
      rw [hBigdef]
      refine Finset.card_bij (fun (q : (GaussianInt×GaussianInt)×(ℤ×ℤ)) (_ : q ∈ _) => q.2) ?_ ?_ ?_
      · intro q hq
        obtain ⟨hqB, hq1⟩ := Finset.mem_filter.mp hq
        obtain ⟨hqBC, hΔ, hcongr⟩ := Finset.mem_filter.mp hqB
        obtain ⟨hqZ, hqC⟩ := (mem_prod54 (Zb.product Zb) (Cbox.product Cbox) q).mp hqBC
        rw [hq1] at hΔ hcongr
        rw [Df54_eq, if_neg hΔ]
        exact Finset.mem_filter.mpr ⟨hqC, hcongr⟩
      · intro q1 hq1 q2 hq2 h
        obtain ⟨-, h1⟩ := Finset.mem_filter.mp hq1
        obtain ⟨-, h2⟩ := Finset.mem_filter.mp hq2
        exact Prod.ext (h1.trans h2.symm) h
      · intro p hp
        rw [Df54_eq] at hp
        by_cases hΔ : Work.FIPlan.Delta z.1 z.2 = 0
        · rw [if_pos hΔ] at hp; exact absurd hp (by simp)
        · rw [if_neg hΔ] at hp
          obtain ⟨hpC, hpcongr⟩ := Finset.mem_filter.mp hp
          obtain ⟨hp1, hp2⟩ := (mem_prod54 Cbox Cbox p).mp hpC
          refine ⟨(z, p), ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨(mem_prod54 (Zb.product Zb) (Cbox.product Cbox) (z,p)).mpr
              ⟨hz, (mem_prod54 Cbox Cbox p).mpr ⟨hp1, hp2⟩⟩, hΔ, hpcongr⟩, rfl⟩
    have hmap : Set.MapsTo Prod.fst (↑Big : Set ((GaussianInt×GaussianInt)×(ℤ×ℤ))) (↑(Zb.product Zb)) :=
      fun q hq => (mem_prod54 (Zb.product Zb) (Cbox.product Cbox) q).mp
        (Finset.mem_filter.mp hq).1 |>.1
    rw [Finset.card_eq_sum_card_fiberwise hmap, Nat.cast_sum, sum_prod54]
    apply Finset.sum_congr rfl; intro z1 hz1
    apply Finset.sum_congr rfl; intro z2 hz2
    rw [show (Big.filter (fun q => q.1 = (z1,z2))).card = (Df54 Cbox z1 z2).card from
      hfib (z1,z2) ((mem_prod54 Zb Zb (z1,z2)).mpr ⟨hz1,hz2⟩)]
  have hpt : ∀ z1 ∈ Zb, ∀ z2 ∈ Zb,
      (if Work.FIPlan.Delta z1 z2 = 0 then 0
        else ∑ w ∈ Work.FIPlan.gBox R, ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
            * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ))
        ≤ ((Df54 Cbox z1 z2).card : ℝ) := by
    intro z1 hz1 z2 hz2
    rw [hZbdef] at hz1 hz2
    by_cases hΔ : Work.FIPlan.Delta z1 z2 = 0
    · rw [if_pos hΔ]; positivity
    · rw [if_neg hΔ]
      set S : Finset (ℤ×ℤ) := (Cbox.product Cbox).filter (fun p : ℤ×ℤ =>
          (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1:GaussianInt)^2 * z2 - (p.2:GaussianInt)^2 * z1
            ∧ Work.FIArea2.wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox R) with hSdef
      have hK : ∀ w ∈ Work.FIPlan.gBox R, ∀ c1 c2 : ℤ, Work.FIPlan.cForm w z1 = c1 * c1 →
          Work.FIPlan.cForm w z2 = c2 * c2 →
          -(C0:ℤ) ≤ c1 ∧ c1 ≤ (C0:ℤ) ∧ -(C0:ℤ) ≤ c2 ∧ c2 ≤ (C0:ℤ) := by
        intro w hw c1 c2 hc1 hc2
        have h1 : c1.natAbs ≤ C0 := by rw [hC0def]; exact abs_c_le_C0l hR hw hz1 (by rw [hc1]; ring)
        have h2 : c2.natAbs ≤ C0 := by rw [hC0def]; exact abs_c_le_C0l hR hw hz2 (by rw [hc2]; ring)
        have hle1 : (c1.natAbs : ℤ) ≤ (C0:ℤ) := by exact_mod_cast h1
        have hle2 : (c2.natAbs : ℤ) ≤ (C0:ℤ) := by exact_mod_cast h2
        refine ⟨?_, ?_, ?_, ?_⟩
        · have := Int.le_natAbs (a := -c1); rw [Int.natAbs_neg] at this; linarith
        · exact Int.le_natAbs.trans hle1
        · have := Int.le_natAbs (a := -c2); rw [Int.natAbs_neg] at this; linarith
        · exact Int.le_natAbs.trans hle2
      have hS : ∀ p : ℤ×ℤ, p ∈ S ↔ Work.FIArea2.wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox R ∧
          p.1 ∈ Finset.Icc (-(C0:ℤ)) (C0:ℤ) ∧ p.2 ∈ Finset.Icc (-(C0:ℤ)) (C0:ℤ) ∧
          (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1:GaussianInt)^2 * z2 - (p.2:GaussianInt)^2 * z1 := by
        intro p
        constructor
        · intro hp
          obtain ⟨hpC, hpcongr, hpw⟩ := Finset.mem_filter.mp hp
          obtain ⟨hp1, hp2⟩ := (mem_prod54 Cbox Cbox p).mp hpC
          rw [hCboxdef] at hp1 hp2
          exact ⟨hpw, hp1, hp2, hpcongr⟩
        · rintro ⟨hpw, hp1, hp2, hpcongr⟩
          exact Finset.mem_filter.mpr ⟨(mem_prod54 Cbox Cbox p).mpr
            ⟨by rw [hCboxdef]; exact hp1, by rw [hCboxdef]; exact hp2⟩, hpcongr, hpw⟩
      have hmain := Work.FIArea2.sum_gBox_eq_sum_congruences (R := R) (f := fun _ => (1:ℝ))
        (z1 := z1) (z2 := z2) hΔ C0 S hK (by intro p; rw [hS p]; tauto)
      have hcard : (S.card : ℝ) ≤ ((Df54 Cbox z1 z2).card : ℝ) := by
        have hsub : S ⊆ Df54 Cbox z1 z2 := by
          intro p hp
          rw [hS p] at hp
          rw [Df54_eq, if_neg hΔ]
          exact Finset.mem_filter.mpr ⟨(mem_prod54 Cbox Cbox p).mpr
            ⟨by rw [hCboxdef]; exact hp.2.1, by rw [hCboxdef]; exact hp.2.2.1⟩, hp.2.2.2⟩
        exact_mod_cast Finset.card_le_card hsub
      have hmain' : (∑ w ∈ Work.FIPlan.gBox R, ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
          * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)) = (S.card : ℝ) := by
        rw [show (S.card : ℝ) = ∑ p ∈ S, (1:ℝ) from by rw [Finset.sum_const]; simp, ← hmain]
        apply Finset.sum_congr rfl; intro w _; ring
      rw [hmain']
      exact hcard
  have hA : (∑ w ∈ (Work.FIPlan.gBox R).erase 0, ∑ z1 ∈ Zb, ∑ z2 ∈ Zb,
        (if Work.FIPlan.Delta z1 z2 = 0 then 0
         else ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
            * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)))
      ≤ ∑ z1 ∈ Zb, ∑ z2 ∈ Zb, ((Df54 Cbox z1 z2).card : ℝ) := by
    calc _ ≤ ∑ w ∈ Work.FIPlan.gBox R, ∑ z1 ∈ Zb, ∑ z2 ∈ Zb,
          (if Work.FIPlan.Delta z1 z2 = 0 then 0
           else ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          intro w _ _; positivity
      _ = ∑ z1 ∈ Zb, ∑ z2 ∈ Zb, ∑ w ∈ Work.FIPlan.gBox R,
          (if Work.FIPlan.Delta z1 z2 = 0 then 0
           else ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
              * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro z1 _
          rw [Finset.sum_comm]
      _ ≤ ∑ z1 ∈ Zb, ∑ z2 ∈ Zb, ((Df54 Cbox z1 z2).card : ℝ) := by
          apply Finset.sum_le_sum; intro z1 hz1
          apply Finset.sum_le_sum; intro z2 hz2
          rw [show (∑ w ∈ Work.FIPlan.gBox R, (if Work.FIPlan.Delta z1 z2 = 0 then 0
                else ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
                   * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)))
              = (if Work.FIPlan.Delta z1 z2 = 0 then 0
                 else ∑ w ∈ Work.FIPlan.gBox R, ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
                   * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)) from by
                by_cases h : Work.FIPlan.Delta z1 z2 = 0
                · simp [h]
                · simp [h]]
          exact hpt z1 hz1 z2 hz2
  have hstep1 : (∑ w ∈ (Work.FIPlan.gBox R).erase 0, ∑ z1 ∈ Work.FIArea1.Zbox N,
        ∑ z2 ∈ Work.FIArea1.Zbox N,
        (if Work.FIPlan.Delta z1 z2 = 0 then 0
         else ((Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℕ) : ℝ)
            * ((Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℕ) : ℝ)))
      ≤ (Big.card : ℝ) := by
    rw [hBigcard]
    rw [← hZbdef]
    exact hA
  set Tup2 : Finset (((ℤ×ℤ)×(ℤ×ℤ))×(ℤ×ℤ)) :=
    (((Sbox.product Sbox).product (Cbox.product Cbox)).product (Box.product Box)).filter
      (fun x => dTil x.2.1 x.2.2 x.1.1.1 x.1.1.2 ≠ 0 ∧
                dTil x.2.1 x.2.2 x.1.1.1 x.1.1.2 ∣ nSt x.1.2.1 x.1.2.2 x.1.1.1 x.1.1.2) with hTup2def
  have memTup2 : ∀ x : ((ℤ×ℤ)×(ℤ×ℤ))×(ℤ×ℤ), x ∈ Tup2 ↔
      x.1.1.1 ∈ Sbox ∧ x.1.1.2 ∈ Sbox ∧ x.1.2.1 ∈ Cbox ∧ x.1.2.2 ∈ Cbox ∧
      x.2.1 ∈ Box ∧ x.2.2 ∈ Box ∧
      dTil x.2.1 x.2.2 x.1.1.1 x.1.1.2 ≠ 0 ∧ dTil x.2.1 x.2.2 x.1.1.1 x.1.1.2 ∣ nSt x.1.2.1 x.1.2.2 x.1.1.1 x.1.1.2 := by
    intro x
    rw [hTup2def, Finset.mem_filter]
    constructor
    · rintro ⟨hmem, hcond⟩
      obtain ⟨hmem1, hmemb⟩ := (mem_prod54 ((Sbox.product Sbox).product (Cbox.product Cbox)) (Box.product Box) x).mp hmem
      obtain ⟨hmS, hmC⟩ := (mem_prod54 (Sbox.product Sbox) (Cbox.product Cbox) x.1).mp hmem1
      obtain ⟨hmS1, hmS2⟩ := (mem_prod54 Sbox Sbox x.1.1).mp hmS
      obtain ⟨hmC1, hmC2⟩ := (mem_prod54 Cbox Cbox x.1.2).mp hmC
      obtain ⟨hmB1, hmB2⟩ := (mem_prod54 Box Box x.2).mp hmemb
      exact ⟨hmS1, hmS2, hmC1, hmC2, hmB1, hmB2, hcond⟩
    · rintro ⟨hmS1, hmS2, hmC1, hmC2, hmB1, hmB2, hcond⟩
      exact ⟨(mem_prod54 _ _ x).mpr ⟨(mem_prod54 _ _ x.1).mpr
        ⟨(mem_prod54 _ _ x.1.1).mpr ⟨hmS1,hmS2⟩, (mem_prod54 _ _ x.1.2).mpr ⟨hmC1,hmC2⟩⟩,
        (mem_prod54 _ _ x.2).mpr ⟨hmB1,hmB2⟩⟩, hcond⟩
  have hstep2 : (Big.card : ℝ) ≤ (Tup2.card : ℝ) := by
    have h : Big.card ≤ Tup2.card := by
      rw [hBigdef]
      apply Finset.card_le_card_of_injOn
        (fun q : (GaussianInt×GaussianInt)×(ℤ×ℤ) =>
          (((q.1.1.im, q.1.2.im), (q.2.1, q.2.2)), (q.1.1.re, q.1.2.re)))
      · intro q hq
        obtain ⟨hqBC, hΔ, hcongr⟩ := Finset.mem_filter.mp hq
        obtain ⟨hqZ, hqC⟩ := (mem_prod54 (Zb.product Zb) (Cbox.product Cbox) q).mp hqBC
        obtain ⟨hz1, hz2⟩ := (mem_prod54 Zb Zb q.1).mp hqZ
        obtain ⟨hc1, hc2⟩ := (mem_prod54 Cbox Cbox q.2).mp hqC
        rw [hZbdef] at hz1 hz2
        have him1 : q.1.1.im ∈ Sbox := by
          rw [hSboxdef, Finset.mem_erase, hBoxdef, hKZdef]
          exact ⟨Zbox_im_ne_zero hz1 hN, Zbox_im_mem hz1⟩
        have him2 : q.1.2.im ∈ Sbox := by
          rw [hSboxdef, Finset.mem_erase, hBoxdef, hKZdef]
          exact ⟨Zbox_im_ne_zero hz2 hN, Zbox_im_mem hz2⟩
        have hre1 : q.1.1.re ∈ Box := by rw [hBoxdef, hKZdef]; exact Zbox_re_mem hz1
        have hre2 : q.1.2.re ∈ Box := by rw [hBoxdef, hKZdef]; exact Zbox_re_mem hz2
        have hdt : dTil q.1.1.re q.1.2.re q.1.1.im q.1.2.im ≠ 0 := by
          intro h0
          have hgpos : 0 < q.1.1.im.natAbs.gcd q.1.2.im.natAbs :=
            Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (Zbox_im_ne_zero hz1 hN))
          apply hΔ
          rw [show q.1.1 = (⟨q.1.1.re, q.1.1.im⟩ : GaussianInt) from rfl,
              show q.1.2 = (⟨q.1.2.re, q.1.2.im⟩ : GaussianInt) from rfl,
              Delta_mk, dTil_eq, h0, mul_zero]
        have hcongr' : dTil q.1.1.re q.1.2.re q.1.1.im q.1.2.im ∣ nSt q.2.1 q.2.2 q.1.1.im q.1.2.im :=
          congr_imp_dTil_dvd (Or.inl (Zbox_im_ne_zero hz1 hN)) hcongr
        exact (memTup2 _).mpr ⟨him1, him2, hc1, hc2, hre1, hre2, hdt, hcongr'⟩
      · intro q1 hq1 q2 hq2 h
        have e_im1 : q1.1.1.im = q2.1.1.im := congrArg (fun y => y.1.1.1) h
        have e_im2 : q1.1.2.im = q2.1.2.im := congrArg (fun y => y.1.1.2) h
        have e_c1 : q1.2.1 = q2.2.1 := congrArg (fun y => y.1.2.1) h
        have e_c2 : q1.2.2 = q2.2.2 := congrArg (fun y => y.1.2.2) h
        have e_re1 : q1.1.1.re = q2.1.1.re := congrArg (fun y => y.2.1) h
        have e_re2 : q1.1.2.re = q2.1.2.re := congrArg (fun y => y.2.2) h
        have e1 : q1.1.1 = q2.1.1 := by
          rw [show q1.1.1 = (⟨q1.1.1.re, q1.1.1.im⟩ : GaussianInt) from rfl,
              show q2.1.1 = (⟨q2.1.1.re, q2.1.1.im⟩ : GaussianInt) from rfl, e_re1, e_im1]
        have e2 : q1.1.2 = q2.1.2 := by
          rw [show q1.1.2 = (⟨q1.1.2.re, q1.1.2.im⟩ : GaussianInt) from rfl,
              show q2.1.2 = (⟨q2.1.2.re, q2.1.2.im⟩ : GaussianInt) from rfl, e_re2, e_im2]
        exact Prod.ext (Prod.ext e1 e2) (Prod.ext e_c1 e_c2)
    exact_mod_cast h
  have hstep3 : (Tup2.card : ℝ) ≤
      2*C_tau*((C0:ℝ)+1)^2*(Real.log (2*((C0:ℝ)+2)))^510 *
        (2*(KZ.natAbs:ℝ)*C_h*((KZ.natAbs:ℝ)+1)*(Real.log ((KZ.natAbs:ℝ)+2))^2 + 4*(KZ.natAbs:ℝ)^2)
      + C_r*((KZ.natAbs:ℝ)+1)*((KZ.natAbs:ℝ)+2+(C0:ℝ))*(2*(KZ.natAbs:ℝ)+1)^2 := by
    -- ## Step 3: `Tup2` as a sum of `(r₁,r₂)`-fibre bounds over `DOM = Sbox² × Cbox²`
    set A : ℝ := (((2 * KZ.natAbs + 1 : ℕ)) : ℝ) ^ 2 with hAdef
    set CtauB : ℝ := 2 * C_tau * ((C0 : ℝ) + 1) ^ 2 * (Real.log (2 * ((C0 : ℝ) + 2))) ^ 510
      with hCtauBdef
    set DOM : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := (Sbox.product Sbox).product (Cbox.product Cbox)
      with hDOMdef
    set Fib : ((ℤ × ℤ) × (ℤ × ℤ)) → Finset (ℤ × ℤ) := fun y => (Box.product Box).filter
        (fun r : ℤ × ℤ => dTil r.1 r.2 y.1.1 y.1.2 ≠ 0 ∧
          dTil r.1 r.2 y.1.1 y.1.2 ∣ nSt y.2.1 y.2.2 y.1.1 y.1.2) with hFibdef
    set Bnd : ((ℤ × ℤ) × (ℤ × ℤ)) → ℝ := fun y => ((if nSt y.2.1 y.2.2 y.1.1 y.1.2 = 0
        then (2 * KZ.natAbs + 1) ^ 2
        else 2 * (nSt y.2.1 y.2.2 y.1.1 y.1.2).natAbs.divisors.card
              * (2 * KZ.natAbs / (sS1 y.1.1 y.1.2).natAbs + 1) : ℕ) : ℝ) with hBnddef
    have hcard : (Tup2.card : ℝ) = ∑ y ∈ DOM, ((Tup2.filter (fun x => x.1 = y)).card : ℝ) := by
      have hmap : Set.MapsTo Prod.fst (↑Tup2 : Set (((ℤ × ℤ) × (ℤ × ℤ)) × (ℤ × ℤ)))
          (↑DOM : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
        intro x hx
        rw [hTup2def] at hx
        rw [hDOMdef]
        exact (mem_prod54 _ _ x).mp (Finset.mem_filter.mp hx).1 |>.1
      rw [Finset.card_eq_sum_card_fiberwise hmap, Nat.cast_sum]
    have hfib : ∀ y ∈ DOM, (Tup2.filter (fun x => x.1 = y)).card ≤ (Fib y).card := by
      intro y hy
      rw [hFibdef]
      refine Finset.card_le_card_of_injOn (fun x => x.2) ?_ ?_
      · intro x hx
        obtain ⟨hxT, hx1⟩ := Finset.mem_filter.mp hx
        rw [hTup2def] at hxT
        obtain ⟨hxmem, hxcond⟩ := Finset.mem_filter.mp hxT
        rw [hx1] at hxcond
        exact Finset.mem_filter.mpr ⟨(mem_prod54 _ _ x).mp hxmem |>.2, hxcond⟩
      · intro x1 hx1 x2 hx2 h
        obtain ⟨-, e1⟩ := Finset.mem_filter.mp hx1
        obtain ⟨-, e2⟩ := Finset.mem_filter.mp hx2
        exact Prod.ext (e1.trans e2.symm) h
    have hbound : ∀ y ∈ DOM, ((Fib y).card : ℝ) ≤ Bnd y := by
      intro y hy
      rw [hFibdef, hBnddef]
      rw [hDOMdef] at hy
      obtain ⟨hyS, hyC⟩ := (mem_prod54 (Sbox.product Sbox) (Cbox.product Cbox) y).mp hy
      obtain ⟨hyS1, hyS2⟩ := (mem_prod54 Sbox Sbox y.1).mp hyS
      simp only [hBoxdef]
      exact_mod_cast fibre_card_le hKZ0 (s1 := y.1.1) (s2 := y.1.2) (c1 := y.2.1) (c2 := y.2.2)
        hyS1 hyS2
    have hdom : (Tup2.card : ℝ)
        ≤ ∑ s ∈ Sbox.product Sbox, ∑ c ∈ Cbox.product Cbox, Bnd (s, c) := by
      have hd : (Tup2.card : ℝ) ≤ ∑ y ∈ DOM, Bnd y := by
        rw [hcard]
        apply Finset.sum_le_sum; intro y hy
        exact (by exact_mod_cast hfib y hy :
            ((Tup2.filter (fun x => x.1 = y)).card : ℝ) ≤ ((Fib y).card : ℝ)).trans (hbound y hy)
      rw [hDOMdef, sum_prod54] at hd
      exact hd
    have hsplit : ∀ s ∈ Sbox.product Sbox,
        (∑ c ∈ Cbox.product Cbox, Bnd (s, c))
        ≤ A * (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ)
          + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1) * CtauB := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := (mem_prod54 Sbox Sbox s).mp hs
      have hs1ne : s.1 ≠ 0 := (Finset.mem_erase.mp hs1).1
      have hgpos : 0 < s.1.natAbs.gcd s.2.natAbs :=
        Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hs1ne)
      have hbox1 : s.1.natAbs ≤ KZ.natAbs :=
        natAbs_le_natAbs_of_mem_Icc (Finset.mem_erase.mp hs1).2
      have hbox2 : s.2.natAbs ≤ KZ.natAbs :=
        natAbs_le_natAbs_of_mem_Icc (Finset.mem_erase.mp hs2).2
      have hKZle : KZ.natAbs ≤ 4 * C0 := by rw [hKZdef]; exact KZ_le_four_C0l R N hN hRN
      have hS1le : (sS1 s.1 s.2).natAbs ≤ 4 * C0 := by
        rw [sS1_natAbs]; exact (Nat.div_le_self _ _).trans (hbox1.trans hKZle)
      have hS2le : (sS2 s.1 s.2).natAbs ≤ 4 * C0 := by
        rw [sS2_natAbs]; exact (Nat.div_le_self _ _).trans (hbox2.trans hKZle)
      have htau := hCtau (sS2 s.1 s.2) (sS1 s.1 s.2) C0 ((sS_coprime s.1 s.2 hgpos).symm)
        (by rw [hC0def]; exact C0l_pos R N hR (by linarith)) hS2le hS1le
      have hkey : (∑ c ∈ Cbox.product Cbox,
            (if nSt c.1 c.2 s.1 s.2 = 0 then 0
             else ((nSt c.1 c.2 s.1 s.2).natAbs.divisors.card : ℝ)))
          ≤ C_tau * ((C0 : ℝ) + 1) ^ 2 * (Real.log (2 * ((C0 : ℝ) + 2))) ^ 510 := by
        rw [hCboxdef, sum_prod54]
        have heq : (∑ c1 ∈ Finset.Icc (-(C0 : ℤ)) (C0 : ℤ),
              ∑ c2 ∈ Finset.Icc (-(C0 : ℤ)) (C0 : ℤ),
              (if nSt c1 c2 s.1 s.2 = 0 then 0
               else ((nSt c1 c2 s.1 s.2).natAbs.divisors.card : ℝ)))
            = (∑ c1 ∈ Finset.Icc (-(C0 : ℤ)) (C0 : ℤ),
              ∑ c2 ∈ Finset.Icc (-(C0 : ℤ)) (C0 : ℤ),
              (if sS2 s.1 s.2 * c1 ^ 2 - sS1 s.1 s.2 * c2 ^ 2 = 0 then 0
               else (((sS2 s.1 s.2 * c1 ^ 2 - sS1 s.1 s.2 * c2 ^ 2).natAbs).divisors.card
                 : ℝ))) := by
          apply Finset.sum_congr rfl; intro c1 _
          apply Finset.sum_congr rfl; intro c2 _
          rw [nSt_comm c1 c2 s.1 s.2]
        rw [heq]; exact htau
      have hpt : ∀ c ∈ Cbox.product Cbox, Bnd (s, c) ≤
          A * (if nSt c.1 c.2 s.1 s.2 = 0 then (1 : ℝ) else 0)
          + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1)
            * (if nSt c.1 c.2 s.1 s.2 = 0 then 0
               else 2 * ((nSt c.1 c.2 s.1 s.2).natAbs.divisors.card : ℝ)) := by
        intro c hc
        rw [hBnddef, hAdef]
        simp only []
        by_cases h : nSt c.1 c.2 s.1 s.2 = 0
        · simp only [h, if_true, if_false, mul_one, mul_zero, add_zero]
          push_cast
          ring_nf
          exact le_of_eq rfl
        · simp only [h, if_true, if_false, mul_one, mul_zero, add_zero]
          have hle : (((2 * KZ.natAbs / (sS1 s.1 s.2).natAbs + 1 : ℕ)) : ℝ)
              ≤ (2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1 := by
            have hc' := Nat.cast_div_le (α := ℝ) (m := 2 * KZ.natAbs)
              (n := (sS1 s.1 s.2).natAbs)
            push_cast at hc'
            push_cast
            linarith
          have hτ : (0 : ℝ) ≤ ((nSt c.1 c.2 s.1 s.2).natAbs.divisors.card : ℝ) := by positivity
          push_cast
          push_cast at hle
          nlinarith [hle, hτ]
      calc ∑ c ∈ Cbox.product Cbox, Bnd (s, c)
          ≤ ∑ c ∈ Cbox.product Cbox, (A * (if nSt c.1 c.2 s.1 s.2 = 0 then (1 : ℝ) else 0)
              + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1)
                * (if nSt c.1 c.2 s.1 s.2 = 0 then 0
                   else 2 * ((nSt c.1 c.2 s.1 s.2).natAbs.divisors.card : ℝ))) :=
            Finset.sum_le_sum hpt
        _ = A * (∑ c ∈ Cbox.product Cbox, (if nSt c.1 c.2 s.1 s.2 = 0 then (1 : ℝ) else 0))
              + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1)
                * (∑ c ∈ Cbox.product Cbox, (if nSt c.1 c.2 s.1 s.2 = 0 then 0
                    else 2 * ((nSt c.1 c.2 s.1 s.2).natAbs.divisors.card : ℝ))) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = A * (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ)
              + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1)
                * (2 * (∑ c ∈ Cbox.product Cbox, (if nSt c.1 c.2 s.1 s.2 = 0 then 0
                    else ((nSt c.1 c.2 s.1 s.2).natAbs.divisors.card : ℝ)))) := by
            have e1 : (∑ c ∈ Cbox.product Cbox,
                  (if nSt c.1 c.2 s.1 s.2 = 0 then (1 : ℝ) else 0))
                = (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ) :=
              Finset.sum_boole _ _
            have e2 : (∑ c ∈ Cbox.product Cbox, (if nSt c.1 c.2 s.1 s.2 = 0 then 0
                  else 2 * ((nSt c.1 c.2 s.1 s.2).natAbs.divisors.card : ℝ)))
                = 2 * (∑ c ∈ Cbox.product Cbox, (if nSt c.1 c.2 s.1 s.2 = 0 then 0
                    else ((nSt c.1 c.2 s.1 s.2).natAbs.divisors.card : ℝ))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro c _
              by_cases h : nSt c.1 c.2 s.1 s.2 = 0 <;>
                simp only [h, if_true, if_false, mul_zero]
            rw [e1, e2]
        _ ≤ A * (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ)
              + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1)
                * (2 * (C_tau * ((C0 : ℝ) + 1) ^ 2
                    * (Real.log (2 * ((C0 : ℝ) + 2))) ^ 510)) := by
            apply add_le_add_right
            apply mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith [hkey]
        _ = A * (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ)
              + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1) * CtauB := by
            rw [hCtauBdef]; ring
    have hsum : (∑ s ∈ Sbox.product Sbox, ∑ c ∈ Cbox.product Cbox, Bnd (s, c))
        ≤ ∑ s ∈ Sbox.product Sbox,
            (A * (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ)
              + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1) * CtauB) :=
      Finset.sum_le_sum hsplit
    have hT0 : (∑ s ∈ Sbox.product Sbox,
          (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ))
        ≤ C_r * ((KZ.natAbs : ℝ) + 1) * ((KZ.natAbs : ℝ) + 1 + ((C0 : ℝ) + 1)) := by
      have hCR : (CRset KZ.natAbs C0).card
          ≤ C_r * ((KZ.natAbs : ℝ) + 1) * ((KZ.natAbs : ℝ) + 1 + ((C0 : ℝ) + 1)) :=
        hCr KZ.natAbs C0
      have h2 : (((Sbox.product Sbox).product (Cbox.product Cbox)).filter
            (fun q : (ℤ × ℤ) × (ℤ × ℤ) => nSt q.2.1 q.2.2 q.1.1 q.1.2 = 0))
          = CRset KZ.natAbs C0 := by
        rw [hSboxdef, hBoxdef, hCboxdef]
        unfold CRset
        rw [Int.natAbs_of_nonneg hKZ0]
        ext q
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hm, h0⟩
          refine ⟨hm, ?_⟩
          have hne := nSt_eq q.2.1 q.2.2 q.1.1 q.1.2
          rw [h0, mul_zero] at hne
          linarith
        · rintro ⟨hm, h0⟩
          have hs1 : q.1.1 ≠ 0 := by
            have hp1 : q.1.1 ∈ (Finset.Icc (-KZ) KZ).erase 0 :=
              ((mem_prod54 _ _ q.1).mp ((mem_prod54 _ _ q).mp hm).1).1
            exact (Finset.mem_erase.mp hp1).1
          refine ⟨hm, ?_⟩
          have hne := nSt_eq q.2.1 q.2.2 q.1.1 q.1.2
          rw [h0] at hne
          rw [sub_self] at hne
          have hg : (((q.1.1.natAbs.gcd q.1.2.natAbs : ℕ)) : ℤ) ≠ 0 := by
            exact_mod_cast (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr hs1)).ne'
          exact (mul_eq_zero.mp hne.symm).resolve_left hg
      have h1 : (∑ s ∈ Sbox.product Sbox,
            ((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card)
          = (CRset KZ.natAbs C0).card := by
        rw [(card_filter_product (Sbox.product Sbox) (Cbox.product Cbox)
              (fun q => nSt q.2.1 q.2.2 q.1.1 q.1.2 = 0)).symm, h2]
      rw [← Nat.cast_sum, h1]
      exact_mod_cast hCR
    have hharm : (∑ s ∈ Sbox.product Sbox, ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1))
        ≤ 2 * (KZ.natAbs : ℝ) * C_h * ((KZ.natAbs : ℝ) + 1)
            * (Real.log ((KZ.natAbs : ℝ) + 2)) ^ 2
          + (2 * (KZ.natAbs : ℝ)) ^ 2 := by
      have hHsub : (∑ s ∈ Sbox.product Sbox, (((sS1 s.1 s.2).natAbs : ℝ))⁻¹)
          ≤ C_h * ((KZ.natAbs : ℝ) + 1) * (Real.log ((KZ.natAbs : ℝ) + 2)) ^ 2 := by
        rw [hSboxdef, hBoxdef, sum_prod54]
        rw [show Finset.Icc (-KZ) KZ = Finset.Icc (-((KZ.natAbs : ℤ))) ((KZ.natAbs : ℤ)) from by
          rw [Int.natAbs_of_nonneg hKZ0]]
        refine le_trans ?_ (hCh KZ.natAbs)
        apply Finset.sum_le_sum; intro s1 _
        apply Finset.sum_le_sum; intro s2 _
        rw [sS1_natAbs]
      have hScard : Sbox.card = 2 * KZ.natAbs := by
        rw [hSboxdef, hBoxdef,
          Finset.card_erase_of_mem (by rw [Finset.mem_Icc]; exact ⟨by linarith [hKZ0], hKZ0⟩)]
        rw [box_card KZ hKZ0]
        omega
      have hcard2 : (∑ _s ∈ Sbox.product Sbox, (1 : ℝ)) = (2 * (KZ.natAbs : ℝ)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_prod54, hScard]
        push_cast
        ring
      have h1 : (∑ s ∈ Sbox.product Sbox, (2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs)
          = (2 * (KZ.natAbs : ℝ))
              * (∑ s ∈ Sbox.product Sbox, (((sS1 s.1 s.2).natAbs : ℝ))⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        rw [div_eq_mul_inv]
      have hstep : (2 * (KZ.natAbs : ℝ))
            * (∑ s ∈ Sbox.product Sbox, (((sS1 s.1 s.2).natAbs : ℝ))⁻¹)
          ≤ 2 * (KZ.natAbs : ℝ) * C_h * ((KZ.natAbs : ℝ) + 1)
              * (Real.log ((KZ.natAbs : ℝ) + 2)) ^ 2 := by
        calc (2 * (KZ.natAbs : ℝ))
              * (∑ s ∈ Sbox.product Sbox, (((sS1 s.1 s.2).natAbs : ℝ))⁻¹)
            ≤ (2 * (KZ.natAbs : ℝ))
                * (C_h * ((KZ.natAbs : ℝ) + 1) * (Real.log ((KZ.natAbs : ℝ) + 2)) ^ 2) :=
              mul_le_mul_of_nonneg_left hHsub (by positivity)
          _ = 2 * (KZ.natAbs : ℝ) * C_h * ((KZ.natAbs : ℝ) + 1)
                * (Real.log ((KZ.natAbs : ℝ) + 2)) ^ 2 := by ring
      rw [Finset.sum_add_distrib, h1, hcard2]
      linarith [hstep]
    have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
    have htau0 : (0 : ℝ) ≤ CtauB := by rw [hCtauBdef]; positivity
    calc (Tup2.card : ℝ)
        ≤ ∑ s ∈ Sbox.product Sbox, ∑ c ∈ Cbox.product Cbox, Bnd (s, c) := hdom
      _ ≤ ∑ s ∈ Sbox.product Sbox,
            (A * (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ)
              + ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1) * CtauB) := hsum
      _ = A * (∑ s ∈ Sbox.product Sbox,
              (((Cbox.product Cbox).filter (fun c => nSt c.1 c.2 s.1 s.2 = 0)).card : ℝ))
            + CtauB * (∑ s ∈ Sbox.product Sbox,
                ((2 * KZ.natAbs : ℝ) / (sS1 s.1 s.2).natAbs + 1)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          rw [Finset.sum_add_distrib]
          congr 1 <;> (apply Finset.sum_congr rfl; intro s _; ring)
      _ ≤ A * (C_r * ((KZ.natAbs : ℝ) + 1) * ((KZ.natAbs : ℝ) + 1 + ((C0 : ℝ) + 1)))
            + CtauB * (2 * (KZ.natAbs : ℝ) * C_h * ((KZ.natAbs : ℝ) + 1)
                * (Real.log ((KZ.natAbs : ℝ) + 2)) ^ 2 + (2 * (KZ.natAbs : ℝ)) ^ 2) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hT0 hA0)
            (mul_le_mul_of_nonneg_left hharm htau0)
      _ ≤ 2 * C_tau * ((C0 : ℝ) + 1) ^ 2 * (Real.log (2 * ((C0 : ℝ) + 2))) ^ 510
            * (2 * (KZ.natAbs : ℝ) * C_h * ((KZ.natAbs : ℝ) + 1)
                * (Real.log ((KZ.natAbs : ℝ) + 2)) ^ 2 + 4 * (KZ.natAbs : ℝ) ^ 2)
          + C_r * ((KZ.natAbs : ℝ) + 1) * ((KZ.natAbs : ℝ) + 2 + (C0 : ℝ))
              * (2 * (KZ.natAbs : ℝ) + 1) ^ 2 := by
          rw [hAdef, hCtauBdef]
          apply le_of_eq
          push_cast
          ring
  have hC0bd : ((C0 : ℝ) + 1) ≤ 2 * Real.sqrt ((R.natAbs : ℝ) * Real.sqrt N) + 3 := by
    have hlt : (C0 : ℝ) < Real.sqrt (4 * (R.natAbs : ℝ) * Real.sqrt N) + 1 := by
      rw [hC0def]
      exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    have h4 : Real.sqrt (4 * (R.natAbs : ℝ) * Real.sqrt N)
        = 2 * Real.sqrt ((R.natAbs : ℝ) * Real.sqrt N) := by
      rw [show (4 : ℝ) * (R.natAbs : ℝ) * Real.sqrt N
            = (2 : ℝ) ^ 2 * ((R.natAbs : ℝ) * Real.sqrt N) by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have hMbd : ((KZ.natAbs : ℝ) + 1) ≤ 3 * Real.sqrt N + 3 := by
    have hlt : (KZ.natAbs : ℝ) < Real.sqrt (2 * N) + 1 := by
      rw [hKZdef, KZ_natAbs]
      exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (2 * N) ≤ 2 * Real.sqrt N := by
      have h := Real.sqrt_le_sqrt (show (2 : ℝ) * N ≤ 4 * N by
        nlinarith [Real.sqrt_nonneg N, hN])
      rw [show (4 : ℝ) * N = (2 : ℝ) ^ 2 * N by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
      exact h
    have hs1 : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by linarith)
    linarith
  have hfin := offdiag_final_l51 R N C0 (KZ.natAbs) C_tau C_h C_r hR hN hRN
    (by rw [hC0def]; exact C0l_pos R N hR (by linarith)) hC0bd hMbd
    hCtau_pos hCh_pos hCr_pos
  exact (hstep1.trans hstep2).trans (hstep3.trans hfin)