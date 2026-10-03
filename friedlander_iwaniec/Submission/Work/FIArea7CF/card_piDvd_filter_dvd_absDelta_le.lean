import Mathlib
import Submission.Work.FIArea7.PiPairDefs
import Submission.Work.FIArea7CF.card_gBox_filter_dvd_absDelta

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Helpers: scaling of Delta by a common Gaussian factor -/

/-- Delta(pi z, pi w) = |pi|^2 Delta(z,w). -/
lemma Delta_mul_mul (π z w : GaussianInt) :
    Work.FIPlan.Delta (π * z) (π * w) = (Work.FIPlan.gnorm π : ℤ) * Work.FIPlan.Delta z w := by
  have hsp : star π * π = ((Work.FIPlan.gnorm π : ℤ) : GaussianInt) := by
    rw [mul_comm (star π) π, ← Zsqrtd.norm_eq_mul_conj]
    congr 1
    exact (GaussianInt.abs_natCast_norm π).symm
  rw [Work.FIPlan.Delta]
  have hmul : star (π * z) * (π * w)
      = ((Work.FIPlan.gnorm π : ℤ) : GaussianInt) * (star z * w) := by
    rw [star_mul, ← hsp]
    ring
  rw [hmul, Zsqrtd.im_smul]
  rfl

/-- |Delta(pi z, pi w)| = |pi|^2 |Delta(z,w)|. -/
lemma absDelta_mul_mul (π z w : GaussianInt) :
    Work.FIPlan.absDelta (π * z) (π * w) = Work.FIPlan.gnorm π * Work.FIPlan.absDelta z w := by
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, Delta_mul_mul, Int.natAbs_mul,
    Int.natAbs_natCast]

/-! ## Helper: the pi-sublattice of the box sits in the shrunk box -/

/-- If pi*w lies in the box gBox R (0 <= R, pi != 0) then w lies in the shrunk box
gBox (floor (R*sqrt 2 / sqrt (gnorm pi))). -/
lemma mem_gBox_shrunk_of_mul_mem (π w : GaussianInt) (R : ℤ) (hR : 0 ≤ R) (hπ : π ≠ 0)
    (h : π * w ∈ Work.FIPlan.gBox R) :
    w ∈ Work.FIPlan.gBox ((shrunkNat R π : ℕ) : ℤ) := by
  obtain ⟨h1, h2, h3, h4⟩ := cf_mem_gBox_iff.mp h
  have hgnorm_pos : 0 < Work.FIPlan.gnorm π := by
    rw [Work.FIPlan.gnorm]
    exact Int.natAbs_pos.mpr (ne_of_gt ((GaussianInt.norm_pos).mpr hπ))
  have hgR : ((Work.FIPlan.gnorm π : ℕ) : ℝ) = (π.re : ℝ) ^ 2 + (π.im : ℝ) ^ 2 := by
    have hZ : (Work.FIPlan.gnorm π : ℤ) = π.re ^ 2 + π.im ^ 2 := by
      rw [Work.FIPlan.gnorm, GaussianInt.abs_natCast_norm, Zsqrtd.norm_def]
      ring
    exact_mod_cast hZ
  have hnormeq : ((π * w).re : ℝ) ^ 2 + ((π * w).im : ℝ) ^ 2
      = ((π.re : ℝ) ^ 2 + (π.im : ℝ) ^ 2) * ((w.re : ℝ) ^ 2 + (w.im : ℝ) ^ 2) := by
    have hZ : (π * w).re ^ 2 + (π * w).im ^ 2 = (π.re ^ 2 + π.im ^ 2) * (w.re ^ 2 + w.im ^ 2) := by
      rw [Zsqrtd.re_mul, Zsqrtd.im_mul]
      ring
    exact_mod_cast hZ
  have hRnn : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hPabs : |((π * w).re : ℝ)| ≤ (R : ℝ) := by
    rw [abs_le]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hQabs : |((π * w).im : ℝ)| ≤ (R : ℝ) := by
    rw [abs_le]
    exact ⟨by exact_mod_cast h3, by exact_mod_cast h4⟩
  have hP2 : ((π * w).re : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hRnn]; exact hPabs
  have hQ2 : ((π * w).im : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hRnn]; exact hQabs
  have hsumPQ : ((π * w).re : ℝ) ^ 2 + ((π * w).im : ℝ) ^ 2 ≤ 2 * (R : ℝ) ^ 2 := by linarith
  have hgposR : (0 : ℝ) < ((Work.FIPlan.gnorm π : ℕ) : ℝ) := by exact_mod_cast hgnorm_pos
  have hkey : ((Work.FIPlan.gnorm π : ℕ) : ℝ) * ((w.re : ℝ) ^ 2 + (w.im : ℝ) ^ 2)
      = ((π * w).re : ℝ) ^ 2 + ((π * w).im : ℝ) ^ 2 := by
    rw [hgR, hnormeq]
  have hxG : (w.re : ℝ) ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
    have hle : (w.re : ℝ) ^ 2 ≤ (w.re : ℝ) ^ 2 + (w.im : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (w.im : ℝ)]
    have h2 : (w.re : ℝ) ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℝ)
        ≤ ((w.re : ℝ) ^ 2 + (w.im : ℝ) ^ 2) * ((Work.FIPlan.gnorm π : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hgposR)
    have h3 : ((w.re : ℝ) ^ 2 + (w.im : ℝ) ^ 2) * ((Work.FIPlan.gnorm π : ℕ) : ℝ)
        = ((π * w).re : ℝ) ^ 2 + ((π * w).im : ℝ) ^ 2 := by
      rw [mul_comm]; exact hkey
    linarith [h2, h3, hsumPQ]
  have hyG : (w.im : ℝ) ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
    have hle : (w.im : ℝ) ^ 2 ≤ (w.re : ℝ) ^ 2 + (w.im : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (w.re : ℝ)]
    have h2 : (w.im : ℝ) ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℝ)
        ≤ ((w.re : ℝ) ^ 2 + (w.im : ℝ) ^ 2) * ((Work.FIPlan.gnorm π : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hgposR)
    have h3 : ((w.re : ℝ) ^ 2 + (w.im : ℝ) ^ 2) * ((Work.FIPlan.gnorm π : ℕ) : ℝ)
        = ((π * w).re : ℝ) ^ 2 + ((π * w).im : ℝ) ^ 2 := by
      rw [mul_comm]; exact hkey
    linarith [h2, h3, hsumPQ]
  have hsqa : ((w.re : ℝ) * Real.sqrt ((Work.FIPlan.gnorm π : ℕ) : ℝ)) ^ 2
      ≤ ((R : ℝ) * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hgposR),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [hxG]
  have hsqb : ((w.im : ℝ) * Real.sqrt ((Work.FIPlan.gnorm π : ℕ) : ℝ)) ^ 2
      ≤ ((R : ℝ) * Real.sqrt 2) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hgposR),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith [hyG]
  have hxabs : |(w.re : ℝ)| * Real.sqrt ((Work.FIPlan.gnorm π : ℕ) : ℝ)
      ≤ (R : ℝ) * Real.sqrt 2 := by
    have h := sq_le_sq.mp hsqa
    rwa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg ((Work.FIPlan.gnorm π : ℕ) : ℝ)),
      abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg hRnn] at h
  have hyabs : |(w.im : ℝ)| * Real.sqrt ((Work.FIPlan.gnorm π : ℕ) : ℝ)
      ≤ (R : ℝ) * Real.sqrt 2 := by
    have h := sq_le_sq.mp hsqb
    rwa [abs_mul, abs_of_nonneg (Real.sqrt_nonneg ((Work.FIPlan.gnorm π : ℕ) : ℝ)),
      abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg hRnn] at h
  have hxle : |(w.re : ℝ)|
      ≤ (R : ℝ) * Real.sqrt 2 / Real.sqrt ((Work.FIPlan.gnorm π : ℕ) : ℝ) := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hgposR)]
    exact hxabs
  have hyle : |(w.im : ℝ)|
      ≤ (R : ℝ) * Real.sqrt 2 / Real.sqrt ((Work.FIPlan.gnorm π : ℕ) : ℝ) := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hgposR)]
    exact hyabs
  have hcast_re : ((w.re.natAbs : ℕ) : ℝ) = |(w.re : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hcast_im : ((w.im.natAbs : ℕ) : ℝ) = |(w.im : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hxfloor : w.re.natAbs ≤ shrunkNat R π := by
    rw [shrunkNat]
    apply Nat.le_floor
    rw [hcast_re]
    exact hxle
  have hyfloor : w.im.natAbs ≤ shrunkNat R π := by
    rw [shrunkNat]
    apply Nat.le_floor
    rw [hcast_im]
    exact hyle
  have hxZ : |w.re| ≤ ((shrunkNat R π : ℕ) : ℤ) := by
    have h := show ((w.re.natAbs : ℕ) : ℤ) ≤ ((shrunkNat R π : ℕ) : ℤ) by exact_mod_cast hxfloor
    rwa [Int.natCast_natAbs] at h
  have hyZ : |w.im| ≤ ((shrunkNat R π : ℕ) : ℤ) := by
    have h := show ((w.im.natAbs : ℕ) : ℤ) ≤ ((shrunkNat R π : ℕ) : ℤ) by exact_mod_cast hyfloor
    rwa [Int.natCast_natAbs] at h
  rw [cf_mem_gBox_iff]
  exact ⟨(abs_le.mp hxZ).1, (abs_le.mp hxZ).2, (abs_le.mp hyZ).1, (abs_le.mp hyZ).2⟩

/-! ## Helper: the witness w with pi*w = z -/

/-- A choice of w with pi*w = z when pi divides z, and 0 otherwise. -/
def piWit (π z : GaussianInt) : GaussianInt :=
  if h : π ∣ z then Classical.choose h else 0

lemma piWit_mul_eq {π z : GaussianInt} (h : π ∣ z) : π * piWit π z = z := by
  simp only [piWit, dif_pos h]
  exact (Classical.choose_spec h).symm

/-! ## The main count -/

theorem card_piDvd_filter_dvd_absDelta_le (π z1' : GaussianInt) (R : ℤ) (hR : 0 ≤ R) (hπ : π ≠ 0)
    (c : ℕ) (hc : 0 < c) (hcop : IsCoprime z1'.re (c : ℤ))
    (hPc : Nat.Coprime (Work.FIPlan.gnorm π) c) :
    (((Work.FIArea7.piDvdAbsDeltaFinset π z1' R c).card : ℕ) : ℝ)
      ≤ ((Work.FIArea7.rhoPi R π : ℝ)) * ((Work.FIArea7.rhoPi R π : ℝ) / c + 1) := by
  set S : Finset GaussianInt := piDvdAbsDeltaFinset π z1' R c with hS
  set T : Finset GaussianInt :=
    (Work.FIPlan.gBox ((shrunkNat R π : ℕ) : ℤ)).filter
      (fun w => c ∣ Work.FIPlan.absDelta z1' w) with hT
  have hmemS : ∀ {z2 : GaussianInt}, z2 ∈ S →
      z2 ∈ (Work.FIPlan.gBox R).filter
        (fun z => π ∣ z ∧ c ∣ Work.FIPlan.absDelta (π * z1') z) := by
    intro z2 hz2
    rw [hS, Work.FIArea7.piDvdAbsDeltaFinset] at hz2
    exact hz2
  have hwit : ∀ z2 ∈ S, π * piWit π z2 = z2 := by
    intro z2 hz2
    exact piWit_mul_eq (Finset.mem_filter.mp (hmemS hz2)).2.1
  have hinj : Set.InjOn (piWit π) (↑S : Set GaussianInt) := by
    intro z2 hz2 z2' hz2' heq
    simp only [Finset.mem_coe] at hz2 hz2'
    rw [← hwit z2 hz2, ← hwit z2' hz2', heq]
  have hmaps : Set.MapsTo (piWit π) (↑S : Set GaussianInt) (↑T : Set GaussianInt) := by
    intro z2 hz2
    simp only [Finset.mem_coe] at hz2 ⊢
    obtain ⟨hz2box, _hdvd, hcdvd⟩ := Finset.mem_filter.mp (hmemS hz2)
    have hmul : π * piWit π z2 = z2 := hwit z2 hz2
    rw [hT, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · exact mem_gBox_shrunk_of_mul_mem π (piWit π z2) R hR hπ (hmul.symm ▸ hz2box)
    · have h := hcdvd
      rw [← hmul, absDelta_mul_mul] at h
      exact hPc.symm.dvd_of_dvd_mul_left h
  have hcard : S.card ≤ T.card := Finset.card_le_card_of_injOn (piWit π) hmaps hinj
  have hTcard : T.card ≤ (2 * shrunkNat R π + 1) * ((2 * shrunkNat R π + 1) / c + 1) := by
    have htoNat : (2 * ((shrunkNat R π : ℕ) : ℤ) + 1).toNat = 2 * shrunkNat R π + 1 := by
      rw [show (2 * ((shrunkNat R π : ℕ) : ℤ) + 1) = ((2 * shrunkNat R π + 1 : ℕ) : ℤ) by
            push_cast; ring]
      exact Int.toNat_natCast _
    have hb := card_gBox_filter_dvd_absDelta z1' ((shrunkNat R π : ℕ) : ℤ) c hc hcop
    simpa [htoNat] using hb
  have hSle : S.card ≤ (2 * shrunkNat R π + 1) * ((2 * shrunkNat R π + 1) / c + 1) :=
    le_trans hcard hTcard
  rw [Work.FIArea7.rhoPi]
  have hmain : ((S.card : ℕ) : ℝ)
      ≤ ((2 * shrunkNat R π + 1 : ℕ) : ℝ) * (((2 * shrunkNat R π + 1 : ℕ) : ℝ) / c + 1) := by
    have hcast : ((S.card : ℕ) : ℝ)
        ≤ (((2 * shrunkNat R π + 1) * ((2 * shrunkNat R π + 1) / c + 1) : ℕ) : ℝ) := by
      exact_mod_cast hSle
    have hEq : (((2 * shrunkNat R π + 1) * ((2 * shrunkNat R π + 1) / c + 1) : ℕ) : ℝ)
        = ((2 * shrunkNat R π + 1 : ℕ) : ℝ)
          * ((((2 * shrunkNat R π + 1) / c : ℕ) : ℝ) + 1) := by
      push_cast; ring
    rw [hEq] at hcast
    refine le_trans hcast ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hd : (((2 * shrunkNat R π + 1) / c : ℕ) : ℝ)
        ≤ ((2 * shrunkNat R π + 1 : ℕ) : ℝ) / (c : ℝ) := Nat.cast_div_le
    exact add_le_add hd le_rfl
  exact hmain

end

end Work.FIArea7
