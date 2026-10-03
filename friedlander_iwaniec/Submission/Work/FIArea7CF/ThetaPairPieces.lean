import Mathlib
import Submission.Work.FIArea7CF.card_gBox_filter_dvd_absDelta
import Submission.Work.FIArea7CF.card_piDvd_filter_dvd_absDelta_le
import Submission.Work.FIArea7.PiPairDefs
import Submission.Work.FIArea7.PiPairAux
import Submission.Work.FIArea7.pairMass_fibre_le
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Commons.NumberTheory.Int.ncard_int_residue_class_sq_le
import Submission.Work.FIArea7.SumMassDefs
import Submission.Work.FIArea7CF.uniMode_pairMass_le
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Work.FIArea3.card_polarBox_filter_dvd_absDelta_gcd

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem card_gBox_filter_dvd_absDelta_gcd (z1 : GaussianInt) (R : ℤ) (hR : 0 ≤ R) (c : ℕ)
    (hc : 0 < c)
    (hcop : Nat.Coprime (Nat.gcd z1.re.natAbs z1.im.natAbs) c) :
    (((Work.FIPlan.gBox R).filter (fun z2 => c ∣ Work.FIPlan.absDelta z1 z2)).card : ℝ)
      ≤ 16 * (((2 * R + 1).toNat : ℝ) * (((2 * R + 1).toNat : ℝ) / c + 1)) := by
  classical
  set SB : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z2 => c ∣ Work.FIPlan.absDelta z1 z2) with hSB
  set g : ℕ := Nat.gcd z1.re.natAbs c with hgdef
  set d : ℕ := c / g with hddef
  have hgd : g ∣ c := by rw [hgdef]; exact Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hc
  have hgle : g ≤ c := Nat.gcd_le_right _ hc
  have hdpos : 0 < d := by rw [hddef]; exact Nat.div_pos hgle hgpos
  have hgdc : g * d = c := by rw [hddef, mul_comm]; exact Nat.div_mul_cancel hgd
  have hcop_im : Nat.Coprime g z1.im.natAbs := by
    rw [hgdef, Nat.coprime_iff_gcd_eq_one]
    have h1 : Nat.gcd (Nat.gcd z1.re.natAbs z1.im.natAbs) c = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hcop
    rw [Nat.gcd_assoc, Nat.gcd_comm z1.im.natAbs c, ← Nat.gcd_assoc] at h1
    exact h1
  have hg_dvd_re : (g : ℤ) ∣ z1.re := by
    rw [hgdef]
    exact Int.dvd_natAbs.mp (Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _))
  have hcong_fact : ∀ y1 y2 : ℤ, (c : ℤ) ∣ z1.re * (y1 - y2) → (d : ℤ) ∣ (y1 - y2) := by
    intro y1 y2 h
    have h' := Work.FIArea3.dvd_div_gcd_of_dvd_mul hc h
    rw [← hgdef, ← hddef] at h'
    exact h'
  have hmaps : Set.MapsTo (fun z : GaussianInt => z.re) (↑SB : Set GaussianInt)
      (↑(Finset.Icc (-R) R) : Set ℤ) := by
    intro z hz
    rw [Finset.mem_coe, hSB, Finset.mem_filter] at hz
    have h := Work.FIArea7.cf_mem_gBox_iff.mp hz.1
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hrow : ∀ x ∈ Finset.Icc (-R) R,
      ((SB.filter (fun z => z.re = x)).card : ℝ)
        ≤ (if (g : ℤ) ∣ x then ((2 * R + 1).toNat : ℝ) / (d : ℝ) + 1 else 0) := by
    intro x hx
    by_cases hgx : (g : ℤ) ∣ x
    · rw [if_pos hgx]
      set Y : Finset ℤ := (SB.filter (fun z => z.re = x)).image (fun z => z.im) with hY
      have hYcard : Y.card = (SB.filter (fun z => z.re = x)).card := by
        rw [hY]
        refine Finset.card_image_of_injOn ?_
        intro a ha b hb hab
        have ha' : a ∈ SB ∧ a.re = x := Finset.mem_filter.mp ha
        have hb' : b ∈ SB ∧ b.re = x := Finset.mem_filter.mp hb
        exact Zsqrtd.ext (by rw [ha'.2, hb'.2]) hab
      have hsub : ∀ y ∈ Y, y ∈ Finset.Icc (-R) R := by
        intro y hy
        rw [hY] at hy
        obtain ⟨z, hzF, rfl⟩ := Finset.mem_image.mp hy
        have hz' : z ∈ SB ∧ z.re = x := Finset.mem_filter.mp hzF
        have hzg : z ∈ Work.FIPlan.gBox R := (Finset.mem_filter.mp hz'.1).1
        have h := Work.FIArea7.cf_mem_gBox_iff.mp hzg
        exact Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2⟩
      have hcong : ∀ y1 ∈ Y, ∀ y2 ∈ Y, ((d : ℕ) : ℤ) ∣ y1 - y2 := by
        intro y1 hy1 y2 hy2
        rw [hY] at hy1 hy2
        obtain ⟨zA, hzA, rfl⟩ := Finset.mem_image.mp hy1
        obtain ⟨zB, hzB, rfl⟩ := Finset.mem_image.mp hy2
        have hzA' : zA ∈ SB ∧ zA.re = x := Finset.mem_filter.mp hzA
        have hzB' : zB ∈ SB ∧ zB.re = x := Finset.mem_filter.mp hzB
        have hdA : c ∣ Work.FIPlan.absDelta z1 zA := (Finset.mem_filter.mp hzA'.1).2
        have hdB : c ∣ Work.FIPlan.absDelta z1 zB := (Finset.mem_filter.mp hzB'.1).2
        have hdA' : (c : ℤ) ∣ z1.re * zA.im - z1.im * zA.re := by
          simpa [Work.FIArea7.Delta_eq z1 zA] using Work.FIArea7.dvd_Delta_of_dvd_absDelta hdA
        have hdB' : (c : ℤ) ∣ z1.re * zB.im - z1.im * zB.re := by
          simpa [Work.FIArea7.Delta_eq z1 zB] using Work.FIArea7.dvd_Delta_of_dvd_absDelta hdB
        have hkey : (c : ℤ) ∣ z1.re * (zA.im - zB.im) := by
          have h := dvd_sub hdA' hdB'
          have he : z1.re * zA.im - z1.im * zA.re - (z1.re * zB.im - z1.im * zB.re)
              = z1.re * (zA.im - zB.im) := by rw [hzA'.2, hzB'.2]; ring
          rwa [he] at h
        exact hcong_fact zA.im zB.im hkey
      have hle : Y.card ≤ (2 * R + 1).toNat / d + 1 :=
        Work.FIArea7.card_le_div_of_pairwise_dvd R d hdpos Y hsub hcong
      rw [← hYcard]
      have h1 : ((Y.card : ℕ) : ℝ) ≤ ((((2 * R + 1).toNat / d + 1 : ℕ)) : ℝ) := by
        exact_mod_cast hle
      push_cast at h1
      have h3 : ((((2 * R + 1).toNat / d : ℕ)) : ℝ) ≤ ((2 * R + 1).toNat : ℝ) / (d : ℝ) :=
        Nat.cast_div_le (α := ℝ)
      linarith
    · rw [if_neg hgx]
      have hemp : SB.filter (fun z => z.re = x) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr ?_
        intro z hzS hzre
        have hd : c ∣ Work.FIPlan.absDelta z1 z := (Finset.mem_filter.mp hzS).2
        have hd' : (c : ℤ) ∣ z1.re * z.im - z1.im * z.re := by
          simpa [Work.FIArea7.Delta_eq z1 z] using Work.FIArea7.dvd_Delta_of_dvd_absDelta hd
        rw [hzre] at hd'
        have hg_dvd_c : (g : ℤ) ∣ (c : ℤ) := Int.ofNat_dvd.mpr hgd
        have hgm : (g : ℤ) ∣ z1.im * x := by
          have h1 : (g : ℤ) ∣ z1.re * z.im - z1.im * x := hg_dvd_c.trans hd'
          have h2 : (g : ℤ) ∣ z1.re * z.im := hg_dvd_re.mul_right z.im
          have h3 := dvd_sub h1 h2
          simpa using h3
        have hcopI : IsCoprime (g : ℤ) z1.im := by
          rw [Int.isCoprime_iff_nat_coprime]
          simpa using hcop_im
        have hgx' : (g : ℤ) ∣ x := by
          have hmul : (g : ℤ) ∣ x * z1.im := by rwa [mul_comm] at hgm
          exact hcopI.dvd_of_dvd_mul_right hmul
        exact hgx hgx'
      rw [hemp]; simp
  have hsum1 : (SB.card : ℝ)
      ≤ (((Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x)).card : ℝ)
          * (((2 * R + 1).toNat : ℝ) / (d : ℝ) + 1) := by
    have hstep : (∑ x ∈ Finset.Icc (-R) R, ((SB.filter (fun z => z.re = x)).card : ℝ))
        ≤ ∑ x ∈ Finset.Icc (-R) R,
            (if (g : ℤ) ∣ x then ((2 * R + 1).toNat : ℝ) / (d : ℝ) + 1 else 0) :=
      Finset.sum_le_sum hrow
    have hsum2 : (∑ x ∈ Finset.Icc (-R) R,
        (if (g : ℤ) ∣ x then ((2 * R + 1).toNat : ℝ) / (d : ℝ) + 1 else 0))
        = (((Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x)).card : ℝ)
          * (((2 * R + 1).toNat : ℝ) / (d : ℝ) + 1) := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcast : ((SB.card : ℕ) : ℝ)
        = ∑ x ∈ Finset.Icc (-R) R, ((SB.filter (fun z => z.re = x)).card : ℝ) := by
      rw [hcard]; push_cast; rfl
    rw [hcast, ← hsum2]
    exact hstep
  have hTxcard : (((Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x)).card : ℝ)
      ≤ ((2 * R + 1).toNat : ℝ) / (g : ℝ) + 1 := by
    have hsub : ∀ x ∈ (Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x),
        x ∈ Finset.Icc (-R) R := fun x hx => (Finset.mem_filter.mp hx).1
    have hcong : ∀ x ∈ (Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x),
        ∀ y ∈ (Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x), (g : ℤ) ∣ x - y := by
      intro x hx y hy
      exact dvd_sub (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    have hle := Work.FIArea7.card_le_div_of_pairwise_dvd R g hgpos
      ((Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x)) hsub hcong
    have h1 : ((((Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x)).card : ℕ) : ℝ)
        ≤ ((((2 * R + 1).toNat / g + 1 : ℕ)) : ℝ) := by exact_mod_cast hle
    push_cast at h1
    have h3 := Nat.cast_div_le (α := ℝ) (m := (2 * R + 1).toNat) (n := g)
    linarith
  set N : ℝ := ((2 * R + 1).toNat : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := by
    rw [hNdef]
    have h0 : (0 : ℤ) ≤ 2 * R + 1 := by linarith
    have h1 : (1 : ℤ) ≤ (((2 * R + 1).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; linarith
    exact_mod_cast h1
  have hN0 : (0 : ℝ) ≤ N := le_trans zero_le_one hN1
  have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hgpos
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  have hgdcR : (g : ℝ) * (d : ℝ) = (c : ℝ) := by rw [← Nat.cast_mul, hgdc]
  have hsplit : (N / (g : ℝ) + 1) * (N / (d : ℝ) + 1)
      = N ^ 2 / (c : ℝ) + N / (g : ℝ) + N / (d : ℝ) + 1 := by
    rw [← hgdcR]
    field_simp
    ring
  calc (SB.card : ℝ)
      ≤ (((Finset.Icc (-R) R).filter (fun x => (g : ℤ) ∣ x)).card : ℝ)
          * ((2 * R + 1).toNat / (d : ℝ) + 1) := hsum1
    _ ≤ ((2 * R + 1).toNat / (g : ℝ) + 1) * ((2 * R + 1).toNat / (d : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right hTxcard
        positivity
    _ = N ^ 2 / (c : ℝ) + N / (g : ℝ) + N / (d : ℝ) + 1 := by
        rw [← hNdef]; exact hsplit
    _ ≤ 16 * (N * (N / (c : ℝ) + 1)) := by
        have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
        have hNg : N / (g : ℝ) ≤ N := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (g : ℝ))]
          nlinarith [hN0, hg1]
        have hNd : N / (d : ℝ) ≤ N := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (d : ℝ))]
          nlinarith [hN0, hd1]
        have hNsq : (0 : ℝ) ≤ N ^ 2 / (c : ℝ) := div_nonneg (sq_nonneg N) (le_of_lt hc0)
        have hrhs : 16 * (N * (N / (c : ℝ) + 1)) = 16 * (N ^ 2 / (c : ℝ)) + 16 * N := by ring
        rw [hrhs]
        nlinarith [hN1, hNsq, hNg, hNd, hN0]

lemma gnorm_factor (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  have h := Work.FIArea7.norm_eq z
  have h2 : ((z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℕ) : ℤ) = ((Work.FIPlan.gnorm z : ℕ) : ℤ) := by
    rw [h]
    have e1 : ((z.re.natAbs ^ 2 : ℕ) : ℤ) = z.re ^ 2 := by
      push_cast; exact sq_abs z.re
    have e2 : ((z.im.natAbs ^ 2 : ℕ) : ℤ) = z.im ^ 2 := by
      push_cast; exact sq_abs z.im
    rw [Nat.cast_add, e1, e2]
  exact_mod_cast h2.symm

private lemma radN_nonneg' (Pa : Work.FITop.Params) : 0 ≤ Work.FITop.radN Pa := by
  rw [Work.FITop.radN]; exact Int.natCast_nonneg _

private lemma absDelta_comm' (a b : GaussianInt) :
    Work.FIPlan.absDelta a b = Work.FIPlan.absDelta b a := by
  rw [Work.FIPlan.absDelta, Work.FIPlan.absDelta, Work.FIArea7.Delta_eq, Work.FIArea7.Delta_eq]
  have h : b.re * a.im - b.im * a.re = -(a.re * b.im - a.im * b.re) := by ring
  rw [h, Int.natAbs_neg]

theorem card_gBox_filter_dvd_absDelta_gnorm (z1 : GaussianInt) (R : ℤ) (hR : 0 ≤ R)
    (c : ℕ) (hc : 0 < c) (hgn : Nat.Coprime (Work.FIPlan.gnorm z1) c) :
    (((Work.FIPlan.gBox R).filter (fun z2 => c ∣ Work.FIPlan.absDelta z1 z2)).card : ℝ)
      ≤ 16 * (((2 * R + 1).toNat : ℝ) * (((2 * R + 1).toNat : ℝ) / c + 1)) := by
  refine card_gBox_filter_dvd_absDelta_gcd z1 R hR c hc (hgn.coprime_dvd_left ?_)
  have hd1 : Nat.gcd z1.re.natAbs z1.im.natAbs ∣ z1.re.natAbs := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd z1.re.natAbs z1.im.natAbs ∣ z1.im.natAbs := Nat.gcd_dvd_right _ _
  have h1 : Nat.gcd z1.re.natAbs z1.im.natAbs ∣ z1.re.natAbs ^ 2 := by
    rw [sq]; exact dvd_mul_of_dvd_left hd1 _
  have h2 : Nat.gcd z1.re.natAbs z1.im.natAbs ∣ z1.im.natAbs ^ 2 := by
    rw [sq]; exact dvd_mul_of_dvd_left hd2 _
  have h3 : Nat.gcd z1.re.natAbs z1.im.natAbs ∣ z1.re.natAbs ^ 2 + z1.im.natAbs ^ 2 :=
    dvd_add h1 h2
  rw [gnorm_factor z1]; exact h3

theorem pairPi_le_massW_rhoPi' (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ)
    (π : GaussianInt) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hπ : π ∈ Work.FIArea7.bigPi Pa (4 * b * e)) :
    Work.FIArea7.pairPi Pa b e β π
      ≤ 16 * (Work.FIArea7.massW Pa β π (4 * b * e)
          * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
              * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1))) := by
  classical
  obtain ⟨hπbox, hπprime, hπre, hπim, hπPz, hπcop⟩ := (Work.FIArea7.mem_bigPi).mp hπ
  have hπne : π ≠ 0 := hπprime.ne_zero
  set m : ℕ := 4 * b * e with hmdef
  have hc : 0 < m := by rw [hmdef]; positivity
  have hR : 0 ≤ Work.FITop.radN Pa := radN_nonneg' Pa
  set s : Finset GaussianInt := Work.FIArea7.piBox Pa π m with hsdef
  set f : GaussianInt → ℝ := fun w => ‖β (π * w)‖ with hfdef
  have hspos : 0 < (Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) := by
    have : 1 ≤ Work.FIArea7.rhoPi (Work.FITop.radN Pa) π := Work.FIArea7.one_le_rhoPi _ _
    exact_mod_cast this
  have hMnn : (0:ℝ) ≤ 16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
      * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1)) := by positivity
  set T : Finset (GaussianInt × GaussianInt) :=
    (s ×ˢ s).filter (fun q => m ∣ Work.FIPlan.absDelta (π * q.1) (π * q.2)) with hTdef
  have hsub : ∀ z ∈ s, Nat.Coprime (Work.FIPlan.gnorm z) m := by
    intro z hz
    rw [hsdef, Work.FIArea7.piBox] at hz
    exact (Finset.mem_filter.mp hz).2
  have hgBox : ∀ z ∈ s, π * z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa) := by
    intro z hz
    rw [hsdef, Work.FIArea7.piBox] at hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
  have hshr : ∀ z ∈ s, z ∈ Work.FIPlan.gBox ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) := by
    intro z hz
    rw [hsdef, Work.FIArea7.piBox] at hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  have hT1 : ∀ p ∈ T, p.1 ∈ s := by
    intro p hp; rw [hTdef, Finset.mem_filter] at hp; exact (Finset.mem_product.mp hp.1).1
  have hT2 : ∀ p ∈ T, p.2 ∈ s := by
    intro p hp; rw [hTdef, Finset.mem_filter] at hp; exact (Finset.mem_product.mp hp.1).2
  have hrow : ∀ z ∈ s, ((T.filter (fun p => p.1 = z)).card : ℝ)
      ≤ 16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
          * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1)) := by
    intro z hz
    have hcardle : (T.filter (fun p => p.1 = z)).card
        ≤ ((Work.FIPlan.gBox ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ)).filter
            (fun w2 => m ∣ Work.FIPlan.absDelta z w2)).card := by
      refine Finset.card_le_card_of_injOn (f := fun p : GaussianInt × GaussianInt => p.2) ?_ ?_
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        obtain ⟨hpT, hp1⟩ := hp
        rw [hTdef, Finset.mem_filter] at hpT
        obtain ⟨hpmem, hpdvd⟩ := hpT
        rw [Finset.mem_product] at hpmem
        refine Finset.mem_filter.mpr ⟨hshr p.2 hpmem.2, ?_⟩
        rw [hp1, Work.FIArea7.absDelta_mul_mul] at hpdvd
        exact hπcop.symm.dvd_of_dvd_mul_left hpdvd
      · intro p hp q hq hpq
        rw [Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext (by rw [hp.2, hq.2]) hpq
    have hcount := card_gBox_filter_dvd_absDelta_gnorm z
      ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) (by positivity) m hc (hsub z hz)
    have hid : ((2 * ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) + 1).toNat : ℝ)
        = (Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) := by
      rw [Work.FIArea7.rhoPi]
      have htoN : (2 * ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) + 1).toNat
          = 2 * Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π + 1 := by
        rw [show (2 * ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) + 1)
            = (((2 * Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π + 1 : ℕ)) : ℤ) by push_cast; ring]
        exact Int.toNat_natCast _
      rw [htoN]
    rw [hid] at hcount
    calc ((T.filter (fun p => p.1 = z)).card : ℝ)
        ≤ ((((Work.FIPlan.gBox ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ)).filter
            (fun w2 => m ∣ Work.FIPlan.absDelta z w2)).card : ℕ) : ℝ) := by
          exact_mod_cast hcardle
      _ ≤ 16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
            * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / m + 1)) := hcount
      _ = 16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
            * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1)) := by
          rw [hmdef]; push_cast; ring
  have hcol : ∀ z ∈ s, ((T.filter (fun p => p.2 = z)).card : ℝ)
      ≤ 16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
          * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1)) := by
    intro z hz
    have hcardle : (T.filter (fun p => p.2 = z)).card
        ≤ ((Work.FIPlan.gBox ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ)).filter
            (fun w1 => m ∣ Work.FIPlan.absDelta z w1)).card := by
      refine Finset.card_le_card_of_injOn (f := fun p : GaussianInt × GaussianInt => p.1) ?_ ?_
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp
        obtain ⟨hpT, hp2⟩ := hp
        rw [hTdef, Finset.mem_filter] at hpT
        obtain ⟨hpmem, hpdvd⟩ := hpT
        rw [Finset.mem_product] at hpmem
        refine Finset.mem_filter.mpr ⟨hshr p.1 hpmem.1, ?_⟩
        rw [hp2, Work.FIArea7.absDelta_mul_mul] at hpdvd
        have h' : m ∣ Work.FIPlan.absDelta p.1 z := hπcop.symm.dvd_of_dvd_mul_left hpdvd
        rwa [absDelta_comm'] at h'
      · intro p hp q hq hpq
        rw [Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext hpq (by rw [hp.2, hq.2])
    have hcount := card_gBox_filter_dvd_absDelta_gnorm z
      ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) (by positivity) m hc (hsub z hz)
    have hid : ((2 * ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) + 1).toNat : ℝ)
        = (Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) := by
      rw [Work.FIArea7.rhoPi]
      have htoN : (2 * ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) + 1).toNat
          = 2 * Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π + 1 := by
        rw [show (2 * ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ) + 1)
            = (((2 * Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π + 1 : ℕ)) : ℤ) by push_cast; ring]
        exact Int.toNat_natCast _
      rw [htoN]
    rw [hid] at hcount
    calc ((T.filter (fun p => p.2 = z)).card : ℝ)
        ≤ ((((Work.FIPlan.gBox ((Work.FIArea7.shrunkNat (Work.FITop.radN Pa) π : ℕ) : ℤ)).filter
            (fun w1 => m ∣ Work.FIPlan.absDelta z w1)).card : ℕ) : ℝ) := by
          exact_mod_cast hcardle
      _ ≤ 16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
            * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / m + 1)) := hcount
      _ = 16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
            * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1)) := by
          rw [hmdef]; push_cast; ring
  have hfin := Work.FIArea7.pairMass_fibre_le s f T
    (16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
      * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1)))
    hMnn hT1 hT2 hrow hcol
  have hkey : (∑ p ∈ T, f p.1 * f p.2) = Work.FIArea7.pairPi Pa b e β π := by
    rw [hTdef, hsdef, hfdef, Work.FIArea7.pairPi, hmdef, Finset.sum_filter, Finset.sum_product]
  have hmass : (∑ z ∈ s, f z ^ 2) = Work.FIArea7.massW Pa β π m := by
    rw [Work.FIArea7.massW, hsdef, hfdef]
  rw [hkey, hmass] at hfin
  rw [hmdef] at hfin
  calc Work.FIArea7.pairPi Pa b e β π
      ≤ 16 * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
          * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1))
          * Work.FIArea7.massW Pa β π (4 * b * e) := hfin
    _ = 16 * (Work.FIArea7.massW Pa β π (4 * b * e)
          * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
              * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1))) := by ring

/-- **The sharp weighted non-coprime pair mass** with `θ` retained, from the three structural
inputs.  Same assembly as `uniMode_pairMass_le_of_pieces` but keeping `θ` (which is what absorbs
the extra logarithms in the sharp target). -/
theorem pairMass_theta_of_pieces
    (H5 : ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ (b e : ℕ), 1 ≤ b → 1 ≤ e →
      Work.FIArea7.uniMode_pairInner Pa b e β
        ≤ ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.pairPi Pa b e β π)
    (H6 : ∀ (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) (π : GaussianInt),
      1 ≤ b → 1 ≤ e → π ∈ Work.FIArea7.bigPi Pa (4 * b * e) →
      Work.FIArea7.pairPi Pa b e β π
        ≤ 16 * (Work.FIArea7.massW Pa β π (4 * b * e)
            * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ)
                * ((Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) / (4 * b * e) + 1))))
    (H7 : ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ (m : ℕ),
      ∑ π ∈ Work.FIArea7.bigPi Pa m, Work.FIArea7.massW Pa β π m
        ≤ (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
            * (6 * Real.log (Pa.N + 2))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ (X : ℕ),
        1 ≤ X → (X : ℝ) ^ 9 ≤ Pa.N →
        ((((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0)).card : ℝ)
            ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)) →
        ((∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
            ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3) →
        Work.FIArea7.uniMode_pairMass Pa X β
          ≤ C * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (Pa.N + 2)) ^ 5
              * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) := by
  refine ⟨100000000, by norm_num, ?_⟩
  intro Pa φ z0 β hβ X hX1 hX9 hcard hmass
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith
  have hNnn : (0 : ℝ) ≤ (Pa.N : ℝ) := le_of_lt hNpos
  set L : ℝ := Real.log (Pa.N + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h3 : (3 : ℝ) ≤ Pa.N + 2 := by linarith
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    exact le_trans (le_of_lt hlog3) (Real.log_le_log (by norm_num) h3)
  have hLpos : (0 : ℝ) < L := by linarith
  set E2 : ℝ := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2 with hE2def
  have hE2nn : (0 : ℝ) ≤ E2 := by rw [hE2def]; positivity
  have hmass' : E2 ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 3 := by
    rw [hE2def, hLdef]
    have hlog : Real.log (Pa.N + 2) = Real.log (2 + (Pa.N : ℝ)) := by
      congr 1; ring
    rw [hlog]
    exact hmass
  have hPzR : (0 : ℝ) < (Pa.Pz : ℝ) := by exact_mod_cast Work.FIArea7.Pz_pos Pa
  have hPz1 : (1 : ℝ) ≤ (Pa.Pz : ℝ) := by
    exact_mod_cast (by have := Pa.hP2; omega : 1 ≤ Pa.Pz)
  set ρ : ℝ := (Work.FIArea7.rhoBar Pa : ℝ) with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ_le : ρ ≤ 12 * Real.sqrt ((Pa.N : ℝ) / Pa.Pz) + 1 := by
    have hR : (Work.FITop.radN Pa : ℝ) ≤ 2 * Real.sqrt (Pa.N : ℝ) + 1 :=
      Work.FIArea7.radN_le Pa
    have hfl : ((Nat.floor ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ)) : ℕ) : ℝ)
        ≤ (Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ) := by
      apply Nat.floor_le
      have h0 : (0 : ℝ) ≤ ((Work.FITop.radN Pa : ℤ) : ℝ) := by exact_mod_cast radN_nonneg' Pa
      exact div_nonneg (mul_nonneg h0 (Real.sqrt_nonneg 2)) (Real.sqrt_nonneg _)
    have hsN1 : (1 : ℝ) ≤ Real.sqrt (Pa.N : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
    have hR3 : (Work.FITop.radN Pa : ℝ) ≤ 3 * Real.sqrt (Pa.N : ℝ) := by linarith
    have hs2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have hspz1 : (1 : ℝ) ≤ Real.sqrt (Pa.Pz : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hPz1
    have hsqrtdiv : Real.sqrt (Pa.N : ℝ) / Real.sqrt (Pa.Pz : ℝ)
        = Real.sqrt ((Pa.N : ℝ) / Pa.Pz) := (Real.sqrt_div hNnn _).symm
    have hx : (Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ)
        ≤ 6 * Real.sqrt ((Pa.N : ℝ) / Pa.Pz) := by
      have h1 : (Work.FITop.radN Pa : ℝ) * Real.sqrt 2
          ≤ (3 * Real.sqrt (Pa.N : ℝ)) * 2 :=
        mul_le_mul hR3 hs2 (Real.sqrt_nonneg 2) (by positivity)
      have h2 : (6 * (Real.sqrt (Pa.N : ℝ) / Real.sqrt (Pa.Pz : ℝ))) * Real.sqrt (Pa.Pz : ℝ)
          = 6 * Real.sqrt (Pa.N : ℝ) := by field_simp
      rw [← hsqrtdiv, div_le_iff₀ (Real.sqrt_pos_of_pos hPzR), h2]
      linarith
    calc ρ = 2 * ((Nat.floor ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2
            / Real.sqrt (Pa.Pz : ℝ)) : ℕ) : ℝ) + 1 := by
          rw [hρdef, Work.FIArea7.rhoBar]; push_cast; ring
      _ ≤ 2 * ((Work.FITop.radN Pa : ℝ) * Real.sqrt 2 / Real.sqrt (Pa.Pz : ℝ)) + 1 := by
          linarith [hfl]
      _ ≤ 2 * (6 * Real.sqrt ((Pa.N : ℝ) / Pa.Pz)) + 1 := by linarith [hx]
      _ = 12 * Real.sqrt ((Pa.N : ℝ) / Pa.Pz) + 1 := by ring
  have hρ_sq : ρ ^ 2 ≤ 200 * ((Pa.N : ℝ) / Pa.Pz + 1) := by
    have hu0 : (0 : ℝ) ≤ Real.sqrt ((Pa.N : ℝ) / Pa.Pz) := Real.sqrt_nonneg _
    have husq : (Real.sqrt ((Pa.N : ℝ) / Pa.Pz)) ^ 2 = (Pa.N : ℝ) / Pa.Pz :=
      Real.sq_sqrt (by positivity)
    have h1 : ρ ^ 2 ≤ (12 * Real.sqrt ((Pa.N : ℝ) / Pa.Pz) + 1) ^ 2 :=
      pow_le_pow_left₀ hρ0 hρ_le 2
    nlinarith [h1, hu0, husq]
  have hlogX : 1 + Real.log X ≤ 2 * L := by
    have hX1R : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
    have hXleN : (X : ℝ) ≤ (Pa.N : ℝ) := by
      have h1 : (X : ℝ) ≤ (X : ℝ) ^ 9 := by
        simpa using pow_le_pow_right₀ hX1R (by norm_num : (1 : ℕ) ≤ 9)
      linarith [hX9]
    have hlogN : Real.log (X : ℝ) ≤ Real.log (Pa.N : ℝ) :=
      Real.log_le_log (by linarith) hXleN
    have hlogN2 : Real.log (Pa.N : ℝ) ≤ Real.log (Pa.N + 2) :=
      Real.log_le_log hNpos (by linarith)
    have hlogX0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1R
    rw [hLdef]
    linarith
  have hlogB : 1 + Real.log (Work.FIArea7.uniB Pa) ≤ 3 * L := by
    have hub : (Work.FIArea7.uniB Pa : ℝ) ≤ 6 * (Pa.N : ℝ) := Work.FIArea7.uniB_le Pa
    have hubpos : (0 : ℝ) < (Work.FIArea7.uniB Pa : ℝ) := by
      have : 0 < Work.FIArea7.uniB Pa := by rw [Work.FIArea7.uniB]; omega
      exact_mod_cast this
    have hlogB' : Real.log (Work.FIArea7.uniB Pa) ≤ Real.log (6 * (Pa.N : ℝ)) :=
      Real.log_le_log hubpos hub
    have h6N : Real.log (6 * (Pa.N : ℝ)) ≤ 2 * Real.log (Pa.N + 2) := by
      have h6 : (6 * (Pa.N : ℝ)) ≤ (Pa.N + 2) ^ 2 := by nlinarith
      have h := Real.log_le_log (by positivity) h6
      rw [Real.log_pow] at h
      norm_num at h
      exact h
    rw [hLdef]
    linarith
  have hlogX0 : 0 ≤ 1 + Real.log X := by
    have : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX1)
    linarith
  have hlogB0 : 0 ≤ 1 + Real.log (Work.FIArea7.uniB Pa) := by
    have : 0 ≤ Real.log (Work.FIArea7.uniB Pa) := by
      apply Real.log_nonneg
      have : 0 < Work.FIArea7.uniB Pa := by rw [Work.FIArea7.uniB]; omega
      exact_mod_cast (by omega : 1 ≤ Work.FIArea7.uniB Pa)
    linarith
  have hsum_be := Work.FIArea7.sum_be_bound (Work.FIArea7.uniB Pa) X ρ hρ0
  -- the per-block sum bound: constant pulled out with a general factor
  have h3gen : ∀ c : ℝ, (∑ b ∈ Finset.Icc 1 (Work.FIArea7.uniB Pa), ∑ e ∈ Finset.Icc 1 X,
        c * ((1 / (b : ℝ)) * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1))))
      = c * (∑ b ∈ Finset.Icc 1 (Work.FIArea7.uniB Pa), ∑ e ∈ Finset.Icc 1 X,
        (1 / (b : ℝ)) * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1))) := by
    intro c
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
  have hπbound : ∀ b ∈ Finset.Icc 1 (Work.FIArea7.uniB Pa), ∀ e ∈ Finset.Icc 1 X,
      (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.pairPi Pa b e β π)
        ≤ 96 * L * E2 * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1)) := by
    intro b hb e he
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have h7' : (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e),
          Work.FIArea7.massW Pa β π (4 * b * e)) ≤ E2 * (6 * L) := by
      rw [hE2def, hLdef]
      have h := H7 hβ (4 * b * e)
      have hlog : Real.log (Pa.N + 2) = Real.log (Pa.N + 2) := rfl
      linarith [h]
    have hgen : ∀ c : ℝ, (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e),
          (16 : ℝ) * (Work.FIArea7.massW Pa β π (4 * b * e) * c))
        = 16 * (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e),
            Work.FIArea7.massW Pa β π (4 * b * e)) * c := by
      intro c
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro π _
      ring
    calc (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.pairPi Pa b e β π)
        ≤ ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e),
            (16 : ℝ) * (Work.FIArea7.massW Pa β π (4 * b * e)
              * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1))) := by
          refine Finset.sum_le_sum (fun π hπ => ?_)
          refine le_trans (H6 Pa b e β π hb1 he1 hπ) ?_
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul_of_nonneg_left _ (by rw [Work.FIArea7.massW]; positivity)
          have hρπ : (Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) ≤ ρ := by
            rw [hρdef]; exact_mod_cast Work.FIArea7.rhoPi_le_rhoBar hπ
          have hρπ0 : (0 : ℝ) ≤ (Work.FIArea7.rhoPi (Work.FITop.radN Pa) π : ℝ) := by positivity
          apply mul_le_mul hρπ _ (by positivity) (by linarith)
          apply add_le_add _ le_rfl
          exact div_le_div_of_nonneg_right hρπ (by positivity)
      _ = 16 * (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e),
            Work.FIArea7.massW Pa β π (4 * b * e))
            * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1)) := hgen _
      _ ≤ 16 * (E2 * (6 * L)) * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left h7' (by norm_num)
      _ = 96 * L * E2 * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1)) := by ring
  have hmain : Work.FIArea7.uniMode_pairMass Pa X β
      ≤ ∑ b ∈ Finset.Icc 1 (Work.FIArea7.uniB Pa), ∑ e ∈ Finset.Icc 1 X,
          (96 * L * E2) * ((1 / (b : ℝ)) * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1))) := by
    rw [Work.FIArea7.uniMode_pairMass]
    refine Finset.sum_le_sum (fun b hb => Finset.sum_le_sum (fun e he => ?_))
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    calc (1 / (b : ℝ)) * Work.FIArea7.uniMode_pairInner Pa b e β
        ≤ (1 / (b : ℝ)) * (∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e),
            Work.FIArea7.pairPi Pa b e β π) :=
          mul_le_mul_of_nonneg_left (H5 hβ b e hb1 (Finset.mem_Icc.mp he).1) (by positivity)
      _ ≤ (1 / (b : ℝ)) * (96 * L * E2 * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1))) :=
          mul_le_mul_of_nonneg_left (hπbound b hb e he) (by positivity)
      _ = (96 * L * E2) * ((1 / (b : ℝ)) * (ρ * (ρ / (4 * (b : ℝ) * (e : ℝ)) + 1))) := by ring
  have hbound : Work.FIArea7.uniMode_pairMass Pa X β
      ≤ (96 * L * E2) * (ρ ^ 2 * (1 + Real.log X) / 2
          + ρ * (1 + Real.log (Work.FIArea7.uniB Pa)) * X) := by
    rw [h3gen (96 * L * E2)] at hmain
    exact le_trans hmain (mul_le_mul_of_nonneg_left hsum_be (by positivity))
  have h1' : ρ ^ 2 * (1 + Real.log X) / 2 ≤ 200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L := by
    have h := mul_le_mul hρ_sq hlogX hlogX0 (by positivity)
    have h2L : 200 * ((Pa.N : ℝ) / Pa.Pz + 1) * (2 * L) / 2
        = 200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L := by ring
    linarith [h, h2L]
  have h2' : ρ * (1 + Real.log (Work.FIArea7.uniB Pa)) * X
      ≤ (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X := by
    have h3s : Real.sqrt ((Pa.N : ℝ) / Pa.Pz) ≤ Real.sqrt (Pa.N : ℝ) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_iff₀ hPzR]; nlinarith [hNpos]
    have hb : ρ ≤ 12 * Real.sqrt (Pa.N) + 1 := by linarith [hρ_le, h3s]
    have hb0 : (0 : ℝ) ≤ 12 * Real.sqrt (Pa.N : ℝ) + 1 := by positivity
    have hInner : ρ * (1 + Real.log (Work.FIArea7.uniB Pa))
        ≤ (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) :=
      mul_le_mul hb hlogB hlogB0 hb0
    exact mul_le_mul_of_nonneg_right hInner (by positivity)
  have hsum1 : ρ ^ 2 * (1 + Real.log X) / 2
        + ρ * (1 + Real.log (Work.FIArea7.uniB Pa)) * X
      ≤ 200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L
        + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X := add_le_add h1' h2'
  have hfinal : Work.FIArea7.uniMode_pairMass Pa X β
      ≤ (96 * L * E2) * (200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L
          + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X) :=
    le_trans hbound (mul_le_mul_of_nonneg_left hsum1 (by positivity))
  have hmass2 : (96 * L * E2) * (200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L
          + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X)
      ≤ (96 * L * (1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 3))
          * (200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L
              + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hmass' (by positivity)
  have hshr : (96 * L * (1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 3))
          * (200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L
              + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X)
      ≤ 100000000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 5
          * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) := by
    have hA0 : (0 : ℝ) ≤ Pa.θ * Pa.N + Real.sqrt Pa.N + 1 := by
      have h1 : 0 ≤ Pa.θ * Pa.N := mul_nonneg Pa.hθ0.le (le_of_lt hNpos)
      have h2 : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
      linarith
    have hXL : (0 : ℝ) ≤ (X : ℝ) := by positivity
    have hsN : (0 : ℝ) ≤ Real.sqrt (Pa.N : ℝ) := Real.sqrt_nonneg _
    have hkey : 200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L
          + (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X
        ≤ 200 * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) * L := by
      have h12 : (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X
          ≤ 200 * (Real.sqrt Pa.N + 1) * (X : ℝ) * L := by
        have h1 : (12 * Real.sqrt (Pa.N : ℝ) + 1) * 3 ≤ 200 * (Real.sqrt Pa.N + 1) := by
          nlinarith [hsN]
        have hL0 : (0 : ℝ) ≤ L := le_of_lt hLpos
        calc (12 * Real.sqrt (Pa.N : ℝ) + 1) * (3 * L) * X
            = ((12 * Real.sqrt (Pa.N : ℝ) + 1) * 3) * L * X := by ring
          _ ≤ (200 * (Real.sqrt Pa.N + 1)) * L * X :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hL0) hXL
          _ = 200 * (Real.sqrt Pa.N + 1) * (X : ℝ) * L := by ring
      have heq : 200 * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) * L
          = 200 * ((Pa.N : ℝ) / Pa.Pz + 1) * L + 200 * (Real.sqrt Pa.N + 1) * (X : ℝ) * L :=
        by ring
      rw [heq]
      linarith [h12]
    have hMnn : (0 : ℝ) ≤ (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 5
        * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) := by
      apply mul_nonneg (mul_nonneg hA0 (by positivity))
      apply add_nonneg (by positivity) (by positivity)
    have hfin : (96 * L * (1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 3))
          * (200 * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) * L)
        = 19200000 * ((Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 5
          * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ))) := by ring
    have hfin2 : (100000000 : ℝ) * ((Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 5
          * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)))
        = 100000000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 5
          * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) := by ring
    refine le_trans (mul_le_mul_of_nonneg_left hkey ?_) ?_
    · apply mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      exact mul_nonneg (mul_nonneg (by norm_num) hA0) (by positivity)
    · rw [hfin, ← hfin2]
      exact mul_le_mul_of_nonneg_right (by norm_num : (19200000:ℝ) ≤ 100000000) hMnn
  exact le_trans hfinal (le_trans hmass2 hshr)

/-- The product of the norms of a finset of Gaussian integers. -/
lemma gnorm_prod' (s : Finset GaussianInt) :
    Work.FIPlan.gnorm (∏ π ∈ s, π) = ∏ π ∈ s, Work.FIPlan.gnorm π := by
  classical
  induction s using Finset.induction_on with
  | empty => decide
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Work.FIArea7.gnorm_mul, ih]

/-- Two associated elements of the canonical quadrant `0 < re, 0 ≤ im` are equal. -/
lemma associated_quad_eq {p q : GaussianInt} (hpre : 0 < p.re) (hpim : 0 ≤ p.im)
    (hqre : 0 < q.re) (hqim : 0 ≤ q.im) (h : Associated p q) : p = q := by
  obtain ⟨u, hu⟩ := h
  have hu' : ((u : GaussianIntˣ) : GaussianInt) = 1 ∨ ((u : GaussianIntˣ) : GaussianInt) = -1
      ∨ ((u : GaussianIntˣ) : GaussianInt) = (⟨0, 1⟩ : GaussianInt)
      ∨ ((u : GaussianIntˣ) : GaussianInt) = (⟨0, -1⟩ : GaussianInt) :=
    (Commons.NumberTheory.GaussianInt.units_classification _).mp u.isUnit
  rcases hu' with h1 | h1 | h1 | h1
  · rw [h1, mul_one] at hu; exact hu
  · rw [h1, mul_neg, mul_one] at hu
    have h2 := congrArg (fun x : GaussianInt => x.re) hu
    rw [Zsqrtd.re_neg] at h2
    linarith
  · rw [h1] at hu
    have h2 := congrArg (fun x : GaussianInt => x.re) hu
    rw [Zsqrtd.re_mul] at h2
    ring_nf at h2
    linarith
  · rw [h1] at hu
    have h2 := congrArg (fun x : GaussianInt => x.im) hu
    rw [Zsqrtd.im_mul] at h2
    ring_nf at h2
    linarith

/-- Distinct elements of `bigPi Pa m` do not divide each other. -/
lemma not_dvd_of_bigPi_ne {Pa : Work.FITop.Params} {m : ℕ} {p q : GaussianInt}
    (hp : p ∈ Work.FIArea7.bigPi Pa m) (hq : q ∈ Work.FIArea7.bigPi Pa m) (hpq : p ≠ q) :
    ¬ p ∣ q := by
  obtain ⟨-, hpprime, hpre, hpim, -, -⟩ := (Work.FIArea7.mem_bigPi).mp hp
  obtain ⟨-, hqprime, hqre, hqim, -, -⟩ := (Work.FIArea7.mem_bigPi).mp hq
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hqne : q ≠ 0 := hqprime.ne_zero
  rcases hqprime.2.2 p c (by rw [hc]) with h1 | h1
  · exact hpq (associated_quad_eq hpre hpim hqre hqim (associated_of_dvd_dvd ⟨c, hc⟩ h1))
  · obtain ⟨e, he⟩ := h1
    have h : q = q * (p * e) := by
      calc q = p * c := hc
        _ = p * (q * e) := by rw [he]
        _ = q * (p * e) := by ring
    have h1e : (1 : GaussianInt) = p * e := mul_left_cancel₀ hqne (by rw [mul_one]; exact h)
    exact hpprime.not_isUnit (isUnit_iff_dvd_one.mpr ⟨e, h1e⟩)

/-- The number of primes of `bigPi Pa m` dividing a supported `z` is `≤ 6 log(N+2)`. -/
lemma bigPiDvd_card_le {Pa : Work.FITop.Params} {m : ℕ} {z : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa)) (hz0 : z ≠ 0) :
    ((Work.FIArea7.bigPiDvd Pa m z).card : ℝ) ≤ 6 * Real.log (Pa.N + 2) := by
  classical
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
  have hPz2 : 2 ≤ Pa.Pz := Pa.hP2
  -- the product of the `π` divides `z`
  have hpdvd : (∏ π ∈ Work.FIArea7.bigPiDvd Pa m z, π) ∣ z := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro p hpd q hqd hpq
      rw [Function.onFun]
      have hp : p ∈ Work.FIArea7.bigPi Pa m := ((Work.FIArea7.mem_bigPiDvd).mp hpd).1
      have hq : q ∈ Work.FIArea7.bigPi Pa m := ((Work.FIArea7.mem_bigPiDvd).mp hqd).1
      have hpprime : Prime p := (Work.FIArea7.mem_bigPi.mp hp).2.1
      rw [hpprime.coprime_iff_not_dvd]
      exact not_dvd_of_bigPi_ne hp hq hpq
    · intro π hπ
      exact ((Work.FIArea7.mem_bigPiDvd).mp hπ).2
  have hgn_dvd : (∏ π ∈ Work.FIArea7.bigPiDvd Pa m z, Work.FIPlan.gnorm π)
      ∣ Work.FIPlan.gnorm z := by
    have h := gnorm_dvd_of_dvd hpdvd
    rwa [gnorm_prod'] at h
  have hgn_pos : 0 < Work.FIPlan.gnorm z := by
    rw [Nat.pos_iff_ne_zero]; intro h
    exact hz0 (gnorm_eq_zero_iff.mp h)
  have hle_gn : (∏ π ∈ Work.FIArea7.bigPiDvd Pa m z, Work.FIPlan.gnorm π)
      ≤ Work.FIPlan.gnorm z := Nat.le_of_dvd hgn_pos hgn_dvd
  -- `(Pz+1)^{#} ≤ ∏ gnorm`
  have hprod_le : (Pa.Pz + 1) ^ (Work.FIArea7.bigPiDvd Pa m z).card
      ≤ ∏ π ∈ Work.FIArea7.bigPiDvd Pa m z, Work.FIPlan.gnorm π := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun π hπ => ?_)
    have : Pa.Pz < Work.FIPlan.gnorm π :=
      (Work.FIArea7.mem_bigPi.mp ((Work.FIArea7.mem_bigPiDvd).mp hπ).1).2.2.2.2.1
    omega
  -- gnorm z ≤ (N+2)^4
  have hgn_le : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ ((Pa.N : ℝ) + 2) ^ 4 := by
    have hbox := Work.FIArea7.cf_mem_gBox_iff.mp hz
    have hsq : ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
    have h1 : ((Work.FIPlan.gnorm z : ℕ) : ℤ) ≤ 2 * (Work.FITop.radN Pa) ^ 2 := by
      rw [hsq]; nlinarith [hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2]
    have h2 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (Work.FITop.radN Pa : ℝ) ^ 2 := by
      exact_mod_cast h1
    have hR : (Work.FITop.radN Pa : ℝ) ≤ 2 * Real.sqrt (Pa.N : ℝ) + 1 := Work.FIArea7.radN_le Pa
    have hsn : Real.sqrt (Pa.N : ℝ) ≤ (Pa.N : ℝ) := by
      nlinarith [Real.sq_sqrt (le_of_lt (by linarith : (0:ℝ) < (Pa.N:ℝ))), Real.sqrt_nonneg (Pa.N:ℝ), hN1]
    have h3 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (Pa.N + 2) ^ 4 := by
      have hR2 : (Work.FITop.radN Pa : ℝ) ^ 2 ≤ (2 * Real.sqrt (Pa.N : ℝ) + 1) ^ 2 :=
        pow_le_pow_left₀ (by exact_mod_cast radN_nonneg' Pa : (0:ℝ) ≤ (Work.FITop.radN Pa : ℝ)) hR 2
      have h4a : 2 * (2 * Real.sqrt (Pa.N : ℝ) + 1) ^ 2 ≤ 16 * (Pa.N : ℝ) + 2 := by
        have hs2 : Real.sqrt (Pa.N : ℝ) ^ 2 = (Pa.N : ℝ) :=
          Real.sq_sqrt (by linarith)
        have hs0 : (0 : ℝ) ≤ Real.sqrt (Pa.N : ℝ) := Real.sqrt_nonneg _
        nlinarith [hs2, hs0, hsn]
      have h4b : 16 * (Pa.N : ℝ) + 2 ≤ (Pa.N + 2) ^ 4 := by
        have hx : ((Pa.N:ℝ) + 2) ^ 4
            = (Pa.N:ℝ)^4 + 8*(Pa.N:ℝ)^3 + 24*(Pa.N:ℝ)^2 + 32*(Pa.N:ℝ) + 16 := by ring
        rw [hx]
        have h0 : (0:ℝ) ≤ (Pa.N:ℝ) := by linarith
        nlinarith [h0, sq_nonneg (Pa.N:ℝ), sq_nonneg ((Pa.N:ℝ)^2)]
      linarith [h2, hR2, h4a, h4b]
    exact h3
  -- logs
  have hL1 : (1 : ℝ) ≤ Real.log (Pa.N + 2) := by
    have h3 : (3 : ℝ) ≤ Pa.N + 2 := by linarith
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    exact le_trans (le_of_lt hlog3) (Real.log_le_log (by norm_num) h3)
  have hPz1 : (1 : ℝ) ≤ (Pa.Pz : ℝ) := by exact_mod_cast (by omega : 1 ≤ Pa.Pz)
  have hlogPz : (1 : ℝ) ≤ Real.log ((Pa.Pz : ℝ) + 1) := by
    have h3 : (3 : ℝ) ≤ (Pa.Pz : ℝ) + 1 := by exact_mod_cast (by omega : 3 ≤ Pa.Pz + 1)
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    exact le_trans (le_of_lt hlog3) (Real.log_le_log (by norm_num) h3)
  have hstep1 : ((Work.FIArea7.bigPiDvd Pa m z).card : ℝ) * Real.log ((Pa.Pz : ℝ) + 1)
      ≤ Real.log (Work.FIPlan.gnorm z) := by
    have h := hprod_le.trans hle_gn
    have hcast : (((Pa.Pz + 1) ^ (Work.FIArea7.bigPiDvd Pa m z).card : ℕ) : ℝ)
        ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by exact_mod_cast h
    have hlog := Real.log_le_log (by positivity) hcast
    have h1 : ((Pa.Pz + 1 : ℕ) : ℝ) = (Pa.Pz : ℝ) + 1 := by push_cast; ring
    rw [Nat.cast_pow, h1, Real.log_pow] at hlog
    exact hlog
  have hstep2 : Real.log (Work.FIPlan.gnorm z) ≤ 4 * Real.log (Pa.N + 2) := by
    have hgn1 : (0 : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by exact_mod_cast hgn_pos
    have h := Real.log_le_log hgn1 hgn_le
    rwa [Real.log_pow] at h
  have hcard0 : (0 : ℝ) ≤ ((Work.FIArea7.bigPiDvd Pa m z).card : ℝ) := by positivity
  have : ((Work.FIArea7.bigPiDvd Pa m z).card : ℝ) * Real.log ((Pa.Pz : ℝ) + 1)
      ≤ 4 * Real.log (Pa.N + 2) := le_trans hstep1 hstep2
  have hfinal2 : ((Work.FIArea7.bigPiDvd Pa m z).card : ℝ) ≤ 4 * Real.log (Pa.N + 2) :=
    le_trans (le_mul_of_one_le_right hcard0 hlogPz) this
  linarith [hfinal2, hL1]

/-- **The `π`-sublattice total mass bound.** -/
theorem sum_massW_le' {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (m : ℕ) :
    ∑ π ∈ Work.FIArea7.bigPi Pa m, Work.FIArea7.massW Pa β π m
      ≤ (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
          * (6 * Real.log (Pa.N + 2)) := by
  classical
  have hstep : ∀ π ∈ Work.FIArea7.bigPi Pa m, Work.FIArea7.massW Pa β π m
      ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), (if π ∣ z then ‖β z‖ ^ 2 else 0) := by
    intro π hπ
    have hπ0 : π ≠ 0 := (Work.FIArea7.mem_bigPi.mp hπ).2.1.ne_zero
    rw [Work.FIArea7.massW]
    have hmap : ∀ w ∈ Work.FIArea7.piBox Pa π m, π * w ∈
        (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => π ∣ z) := by
      intro w hw
      rw [Work.FIArea7.piBox] at hw
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2, ⟨w, rfl⟩⟩
    have h1 : (∑ w ∈ Work.FIArea7.piBox Pa π m, ‖β (π * w)‖ ^ 2)
        = ∑ z ∈ (Work.FIArea7.piBox Pa π m).image (fun w => π * w), ‖β z‖ ^ 2 := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact mul_left_cancel₀ hπ0 hab
    rw [h1]
    calc (∑ z ∈ (Work.FIArea7.piBox Pa π m).image (fun w => π * w), ‖β z‖ ^ 2)
        ≤ ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => π ∣ z), ‖β z‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro z hz
            rw [Finset.mem_image] at hz
            obtain ⟨w, hw, rfl⟩ := hz
            exact hmap w hw
          · intro z _ _; positivity
      _ = ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), (if π ∣ z then ‖β z‖ ^ 2 else 0) := by
          rw [Finset.sum_filter]
  have hmain : (∑ π ∈ Work.FIArea7.bigPi Pa m, Work.FIArea7.massW Pa β π m)
      ≤ ∑ π ∈ Work.FIArea7.bigPi Pa m, ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (if π ∣ z then ‖β z‖ ^ 2 else 0) := Finset.sum_le_sum hstep
  rw [Finset.sum_comm] at hmain
  have hcount : ∀ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      (∑ π ∈ Work.FIArea7.bigPi Pa m, (if π ∣ z then ‖β z‖ ^ 2 else 0))
        ≤ (6 * Real.log (Pa.N + 2)) * ‖β z‖ ^ 2 := by
    intro z hz
    by_cases hzβ : β z = 0
    · have h0 : ∀ π ∈ Work.FIArea7.bigPi Pa m,
          (if π ∣ z then ‖β z‖ ^ 2 else 0) = 0 := by
        intro π _; simp [hzβ]
      rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
      exact mul_nonneg (mul_nonneg (by norm_num)
        (Real.log_nonneg (by linarith [Pa.hN1] : (1:ℝ) ≤ (Pa.N:ℝ) + 2))) (sq_nonneg _)
    · have hz0 : z ≠ 0 := by
        intro h0
        have hNlt : (Pa.N : ℝ) < (Work.FIPlan.gnorm z : ℝ) := (hβ.support hzβ).2.1
        have hgn0 : ((Work.FIPlan.gnorm (0 : GaussianInt) : ℕ) : ℝ) = 0 := by
          rw [show Work.FIPlan.gnorm (0 : GaussianInt) = 0 by decide]; norm_num
        rw [h0] at hNlt
        rw [hgn0] at hNlt
        linarith [Pa.hN1]
      have hcz : (∑ π ∈ Work.FIArea7.bigPi Pa m, (if π ∣ z then ‖β z‖ ^ 2 else 0))
          = ((Work.FIArea7.bigPiDvd Pa m z).card : ℝ) * ‖β z‖ ^ 2 := by
        rw [Work.FIArea7.bigPiDvd, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [hcz]
      exact mul_le_mul_of_nonneg_right (bigPiDvd_card_le hz hz0) (by positivity)
  refine le_trans hmain ?_
  calc (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ π ∈ Work.FIArea7.bigPi Pa m, (if π ∣ z then ‖β z‖ ^ 2 else 0))
      ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (6 * Real.log (Pa.N + 2)) * ‖β z‖ ^ 2 :=
        Finset.sum_le_sum hcount
    _ = (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
          * (6 * Real.log (Pa.N + 2)) := by
        rw [← Finset.mul_sum]; ring

end

end Work.FIArea7
