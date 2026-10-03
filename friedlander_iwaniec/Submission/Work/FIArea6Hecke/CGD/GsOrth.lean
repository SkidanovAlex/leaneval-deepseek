import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus

set_option autoImplicit false

namespace Work.FIArea6Hecke.CGD

open scoped BigOperators
open Work.FIArea6Hecke.R

noncomputable section

/-! ## Elementary algebra of `gdot`, `ekern`, and `gnorm` -/

/-- `gdot x y = Re (x · conj y)`. -/
private lemma gdot_eq_re_mul_star (x y : GaussianInt) : gdot x y = (x * star y).re := by
  simp only [gdot, Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- `M · conj M = |M|²`, viewed as a Gaussian integer. -/
private lemma mul_star_self_eq_gnorm (M : GaussianInt) :
    M * star M = ((Work.FIPlan.gnorm M : ℤ) : GaussianInt) := by
  rw [Work.FIPlan.gnorm, Int.cast_natCast, GaussianInt.natCast_natAbs_norm,
    Zsqrtd.norm_eq_mul_conj]

/-- The norm of a nonzero Gaussian integer is nonzero. -/
private lemma gnorm_ne_zero' {M : GaussianInt} (hM : M ≠ 0) : Work.FIPlan.gnorm M ≠ 0 := by
  rw [Work.FIPlan.gnorm, Ne, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]
  exact hM

/-- `gdot` is homogeneous of degree `2` under multiplication by `M`. -/
private lemma gdot_mul_mul (M u v : GaussianInt) :
    gdot (M * u) (M * v) = (Work.FIPlan.gnorm M : ℤ) * gdot u v := by
  rw [gdot_eq_re_mul_star, gdot_eq_re_mul_star]
  have h : M * u * star (M * v) = ((Work.FIPlan.gnorm M : ℤ) : GaussianInt) * (u * star v) := by
    rw [star_mul']
    rw [show M * u * (star M * star v) = (M * star M) * (u * star v) from by ring,
      mul_star_self_eq_gnorm]
  rw [h]
  simp [Zsqrtd.re_mul]

/-- `gdot` is homogeneous in the second argument under multiplication by an integer. -/
private lemma gdot_intCast_mul_right (n : ℤ) (x y : GaussianInt) :
    gdot x ((n : GaussianInt) * y) = n * gdot x y := by
  rw [gdot_eq_re_mul_star, gdot_eq_re_mul_star]
  have hstar : star ((n : GaussianInt)) = (n : GaussianInt) := by
    apply Zsqrtd.ext
    · simp
    · simp
  have h : x * star ((n : GaussianInt) * y) = (n : GaussianInt) * (x * star y) := by
    rw [star_mul', hstar]; ring
  rw [h]
  simp [Zsqrtd.re_mul]

/-- The value of `ekern` is one exactly when `|M|²` divides `gdot s w`. -/
private lemma ekern_eq_one_iff (M : GaussianInt) (hM : M ≠ 0) (w s : GaussianInt) :
    ekern M w s = 1 ↔ (Work.FIPlan.gnorm M : ℤ) ∣ gdot s w := by
  have hGN0 : (Work.FIPlan.gnorm M : ℕ) ≠ 0 := gnorm_ne_zero' hM
  have hGN : ((Work.FIPlan.gnorm M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hGN0
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  constructor
  · intro h
    rw [ekern, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have him : (2 * Real.pi * (gdot s w : ℤ) / (Work.FIPlan.gnorm M : ℕ) : ℝ)
        = (n : ℝ) * (2 * Real.pi) := by
      have hc := congrArg Complex.im hn
      simpa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using hc
    have hdiv : ((gdot s w : ℤ) : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ) = (n : ℝ) := by
      have h1 : (2 * Real.pi) *
          (((gdot s w : ℤ) : ℝ) / ((Work.FIPlan.gnorm M : ℕ) : ℝ))
          = (2 * Real.pi) * (n : ℝ) := by
        rw [← mul_div_assoc, him]
        ring
      exact mul_left_cancel₀ h2pi h1
    have hG : ((gdot s w : ℤ) : ℝ) = (n : ℝ) * ((Work.FIPlan.gnorm M : ℕ) : ℝ) :=
      (div_eq_iff hGN).mp hdiv
    refine ⟨n, ?_⟩
    have hthis : gdot s w = n * (Work.FIPlan.gnorm M : ℤ) := by exact_mod_cast hG
    rw [hthis]; ring
  · rintro ⟨k, hk⟩
    have hmain : (2 * Real.pi * (gdot s w : ℤ) / (Work.FIPlan.gnorm M : ℕ) : ℝ)
        = 2 * Real.pi * (k : ℝ) := by
      rw [hk]
      have hc : (((Work.FIPlan.gnorm M : ℤ) : ℝ)) = ((Work.FIPlan.gnorm M : ℕ) : ℝ) := by
        simp
      rw [Int.cast_mul, hc]
      field_simp
    have harg : ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I
        = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [ekern, hmain, harg]
    exact Complex.exp_int_mul_two_pi_mul_I k

/-- `ekern` is invariant under adding multiples of `M` to its argument, provided the frequency
is a multiple of `M`. -/
private lemma ekern_period (M : GaussianInt) (hM : M ≠ 0) (t : GaussianInt) {z w : GaussianInt}
    (h : M ∣ z - w) : ekern M (M * star t) z = ekern M (M * star t) w := by
  obtain ⟨u, hu⟩ := h
  have hz : z = w + M * u := by rw [← hu]; abel
  rw [hz, ekern_add_right]
  have hone : ekern M (M * star t) (M * u) = 1 :=
    (ekern_eq_one_iff M hM (M * star t) (M * u)).mpr
      ⟨gdot u (star t), by rw [gdot_mul_mul]⟩
  rw [hone, mul_one]

/-- For `M ∤ t` the additive character `a ↦ ekern M (M * conj t) a` is nontrivial. -/
private lemma exists_ekern_ne_one (M : GaussianInt) (hM : M ≠ 0) (t : GaussianInt) (ht : ¬ M ∣ t) :
    ∃ s : GaussianInt, ekern M (M * star t) s ≠ 1 := by
  by_contra h
  push Not at h
  have h1 : (Work.FIPlan.gnorm M : ℤ) ∣ (M * star t).re := by
    have h' := (ekern_eq_one_iff M hM (M * star t) 1).mp (h 1)
    simpa [gdot] using h'
  have h2 : (Work.FIPlan.gnorm M : ℤ) ∣ (M * star t).im := by
    have h' := (ekern_eq_one_iff M hM (M * star t) ⟨(0 : ℤ), 1⟩).mp (h ⟨(0 : ℤ), 1⟩)
    simpa [gdot] using h'
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hNw : ((Work.FIPlan.gnorm M : ℤ) : GaussianInt) ∣ M * star t := by
    refine ⟨⟨a, b⟩, ?_⟩
    apply Zsqrtd.ext
    · simp [ha]
    · simp [hb]
  obtain ⟨u, hu⟩ := hNw
  have hstarM : star M ≠ 0 := by
    intro hh
    exact hM (by have := congrArg star hh; simpa using this)
  have hEq : M * star t = M * (star M * u) := by
    rw [hu, ← mul_star_self_eq_gnorm]; ring
  have hcancel : star t = star M * u := mul_left_cancel₀ hM hEq
  exact ht ⟨star u, by rw [← star_star t, hcancel, star_mul', star_star]⟩

/-! ## The orthogonality relation -/

theorem GsOrth (M : GaussianInt) (hM : M ≠ 0)
    (S : Finset GaussianInt) (hS : Work.FIArea6Hecke.R.IsCRS M S) (t : GaussianInt) :
    (M ∣ t → Finset.sum S (fun a => Work.FIArea6Hecke.R.ekern M (M * star t) a) =
      ((S.card : ℕ) : ℂ)) ∧
    (¬ M ∣ t → Finset.sum S (fun a => Work.FIArea6Hecke.R.ekern M (M * star t) a) = 0) := by
  refine ⟨?_, ?_⟩
  · intro hMt
    have hkern : ∀ a : GaussianInt, ekern M (M * star t) a = 1 := by
      intro a
      obtain ⟨k, hk⟩ := hMt
      have ht' : M * star t = ((Work.FIPlan.gnorm M : ℤ) : GaussianInt) * star k := by
        rw [hk, star_mul']
        rw [show M * (star M * star k) = M * star M * star k from by ring,
          mul_star_self_eq_gnorm]
      refine (ekern_eq_one_iff M hM (M * star t) a).mpr ⟨gdot a (star k), ?_⟩
      rw [ht', gdot_intCast_mul_right]
    calc Finset.sum S (fun a => ekern M (M * star t) a)
        = Finset.sum S (fun _ => (1 : ℂ)) := Finset.sum_congr rfl (fun a _ => hkern a)
      _ = ((S.card : ℕ) : ℂ) := by simp
  · intro hnt
    obtain ⟨s0, hs0⟩ := exists_ekern_ne_one M hM t hnt
    set f : GaussianInt → ℂ := fun a => ekern M (M * star t) a with hf
    have hs0' : f s0 ≠ 1 := by simpa only [hf] using hs0
    have hper : ∀ z w : GaussianInt, M ∣ (z - w) → f z = f w := by
      intro z w hzw
      simpa only [hf] using ekern_period M hM t hzw
    have hCC := CrsCalculus M S S hS hS f hper
    have hT : IsCRS M (S.image (fun a => a + s0)) := hCC.2.1 s0
    have hsum1 : Finset.sum S f = Finset.sum (S.image (fun a => a + s0)) f :=
      (CrsCalculus M S (S.image (fun a => a + s0)) hS hT f hper).1
    have hsum2 : Finset.sum (S.image (fun a => a + s0)) f
        = Finset.sum S (fun a => f (a + s0)) := hCC.2.2.2.1 s0
    have hshift : Finset.sum S (fun a => f (a + s0)) = f s0 * Finset.sum S f := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      show f (a + s0) = f s0 * f a
      simp only [hf]
      rw [ekern_add_right]
      ring
    have hfix : Finset.sum S f = f s0 * Finset.sum S f := by
      calc Finset.sum S f = Finset.sum (S.image (fun a => a + s0)) f := hsum1
        _ = Finset.sum S (fun a => f (a + s0)) := hsum2
        _ = f s0 * Finset.sum S f := hshift
    have hzero : (f s0 - 1) * Finset.sum S f = 0 := by
      have hfs : f s0 * Finset.sum S f = Finset.sum S f := hfix.symm
      rw [sub_mul, one_mul, hfs, sub_self]
    have hne : f s0 - 1 ≠ 0 := sub_ne_zero.mpr hs0'
    have hsum0 : Finset.sum S f = 0 := by
      rcases mul_eq_zero.mp hzero with hh | hh
      · exact absurd hh hne
      · exact hh
    simpa only [hf] using hsum0

end

end Work.FIArea6Hecke.CGD
