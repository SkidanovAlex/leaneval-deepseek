import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea6.card_fiber_mod_le
import Submission.Work.FIArea7.dvd_delta_iff_exists_omega
import Submission.Work.FIArea6b.disc_strip_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `Δ(z₁,z₂) = -Δ(z₂,z₁)`. -/
lemma Delta_eq_neg (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = -Work.FIPlan.Delta z2 z1 := by
  rw [Work.FIArea7.Delta_eq, Work.FIArea7.Delta_eq]
  ring

/-- The near-diagonal `Δ`-fibre count (`fibCountDvdNear`): as `card_dvd_delta_fiber_le`, but with the extra condition `|Δ(z₁,z₂)| ≤ M`. Writing the solutions of `4d ∣ Δ(z₁,z₂)` as `z₂ = ω z₁ + 4d·k` (at most `4d` classes `ω`, each `ω` a unit mod `4d`), the condition becomes `|Im(z̄₁ k)| ≤ M/(4d)`: a strip of width `M/(2d|z₁|)` through the disc of radius `5θ√N/(4d)`, which contains at most a constant times `(10θ√N/(4d)+1)·(M/(2d√N)+1)` lattice points. -/
theorem card_dvd_delta_fiber_near_le (Pa : Work.FITop.Params) (φ : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (z1 : GaussianInt) (hz1 : Work.FITop3.InPolarBox Pa φ z1)
    (hcop : Nat.Coprime (Work.FIPlan.gnorm z1) (4 * d)) (M : ℝ) (hM : 0 ≤ M) :
    (Work.FIArea6.fibCountDvdNear Pa φ d M z1 : ℝ)
      ≤ 4 * (d : ℝ) * (10 * Pa.θ * Real.sqrt Pa.N / (4 * (d : ℝ)) + 1)
          * (M / (2 * (d : ℝ) * Real.sqrt Pa.N) + 1) := by
  set q : ℕ := 4 * d with hqdef
  have hq4 : 4 ≤ q := by rw [hqdef]; exact Nat.mul_le_mul_left 4 hd
  have hq1 : 1 ≤ q := by omega
  haveI : NeZero q := ⟨by omega⟩
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  set ρ : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hρdef
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    exact mul_nonneg (mul_nonneg (by norm_num) Pa.hθ0.le) (Real.sqrt_nonneg _)
  set c0 : ℂ := (Real.sqrt Pa.N : ℂ) * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I)
    with hc0def
  set S : Finset GaussianInt := (Work.FITop.boxN Pa).filter
    (fun z => Work.FITop3.InPolarBox Pa φ z ∧ Nat.Coprime (Work.FIPlan.gnorm z) q ∧
      q ∣ Work.FIPlan.absDelta z1 z ∧ (Work.FIPlan.Delta z1 z).natAbs ≤ M) with hSdef
  have hcard_eq : Work.FIArea6.fibCountDvdNear Pa φ d M z1 = S.card := rfl
  rw [hcard_eq]
  have hSspec : ∀ z ∈ S, Work.FITop3.InPolarBox Pa φ z ∧ Nat.Coprime (Work.FIPlan.gnorm z) q ∧
      q ∣ Work.FIPlan.absDelta z1 z ∧ (Work.FIPlan.Delta z1 z).natAbs ≤ M := by
    intro z hz
    rw [hSdef] at hz
    exact (Finset.mem_filter.mp hz).2
  have hdist : ∀ z ∈ S, ‖z.toComplex - c0‖ ≤ ρ := by
    intro z hz
    rw [hc0def, hρdef]
    exact Work.FIArea4.dist_polarBox_le Pa φ z (hSspec z hz).1
  have hz1ne : z1.re ≠ 0 ∨ z1.im ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : z1 = 0 := Zsqrtd.ext (by simpa using h.1) (by simpa using h.2)
    have h1 : Pa.N < (Work.FIPlan.gnorm z1 : ℝ) := (hz1).2.1
    have h2 : (Work.FIPlan.gnorm z1 : ℝ) = 0 := by
      rw [h0]; simp [Work.FIPlan.gnorm, Zsqrtd.norm]
    have h3 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
    rw [h2] at h1; linarith
  have hexists : ∀ z ∈ S, ∃ ω : ZMod q, (z.re : ZMod q) = ω * (z1.re : ZMod q) ∧
      (z.im : ZMod q) = ω * (z1.im : ZMod q) := by
    intro z hz
    obtain ⟨-, hzcop, hzdvd, -⟩ := hSspec z hz
    have hdvdz : (q : ℤ) ∣ Work.FIPlan.Delta z z1 := by
      have h1 : (q : ℤ) ∣ Work.FIPlan.Delta z1 z := by
        have h2 : (q : ℤ) ∣ (((Work.FIPlan.Delta z1 z).natAbs : ℕ) : ℤ) := by
          exact_mod_cast hzdvd
        exact Int.dvd_natAbs.mp h2
      rw [Delta_eq_neg]
      exact dvd_neg.mpr h1
    exact (Work.FIArea7.dvd_delta_iff_exists_omega (show 0 < q by omega) z z1 hcop).mp hdvdz
  let cls : GaussianInt → ZMod q := fun z => if h : z ∈ S then Classical.choose (hexists z h) else 0
  have hcls : ∀ z (hz : z ∈ S), (z.re : ZMod q) = cls z * (z1.re : ZMod q) ∧
      (z.im : ZMod q) = cls z * (z1.im : ZMod q) := by
    intro z hz
    have h1 : cls z = Classical.choose (hexists z hz) := by simp only [cls, dif_pos hz]
    rw [h1]
    exact Classical.choose_spec (hexists z hz)
  have hcard : S.card = ∑ ω : ZMod q, (S.filter (fun z => cls z = ω)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := cls)
      (s := S) (t := (Finset.univ : Finset (ZMod q))) (fun z _ => Finset.mem_univ _)
    rw [h]
  have hfib : ∀ ω : ZMod q, ((S.filter (fun z => cls z = ω)).card : ℝ)
      ≤ (2 * (ρ / (q:ℝ)) + 1) * (2 * (M / (q:ℝ)) / ‖z1.toComplex‖ + 1) := by
    intro ω
    set F : Finset GaussianInt := S.filter (fun z => cls z = ω) with hFdef
    have hFspec : ∀ z ∈ F, z ∈ S ∧ cls z = ω := by
      intro z hz; rw [hFdef] at hz; exact Finset.mem_filter.mp hz
    have hv : (((ω.val : ℕ) : ℤ) : ZMod q) = ω := by
      rw [Int.cast_natCast]
      exact (ZMod.natCast_val (R := ZMod q) ω).trans (ZMod.cast_id q ω)
    have hdiv : ∀ z ∈ F, (q:ℤ) ∣ (z.re - ((ω.val : ℕ) : ℤ) * z1.re) ∧
        (q:ℤ) ∣ (z.im - ((ω.val : ℕ) : ℤ) * z1.im) := by
      intro z hz
      obtain ⟨hzS, hzcls⟩ := hFspec z hz
      have hc := hcls z hzS
      rw [hzcls] at hc
      constructor
      · have h2 : ((z.re : ℤ) : ZMod q) = ((((ω.val : ℕ) : ℤ) * z1.re : ℤ) : ZMod q) := by
          rw [Int.cast_mul, hv]
          exact hc.1
        have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub z.re (((ω.val : ℕ) : ℤ) * z1.re) q).mp h2
        have h3' : (q:ℤ) ∣ -(z.re - (((ω.val : ℕ) : ℤ) * z1.re)) := by
          rw [neg_sub]; exact h3
        exact dvd_neg.mp h3'
      · have h2 : ((z.im : ℤ) : ZMod q) = ((((ω.val : ℕ) : ℤ) * z1.im : ℤ) : ZMod q) := by
          rw [Int.cast_mul, hv]
          exact hc.2
        have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub z.im (((ω.val : ℕ) : ℤ) * z1.im) q).mp h2
        have h3' : (q:ℤ) ∣ -(z.im - (((ω.val : ℕ) : ℤ) * z1.im)) := by
          rw [neg_sub]; exact h3
        exact dvd_neg.mp h3'
    set kf : GaussianInt → ℤ × ℤ := fun z =>
      ((z.re - ((ω.val : ℕ) : ℤ) * z1.re) / (q:ℤ),
       (z.im - ((ω.val : ℕ) : ℤ) * z1.im) / (q:ℤ)) with hkfdef
    have hkf_eq : ∀ z ∈ F, (kf z).1 * (q:ℤ) = z.re - ((ω.val : ℕ) : ℤ) * z1.re ∧
        (kf z).2 * (q:ℤ) = z.im - ((ω.val : ℕ) : ℤ) * z1.im := by
      intro z hz
      obtain ⟨h1, h2⟩ := hdiv z hz
      exact ⟨Int.ediv_mul_cancel h1, Int.ediv_mul_cancel h2⟩
    have hinj : Set.InjOn kf ↑F := by
      intro z hz z' hz' h
      have hk := hkf_eq z hz
      have hk' := hkf_eq z' hz'
      have h12 : (kf z).1 = (kf z').1 := by rw [h]
      have h34 : (kf z).2 = (kf z').2 := by rw [h]
      have hk1' : (kf z).1 * (q:ℤ) = z'.re - ((ω.val : ℕ) : ℤ) * z1.re := by
        have hh := hk'.1
        rw [← h12] at hh
        exact hh
      have hk2' : (kf z).2 * (q:ℤ) = z'.im - ((ω.val : ℕ) : ℤ) * z1.im := by
        have hh := hk'.2
        rw [← h34] at hh
        exact hh
      have h1 : z.re = z'.re := by linarith [hk.1, hk1']
      have h2 : z.im = z'.im := by linarith [hk.2, hk2']
      exact Zsqrtd.ext h1 h2
    set K : Finset (ℤ × ℤ) := F.image kf with hKdef
    have hKcard : (K.card : ℝ) = (F.card : ℝ) := by
      rw [hKdef, Finset.card_image_of_injOn hinj]
    have hball : ∀ k ∈ K,
        ((k.1 : ℝ) - ((c0.re - ((ω.val : ℕ) : ℝ) * z1.re) / (q:ℝ))) ^ 2
        + ((k.2 : ℝ) - ((c0.im - ((ω.val : ℕ) : ℝ) * z1.im) / (q:ℝ))) ^ 2 ≤ (ρ / (q:ℝ)) ^ 2 := by
      intro k hk
      rw [hKdef] at hk
      obtain ⟨z, hzF, hzk⟩ := Finset.mem_image.mp hk
      obtain ⟨hzS, -⟩ := hFspec z hzF
      rw [← hzk]
      have hkz := hkf_eq z hzF
      have hb := hdist z hzS
      have hnorm : ‖z.toComplex - c0‖ ^ 2
          = ((z.re : ℝ) - c0.re) ^ 2 + ((z.im : ℝ) - c0.im) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          ← Work.FIArea4.ofReal_re_eq_re z, ← Work.FIArea4.ofReal_im_eq_im z]
        ring
      have hb2 : ((z.re : ℝ) - c0.re) ^ 2 + ((z.im : ℝ) - c0.im) ^ 2 ≤ ρ ^ 2 := by
        rw [← hnorm]
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
      have key : ((kf z).1 : ℝ) = ((z.re : ℝ) - ((ω.val : ℕ) : ℝ) * z1.re) / (q:ℝ) := by
        have h := congrArg (fun t : ℤ => (t : ℝ)) hkz.1
        push_cast at h
        have hq0 : ((q:ℤ) : ℝ) ≠ 0 := by
          simp only [Int.cast_natCast]; exact ne_of_gt hqR
        field_simp
        linarith [h]
      have key2 : ((kf z).2 : ℝ) = ((z.im : ℝ) - ((ω.val : ℕ) : ℝ) * z1.im) / (q:ℝ) := by
        have h := congrArg (fun t : ℤ => (t : ℝ)) hkz.2
        push_cast at h
        have hq0 : ((q:ℤ) : ℝ) ≠ 0 := by
          simp only [Int.cast_natCast]; exact ne_of_gt hqR
        field_simp
        linarith [h]
      have hmain : ((kf z).1 : ℝ) - ((c0.re - ((ω.val : ℕ) : ℝ) * z1.re) / (q:ℝ))
          = ((z.re : ℝ) - c0.re) / (q:ℝ) := by
        rw [key]; ring
      have hmain2 : ((kf z).2 : ℝ) - ((c0.im - ((ω.val : ℕ) : ℝ) * z1.im) / (q:ℝ))
          = ((z.im : ℝ) - c0.im) / (q:ℝ) := by
        rw [key2]; ring
      rw [hmain, hmain2, div_pow, div_pow, ← add_div, div_pow]
      exact div_le_div_of_nonneg_right hb2 (sq_nonneg _)
    have hstrip : ∀ k ∈ K,
        |(z1.re : ℝ) * (k.2 : ℝ) - (z1.im : ℝ) * (k.1 : ℝ)| ≤ M / (q:ℝ) := by
      intro k hk
      rw [hKdef] at hk
      obtain ⟨z, hzF, hzk⟩ := Finset.mem_image.mp hk
      obtain ⟨hzS, -⟩ := hFspec z hzF
      obtain ⟨-, -, -, hzM⟩ := hSspec z hzS
      rw [← hzk]
      have hkz := hkf_eq z hzF
      have hD : Work.FIPlan.Delta z1 z
          = (q:ℤ) * (z1.re * (kf z).2 - z1.im * (kf z).1) := by
        rw [Work.FIArea7.Delta_eq]
        have h1 : z.re = ((ω.val : ℕ) : ℤ) * z1.re + (q:ℤ) * (kf z).1 := by linarith [hkz.1]
        have h2 : z.im = ((ω.val : ℕ) : ℤ) * z1.im + (q:ℤ) * (kf z).2 := by linarith [hkz.2]
        rw [h1, h2]; ring
      have hMle : |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| ≤ M := by
        have h3 : ((Work.FIPlan.Delta z1 z).natAbs : ℝ) = |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| := by
          have h4 : (((Work.FIPlan.Delta z1 z).natAbs : ℤ) : ℝ)
              = |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| := by
            rw [Int.natCast_natAbs]
            exact Int.cast_abs
          simpa using h4
        rw [← h3]
        exact hzM
      have hcast : |(z1.re : ℝ) * (kf z).2 - (z1.im : ℝ) * (kf z).1|
          = |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| / (q:ℝ) := by
        rw [hD]
        push_cast
        rw [abs_mul, abs_of_pos hqR]
        field_simp
      rw [hcast]
      exact div_le_div_of_nonneg_right hMle hqR.le
    have hc := Work.FIArea6b.disc_strip_card z1.re z1.im hz1ne (ρ / (q:ℝ)) (M / (q:ℝ))
      (by positivity) (div_nonneg hM hqR.le)
      (((c0.re - ((ω.val : ℕ) : ℝ) * z1.re) / (q:ℝ)),
       ((c0.im - ((ω.val : ℕ) : ℝ) * z1.im) / (q:ℝ))) K hball hstrip
    have hsq : (z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2 = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
      simp only [pow_two]
      rw [Work.FIArea4.ofReal_re_eq_re z1, Work.FIArea4.ofReal_im_eq_im z1]
      rw [← Complex.normSq_apply, ← Complex.sq_norm]
      exact Work.FIArea4.normSq_toComplex_gnorm z1
    have hz1norm : Real.sqrt ((z1.re : ℝ) ^ 2 + (z1.im : ℝ) ^ 2) = ‖z1.toComplex‖ := by
      rw [hsq]
      exact (Work.FIArea4.norm_toComplex_eq_sqrt_gnorm z1).symm
    rw [hz1norm] at hc
    rw [← hKcard]
    exact hc
  have hsum : (S.card : ℝ) ≤ (q : ℝ) * ((2 * (ρ / (q:ℝ)) + 1)
      * (2 * (M / (q:ℝ)) / ‖z1.toComplex‖ + 1)) := by
    rw [hcard]
    push_cast
    calc (∑ ω : ZMod q, ((S.filter (fun z => cls z = ω)).card : ℝ))
        ≤ ∑ _ω : ZMod q, ((2 * (ρ / (q:ℝ)) + 1) * (2 * (M / (q:ℝ)) / ‖z1.toComplex‖ + 1)) :=
          Finset.sum_le_sum (fun ω _ => hfib ω)
      _ = (Fintype.card (ZMod q) : ℝ) * ((2 * (ρ / (q:ℝ)) + 1)
            * (2 * (M / (q:ℝ)) / ‖z1.toComplex‖ + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (q : ℝ) * ((2 * (ρ / (q:ℝ)) + 1) * (2 * (M / (q:ℝ)) / ‖z1.toComplex‖ + 1)) := by
          rw [ZMod.card]
  have hz1ge : Real.sqrt Pa.N ≤ ‖z1.toComplex‖ := by
    rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
    exact Real.sqrt_le_sqrt (le_of_lt (hz1).2.1)
  have hNpos : (0:ℝ) < Real.sqrt Pa.N := by
    have : (0:ℝ) < Pa.N := by exact_mod_cast (lt_of_lt_of_le zero_lt_one Pa.hN1)
    positivity
  have hstep : 2 * (M / (q:ℝ)) / ‖z1.toComplex‖ + 1 ≤ 2 * (M / (q:ℝ)) / Real.sqrt Pa.N + 1 := by
    have h1 : 0 ≤ 2 * (M / (q:ℝ)) := by positivity
    have h2 : 2 * (M / (q:ℝ)) / ‖z1.toComplex‖ ≤ 2 * (M / (q:ℝ)) / Real.sqrt Pa.N :=
      div_le_div_of_nonneg_left h1 hNpos hz1ge
    linarith
  have hfac0 : (0:ℝ) ≤ 2 * (ρ / (q:ℝ)) + 1 := by
    have : 0 ≤ ρ / (q:ℝ) := div_nonneg hρ0 hqR.le
    linarith
  have hgoal : (q : ℝ) * ((2 * (ρ / (q:ℝ)) + 1) * (2 * (M / (q:ℝ)) / Real.sqrt Pa.N + 1))
      = 4 * (d : ℝ) * (10 * Pa.θ * Real.sqrt Pa.N / (4 * (d : ℝ)) + 1)
          * (M / (2 * (d : ℝ) * Real.sqrt Pa.N) + 1) := by
    rw [hρdef, hqdef]
    push_cast
    field_simp
    ring
  calc (S.card : ℝ)
      ≤ (q : ℝ) * ((2 * (ρ / (q:ℝ)) + 1) * (2 * (M / (q:ℝ)) / ‖z1.toComplex‖ + 1)) := hsum
    _ ≤ (q : ℝ) * ((2 * (ρ / (q:ℝ)) + 1) * (2 * (M / (q:ℝ)) / Real.sqrt Pa.N + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hfac0) hqR.le
    _ = 4 * (d : ℝ) * (10 * Pa.θ * Real.sqrt Pa.N / (4 * (d : ℝ)) + 1)
          * (M / (2 * (d : ℝ) * Real.sqrt Pa.N) + 1) := hgoal

end

end Work.FIArea6
