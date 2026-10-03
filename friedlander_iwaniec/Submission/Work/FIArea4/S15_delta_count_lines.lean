import Mathlib
import Submission.Work.FIArea4.S15_hard_defs
import Submission.Work.FIArea4.S15delta
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea4.S15box

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 1000000

/-!
# `Submission.Work.FIArea4.S15_delta_count_lines`

The double count

  `Σ_{q ≤ Q} #{z₂ ∈ polarBox : 4q ∣ |Δ(z₁,z₂)|, Δ(z₁,z₂) ≠ 0} ≪ (θN + 1)(log Q + 1) + Q`

of FI §15.  The estimate is *not* the per-`q` lattice count `≪ θ²N/q + √N + 1` summed over `q`
(the additive `√N` per modulus would give `Q√N`, which the target does not allow).  Instead the
input is the *linear* function `z₂ ↦ Δ(z₁,z₂)`: it is Lipschitz of constant `|z₁|`, so its values
on the polar box lie in an interval of length `≪ ρ|z₁| ≪ θN`, while `(z₁.re, z₁.im) = 1` forces
the fibres of `z₂ ↦ Δ(z₁,z₂)` on the (thin) polar box to be spaced at least `|z₁|` apart, hence of
cardinality at most `≪ ρ/|z₁| + 1 ≤ 21`.  Counting multiples of `4q` inside the interval gives
`N_q ≪ θN/q + 1`, and `Σ_{q ≤ Q} 1/q ≤ log Q + 1` finishes.
-/

/-- `Δ(z₁,z₁) = 0`. -/
lemma Delta_self (z1 : GaussianInt) : Work.FIPlan.Delta z1 z1 = 0 := by
  rw [Work.FIArea4.Delta_eq]; ring

/-- **Lipschitz bound for `Δ` in its second argument:**
`|Δ(z₁,z) - Δ(z₁,w)| ≤ |z₁|·‖z - w‖`. -/
lemma abs_Delta_sub_le (z1 z w : GaussianInt) :
    |((Work.FIPlan.Delta z1 z : ℤ) : ℝ) - ((Work.FIPlan.Delta z1 w : ℤ) : ℝ)|
      ≤ ‖z1.toComplex‖ * ‖z.toComplex - w.toComplex‖ := by
  have h1 : ((Work.FIPlan.Delta z1 z : ℤ) : ℝ) - ((Work.FIPlan.Delta z1 w : ℤ) : ℝ)
      = ((Work.FIPlan.Delta z1 (z - w) : ℤ) : ℝ) := by
    rw [← Int.cast_sub]
    congr 1
    rw [Work.FIArea4.Delta_eq, Work.FIArea4.Delta_eq, Work.FIArea4.Delta_eq]
    simp only [Zsqrtd.im_sub, Zsqrtd.re_sub]
    ring
  rw [h1]
  have h2 : ((Work.FIPlan.Delta z1 (z - w) : ℤ) : ℝ)
      = ((starRingEnd ℂ) z1.toComplex * (z - w).toComplex).im := by
    rw [Work.FIPlan.Delta, GaussianInt.intCast_im, GaussianInt.toComplex_mul,
      GaussianInt.toComplex_star]
  rw [h2]
  calc |((starRingEnd ℂ) z1.toComplex * (z - w).toComplex).im|
      ≤ ‖(starRingEnd ℂ) z1.toComplex * (z - w).toComplex‖ := Complex.abs_im_le_norm _
    _ = ‖z1.toComplex‖ * ‖(z - w).toComplex‖ := by rw [norm_mul, Complex.norm_conj]
    _ = ‖z1.toComplex‖ * ‖z.toComplex - w.toComplex‖ := by rw [map_sub]

/-- **Fibre bound.**  For a finite set `T` of Gaussian integers of diameter `≤ 2ρ` and a
Gaussian integer `z₁` with `z₁.re ≠ 0` and `(z₁.re, z₁.im) = 1`, every value of `z ↦ Δ(z₁,z)` is
attained at most `4ρ/|z₁| + 1` times on `T`.

The points of the fibre differ from a fixed one by a multiple of the primitive vector
`(z₁.re, z₁.im)`, hence are spaced `|z₁|` apart inside a set of diameter `2ρ`. -/
lemma card_Delta_fiber_le {T : Finset GaussianInt} {z1 : GaussianInt} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hr : z1.re ≠ 0) (hcop : IsCoprime z1.re z1.im)
    (hdiam : ∀ z ∈ T, ∀ w ∈ T, ‖z.toComplex - w.toComplex‖ ≤ 2 * ρ) (m : ℤ) :
    ((T.filter (fun z => Work.FIPlan.Delta z1 z = m)).card : ℝ) ≤ 4 * ρ / ‖z1.toComplex‖ + 1 := by
  classical
  set F : Finset GaussianInt := T.filter (fun z => Work.FIPlan.Delta z1 z = m) with hFdef
  have hz1pos : 0 < ‖z1.toComplex‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hr
    have h1 := GaussianInt.intCast_re z1
    rw [h0, Complex.zero_re] at h1
    exact_mod_cast h1
  rcases F.eq_empty_or_nonempty with h | hne
  · rw [h]; simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · obtain ⟨z0, hz0⟩ := hne
    have hz0F : Work.FIPlan.Delta z1 z0 = m := (Finset.mem_filter.mp hz0).2
    have hz0T : z0 ∈ T := (Finset.mem_filter.mp hz0).1
    let g : GaussianInt → ℤ := fun z => (z.re - z0.re) / z1.re
    have hrel : ∀ z ∈ F, z1.re * (z.im - z0.im) = z1.im * (z.re - z0.re) := by
      intro z hz
      have hzF : Work.FIPlan.Delta z1 z = m := (Finset.mem_filter.mp hz).2
      rw [Work.FIArea4.Delta_eq] at hzF
      rw [Work.FIArea4.Delta_eq] at hz0F
      linarith
    have hdiv : ∀ z ∈ F, z1.re ∣ (z.re - z0.re) := by
      intro z hz
      have h := hrel z hz
      have h2 : z1.re ∣ z1.im * (z.re - z0.re) := ⟨z.im - z0.im, h.symm⟩
      rw [mul_comm] at h2
      exact hcop.dvd_of_dvd_mul_right h2
    have hgzre : ∀ z ∈ F, z.re - z0.re = z1.re * g z := by
      intro z hz
      exact (Int.mul_ediv_cancel' (hdiv z hz)).symm
    have hgzim : ∀ z ∈ F, z.im - z0.im = z1.im * g z := by
      intro z hz
      have h := hrel z hz
      have hre := hgzre z hz
      have hh : z1.re * (z.im - z0.im) = z1.re * (z1.im * g z) := by rw [h, hre]; ring
      exact mul_left_cancel₀ hr hh
    have hdecomp : ∀ z ∈ F, z - z0 = (g z : GaussianInt) * z1 := by
      intro z hz
      have h1 := hgzre z hz
      have h2 := hgzim z hz
      apply Zsqrtd.ext
      · simp only [Zsqrtd.re_sub, Zsqrtd.re_mul]
        rw [h1]; simp; ring
      · simp only [Zsqrtd.im_sub, Zsqrtd.im_mul]
        rw [h2]; simp; ring
    have hgbound : ∀ z ∈ F, |(g z : ℝ)| ≤ 2 * ρ / ‖z1.toComplex‖ := by
      intro z hz
      have hzT : z ∈ T := (Finset.mem_filter.mp hz).1
      have hdist := hdiam z hzT z0 hz0T
      have hde := hdecomp z hz
      have hcoe : (z.toComplex - z0.toComplex) = (g z : ℂ) * z1.toComplex := by
        rw [← map_sub, hde, map_mul]; congr 1; simp
      have hnorm : ‖(g z : ℂ) * z1.toComplex‖ = |(g z : ℝ)| * ‖z1.toComplex‖ := by
        rw [norm_mul, Complex.norm_intCast]
      rw [hcoe, hnorm] at hdist
      rw [le_div_iff₀ hz1pos]
      linarith
    have hinj : Set.InjOn g (↑F : Set GaussianInt) := by
      intro z hz w hw hzw
      have h1 := hdecomp z hz
      have h2 := hdecomp w hw
      have h3 : z - z0 = w - z0 := by rw [h1, h2, hzw]
      have h4 : z.re - z0.re = w.re - z0.re := by rw [← Zsqrtd.re_sub, ← Zsqrtd.re_sub, h3]
      have h5 : z.im - z0.im = w.im - z0.im := by rw [← Zsqrtd.im_sub, ← Zsqrtd.im_sub, h3]
      exact Zsqrtd.ext (by omega) (by omega)
    have hcard : (F.card : ℝ) = ((F.image g).card : ℝ) := by
      rw [Finset.card_image_of_injOn hinj]
    rw [hcard]
    have hρ' : (0:ℝ) ≤ 2 * ρ / ‖z1.toComplex‖ := by positivity
    have hmain := Work.FIArea4.card_int_le_of_mem_interval (F.image g)
      (t := -(2 * ρ / ‖z1.toComplex‖)) (ρ := 2 * ρ / ‖z1.toComplex‖) hρ' ?_
    · have heq : 2 * (2 * ρ / ‖z1.toComplex‖) + 1 = 4 * ρ / ‖z1.toComplex‖ + 1 := by ring
      linarith [hmain, heq.le]
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hb := hgbound z hz
      rw [abs_le] at hb
      exact ⟨hb.1, by linarith [hb.2]⟩

/-- **Per-modulus count.**  For a thin set `T` (diameter `≤ 2ρ`) and `z₁` as above, the number of
`z ∈ T` with `4q ∣ Δ(z₁,z)` and `Δ(z₁,z) ≠ 0` is `≤ (4ρ/|z₁| + 1)·(ρ|z₁|/q + 1)`.

The fibre bound controls the multiplicity of each value, and the values themselves lie in an
interval of length `2·2ρ|z₁|`, so the number of multiples of `4q` in it is `≤ ρ|z₁|/q + 1`. -/
lemma card_Delta_dvd_le {T : Finset GaussianInt} {z1 : GaussianInt} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hr : z1.re ≠ 0) (hcop : IsCoprime z1.re z1.im)
    (hdiam : ∀ z ∈ T, ∀ w ∈ T, ‖z.toComplex - w.toComplex‖ ≤ 2 * ρ)
    (hspan : ∀ z ∈ T, |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| ≤ 2 * ρ * ‖z1.toComplex‖)
    (q : ℕ) (hq : 1 ≤ q) :
    ((T.filter (fun z => (4 * q : ℤ) ∣ Work.FIPlan.Delta z1 z
        ∧ Work.FIPlan.Delta z1 z ≠ 0)).card : ℝ)
      ≤ (4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖ / q + 1) := by
  classical
  have hz1pos : 0 < ‖z1.toComplex‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hr
    have h1 := GaussianInt.intCast_re z1
    rw [h0, Complex.zero_re] at h1
    exact_mod_cast h1
  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have h4qpos : (0:ℝ) < ((4 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 4 * q)
  set S : Finset GaussianInt := T.filter (fun z => (4 * q : ℤ) ∣ Work.FIPlan.Delta z1 z
      ∧ Work.FIPlan.Delta z1 z ≠ 0) with hS
  set f : GaussianInt → ℤ := fun z => Work.FIPlan.Delta z1 z / (4 * q : ℤ) with hf
  have hfiber : ∀ k ∈ S.image f,
      ((S.filter (fun z => f z = k)).card : ℝ) ≤ 4 * ρ / ‖z1.toComplex‖ + 1 := by
    intro k hk
    have hsub : S.filter (fun z => f z = k)
        ⊆ T.filter (fun z => Work.FIPlan.Delta z1 z = (4 * q : ℤ) * k) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      obtain ⟨hzS, hzk⟩ := hz
      have hS' := Finset.mem_filter.mp hzS
      refine ⟨hS'.1, ?_⟩
      have h4 : (4 * q : ℤ) * f z = Work.FIPlan.Delta z1 z := Int.mul_ediv_cancel' hS'.2.1
      rw [hzk] at h4
      exact h4.symm
    have hle : ((S.filter (fun z => f z = k)).card : ℝ)
        ≤ ((T.filter (fun z => Work.FIPlan.Delta z1 z = (4 * q : ℤ) * k)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact hle.trans (card_Delta_fiber_le hρ hr hcop hdiam _)
  have hcardS : (S.card : ℝ)
      ≤ (4 * ρ / ‖z1.toComplex‖ + 1) * ((S.image f).card : ℝ) := by
    have hmaps : Set.MapsTo f ↑S ↑(S.image f) := fun z hz => Finset.mem_image_of_mem _ hz
    have h1 : (S.card : ℝ) = ∑ k ∈ S.image f, ((S.filter (fun z => f z = k)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    rw [h1]
    calc ∑ k ∈ S.image f, ((S.filter (fun z => f z = k)).card : ℝ)
        ≤ ∑ _k ∈ S.image f, (4 * ρ / ‖z1.toComplex‖ + 1) := Finset.sum_le_sum hfiber
      _ = ((S.image f).card : ℝ) * (4 * ρ / ‖z1.toComplex‖ + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (4 * ρ / ‖z1.toComplex‖ + 1) * ((S.image f).card : ℝ) := by ring
  have himg : ((S.image f).card : ℝ) ≤ ρ * ‖z1.toComplex‖ / q + 1 := by
    have hA : (0:ℝ) ≤ ρ * ‖z1.toComplex‖ / (2 * q) := by positivity
    have hmain := Work.FIArea4.card_int_le_of_mem_interval (S.image f)
      (t := -(ρ * ‖z1.toComplex‖ / (2 * q))) (ρ := ρ * ‖z1.toComplex‖ / (2 * q)) hA ?_
    · have heq : 2 * (ρ * ‖z1.toComplex‖ / (2 * q)) + 1 = ρ * ‖z1.toComplex‖ / q + 1 := by
        field_simp
      linarith [hmain, heq.le]
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hS' := Finset.mem_filter.mp hz
      have h4 : (4 * q : ℤ) * f z = Work.FIPlan.Delta z1 z := Int.mul_ediv_cancel' hS'.2.1
      have h4R : ((4 * q : ℕ) : ℝ) * (f z : ℝ) = ((Work.FIPlan.Delta z1 z : ℤ) : ℝ) := by
        rw [← h4]; push_cast; ring
      have hae : ((4 * q : ℕ) : ℝ) * |(f z : ℝ)| = |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| := by
        rw [← h4R, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((4 * q : ℕ) : ℝ))]
      have hle : ((4 * q : ℕ) : ℝ) * |(f z : ℝ)| ≤ 2 * ρ * ‖z1.toComplex‖ := by
        rw [hae]; exact hspan z hS'.1
      have hb : |(f z : ℝ)| ≤ ρ * ‖z1.toComplex‖ / (2 * q) := by
        have hAeq : ρ * ‖z1.toComplex‖ / (2 * q) * ((4 * q : ℕ) : ℝ)
            = 2 * ρ * ‖z1.toComplex‖ := by
          push_cast
          field_simp
          ring
        have hgt : |(f z : ℝ)| * ((4 * q : ℕ) : ℝ)
            ≤ ρ * ‖z1.toComplex‖ / (2 * q) * ((4 * q : ℕ) : ℝ) := by
          rw [hAeq, mul_comm |(f z : ℝ)| ((4 * q : ℕ) : ℝ)]
          exact hle
        exact le_of_mul_le_mul_right hgt h4qpos
      rw [abs_le] at hb
      exact ⟨hb.1, by linarith [hb.2]⟩
  have hK0 : (0:ℝ) ≤ 4 * ρ / ‖z1.toComplex‖ + 1 := by
    have h2 : (0:ℝ) ≤ 4 * ρ / ‖z1.toComplex‖ :=
      div_nonneg (by linarith [hρ]) (norm_nonneg _)
    linarith
  exact hcardS.trans (mul_le_mul_of_nonneg_left himg hK0)

/-- The harmonic sum bound in the form used below. -/
lemma sum_inv_Icc_le_log (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / q) ≤ Real.log (Q : ℝ) + 1 := by
  have h1 : (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / q) = ((harmonic Q : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [one_div, Rat.cast_inv, Rat.cast_natCast]
  rw [h1]
  simpa [add_comm] using harmonic_le_one_add_log Q

/-- **FI §15, the double count of `Δ`-divisibility lines.** -/
theorem S15_delta_count_lines :
    ∃ C : ℝ, 0 < C ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z1 : GaussianInt) (Q : ℕ),
      z1 ∈ Work.FIArea4.S15polarBox Pa φ → Nat.Coprime z1.re.natAbs z1.im.natAbs → 1 ≤ Q →
      (∑ q ∈ Finset.Icc 1 Q,
          ((((Work.FIArea4.S15polarBox Pa φ).filter
              (fun z2 => 4 * q ∣ Work.FIPlan.absDelta z1 z2
                ∧ Work.FIPlan.absDelta z1 z2 ≠ 0)).card : ℕ) : ℝ))
        ≤ C * ((Pa.θ * Pa.N + 1) * (Real.log ((Q : ℝ) + 2) + 1) + (Q : ℝ)) := by
  refine ⟨200, by norm_num, ?_⟩
  intro Pa φ z1 Q hz1 hcop hQ
  have hz1box : z1 ∈ Work.FITop.boxN Pa ∧ Work.FITop3.InPolarBox Pa φ z1 :=
    Work.FIArea4.mem_S15polarBox.mp hz1
  set c0 : ℂ := (Real.sqrt Pa.N : ℂ)
    * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I) with hc0
  set ρ : ℝ := 5 * Pa.θ * Real.sqrt Pa.N with hρdef
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea4.theta_le_one Pa
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]
    exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Pa.hθ0)) (Real.sqrt_nonneg _)
  have hcopI : IsCoprime z1.re z1.im := Int.isCoprime_iff_nat_coprime.mpr hcop
  -- the polar box lies in a disc of radius `ρ`
  have hTball : ∀ z ∈ Work.FIArea4.S15polarBox Pa φ, ‖z.toComplex - c0‖ ≤ ρ := by
    intro z hz
    have hbox : Work.FITop3.InPolarBox Pa φ z := (Work.FIArea4.mem_S15polarBox.mp hz).2
    rw [hc0, hρdef]
    exact Work.FIArea4.dist_polarBox_le Pa φ z hbox
  have hdiam : ∀ z ∈ Work.FIArea4.S15polarBox Pa φ, ∀ w ∈ Work.FIArea4.S15polarBox Pa φ,
      ‖z.toComplex - w.toComplex‖ ≤ 2 * ρ := by
    intro z hz w hw
    have h1 := hTball z hz
    have h2 := hTball w hw
    have he : z.toComplex - w.toComplex = (z.toComplex - c0) - (w.toComplex - c0) := by ring
    rw [he]
    calc ‖(z.toComplex - c0) - (w.toComplex - c0)‖
        ≤ ‖z.toComplex - c0‖ + ‖w.toComplex - c0‖ := norm_sub_le _ _
      _ ≤ ρ + ρ := add_le_add h1 h2
      _ = 2 * ρ := by ring
  -- `|z₁| > √N` and `1 < |z₁|²`
  have hLl : Real.sqrt Pa.N < ‖z1.toComplex‖ := by
    rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
    exact Real.sqrt_lt_sqrt hN0 hz1box.2.2.1
  have hgn1 : (1:ℝ) < (Work.FIPlan.gnorm z1 : ℝ) := by
    have h1 := hz1box.2.2.1
    linarith
  -- both coordinates of `z₁` are nonzero
  have hz1r : z1.re ≠ 0 := by
    intro h
    have hc0' : Nat.Coprime 0 z1.im.natAbs := by
      rw [h] at hcop; simpa using hcop
    have him1 : z1.im.natAbs = 1 := (Nat.coprime_zero_left _).mp hc0'
    have hsq : z1.im * z1.im = 1 := by
      have hh := Int.natAbs_mul_self (a := z1.im)
      rw [him1] at hh
      simpa using hh.symm
    have hgn : Work.FIPlan.gnorm z1 = 1 := by
      rw [Work.FIPlan.gnorm]
      have hnorm : Zsqrtd.norm z1 = z1.re * z1.re + z1.im * z1.im := by simp [Zsqrtd.norm]
      rw [hnorm, h, hsq]
      norm_num
    have : (Work.FIPlan.gnorm z1 : ℝ) = 1 := by exact_mod_cast hgn
    linarith [hgn1, this]
  -- the image of `Δ(z₁,·)` on the box lies in `[-2ρ|z₁|, 2ρ|z₁|]`
  have hspan : ∀ z ∈ Work.FIArea4.S15polarBox Pa φ,
      |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| ≤ 2 * ρ * ‖z1.toComplex‖ := by
    intro z hz
    have h := abs_Delta_sub_le z1 z z1
    have h0 : ((Work.FIPlan.Delta z1 z1 : ℤ) : ℝ) = 0 := by
      rw [Delta_self]; norm_num
    rw [h0, sub_zero] at h
    have h2 := hdiam z hz z1 hz1
    calc |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)|
        ≤ ‖z1.toComplex‖ * ‖z.toComplex - z1.toComplex‖ := h
      _ ≤ ‖z1.toComplex‖ * (2 * ρ) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = 2 * ρ * ‖z1.toComplex‖ := by ring
  -- per-modulus bound
  have hper : ∀ q ∈ Finset.Icc 1 Q,
      ((((Work.FIArea4.S15polarBox Pa φ).filter (fun z2 => (4 * q : ℤ) ∣ Work.FIPlan.Delta z1 z2
          ∧ Work.FIPlan.Delta z1 z2 ≠ 0)).card : ℕ) : ℝ)
        ≤ (4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖ / q + 1) := by
    intro q hq
    have h1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    exact card_Delta_dvd_le hρ0 hz1r hcopI hdiam hspan q h1
  -- the two predicates coincide
  have hconv : ∀ q : ℕ,
      ((((Work.FIArea4.S15polarBox Pa φ).filter (fun z2 => 4 * q ∣ Work.FIPlan.absDelta z1 z2
          ∧ Work.FIPlan.absDelta z1 z2 ≠ 0)).card : ℕ) : ℝ)
        = ((((Work.FIArea4.S15polarBox Pa φ).filter (fun z2 => (4 * q : ℤ) ∣ Work.FIPlan.Delta z1 z2
          ∧ Work.FIPlan.Delta z1 z2 ≠ 0)).card : ℕ) : ℝ) := by
    intro q
    have h1 : ∀ z2 : GaussianInt, (4 * q ∣ Work.FIPlan.absDelta z1 z2)
        ↔ ((4 * q : ℤ) ∣ Work.FIPlan.Delta z1 z2) := by
      intro z2
      rw [Work.FIArea4.dvd_absDelta_iff, Work.FIArea4.Delta_eq]
    have h2 : ∀ z2 : GaussianInt, (Work.FIPlan.absDelta z1 z2 ≠ 0)
        ↔ (Work.FIPlan.Delta z1 z2 ≠ 0) := by
      intro z2
      rw [Work.FIPlan.absDelta, Int.natAbs_ne_zero]
    have hf : (Work.FIArea4.S15polarBox Pa φ).filter
          (fun z2 => 4 * q ∣ Work.FIPlan.absDelta z1 z2 ∧ Work.FIPlan.absDelta z1 z2 ≠ 0)
        = (Work.FIArea4.S15polarBox Pa φ).filter
          (fun z2 => (4 * q : ℤ) ∣ Work.FIPlan.Delta z1 z2
            ∧ Work.FIPlan.Delta z1 z2 ≠ 0) := by
      apply Finset.filter_congr
      intro z2 _
      rw [h1 z2, h2 z2]
    rw [hf]
  have hsum_conv : (∑ q ∈ Finset.Icc 1 Q,
        ((((Work.FIArea4.S15polarBox Pa φ).filter (fun z2 => 4 * q ∣ Work.FIPlan.absDelta z1 z2
            ∧ Work.FIPlan.absDelta z1 z2 ≠ 0)).card : ℕ) : ℝ))
      = ∑ q ∈ Finset.Icc 1 Q,
        ((((Work.FIArea4.S15polarBox Pa φ).filter (fun z2 => (4 * q : ℤ) ∣ Work.FIPlan.Delta z1 z2
            ∧ Work.FIPlan.Delta z1 z2 ≠ 0)).card : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact hconv q
  -- the sum of the per-modulus bounds
  have hsumval : (∑ q ∈ Finset.Icc 1 Q,
        (4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖ / q + 1))
      = (4 * ρ / ‖z1.toComplex‖ + 1)
        * (ρ * ‖z1.toComplex‖ * (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / q) + (Q : ℝ)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [div_eq_mul_inv, one_div]
    · rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp
  have hK0 : (0:ℝ) ≤ 4 * ρ / ‖z1.toComplex‖ + 1 := by
    have h2 : (0:ℝ) ≤ 4 * ρ / ‖z1.toComplex‖ :=
      div_nonneg (by linarith [hρ0]) (norm_nonneg _)
    linarith
  have hρL0 : (0:ℝ) ≤ ρ * ‖z1.toComplex‖ := mul_nonneg hρ0 (norm_nonneg _)
  have hharm := sum_inv_Icc_le_log Q
  have hlog0 : (0:ℝ) ≤ Real.log (Q : ℝ) + 1 := by
    have h1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
    have h2 := Real.log_nonneg h1
    linarith
  have hQ0 : (0:ℝ) ≤ (Q:ℝ) := by positivity
  -- constants
  have hKle : 4 * ρ / ‖z1.toComplex‖ + 1 ≤ 21 := by
    have hLpos : 0 < ‖z1.toComplex‖ := lt_of_le_of_lt (Real.sqrt_nonneg _) hLl
    have h1 : 4 * ρ / ‖z1.toComplex‖ ≤ 20 * Pa.θ := by
      rw [hρdef, div_le_iff₀ hLpos]
      have h2 := mul_lt_mul_of_pos_left hLl (by linarith [Pa.hθ0] : (0:ℝ) < 20 * Pa.θ)
      nlinarith [h2]
    nlinarith [h1, hθ1]
  have hLle : ‖z1.toComplex‖ ≤ Real.sqrt (2 * Pa.N) := by
    rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
    apply Real.sqrt_le_sqrt
    nlinarith [hz1box.2.2.2.1, hθ1]
  have hsqrt2 : Real.sqrt 2 ≤ 8 / 5 := by
    have h := Real.sqrt_le_sqrt (show (2:ℝ) ≤ (8/5)^2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 8 / 5)] at h
  have hsN : Real.sqrt Pa.N * Real.sqrt (2 * Pa.N) ≤ (8/5) * Pa.N := by
    have h1 : Real.sqrt Pa.N * Real.sqrt (2 * Pa.N) = Real.sqrt 2 * Pa.N := by
      rw [← Real.sqrt_mul hN0]
      rw [show Pa.N * (2 * Pa.N) = 2 * Pa.N ^ 2 by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hN0]
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_right hsqrt2 hN0
    linarith [h2]
  have hρLle : ρ * ‖z1.toComplex‖ ≤ 8 * (Pa.θ * Pa.N) := by
    calc ρ * ‖z1.toComplex‖ ≤ (5 * Pa.θ * Real.sqrt Pa.N) * Real.sqrt (2 * Pa.N) := by
          apply mul_le_mul_of_nonneg_left hLle
          rw [hρdef]
          exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt Pa.hθ0)) (Real.sqrt_nonneg _)
      _ = 5 * Pa.θ * (Real.sqrt Pa.N * Real.sqrt (2 * Pa.N)) := by ring
      _ ≤ 5 * Pa.θ * ((8/5) * Pa.N) := by
          apply mul_le_mul_of_nonneg_left hsN (mul_nonneg (by norm_num) (le_of_lt Pa.hθ0))
      _ = 8 * (Pa.θ * Pa.N) := by ring
  have ha0 : (0:ℝ) ≤ Pa.θ * Pa.N := mul_nonneg (le_of_lt Pa.hθ0) hN0
  have hQ1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
  have hlogle : Real.log (Q : ℝ) ≤ Real.log ((Q : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog20 : (0:ℝ) ≤ Real.log ((Q : ℝ) + 2) + 1 := by
    have h1 : (1:ℝ) ≤ (Q:ℝ) + 2 := by linarith
    have h2 := Real.log_nonneg h1
    linarith
  have hKρL : (4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖)
      ≤ 21 * (8 * (Pa.θ * Pa.N)) :=
    mul_le_mul hKle hρLle hρL0 (by norm_num)
  have hbound1 : (4 * ρ / ‖z1.toComplex‖ + 1)
        * (ρ * ‖z1.toComplex‖ * (Real.log (Q : ℝ) + 1) + (Q : ℝ))
      ≤ 168 * (Pa.θ * Pa.N) * (Real.log (Q : ℝ) + 1) + 21 * (Q : ℝ) := by
    have hA : (4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖ * (Real.log (Q:ℝ) + 1))
        ≤ 168 * (Pa.θ * Pa.N) * (Real.log (Q : ℝ) + 1) := by
      have h3 := mul_le_mul_of_nonneg_right hKρL hlog0
      calc (4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖ * (Real.log (Q:ℝ) + 1))
          = ((4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖)) * (Real.log (Q:ℝ) + 1) := by
            ring
        _ ≤ (21 * (8 * (Pa.θ * Pa.N))) * (Real.log (Q:ℝ) + 1) := h3
        _ = 168 * (Pa.θ * Pa.N) * (Real.log (Q:ℝ) + 1) := by ring
    have hB : (4 * ρ / ‖z1.toComplex‖ + 1) * (Q:ℝ) ≤ 21 * (Q:ℝ) :=
      mul_le_mul_of_nonneg_right hKle hQ0
    calc (4 * ρ / ‖z1.toComplex‖ + 1)
          * (ρ * ‖z1.toComplex‖ * (Real.log (Q : ℝ) + 1) + (Q : ℝ))
        = (4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖ * (Real.log (Q:ℝ) + 1))
            + (4 * ρ / ‖z1.toComplex‖ + 1) * (Q:ℝ) := by ring
      _ ≤ 168 * (Pa.θ * Pa.N) * (Real.log (Q : ℝ) + 1) + 21 * (Q : ℝ) := add_le_add hA hB
  have hbound2 : 168 * (Pa.θ * Pa.N) * (Real.log (Q : ℝ) + 1) + 21 * (Q : ℝ)
      ≤ 200 * ((Pa.θ * Pa.N + 1) * (Real.log ((Q : ℝ) + 2) + 1) + (Q : ℝ)) := by
    have h1 : 168 * (Pa.θ * Pa.N) * (Real.log (Q : ℝ) + 1)
        ≤ 200 * (Pa.θ * Pa.N + 1) * (Real.log ((Q : ℝ) + 2) + 1) := by
      calc 168 * (Pa.θ * Pa.N) * (Real.log (Q : ℝ) + 1)
          ≤ 168 * (Pa.θ * Pa.N) * (Real.log ((Q : ℝ) + 2) + 1) := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) ha0)
              linarith [hlogle]
        _ ≤ 200 * (Pa.θ * Pa.N + 1) * (Real.log ((Q : ℝ) + 2) + 1) := by
              apply mul_le_mul_of_nonneg_right _ hlog20
              nlinarith [ha0]
    have hexp : 200 * ((Pa.θ * Pa.N + 1) * (Real.log ((Q : ℝ) + 2) + 1) + (Q : ℝ))
        = 200 * (Pa.θ * Pa.N + 1) * (Real.log ((Q : ℝ) + 2) + 1) + 200 * (Q : ℝ) := by ring
    rw [hexp]
    linarith [h1, hQ0]
  rw [hsum_conv]
  calc (∑ q ∈ Finset.Icc 1 Q,
        ((((Work.FIArea4.S15polarBox Pa φ).filter (fun z2 => (4 * q : ℤ) ∣ Work.FIPlan.Delta z1 z2
            ∧ Work.FIPlan.Delta z1 z2 ≠ 0)).card : ℕ) : ℝ))
      ≤ ∑ q ∈ Finset.Icc 1 Q,
          (4 * ρ / ‖z1.toComplex‖ + 1) * (ρ * ‖z1.toComplex‖ / q + 1) :=
        Finset.sum_le_sum hper
    _ = (4 * ρ / ‖z1.toComplex‖ + 1)
        * (ρ * ‖z1.toComplex‖ * (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / q) + (Q : ℝ)) := hsumval
    _ ≤ (4 * ρ / ‖z1.toComplex‖ + 1)
        * (ρ * ‖z1.toComplex‖ * (Real.log (Q : ℝ) + 1) + (Q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hharm hρL0) le_rfl) hK0
    _ ≤ 168 * (Pa.θ * Pa.N) * (Real.log (Q : ℝ) + 1) + 21 * (Q : ℝ) := hbound1
    _ ≤ 200 * ((Pa.θ * Pa.N + 1) * (Real.log ((Q : ℝ) + 2) + 1) + (Q : ℝ)) := hbound2

end

end Work.FIArea4
