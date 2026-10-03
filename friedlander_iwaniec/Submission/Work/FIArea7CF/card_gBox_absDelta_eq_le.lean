import Mathlib
import Submission.Work.FIArea7CF.card_gBox_filter_dvd_absDelta
import Submission.Work.FIPlan.Interface

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## Counting the fibre `|Δ(z₁,z₂)| = d`

Fix `z₁ = r₁ + i s₁ ≠ 0` with `gcd(r₁,s₁) = 1`, and a target value `d ≥ 0`.  We bound the number
of `z₂` in the box `|re|, |im| ≤ R` with `|Δ(z₁,z₂)| = d`, where `Δ(z₁,z₂) = r₁s₂ − r₂s₁`
(`Work.FIPlan.absDelta`).

The key point is that the two sets `Δ = d` and `Δ = −d` are *affine lines of lattice points*:
if `z₂, z₂'` both satisfy `Δ = c` then `r₁(s₂ − s₂') = s₁(r₂ − r₂')`, and coprimality of `r₁,s₁`
forces `r₁ ∣ r₂ − r₂'` (respectively `s₁ ∣ s₂ − s₂'`).  Projecting onto the coordinate whose
coefficient has the larger absolute value `M = max(|r₁|,|s₁|)` is injective on the fibre, so the
fibre is carried into a subset of `[−R,R]` all of whose members are pairwise congruent mod `M`,
which therefore has at most `2R/M + 1` elements (the elementary `card_le_div_of_pairwise_dvd_real`
below).  Summing the two signs gives `2·(2R/M + 1)`. -/

/-- `(a / b : ℕ)` cast to `ℝ` is at most `a / b`. -/
private lemma natCast_div_le_real (a b : ℕ) : (((a / b : ℕ)) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp
  · have hb : (0:ℝ) < (b : ℝ) := by exact_mod_cast h
    rw [le_div_iff₀ hb]
    have h1 : (a / b) * b ≤ a := Nat.div_mul_le_self a b
    calc (((a / b : ℕ)) : ℝ) * (b : ℝ) = (((a / b) * b : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (a : ℝ) := by exact_mod_cast h1

/-- A subset `U ⊆ [−R,R]` of the integers all of whose members are pairwise congruent modulo `a`
has at most `2R/a + 1` elements. -/
lemma card_le_div_of_pairwise_dvd_real (R : ℤ) (hR : 0 ≤ R) (a : ℕ) (ha : 0 < a)
    (U : Finset ℤ)
    (hsub : ∀ x ∈ U, x ∈ Finset.Icc (-R) R)
    (hcong : ∀ x ∈ U, ∀ y ∈ U, (a : ℤ) ∣ x - y) :
    (U.card : ℝ) ≤ 2 * (R : ℝ) / (a : ℝ) + 1 := by
  have haZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  rcases U.eq_empty_or_nonempty with hem | hne
  · rw [hem]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hR0 : (0:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have ha0 : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
    have : (0:ℝ) ≤ 2 * (R:ℝ) / (a:ℝ) := div_nonneg (by linarith) (le_of_lt ha0)
    linarith
  · set m : ℤ := U.min' hne with hmdef
    have hmU : m ∈ U := U.min'_mem hne
    have hle : ∀ x ∈ U, m ≤ x := fun x hx => U.min'_le x hx
    have h2R : (0:ℤ) ≤ 2 * R := by linarith
    set f : ℤ → ℕ := fun x => ((x - m) / (a : ℤ)).toNat with hf
    have hconv : ((2 * R : ℤ) / (a : ℤ)).toNat = (2 * R).toNat / a := by
      have h : (2 * R : ℤ) = ((2 * R).toNat : ℤ) := (Int.toNat_of_nonneg h2R).symm
      conv_lhs => rw [h]
      rw [Int.ofNat_ediv_ofNat, Int.toNat_natCast]
    have hxm : ∀ x ∈ U, x - m ≤ 2 * R := by
      intro x hx
      have hxI : -R ≤ x ∧ x ≤ R := Finset.mem_Icc.mp (hsub x hx)
      have hmI : -R ≤ m ∧ m ≤ R := Finset.mem_Icc.mp (hsub m hmU)
      linarith
    have hxm0 : ∀ x ∈ U, (0 : ℤ) ≤ x - m := by
      intro x hx; linarith [hle x hx]
    have hbd : ∀ x ∈ U, f x < (2 * R).toNat / a + 1 := by
      intro x hx
      have h1 : f x ≤ ((2 * R : ℤ) / (a : ℤ)).toNat := by
        simp only [hf]
        exact Int.toNat_le_toNat (Int.ediv_le_ediv haZ (hxm x hx))
      rw [hconv] at h1
      omega
    have hinj : Set.InjOn f (↑U : Set ℤ) := by
      intro x hx y hy hxy
      simp only [hf] at hxy
      have hx0 : (0 : ℤ) ≤ (x - m) / (a : ℤ) := Int.ediv_nonneg (hxm0 x hx) (le_of_lt haZ)
      have hy0 : (0 : ℤ) ≤ (y - m) / (a : ℤ) := Int.ediv_nonneg (hxm0 y hy) (le_of_lt haZ)
      have h1 : (x - m) / (a : ℤ) = (y - m) / (a : ℤ) := by
        have e1 : (((x - m) / (a : ℤ)).toNat : ℤ) = (x - m) / (a : ℤ) := Int.toNat_of_nonneg hx0
        have e2 : (((y - m) / (a : ℤ)).toNat : ℤ) = (y - m) / (a : ℤ) := Int.toNat_of_nonneg hy0
        have e3 : (((x - m) / (a : ℤ)).toNat : ℤ) = (((y - m) / (a : ℤ)).toNat : ℤ) := by
          exact_mod_cast hxy
        rw [e1, e2] at e3
        exact e3
      have hdx : (a : ℤ) ∣ x - m := hcong x hx m hmU
      have hdy : (a : ℤ) ∣ y - m := hcong y hy m hmU
      have m1 : (a : ℤ) * ((x - m) / (a : ℤ)) = x - m := Int.mul_ediv_cancel' hdx
      have m2 : (a : ℤ) * ((y - m) / (a : ℤ)) = y - m := Int.mul_ediv_cancel' hdy
      rw [h1] at m1
      linarith
    have hmaps2 : Set.MapsTo f (↑U : Set ℤ)
        (↑(Finset.range ((2 * R).toNat / a + 1)) : Set ℕ) := by
      intro x hx
      simpa [Finset.mem_range] using hbd x hx
    have hcard := Finset.card_le_card_of_injOn f hmaps2 hinj
    have hcard' : U.card ≤ (2 * R).toNat / a + 1 := by simpa using hcard
    have h2Rnat : ((2 * R).toNat : ℝ) = 2 * (R : ℝ) := by
      have h : ((2 * R).toNat : ℤ) = 2 * R := Int.toNat_of_nonneg h2R
      calc ((2 * R).toNat : ℝ) = (((2 * R).toNat : ℤ) : ℝ) := by push_cast; ring
        _ = ((2 * R : ℤ) : ℝ) := by rw [h]
        _ = 2 * (R : ℝ) := by push_cast; ring
    calc (U.card : ℝ) ≤ ((((2 * R).toNat / a + 1 : ℕ)) : ℝ) := by exact_mod_cast hcard'
      _ = ((((2 * R).toNat / a : ℕ)) : ℝ) + 1 := by push_cast; ring
      _ ≤ (2 * (R : ℝ)) / (a : ℝ) + 1 := by
          have h1 : ((((2 * R).toNat / a : ℕ)) : ℝ) ≤ ((2 * R).toNat : ℝ) / (a : ℝ) :=
            natCast_div_le_real _ _
          rw [h2Rnat] at h1
          linarith

/-- **The fibre count `Δ(z₁,z₂) = c`.**  For a fixed Gaussian integer `z₁ = r₁ + i s₁` with
`gcd(r₁,s₁) = 1`, the number of `z₂` in the box `|re|, |im| ≤ R` solving the linear equation
`Δ(z₁,z₂) = c` is at most `2R/M + 1`, where `M = max(|r₁|,|s₁|)`. -/
lemma card_gBox_Delta_eq_le (R : ℤ) (hR : 0 ≤ R) (z1 : GaussianInt) (c : ℤ)
    (hz1 : z1 ≠ 0) (hcop : IsCoprime z1.re z1.im) :
    (((Work.FIPlan.gBox R).filter (fun z2 => Work.FIPlan.Delta z1 z2 = c)).card : ℝ)
      ≤ 2 * (R : ℝ) / (max z1.re.natAbs z1.im.natAbs : ℝ) + 1 := by
  set S : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z2 => Work.FIPlan.Delta z1 z2 = c) with hS
  have hM1 : 1 ≤ max z1.re.natAbs z1.im.natAbs := by
    rcases Nat.eq_zero_or_pos (max z1.re.natAbs z1.im.natAbs) with h | h
    · exfalso
      have h1 : z1.re.natAbs = 0 := by
        have := le_max_left z1.re.natAbs z1.im.natAbs; omega
      have h2 : z1.im.natAbs = 0 := by
        have := le_max_right z1.re.natAbs z1.im.natAbs; omega
      exact hz1 (Zsqrtd.ext (Int.natAbs_eq_zero.mp h1) (Int.natAbs_eq_zero.mp h2))
    · exact h
  rcases le_total z1.im.natAbs z1.re.natAbs with hle | hle
  · -- Case A: `M = |r₁|`, project onto `Re`.
    have hM : max z1.re.natAbs z1.im.natAbs = z1.re.natAbs := max_eq_left hle
    have hr1 : z1.re ≠ 0 := Int.natAbs_pos.mp (by rw [← hM]; exact hM1)
    have hinj : Set.InjOn (fun z : GaussianInt => z.re) (↑S : Set GaussianInt) := by
      intro x hx y hy hxy
      change x.re = y.re at hxy
      simp only [Finset.mem_coe, hS, Finset.mem_filter] at hx hy
      have h1 : z1.re * x.im - z1.im * x.re = c := by rw [← Delta_eq z1 x]; exact hx.2
      have h2 : z1.re * y.im - z1.im * y.re = c := by rw [← Delta_eq z1 y]; exact hy.2
      have heq : z1.re * x.im = z1.re * y.im := by
        have hh : z1.re * x.im - z1.im * x.re = z1.re * y.im - z1.im * y.re := h1.trans h2.symm
        rw [hxy] at hh
        linarith
      exact Zsqrtd.ext hxy (mul_left_cancel₀ hr1 heq)
    have hcardU : ((S.image (fun z : GaussianInt => z.re)).card : ℝ) = (S.card : ℝ) := by
      rw [Finset.card_image_of_injOn hinj]
    have hsubU : ∀ x ∈ S.image (fun z : GaussianInt => z.re), x ∈ Finset.Icc (-R) R := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨z, hzS, rfl⟩ := hx
      have hzg : z ∈ Work.FIPlan.gBox R := (Finset.mem_filter.mp hzS).1
      have h := cf_mem_gBox_iff.mp hzg
      exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
    have hcongU : ∀ x ∈ S.image (fun z : GaussianInt => z.re),
        ∀ y ∈ S.image (fun z : GaussianInt => z.re), (z1.re.natAbs : ℤ) ∣ x - y := by
      intro x hx y hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨z2, hz2S, rfl⟩ := hx
      obtain ⟨z2', hz2'S, rfl⟩ := hy
      have h1 : z1.re * z2.im - z1.im * z2.re = c := by
        rw [← Delta_eq z1 z2]; exact (Finset.mem_filter.mp hz2S).2
      have h2 : z1.re * z2'.im - z1.im * z2'.re = c := by
        rw [← Delta_eq z1 z2']; exact (Finset.mem_filter.mp hz2'S).2
      have hdiff : z1.re * (z2.im - z2'.im) = z1.im * (z2.re - z2'.re) := by linarith
      have hdvd : z1.re ∣ z2.re - z2'.re := by
        have hzz : z1.re ∣ z1.im * (z2.re - z2'.re) := by
          rw [← hdiff]; exact dvd_mul_right _ _
        exact IsCoprime.dvd_of_dvd_mul_left hcop hzz
      exact Int.natAbs_dvd.mpr hdvd
    have hbound := card_le_div_of_pairwise_dvd_real R hR z1.re.natAbs
      (Int.natAbs_pos.mpr hr1) (S.image (fun z : GaussianInt => z.re)) hsubU hcongU
    rw [show max (z1.re.natAbs : ℝ) (z1.im.natAbs : ℝ) = (z1.re.natAbs : ℝ) by
      rw [← Nat.cast_max, hM]]
    rw [← hcardU]
    exact hbound
  · -- Case B: `M = |s₁|`, project onto `Im`.
    have hM : max z1.re.natAbs z1.im.natAbs = z1.im.natAbs := max_eq_right hle
    have hi1 : z1.im ≠ 0 := Int.natAbs_pos.mp (by rw [← hM]; exact hM1)
    have hinj : Set.InjOn (fun z : GaussianInt => z.im) (↑S : Set GaussianInt) := by
      intro x hx y hy hxy
      change x.im = y.im at hxy
      simp only [Finset.mem_coe, hS, Finset.mem_filter] at hx hy
      have h1 : z1.re * x.im - z1.im * x.re = c := by rw [← Delta_eq z1 x]; exact hx.2
      have h2 : z1.re * y.im - z1.im * y.re = c := by rw [← Delta_eq z1 y]; exact hy.2
      have heq : z1.im * x.re = z1.im * y.re := by
        have hh : z1.re * x.im - z1.im * x.re = z1.re * y.im - z1.im * y.re := h1.trans h2.symm
        rw [hxy] at hh
        linarith
      exact Zsqrtd.ext (mul_left_cancel₀ hi1 heq) hxy
    have hcardU : ((S.image (fun z : GaussianInt => z.im)).card : ℝ) = (S.card : ℝ) := by
      rw [Finset.card_image_of_injOn hinj]
    have hsubU : ∀ x ∈ S.image (fun z : GaussianInt => z.im), x ∈ Finset.Icc (-R) R := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨z, hzS, rfl⟩ := hx
      have hzg : z ∈ Work.FIPlan.gBox R := (Finset.mem_filter.mp hzS).1
      have h := cf_mem_gBox_iff.mp hzg
      exact Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2⟩
    have hcongU : ∀ x ∈ S.image (fun z : GaussianInt => z.im),
        ∀ y ∈ S.image (fun z : GaussianInt => z.im), (z1.im.natAbs : ℤ) ∣ x - y := by
      intro x hx y hy
      rw [Finset.mem_image] at hx hy
      obtain ⟨z2, hz2S, rfl⟩ := hx
      obtain ⟨z2', hz2'S, rfl⟩ := hy
      have h1 : z1.re * z2.im - z1.im * z2.re = c := by
        rw [← Delta_eq z1 z2]; exact (Finset.mem_filter.mp hz2S).2
      have h2 : z1.re * z2'.im - z1.im * z2'.re = c := by
        rw [← Delta_eq z1 z2']; exact (Finset.mem_filter.mp hz2'S).2
      have hdiff : z1.im * (z2.re - z2'.re) = z1.re * (z2.im - z2'.im) := by linarith
      have hdvd : z1.im ∣ z2.im - z2'.im := by
        have hzz : z1.im ∣ z1.re * (z2.im - z2'.im) := by
          rw [← hdiff]; exact dvd_mul_right _ _
        exact IsCoprime.dvd_of_dvd_mul_left hcop.symm hzz
      exact Int.natAbs_dvd.mpr hdvd
    have hbound := card_le_div_of_pairwise_dvd_real R hR z1.im.natAbs
      (Int.natAbs_pos.mpr hi1) (S.image (fun z : GaussianInt => z.im)) hsubU hcongU
    rw [show max (z1.re.natAbs : ℝ) (z1.im.natAbs : ℝ) = (z1.im.natAbs : ℝ) by
      rw [← Nat.cast_max, hM]]
    rw [← hcardU]
    exact hbound

/-- **The fibre count of `|Δ| = d`.**  For `z₁ ≠ 0` with coprime coordinates, the number of `z₂`
in the box `|re|, |im| ≤ R` with `|Δ(z₁,z₂)| = d` is at most `2·(2R/M + 1)` with
`M = max(|Re z₁|, |Im z₁|)`; the two signs `Δ = ±d` each contribute at most `2R/M + 1`. -/
theorem card_gBox_absDelta_eq_le (R : ℤ) (hR : 0 ≤ R) (z1 : GaussianInt) (d : ℕ)
    (hz1 : z1 ≠ 0) (hcop : IsCoprime z1.re z1.im) :
    (((Work.FIPlan.gBox R).filter (fun z2 => Work.FIPlan.absDelta z1 z2 = d)).card : ℝ)
      ≤ 2 * (2 * (R : ℝ) / (max z1.re.natAbs z1.im.natAbs : ℝ) + 1) := by
  set S : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z2 => Work.FIPlan.absDelta z1 z2 = d) with hS
  set S1 : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z2 => Work.FIPlan.Delta z1 z2 = (d : ℤ)) with hS1
  set S2 : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z2 => Work.FIPlan.Delta z1 z2 = -(d : ℤ)) with hS2
  have hsub : S ⊆ S1 ∪ S2 := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    obtain ⟨hzg, hzΔ⟩ := hz
    have h : (Work.FIPlan.Delta z1 z).natAbs = d := by
      simpa only [Work.FIPlan.absDelta] using hzΔ
    rcases Int.natAbs_eq_iff.mp h with h' | h'
    · exact Finset.mem_union_left _ (by rw [hS1, Finset.mem_filter]; exact ⟨hzg, h'⟩)
    · exact Finset.mem_union_right _ (by rw [hS2, Finset.mem_filter]; exact ⟨hzg, h'⟩)
  have hcard : S.card ≤ S1.card + S2.card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_union_le S1 S2)
  have h1 := card_gBox_Delta_eq_le R hR z1 (d : ℤ) hz1 hcop
  have h2 := card_gBox_Delta_eq_le R hR z1 (-(d : ℤ)) hz1 hcop
  have h1' : (S1.card : ℝ) ≤ 2 * (R : ℝ) / (max z1.re.natAbs z1.im.natAbs : ℝ) + 1 := by
    rw [hS1]; exact h1
  have h2' : (S2.card : ℝ) ≤ 2 * (R : ℝ) / (max z1.re.natAbs z1.im.natAbs : ℝ) + 1 := by
    rw [hS2]; exact h2
  calc (S.card : ℝ) ≤ (S1.card : ℝ) + (S2.card : ℝ) := by exact_mod_cast hcard
    _ ≤ (2 * (R : ℝ) / (max z1.re.natAbs z1.im.natAbs : ℝ) + 1)
          + (2 * (R : ℝ) / (max z1.re.natAbs z1.im.natAbs : ℝ) + 1) := add_le_add h1' h2'
    _ = 2 * (2 * (R : ℝ) / (max z1.re.natAbs z1.im.natAbs : ℝ) + 1) := by ring

end

end Work.FIArea7
