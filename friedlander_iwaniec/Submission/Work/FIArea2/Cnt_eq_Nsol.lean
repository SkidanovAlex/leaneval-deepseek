import Mathlib
import Submission.Work.FIArea2.G0_defect
import Submission.Work.FIArea2.NsolDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Coordinate facts in `ℤ[i]` -/

lemma gnorm_cast_sq (z : GaussianInt) :
    (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, Nat.cast_add,
    Int.natAbs_mul_self, Int.natAbs_mul_self]
  ring

lemma star_mul_re (z1 z2 : GaussianInt) :
    (star z1 * z2).re = z1.re * z2.re + z1.im * z2.im := by
  simp [Zsqrtd.re_mul]

lemma star_mul_im (z1 z2 : GaussianInt) :
    (star z1 * z2).im = z1.re * z2.im - z1.im * z2.re := by
  simp [Zsqrtd.im_mul, sub_eq_add_neg]

lemma gnorm_mul_re (z1 z2 : GaussianInt) :
    (Work.FIPlan.gnorm z1 : ℤ) * z2.re
      = z1.re * (star z1 * z2).re - (star z1 * z2).im * z1.im := by
  rw [gnorm_cast_sq, star_mul_re, star_mul_im]; ring

lemma gnorm_mul_im (z1 z2 : GaussianInt) :
    (Work.FIPlan.gnorm z1 : ℤ) * z2.im
      = z1.im * (star z1 * z2).re + (star z1 * z2).im * z1.re := by
  rw [gnorm_cast_sq, star_mul_re, star_mul_im]; ring

/-- `(x² r₂ - y² r₁) % q = 0` is the same as the `ZMod q` equation `r₂ x² = r₁ y²`. -/
lemma emod_zero_iff_zmod (q : ℕ) [NeZero q] (x y : ℕ) (r1 r2 : ℤ) :
    (x ^ 2 * r2 - y ^ 2 * r1) % (q : ℤ) = 0 ↔
      (r2 : ZMod q) * (x : ZMod q) ^ 2 = (r1 : ZMod q) * (y : ZMod q) ^ 2 := by
  have hiff : (((x ^ 2 * r2 - y ^ 2 * r1 : ℤ)) : ZMod q) = 0 ↔
      (x ^ 2 * r2 - y ^ 2 * r1) % (q : ℤ) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨Int.emod_eq_zero_of_dvd, Int.dvd_of_emod_eq_zero⟩
  have hcast : (((x ^ 2 * r2 - y ^ 2 * r1 : ℤ)) : ZMod q)
      = (r2 : ZMod q) * (x : ZMod q) ^ 2 - (r1 : ZMod q) * (y : ZMod q) ^ 2 := by
    push_cast
    ring
  rw [← hiff, hcast, sub_eq_zero]

lemma star_mul_im_zmod_eq_zero {z1 z2 : GaussianInt}
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    ((star z1 * z2).im : ZMod (Work.FIPlan.absDelta z1 z2)) = 0 := by
  haveI : NeZero (Work.FIPlan.absDelta z1 z2) := ⟨hD⟩
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Int.natAbs_dvd_self

/-! ### Step 1: `Cnt` as a count of `ZMod` solutions -/

set_option maxRecDepth 100000 in
lemma Cnt_eq_zmod_card (z1 z2 : GaussianInt) [NeZero (Work.FIPlan.absDelta z1 z2)] :
    Cnt z1 z2 =
      ((Finset.univ : Finset (ZMod (Work.FIPlan.absDelta z1 z2) ×
          ZMod (Work.FIPlan.absDelta z1 z2))).filter
        (fun p => (z2.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
                    = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 ∧
                  (z2.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
                    = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2)).card := by
  unfold Cnt
  refine Finset.card_bij
    (fun (p : ℕ × ℕ) _ => ((p.1 : ZMod (Work.FIPlan.absDelta z1 z2)),
                           (p.2 : ZMod (Work.FIPlan.absDelta z1 z2)))) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨hp1, hp2⟩, hc1, hc2⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(emod_zero_iff_zmod _ p.1 p.2 z1.re z2.re).mp hc1,
           (emod_zero_iff_zmod _ p.1 p.2 z1.im z2.im).mp hc2⟩
  · intro p hp r hr heq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp hr
    obtain ⟨⟨hp1, hp2⟩, _⟩ := hp
    obtain ⟨⟨hr1, hr2⟩, _⟩ := hr
    rw [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    refine Prod.ext ?_ ?_
    · have := congrArg ZMod.val h1
      rwa [ZMod.val_natCast_of_lt hp1, ZMod.val_natCast_of_lt hr1] at this
    · have := congrArg ZMod.val h2
      rwa [ZMod.val_natCast_of_lt hp2, ZMod.val_natCast_of_lt hr2] at this
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    obtain ⟨hc1, hc2⟩ := hb
    refine ⟨(b.1.val, b.2.val), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨b.1.val_lt, b.2.val_lt⟩, ?_, ?_⟩
      · rw [emod_zero_iff_zmod]
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        exact hc1
      · rw [emod_zero_iff_zmod]
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        exact hc2
    · simp

/-! ### Step 2: the two-congruence system and the single congruence have the same solutions -/

lemma two_iff_one {z1 z2 : GaussianInt} {a : ℕ}
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)])
    (p : ZMod (Work.FIPlan.absDelta z1 z2) × ZMod (Work.FIPlan.absDelta z1 z2)) :
    ((z2.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
        = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 ∧
      (z2.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
        = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) ↔
    (a : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2 = p.2 ^ 2 := by
  haveI : NeZero (Work.FIPlan.absDelta z1 z2) := ⟨hD⟩
  have hu : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))
      = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) ^ 2 + (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) ^ 2 := by
    rw [show (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))
        = ((Work.FIPlan.gnorm z1 : ℤ) : ZMod (Work.FIPlan.absDelta z1 z2))
        from (Int.cast_natCast _).symm]
    rw [gnorm_cast_sq z1]
    push_cast
    ring
  have hR : ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2))
      = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.re : ZMod (Work.FIPlan.absDelta z1 z2)) + (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.im : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    have h := congrArg (fun t : ℤ => (t : ZMod (Work.FIPlan.absDelta z1 z2)))
      (star_mul_re z1 z2)
    push_cast at h
    exact h
  have hDz : ((star z1 * z2).im : ZMod (Work.FIPlan.absDelta z1 z2)) = 0 :=
    star_mul_im_zmod_eq_zero hD
  have hid1 : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.re : ZMod (Work.FIPlan.absDelta z1 z2))
      = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    have h := congrArg (fun t : ℤ => (t : ZMod (Work.FIPlan.absDelta z1 z2)))
      (gnorm_mul_re z1 z2)
    push_cast at h
    rw [hDz, zero_mul, sub_zero] at h
    exact h
  have hid2 : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.im : ZMod (Work.FIPlan.absDelta z1 z2))
      = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    have h := congrArg (fun t : ℤ => (t : ZMod (Work.FIPlan.absDelta z1 z2)))
      (gnorm_mul_im z1 z2)
    push_cast at h
    rw [hDz, zero_mul, add_zero] at h
    exact h
  have huu : IsUnit ((Work.FIPlan.gnorm z1 : ℕ) : ZMod (Work.FIPlan.absDelta z1 z2)) :=
    (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2)).mpr hni
  have haZ : (a : ZMod (Work.FIPlan.absDelta z1 z2)) * (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))
      = ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    have h := (ZMod.intCast_eq_intCast_iff ((a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ))
        ((star z1 * z2).re) (Work.FIPlan.absDelta z1 z2)).mpr ha
    push_cast at h
    exact h
  constructor
  · rintro ⟨h1, h2⟩
    have hRc : ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
        = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 := by
      rw [hR, hu]
      linear_combination (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * h1 + (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * h2
    have h0 : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((a : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2 - p.2 ^ 2) = 0 := by
      have hua : (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (a : ZMod (Work.FIPlan.absDelta z1 z2)) = ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) := by
        rw [mul_comm, haZ]
      rw [mul_sub, ← mul_assoc, hua, hRc, sub_self]
    have := (IsUnit.mul_right_eq_zero huu).mp h0
    rwa [sub_eq_zero] at this
  · intro h1
    have hRc : ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
        = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 := by
      calc ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2
          = ((a : ZMod (Work.FIPlan.absDelta z1 z2)) * (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by rw [haZ]
        _ = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((a : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2) := by ring
        _ = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2 := by rw [h1]
    refine ⟨?_, ?_⟩
    · apply IsUnit.mul_left_cancel huu
      calc (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((z2.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2)
          = ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.re : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by ring
        _ = ((z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by rw [hid1]
        _ = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * (((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2) := by ring
        _ = (z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) := by rw [hRc]
        _ = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((z1.re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) := by ring
    · apply IsUnit.mul_left_cancel huu
      calc (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((z2.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2)
          = ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * (z2.im : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by ring
        _ = ((z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * ((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2))) * p.1 ^ 2 := by rw [hid2]
        _ = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * (((star z1 * z2).re : ZMod (Work.FIPlan.absDelta z1 z2)) * p.1 ^ 2) := by ring
        _ = (z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * ((Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) := by rw [hRc]
        _ = (Work.FIPlan.gnorm z1 : ZMod (Work.FIPlan.absDelta z1 z2)) * ((z1.im : ZMod (Work.FIPlan.absDelta z1 z2)) * p.2 ^ 2) := by ring

/-- **(*FI* (6.4)–(6.6) = (8.8))**: the count of (6.12) — pairs of rational residues `(γ₁,γ₂)` mod `|Δ|` satisfying the two congruences (6.5) `γ₁²r₁ ≡ γ₂²r₂`, `γ₁²s₁ ≡ γ₂²s₂ (mod |Δ|)` — equals the number of solutions of the *single* congruence `a γ₁² ≡ γ₂² (mod |Δ|)` of (8.8), where `a ≡ z₂/z₁ ≡ Re(z̄₁z₂)·|z₁|^{-2} (mod |Δ|)` (the residue of (6.6)).

Proof sketch: in `Z[i]/(|Δ|)`, `γ₁²z₂ ≡ γ₂²z₁ ⟺ γ₁²z̄₁z₂ ≡ γ₂²|z₁|²` (multiply by `z̄₁`), and `z̄₁z₂ = Re(z̄₁z₂) + iΔ` with `iΔ ≡ 0 (mod |Δ|)`, so the two-congruence count is the count of `Re(z̄₁z₂)γ₁² ≡ |z₁|²γ₂²`; multiplying by the inverse of `|z₁|²` (which exists by the coprimality hypothesis `(|z₁|², |Δ|) = 1`) gives `a γ₁² ≡ γ₂²`. -/
theorem Cnt_eq_Nsol {z1 z2 : GaussianInt} {a : ℕ}
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (hni : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2))
    (ha : (a : ℤ) * (Work.FIPlan.gnorm z1 : ℤ)
        ≡ (star z1 * z2).re [ZMOD (Work.FIPlan.absDelta z1 z2 : ℤ)]) :
    Cnt z1 z2 = Nsol (Work.FIPlan.absDelta z1 z2) a := by
  haveI : NeZero (Work.FIPlan.absDelta z1 z2) := ⟨hD⟩
  rw [Nsol_eq_filter (Work.FIPlan.absDelta z1 z2) a, Cnt_eq_zmod_card z1 z2]
  apply congrArg Finset.card
  exact Finset.filter_congr (fun p _ => two_iff_one hD hni ha p)

end

end Work.FIArea2
