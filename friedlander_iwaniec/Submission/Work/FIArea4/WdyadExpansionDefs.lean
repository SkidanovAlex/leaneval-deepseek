import Mathlib
import Submission.Work.FIArea4.WdyadSetup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Combinatorial vocabulary for the Poisson expansion of the dyadic dual variance

This module collects the number-theoretic input for
`Work.FIArea4.Wdyad_expansion`.  Everything here is about the indicator function

`cind d s c = [s ≡ c (mod d)]`  (as a complex number),

the canonical solution `a0 d r s h` of `r * a ≡ s (mod d)` (for `r` coprime to `d`), and the
elementary fact that summing such indicators over two moduli `d₁, d₂` is the same as summing
over the single modulus `[d₁, d₂]` (which is what makes the Poisson step of the expansion
produce the least common multiple).
-/

namespace Work.FIArea4

open Finset

noncomputable section

/-- The indicator (as a complex number) of the congruence `s ≡ c (mod d)`. -/
def cind (d : ℕ) (s : ℤ) (c : ℕ) : ℂ := if (s : ZMod d) = (c : ZMod d) then 1 else 0

/-- The canonical solution `a ∈ [0, d)` of `r * a ≡ s (mod d)`, for `r` coprime to `d`. -/
def a0 (d r : ℕ) (s : ℤ) (h : Nat.Coprime r d) : ℕ :=
  ZMod.val ((↑((ZMod.unitOfCoprime r h)⁻¹ : (ZMod d)ˣ) : ZMod d) * (s : ZMod d))

lemma a0_spec {d r : ℕ} [NeZero d] (s : ℤ) (h : Nat.Coprime r d) :
    (a0 d r s h : ZMod d) = (↑((ZMod.unitOfCoprime r h)⁻¹ : (ZMod d)ˣ) : ZMod d) * (s : ZMod d) := by
  unfold a0; rw [ZMod.natCast_zmod_val]

lemma a0_mul {d r : ℕ} [NeZero d] (s : ℤ) (h : Nat.Coprime r d) :
    (r : ZMod d) * (a0 d r s h : ZMod d) = (s : ZMod d) := by
  have key : (↑(ZMod.unitOfCoprime r h) : ZMod d) *
      (↑((ZMod.unitOfCoprime r h)⁻¹ : (ZMod d)ˣ) : ZMod d) = 1 := by
    rw [← Units.val_mul]; exact Units.mul_inv _
  unfold a0
  rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime r h, ← mul_assoc, key, one_mul]

lemma a0_lt {d r : ℕ} [NeZero d] (s : ℤ) (h : Nat.Coprime r d) : a0 d r s h < d := by
  unfold a0; exact ZMod.val_lt _

lemma a0_unique {d r : ℕ} [NeZero d] (s : ℤ) (h : Nat.Coprime r d)
    {a a' : ℕ} (ha : a < d) (ha' : a' < d)
    (hsa : (s : ZMod d) = (r : ZMod d) * (a : ZMod d))
    (hsa' : (s : ZMod d) = (r : ZMod d) * (a' : ZMod d)) : a = a' := by
  have h1 : ((r * a : ℕ) : ZMod d) = ((r * a' : ℕ) : ZMod d) := by
    rw [Nat.cast_mul, Nat.cast_mul, hsa.symm, hsa']
  have h2 : (r * a) % d = (r * a') % d := (ZMod.natCast_eq_natCast_iff' _ _ d).mp h1
  have h3 : r * a ≡ r * a' [MOD d] := h2
  have h4 : a ≡ a' [MOD d] := Nat.ModEq.cancel_left_of_coprime (m := d) (c := r) h.symm h3
  rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h4

lemma cind_eq_ite {d r : ℕ} [NeZero d] (s : ℤ) (h : Nat.Coprime r d) {a : ℕ} (ha : a < d) :
    cind d s (r*a) = if a = a0 d r s h then 1 else 0 := by
  unfold cind
  rw [Nat.cast_mul]
  by_cases hae : a = a0 d r s h
  · rw [if_pos (by rw [hae]; exact (a0_mul s h).symm), if_pos hae]
  · rw [if_neg, if_neg hae]
    intro hsa
    exact hae (a0_unique s h ha (a0_lt s h) hsa (a0_mul s h).symm)

lemma sum_cind_right {d r : ℕ} [NeZero d] (s : ℤ) (h : Nat.Coprime r d) (f : ℕ → ℂ) :
    ∑ a ∈ Finset.range d, f a * cind d s (r*a) = f (a0 d r s h) := by
  have h1 : ∀ b ∈ Finset.range d, b ≠ a0 d r s h → f b * cind d s (r*b) = 0 := by
    intro b hb hne
    rw [cind_eq_ite s h (Finset.mem_range.mp hb), if_neg hne, mul_zero]
  have h2 : a0 d r s h ∉ Finset.range d → f (a0 d r s h) * cind d s (r*(a0 d r s h)) = 0 :=
    fun hnot => absurd (Finset.mem_range.mpr (a0_lt s h)) hnot
  rw [Finset.sum_eq_single (a0 d r s h) h1 h2]
  rw [cind_eq_ite s h (a0_lt s h), if_pos rfl, mul_one]

lemma sum_cind_left {d r : ℕ} [NeZero d] (s : ℤ) (h : Nat.Coprime r d) (f : ℕ → ℂ) :
    ∑ a ∈ Finset.range d, cind d s (r*a) * f a = f (a0 d r s h) := by
  rw [show (∑ a ∈ Finset.range d, cind d s (r*a) * f a)
      = ∑ a ∈ Finset.range d, f a * cind d s (r*a) from
    Finset.sum_congr rfl (fun a _ => mul_comm _ _)]
  exact sum_cind_right s h f

/-- The canonical solutions of `r a ≡ s` modulo `L` and modulo a divisor `d ∣ L` are related by
reduction modulo `d`. -/
lemma a0_lcm_mod {L d r : ℕ} [NeZero d] [NeZero L] (hdvd : d ∣ L)
    (hL : Nat.Coprime r L) (hd : Nat.Coprime r d) (s : ℤ) :
    a0 L r s hL % d = a0 d r s hd := by
  have hmul := a0_mul (d := L) (r := r) s hL
  have hcast : (r : ZMod d) * (↑(a0 L r s hL) : ZMod d) = (s : ZMod d) := by
    have h' := congrArg (ZMod.castHom hdvd (ZMod d)) hmul
    simp only [map_mul, ZMod.castHom_apply] at h'
    simpa only [ZMod.cast_natCast hdvd r, ZMod.cast_natCast hdvd (a0 L r s hL),
      ZMod.cast_intCast hdvd s] using h'
  refine a0_unique s hd (Nat.mod_lt _ (NeZero.pos d)) (a0_lt s hd) ?_ (a0_mul s hd).symm
  rw [hcast.symm]
  congr 1
  exact (ZMod.natCast_eq_natCast_iff' _ _ d).mpr (Nat.mod_mod _ _).symm

/-- Summing the indicator over the pair of moduli `d₁, d₂` is the same as summing over the single
modulus `[d₁, d₂]` reindexed by the Chinese remainder theorem. -/
lemma cind_double {d1 d2 r : ℕ} [NeZero d1] [NeZero d2] [NeZero (Nat.lcm d1 d2)]
    (hc : Nat.Coprime r (d1*d2)) (g : ℕ → ℕ → ℂ) (s : ℤ) :
    (∑ a1 ∈ Finset.range d1, ∑ a2 ∈ Finset.range d2,
        g a1 a2 * cind d1 s (r*a1) * cind d2 s (r*a2))
      = ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          g (a % d1) (a % d2) * cind (Nat.lcm d1 d2) s (r*a) := by
  have h1 : Nat.Coprime r d1 := hc.coprime_dvd_right (dvd_mul_right d1 d2)
  have h2 : Nat.Coprime r d2 := hc.coprime_dvd_right (dvd_mul_left d2 d1)
  have hL : Nat.Coprime r (Nat.lcm d1 d2) :=
    hc.coprime_dvd_right (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
  have hA : (∑ a1 ∈ Finset.range d1, ∑ a2 ∈ Finset.range d2,
        g a1 a2 * cind d1 s (r*a1) * cind d2 s (r*a2))
      = g (a0 d1 r s h1) (a0 d2 r s h2) := by
    trans ∑ a1 ∈ Finset.range d1, g a1 (a0 d2 r s h2) * cind d1 s (r*a1)
    · exact Finset.sum_congr rfl (fun a1 _ =>
        sum_cind_right s h2 (fun a2 => g a1 a2 * cind d1 s (r*a1)))
    · exact sum_cind_right s h1 (fun a1 => g a1 (a0 d2 r s h2))
  rw [hA]
  rw [← a0_lcm_mod (L := Nat.lcm d1 d2) (d := d1) (Nat.dvd_lcm_left d1 d2) hL h1 s,
      ← a0_lcm_mod (L := Nat.lcm d1 d2) (d := d2) (Nat.dvd_lcm_right d1 d2) hL h2 s]
  exact (sum_cind_right s hL (fun a => g (a % d1) (a % d2))).symm

end

end Work.FIArea4
