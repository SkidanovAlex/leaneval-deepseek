import Mathlib
import Submission.Work.FIArea4.WdyadGenDefs
import Submission.Work.FIArea4.Vflip.Wdyad_symm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Finset
open scoped BigOperators

namespace Work.FIArea4.WdyadGen

/-!
# The `e`-th stratum identity for the `W`-side class sum `TZbox`

This file proves `TZbox_stratum`, the identity underlying the stratification of the dyadic dual
variance `Wdyad` according to `gcd(a,d)`: for `e ≥ 1`,

`TZbox D (2D) (gLift γ e) r s
   = [e ∣ s] · [(r,e)=1] · (r | oddPart e) · TZbox (D/e) (2D/e) (gamE γ e) r (s/e)`.

The proof proceeds by writing the `a`-sum over `range d` with `gcd a d = e` as a sum over
`a' < d/e` with `(a', d/e) = 1` (the change of variable `a = e·a'`), using the entry relation
`Mentry (e d') (e a') r s = [e ∣ s][(r,e)=1](r|oddPart e) · Mentry d' a' r (s/e)`, and then
reindexing the `d`-sum over the multiples of `e` by `d ↦ d/e`.
-/

/-- Reindexing the `a`-sum: summing `G a` over `a < e·d'` with `gcd a (e·d') = e` is the same
as summing `G (e·a')` over `a' < d'` with `(a',d') = 1`. -/
lemma sum_stratum {M : Type*} [AddCommMonoid M] {e d' : ℕ} (he : 1 ≤ e) (G : ℕ → M) :
    (∑ a ∈ Finset.range (e*d'), (if Nat.gcd a (e*d') = e then G a else 0))
      = ∑ a' ∈ Finset.range d', (if Nat.Coprime a' d' then G (e*a') else 0) := by
  simp only [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => a / e) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    obtain ⟨ha1, ha2⟩ := ha
    have hea : e ∣ a := ha2 ▸ Nat.gcd_dvd_left a (e*d')
    refine ⟨?_, ?_⟩
    · have hlt : e * (a/e) < e * d' := by rw [Nat.mul_div_cancel' hea]; exact ha1
      exact (Nat.mul_lt_mul_left (by omega : 0 < e)).mp hlt
    · rw [Nat.coprime_iff_gcd_eq_one]
      have hg : e * (a/e).gcd d' = e := by rw [← Nat.gcd_mul_left, Nat.mul_div_cancel' hea, ha2]
      exact Nat.mul_left_cancel (by omega : 0 < e) (by rw [hg, mul_one])
  · intro a1 ha1 a2 ha2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at ha1 ha2
    have h1 : e ∣ a1 := ha1.2 ▸ Nat.gcd_dvd_left a1 (e*d')
    have h2 : e ∣ a2 := ha2.2 ▸ Nat.gcd_dvd_left a2 (e*d')
    rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, heq]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨e*b, ⟨?_, ?_⟩, ?_⟩
    · exact (Nat.mul_lt_mul_left (by omega : 0 < e)).mpr hb1
    · rw [Nat.gcd_mul_left, Nat.coprime_iff_gcd_eq_one.mp hb2, mul_one]
    · exact Nat.mul_div_cancel_left b (by omega)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    have h1 : e ∣ a := ha.2 ▸ Nat.gcd_dvd_left a (e*d')
    rw [Nat.mul_div_cancel' h1]

/-- The `Mentry` entry at the stratum `gcd(a,d) = e` factors as the `e`-part of the Jacobi
symbol times the entry of the reduced pair `(a', d')`, `a = e a'`, `d = e d'`, `s = e (s/e)`. -/
lemma Mentry_stratum {e : ℕ} (he : 1 ≤ e) {d' : ℕ} (hd' : 1 ≤ d') (r s a' : ℕ) :
    Work.FIArea4.Mentry (e*d') (e*a') r s =
      (if e ∣ s then (if Nat.Coprime r e then (jacobiSym (r : ℤ) (Work.FIPlan.oddPart e) : ℂ) else 0) else 0)
        * Work.FIArea4.Mentry d' a' r (s/e) := by
  have hkey : Nat.Coprime r (e*d') ∧ ((s : ZMod (e*d')) = (r : ZMod (e*d')) * ((e*a' : ℕ) : ZMod (e*d')))
      ↔ (e ∣ s ∧ Nat.Coprime r e ∧ (Nat.Coprime r d' ∧ ((s/e : ZMod d') = (r : ZMod d') * (a' : ZMod d')))) := by
    have hcop : Nat.Coprime r (e*d') ↔ Nat.Coprime r e ∧ Nat.Coprime r d' := Nat.coprime_mul_iff_right
    have hcong : ((s : ZMod (e*d')) = (r : ZMod (e*d')) * ((e*a' : ℕ) : ZMod (e*d'))) ↔
        e ∣ s ∧ ((s/e : ZMod d') = (r : ZMod d') * (a' : ZMod d')) := by
      have hmodeq : Nat.ModEq (e*d') s (r*(e*a')) ↔ e ∣ s ∧ Nat.ModEq d' (s/e) (r*a') := by
        constructor
        · intro h
          have hdvd : e ∣ s := (h.dvd_iff (dvd_mul_right e d')).mpr ⟨a'*r, by ring⟩
          refine ⟨hdvd, ?_⟩
          have h' : e*(s/e) ≡ e*(r*a') [MOD e*d'] := by
            rw [Nat.mul_div_cancel' hdvd]
            simpa [mul_assoc, mul_comm, mul_left_comm] using h
          exact (Nat.ModEq.mul_left_cancel_iff' (by omega)).mp h'
        · rintro ⟨hdvd, h2⟩
          have h' : e*(s/e) ≡ e*(r*a') [MOD e*d'] := Nat.ModEq.mul_left' e h2
          rw [Nat.mul_div_cancel' hdvd] at h'
          simpa [mul_assoc, mul_comm, mul_left_comm] using h'
      simp only [← Nat.cast_mul]
      rw [ZMod.natCast_eq_natCast_iff, ZMod.natCast_eq_natCast_iff]
      exact hmodeq
    rw [hcop, hcong]; tauto
  have hodd : (jacobiSym (r:ℤ) (Work.FIPlan.oddPart (e*d')) : ℂ) =
      (jacobiSym (r:ℤ) (Work.FIPlan.oddPart e) : ℂ) * (jacobiSym (r:ℤ) (Work.FIPlan.oddPart d') : ℂ) := by
    have h1 : Work.FIPlan.oddPart (e*d') = Work.FIPlan.oddPart e * Work.FIPlan.oddPart d' := by
      unfold Work.FIPlan.oddPart; exact Nat.ordCompl_mul e d' 2
    have h2 : Work.FIPlan.oddPart e ≠ 0 := by unfold Work.FIPlan.oddPart; exact (Nat.ordCompl_pos 2 (by omega)).ne'
    have h3 : Work.FIPlan.oddPart d' ≠ 0 := by unfold Work.FIPlan.oddPart; exact (Nat.ordCompl_pos 2 (by omega)).ne'
    rw [h1, jacobiSym.mul_right' r h2 h3, Int.cast_mul]
  unfold Work.FIArea4.Mentry
  by_cases hcond : (Nat.Coprime r (e*d') ∧ ((s : ZMod (e*d')) = (r : ZMod (e*d')) * ((e*a' : ℕ) : ZMod (e*d'))))
  · rw [if_pos hcond, hodd]
    obtain ⟨hs, hre, hrd, hc'⟩ := hkey.mp hcond
    rw [if_pos hs, if_pos hre, if_pos (show Nat.Coprime r d' ∧ ((s/e : ZMod d') = (r : ZMod d') * (a' : ZMod d')) from ⟨hrd, hc'⟩)]
  · rw [if_neg hcond]
    by_cases hs : e ∣ s
    · by_cases hre : Nat.Coprime r e
      · have hne : ¬ (Nat.Coprime r d' ∧ ((s/e : ZMod d') = (r : ZMod d') * (a' : ZMod d'))) := by
          intro h; exact hcond (hkey.mpr ⟨hs, hre, h⟩)
        rw [if_pos hs, if_pos hre, if_neg hne, mul_zero]
      · rw [if_pos hs, if_neg hre, zero_mul]
    · rw [if_neg hs, zero_mul]

/-- The inner (`a`-)sum of `TZbox D (2D) (gLift γ e) r s` at a fixed modulus `d`: it vanishes
unless `e ∣ d`, and in that case it equals the prefactor times the inner sum of
`TZbox (D/e) (2D/e) (gamE γ e) r (s/e)` at the reduced modulus `d/e`. -/
lemma inner_stratum {e : ℕ} (he : 1 ≤ e) (γ : ℕ → ℕ → ℂ) (r s d : ℕ) :
    (∑ a ∈ Finset.range d, (if Nat.gcd a d = e then γ a d else 0) * Work.FIArea4.Mentry d a r s)
      = if e ∣ d then
          (if e ∣ s then (if Nat.Coprime r e then (jacobiSym (r:ℤ) (Work.FIPlan.oddPart e) : ℂ) else 0) else 0)
            * (∑ a' ∈ Finset.range (d/e), (if Nat.Coprime a' (d/e) then γ (e*a') (e*(d/e)) else 0) * Work.FIArea4.Mentry (d/e) a' r (s/e))
        else 0 := by
  by_cases hd : e ∣ d
  · rw [if_pos hd]
    obtain ⟨d1, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left d1 (by omega : 0 < e)]
    have h1 : (∑ a ∈ Finset.range (e*d1), (if Nat.gcd a (e*d1) = e then γ a (e*d1) else 0) * Work.FIArea4.Mentry (e*d1) a r s)
        = ∑ a ∈ Finset.range (e*d1), (if Nat.gcd a (e*d1) = e then γ a (e*d1) * Work.FIArea4.Mentry (e*d1) a r s else 0) := by
      apply Finset.sum_congr rfl; intro a ha; rw [ite_mul, zero_mul]
    rw [h1, sum_stratum he (fun a => γ a (e*d1) * Work.FIArea4.Mentry (e*d1) a r s)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a' ha'
    have hd1 : 1 ≤ d1 := by have := Finset.mem_range.mp ha'; omega
    by_cases hc : Nat.Coprime a' d1
    · rw [if_pos hc, if_pos hc, Mentry_stratum he hd1 r s a']
      ring
    · rw [if_neg hc, if_neg hc, zero_mul, mul_zero]
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : Nat.gcd a d ≠ e := by intro h; exact hd (h ▸ Nat.gcd_dvd_right a d)
    rw [if_neg hne, zero_mul]

/-- Reindexing the modulus sum: the moduli `d ∈ (D, 2D]` divisible by `e` correspond
bijectively to `d' ∈ (D/e, 2D/e]` via `d = e·d'`. -/
lemma sum_Ioc_div {M : Type*} [AddCommMonoid M] {e D : ℕ} (he : 1 ≤ e) (G : ℕ → M) :
    (∑ d ∈ (Finset.Ioc D (2*D)).filter (fun d => e ∣ d), G (d/e))
      = ∑ d' ∈ Finset.Ioc (D/e) (2*D/e), G d' := by
  refine Finset.sum_bij (fun d _ => d/e) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hd ⊢
    obtain ⟨⟨hd1, hd2⟩, hdvd⟩ := hd
    refine ⟨?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (by omega : 0 < e), Nat.div_mul_cancel hdvd]
      exact hd1
    · exact Nat.div_le_div_right hd2
  · intro d1 hd1 d2 hd2 heq
    simp only [Finset.mem_filter] at hd1 hd2
    rw [← Nat.mul_div_cancel' hd1.2, ← Nat.mul_div_cancel' hd2.2, heq]
  · intro b hb
    simp only [Finset.mem_Ioc] at hb
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨e*b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, dvd_mul_right e b⟩
      · rw [Nat.div_lt_iff_lt_mul (by omega : 0 < e)] at hb1
        rw [Nat.mul_comm e b]; exact hb1
      · rw [Nat.le_div_iff_mul_le (by omega : 0 < e)] at hb2
        rw [Nat.mul_comm e b]; exact hb2
    · exact Nat.mul_div_cancel_left b (by omega)
  · intro d hd
    rfl

theorem TZbox_stratum {e : ℕ} (he : 1 ≤ e) (γ : ℕ → ℕ → ℂ) (D r s : ℕ) :
    Work.FIArea4.TZbox D (2 * D) (Work.FIArea4.gLift γ e) r s =
      (if e ∣ s then (if Nat.Coprime r e then
          (jacobiSym (r : ℤ) (Work.FIPlan.oddPart e) : ℂ) else 0)
        * Work.FIArea4.TZbox (D / e) (2 * D / e) (Work.FIArea4.gamE γ e) r (s / e)
        else 0) := by
  simp only [Work.FIArea4.TZbox, Work.FIArea4.gLift, Work.FIArea4.gamE]
  have hstep : ∀ d : ℕ,
      (∑ a ∈ Finset.range d, (if Nat.gcd a d = e then γ a d else 0) * Work.FIArea4.Mentry d a r s)
        = if e ∣ d then
            (if e ∣ s then (if Nat.Coprime r e then (jacobiSym (r:ℤ) (Work.FIPlan.oddPart e) : ℂ) else 0) else 0)
              * (∑ a' ∈ Finset.range (d/e), (if Nat.Coprime a' (d/e) then γ (e*a') (e*(d/e)) else 0) * Work.FIArea4.Mentry (d/e) a' r (s/e))
          else 0 := fun d => inner_stratum he γ r s d
  rw [Finset.sum_congr rfl (fun d _ => hstep d)]
  rw [← Finset.sum_filter]
  rw [← Finset.mul_sum]
  rw [sum_Ioc_div (e := e) (D := D) he
    (fun d' => ∑ a' ∈ Finset.range d', (if Nat.Coprime a' d' then γ (e*a') (e*d') else 0) * Work.FIArea4.Mentry d' a' r (s/e))]
  rw [ite_mul, zero_mul]

end Work.FIArea4.WdyadGen
