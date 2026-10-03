import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.jacobi_congruence_count
import Submission.Work.FIArea4.Evar_eq_sum_clsSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# The sharp trivial bound for the local variance `E(d)` of FI (11.7)

`Work.FIPlan.Evar R S d α = Σ_{a < d} |Σ_{r̄s ≡ a (d)} α_{rs}(r/d')|²` is a sum of squared
"class sums", the classes being the residue classes `a ≡ s r⁻¹ (mod d)` of the box
`[1,2R] × [1,2S]` restricted to `r` coprime to `d`.  Cauchy–Schwarz in each class shows

  `E(d) ≤ (max class size) · p14L2 R S α`,

so everything rests on counting a single class.  Two elementary counts give the sharp bound

  `#class(a) ≤ min (4RS/d + 2R, 4RS/d + 2S) ≤ 4RS/d + 2√(RS)`:

* for each `r` the integer `s ≤ 2S` is determined modulo `d`, so `#class ≤ 2R·⌊2S/d + 1⌋`;
* writing `g = (a,d)`, the equation `s ≡ r a (mod d)` with `(r,d) = 1` forces `(s,d) = g`,
  hence `s = g s₁` with `s₁ ≤ 2S/g`; for each `s₁` the count `r a/g ≡ s₁ (mod d/g)` puts `r`
  in a single class modulo `d/g`, so `#class ≤ (2S/g)·(⌊2R/(d/g)⌋ + 1) ≤ 4RS/d + 2S`.

This is the sharp form of the trivial bound of `Submission/Work/FIArea4/Evar_le_trivial.lean`;
FI use it implicitly in (11.7) (via Lemma 11.2, `jacobi_congruence_count`, which is the same
count with `(a,d) = 1`).
-/

/-! ## Two elementary number-theoretic ingredients -/

/-- **Cancelling a factor coprime to the modulus**: `(r·a, d) = (a, d)` when `(r, d) = 1`. -/
lemma gcd_mul_eq_gcd_of_coprime {r a d : ℕ} (h : Nat.Coprime r d) :
    Nat.gcd (r * a) d = Nat.gcd a d := by
  refine Nat.dvd_antisymm ?_ ?_
  · have hkr : Nat.Coprime (Nat.gcd (r * a) d) r :=
      h.symm.coprime_dvd_left (Nat.gcd_dvd_right (r*a) d)
    have hka : Nat.gcd (r * a) d ∣ a :=
      (hkr.dvd_mul_right).mp (by rw [Nat.mul_comm a r]; exact Nat.gcd_dvd_left (r*a) d)
    exact Nat.dvd_gcd hka (Nat.gcd_dvd_right (r*a) d)
  · exact Nat.dvd_gcd (dvd_mul_of_dvd_right (Nat.gcd_dvd_left a d) r) (Nat.gcd_dvd_right a d)

/-- **The class equation determines `r` modulo `d/(a,d)`**: if `s = r a` and `s = r₀ a` in
`ZMod d`, then `r ≡ r₀ (mod d/(a,d))`.  (No coprimality is needed: the two congruences give
`d ∣ (r - r₀)·a`, and dividing by `(a,d)` leaves a factor coprime to `d/(a,d)`.) -/
lemma modEq_of_zmod_eq (d a s r r₀ : ℕ) (hd : 0 < d)
    (hr : (s : ZMod d) = (r : ZMod d) * (a : ZMod d))
    (hr₀ : (s : ZMod d) = (r₀ : ZMod d) * (a : ZMod d)) :
    r ≡ r₀ [MOD d / Nat.gcd a d] := by
  have h1 : (r * a) % d = s % d := by
    have hh : ((r * a : ℕ) : ZMod d) = (s : ZMod d) := by rw [Nat.cast_mul]; exact hr.symm
    exact (ZMod.natCast_eq_natCast_iff' (r*a) s d).mp hh
  have h2 : (r₀ * a) % d = s % d := by
    have hh : ((r₀ * a : ℕ) : ZMod d) = (s : ZMod d) := by rw [Nat.cast_mul]; exact hr₀.symm
    exact (ZMod.natCast_eq_natCast_iff' (r₀*a) s d).mp hh
  have hmod : r * a ≡ r₀ * a [MOD d] := by
    show (r*a) % d = (r₀*a) % d
    rw [h1, h2]
  have hc := hmod.cancel_right_div_gcd hd
  simpa only [Nat.gcd_comm a d] using hc

/-- **The class equation forces `(s,d) = (a,d)`**: if `s = r a` in `ZMod d` and `(r,d) = 1`,
then `(s,d) = (a,d)`.  In particular `(a,d) ∣ s`. -/
lemma gcd_zmod_eq_gcd_a (d a s r : ℕ)
    (hrcop : Nat.Coprime r d)
    (h : (s : ZMod d) = (r : ZMod d) * (a : ZMod d)) :
    Nat.gcd s d = Nat.gcd a d := by
  have h1 : (r * a) % d = s % d := by
    have hh : ((r * a : ℕ) : ZMod d) = (s : ZMod d) := by rw [Nat.cast_mul]; exact h.symm
    exact (ZMod.natCast_eq_natCast_iff' (r*a) s d).mp hh
  have key : ∀ m : ℕ, Nat.gcd m d = Nat.gcd (m % d) d := by
    intro m
    rw [Nat.gcd_comm m d, Nat.gcd_rec]
  rw [key s, ← h1, ← key (r * a)]
  exact gcd_mul_eq_gcd_of_coprime hrcop

/-! ## Counting one residue class -/

/-- The `r`'s of the class `a` whose second coordinate is `s`: the fibre over `s` of the map
`p ↦ p.2` on `EvarCls R S d a`. -/
def EvarClsFiber (R d a s : ℕ) : Finset ℕ :=
  (EvarR R d).filter (fun r => (s : ZMod d) = (r : ZMod d) * (a : ZMod d))

/-- The fibre over `s` of the class `a` is contained in a single residue class modulo
`d/(a,d)`, so it has at most `⌊2R/(d/(a,d))⌋ + 1` elements. -/
lemma EvarClsFiber_card_le (R d a s : ℕ) (hd : 0 < d) :
    (EvarClsFiber R d a s).card ≤ 2 * R / (d / Nat.gcd a d) + 1 := by
  have hd1 : 0 < d / Nat.gcd a d :=
    Nat.div_pos (Nat.le_of_dvd hd (Nat.gcd_dvd_right a d)) (Nat.gcd_pos_of_pos_right a hd)
  by_cases hne : (EvarClsFiber R d a s).Nonempty
  · obtain ⟨r₀, hr₀⟩ := hne
    have hr₀c : (s : ZMod d) = (r₀ : ZMod d) * (a : ZMod d) := (Finset.mem_filter.mp hr₀).2
    have hsub : EvarClsFiber R d a s ⊆ (Finset.Icc 1 (2 * R)).filter
        (fun r : ℕ => r % (d / Nat.gcd a d) = r₀ % (d / Nat.gcd a d)) := by
      intro r hr
      rw [EvarClsFiber, Finset.mem_filter] at hr
      obtain ⟨hrE, hrc⟩ := hr
      rw [Finset.mem_filter]
      obtain ⟨hrmem, -⟩ := mem_EvarR.mp hrE
      exact ⟨hrmem, modEq_of_zmod_eq d a s r r₀ hd hrc hr₀c⟩
    calc (EvarClsFiber R d a s).card
        ≤ ((Finset.Icc 1 (2 * R)).filter
            (fun r : ℕ => r % (d / Nat.gcd a d) = r₀ % (d / Nat.gcd a d))).card :=
          Finset.card_le_card hsub
      _ ≤ 2 * R / (d / Nat.gcd a d) + 1 :=
          card_filter_mod_le (d / Nat.gcd a d) (2 * R) (r₀ % (d / Nat.gcd a d)) hd1
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp

/-- If `(a,d) ∤ s` then the fibre over `s` is empty: a pair of the class would give
`(s,d) = (a,d)`. -/
lemma EvarClsFiber_eq_empty_of_not_dvd (R d a s : ℕ) (_hd : 0 < d)
    (h : ¬ Nat.gcd a d ∣ s) : EvarClsFiber R d a s = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨r, hr⟩
  rw [EvarClsFiber, Finset.mem_filter] at hr
  obtain ⟨hrE, hrc⟩ := hr
  obtain ⟨-, hrcop⟩ := mem_EvarR.mp hrE
  have hg := gcd_zmod_eq_gcd_a d a s r hrcop hrc
  exact h (hg ▸ Nat.gcd_dvd_left s d)

/-- The number of multiples of `g` in `[1, 2S]` is at most `2S/g`. -/
lemma card_multiples_Icc_le (S g : ℕ) (hg : 0 < g) :
    (((Finset.Icc 1 (2 * S)).filter (fun s => g ∣ s)).card) ≤ 2 * S / g := by
  have hinj : Set.InjOn (fun s : ℕ => s / g)
      ↑((Finset.Icc 1 (2 * S)).filter (fun s => g ∣ s)) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
    have hxy' : x / g = y / g := hxy
    calc x = g * (x / g) := (Nat.mul_div_cancel' hx.2).symm
      _ = g * (y / g) := by rw [hxy']
      _ = y := Nat.mul_div_cancel' hy.2
  have hsub : ((Finset.Icc 1 (2 * S)).filter (fun s => g ∣ s)).image (fun s => s / g)
      ⊆ Finset.Icc 1 (2 * S / g) := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at hs
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hs.1.2⟩
    rw [Nat.one_le_div_iff hg]
    exact Nat.le_of_dvd (by omega) hs.2
  calc ((Finset.Icc 1 (2 * S)).filter (fun s => g ∣ s)).card
      = (((Finset.Icc 1 (2 * S)).filter (fun s => g ∣ s)).image (fun s => s / g)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 (2 * S / g)).card := Finset.card_le_card hsub
    _ = 2 * S / g := by rw [Nat.card_Icc, Nat.add_sub_cancel]

/-! ## The sharp class-size bound -/

/-- **The sharp class-size bound**: every residue class of the local variance contains at most
`4RS/d + 2√(RS) + 2` pairs. -/
lemma EvarCls_card_le_sharp (R S d a : ℕ) (hd : 0 < d) :
    ((EvarCls R S d a).card : ℝ)
      ≤ 4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) + 2 := by
  -- the `r`-count
  have hA : ((EvarCls R S d a).card : ℝ)
      ≤ 4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * (R : ℝ) := by
    have h1 : (EvarCls R S d a).card ≤ 2 * R * (2 * S / d + 1) := EvarCls_card_le R S d a hd
    have hdiv : (((2 * S / d : ℕ)) : ℝ) ≤ 2 * (S : ℝ) / (d : ℝ) := by
      have h := Nat.cast_div_le (α := ℝ) (m := 2 * S) (n := d)
      simpa using h
    have hR : (0 : ℝ) ≤ 2 * (R : ℝ) := by positivity
    have h3 : (((2 * R * (2 * S / d + 1) : ℕ)) : ℝ)
        = 2 * (R : ℝ) * (((2 * S / d : ℕ)) : ℝ) + 2 * (R : ℝ) := by
      push_cast; ring
    have h4 : 2 * (R : ℝ) * (((2 * S / d : ℕ)) : ℝ)
        ≤ 2 * (R : ℝ) * (2 * (S : ℝ) / (d : ℝ)) := mul_le_mul_of_nonneg_left hdiv hR
    have h5 : 2 * (R : ℝ) * (2 * (S : ℝ) / (d : ℝ))
        = 4 * (R : ℝ) * (S : ℝ) / (d : ℝ) := by ring
    have h2 : (((2 * R * (2 * S / d + 1) : ℕ)) : ℝ)
        ≤ 4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * (R : ℝ) := by
      rw [h3]; linarith
    exact le_trans (by exact_mod_cast h1) h2
  -- the `s`-count
  have hB : ((EvarCls R S d a).card : ℝ)
      ≤ 4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * (S : ℝ) := by
    have hgpos : 0 < Nat.gcd a d := Nat.gcd_pos_of_pos_right a hd
    have hgR : (0 : ℝ) < (Nat.gcd a d : ℝ) := by exact_mod_cast hgpos
    have hdvd : Nat.gcd a d ∣ d := Nat.gcd_dvd_right a d
    have hBcard : (EvarCls R S d a).card
        ≤ (2 * S / Nat.gcd a d) * (2 * R / (d / Nat.gcd a d) + 1) := by
      have hdec : (EvarCls R S d a).card
          = ∑ s ∈ Finset.Icc 1 (2 * S), (EvarClsFiber R d a s).card := by
        rw [EvarCls]
        rw [← Finset.product_eq_sprod]
        rw [card_filter_product_eq_sum_snd]
        rfl
      rw [hdec]
      have hsplit : ∑ s ∈ Finset.Icc 1 (2 * S), (EvarClsFiber R d a s).card
          = ∑ s ∈ (Finset.Icc 1 (2 * S)).filter (fun s => Nat.gcd a d ∣ s),
              (EvarClsFiber R d a s).card := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        by_cases h : Nat.gcd a d ∣ s
        · simp [h]
        · rw [if_neg h, EvarClsFiber_eq_empty_of_not_dvd R d a s hd h]
          simp
      rw [hsplit]
      have hmult := card_multiples_Icc_le S (Nat.gcd a d) hgpos
      calc ∑ s ∈ (Finset.Icc 1 (2 * S)).filter (fun s => Nat.gcd a d ∣ s),
              (EvarClsFiber R d a s).card
          ≤ ∑ s ∈ (Finset.Icc 1 (2 * S)).filter (fun s => Nat.gcd a d ∣ s),
              (2 * R / (d / Nat.gcd a d) + 1) :=
            Finset.sum_le_sum (fun s _ => EvarClsFiber_card_le R d a s hd)
        _ = ((Finset.Icc 1 (2 * S)).filter (fun s => Nat.gcd a d ∣ s)).card
              * (2 * R / (d / Nat.gcd a d) + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
        _ ≤ (2 * S / Nat.gcd a d) * (2 * R / (d / Nat.gcd a d) + 1) :=
            Nat.mul_le_mul_right _ hmult
    have hcast0 : ((EvarCls R S d a).card : ℝ)
        ≤ (((2 * S / Nat.gcd a d) * (2 * R / (d / Nat.gcd a d) + 1) : ℕ) : ℝ) := by
      exact_mod_cast hBcard
    refine le_trans hcast0 ?_
    have hd1R : (((d / Nat.gcd a d : ℕ)) : ℝ) = (d : ℝ) / (Nat.gcd a d : ℝ) :=
      Nat.cast_div hdvd (by positivity)
    have hA1 : (((2 * S / Nat.gcd a d : ℕ)) : ℝ) ≤ 2 * (S : ℝ) / (Nat.gcd a d : ℝ) := by
      have h := Nat.cast_div_le (α := ℝ) (m := 2 * S) (n := Nat.gcd a d)
      simpa using h
    have hA2 : (((2 * R / (d / Nat.gcd a d) : ℕ)) : ℝ)
        ≤ 2 * (R : ℝ) / (((d / Nat.gcd a d : ℕ)) : ℝ) := by
      have h := Nat.cast_div_le (α := ℝ) (m := 2 * R) (n := d / Nat.gcd a d)
      simpa using h
    have hcast : ((((2 * S / Nat.gcd a d) * (2 * R / (d / Nat.gcd a d) + 1) : ℕ)) : ℝ)
        = (((2 * S / Nat.gcd a d : ℕ)) : ℝ)
            * ((((2 * R / (d / Nat.gcd a d) : ℕ)) : ℝ) + 1) := by
      push_cast; ring
    rw [hcast]
    have hA2' : (((2 * R / (d / Nat.gcd a d) : ℕ)) : ℝ) + 1
        ≤ 2 * (R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) + 1 := by
      have h := hA2
      rw [hd1R] at h
      have hdiv : 2 * (R : ℝ) / ((d : ℝ) / (Nat.gcd a d : ℝ))
          = 2 * (R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) := by
        rw [div_div_eq_mul_div]
      linarith [h, hdiv.le]
    have hstep : (((2 * S / Nat.gcd a d : ℕ)) : ℝ)
          * ((((2 * R / (d / Nat.gcd a d) : ℕ)) : ℝ) + 1)
        ≤ (2 * (S : ℝ) / (Nat.gcd a d : ℝ))
            * (2 * (R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) + 1) :=
      mul_le_mul hA1 hA2' (by positivity) (by positivity)
    have hfin : (2 * (S : ℝ) / (Nat.gcd a d : ℝ))
          * (2 * (R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) + 1)
        ≤ 4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * (S : ℝ) := by
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      have heq : (2 * (S : ℝ) / (Nat.gcd a d : ℝ))
            * (2 * (R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) + 1)
          = 4 * (R : ℝ) * (S : ℝ) / (d : ℝ)
              + 2 * (S : ℝ) / (Nat.gcd a d : ℝ) := by
        field_simp
        ring
      rw [heq]
      have hle : 2 * (S : ℝ) / (Nat.gcd a d : ℝ) ≤ 2 * (S : ℝ) := by
        rw [div_le_iff₀ hgR]
        have hg1 : (1 : ℝ) ≤ (Nat.gcd a d : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hgpos)
        have hS0 : (0 : ℝ) ≤ 2 * (S : ℝ) := by positivity
        nlinarith [hg1, hS0]
      linarith
    linarith [hstep, hfin]
  -- combine the two counts
  have hmin : min (2 * (R : ℝ)) (2 * (S : ℝ)) ≤ 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) := by
    rcases le_total (R : ℝ) (S : ℝ) with hle | hle
    · rw [min_eq_left (by linarith)]
      have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
      have hs : (R : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := by
        calc (R : ℝ) = Real.sqrt ((R : ℝ) * (R : ℝ)) := (Real.sqrt_mul_self hR0).symm
          _ ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := Real.sqrt_le_sqrt (by nlinarith)
      linarith
    · rw [min_eq_right (by linarith)]
      have hS0 : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
      have hs : (S : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := by
        calc (S : ℝ) = Real.sqrt ((S : ℝ) * (S : ℝ)) := (Real.sqrt_mul_self hS0).symm
          _ ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := Real.sqrt_le_sqrt (by nlinarith)
      linarith
  have hc : ((EvarCls R S d a).card : ℝ)
      ≤ 4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + min (2 * (R : ℝ)) (2 * (S : ℝ)) := by
    rcases le_total (2 * (R : ℝ)) (2 * (S : ℝ)) with hle | hle
    · rw [min_eq_left hle]; exact hA
    · rw [min_eq_right hle]; exact hB
  have hsq : (0 : ℝ) ≤ Real.sqrt ((R : ℝ) * (S : ℝ)) := Real.sqrt_nonneg _
  linarith

/-! ## The local variance -/

/-- **The sharp trivial bound for the local variance of FI (11.7)**: every residue class of
`Work.FIPlan.Evar R S d α` contains at most `4RS/d + 2√(RS) + 2` pairs, and Cauchy-Schwarz in the
class sums gives `E(d) ≤ (max class size)·p14L2 R S α`. The class count is FI Lemma 11.2
(`Submission.Work.FIArea4.jacobi_congruence_count`) applied after the reduction `g = gcd(a,d)`,
`s = g·s₁`, or, more elementarily, two applications of the fact that a class mod `d'` has at most
`2R/d' + 1` elements. -/
theorem P13_sharp_evar :
    ∀ (R S d : ℕ) (α : ℕ → ℕ → ℂ), 0 < d →
      Work.FIPlan.Evar R S d α
        ≤ (4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) + 2)
          * p14L2 R S α := by
  intro R S d α hd
  have hterm : ∀ a, Complex.normSq (clsSum R S d α a)
      ≤ (4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) + 2)
        * ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) := by
    intro a
    rw [clsSum]
    have hcs := normSq_sum_le_card_mul_sum (EvarCls R S d a)
      (fun p => α p.1 p.2 * jw d p.1)
    have hcls : ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2 * jw d p.1)
        ≤ ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) :=
      Finset.sum_le_sum (fun p _ => normSq_mul_jacobiSym_le _ _ _)
    calc Complex.normSq (∑ p ∈ EvarCls R S d a, α p.1 p.2 * jw d p.1)
        ≤ ((EvarCls R S d a).card : ℝ)
            * ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2 * jw d p.1) := hcs
      _ ≤ ((EvarCls R S d a).card : ℝ)
            * ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) :=
          mul_le_mul_of_nonneg_left hcls (Nat.cast_nonneg _)
      _ ≤ (4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) + 2)
            * ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) :=
          mul_le_mul_of_nonneg_right (EvarCls_card_le_sharp R S d a hd)
            (Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg _))
  rw [Evar_eq_sum_clsSum]
  calc ∑ a ∈ Finset.range d, Complex.normSq (clsSum R S d α a)
      ≤ ∑ a ∈ Finset.range d,
          (4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) + 2)
            * ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) :=
        Finset.sum_le_sum (fun a _ => hterm a)
    _ = (4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) + 2)
          * ∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2) := by
        rw [Finset.mul_sum]
    _ ≤ (4 * (R : ℝ) * (S : ℝ) / (d : ℝ) + 2 * Real.sqrt ((R : ℝ) * (S : ℝ)) + 2)
          * p14L2 R S α := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∑ a ∈ Finset.range d, ∑ p ∈ EvarCls R S d a, Complex.normSq (α p.1 p.2)
            ≤ ∑ p ∈ EvarR R d ×ˢ Finset.Icc 1 (2 * S), Complex.normSq (α p.1 p.2) :=
              sum_EvarCls_le R S d hd _ (fun p => Complex.normSq_nonneg _)
          _ ≤ ∑ p ∈ Finset.Icc 1 (2 * R) ×ˢ Finset.Icc 1 (2 * S),
                Complex.normSq (α p.1 p.2) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.product_subset_product_left (Finset.filter_subset _ _)) ?_
              intro p _ _
              exact Complex.normSq_nonneg _
          _ = p14L2 R S α := by
              rw [p14L2, Finset.sum_product]

end

end Work.FIArea4
