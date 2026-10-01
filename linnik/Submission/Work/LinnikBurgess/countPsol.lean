import Mathlib
import Submission.Work.LinnikBurgess.psolDefs

namespace Work.LinnikBurgess

open Polynomial

theorem countPsol {p n B ν : ℕ} [Fact p.Prime] (hν : 1 ≤ ν) (hB : 1 ≤ B)
    (y0 : ℤ) (H : Polynomial ℤ) (u : ℤ)
    (hu : ¬ ((p : ℤ) ∣ u)) (hH : ¬ ((p : ℤ) ∣ H.eval y0)) :
    ((Finset.range (p ^ n)).filter (fun x : ℕ =>
        ((p ^ B : ℕ) : ℤ) ∣ (x : ℤ) * u
          + (x : ℤ) ^ 2 * H.eval (y0 + ((p ^ ν : ℕ) : ℤ) * (x : ℤ)))).card
      ≤ 2 * p ^ (n - B) := by
  classical
  have hp1 : 1 ≤ p := le_of_lt (Fact.out : p.Prime).one_lt
  set T : Finset ℕ := (Finset.range (p ^ n)).filter
      (fun x : ℕ => ((p ^ B : ℕ) : ℤ) ∣ psolVal p ν y0 H u (x : ℤ)) with hT
  set S : Finset ℕ := (Finset.range (p ^ B)).filter
      (fun r : ℕ => ((p ^ B : ℕ) : ℤ) ∣ psolVal p ν y0 H u (r : ℤ)) with hS
  have memS : ∀ r : ℕ, r ∈ S ↔ r < p^B ∧ ((p:ℤ)^B) ∣ psolVal p ν y0 H u (r:ℤ) := by
    intro r
    rw [hS, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← Nat.cast_pow]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [Nat.cast_pow]; exact h2⟩
  have memT : ∀ x : ℕ, x ∈ T ↔ x < p^n ∧ ((p:ℤ)^B) ∣ psolVal p ν y0 H u (x:ℤ) := by
    intro x
    rw [hT, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← Nat.cast_pow]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [Nat.cast_pow]; exact h2⟩
  have hScard : S.card ≤ 2 := by
    have hsplit : S.card = (S.filter (fun r : ℕ => (p:ℤ) ∣ (r:ℤ))).card
        + (S.filter (fun r : ℕ => ¬ (p:ℤ) ∣ (r:ℤ))).card :=
      (Finset.card_filter_add_card_filter_not (s := S) (p := fun r : ℕ => (p:ℤ) ∣ (r:ℤ))).symm
    have h0 : (S.filter (fun r : ℕ => (p:ℤ) ∣ (r:ℤ))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      have ka : a = 0 := by
        obtain ⟨ha1, ha2⟩ := (memS a).mp ha.1
        exact psol_S_nonunit_eq_zero hν y0 H u hu ha1 ha.2 ha2
      have kb : b = 0 := by
        obtain ⟨hb1, hb2⟩ := (memS b).mp hb.1
        exact psol_S_nonunit_eq_zero hν y0 H u hu hb1 hb.2 hb2
      rw [ka, kb]
    have h1 : (S.filter (fun r : ℕ => ¬ (p:ℤ) ∣ (r:ℤ))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      obtain ⟨ha1, ha2⟩ := (memS a).mp ha.1
      obtain ⟨hb1, hb2⟩ := (memS b).mp hb.1
      exact psol_S_unit_eq hν y0 H u hu ha1 hb1 ha.2 hb.2 ha2 hb2
    omega
  have hmaps : Set.MapsTo (fun x : ℕ => x % p ^ B) ↑T ↑S := by
    intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    obtain ⟨hxn, hxP⟩ := (memT x).mp hx
    rw [memS]
    refine ⟨Nat.mod_lt _ (pow_pos (by omega : 0 < p) B), ?_⟩
    have hmod : ((p:ℤ)^B) ∣ ((x:ℤ) - ((x % p^B : ℕ) : ℤ)) := by
      have h := Nat.div_add_mod x (p^B)
      have hcast : ((p^B:ℕ):ℤ) * ((x / p^B : ℕ):ℤ) + ((x % p^B : ℕ):ℤ) = (x:ℤ) := by
        exact_mod_cast h
      have heq : (x:ℤ) - ((x % p^B : ℕ):ℤ) = ((p^B:ℕ):ℤ) * ((x / p^B : ℕ):ℤ) := by linarith
      rw [heq, Nat.cast_pow]
      exact dvd_mul_right _ _
    have h1 : ((p:ℤ)^B) ∣ (psolPoly p ν y0 H u).eval (x:ℤ) := by
      rw [psolPoly_eval]; exact hxP
    have h2 : ((p:ℤ)^B) ∣ (psolPoly p ν y0 H u).eval (x:ℤ)
        - (psolPoly p ν y0 H u).eval ((x % p^B : ℕ):ℤ) := psolPoly_sub_dvd y0 H u hmod
    have h3 := dvd_sub h1 h2
    have heq : (psolPoly p ν y0 H u).eval (x:ℤ)
        - ((psolPoly p ν y0 H u).eval (x:ℤ) - (psolPoly p ν y0 H u).eval ((x % p^B : ℕ):ℤ))
        = (psolPoly p ν y0 H u).eval ((x % p^B : ℕ):ℤ) := by ring
    rw [heq, psolPoly_eval] at h3
    exact h3
  have hfiber : T.card = ∑ r ∈ S, (T.filter (fun x : ℕ => x % p ^ B = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ r ∈ S, (T.filter (fun x : ℕ => x % p ^ B = r)).card ≤ p^(n-B) := by
    intro r _
    have hsub : T.filter (fun x : ℕ => x % p ^ B = r)
        ⊆ (Finset.range (p ^ n)).filter (fun x : ℕ => x % p ^ B = r) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_range.mpr ((memT x).mp hx.1).1, hx.2⟩
    exact (Finset.card_le_card hsub).trans (card_residue_filter_le hp1 B n r)
  calc T.card = ∑ r ∈ S, (T.filter (fun x : ℕ => x % p ^ B = r)).card := hfiber
    _ ≤ ∑ r ∈ S, p^(n-B) := Finset.sum_le_sum hbound
    _ = S.card * p^(n-B) := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * p^(n-B) := Nat.mul_le_mul_right _ hScard


end Work.LinnikBurgess
