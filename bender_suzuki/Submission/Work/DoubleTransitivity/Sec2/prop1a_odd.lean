import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec2.prop1a_odd`

Peterfalvi I §2, Proposition 1 (a) (first assertion): if `H` is a Bender subgroup of a finite
group `G` and `s, t` are involutions of `G` having no common fixed point on `Ω = G ⧸ H`, then
`s * t` has odd order.

The proof is the one from the source: if `s * t` had even order, then `⟨s * t⟩` contains an
involution `u`, and `s` and `t` both invert `s * t`, hence commute with `u`.  Since `u` is an
involution it has a unique fixed point `ω` on `Ω` (`Sec1.unique_fixed`); the commuting of `s`
and `t` with `u` makes `s • ω` and `t • ω` fixed by `u` as well, so by uniqueness they equal
`ω`.  Thus `ω` is a common fixed point of `s` and `t`, contrary to hypothesis.
-/

set_option autoImplicit false

open Submission.Blueprint
open Work.DoubleTransitivity

namespace Work.DoubleTransitivity.Sec2

/-- If `s` inverts `g` (i.e. `s * g * s⁻¹ = g⁻¹`), then it inverts every power of `g`. -/
private lemma pow_conj_eq_inv {G : Type} [Group G] {s g : G} (hsg : s * g * s⁻¹ = g⁻¹) :
    ∀ m : ℕ, s * g ^ m * s⁻¹ = (g ^ m)⁻¹ := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
     have h : (s * g ^ k * s⁻¹) * (s * g * s⁻¹) = s * g ^ (k + 1) * s⁻¹ := by
        rw [pow_succ]; group
     rw [← h, ih, hsg]
     rw [← mul_inv_rev, pow_succ']

theorem prop1a_odd {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsBender H)
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hst : ¬ ∃ ω : Omega H, s • ω = ω ∧ t • ω = ω) :
    Odd (orderOf (s * t)) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨m, hm⟩ := heven
  have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  set g := s * t with hg
  have hgp : g ^ (m + m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one g
  set u := g ^ m with hu
  have hpos : 0 < m := by have := orderOf_pos g; omega
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← pow_mul, show m * 2 = m + m from by ring, hgp]
  have hu_ne : u ≠ 1 := by
    intro h1
    rw [hu] at h1
    have hdvd : orderOf g ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hle : orderOf g ≤ m := Nat.le_of_dvd hpos hdvd
    omega
  have hu_ord : orderOf u = 2 := orderOf_eq_prime hu2 hu_ne
  -- `s` and `t` both invert `g = s * t`.
  have hsg : s * g * s⁻¹ = g⁻¹ := by
    rw [hg]
    have h1 : s * (s * t) * s⁻¹ = t * s⁻¹ := by
      rw [← mul_assoc s s t, ← pow_two, hs2, one_mul]
    have h2 : (s * t)⁻¹ = t * s⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (show t * t = 1 by rw [← pow_two]; exact ht2)]
    rw [h1, h2]
  have htg : t * g * t⁻¹ = g⁻¹ := by
    rw [hg]
    have h1 : t * (s * t) * t⁻¹ = t * s := by group
    have h2 : (s * t)⁻¹ = t * s := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (show t * t = 1 by rw [← pow_two]; exact ht2),
          inv_eq_of_mul_eq_one_right (show s * s = 1 by rw [← pow_two]; exact hs2)]
    rw [h1, h2]
  -- hence both commute with `u = g ^ m`.
  have huinv : u⁻¹ = u := by
    rw [inv_eq_iff_mul_eq_one]; rw [← pow_two]; exact hu2
  have hsu : s * u = u * s := by
    have h1 : s * u * s⁻¹ = u⁻¹ := by rw [hu]; exact pow_conj_eq_inv hsg m
    rw [huinv] at h1
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [h1]
  have htu : t * u = u * t := by
    have h1 : t * u * t⁻¹ = u⁻¹ := by rw [hu]; exact pow_conj_eq_inv htg m
    rw [huinv] at h1
    calc t * u = (t * u * t⁻¹) * t := by group
      _ = u * t := by rw [h1]
  -- `u` is an involution, so it has a unique fixed point on `Ω`.
  obtain ⟨ω, hωu, huniq⟩ := Sec1.unique_fixed hH hu_ord
  have hsω : s • ω = ω := by
    have hfix : u • (s • ω) = s • ω := by
      rw [← mul_smul, hsu.symm, mul_smul, hωu]
    exact huniq (s • ω) hfix
  have htω : t • ω = ω := by
    have hfix : u • (t • ω) = t • ω := by
      rw [← mul_smul, htu.symm, mul_smul, hωu]
    exact huniq (t • ω) hfix
  exact hst ⟨ω, hsω, htω⟩

end Work.DoubleTransitivity.Sec2
