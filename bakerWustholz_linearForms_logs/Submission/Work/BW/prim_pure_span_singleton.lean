import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A primitive vector `r` in a submodule `L ≤ ℤ^m` (meaning `r` is not a
non-trivial multiple of any element of `L`) spans a *saturated* cyclic
submodule: if `c • x ∈ ℤ·r` with `c ≠ 0` and `x ∈ L`, then already `x ∈ ℤ·r`.

The proof reduces `c • x = a • r` by the gcd `g = gcd a c` to the coprime
relation `c₁ • x = a₁ • r`; a Bézout combination then produces `y ∈ L` with
`x = a₁ • y` and `r = c₁ • y`, and primitivity forces `c₁ = ±1`. -/
theorem prim_pure_span_singleton {m : ℕ} {L : Submodule ℤ (Fin m → ℤ)} {r : Fin m → ℤ}
    (hr : r ∈ L)
    (hprim : ∀ (k : ℤ) (y : Fin m → ℤ), y ∈ L → 2 ≤ |k| → k • y ≠ r) :
    ∀ (c : ℤ) (x : Fin m → ℤ), x ∈ L → c ≠ 0 →
      c • x ∈ Submodule.span ℤ ({r} : Set (Fin m → ℤ)) →
        x ∈ Submodule.span ℤ ({r} : Set (Fin m → ℤ)) := by
  intro c x hxL hc hcx
  rw [Submodule.mem_span_singleton] at hcx ⊢
  obtain ⟨a, ha⟩ := hcx
  by_cases ha0 : a = 0
  · have h0 : c • x = 0 := by rw [← ha, ha0, zero_smul]
    have hx0 : x = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd h hc
      · exact h
    exact ⟨0, by rw [zero_smul, hx0]⟩
  · have hgpos : 0 < a.gcd c := Int.gcd_pos_of_ne_zero_left c ha0
    set g : ℤ := (a.gcd c : ℤ) with hg
    have hgne : g ≠ 0 := by rw [hg]; exact_mod_cast hgpos.ne'
    set a1 : ℤ := a / g with ha1
    set c1 : ℤ := c / g with hc1
    have ha_eq : g * a1 = a := by
      rw [ha1]; exact Int.mul_ediv_cancel' (by rw [hg]; exact Int.gcd_dvd_left a c)
    have hc_eq : g * c1 = c := by
      rw [hc1]; exact Int.mul_ediv_cancel' (by rw [hg]; exact Int.gcd_dvd_right a c)
    have hcop : a1.gcd c1 = 1 := by
      rw [ha1, hc1, hg]; exact Int.gcd_div_gcd_div_gcd hgpos
    set A : ℤ := a1.gcdA c1 with hA
    set B : ℤ := a1.gcdB c1 with hB
    have hBez : a1 * A + c1 * B = 1 := by
      rw [hA, hB]
      have h := Int.gcd_eq_gcd_ab a1 c1
      rw [hcop, Nat.cast_one] at h
      linarith
    have hrel : c1 • x = a1 • r := by
      have h1 : g • (c1 • x) = g • (a1 • r) := by
        simp only [smul_smul]
        rw [hc_eq, ha_eq, ha]
      exact smul_right_injective (Fin m → ℤ) hgne h1
    set y : Fin m → ℤ := A • x + B • r with hy
    have hyL : y ∈ L := by
      rw [hy]; exact L.add_mem (L.smul_mem A hxL) (L.smul_mem B hr)
    have hxy1 : a1 • y = x := by
      rw [hy]
      have h2 : (a1 * B) • r = (c1 * B) • x := by
        conv_lhs => rw [mul_comm a1 B, ← smul_smul, ← hrel, smul_smul, mul_comm B c1]
      simp only [smul_add, smul_smul]
      rw [h2, ← add_smul, hBez, one_smul]
    have hry1 : c1 • y = r := by
      rw [hy]
      have h2 : (c1 * A) • x = (a1 * A) • r := by
        conv_lhs => rw [mul_comm c1 A, ← smul_smul, hrel, smul_smul, mul_comm A a1]
      simp only [smul_add, smul_smul]
      rw [h2, ← add_smul, hBez, one_smul]
    have hc1ne : c1 ≠ 0 := by
      intro h; apply hc; rw [← hc_eq, h, mul_zero]
    have hsmall : ¬ (2 ≤ |c1|) := by
      intro h2; exact hprim c1 y hyL h2 hry1
    have hle : |c1| ≤ 1 := by omega
    have hc1sq : c1 * c1 = 1 := by
      rcases Int.abs_le_one_iff.mp hle with h | h | h
      · exact absurd h hc1ne
      · rw [h]; norm_num
      · rw [h]; norm_num
    have hyr : y = c1 • r := by
      have h : c1 • (c1 • y) = c1 • r := by rw [hry1]
      rwa [smul_smul, hc1sq, one_smul] at h
    exact ⟨a1 * c1, by rw [← hxy1, hyr, mul_smul]⟩

end Work.BW
