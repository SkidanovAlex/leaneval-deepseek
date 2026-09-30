import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- Two edges of the MRT graph with the same pair of left endpoints `(x₁, x₂)` and both
satisfying the edge geometry at scale `(P₁, L)` with respect to the separated family `S`
are the same edge: the primes `p₁, p₂` are forced.

The point is that the ratio `p₂ / p₁` is pinned down to within `O(L / x₂)`, and since
`x₂ ≫ L P₁²` while two distinct ratios of primes in `[P₁, 2P₁]` differ by at least
`1/(4 P₁²)`, the ratio is exact.  Equality of the two cross products `p₂ p₁' = p₂' p₁`
together with primality then gives `p₁ = p₁'` and `p₂ = p₂'`. -/
theorem edge_unique (P₁ L : ℝ) (S : Finset ℝ) (e e' : Work.BMF.Edge)
    (hP : 0 < P₁) (hL : 0 < L) (hsep : ∀ x ∈ S, 800 * L * P₁ ^ 2 < x)
    (h₁ : Work.BMF.EdgeGeom S P₁ L e) (h₂ : Work.BMF.EdgeGeom S P₁ L e')
    (hx₁ : e.x₁ = e'.x₁) (hx₂ : e.x₂ = e'.x₂) :
    e.p₁ = e'.p₁ ∧ e.p₂ = e'.p₂ := by
  obtain ⟨_, hx2S, _, hpne, hpr1, hpr2, hgeom⟩ := h₁
  obtain ⟨_, _, _, _, hpr1', _, hgeom'⟩ := h₂
  obtain ⟨hp1, _, hP1le2⟩ := hpr1
  obtain ⟨hp2, _, _⟩ := hpr2
  obtain ⟨hp1', _, hP1le2'⟩ := hpr1'
  have hp1Rpos : (0:ℝ) < e.p₁ := by exact_mod_cast hp1.pos
  have hp1R'pos : (0:ℝ) < e'.p₁ := by exact_mod_cast hp1'.pos
  set A : ℝ := (e.p₂ : ℝ) / e.p₁ with hA
  set B : ℝ := (e'.p₂ : ℝ) / e'.p₁ with hB
  have hx2pos : 0 < e.x₂ := lt_trans (by positivity) (hsep e.x₂ hx2S)
  -- the second edge, expressed at the common endpoints `(e.x₁, e.x₂)`
  have hgeomB : |e.x₁ - B * e.x₂| ≤ 100 * L := by
    rw [← hx₁, ← hx₂] at hgeom'
    exact hgeom'
  -- both ratios sit within `O(L)` of `x₁ / x₂`
  have hdiff : |A - B| * e.x₂ ≤ 200 * L := by
    rw [show |A - B| * e.x₂ = |A * e.x₂ - B * e.x₂| from by
      conv_lhs => rw [← abs_of_pos hx2pos, ← abs_mul]
      congr 1
      ring]
    have h1 : |A * e.x₂ - B * e.x₂| = |(e.x₁ - B * e.x₂) - (e.x₁ - A * e.x₂)| := by
      congr 1; ring
    have h2 : |(e.x₁ - B * e.x₂) - (e.x₁ - A * e.x₂)| ≤
        |e.x₁ - B * e.x₂| + |e.x₁ - A * e.x₂| := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [le_abs_self (e.x₁ - B * e.x₂), neg_le_abs (e.x₁ - A * e.x₂)],
             by linarith [le_abs_self (e.x₁ - A * e.x₂), neg_le_abs (e.x₁ - B * e.x₂)]⟩
    rw [h1]
    linarith [h2, hgeom, hgeomB]
  -- hence the ratios differ by less than `1 / (4 P₁²)`
  have hratio_lt : |A - B| < 1 / (4 * P₁ ^ 2) := by
    have h4P : 0 ≤ (4 : ℝ) * P₁ ^ 2 := by positivity
    have h1 : |A - B| * ((4 : ℝ) * P₁ ^ 2) * e.x₂ ≤ 200 * L * ((4 : ℝ) * P₁ ^ 2) := by
      have hm := mul_le_mul_of_nonneg_right hdiff h4P
      nlinarith [hm]
    have h2 : 200 * L * ((4 : ℝ) * P₁ ^ 2) < e.x₂ := by
      have hs := hsep e.x₂ hx2S
      nlinarith [hs]
    have hstep : (|A - B| * ((4 : ℝ) * P₁ ^ 2)) * e.x₂ < 1 * e.x₂ := by
      rw [one_mul]
      linarith
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4 * P₁ ^ 2)]
    exact (mul_lt_mul_iff_of_pos_right hx2pos).mp hstep
  -- so the cross product `p₂ p₁' - p₂' p₁`, an integer, has absolute value `< 1`
  have hnum : |(e.p₂ : ℝ) * e'.p₁ - (e'.p₂ : ℝ) * e.p₁| < 1 := by
    have hpos : 0 < (e.p₁ : ℝ) * (e'.p₁ : ℝ) := mul_pos hp1Rpos hp1R'pos
    have hdecomp : A - B =
        ((e.p₂ : ℝ) * e'.p₁ - (e'.p₂ : ℝ) * e.p₁) / ((e.p₁ : ℝ) * (e'.p₁ : ℝ)) := by
      rw [hA, hB]; field_simp
    have heq : |(e.p₂ : ℝ) * e'.p₁ - (e'.p₂ : ℝ) * e.p₁| =
        |A - B| * ((e.p₁ : ℝ) * (e'.p₁ : ℝ)) := by
      rw [hdecomp, abs_div, abs_of_pos hpos]
      exact (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
    rw [heq]
    have hle : ((e.p₁ : ℝ) * (e'.p₁ : ℝ)) ≤ 4 * P₁ ^ 2 := by
      nlinarith [hP1le2, hP1le2', mul_nonneg (le_of_lt hp1Rpos) (le_of_lt hp1R'pos), hP]
    have hstep1 : |A - B| * ((e.p₁ : ℝ) * (e'.p₁ : ℝ)) <
        (1 / (4 * P₁ ^ 2)) * ((e.p₁ : ℝ) * (e'.p₁ : ℝ)) :=
      mul_lt_mul_of_pos_right hratio_lt hpos
    have hstep2 : (1 / (4 * P₁ ^ 2)) * ((e.p₁ : ℝ) * (e'.p₁ : ℝ)) ≤
        (1 / (4 * P₁ ^ 2)) * (4 * P₁ ^ 2) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    calc |A - B| * ((e.p₁ : ℝ) * (e'.p₁ : ℝ))
        < (1 / (4 * P₁ ^ 2)) * ((e.p₁ : ℝ) * (e'.p₁ : ℝ)) := hstep1
      _ ≤ (1 / (4 * P₁ ^ 2)) * (4 * P₁ ^ 2) := hstep2
      _ = 1 := by rw [one_div, inv_mul_cancel₀ (by positivity : (4:ℝ) * P₁ ^ 2 ≠ 0)]
  -- the integer cross product vanishes: `p₂ p₁' = p₂' p₁`
  have hNM : e.p₂ * e'.p₁ = e'.p₂ * e.p₁ := by
    have hnum' : |((e.p₂ * e'.p₁ : ℕ) : ℝ) - ((e'.p₂ * e.p₁ : ℕ) : ℝ)| < 1 := by
      push_cast
      exact hnum
    have hlt1 : ((e.p₂ * e'.p₁ : ℕ) : ℝ) - ((e'.p₂ * e.p₁ : ℕ) : ℝ) < 1 :=
      (abs_lt.mp hnum').2
    have hlt2 : ((e'.p₂ * e.p₁ : ℕ) : ℝ) - ((e.p₂ * e'.p₁ : ℕ) : ℝ) < 1 := by
      linarith [(abs_lt.mp hnum').1]
    rcases le_total (e.p₂ * e'.p₁) (e'.p₂ * e.p₁) with h | h
    · have hc : (((e'.p₂ * e.p₁) - (e.p₂ * e'.p₁) : ℕ) : ℝ) < 1 := by
        rw [Nat.cast_sub h]; exact hlt2
      have hc' : (e'.p₂ * e.p₁) - (e.p₂ * e'.p₁) < 1 := by exact_mod_cast hc
      omega
    · have hc : (((e.p₂ * e'.p₁) - (e'.p₂ * e.p₁) : ℕ) : ℝ) < 1 := by
        rw [Nat.cast_sub h]; exact hlt1
      have hc' : (e.p₂ * e'.p₁) - (e'.p₂ * e.p₁) < 1 := by exact_mod_cast hc
      omega
  -- primality upgrades this to equality of the primes
  have hp_eq1 : e.p₁ = e'.p₁ := by
    have hdvdp2 : ¬ e.p₁ ∣ e.p₂ := by
      intro hd
      rcases (Nat.dvd_prime hp2).mp hd with h | h
      · exact hp1.ne_one h
      · exact hpne h
    have hdvd : e.p₁ ∣ e'.p₁ := by
      have : e.p₁ ∣ e.p₂ * e'.p₁ := by rw [hNM]; exact dvd_mul_left _ _
      rcases (hp1.dvd_mul).mp this with h | h
      · exact absurd h hdvdp2
      · exact h
    rcases hp1'.eq_one_or_self_of_dvd e.p₁ hdvd with h | h
    · exact absurd h hp1.ne_one
    · exact h
  have hp_eq2 : e.p₂ = e'.p₂ := by
    rw [hp_eq1] at hNM
    exact Nat.mul_right_cancel hp1'.pos hNM
  exact ⟨hp_eq1, hp_eq2⟩

end Work.N8
