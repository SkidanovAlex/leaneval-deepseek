import Mathlib
import Submission.Work.FIArea1.l51_max_cube_sum_le

namespace Work.FIArea1

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Auxiliary combinatorial facts for the positive-quarter ratio sum

The proof follows the route in the statement: the pair `(m₁,m₂)` is sent to the triple
`(g, m₁/g, m₂/g)` with `g = (m₁,m₂)`, which is injective and takes values in the box
`[1,L]³ ⊓ {g·max(a,b) ≤ L}`; the inner variable `g` is then counted exactly
(`, # {1 ≤ g ≤ L : g·M ≤ L} = L/M`), and one is left with the cubic sum
`Σ_{(a,b) ∈ [1,L]²} 1/max(a,b)³ ≤ 8`. -/

/-- `Σ_{g ∈ [1,L], g·M ≤ L} 1 ≤ L/M` for `1 ≤ M`: the admissible `g` are exactly `1 ≤ g ≤ L/M`. -/
private lemma card_filter_mul_le_div (L M : ℕ) (hM : 1 ≤ M) :
    (((Finset.Icc 1 L).filter (fun g => g * M ≤ L)).card : ℝ) ≤ (L : ℝ) / M := by
  have hMpos : 0 < M := by omega
  have hset : (Finset.Icc 1 L).filter (fun g => g * M ≤ L) = Finset.Icc 1 (L / M) := by
    ext g
    rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le hMpos).mpr h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2.trans (Nat.div_le_self L M)⟩, (Nat.le_div_iff_mul_le hMpos).mp h2⟩
  rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  exact Nat.cast_div_le

/-- The parametrisation map `(m₁,m₂) ↦ ((m₁,m₂), m₁/(m₁,m₂), m₂/(m₁,m₂))`. -/
private def redPhi (p : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (p.1.gcd p.2, p.1 / (p.1.gcd p.2), p.2 / (p.1.gcd p.2))

/-- The summand `1/max(a,b)²` read on a triple `(g,a,b)`. -/
private def redVv (q : ℕ × ℕ × ℕ) : ℝ :=
  (1 : ℝ) / (((max q.2.1 q.2.2 : ℕ) : ℝ)) ^ 2

/-- `redPhi` is injective, since `m₁ = (m₁,m₂)·(m₁/(m₁,m₂))`. -/
private lemma redPhi_inj : Function.Injective redPhi := by
  intro p q h
  simp only [redPhi, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hp1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
  have hq1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left q.1 q.2)
  have hp2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)
  have hq2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right q.1 q.2)
  have e1 : p.1 = q.1 := by
    have key : q.1.gcd q.2 * (q.1 / (q.1.gcd q.2)) = p.1 := by rw [← hp1, h2, h1]
    exact key.symm.trans hq1
  have e2 : p.2 = q.2 := by
    have key : q.1.gcd q.2 * (q.2 / (q.1.gcd q.2)) = p.2 := by rw [← hp2, h3, h1]
    exact key.symm.trans hq2
  exact Prod.ext e1 e2

/-- **The positive-quarter ratio sum.** For every `L : ℕ`,
`Σ_{1 ≤ m₁,m₂ ≤ L} 1/max(m₁/(m₁,m₂), m₂/(m₁,m₂))² ≤ 8L`.

*Route.* The map `(m₁,m₂) ↦ (g, m₁/g, m₂/g)` with `g = gcd(m₁,m₂)` is injective (since
`m₁ = g·(m₁/g)`) and lands in `G = {(g,a,b) ∈ [1,L]³ : g·max(a,b) ≤ L}` (since `g·a = m₁ ≤ L`),
so the sum is at most `Σ_{(g,a,b) ∈ G} 1/max(a,b)²`. For fixed `(a,b)` with `M = max(a,b)`, the
admissible `g` are those with `1 ≤ g ≤ L/M`, at most `L/M` many, so
`Σ_G ≤ Σ_{a,b ≤ L} (L/M)(1/M²) = L·Σ_{a,b≤L} 1/max(a,b)³`. Finally the pairs `(a,b) ∈ [1,L]²`
with `max(a,b) = m` are the `2m-1` pairs `(m,b)` (`b ≤ m`) and `(a,m)` (`a < m`), so
`Σ_{a,b} 1/max(a,b)³ = Σ_{m=1}^{L} (2m-1)/m³ ≤ 2 Σ_{m=1}^{L} 1/m² ≤ 4`
(and `Σ_{m=1}^{L} 1/m² ≤ 2`, e.g. by telescoping `1/m² ≤ 2(1/m - 1/(m+1))`). -/
theorem l51_ratio_sum_pos (L : ℕ) :
    (∑ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L),
        1 / ((max (p.1 / p.1.gcd p.2) (p.2 / p.1.gcd p.2) : ℕ) : ℝ) ^ 2)
    ≤ 8 * (L : ℝ) := by
  have hLHS : (∑ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L),
        1 / ((max (p.1 / p.1.gcd p.2) (p.2 / p.1.gcd p.2) : ℕ) : ℝ) ^ 2)
      = ∑ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L), redVv (redPhi p) := by
    apply Finset.sum_congr rfl; intro p _; rfl
  rw [hLHS]
  set T : Finset (ℕ × ℕ) := (Finset.Icc 1 L).product (Finset.Icc 1 L) with hT
  set A23 : Finset (ℕ × ℕ) := (Finset.Icc 1 L).product (Finset.Icc 1 L) with hA23
  set A : Finset (ℕ × ℕ × ℕ) := (Finset.Icc 1 L).product A23 with hA
  -- Step 1: reindex the sum over the image of `redPhi`, which is injective.
  have hS : (∑ p ∈ T, redVv (redPhi p)) = ∑ q ∈ T.image redPhi, redVv q :=
    (Finset.sum_image (redPhi_inj.injOn)).symm
  -- Step 2: the image lies in the box `A` cut by `g·max(a,b) ≤ L`.
  have hsub : T.image redPhi ⊆ A.filter
      (fun q : ℕ × ℕ × ℕ => q.1 * max q.2.1 q.2.2 ≤ L) := by
    intro q hq
    rw [hT] at hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    rw [hA, Finset.mem_filter]
    have hgp1 : 0 < p.1.gcd p.2 := Nat.gcd_pos_of_pos_left p.2 (by omega)
    have hgp_le1 : p.1.gcd p.2 ≤ p.1 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left p.1 p.2)
    have hgp_le2 : p.1.gcd p.2 ≤ p.2 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right p.1 p.2)
    have hgp_le_L : p.1.gcd p.2 ≤ L := hgp_le1.trans hp1.2
    have ha1 : 1 ≤ p.1 / p.1.gcd p.2 := Nat.div_pos hgp_le1 hgp1
    have haL : p.1 / p.1.gcd p.2 ≤ L := (Nat.div_le_self p.1 _).trans hp1.2
    have hb1 : 1 ≤ p.2 / p.1.gcd p.2 := Nat.div_pos hgp_le2 hgp1
    have hbL : p.2 / p.1.gcd p.2 ≤ L := (Nat.div_le_self p.2 _).trans hp2.2
    have hcond : p.1.gcd p.2 * max (p.1 / p.1.gcd p.2) (p.2 / p.1.gcd p.2) ≤ L := by
      rw [mul_max, Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2),
          Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)]
      exact max_le hp1.2 hp2.2
    refine ⟨?_, hcond⟩
    rw [hA23]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hgp1, hgp_le_L⟩,
        Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha1, haL⟩, Finset.mem_Icc.mpr ⟨hb1, hbL⟩⟩⟩
  have hstep1 : ∑ q ∈ T.image redPhi, redVv q
      ≤ ∑ q ∈ A.filter (fun q : ℕ × ℕ × ℕ => q.1 * max q.2.1 q.2.2 ≤ L), redVv q :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by unfold redVv; positivity)
  -- Step 3: decompose the box sum by `(a,b)`, counting the admissible `g`.
  have hdec : ∑ q ∈ A.filter (fun q : ℕ × ℕ × ℕ => q.1 * max q.2.1 q.2.2 ≤ L), redVv q
      = ∑ c ∈ A23, ((((Finset.Icc 1 L).filter (fun g => g * max c.1 c.2 ≤ L)).card : ℝ)
          * (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2)) := by
    rw [Finset.sum_filter]
    rw [hA]
    rw [show (Finset.Icc 1 L).product A23 = (Finset.Icc 1 L) ×ˢ A23 from rfl]
    rw [Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    show (∑ g ∈ Finset.Icc 1 L,
        (if g * max c.1 c.2 ≤ L then (1 : ℝ) / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2 else 0)) = _
    have hstep : ∀ g : ℕ,
        (if g * max c.1 c.2 ≤ L then (1 : ℝ) / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2 else 0)
        = (if g * max c.1 c.2 ≤ L then (1 : ℝ) else 0)
            * ((1 : ℝ) / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2) := by
      intro g; by_cases h : g * max c.1 c.2 ≤ L <;> simp [h]
    simp only [hstep]
    rw [← Finset.sum_mul, Finset.sum_boole]
  -- Step 4: bound each term by `L/M³`.
  have hbound : (∑ c ∈ A23, ((((Finset.Icc 1 L).filter (fun g => g * max c.1 c.2 ≤ L)).card : ℝ)
          * (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2)))
      ≤ (L : ℝ) * ∑ c ∈ A23, (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 3) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    rw [hA23] at hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hc
    rw [Finset.mem_Icc] at hc1 hc2
    have hM1 : 1 ≤ max c.1 c.2 := hc1.1.trans (le_max_left _ _)
    have hcard := card_filter_mul_le_div L (max c.1 c.2) hM1
    have hw : 0 ≤ (1 : ℝ) / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2 := by positivity
    calc ((((Finset.Icc 1 L).filter (fun g => g * max c.1 c.2 ≤ L)).card : ℝ)
            * (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2))
        ≤ ((L : ℝ) / (max c.1 c.2)) * (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_right hcard hw
      _ = (L : ℝ) * (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 3) := by
          have : ((max c.1 c.2 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp
  -- Step 5: the cubic sum is bounded (delegated lemma), then conclude.
  have hcube : ∑ c ∈ A23, (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 3) ≤ 8 := by
    rw [hA23]
    exact l51_max_cube_sum_le L
  calc ∑ p ∈ T, redVv (redPhi p) = ∑ q ∈ T.image redPhi, redVv q := hS
    _ ≤ ∑ q ∈ A.filter (fun q : ℕ × ℕ × ℕ => q.1 * max q.2.1 q.2.2 ≤ L), redVv q := hstep1
    _ = ∑ c ∈ A23, ((((Finset.Icc 1 L).filter (fun g => g * max c.1 c.2 ≤ L)).card : ℝ)
          * (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 2)) := hdec
    _ ≤ (L : ℝ) * ∑ c ∈ A23, (1 / (((max c.1 c.2 : ℕ) : ℝ)) ^ 3) := hbound
    _ ≤ (L : ℝ) * 8 := by gcongr
    _ = 8 * (L : ℝ) := by ring

end

end Work.FIArea1
