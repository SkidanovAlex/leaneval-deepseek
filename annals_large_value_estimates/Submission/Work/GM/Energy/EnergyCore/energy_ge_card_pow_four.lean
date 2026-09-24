import Mathlib
import Submission.Work.GM.Energy.Defs

namespace Work.GM.Energy.EnergyCore

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- Two reals whose floors agree are at distance `< 1`. -/
private lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  rw [abs_lt]
  constructor
  · have h1 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have h2 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
    rw [← h] at h2
    linarith
  · have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have h2 : x < (⌊x⌋ : ℝ) + 1 := Int.lt_floor_add_one x
    rw [h] at h2
    linarith

/-- The quadruple of coordinates of an element of `Σ k, (ℝ × ℝ) × (ℝ × ℝ)`
(suppressing the index `k := ⌊p₁ + p₂⌋`). -/
private def toQuad (r : Σ k : ℤ, (ℝ × ℝ) × (ℝ × ℝ)) : ℝ × ℝ × ℝ × ℝ :=
  (r.2.1.1, r.2.1.2, r.2.2.1, r.2.2.2)

/-- The number of distinct values of `⌊p₁ + p₂⌋`, `(p₁,p₂) ∈ W × W`, with `W ⊆ [0,T]`,
is at most `2T + 3`: each such value is an integer in `[0, 2T]`. -/
private lemma card_image_floor_le_two_mul_add (W : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) :
    (((W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋)).card : ℝ) ≤ 2 * T + 3 := by
  have hfloor_nonneg : (0 : ℤ) ≤ ⌊2 * T⌋ := Int.floor_nonneg.mpr (by linarith)
  have hsub : (W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋) ⊆ Finset.Icc (0 : ℤ) ⌊2 * T⌋ := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨p, hp, rfl⟩
    rw [Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have h1 : (0 : ℝ) ≤ p.1 + p.2 := by
      have := (hW p.1 hp1).1; have := (hW p.2 hp2).1; linarith
    have h2 : p.1 + p.2 ≤ 2 * T := by
      have := (hW p.1 hp1).2; have := (hW p.2 hp2).2; linarith
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_nonneg.mpr h1, Int.floor_mono h2⟩
  have hcard : ((W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋)).card
      ≤ ⌊2 * T⌋.toNat + 1 := by
    calc ((W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋)).card
        ≤ (Finset.Icc (0 : ℤ) ⌊2 * T⌋).card := Finset.card_le_card hsub
      _ = (⌊2 * T⌋ + 1 - 0).toNat := Int.card_Icc 0 ⌊2 * T⌋
      _ = ⌊2 * T⌋.toNat + 1 := by omega
  have hle : (⌊2 * T⌋.toNat : ℝ) ≤ 2 * T := by
    have h2 : ((⌊2 * T⌋.toNat : ℤ) : ℝ) ≤ 2 * T := by
      rw [Int.toNat_of_nonneg hfloor_nonneg]
      exact Int.floor_le (2 * T)
    exact h2
  have hcast : (((W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋)).card : ℝ)
      ≤ ((⌊2 * T⌋.toNat + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  push_cast at hcast
  linarith

/-- **The counting core.**  For the fibres of `p ↦ g p` on `Q = W × W` (where `g p`
is the floor of `p₁ + p₂`), the sum of the squares of the fibre sizes is at most the
additive energy: two pairs with equal `g`-value satisfy `|p₁ + p₂ - q₁ - q₂| < 1 ≤ 1`,
so the products of two fibres inject into the energy quadruples. -/
private lemma sum_sq_card_fiber_le_energy_aux (W : Finset ℝ) (Q : Finset (ℝ × ℝ))
    (g : ℝ × ℝ → ℤ) (s : Finset ℤ) (F : ℤ → Finset (ℝ × ℝ))
    (hQ : Q = W ×ˢ W) (hg : ∀ p, g p = ⌊p.1 + p.2⌋)
    (hF : ∀ k, F k = Q.filter (fun p => g p = k)) :
    ∑ k ∈ s, ((F k).card : ℝ) ^ 2 ≤ (Submission.GM.energy W : ℝ) := by
  classical
  set Tset : Finset (ℝ × ℝ × ℝ × ℝ) := (W ×ˢ W ×ˢ W ×ˢ W).filter
      (fun q : ℝ × ℝ × ℝ × ℝ => |q.1 + q.2.1 - q.2.2.1 - q.2.2.2| ≤ 1) with hTset
  have henergy : Submission.GM.energy W = Tset.card := by
    unfold Submission.GM.energy
    rw [hTset]
  have hsigcard : ((s.sigma (fun k => F k ×ˢ F k)).card : ℝ)
      = ∑ k ∈ s, ((F k).card : ℝ) ^ 2 := by
    rw [Finset.card_sigma]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Finset.card_product]; push_cast; ring
  rw [henergy, ← hsigcard]
  have hnat : (s.sigma (fun k => F k ×ˢ F k)).card ≤ Tset.card := by
    refine Finset.card_le_card_of_injOn toQuad ?_ ?_
    · rintro ⟨k, ⟨p, q⟩⟩ hr
      rw [Finset.mem_coe] at hr
      obtain ⟨_, hrt⟩ := Finset.mem_sigma.mp hr
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hrt
      rw [hF k] at hp hq
      obtain ⟨hpQ, hpfl⟩ := Finset.mem_filter.mp hp
      obtain ⟨hqQ, hqfl⟩ := Finset.mem_filter.mp hq
      rw [hQ] at hpQ hqQ
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpQ
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqQ
      rw [hg] at hpfl hqfl
      have hfloor : ⌊p.1 + p.2⌋ = ⌊q.1 + q.2⌋ := by rw [hpfl, hqfl]
      have hlt := abs_sub_lt_one_of_floor_eq hfloor
      rw [Finset.mem_coe, hTset, Finset.mem_filter]
      dsimp only [toQuad]
      constructor
      · rw [Finset.mem_product]
        refine ⟨hp1, ?_⟩
        rw [Finset.mem_product]
        refine ⟨hp2, ?_⟩
        rw [Finset.mem_product]
        exact ⟨hq1, hq2⟩
      · have hargs : p.1 + p.2 - q.1 - q.2 = (p.1 + p.2) - (q.1 + q.2) := by ring
        rw [hargs]
        exact le_of_lt hlt
    · rintro ⟨k, ⟨p, q⟩⟩ hr ⟨k', ⟨p', q'⟩⟩ hr' heq
      rw [Finset.mem_coe] at hr hr'
      obtain ⟨-, hrt⟩ := Finset.mem_sigma.mp hr
      obtain ⟨-, hrt'⟩ := Finset.mem_sigma.mp hr'
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hrt
      obtain ⟨hp', hq'⟩ := Finset.mem_product.mp hrt'
      have hpk : g p = k := by rw [hF k] at hp; exact (Finset.mem_filter.mp hp).2
      have hpk' : g p' = k' := by rw [hF k'] at hp'; exact (Finset.mem_filter.mp hp').2
      simp only [toQuad, Prod.mk.injEq] at heq
      obtain ⟨e1, e2, e3, e4⟩ := heq
      have hpp : p = p' := Prod.ext e1 e2
      have hqq : q = q' := Prod.ext e3 e4
      have hkk : k = k' := by rw [← hpk, ← hpk', hpp]
      subst hkk; subst hpp; subst hqq; rfl
  exact_mod_cast hnat

/-- GM (1.7) lower bound for the additive energy: for a finite set `W ⊆ [0,T]` of reals,
`|W|⁴ ≤ (2T+3) E(W)`.  Indeed the pairs of `W × W` are distributed among the at most
`2T+1` half-open unit intervals determined by `⌊p₁ + p₂⌋`, and Cauchy–Schwarz gives
`|W|⁴ ≤ (2T+3) Σ_k c_k²`, while `Σ_k c_k² ≤ E(W)`. -/
theorem energy_ge_card_pow_four (W : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) :
    (W.card : ℝ) ^ 4 ≤ (2 * T + 3) * (Submission.GM.energy W : ℝ) := by
  classical
  have hCS := sq_sum_le_card_mul_sum_sq
      (s := (W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋))
      (f := fun k : ℤ => (((W ×ˢ W).filter (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋ = k)).card : ℝ))
  have hfiber : ((W ×ˢ W).card : ℝ)
      = ∑ k ∈ (W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋),
          (((W ×ˢ W).filter (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋ = k)).card : ℝ) := by
    have hfiber_nat : (W ×ˢ W).card = ∑ k ∈ (W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋),
          ((W ×ˢ W).filter (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋ = k)).card :=
      Finset.card_eq_sum_card_image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋) (W ×ˢ W)
    rw [hfiber_nat]
    push_cast
    rfl
  have h1 : ((W ×ˢ W).card : ℝ) ^ 2
      ≤ (((W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋)).card : ℝ)
        * ∑ k ∈ (W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋),
            (((W ×ˢ W).filter (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋ = k)).card : ℝ) ^ 2 := by
    rw [hfiber]
    exact hCS
  have h2 : (((W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋)).card : ℝ) ≤ 2 * T + 3 :=
    card_image_floor_le_two_mul_add W hT hW
  have h3 : ∑ k ∈ (W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋),
        (((W ×ˢ W).filter (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋ = k)).card : ℝ) ^ 2
      ≤ (Submission.GM.energy W : ℝ) :=
    sum_sq_card_fiber_le_energy_aux W (W ×ˢ W) (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋)
      ((W ×ˢ W).image (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋))
      (fun k : ℤ => (W ×ˢ W).filter (fun p : ℝ × ℝ => ⌊p.1 + p.2⌋ = k))
      rfl (fun p => rfl) (fun k => rfl)
  have h4 : (W.card : ℝ) ^ 4 = ((W ×ˢ W).card : ℝ) ^ 2 := by
    rw [Finset.card_product]; push_cast; ring
  rw [h4]
  refine le_trans h1 ?_
  exact mul_le_mul h2 h3 (Finset.sum_nonneg (fun k _ => sq_nonneg _)) (by linarith)

end Work.GM.Energy.EnergyCore
