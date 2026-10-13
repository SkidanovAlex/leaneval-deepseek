import Mathlib

namespace Work.WilC4

open Set

/-- The "piecewise monotone with at most `P` breakpoints" hypothesis: there is a finite set `B`
of at most `P` points such that `G` is monotone or antitone on every open interval disjoint
from `B`. -/
def PieceMono (G : ℝ → ℝ) (P : ℕ) : Prop :=
  ∃ B : Finset ℝ, B.card ≤ P ∧ ∀ a b : ℝ, a < b →
    (∀ x ∈ Set.Ioo a b, x ∉ B) →
    (MonotoneOn G (Set.Ioo a b) ∨ AntitoneOn G (Set.Ioo a b))

/-- The *localised* piecewise-monotonicity hypothesis: the finite breakpoint set witnesses
monotonicity only on intervals contained in `[1, β]`. -/
def PieceMonoOn (G : ℝ → ℝ) (P : ℕ) (β : ℝ) : Prop :=
  ∃ B : Finset ℝ, B.card ≤ P ∧ ∀ a b : ℝ, 1 ≤ a → b ≤ β → a < b →
    (∀ x ∈ Set.Ioo a b, x ∉ B) →
    (MonotoneOn G (Set.Ioo a b) ∨ AntitoneOn G (Set.Ioo a b))

lemma PieceMono.toOn {G : ℝ → ℝ} {P : ℕ} {β : ℝ} (h : PieceMono G P) :
    PieceMonoOn G P β := by
  obtain ⟨B, hc, hB⟩ := h
  exact ⟨B, hc, fun a b _ _ hab hfree => hB a b hab hfree⟩

/-- The reciprocal of a function that is locally piecewise monotone and positive on `[1, β]`
is again locally piecewise monotone (with the *same* breakpoint set). -/
lemma PieceMonoOn.inv {G : ℝ → ℝ} {P : ℕ} {β : ℝ} (h : PieceMonoOn G P β)
    (hpos : ∀ s ∈ Set.Icc 1 β, 0 < G s) :
    PieceMonoOn (fun s => (G s)⁻¹) P β := by
  obtain ⟨B, hc, hB⟩ := h
  refine ⟨B, hc, fun a b ha hb hab hfree => ?_⟩
  have hpos' : ∀ x ∈ Set.Ioo a b, 0 < G x :=
    fun x hx => hpos x ⟨le_trans ha hx.1.le, le_trans hx.2.le hb⟩
  rcases hB a b ha hb hab hfree with hm | ha'
  · right
    intro x hx y hy hxy
    exact (inv_le_inv₀ (hpos' y hy) (hpos' x hx)).mpr (hm hx hy hxy)
  · left
    intro x hx y hy hxy
    exact (inv_le_inv₀ (hpos' x hx) (hpos' y hy)).mpr (ha' hx hy hxy)

/-- **Dyadic chain bound.**  If `G` satisfies the approximate functional equation
`G (2 s) ≈ ρ · G s` (within `τ`) on `[1, β/2]`, and is positive on `[1, β]`, then for `t ≥ 1`
with `2 ^ j * t ≤ β` we have the two-sided bound
`(ρ - τ) ^ j * G t ≤ G (2 ^ j * t) ≤ (ρ + τ) ^ j * G t`. -/
lemma chain_bound (G : ℝ → ℝ) (ρ τ β : ℝ) (hτ : 0 ≤ τ) (hτρ : τ ≤ ρ)
    (hpos : ∀ s ∈ Set.Icc 1 β, 0 < G s)
    (hG : ∀ s ∈ Set.Icc 1 (β / 2), |G (2 * s) / G s - ρ| ≤ τ) :
    ∀ (j : ℕ) (t : ℝ), 1 ≤ t → (2 : ℝ) ^ j * t ≤ β →
      (ρ - τ) ^ j * G t ≤ G ((2 : ℝ) ^ j * t) ∧
        G ((2 : ℝ) ^ j * t) ≤ (ρ + τ) ^ j * G t := by
  intro j
  induction j with
  | zero =>
      intro t ht _
      simp
  | succ j ih =>
      intro t ht hle
      have ht0 : 0 ≤ t := le_trans zero_le_one ht
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hs1 : 1 ≤ (2 : ℝ) ^ j * t := by
        have := mul_le_mul_of_nonneg_right h1 ht0
        linarith
      have h2eq : (2 : ℝ) ^ (j + 1) * t = 2 * ((2 : ℝ) ^ j * t) := by
        rw [pow_succ]; ring
      have hsβ : (2 : ℝ) ^ j * t ≤ β / 2 := by
        have : 2 * ((2 : ℝ) ^ j * t) ≤ β := by rw [h2eq] at hle; exact hle
        linarith
      have hsmem1 : (2 : ℝ) ^ j * t ∈ Set.Icc 1 β := ⟨hs1, by linarith⟩
      have hGs : 0 < G ((2 : ℝ) ^ j * t) := hpos _ hsmem1
      have hrel := hG ((2 : ℝ) ^ j * t) ⟨hs1, hsβ⟩
      rw [abs_le] at hrel
      obtain ⟨hlo, hhi⟩ := hrel
      have hlo0 : ρ - τ ≤ G (2 * ((2 : ℝ) ^ j * t)) / G ((2 : ℝ) ^ j * t) := by linarith
      have hhi0 : G (2 * ((2 : ℝ) ^ j * t)) / G ((2 : ℝ) ^ j * t) ≤ ρ + τ := by linarith
      have hlo' : (ρ - τ) * G ((2 : ℝ) ^ j * t) ≤ G (2 * ((2 : ℝ) ^ j * t)) := by
        have := (le_div_iff₀ hGs).mp hlo0; linarith
      have hhi' : G (2 * ((2 : ℝ) ^ j * t)) ≤ (ρ + τ) * G ((2 : ℝ) ^ j * t) := by
        have := (div_le_iff₀ hGs).mp hhi0; linarith
      have hle' : (2 : ℝ) ^ j * t ≤ β := by
        have hpos2 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
        nlinarith [hle, ht0, hpos2, h2eq]
      obtain ⟨ihlo, ihhi⟩ := ih t ht hle'
      have hnt : 0 ≤ ρ - τ := by linarith
      have hpt : 0 ≤ ρ + τ := by linarith
      refine ⟨?_, ?_⟩
      · rw [h2eq, pow_succ]
        calc (ρ - τ) ^ j * (ρ - τ) * G t
            = (ρ - τ) * ((ρ - τ) ^ j * G t) := by ring
          _ ≤ (ρ - τ) * G ((2 : ℝ) ^ j * t) := mul_le_mul_of_nonneg_left ihlo hnt
          _ ≤ G (2 * ((2 : ℝ) ^ j * t)) := hlo'
      · rw [h2eq, pow_succ]
        calc G (2 * ((2 : ℝ) ^ j * t))
            ≤ (ρ + τ) * G ((2 : ℝ) ^ j * t) := hhi'
          _ ≤ (ρ + τ) * ((ρ + τ) ^ j * G t) := mul_le_mul_of_nonneg_left ihhi hpt
          _ = (ρ + τ) ^ j * (ρ + τ) * G t := by ring

end Work.WilC4
