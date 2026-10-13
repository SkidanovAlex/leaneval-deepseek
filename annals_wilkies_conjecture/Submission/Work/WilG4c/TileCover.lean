import Mathlib
import Submission.Work.WilG4c.FLemAPI

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **Tile point.**  For a point `x` of the open cube and any `δ ∈ (0,1)`, the `1/K`-grid
tile containing `x` has a base point `j : Fin (n+1) → Fin K` and an interior point `z` of the
unit cube such that the rescaled point `j/K + z/K` again lies in the cube and is within
`δ/K` (in the sup metric) of `x`.  Coordinates where `K·x` is an integer are pushed into the
interior of the tile by `δ`. -/
lemma tile_point {n K : ℕ} (hK : 1 ≤ K) {x : Fin (n + 1) → ℝ} (hx : x ∈ openCube (n + 1))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ (j : Fin (n + 1) → Fin K) (z : Fin (n + 1) → ℝ),
      z ∈ openCube (n + 1) ∧
      (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ)) ∈ openCube (n + 1) ∧
      dist (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ)) x ≤ δ / (K : ℝ) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hx01 : ∀ b, 0 < x b ∧ x b < 1 := fun b => hx b
  let J : Fin (n + 1) → ℕ := fun b => Nat.floor ((K : ℝ) * x b)
  have hJlt : ∀ b, J b < K := by
    intro b
    have h0 : (0 : ℝ) ≤ (K : ℝ) * x b := mul_nonneg (Nat.cast_nonneg K) (le_of_lt (hx01 b).1)
    have h := (Nat.floor_lt h0).mpr (by nlinarith [(hx01 b).2, hKpos])
    simpa only [J] using h
  let j : Fin (n + 1) → Fin K := fun b => ⟨J b, hJlt b⟩
  let z : Fin (n + 1) → ℝ := fun b => max δ ((K : ℝ) * x b - (J b : ℝ))
  have hJreal : ∀ b, (J b : ℝ) = (Nat.floor ((K : ℝ) * x b) : ℝ) := fun b => by simp only [J]
  have hc_lt : ∀ b, (K : ℝ) * x b - (J b : ℝ) < 1 := by
    intro b; have h := Nat.lt_floor_add_one ((K : ℝ) * x b); rw [hJreal b]; linarith
  have hc_nonneg : ∀ b, 0 ≤ (K : ℝ) * x b - (J b : ℝ) := by
    intro b
    have h := Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (le_of_lt (hx01 b).1))
    rw [hJreal b]; linarith
  let y : Fin (n + 1) → ℝ := fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ)
  have hyb : ∀ b, y b = ((J b : ℝ) + z b) / (K : ℝ) := by
    intro b; change ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ) = ((J b : ℝ) + z b) / (K : ℝ)
    simp only [j]; ring
  have hz : z ∈ openCube (n + 1) := by
    intro b
    exact ⟨lt_of_lt_of_le hδ0 (le_max_left (δ : ℝ) ((K : ℝ) * x b - (J b : ℝ))),
           max_lt hδ1 (hc_lt b)⟩
  have hy : y ∈ openCube (n + 1) := by
    intro b
    rw [hyb b]
    constructor
    · apply div_pos
      · have : (0 : ℝ) ≤ (J b : ℝ) := Nat.cast_nonneg _
        have hzp : 0 < z b :=
          lt_of_lt_of_le hδ0 (le_max_left (δ : ℝ) ((K : ℝ) * x b - (J b : ℝ)))
        linarith
      · exact hKpos
    · rw [div_lt_one hKpos]
      have hzl : z b < 1 := max_lt hδ1 (hc_lt b)
      have hJle : (J b : ℝ) + 1 ≤ (K : ℝ) := by
        have h1 : J b + 1 ≤ K := Nat.succ_le_of_lt (hJlt b)
        exact_mod_cast h1
      linarith
  have hdist : dist y x ≤ δ / (K : ℝ) := by
    rw [dist_pi_le_iff (le_of_lt (div_pos hδ0 hKpos))]
    intro b
    rw [Real.dist_eq]
    have hyb' : y b - x b = (max (δ - ((K : ℝ) * x b - (J b : ℝ))) 0) / (K : ℝ) := by
      rw [hyb b]
      have hkey : (J b : ℝ) + z b - (K : ℝ) * x b
          = max (δ - ((K : ℝ) * x b - (J b : ℝ))) 0 := by
        have hzm : z b = max δ ((K : ℝ) * x b - (J b : ℝ)) := rfl
        rw [hzm]
        rcases le_total ((K : ℝ) * x b - (J b : ℝ)) δ with h | h
        · rw [max_eq_left h, max_eq_left (by linarith)]; ring
        · rw [max_eq_right h, max_eq_right (by linarith)]; ring
      have h2 := congrArg (fun u => u / (K : ℝ)) hkey
      rw [sub_div] at h2
      rw [mul_div_cancel_left₀ (x b) (ne_of_gt hKpos)] at h2
      exact h2
    rw [hyb', abs_div, abs_of_pos hKpos]
    apply div_le_div_of_nonneg_right _ (le_of_lt hKpos)
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [hc_nonneg b]) (le_of_lt hδ0)
  exact ⟨j, z, hz, hy, hdist⟩

theorem TileCover {k p : ℕ} (n K : ℕ) (hK : 1 ≤ K) (C : ℝ) (hC1 : 1 ≤ C)
    (hCK : C ≤ (K : ℝ)) (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1))
    (hLip : Work.WilkG4c.LipOnCube F C) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Ψ : (Fin (n + 1) → Fin K) → Finset (Work.WilkG4c.ChartTuple p (n + 1)))
    (hcov : ∀ j : Fin (n + 1) → Fin K,
      Work.WilkG4c.Covers Λ
        (fun i l z => F i l (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ))) (Ψ j) (ε / 2))
    (Φ : Finset (Work.WilkG4c.ChartTuple p (n + 1)))
    (hΦ : ∀ φ : Work.WilkG4c.ChartTuple p (n + 1), φ ∈ Φ ↔ ∃ j : Fin (n + 1) → Fin K,
      ∃ ψ ∈ Ψ j, φ = fun s l t => ((j s : ℕ) : ℝ) / (K : ℝ) + ψ s l t / (K : ℝ)) :
    Work.WilkG4c.Covers Λ F Φ ε := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  set δ : ℝ := min (1 / 2) (ε * (K : ℝ) / (4 * C)) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (by norm_num) (div_pos (mul_pos hε0 hKpos) (by positivity))
  have hδ1 : δ < 1 := by
    rw [hδdef]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδle : δ ≤ ε * (K : ℝ) / (4 * C) := by rw [hδdef]; exact min_le_right _ _
  intro l hl x hx
  obtain ⟨j, z, hz, hy, hdist⟩ := tile_point hK hx δ hδ0 hδ1
  obtain ⟨ψ, hψ, t, ht, hpt⟩ := hcov j l hl z hz
  let φ : Work.WilkG4c.ChartTuple p (n + 1) :=
    fun s l t => ((j s : ℕ) : ℝ) / (K : ℝ) + ψ s l t / (K : ℝ)
  have hφmem : φ ∈ Φ := (hΦ φ).mpr ⟨j, ψ, hψ, rfl⟩
  refine ⟨φ, hφmem, t, ht, fun i => ?_⟩
  have hfirst : |F i l (fun s => φ s l t)
      - F i l (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ))| < ε / 2 := hpt i
  have hsecond :
      |F i l (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ)) - F i l x| < ε / 2 := by
    have h1 : |F i l (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ)) - F i l x| ≤
        C * dist (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ)) x := hLip i l _ x hy hx
    have h2 : C * dist (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ)) x < ε / 2 := by
      have h3 : C * dist (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ)) x
          ≤ C * (δ / (K : ℝ)) := mul_le_mul_of_nonneg_left hdist (le_of_lt hCpos)
      have h4 : C * (δ / (K : ℝ)) ≤ ε / 4 := by
        have hk : δ / (K : ℝ) ≤ (ε * (K : ℝ) / (4 * C)) / (K : ℝ) :=
          div_le_div_of_nonneg_right hδle (le_of_lt hKpos)
        have h5 : C * (δ / (K : ℝ)) ≤ C * ((ε * (K : ℝ) / (4 * C)) / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left hk (le_of_lt hCpos)
        have h6 : C * ((ε * (K : ℝ) / (4 * C)) / (K : ℝ)) = ε / 4 := by
          field_simp
        linarith
      linarith
    linarith
  have hb := abs_sub_le (F i l (fun s => φ s l t))
    (F i l (fun b => ((j b : ℕ) : ℝ) / (K : ℝ) + z b / (K : ℝ))) (F i l x)
  linarith

end Work.WilG4c
