import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Elementary arithmetic step of the `γ`-bound: from `x·H ≤ 2^v σ`, `λ ≤ D/(r d σ)`,
`1 ≤ d·H` (i.e. `H ≥ 1/d`), `0 < d`, `0 < σ`, `0 ≤ D`, conclude `x·λ ≤ 2^v D / r`.
This is BH's row bound `∑ᵢ |L j i| h'(αᵢ) ≤ 2^v σ_j` combined with `λᵢ ≤ Dᵢ ≤ D/(r d σᵢ)`. -/
private lemma gam_arith {r d : ℝ} {v : ℕ} (x H σ l D : ℝ)
    (hr : 0 < r) (hd : 0 < d) (hH : 1 ≤ d * H) (hσ : 0 < σ) (hD : 0 ≤ D)
    (hl : 0 ≤ l) (h1 : x * H ≤ (2:ℝ)^v * σ) (h2 : l ≤ D / (r * d * σ)) :
    x * l ≤ (2:ℝ)^v * D / r := by
  have hHpos : 0 < H := by nlinarith
  have hx' : x ≤ (2:ℝ)^v * σ / H := by
    rw [le_div_iff₀ hHpos]; exact h1
  have hstep : x * l ≤ ((2:ℝ)^v * σ / H) * (D / (r * d * σ)) :=
    mul_le_mul hx' h2 hl (by positivity)
  have heq : ((2:ℝ)^v * σ / H) * (D / (r * d * σ)) = (2:ℝ)^v * D / (H * r * d) := by
    field_simp
  rw [heq] at hstep
  refine le_trans hstep ?_
  apply div_le_div_of_nonneg_left (by positivity) hr
  nlinarith [hH, hr, mul_le_mul_of_nonneg_left hH (le_of_lt hr)]

/-- `|bᵢ| ≤ e^{h'(L)}` for every coefficient of a primitive vector, from `hL b d = max(log max|bᵢ|, 1/d)`. -/
private lemma abs_b_le_exp_hL {n : ℕ} (b : Fin n → ℤ) (d : ℕ) (i : Fin n) :
    |(b i : ℝ)| ≤ Real.exp (hL b d) := by
  set s := Finset.univ.sup (fun i => (b i).natAbs) with hs
  have h1 : (b i).natAbs ≤ s := by
    rw [hs]; exact Finset.le_sup (f := fun i => (b i).natAbs) (Finset.mem_univ i)
  have hcast : |(b i : ℝ)| = ((b i).natAbs : ℝ) :=
    ((Nat.cast_natAbs (α := ℝ) (b i)).trans Int.cast_abs).symm
  have hlog : Real.log (s : ℝ) ≤ hL b d := by
    rw [hL, ← hs]; exact le_max_left _ _
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · have : (b i).natAbs = 0 := Nat.eq_zero_of_le_zero (hs0 ▸ h1)
    rw [hcast, this, Nat.cast_zero]
    exact Real.exp_nonneg _
  · have hsposR : (0:ℝ) < s := by exact_mod_cast hspos
    rw [hcast]
    calc ((b i).natAbs : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1
      _ = Real.exp (Real.log (s:ℝ)) := (Real.exp_log hsposR).symm
      _ ≤ Real.exp (hL b d) := Real.exp_le_exp.mpr hlog

/-- Bound on `γ_m = ∑ᵢ (b_k L_{i,ιm} − b_{ιm} L_{i,k}) · λᵢ` for `λᵢ ≤ Dᵢ = pDj r d σ i`:
`|γ| ≤ 2 e^{h'(L)} 2^v · D`. -/
theorem gamInt_abs_le {K : Type*} [Field K] [NumberField K] {n r : ℕ}
    (φ : K →+* ℂ) (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (v : ℕ) (c : ℝ)
    (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (ι : Fin (r - 1) → Fin n) (m : Fin (r - 1))
    (lm : (j : Fin r) → Fin (pDj r (Module.finrank ℚ K) σ j + 1)) :
    |((gamInt b k L (ι m) (fun i => (lm i : ℕ)) : ℤ) : ℝ)|
      ≤ 2 * Real.exp (hL b (Module.finrank ℚ K)) * (2 : ℝ) ^ v
          * pD r (Module.finrank ℚ K) σ := by
  obtain ⟨-, -, -, -, hσpos, -, hσrow, -⟩ := hBH
  set D := pD r (Module.finrank ℚ K) σ with hDdef
  have hdpos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    have h := Module.finrank_pos (R := ℚ) (M := K); exact_mod_cast h
  have hr2 : 2 ≤ r := by have := m.isLt; omega
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hDnn : 0 ≤ D := by
    rw [hDdef, pD]
    have hlog : 0 ≤ Real.log (2 * (r : ℝ) * (Module.finrank ℚ K : ℝ)) := by
      apply Real.log_nonneg
      have h1 : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      have h2 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
        have h := Module.finrank_pos (R := ℚ) (M := K); exact_mod_cast h
      nlinarith
    have hprod : 0 ≤ ∏ j, σ j := Finset.prod_nonneg (fun j _ => le_of_lt (hσpos j))
    have h2r : (0:ℝ) ≤ (r:ℝ) := by positivity
    have h32 : (0:ℝ) ≤ 32 * (Module.finrank ℚ K : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h2r _))
      (pow_nonneg h32 _)) hlog) hprod
  have hHpos : ∀ c : Fin n, 0 < BakerWustholz.modifiedHeight φ (α c) := by
    intro c
    have h1 : 1 / (Module.finrank ℚ K : ℝ) ≤ BakerWustholz.modifiedHeight φ (α c) := by
      simp only [BakerWustholz.modifiedHeight]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have h2 : 0 < 1 / (Module.finrank ℚ K : ℝ) := one_div_pos.mpr hdpos
    linarith
  have hHge : ∀ c : Fin n, (1:ℝ) ≤ (Module.finrank ℚ K : ℝ) * BakerWustholz.modifiedHeight φ (α c) := by
    intro c
    have h1 : 1 / (Module.finrank ℚ K : ℝ) ≤ BakerWustholz.modifiedHeight φ (α c) := by
      simp only [BakerWustholz.modifiedHeight]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have h2 := (div_le_iff₀ hdpos).mp h1
    simpa [mul_comm] using h2
  have hrow : ∀ (i : Fin r) (cc : Fin n),
      |(L i cc : ℝ)| * BakerWustholz.modifiedHeight φ (α cc) ≤ (2:ℝ)^v * σ i := by
    intro i cc
    refine le_trans (Finset.single_le_sum
      (f := fun cc => |(L i cc : ℝ)| * BakerWustholz.modifiedHeight φ (α cc))
      (fun cc _ => mul_nonneg (abs_nonneg _) (le_of_lt (hHpos cc))) (Finset.mem_univ cc)) ?_
    simpa using hσrow i
  have hfloor : ∀ i : Fin r, ((lm i : ℕ) : ℝ)
      ≤ D / (r * (Module.finrank ℚ K : ℝ) * σ i) := by
    intro i
    have hle : (lm i : ℕ) ≤ pDj r (Module.finrank ℚ K) σ i := by
      have := (lm i).isLt; omega
    have hcast : ((lm i : ℕ) : ℝ) ≤ ((pDj r (Module.finrank ℚ K) σ i : ℕ) : ℝ) := by
      exact_mod_cast hle
    refine le_trans hcast ?_
    rw [pDj, ← hDdef]
    apply Nat.floor_le
    exact div_nonneg hDnn (mul_nonneg (mul_nonneg (le_of_lt hrpos) (le_of_lt hdpos)) (le_of_lt (hσpos i)))
  have hperC : ∀ (i : Fin r) (cc : Fin n),
      |(L i cc : ℝ)| * ((lm i : ℕ) : ℝ) ≤ (2:ℝ)^v * D / r := by
    intro i cc
    exact gam_arith (x := |(L i cc : ℝ)|) (H := BakerWustholz.modifiedHeight φ (α cc))
      (σ := σ i) (l := ((lm i : ℕ) : ℝ)) (D := D) hrpos hdpos (hHge cc) (hσpos i) hDnn
      (Nat.cast_nonneg _) (hrow i cc) (hfloor i)
  have htri : |((gamInt b k L (ι m) (fun i => (lm i : ℕ)) : ℤ) : ℝ)|
      ≤ ∑ i : Fin r, (|(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)|) * ((lm i : ℕ) : ℝ) := by
    rw [show ((gamInt b k L (ι m) (fun i => (lm i : ℕ)) : ℤ) : ℝ)
        = ∑ i : Fin r, ((derVec b k L (ι m) i : ℤ) : ℝ) * ((lm i : ℕ) : ℝ) by
          simp only [gamInt, Int.cast_sum, Int.cast_mul, Int.cast_natCast]]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    have hA : |((derVec b k L (ι m) i : ℤ) : ℝ)|
        ≤ |(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)| := by
      have hcast : ((derVec b k L (ι m) i : ℤ) : ℝ)
          = (b k : ℝ) * (L i (ι m) : ℝ) - (b (ι m) : ℝ) * (L i k : ℝ) := by
        simp only [derVec, Int.cast_sub, Int.cast_mul]
      rw [hcast]
      calc |(b k : ℝ) * (L i (ι m) : ℝ) - (b (ι m) : ℝ) * (L i k : ℝ)|
          ≤ |(b k : ℝ) * (L i (ι m) : ℝ)| + |(b (ι m) : ℝ) * (L i k : ℝ)| := abs_sub _ _
        _ = |(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)| := by rw [abs_mul, abs_mul]
    calc |((derVec b k L (ι m) i : ℤ) : ℝ) * ((lm i : ℕ) : ℝ)|
        = |((derVec b k L (ι m) i : ℤ) : ℝ)| * ((lm i : ℕ) : ℝ) := by
          have hlem : |((lm i : ℕ) : ℝ)| = ((lm i : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg (lm i))
          rw [abs_mul, hlem]
      _ ≤ (|(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)|) * ((lm i : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg _)
  have hsum : ∑ i : Fin r, (|(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)|) * ((lm i : ℕ) : ℝ)
      ≤ 2 * Real.exp (hL b (Module.finrank ℚ K)) * (2:ℝ)^v * D := by
    have hbnd : ∀ i : Fin r,
        (|(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)|) * ((lm i : ℕ) : ℝ)
        ≤ (|(b k : ℝ)| + |(b (ι m) : ℝ)|) * ((2:ℝ)^v * D / r) := by
      intro i
      have h1 := hperC i (ι m)
      have h2 := hperC i k
      calc (|(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)|) * ((lm i : ℕ) : ℝ)
          = |(b k : ℝ)| * (|(L i (ι m) : ℝ)| * ((lm i : ℕ) : ℝ))
            + |(b (ι m) : ℝ)| * (|(L i k : ℝ)| * ((lm i : ℕ) : ℝ)) := by ring
        _ ≤ |(b k : ℝ)| * ((2:ℝ)^v * D / r) + |(b (ι m) : ℝ)| * ((2:ℝ)^v * D / r) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
                (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
        _ = (|(b k : ℝ)| + |(b (ι m) : ℝ)|) * ((2:ℝ)^v * D / r) := by ring
    calc ∑ i : Fin r, (|(b k : ℝ)| * |(L i (ι m) : ℝ)| + |(b (ι m) : ℝ)| * |(L i k : ℝ)|) * ((lm i : ℕ) : ℝ)
        ≤ ∑ i : Fin r, (|(b k : ℝ)| + |(b (ι m) : ℝ)|) * ((2:ℝ)^v * D / r) :=
          Finset.sum_le_sum (fun i _ => hbnd i)
      _ = (r : ℝ) * ((|(b k : ℝ)| + |(b (ι m) : ℝ)|) * ((2:ℝ)^v * D / r)) := by
          rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = (|(b k : ℝ)| + |(b (ι m) : ℝ)|) * ((2:ℝ)^v * D) := by field_simp
      _ ≤ 2 * Real.exp (hL b (Module.finrank ℚ K)) * (2:ℝ)^v * D := by
          have hb1 := abs_b_le_exp_hL b (Module.finrank ℚ K) k
          have hb2 := abs_b_le_exp_hL b (Module.finrank ℚ K) (ι m)
          have hAB : |(b k : ℝ)| + |(b (ι m) : ℝ)| ≤ 2 * Real.exp (hL b (Module.finrank ℚ K)) := by linarith
          have h2vD : 0 ≤ (2:ℝ)^v * D := mul_nonneg (by positivity) hDnn
          calc (|(b k : ℝ)| + |(b (ι m) : ℝ)|) * ((2:ℝ)^v * D)
              ≤ (2 * Real.exp (hL b (Module.finrank ℚ K))) * ((2:ℝ)^v * D) :=
                mul_le_mul_of_nonneg_right hAB h2vD
            _ = 2 * Real.exp (hL b (Module.finrank ℚ K)) * (2:ℝ)^v * D := by ring
  exact le_trans htri hsum

end Work.BW
