import Submission.DS.Truncate
import Submission.DS.Summability

open scoped Nat ENNReal NNReal
open Set
open DuffinSchaefferConjecture

/-!
# Divergence is preserved by the truncation `ψ ↦ min ψ (1/2)`

Paper §2, Case 2, opening step: if `ψ(q) ≥ 1/2` for only finitely many `q`, then
replacing `ψ` by `min ψ (1/2)` does not change the total `∑ ψ*(q)`.  Truncation only
changes `ψ(n)` for the finitely many `n` with `ψ(n) > 1/2`, hence only changes
`ψ*(q) = φ(q) · sup {ψ(n)/n : q ∣ n}` for the finitely many `q` dividing such an `n`;
altering finitely many finite terms cannot turn a divergent extended sum into a
convergent one.
-/

namespace Submission.DS

/-- NNReal: `a / d ≤ a` when `1 ≤ d`. -/
lemma nn_div_le_self {a d : NNReal} (hd : 1 ≤ d) : a / d ≤ a := by
  have hR : ((a / d : NNReal) : ℝ) ≤ (a : ℝ) := by
    rw [NNReal.coe_div]
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    rw [div_le_iff₀ hd0]
    calc
      (a : ℝ) = (a : ℝ) * 1 := by ring
      _ ≤ (a : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_left hdR (by positivity)
  exact_mod_cast hR

/-- NNReal: if `a ≤ 1/2` then `a / d ≤ 1/2` when `1 ≤ d`. -/
lemma nn_div_le_half {a d : NNReal} (ha : a ≤ 1 / 2) (hd : 1 ≤ d) : a / d ≤ 1 / 2 := by
  have hR : ((a / d : NNReal) : ℝ) ≤ ((1 / 2 : NNReal) : ℝ) := by
    rw [NNReal.coe_div]
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hd)
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have haR : (a : ℝ) ≤ (1 / 2 : ℝ) := by exact_mod_cast ha
    calc
      (a : ℝ) / (d : ℝ) ≤ (1 / 2 : ℝ) / (d : ℝ) := div_le_div_of_nonneg_right haR (le_of_lt hd0)
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hd0]
        nlinarith [hdR]
  exact_mod_cast hR

/-- The set of `q` dividing a member of `bigQ ψ`. -/
def divSet (ψ : ℕ+ → ℝ≥0) : Set ℕ+ := {q : ℕ+ | ∃ n : ℕ+, n ∈ bigQ ψ ∧ q ∣ n}

lemma divisor_finite (n : ℕ+) : ({q : ℕ+ | q ∣ n}).Finite := by
  let s : Set ℕ+ := {q : ℕ+ | (q : ℕ) ≤ (n : ℕ)}
  have hsub : {q : ℕ+ | q ∣ n} ⊆ s := by
    intro q hq
    have hqN : (q : ℕ) ∣ (n : ℕ) := (PNat.dvd_iff).mp hq
    exact Nat.le_of_dvd n.2 hqN
  have himg : ((fun q : ℕ+ => (q : ℕ)) '' s) ⊆ Set.Icc 0 (n : ℕ) := by
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    exact ⟨Nat.zero_le (q : ℕ), by simpa [s] using hq⟩
  have hfinImg : ((fun q : ℕ+ => (q : ℕ)) '' s).Finite :=
    (Set.finite_Icc 0 (n : ℕ)).subset himg
  have hs : s.Finite :=
    (Set.finite_image_iff (Set.injOn_of_injective PNat.coe_injective (s := s))).1 hfinImg
  exact hs.subset hsub

lemma divSet_finite (ψ : ℕ+ → ℝ≥0) (hFin : (bigQ ψ).Finite) : (divSet ψ).Finite := by
  have hEq : divSet ψ = ⋃ n ∈ bigQ ψ, {q : ℕ+ | q ∣ n} := by
    ext q
    constructor <;> intro hq
    · rcases hq with ⟨n, hn, hdvd⟩
      exact Set.mem_iUnion₂.mpr ⟨n, hn, hdvd⟩
    · rcases Set.mem_iUnion₂.mp hq with ⟨n, hn, hdvd⟩
      exact ⟨n, hn, hdvd⟩
  rw [hEq]
  exact hFin.biUnion (fun n _hn => divisor_finite n)

/-- A denominator outside `bigQ` is untouched by the truncation. -/
lemma psiHalf_eq_of_not_mem_bigQ {ψ : ℕ+ → ℝ≥0} {n : ℕ+} (hn : n ∉ bigQ ψ) :
    psiHalf ψ n = ψ n := by
  have hlt : ψ n < (1 / 2 : ℝ≥0) := lt_of_not_ge hn
  exact psiHalf_of_le_half (le_of_lt hlt)

/-- Truncation leaves `ψ*(q)` unchanged for `q` dividing no large value. -/
lemma psiStar_eq_of_not_mem_divSet (ψ : ℕ+ → ℝ≥0) {q : ℕ+} (hq : q ∉ divSet ψ) :
    ψ_star (psiHalf ψ) q = ψ_star ψ q := by
  have hrad : rad (psiHalf ψ) q = rad ψ q := by
    unfold rad
    congr 1
    apply Set.Subset.antisymm
    · intro r hr
      rcases hr with ⟨n, hdvd, hrfl⟩
      have hnot : n ∉ bigQ ψ := by
        intro hn
        exact hq ⟨n, hn, hdvd⟩
      refine ⟨n, hdvd, ?_⟩
      have hh : psiHalf ψ n = ψ n := psiHalf_eq_of_not_mem_bigQ hnot
      rw [hrfl, hh]
    · intro r hr
      rcases hr with ⟨n, hdvd, hrfl⟩
      have hnot : n ∉ bigQ ψ := by
        intro hn
        exact hq ⟨n, hn, hdvd⟩
      refine ⟨n, hdvd, ?_⟩
      have hh : psiHalf ψ n = ψ n := psiHalf_eq_of_not_mem_bigQ hnot
      rw [hrfl, ← hh]
  rw [psiStar_eq_phi_mul_rad, psiStar_eq_phi_mul_rad]
  rw [hrad]

/-- Under Case 2 (`bigQ` finite) every sup-radius is finite. -/
lemma rad_lt_top_of_bigQ_finite (ψ : ℕ+ → ℝ≥0) (hFin : (bigQ ψ).Finite) (q : ℕ+) :
    rad ψ q < ∞ := by
  have himg : ((fun n : ℕ+ => ψ n) '' bigQ ψ).Finite := hFin.image ψ
  rcases himg.bddAbove with ⟨B, hB⟩
  let C : NNReal := max B (1 / 2)
  have hleB : B ≤ C := by exact le_max_left B (1 / 2)
  have hleHalf : (1 / 2 : NNReal) ≤ C := by exact le_max_right B (1 / 2)
  have honeE : ∀ n : ℕ+, (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    intro n
    exact_mod_cast (show 1 ≤ (n : ℕ) from n.2)
  have hval_le_self : ∀ n : ℕ+, (ψ n : ℝ≥0∞) / (n : ℝ≥0∞) ≤ (ψ n : ℝ≥0∞) := by
    intro n
    apply ENNReal.div_le_of_le_mul
    calc
      (ψ n : ℝ≥0∞) = (ψ n : ℝ≥0∞) * 1 := by simp
      _ ≤ (ψ n : ℝ≥0∞) * (n : ℝ≥0∞) := mul_le_mul' le_rfl (honeE n)
  have hbound : ∀ n : ℕ+, q ∣ n → (ψ n : ℝ≥0∞) / (n : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
    intro n hdvd
    by_cases hn : n ∈ bigQ ψ
    · have hψnB : ψ n ≤ B := hB ⟨n, hn, rfl⟩
      have h2 : (ψ n : ℝ≥0∞) ≤ (C : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr (le_trans hψnB hleB)
      exact le_trans (hval_le_self n) h2
    · have hlt : ψ n < (1 / 2 : ℝ≥0) := lt_of_not_ge hn
      have h2 : (ψ n : ℝ≥0∞) ≤ (C : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr (le_trans (le_of_lt hlt) hleHalf)
      exact le_trans (hval_le_self n) h2
  have hle : rad ψ q ≤ (C : ℝ≥0∞) := by
    unfold rad
    apply sSup_le
    intro y hy
    rcases hy with ⟨n, hdvd, hrfl⟩
    rw [hrfl]
    exact hbound n hdvd
  exact lt_of_le_of_lt hle (ENNReal.coe_lt_top)

/-- `ψ*(q)` is finite for all `q` under Case 2. -/
lemma psiStar_lt_top_of_bigQ_finite (ψ : ℕ+ → ℝ≥0) (hFin : (bigQ ψ).Finite) (q : ℕ+) :
    ψ_star ψ q < ∞ := by
  rw [psiStar_eq_phi_mul_rad]
  have hφ : ((φ (q : ℕ) : ℕ) : ℝ≥0∞) < ∞ := by
    simpa using ENNReal.natCast_lt_top (φ (q : ℕ))
  exact ENNReal.mul_lt_top hφ (rad_lt_top_of_bigQ_finite ψ hFin q)

/-- The sup-radius of the truncated function is bounded by `1/2`. -/
lemma rad_half_lt_top (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : rad (psiHalf ψ) q < ∞ := by
  have hval_le : ∀ n : ℕ+, q ∣ n → ((psiHalf ψ n : ℝ≥0∞) / (n : ℝ≥0∞)) ≤
      ((1 / 2 : NNReal) : ℝ≥0∞) := by
    intro n hdvd
    have h1 : (psiHalf ψ n : ℝ≥0∞) / (n : ℝ≥0∞) ≤ (psiHalf ψ n : ℝ≥0∞) := by
      apply ENNReal.div_le_of_le_mul
      calc
        (psiHalf ψ n : ℝ≥0∞) = (psiHalf ψ n : ℝ≥0∞) * 1 := by simp
        _ ≤ (psiHalf ψ n : ℝ≥0∞) * (n : ℝ≥0∞) := by
          exact mul_le_mul' le_rfl (by
            exact_mod_cast (show 1 ≤ (n : ℕ) from n.2))
    have h2 : (psiHalf ψ n : ℝ≥0∞) ≤ ((1 / 2 : NNReal) : ℝ≥0∞) :=
      ENNReal.coe_le_coe.mpr (psiHalf_le_half ψ n)
    exact le_trans h1 h2
  have hle : rad (psiHalf ψ) q ≤ ((1 / 2 : NNReal) : ℝ≥0∞) := by
    unfold rad
    apply sSup_le
    intro y hy
    rcases hy with ⟨n, hdvd, hrfl⟩
    rw [hrfl]
    exact hval_le n hdvd
  exact lt_of_le_of_lt hle ENNReal.coe_lt_top

/-- `ψ*(min ψ 1/2)(q)` is finite for all `q`. -/
lemma psiStarHalf_lt_top (ψ : ℕ+ → ℝ≥0) (q : ℕ+) : ψ_star (psiHalf ψ) q < ∞ := by
  rw [psiStar_eq_phi_mul_rad]
  have hφ : ((φ (q : ℕ) : ℕ) : ℝ≥0∞) < ∞ := by
    simpa using ENNReal.natCast_lt_top (φ (q : ℕ))
  exact ENNReal.mul_lt_top hφ (rad_half_lt_top ψ q)

/-- A divergent extended sum stays divergent when finitely many finite terms are changed. -/
lemma tsum_eq_top_of_finite_diff {f g : ℕ+ → ℝ≥0∞} (D : Set ℕ+) (hD : D.Finite)
    (hagree : ∀ q, q ∉ D → f q = g q)
    (hfD : ∀ q, q ∈ D → f q < ∞) (_hgD : ∀ q, q ∈ D → g q < ∞)
    (hfTop : (∑' q : ℕ+, f q) = ∞) : (∑' q : ℕ+, g q) = ∞ := by
  classical
  let s : Finset ℕ+ := hD.toFinset
  have hsD : ∀ q : ℕ+, q ∈ s ↔ q ∈ D := fun q => hD.mem_toFinset
  let fD : ℕ+ → ℝ≥0∞ := fun q => if q ∈ s then f q else 0
  let fC : ℕ+ → ℝ≥0∞ := fun q => if q ∈ s then 0 else f q
  let gD : ℕ+ → ℝ≥0∞ := fun q => if q ∈ s then g q else 0
  let gC : ℕ+ → ℝ≥0∞ := fun q => if q ∈ s then 0 else g q
  have hf_split : ∀ q, f q = fD q + fC q := by
    intro q
    by_cases hq : q ∈ s
    · simp [fD, fC, hq]
    · simp [fD, fC, hq]
  have hg_split : ∀ q, g q = gD q + gC q := by
    intro q
    by_cases hq : q ∈ s
    · simp [gD, gC, hq]
    · simp [gD, gC, hq]
  have hC : fC = gC := by
    funext q
    by_cases hq : q ∈ s
    · simp [fC, gC, hq]
    · have hqD : q ∉ D := by
        intro hd
        exact hq ((hsD q).2 hd)
      simp [fC, gC, hq, hagree q hqD]
  have hsumf : (∑' q : ℕ+, f q) = (∑' q : ℕ+, fD q) + (∑' q : ℕ+, fC q) := by
    calc
      (∑' q : ℕ+, f q) = ∑' q : ℕ+, (fD q + fC q) := by simp [hf_split]
      _ = (∑' q : ℕ+, fD q) + (∑' q : ℕ+, fC q) := by rw [ENNReal.tsum_add]
  have hsumg : (∑' q : ℕ+, g q) = (∑' q : ℕ+, gD q) + (∑' q : ℕ+, gC q) := by
    calc
      (∑' q : ℕ+, g q) = ∑' q : ℕ+, (gD q + gC q) := by simp [hg_split]
      _ = (∑' q : ℕ+, gD q) + (∑' q : ℕ+, gC q) := by rw [ENNReal.tsum_add]
  have hSf : (∑' q : ℕ+, fD q) < ∞ := by
    have hfin := tsum_eq_sum (L := SummationFilter.unconditional (β := ℕ+)) (f := fD) (s := s) (by intro q hq; simp [fD, hq])
    rw [hfin]
    exact (ENNReal.sum_lt_top).2 (by
      intro q hq
      have hqD : q ∈ D := (hsD q).1 hq
      have hfq : fD q = f q := by simp [fD, hq]
      simpa [hfq] using hfD q hqD)
  have hR : (∑' q : ℕ+, fC q) = ∞ := by
    have hEq : (∑' q : ℕ+, fD q) + (∑' q : ℕ+, fC q) = ⊤ := by
      rwa [← hsumf]
    exact (ENNReal.add_eq_top.mp hEq).resolve_left (ne_of_lt hSf)
  calc
    (∑' q : ℕ+, g q) = (∑' q : ℕ+, gD q) + (∑' q : ℕ+, gC q) := hsumg
    _ = (∑' q : ℕ+, gD q) + (∑' q : ℕ+, fC q) := by rw [← hC]
    _ = ⊤ := by simp [hR]

/-- **Truncation preserves divergence of `∑ ψ*`** (paper §2, Case 2). -/
lemma tsum_psiStar_min_half (ψ : ℕ+ → ℝ≥0) (hFin : (bigQ ψ).Finite)
    (hψ : (∑' q : ℕ+, ψ_star ψ q) = ∞) :
    (∑' q : ℕ+, ψ_star (psiHalf ψ) q) = ∞ := by
  let D := divSet ψ
  have hDfin : D.Finite := divSet_finite ψ hFin
  apply tsum_eq_top_of_finite_diff (f := fun q => ψ_star ψ q)
    (g := fun q => ψ_star (psiHalf ψ) q) D hDfin
  · intro q hq
    exact (psiStar_eq_of_not_mem_divSet ψ hq).symm
  · intro q _hq
    exact psiStar_lt_top_of_bigQ_finite ψ hFin q
  · intro q _hq
    exact psiStarHalf_lt_top ψ q
  · exact hψ

end Submission.DS
