import Submission.DS.CircVol
import Submission.DS.NumAux
import Submission.DS.NumAux2

open scoped Nat ENNReal NNReal
open Set Filter MeasureTheory
open DuffinSchaefferConjecture

/-!
# General-to-decayed reduction for Gallagher's zero-one law

For arbitrary `ψ : ℕ+ → ℝ≥0`, `W ψ` is null or full.  Split on whether the radii
`radSeq ψ n = ψ(n)/n` tend to zero:

* **decaying radii**: `gallagher_zero_one_decay` applies once we clip the finitely many
  radii above `1/2` (via `min ψ (q/2)`), which leaves `W ψ` unchanged by
  `W_of_eventually_eq` and preserves `Tendsto … 0`.
* **non-decaying radii**: the radii are `≥ ε` for infinitely many denominators; reduced
  fractions with denominator `q` are eventually `ε`-dense (every window of
  `2^(2ω(q)+1)` consecutive integers contains a totative of `q`, and that window length
  is `o(q)`), so every `x ∈ [0,1]` is coprime-approximable by every sufficiently large
  such denominator: `W ψ = [0,1]`.
-/

namespace Submission.DS

/-- Clipping radii at `1/2` (i.e. `ψ ↦ min ψ (q/2)`) keeps `W` unchanged and radii
`≤ 1/2`. -/
lemma clip_le_half (ψ : ℕ+ → ℝ≥0) : ∀ q : ℕ+, (min (ψ q) ((q : NNReal) / 2) / q : NNReal) ≤ (1 / 2 : NNReal) := by
  intro q
  rw [← NNReal.coe_le_coe]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast PNat.pos q
  have hm' : ((min (ψ q) ((q : NNReal) / 2) : NNReal) : ℝ) ≤ (q : ℝ) / 2 := by
    have := NNReal.coe_le_coe.mpr (min_le_right (ψ q) ((q : NNReal) / 2))
    simpa [NNReal.coe_div] using this
  rw [NNReal.coe_div]
  have hmain : ((min (ψ q) ((q : NNReal) / 2) : NNReal) : ℝ) / (q : ℝ) ≤ (1 / 2 : ℝ) := by
    calc
      ((min (ψ q) ((q : NNReal) / 2) : NNReal) : ℝ) / (q : ℝ) ≤ ((q : ℝ) / 2) / (q : ℝ) :=
        div_le_div_of_nonneg_right hm' (le_of_lt hqpos)
      _ = (1 / 2 : ℝ) := by field_simp [hqpos.ne']
  simpa using hmain

/-- The radius sequence is nonnegative. -/
lemma radSeq_nonneg (ψ : ℕ+ → ℝ≥0) (n : ℕ) : 0 ≤ radSeq ψ n := by
  unfold radSeq
  by_cases hn : 0 < n
  · simp [hn]
    positivity
  · simp [hn]

/-- If the radii `radSeq ψ` tend to `0`, then `W ψ` is null or full. -/
theorem gallagher_zero_one_of_decay (ψ : ℕ+ → ℝ≥0)
    (hdec : Tendsto (radSeq ψ) atTop (nhds (0 : ℝ))) :
    volume (W ψ) = 0 ∨ volume (W ψ) = 1 := by
  classical
  let χ : ℕ+ → ℝ≥0 := fun q => min (ψ q) ((q : NNReal) / 2)
  have hδχ : ∀ q : ℕ+, (χ q / q : NNReal) ≤ (1 / 2 : NNReal) := by
    intro q
    simpa [χ] using clip_le_half ψ q
  have hEv := Metric.tendsto_atTop.mp hdec (1 / 2 : ℝ) (by norm_num)
  rcases hEv with ⟨N, hN⟩
  have hNabs : ∀ n : ℕ, N ≤ n → |radSeq ψ n| < (1 / 2 : ℝ) := by
    intro n hn
    simpa [Real.dist_eq] using hN n hn
  -- For cofinitely many q, χ q = ψ q
  have hbad_sub : {q : ℕ+ | ¬ χ q = ψ q} ⊆ {q : ℕ+ | (1 / 2 : ℝ) ≤ radSeq ψ (q : ℕ)} := by
    intro q hq
    by_cases hle' : ψ q ≤ (q : NNReal) / 2
    · exfalso; apply hq; exact min_eq_left hle'
    · have hgtNN : (q : NNReal) / 2 < ψ q := lt_of_not_ge hle'
      have hgtR : (q : ℝ) / 2 < (ψ q : ℝ) := by
        have := NNReal.coe_lt_coe.mpr hgtNN
        simpa [NNReal.coe_div] using this
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast PNat.pos q
      have hgt : (1 / 2 : ℝ) < (ψ q : ℝ) / (q : ℝ) := by
        have h1 : ((q : ℝ) / 2) / (q : ℝ) < (ψ q : ℝ) / (q : ℝ) :=
          div_lt_div_of_pos_right hgtR hqpos
        have h2 : ((q : ℝ) / 2) / (q : ℝ) = (1 / 2 : ℝ) := by field_simp [hqpos.ne']
        simpa [h2] using h1
      have hgt12 : (1 / 2 : ℝ) < radSeq ψ (q : ℕ) := by
        rw [radSeq_eq_coe ψ q]
        simpa [NNReal.coe_div] using hgt
      exact le_of_lt hgt12
  have hbigFin : ({n : ℕ | (1 / 2 : ℝ) ≤ radSeq ψ n} : Set ℕ).Finite := by
    refine (Set.finite_lt_nat N).subset ?_
    intro n hn
    by_contra hnN
    have hlt : |radSeq ψ n| < (1 / 2 : ℝ) := hNabs n (Nat.le_of_not_gt hnN)
    have hle : (1 / 2 : ℝ) ≤ |radSeq ψ n| := le_trans hn (le_abs_self (radSeq ψ n))
    exact (not_lt_of_ge hle) hlt
  have hpreFin : ({q : ℕ+ | (1 / 2 : ℝ) ≤ radSeq ψ (q : ℕ)} : Set ℕ+).Finite := by
    let f : ℕ+ → ℕ := fun q => (q : ℕ)
    refine (Set.finite_image_iff (f := f)
      (s := ({q : ℕ+ | (1 / 2 : ℝ) ≤ radSeq ψ (q : ℕ)} : Set ℕ+))
      (Set.injOn_of_injective PNat.coe_injective (s := ({q : ℕ+ | (1 / 2 : ℝ) ≤ radSeq ψ (q : ℕ)} : Set ℕ+)))).1 ?_
    refine (hbigFin.subset ?_)
    intro n hn
    rcases hn with ⟨q, hq, rfl⟩
    exact hq
  have hEqCo : ∀ᶠ q : ℕ+ in Filter.cofinite, χ q = ψ q := by
    rw [Filter.eventually_cofinite]
    exact hpreFin.subset hbad_sub
  -- radSeq χ → 0 as well
  have hEqCo' : ∀ q : ℕ+, N ≤ (q : ℕ) → χ q = ψ q := by
    intro q hqN
    exact (not_not.mp (by
      intro hneq
      have hle12 : (1 / 2 : ℝ) ≤ radSeq ψ (q : ℕ) := hbad_sub hneq
      have hlt : |radSeq ψ (q : ℕ)| < (1 / 2 : ℝ) := hNabs (q : ℕ) hqN
      exact (not_lt_of_ge (le_trans hle12 (le_abs_self (radSeq ψ (q : ℕ))))) hlt))
  have hEqSeq : (radSeq χ) =ᶠ[atTop] (radSeq ψ) := by
    refine eventually_atTop.2 ⟨max N 1, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := le_trans (Nat.le_max_right N 1) hn
    have hnN : N ≤ n := le_trans (Nat.le_max_left N 1) hn
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn1
    unfold radSeq
    simp only [hnpos, ↓reduceDIte]
    rw [hEqCo' ⟨n, hnpos⟩ hnN]
  have hχdec : Tendsto (radSeq χ) atTop (nhds (0 : ℝ)) := hdec.congr' hEqSeq.symm
  have hW : W χ = W ψ := W_of_eventually_eq (ψ := χ) (χ := ψ) hEqCo
  rcases gallagher_zero_one_decay χ hχdec hδχ with h0 | h1
  · left
    calc
      volume (W ψ) = volume (W χ) := by rw [hW]
      _ = 0 := h0
  · right
    calc
      volume (W ψ) = volume (W χ) := by rw [hW]
      _ = 1 := h1

/-- If the radii do not tend to zero then they are bounded below by a positive constant
on an infinite set of denominators. -/
lemma exists_epsilon_big_radSeq (ψ : ℕ+ → ℝ≥0)
    (hbig : ¬ Tendsto (radSeq ψ) atTop (nhds (0 : ℝ))) :
    ∃ ε : ℝ, 0 < ε ∧ ({n : ℕ | ε ≤ radSeq ψ n}).Infinite := by
  classical
  by_contra hcon
  have hfin : ∀ ε : ℝ, 0 < ε → ({n : ℕ | ε ≤ radSeq ψ n}).Finite := by
    intro ε hε
    by_contra hnotfin
    exact hcon ⟨ε, hε, (Set.not_finite.mp hnotfin)⟩
  apply hbig
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcof : ∀ᶠ n in atTop, |radSeq ψ n| < ε := by
    have hfinε := hfin ε hε
    have hcof' : ∀ᶠ n in atTop, n ∉ ({n : ℕ | ε ≤ radSeq ψ n} : Set ℕ) := by
      rcases hfinε.bddAbove with ⟨B, hB⟩
      refine eventually_atTop.2 ⟨B + 1, ?_⟩
      intro n hn
      by_contra hnS
      have hleB : n ≤ B := hB hnS
      omega
    filter_upwards [hcof'] with n hn
    have hnotle : ¬ ε ≤ radSeq ψ n := hn
    have hlt : radSeq ψ n < ε := lt_of_not_ge hnotle
    rw [abs_of_nonneg (radSeq_nonneg ψ n)]
    exact hlt
  rcases (Filter.eventually_atTop.1 hcof) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simpa [Real.dist_eq] using hN n hn

/-- Every `x ∈ [0,1]` is within `ε` of a reduced fraction with denominator exactly `q`,
for every sufficiently large `q`. -/
lemma dense_coprime_den (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∀ q : ℕ, Q ≤ q → ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      ∃ a : ℕ, Nat.Coprime a q ∧ |x - (a : ℝ) / (q : ℝ)| ≤ ε := by
  classical
  rcases window_len_bound ε hε with ⟨Q₀, hQ₀⟩
  let Q : ℕ := max Q₀ 1
  refine ⟨Q, le_max_right Q₀ 1, ?_⟩
  intro q hq x hx
  have hqQ₀ : Q₀ ≤ q := le_trans (le_max_left Q₀ 1) hq
  have hq1 : 1 ≤ q := le_trans (le_max_right Q₀ 1) hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hq1)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  -- nearest integer b to x*q
  let bI : ℤ := ⌊x * (q : ℝ)⌋
  have hbI0 : 0 ≤ bI := Int.floor_nonneg.mpr (mul_nonneg hx.1 (le_of_lt hqpos))
  let b : ℕ := bI.toNat
  have hbI_eq : (b : ℤ) = bI := by
    dsimp [b]
    exact Int.toNat_of_nonneg hbI0
  have hbR : (b : ℝ) = (bI : ℝ) := by exact_mod_cast hbI_eq
  have hfl1 : (bI : ℝ) ≤ x * (q : ℝ) := by
    simpa [bI] using (Int.floor_le (x * (q : ℝ)))
  have hfl2 : x * (q : ℝ) < (bI : ℝ) + 1 := by
    simpa [bI] using (Int.lt_floor_add_one (x * (q : ℝ)))
  have habs : |x * (q : ℝ) - (bI : ℝ)| < 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hfl1)]
    linarith
  have hdb : |x - (b : ℝ) / (q : ℝ)| < (1 : ℝ) / (q : ℝ) := by
    have hEQ : x - (b : ℝ) / (q : ℝ) = (x * (q : ℝ) - (b : ℝ)) / (q : ℝ) := by
      field_simp [hqne]
    calc
      |x - (b : ℝ) / (q : ℝ)| = |(x * (q : ℝ) - (b : ℝ)) / (q : ℝ)| := by rw [hEQ]
      _ = |x * (q : ℝ) - (bI : ℝ)| / (q : ℝ) := by
        rw [hbR]
        rw [abs_div, abs_of_pos hqpos]
      _ < (1 : ℝ) / (q : ℝ) := div_lt_div_of_pos_right habs hqpos
  -- a window of length L contains a totative of q
  let L : ℕ := 2 ^ (2 * q.primeFactors.card + 1)
  rcases totative_in_window q b hq1 with ⟨t, ht, hcop⟩
  let a : ℕ := b + t
  have hcop' : Nat.Coprime a q := by
    change Nat.Coprime (b + t) q
    exact hcop
  have hsum : (a : ℝ) = (b : ℝ) + (t : ℝ) := by
    change (((b + t : ℕ) : ℝ)) = (b : ℝ) + (t : ℝ)
    norm_num
  have hta : |(b : ℝ) / (q : ℝ) - (a : ℝ) / (q : ℝ)| = (t : ℝ) / (q : ℝ) := by
    calc
      |(b : ℝ) / (q : ℝ) - (a : ℝ) / (q : ℝ)| = |(((b : ℝ) - (a : ℝ)) / (q : ℝ))| := by
        rw [sub_div]
      _ = |((b : ℝ) - (a : ℝ))| / (q : ℝ) := by
        rw [abs_div, abs_of_pos hqpos]
      _ = (t : ℝ) / (q : ℝ) := by
        have hdiff : (b : ℝ) - (a : ℝ) = -((t : ℝ)) := by
          rw [hsum]
          ring
        rw [hdiff, abs_neg, abs_of_nonneg]
        positivity
  have htdiv : (t : ℝ) / (q : ℝ) < (L : ℝ) / (q : ℝ) := by
    exact div_lt_div_of_pos_right (by exact_mod_cast ht) hqpos
  have hLsum : ((1 : ℝ) + (L : ℝ)) / (q : ℝ) ≤ ε := by
    have hbig := hQ₀ q hqQ₀
    have hle : (1 : ℝ) + (L : ℝ) ≤ ε * (q : ℝ) := by
      simpa [L] using hbig
    have h1 : ((1 : ℝ) + (L : ℝ)) / (q : ℝ) ≤ (ε * (q : ℝ)) / (q : ℝ) :=
      div_le_div_of_nonneg_right hle (le_of_lt hqpos)
    have h2 : (ε * (q : ℝ)) / (q : ℝ) = ε := by field_simp [hqne]
    simpa [h2] using h1
  have hdb' : |x - (b : ℝ) / (q : ℝ)| ≤ (1 : ℝ) / (q : ℝ) := le_of_lt hdb
  have htri : |x - (a : ℝ) / (q : ℝ)| ≤
      |x - (b : ℝ) / (q : ℝ)| + |(b : ℝ) / (q : ℝ) - (a : ℝ) / (q : ℝ)| := by
    simpa [Real.dist_eq] using
      (dist_triangle x ((b : ℝ) / (q : ℝ)) ((a : ℝ) / (q : ℝ)))
  have hmain : |x - (a : ℝ) / (q : ℝ)| < ((1 : ℝ) + (L : ℝ)) / (q : ℝ) := by
    calc
      |x - (a : ℝ) / (q : ℝ)| ≤
          |x - (b : ℝ) / (q : ℝ)| + |(b : ℝ) / (q : ℝ) - (a : ℝ) / (q : ℝ)| := htri
      _ ≤ (1 : ℝ) / (q : ℝ) + (t : ℝ) / (q : ℝ) := by
        rw [hta]
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_left hdb' ((t : ℝ) / (q : ℝ)))
      _ < (1 : ℝ) / (q : ℝ) + (L : ℝ) / (q : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_lt_add_left htdiv ((1 : ℝ) / (q : ℝ)))
      _ = ((1 : ℝ) + (L : ℝ)) / (q : ℝ) := by
        rw [add_div]
  exact ⟨a, hcop', le_of_lt (lt_of_lt_of_le hmain hLsum)⟩

/-- If the radii do not decay to zero, the coprime fractions are `ε`-dense for every
`ε > 0` at infinitely many scales, so `W ψ = [0,1]` has full measure. -/
theorem volume_W_eq_one_of_not_decay (ψ : ℕ+ → ℝ≥0)
    (hbig : ¬ Tendsto (radSeq ψ) atTop (nhds (0 : ℝ))) :
    volume (W ψ) = 1 := by
  classical
  have hfull : W ψ = Set.Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx01
      rcases exists_epsilon_big_radSeq ψ hbig with ⟨ε, hε, hSinf⟩
      rcases dense_coprime_den ε hε with ⟨Q, hQ1, hQ⟩
      let S : Set ℕ := {n : ℕ | ε ≤ radSeq ψ n}
      have hSpos : ∀ n ∈ S, 0 < n := by
        intro n hn
        by_contra hn0
        have hnz : n = 0 := Nat.eq_zero_of_not_pos hn0
        subst n
        have hthis : ε ≤ radSeq ψ 0 := hn
        unfold radSeq at hthis
        simp at hthis
        linarith
      let GoodP : Set ℕ+ := {q : ℕ+ | ε ≤ radSeq ψ (q : ℕ)}
      have himg : ((fun q : ℕ+ => (q : ℕ)) '' GoodP) = S := by
        ext n
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact hq
        · intro hn
          have hnpos : 0 < n := hSpos n hn
          refine ⟨⟨n, hnpos⟩, ?_, rfl⟩
          exact hn
      have hGoodPinf : GoodP.Infinite := by
        by_contra hc
        have hc' : ((fun q : ℕ+ => (q : ℕ)) '' GoodP).Finite := by
          exact (Set.finite_image_iff (f := fun q : ℕ+ => (q : ℕ)) (s := GoodP)
            (Set.injOn_of_injective PNat.coe_injective (s := GoodP))).2 (Set.not_infinite.mp hc)
        rw [himg] at hc'
        exact hSinf hc'
      have hxAcopr : ∀ q : ℕ+, Q ≤ (q : ℕ) → q ∈ GoodP → x ∈ Acopr ψ q := by
        intro q hqQ hqg
        dsimp [GoodP] at hqg
        rcases hQ (q : ℕ) hqQ x hx01 with ⟨a, hcop, hdist⟩
        refine ⟨a, hcop, ?_⟩
        unfold inequality_1_7
        have hεr : ε ≤ ((ψ q / q : NNReal) : ℝ) := by
          rwa [radSeq_eq_coe ψ q] at hqg
        exact le_trans hdist hεr
      have hlim : x ∈ limsupDenoms (Acopr ψ) := by
        rw [mem_limsupDenoms_iff_forall_ge]
        intro N
        have hUB := (infinite_iff_forall_ge GoodP).1 hGoodPinf (max N Q)
        rcases hUB with ⟨q, hqg, hqbig⟩
        have hqN : N ≤ (q : ℕ) := le_trans (Nat.le_max_left N Q) hqbig
        have hqQ : Q ≤ (q : ℕ) := le_trans (Nat.le_max_right N Q) hqbig
        exact ⟨q, hqN, hxAcopr q hqQ hqg⟩
      exact ⟨hx01, hlim⟩
  have hvol : volume (W ψ) = 1 := by
    rw [hfull]
    rw [Real.volume_Icc]
    norm_num
  exact hvol


/-- Gallagher's zero-one law for `W ψ`, for arbitrary `ψ`. -/
theorem gallagher_zero_one_any (ψ : ℕ+ → ℝ≥0) :
    volume (W ψ) = 0 ∨ volume (W ψ) = 1 := by
  by_cases hdec : Tendsto (radSeq ψ) atTop (nhds (0 : ℝ))
  · exact gallagher_zero_one_of_decay ψ hdec
  · exact Or.inr (volume_W_eq_one_of_not_decay ψ hdec)

end Submission.DS
