import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Core.blk_sep_base
import Submission.Work.TMC16Core.Core.irrat_block_gen

/-!
# `irrat_blk_nr` : the irrational block estimate from continued-fraction data

Assembly file.  The two delegated ingredients are imported:
* `Work.TMC16Core.Core.blk_sep_base` : separation of the block at the base scale
  `fracDist (d * α) ≥ 1/(2 * q 0)` for `d < q 0` (`Core/blk_sep_base.lean`);
* `Work.TMC16Core.Core.irrat_block_gen` : AJ Lemma 9.6 (`irrat-1`) in the general regime
  `q * Δ < 1` (`Core/irrat_block_gen.lean`).

Everything here is the reduction: the integer block `Icc p (p + q(n-1) - 1)` is re-indexed to
`Icc 1 q(n-1)`, the smallness `q(n-1) * Δ(n-1) < 1`, the rational approximation
`round (q(n-1) * α)` and the separation hypothesis are supplied from the hypotheses, and
`log (∏ …)` is replaced by the corresponding sum of logs.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core
open scoped BigOperators

/-! ## Separation -/

/-- `fracDist` is even: its definition `|x - round x|` uses only `round_le`. -/
lemma fracDist_neg (x : ℝ) : fracDist (-x) = fracDist x := by
  have key : ∀ y : ℝ, fracDist y = Basic.nn y := fun _ => rfl
  rw [key, key]
  apply le_antisymm
  · simp only [Basic.nn]
    calc |-x - ↑(round (-x))| ≤ |-x + ↑(round x)| := by
            simpa using round_le (-x) (-(round x))
      _ = |x - ↑(round x)| := by
            rw [show (-x : ℝ) + ↑(round x) = -(x - ↑(round x)) by ring, abs_neg]
  · simp only [Basic.nn]
    calc |x - ↑(round x)| ≤ |x + ↑(round (-x))| := by
            simpa using round_le x (-(round (-x)))
      _ = |-x - ↑(round (-x))| := by
            rw [show (x : ℝ) + ↑(round (-x)) = -(-x - ↑(round (-x))) by ring, abs_neg]

/-- The base-scale estimate propagates to every scale: `fracDist (d * α) ≥ 1/(2 * q N)` for
`d < q N`. -/
theorem sep_all {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hbase : ∀ d : ℕ, 1 ≤ d → d < q 0 → 1 / (2 * (q 0 : ℝ)) ≤ fracDist ((d : ℝ) * α)) :
    ∀ N d : ℕ, 1 ≤ d → d < q N → 1 / (2 * (q N : ℝ)) ≤ fracDist ((d : ℝ) * α) := by
  intro N
  induction N with
  | zero => exact hbase
  | succ N ih =>
    intro d hd hdq
    have hqmono : q N < q (N + 1) := hmono (Nat.lt_succ_self N)
    rcases lt_or_ge d (q N) with hlt | hge
    · have h1 := ih d hd hlt
      refine le_trans ?_ h1
      have hqle : (q N : ℝ) ≤ (q (N + 1) : ℝ) := by exact_mod_cast hqmono.le
      have h2q : (0 : ℝ) < 2 * (q N : ℝ) := by
        have : (0 : ℝ) < (q N : ℝ) := by exact_mod_cast hqpos N
        linarith
      exact one_div_le_one_div_of_le h2q (by linarith)
    · have hΔN : Δ N ≤ fracDist ((d : ℝ) * α) := hbest N d hge hdq
      have hlo := hΔlo N
      have hsum : (q N : ℝ) + (q (N + 1) : ℝ) < 2 * (q (N + 1) : ℝ) := by
        have : (q N : ℝ) < (q (N + 1) : ℝ) := by exact_mod_cast hqmono
        linarith
      have hpos' : (0 : ℝ) < (q N : ℝ) + (q (N + 1) : ℝ) := by
        have : (0 : ℝ) < (q N : ℝ) := by exact_mod_cast hqpos N
        linarith
      have hthis : 1 / (2 * (q (N + 1) : ℝ)) < 1 / ((q N : ℝ) + (q (N + 1) : ℝ)) :=
        one_div_lt_one_div_of_lt hpos' hsum
      have hlo' : 1 / ((q N : ℝ) + (q (N + 1) : ℝ)) < Δ N := by
        rw [add_comm]; exact hlo
      exact le_trans hthis.le (le_trans hlo'.le hΔN)

/-! ## Re-indexing the block -/

/-- The occurrence of `ℤ`-shifted block sums: for the phase `2x = ξ + (p-1)α` the integer block
`Icc p (p+L-1)` with the minimum removed turns into the index block `Icc 1 L` with the
corresponding index removed. -/
lemma sum_block_reindex {L : ℕ} {p k₀ : ℤ} (ξ α : ℝ)
    (hk₀ : k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1)) :
    (∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|)
      = ∑ k ∈ (Finset.Icc 1 L).erase ((k₀ - p + 1).toNat),
          Real.log |Real.sin (2 * Real.pi * ((ξ + ((p : ℝ) - 1) * α) / 2
            + (k : ℝ) * α / 2))| := by
  set x : ℝ := (ξ + ((p : ℝ) - 1) * α) / 2 with hx
  set j₀ : ℕ := (k₀ - p + 1).toNat with hj₀
  have hmem₀ : k₀ - p + 1 ∈ Finset.Icc 1 (L : ℤ) := by
    rw [Finset.mem_Icc] at hk₀
    rw [Finset.mem_Icc]
    omega
  have hj₀spec : ((j₀ : ℕ) : ℤ) = k₀ - p + 1 := by
    rw [hj₀]
    exact Int.toNat_of_nonneg (by rw [Finset.mem_Icc] at hmem₀; omega)
  refine Finset.sum_bij (fun k _ => (k - p + 1).toNat) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkne, hkmem⟩ := hk
    rw [Finset.mem_erase]
    constructor
    · intro hcon
      apply hkne
      have h1 : 0 ≤ k - p + 1 := by rw [Finset.mem_Icc] at hkmem; omega
      have h2 : 0 ≤ k₀ - p + 1 := by rw [Finset.mem_Icc] at hk₀; omega
      have hcon' : (k - p + 1).toNat = (k₀ - p + 1).toNat := by rw [hj₀] at hcon; exact hcon
      have hconZ : ((k - p + 1).toNat : ℤ) = ((k₀ - p + 1).toNat : ℤ) := by exact_mod_cast hcon'
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at hconZ
      omega
    · rw [Finset.mem_Icc] at hkmem ⊢
      have h1 : 0 ≤ k - p + 1 := by omega
      have h2 : k - p + 1 ≤ (L : ℤ) := by omega
      constructor
      · have : (1 : ℤ) ≤ ((k - p + 1).toNat : ℤ) := by rw [Int.toNat_of_nonneg h1]; omega
        omega
      · have : ((k - p + 1).toNat : ℤ) ≤ (L : ℤ) := by rw [Int.toNat_of_nonneg h1]; omega
        omega
  · intro k₁ hk₁ k₂ hk₂ heq
    rw [Finset.mem_erase] at hk₁ hk₂
    have h1 : 0 ≤ k₁ - p + 1 := by rw [Finset.mem_Icc] at hk₁; omega
    have h2 : 0 ≤ k₂ - p + 1 := by rw [Finset.mem_Icc] at hk₂; omega
    have heq' : ((k₁ - p + 1).toNat : ℤ) = ((k₂ - p + 1).toNat : ℤ) := by exact_mod_cast heq
    rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at heq'
    omega
  · intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hbne, hbmem⟩ := hb
    refine ⟨(b : ℤ) + p - 1, ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hcon
        apply hbne
        rw [hj₀]
        rw [← hcon]
        have : (b : ℤ) + p - 1 - p + 1 = (b : ℤ) := by ring
        rw [this, Int.toNat_natCast]
      · rw [Finset.mem_Icc] at hbmem ⊢
        constructor <;> omega
    · have : (b : ℤ) + p - 1 - p + 1 = (b : ℤ) := by ring
      rw [this, Int.toNat_natCast]
  · intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkne, hkmem⟩ := hk
    have h1 : 0 ≤ k - p + 1 := by rw [Finset.mem_Icc] at hkmem; omega
    have hcast : ((((k - p + 1).toNat : ℕ)) : ℝ) = (k : ℝ) - (p : ℝ) + 1 := by
      have hzi : (((k - p + 1).toNat : ℕ) : ℤ) = k - p + 1 := Int.toNat_of_nonneg h1
      have hreal : (((k - p + 1).toNat : ℕ) : ℝ) = ((k - p + 1 : ℤ) : ℝ) := by exact_mod_cast hzi
      rw [hreal]; push_cast; ring
    congr 2
    rw [hx, hcast]
    ring

/-! ## Elementary consequences of the `nn`/`S` API -/

/-- `|sin (π a)| ≤ |sin (π b)|` implies `nn a ≤ nn b`. -/
lemma nn_le_of_S_le {a b : ℝ} (h : Basic.S a ≤ Basic.S b) : Basic.nn a ≤ Basic.nn b := by
  rw [Basic.S_eq_sin_nn, Basic.S_eq_sin_nn] at h
  have ha : Real.pi * Basic.nn a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    constructor <;> nlinarith [Real.pi_pos, Basic.nn_nonneg a, Basic.nn_le_half a]
  have hb : Real.pi * Basic.nn b ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    constructor <;> nlinarith [Real.pi_pos, Basic.nn_nonneg b, Basic.nn_le_half b]
  have h2 := (Real.strictMonoOn_sin.le_iff_le ha hb).mp h
  nlinarith [Real.pi_pos]

/-! ## The separation hypothesis in the form used by `irrat_block_gen` -/

lemma sep_pair {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hbase : ∀ d : ℕ, 1 ≤ d → d < q 0 → 1 / (2 * (q 0 : ℝ)) ≤ fracDist ((d : ℝ) * α))
    {N : ℕ} :
    ∀ k l : ℕ, 1 ≤ k → k ≤ q N → 1 ≤ l → l ≤ q N → k ≠ l →
      1 / (2 * (q N : ℝ)) ≤ fracDist ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * α) := by
  intro k l hk1 hk2 hl1 hl2 hkl
  have hsep := sep_all hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hbase
  rcases le_or_gt k l with hle | hlt
  · have hd1 : 1 ≤ l - k := by omega
    have hdlt : l - k < q N := by omega
    have h1 := hsep N (l - k) hd1 hdlt
    have hcast : ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ)) = -(((l - k : ℕ) : ℝ)) := by
      push_cast [Nat.cast_sub hle] ; ring
    rw [hcast, show -(((l - k : ℕ) : ℝ)) * α = -((((l - k : ℕ) : ℝ)) * α) by ring, fracDist_neg]
    exact h1
  · have hd1 : 1 ≤ k - l := by omega
    have hdlt : k - l < q N := by omega
    have h1 := hsep N (k - l) hd1 hdlt
    have hcast : ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ)) = ((k - l : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hlt.le]; ring
    rw [hcast]
    exact h1


/-! ## The target -/

theorem irrat_blk_nr {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n : ℕ} (hn : 1 ≤ n) {p : ℤ} {ξ : ℝ} {k₀ : ℤ}
    (hk₀ : k₀ ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1))
    (hmin : ∀ k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1),
      |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
        |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) :
    |∑ k ∈ (Finset.Icc p (p + (q (n - 1) : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
      + ((q (n - 1) : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q (n - 1) : ℝ) := by
  have hLpos : 0 < q (n - 1) := hqpos (n - 1)
  have hbase := blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
  set j₀ : ℕ := (k₀ - p + 1).toNat with hj₀def
  have hj₀nn : 0 ≤ k₀ - p + 1 := by rw [Finset.mem_Icc] at hk₀; omega
  have hj₀cast : ((j₀ : ℕ) : ℤ) = k₀ - p + 1 := by
    rw [hj₀def]; exact Int.toNat_of_nonneg hj₀nn
  have hj₀mem : j₀ ∈ Finset.Icc 1 (q (n - 1)) := by
    rw [Finset.mem_Icc] at hk₀ ⊢
    constructor
    · have : (1 : ℤ) ≤ ((j₀ : ℕ) : ℤ) := by rw [hj₀cast]; omega
      omega
    · have : ((j₀ : ℕ) : ℤ) ≤ (q (n - 1) : ℤ) := by rw [hj₀cast]; omega
      omega
  -- re-index the sum
  have hre := sum_block_reindex (L := q (n - 1)) (p := p) (k₀ := k₀) ξ α hk₀
  rw [hre]
  -- the block estimate
  have hblock := irrat_block_gen (α := α) (q := q (n - 1)) (Δ := Δ (n - 1))
    hLpos (hΔpos (n - 1))
    (by
      refine ⟨round (((q (n - 1) : ℕ) : ℝ) * α), ?_⟩
      have h := hΔeq (n - 1)
      rw [h]
      exact le_of_eq rfl)
    (by
      have hup := hΔup (n - 1)
      have hmono' : q (n - 1) < q ((n - 1) + 1) := hmono (Nat.lt_succ_self (n - 1))
      have hq1 : (0 : ℝ) < ((q (n - 1) : ℕ) : ℝ) := by exact_mod_cast hqpos (n - 1)
      have hq2 : (0 : ℝ) < ((q ((n - 1) + 1) : ℕ) : ℝ) := by exact_mod_cast hqpos ((n - 1) + 1)
      have h1 : ((q (n - 1) : ℕ) : ℝ) * Δ (n - 1)
          < ((q (n - 1) : ℕ) : ℝ) * (1 / ((q ((n - 1) + 1) : ℕ) : ℝ)) := by
        have := mul_lt_mul_of_pos_left hup hq1
        simpa using this
      have h2 : ((q (n - 1) : ℕ) : ℝ) * (1 / ((q ((n - 1) + 1) : ℕ) : ℝ)) < 1 := by
        rw [mul_one_div, div_lt_one hq2]
        exact_mod_cast hmono'
      linarith)
    (sep_pair hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hbase (N := n - 1))
    ((ξ + ((p : ℝ) - 1) * α) / 2) hj₀mem
    (by
      intro k hk
      rw [Finset.mem_Icc] at hk
      -- the corresponding integer site
      have hkZ : (p + (k : ℤ) - 1) ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) := by
        rw [Finset.mem_Icc]; constructor <;> omega
      have h := hmin (p + (k : ℤ) - 1) hkZ
      have e1 : 2 * Real.pi * ((ξ + ((p : ℝ) - 1) * α) / 2 + (k : ℝ) * α / 2)
          = Real.pi * (ξ + (((p + (k : ℤ) - 1 : ℤ)) : ℝ) * α) := by push_cast; ring
      have e2 : 2 * Real.pi * ((ξ + ((p : ℝ) - 1) * α) / 2 + (j₀ : ℝ) * α / 2)
          = Real.pi * (ξ + (k₀ : ℝ) * α) := by
        have hj₀real : ((j₀ : ℕ) : ℝ) = (k₀ : ℝ) - (p : ℝ) + 1 := by
          have h : ((((j₀ : ℕ) : ℤ)) : ℝ) = (((k₀ - p + 1 : ℤ)) : ℝ) := by rw [hj₀cast]
          simpa using h
        rw [hj₀real]; ring
      rw [e1, e2]
      exact h)
  -- the factors in the erase-set are nonzero
  have hnonzero : ∀ k ∈ (Finset.Icc 1 (q (n - 1))).erase j₀,
      |Real.sin (2 * Real.pi * ((ξ + ((p : ℝ) - 1) * α) / 2 + (k : ℝ) * α / 2))| ≠ 0 := by
    intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkne, hkmem⟩ := hk
    rw [Finset.mem_Icc] at hkmem
    set m : ℤ := p + (k : ℤ) - 1 with hmdef
    have hmmem : m ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) := by
      rw [Finset.mem_Icc]; constructor <;> simp only [hmdef] <;> omega
    have hmk : m - k₀ = (k : ℤ) - (j₀ : ℤ) := by
      rw [hmdef, hj₀cast]; ring
    have hj₀1 : 1 ≤ j₀ := (Finset.mem_Icc.mp hj₀mem).1
    have hj₀2 : j₀ ≤ q (n - 1) := (Finset.mem_Icc.mp hj₀mem).2
    have hsep' := sep_pair hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hbase
      (N := n - 1) k j₀ hkmem.1 hkmem.2 hj₀1 hj₀2 hkne
    have hminm : Basic.S (ξ + (k₀ : ℝ) * α) ≤ Basic.S (ξ + (m : ℝ) * α) := by
      have h := hmin m hmmem
      simpa only [Basic.S] using h
    have hle : Basic.nn (ξ + (k₀ : ℝ) * α) ≤ Basic.nn (ξ + (m : ℝ) * α) := nn_le_of_S_le hminm
    have hdiff : Basic.nn ((ξ + (m : ℝ) * α) - (ξ + (k₀ : ℝ) * α))
        = fracDist ((((k : ℤ) - (j₀ : ℤ) : ℤ) : ℝ) * α) := by
      have h1 : (ξ + (m : ℝ) * α) - (ξ + (k₀ : ℝ) * α) = ((m - k₀ : ℤ) : ℝ) * α := by
        push_cast; ring
      rw [h1, hmk]; rfl
    have htri : Basic.nn ((ξ + (m : ℝ) * α) - (ξ + (k₀ : ℝ) * α))
        ≤ Basic.nn (ξ + (m : ℝ) * α) + Basic.nn (ξ + (k₀ : ℝ) * α) := by
      have h := Basic.nn_add_le (ξ + (m : ℝ) * α) (-(ξ + (k₀ : ℝ) * α))
      have h2 : (ξ + (m : ℝ) * α) + (-(ξ + (k₀ : ℝ) * α))
          = (ξ + (m : ℝ) * α) - (ξ + (k₀ : ℝ) * α) := by ring
      rw [h2] at h
      have hneg : Basic.nn (-(ξ + (k₀ : ℝ) * α)) = Basic.nn (ξ + (k₀ : ℝ) * α) := by
        have key : ∀ w : ℝ, Basic.nn w = fracDist w := fun _ => rfl
        rw [key, key, fracDist_neg]
      rwa [hneg] at h
    have hqL : (0 : ℝ) < ((q (n - 1) : ℕ) : ℝ) := by exact_mod_cast hqpos (n - 1)
    have hnnpos : 0 < Basic.nn (ξ + (m : ℝ) * α) := by
      have h1 : 1 / (2 * ((q (n - 1) : ℕ) : ℝ)) ≤ Basic.nn ((ξ + (m : ℝ) * α) - (ξ + (k₀ : ℝ) * α)) := by
        rw [hdiff]; exact hsep'
      have h2 : (0 : ℝ) < 1 / (2 * ((q (n - 1) : ℕ) : ℝ)) := by positivity
      linarith
    have harg : 2 * Real.pi * ((ξ + ((p : ℝ) - 1) * α) / 2 + (k : ℝ) * α / 2)
        = Real.pi * (ξ + (m : ℝ) * α) := by
      rw [hmdef]; push_cast; ring
    rw [harg]
    have hSpos : 0 < Basic.S (ξ + (m : ℝ) * α) := by
      rw [Basic.S_eq_sin_nn]
      exact Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by nlinarith [Real.pi_pos, Basic.nn_le_half (ξ + (m : ℝ) * α),
          Basic.nn_nonneg (ξ + (m : ℝ) * α)])
    rw [Basic.S] at hSpos
    exact abs_ne_zero.mpr (abs_ne_zero.mp (ne_of_gt hSpos))
  -- replace the product by the sum of logs
  have hprod : Real.log (∏ k ∈ (Finset.Icc 1 (q (n - 1))).erase j₀,
        |Real.sin (2 * Real.pi * ((ξ + ((p : ℝ) - 1) * α) / 2 + (k : ℝ) * α / 2))|)
      = ∑ k ∈ (Finset.Icc 1 (q (n - 1))).erase j₀,
          Real.log |Real.sin (2 * Real.pi * ((ξ + ((p : ℝ) - 1) * α) / 2 + (k : ℝ) * α / 2))| :=
    Real.log_prod hnonzero
  rw [hprod] at hblock
  linarith [hblock]

end Work.TMC16Core.Core
