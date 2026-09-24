import Mathlib
import Submission.Work.GM.S3.Gen.cellstatements
import Submission.Work.GM.S3.Gen.bumps_exist
import Submission.Work.GM.S3.Gen.cs_defs
import Submission.Work.GM.S3.s3_tail_noclash
import Submission.Work.GM.S3.gen_defs
import Submission.Work.GM.S3.Defs
import Submission.Commons.Analysis.Sampling.card_le_separated_finset

/-!
# The final assembly of the "cell route" to `S3Statement`

This file proves `Work.GM.S3.Gen.s3_of_cellSum_of`: `Submission.GM.S3Statement` (GM Prop 10.1)
follows from

* `hAff`  : GM Prop 9.1 (`AffineStatement`),
* `hL84`  : the relaxed Lemma 8.4 (`Lemma84RelaxedStatement`),
* `hCell` : the per-cell bound `S30g ≤ C N^ε (Mbig³ |W|^{3/2} + Mbig² |W|^{1/2} E^{1/2})`
            (`CellBoundStatement`, i.e. `S30g_le_cell`),
* `hSum`  : the cell decomposition of the truncated sum `Σ ‖I_m‖` (`CellSumStatement`,
            i.e. `S3_le_cellSum`).

The remaining work is arithmetic (see `NOTES_final_assembly.md`):

* `s3_tail_noclash` truncates `Spart 3 N W` at level `Klev N δ'`, with an `N^{-20}` tail;
* the cell decomposition bounds the truncated sum by `C N^{δ'} · cellSum + …`;
* the per-cell bound is applied to each cell of `cellFam` with `Mbig = Mdy N δ' j`; summing the
  geometric series over the dyadic levels `j < cellJ N δ'` gives the majorant
  `cellSum ≤ 4 Ccell N²N^{δ'}T^{δ'/2}J²(K²|W|^{3/2} + K|W|^{1/2}E^{1/2})`;
* all losses (`J² = O(log²N)`, the `T^{δ'}`-powers, the tails) are absorbed into `N^δ`.

Everything is explicit: `δ' := min δ 1 / 32`, and `N₀` is chosen so that the absorption
inequalities of the last step hold.
-/

namespace Work.GM.S3.Gen

open Complex Finset MeasureTheory
open scoped BigOperators

open Submission.GM (Rfun energy Separated Iterm Spart nzCount)
open Submission.LargeValues (M)

set_option maxHeartbeats 1000000

/-! ## Elementary growth lemmas -/

/-- For every positive exponent `e` and every constant `C` there is `N₀` with `C ≤ N^e` for
`N ≥ N₀`. -/
lemma eventually_const_le_rpow {e : ℝ} (he : 0 < e) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C ≤ (N : ℝ) ^ e := by
  have htend : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ e) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  exact Filter.eventually_atTop.mp (htend.eventually_ge_atTop C)

/-- `C · (cellJ N δ')²` is eventually dominated by `N^(3δ/8)`, for `δ > 0`, `0 < δ' ≤ 1`
(so that `⌈δ'⌉ = 1` and `cellJ N δ' = O(log N)`) and `0 < C`.

The general statement is used with `δ' = min δ 1 / 32`. -/
lemma eventually_cellJ_sq_le {δ δ' : ℝ} (hδ : 0 < δ) (hδ'pos : 0 < δ') (hδ'le : δ' ≤ 1)
    {C : ℝ} (hC : 0 < C) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      C * (cellJ N δ' : ℝ) ^ 2 ≤ (N : ℝ) ^ (3 * δ / 8) := by
  have hceil : Nat.ceil δ' = 1 := by
    rw [Nat.ceil_eq_iff (by norm_num : (1 : ℕ) ≠ 0)]
    exact ⟨by simpa using hδ'pos, by simpa using hδ'le⟩
  set e : ℝ := 3 * δ / 8 with hedef
  have hepos : 0 < e := by rw [hedef]; positivity
  have hlog2 : (0.69 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlogbound : ∀ N : ℕ, (Real.log (N : ℝ)) ^ 2 ≤ 64 * (N : ℝ) ^ (e / 4) / e ^ 2 := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · rw [hN0]
      simp [Real.log_zero, Real.zero_rpow (by linarith : e / 4 ≠ 0)]
    · have hNposr : (0 : ℝ) < N := by exact_mod_cast hNpos
      have h1 : Real.log (N : ℝ) ≤ (N : ℝ) ^ (e / 8) / (e / 8) :=
        Real.log_le_rpow_div hNposr.le (by linarith)
      have hnonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hNpos)
      have h2 : Real.log (N : ℝ) ^ 2 ≤ ((N : ℝ) ^ (e / 8) / (e / 8)) ^ 2 :=
        pow_le_pow_left₀ hnonneg h1 2
      have h3 : ((N : ℝ) ^ (e / 8) / (e / 8)) ^ 2 = 64 * ((N : ℝ) ^ (e / 8)) ^ 2 / e ^ 2 := by
        field_simp
        ring
      have h4 : ((N : ℝ) ^ (e / 8)) ^ 2 = (N : ℝ) ^ (e / 4) := by
        rw [sq, ← Real.rpow_add hNposr (e / 8) (e / 8)]
        congr 1
        ring
      rw [h3, h4] at h2
      exact h2
  have hcellJ : ∀ N : ℕ, 3 ≤ N → (cellJ N δ' : ℝ) ≤ 280 * Real.log (N : ℝ) := by
    intro N hN3
    have hN1 : 1 ≤ N := by omega
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
    have hlogN1 : 1 ≤ Real.log (N : ℝ) := by
      have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
      have h1 : 1 ≤ Real.log 3 := by
        have h := Real.log_le_log (Real.exp_pos 1) Real.exp_one_lt_three.le
        rwa [Real.log_exp] at h
      exact le_trans h1 (Real.log_le_log (by norm_num) h3)
    have hlogb : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
      have h := Real.natLog_le_logb N 2
      rw [Real.logb] at h
      push_cast at h
      exact h
    have hbound : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have h1 : Real.log (N : ℝ) / Real.log 2 ≤ Real.log (N : ℝ) / 0.69 :=
        div_le_div_of_nonneg_left hlogN (by norm_num) hlog2.le
      have h2 : Real.log (N : ℝ) / 0.69 ≤ 2 * Real.log (N : ℝ) := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.69)]
        linarith
      linarith
    have hcast : (cellJ N δ' : ℝ) ≤ 8 * ((Nat.log 2 N : ℝ) + 1) + 256 := by
      rw [cellJ, hceil]
      push_cast
      ring_nf
      exact le_rfl
    calc (cellJ N δ' : ℝ) ≤ 8 * ((Nat.log 2 N : ℝ) + 1) + 256 := hcast
      _ = 8 * (Nat.log 2 N : ℝ) + 264 := by ring
      _ ≤ 8 * (2 * Real.log (N : ℝ)) + 264 := by linarith
      _ ≤ 16 * Real.log (N : ℝ) + 264 * Real.log (N : ℝ) := by nlinarith
      _ = 280 * Real.log (N : ℝ) := by ring
  obtain ⟨N₁, hN₁⟩ := eventually_const_le_rpow (e := 3 * e / 4) (by linarith)
    (C * 78400 * 64 / e ^ 2)
  refine ⟨max 3 N₁, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN1' : N₁ ≤ N := le_trans (le_max_right _ _) hN
  have hKN : C * 78400 * 64 / e ^ 2 ≤ (N : ℝ) ^ (3 * e / 4) := hN₁ N hN1'
  have hNposr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsq : (cellJ N δ' : ℝ) ^ 2 ≤ (280 * Real.log (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hcellJ N hN3) 2
  have h280 : (280 * Real.log (N : ℝ)) ^ 2 = 78400 * (Real.log (N : ℝ)) ^ 2 := by ring
  calc C * (cellJ N δ' : ℝ) ^ 2 ≤ C * (280 * Real.log (N : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hC.le
    _ = C * 78400 * (Real.log (N : ℝ)) ^ 2 := by rw [h280]; ring
    _ ≤ C * 78400 * (64 * (N : ℝ) ^ (e / 4) / e ^ 2) := by
        have h := hlogbound N
        nlinarith [h, hC, sq_nonneg e]
    _ = (C * 78400 * 64 / e ^ 2) * (N : ℝ) ^ (e / 4) := by ring
    _ ≤ (N : ℝ) ^ (3 * e / 4) * (N : ℝ) ^ (e / 4) :=
        mul_le_mul_of_nonneg_right hKN (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N : ℝ) ^ (3 * δ / 8) := by
        rw [← Real.rpow_add hNposr (3 * e / 4) (e / 4)]
        congr 1
        rw [hedef]
        ring

/-! ## The geometric sums of the dyadic scales -/

lemma Mdy_eq_mul (N : ℕ) (δ : ℝ) (j : ℕ) : Mdy N δ j = Klev N δ * (1 / 2 : ℝ) ^ j := by
  simp only [Mdy]
  rw [one_div, inv_pow, div_eq_mul_inv]

lemma Mdy_sq_eq (N : ℕ) (δ : ℝ) (j : ℕ) :
    (Mdy N δ j) ^ 2 = (Klev N δ) ^ 2 * (1 / 4 : ℝ) ^ j := by
  rw [Mdy_eq_mul, mul_pow]
  congr 1
  rw [← pow_mul, show j * 2 = 2 * j by ring, pow_mul]
  norm_num

lemma geom_half_le (J : ℕ) : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j ≤ 2 := by
  have h := geom_sum_mul_neg (x := (1 / 2 : ℝ)) J
  have hpos : 0 < (1 / 2 : ℝ) ^ J := by positivity
  have : (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j) * (1 - 1 / 2) ≤ 1 := by
    rw [h]
    linarith
  linarith

lemma geom_quarter_le (J : ℕ) : ∑ j ∈ Finset.range J, (1 / 4 : ℝ) ^ j ≤ 2 := by
  have h := geom_sum_mul_neg (x := (1 / 4 : ℝ)) J
  have hpos : 0 < (1 / 4 : ℝ) ^ J := by positivity
  have : (∑ j ∈ Finset.range J, (1 / 4 : ℝ) ^ j) * (1 - 1 / 4) ≤ 1 := by
    rw [h]
    linarith
  linarith

lemma sum_Mdy_le {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (J : ℕ) :
    ∑ j ∈ Finset.range J, Mdy N δ j ≤ 2 * Klev N δ := by
  have hK : 0 ≤ Klev N δ := (csKlev_pos hN δ).le
  calc ∑ j ∈ Finset.range J, Mdy N δ j
      = ∑ j ∈ Finset.range J, Klev N δ * (1 / 2 : ℝ) ^ j :=
        Finset.sum_congr rfl (fun j _ => Mdy_eq_mul N δ j)
    _ = Klev N δ * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ Klev N δ * 2 := mul_le_mul_of_nonneg_left (geom_half_le J) hK
    _ = 2 * Klev N δ := by ring

lemma sum_Mdy_sq_le {N : ℕ} (hN : 1 ≤ N) (δ : ℝ) (J : ℕ) :
    ∑ j ∈ Finset.range J, (Mdy N δ j) ^ 2 ≤ 2 * (Klev N δ) ^ 2 := by
  have hK : 0 ≤ Klev N δ := (csKlev_pos hN δ).le
  calc ∑ j ∈ Finset.range J, (Mdy N δ j) ^ 2
      = ∑ j ∈ Finset.range J, (Klev N δ) ^ 2 * (1 / 4 : ℝ) ^ j :=
        Finset.sum_congr rfl (fun j _ => Mdy_sq_eq N δ j)
    _ = (Klev N δ) ^ 2 * ∑ j ∈ Finset.range J, (1 / 4 : ℝ) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ (Klev N δ) ^ 2 * 2 := mul_le_mul_of_nonneg_left (geom_quarter_le J) (sq_nonneg _)
    _ = 2 * (Klev N δ) ^ 2 := by ring

/-- `Mdy N δ ·` is antitone in the level `j` (for `N ≥ 1`). -/
lemma Mdy_mono {N : ℕ} (hN : 1 ≤ N) {δ : ℝ} {i j : ℕ} (hij : j ≤ i) :
    Mdy N δ i ≤ Mdy N δ j := by
  have hK : 0 < Klev N δ := csKlev_pos hN δ
  have h2 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ i := pow_le_pow_right₀ (by norm_num) hij
  simp only [Mdy]
  exact div_le_div_of_nonneg_left hK.le (by positivity) h2

/-! ## The truncation level identities -/

/-- `N² · Klev N δ ² = (M N)^(2+2δ)`. -/
lemma N_sq_mul_Klev_sq (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) :
    (N : ℝ) ^ 2 * (Klev N δ) ^ 2 = (M N) ^ (2 + 2 * δ) := by
  have hTpos : 0 < M N := Submission.LargeValues.M_pos hN
  rw [Klev, div_pow]
  rw [show ((M N) ^ (1 + δ)) ^ 2 = (M N) ^ (2 + 2 * δ) from by
    rw [sq, ← Real.rpow_add hTpos (1 + δ) (1 + δ)]
    congr 1
    ring]
  field_simp

/-- `N² · Klev N δ = N · (M N)^(1+δ)`. -/
lemma N_sq_mul_Klev (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) :
    (N : ℝ) ^ 2 * Klev N δ = (N : ℝ) * (M N) ^ (1 + δ) := by
  rw [Klev]
  field_simp

/-! ## The cell-sum majorant -/

/-- **The cell-sum majorant.**  If every cell `p` of `cellFam N δ' (δ'/2) J` satisfies the
per-cell bound `S30g ≤ Ccell · N^{δ'} · (M(j)³ A + M(j)² B)` with `M(j) = Mdy N δ' p.2.1` (this is
`hCell` applied with `Mbig = M(j)`), then the cell sum `Σ_p (N²/B(j)) S30g` is bounded by

`4 · Ccell · N² · N^{δ'} · T^{δ'/2} · J² · (K² A + K B)`, `T = M N`, `K = Klev N δ'`. -/
lemma cellSum_le_majorant (N : ℕ) (hN : 1 ≤ N) (δ' : ℝ) (J : ℕ) (W : Finset ℝ)
    (ψ₁ ψ₂ : ℝ → ℝ) {Ccell A B : ℝ} (hCcell : 0 ≤ Ccell) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcell : ∀ p ∈ cellFam N δ' (δ' / 2) J,
      S30g N W (Bdy N δ' (δ' / 2) p.2.1) (Mdy N δ' p.1) (Mdy N δ' p.2.1) (Mdy N δ' p.2.2) ψ₁ ψ₂
        ≤ Ccell * (N : ℝ) ^ δ' *
            ((Mdy N δ' p.2.1) ^ 3 * A + (Mdy N δ' p.2.1) ^ 2 * B)) :
    cellSum N W δ' (δ' / 2) J ψ₁ ψ₂ ≤
      4 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' * (M N) ^ (δ' / 2) * (J : ℝ) ^ 2 *
        ((Klev N δ') ^ 2 * A + Klev N δ' * B) := by
  classical
  have hKpos : 0 < Klev N δ' := csKlev_pos hN δ'
  have hTpos : 0 < (M N) ^ (δ' / 2) :=
    Real.rpow_pos_of_pos (Submission.LargeValues.M_pos hN) _
  have hMdypos : ∀ j : ℕ, 0 < Mdy N δ' j := fun j => csMdy_pos hN δ' j
  let G : ℕ × (ℕ × ℕ) → ℝ := fun p =>
    ((N : ℝ) ^ 2 / Bdy N δ' (δ' / 2) p.2.1) *
      (Ccell * (N : ℝ) ^ δ' *
        ((Mdy N δ' p.2.1) ^ 3 * A + (Mdy N δ' p.2.1) ^ 2 * B))
  let FF : ℕ → ℝ := fun j =>
    2 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' * (M N) ^ (δ' / 2) *
      ((Mdy N δ' j) ^ 2 * A + Mdy N δ' j * B)
  have hG_eq : ∀ p : ℕ × (ℕ × ℕ), G p = FF p.2.1 := by
    intro p
    have h2 : (2 : ℝ) ^ p.2.1 ≠ 0 := by positivity
    have hTne : (M N) ^ (δ' / 2) ≠ 0 := ne_of_gt hTpos
    have hKne : Klev N δ' ≠ 0 := ne_of_gt hKpos
    change ((N : ℝ) ^ 2 / Bdy N δ' (δ' / 2) p.2.1) *
        (Ccell * (N : ℝ) ^ δ' *
          ((Mdy N δ' p.2.1) ^ 3 * A + (Mdy N δ' p.2.1) ^ 2 * B))
      = 2 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' * (M N) ^ (δ' / 2) *
        ((Mdy N δ' p.2.1) ^ 2 * A + Mdy N δ' p.2.1 * B)
    simp only [Bdy, Mdy]
    field_simp
  have hG_nonneg : ∀ p : ℕ × (ℕ × ℕ), 0 ≤ G p := by
    intro p
    have hMdy : 0 ≤ Mdy N δ' p.2.1 := (hMdypos _).le
    have hBdyp : 0 ≤ (N : ℝ) ^ 2 / Bdy N δ' (δ' / 2) p.2.1 :=
      div_nonneg (by positivity) (Bdy_pos hN hKpos).le
    have hinner : 0 ≤ Ccell * (N : ℝ) ^ δ' *
        ((Mdy N δ' p.2.1) ^ 3 * A + (Mdy N δ' p.2.1) ^ 2 * B) := by
      have h1 : 0 ≤ (Mdy N δ' p.2.1) ^ 3 * A := mul_nonneg (pow_nonneg hMdy 3) hA
      have h2 : 0 ≤ (Mdy N δ' p.2.1) ^ 2 * B := mul_nonneg (pow_nonneg hMdy 2) hB
      exact mul_nonneg (mul_nonneg hCcell (by positivity)) (add_nonneg h1 h2)
    exact mul_nonneg hBdyp hinner
  have hstep1 : cellSum N W δ' (δ' / 2) J ψ₁ ψ₂ ≤
      ∑ p ∈ cellFam N δ' (δ' / 2) J, G p := by
    rw [cellSum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpos : 0 ≤ (N : ℝ) ^ 2 / Bdy N δ' (δ' / 2) p.2.1 :=
      div_nonneg (by positivity) (Bdy_pos hN hKpos).le
    have := mul_le_mul_of_nonneg_left (hcell p hp) hpos
    calc ((N : ℝ) ^ 2 / Bdy N δ' (δ' / 2) p.2.1) *
          S30g N W (Bdy N δ' (δ' / 2) p.2.1) (Mdy N δ' p.1) (Mdy N δ' p.2.1)
            (Mdy N δ' p.2.2) ψ₁ ψ₂
        = _ := rfl
      _ ≤ ((N : ℝ) ^ 2 / Bdy N δ' (δ' / 2) p.2.1) *
            (Ccell * (N : ℝ) ^ δ' *
              ((Mdy N δ' p.2.1) ^ 3 * A + (Mdy N δ' p.2.1) ^ 2 * B)) := this
      _ = G p := rfl
  have hstep2 : ∑ p ∈ cellFam N δ' (δ' / 2) J, G p ≤
      ∑ p ∈ (Finset.range J ×ˢ Finset.range J ×ˢ Finset.range J), G p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro p _ _
    exact hG_nonneg p
  have hstep3 : ∑ p ∈ (Finset.range J ×ˢ Finset.range J ×ˢ Finset.range J), G p ≤
      (J : ℝ) ^ 2 * ∑ j ∈ Finset.range J, FF j := by
    have hprod : ∑ p ∈ (Finset.range J ×ˢ Finset.range J ×ˢ Finset.range J), G p
        = ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J,
            G (i, (j, k)) := by
      rw [Finset.sum_product]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_product _ _ _
    rw [hprod]
    have inner : ∀ i : ℕ, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, G (i, (j, k)) ≤
        (J : ℝ) * ∑ j ∈ Finset.range J, FF j := by
      intro i
      have hk : ∀ j : ℕ, ∑ k ∈ Finset.range J, G (i, (j, k)) ≤ (J : ℝ) * FF j := by
        intro j
        calc ∑ k ∈ Finset.range J, G (i, (j, k)) ≤ ∑ _k ∈ Finset.range J, FF j :=
              Finset.sum_le_sum (fun k _ => le_of_eq (hG_eq (i, (j, k))))
          _ = (J : ℝ) * FF j := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, G (i, (j, k))
          ≤ ∑ j ∈ Finset.range J, (J : ℝ) * FF j := Finset.sum_le_sum (fun j _ => hk j)
        _ = (J : ℝ) * ∑ j ∈ Finset.range J, FF j := by rw [Finset.mul_sum]
    calc ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, ∑ k ∈ Finset.range J, G (i, (j, k))
        ≤ ∑ _i ∈ Finset.range J, (J : ℝ) * ∑ j ∈ Finset.range J, FF j :=
          Finset.sum_le_sum (fun i _ => inner i)
      _ = (J : ℝ) ^ 2 * ∑ j ∈ Finset.range J, FF j := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hFFsum : ∑ j ∈ Finset.range J, FF j ≤
      2 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' * (M N) ^ (δ' / 2) *
        (2 * (Klev N δ') ^ 2 * A + 2 * Klev N δ' * B) := by
    have hc : 0 ≤ 2 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' * (M N) ^ (δ' / 2) := by
      have h1 : 0 ≤ 2 * Ccell * (N : ℝ) ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg h1 (by positivity)) hTpos.le
    calc ∑ j ∈ Finset.range J, FF j
        = 2 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' * (M N) ^ (δ' / 2) *
            ∑ j ∈ Finset.range J, ((Mdy N δ' j) ^ 2 * A + Mdy N δ' j * B) := by
          rw [Finset.mul_sum]
      _ ≤ 2 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' * (M N) ^ (δ' / 2) *
            (2 * (Klev N δ') ^ 2 * A + 2 * Klev N δ' * B) := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
          have h1 := sum_Mdy_sq_le hN δ' J
          have h2 := sum_Mdy_le hN δ' J
          have h3 : (∑ j ∈ Finset.range J, (Mdy N δ' j) ^ 2) * A ≤
              (2 * (Klev N δ') ^ 2) * A := mul_le_mul_of_nonneg_right h1 hA
          have h4 : (∑ j ∈ Finset.range J, Mdy N δ' j) * B ≤ (2 * Klev N δ') * B :=
            mul_le_mul_of_nonneg_right h2 hB
          linarith
  have hmain := hstep1.trans (hstep2.trans (hstep3.trans
    (mul_le_mul_of_nonneg_left hFFsum (by positivity))))
  refine hmain.trans (le_of_eq ?_)
  ring

theorem s3_of_cellSum_of (hAff : Submission.GM.AffineStatement)
    (hL84 : Work.GM.S3.Lemma84RelaxedStatement)
    (hCell : Work.GM.S3.Gen.CellBoundStatement hAff hL84)
    (hSum : Work.GM.S3.Gen.CellSumStatement) :
    Submission.GM.S3Statement := by
  intro ε δ hε hδ
  set δ' : ℝ := min δ 1 / 32 with hδ'def
  have hδ'pos : 0 < δ' := by
    rw [hδ'def]
    exact div_pos (lt_min hδ one_pos) (by norm_num)
  have hδ'le1 : δ' ≤ 1 := by
    rw [hδ'def]
    have h := min_le_right δ 1
    linarith
  have h32δ' : 32 * δ' ≤ δ := by
    rw [hδ'def]
    have h := min_le_left δ 1
    linarith
  have h5δ' : 5 * δ' ≤ 5 * δ / 8 := by linarith
  set εc : ℝ := min ε δ' with hεcdef
  have hεcpos : 0 < εc := by rw [hεcdef]; exact lt_min hε hδ'pos
  have hεcleε : εc ≤ ε := by rw [hεcdef]; exact min_le_left _ _
  have hεcleδ' : εc ≤ δ' := by rw [hεcdef]; exact min_le_right _ _
  obtain ⟨ψ₁, ψ₂, hb1, hb2, hψ1maj, hψ2maj⟩ := bumps_exist
  obtain ⟨Ccell, hCcellpos, Ncell, hCell'⟩ := hCell ψ₁ ψ₂ hb1 hb2 εc hεcpos
  obtain ⟨Csum, hCsumpos, Nsum, hSum'⟩ := hSum ε δ' hε hδ'pos
  obtain ⟨Ctail, hCtailpos, Ntail, hTail⟩ := s3_tail_noclash ε δ' hε hδ'pos
  have hCcellnn : 0 ≤ Ccell := hCcellpos.le
  have hCsumnn : 0 ≤ Csum := hCsumpos.le
  have hCtailnn : 0 ≤ Ctail := hCtailpos.le
  obtain ⟨NA, hNA⟩ := eventually_cellJ_sq_le hδ hδ'pos hδ'le1 (C := 64 * Csum * Ccell)
    (by positivity)
  obtain ⟨NB, hNB⟩ := eventually_const_le_rpow (e := δ / 2) (by linarith)
    (8 * (2 : ℝ) ^ (3 / 2 : ℝ) * Csum)
  obtain ⟨ND, hND⟩ := eventually_const_le_rpow (e := δ / 2) (by linarith)
    (8 * (Ctail + Csum))
  refine ⟨1, one_pos, max (max (max Nsum Ncell) (max Ntail 3)) (max NA (max NB ND)), ?_⟩
  intro N hN W hWmem hWsep
  have hNsum : Nsum ≤ N := by omega
  have hNcell : Ncell ≤ N := by omega
  have hNtail : Ntail ≤ N := by omega
  have hN3 : 3 ≤ N := by omega
  have hNAle : NA ≤ N := by omega
  have hNBle : NB ≤ N := by omega
  have hNDle : ND ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  by_cases hW0 : W = ∅
  · subst hW0
    simp [Submission.GM.Spart, Submission.GM.Iterm, Submission.GM.energy]
  · -- ## the main case: `W` is nonempty
    have hWne : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hW0
    have hcard1 : 1 ≤ W.card := Finset.card_pos.mpr hWne
    have hcard1r : (1 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hcard1
    have hcardposr : (0 : ℝ) < (W.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr hWne)
    have hcardnn : (0 : ℝ) ≤ (W.card : ℝ) := hcardposr.le
    have hT1 : 1 ≤ M N := Submission.LargeValues.M_ge_one hN1
    have hTpos : 0 < M N := Submission.LargeValues.M_pos hN1
    have hTnn : 0 ≤ M N := hTpos.le
    have hN3r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := hNpos.le
    have hTpow : ∀ a : ℝ, (M N) ^ a = (N : ℝ) ^ ((6 / 5 : ℝ) * a) := by
      intro a
      rw [Submission.LargeValues.M, ← Real.rpow_mul hNnn]
    have hT2r : (M N) ^ 2 = (M N) ^ ((2 : ℝ)) := (Real.rpow_natCast (M N) 2).symm
    have hsepεc : Submission.GM.Separated W ((M N) ^ εc) := by
      intro t ht s hs hts
      exact le_trans (Real.rpow_le_rpow_of_exponent_le hT1 hεcleε) (hWsep t ht s hs hts)
    -- ## the cardinality bound
    have hTseple : 1 ≤ (M N) ^ εc := Real.one_le_rpow hT1 hεcpos.le
    have hcardT : (W.card : ℝ) ≤ 2 * M N := by
      have hb := Commons.Analysis.Sampling.card_le_separated_finset (s := W) (δ := 1)
        (by norm_num)
        (fun x hx y hy hxy => le_trans hTseple (hsepεc x hx y hy hxy))
        (a := 0) (b := M N) hTnn
        (fun x hx => (Set.mem_Icc.mp (hWmem x hx)).1)
        (fun x hx => (Set.mem_Icc.mp (hWmem x hx)).2)
      linarith
    -- ## the two weights `A`, `B` and the target `X`
    set A : ℝ := (W.card : ℝ) ^ (3 / 2 : ℝ) with hAdef
    set B : ℝ := (W.card : ℝ) ^ (1 / 2 : ℝ) * (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ)
      with hBdef
    have hA0 : 0 ≤ A := by rw [hAdef]; exact Real.rpow_nonneg hcardnn _
    have hB0 : 0 ≤ B := by
      rw [hBdef]
      exact mul_nonneg (Real.rpow_nonneg hcardnn _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hA1 : 1 ≤ A := by
      rw [hAdef]
      calc (1 : ℝ) = (1 : ℝ) ^ (3 / 2 : ℝ) := by norm_num
        _ ≤ (W.card : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hcard1r (by norm_num)
    set X : ℝ := (N : ℝ) ^ δ * ((M N) ^ 2 * A + (M N) * (N : ℝ) * B) with hXdef
    have hX0 : 0 ≤ X := by
      rw [hXdef]
      exact mul_nonneg (Real.rpow_nonneg hNnn _)
        (add_nonneg (mul_nonneg (sq_nonneg _) hA0) (mul_nonneg (mul_nonneg hTnn hNnn) hB0))
    have hXlow : (N : ℝ) ^ δ * ((M N) ^ 2 * A) ≤ X := by
      rw [hXdef]
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hTnn hNnn) hB0))
        (Real.rpow_nonneg hNnn _)
    have hXlow2 : (N : ℝ) ^ δ * ((M N) * (N : ℝ) * B) ≤ X := by
      rw [hXdef]
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hA0))
        (Real.rpow_nonneg hNnn _)
    -- ## the truncated sum
    set TR : ℂ := ∑ m₁ ∈ Finset.Icc (-⌊Klev N δ'⌋) ⌊Klev N δ'⌋,
      ∑ m₂ ∈ Finset.Icc (-⌊Klev N δ'⌋) ⌊Klev N δ'⌋,
      ∑ m₃ ∈ Finset.Icc (-⌊Klev N δ'⌋) ⌊Klev N δ'⌋,
        (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then Iterm N W (m₁, m₂, m₃) else 0) with hTRdef
    set TRn : ℝ := ∑ m₁ ∈ Finset.Icc (-⌊Klev N δ'⌋) ⌊Klev N δ'⌋,
      ∑ m₂ ∈ Finset.Icc (-⌊Klev N δ'⌋) ⌊Klev N δ'⌋,
      ∑ m₃ ∈ Finset.Icc (-⌊Klev N δ'⌋) ⌊Klev N δ'⌋,
        (if m₁ ≠ 0 ∧ m₂ ≠ 0 ∧ m₃ ≠ 0 then ‖Iterm N W (m₁, m₂, m₃)‖ else 0) with hTRndef
    have htailbound : ‖Submission.GM.Spart 3 N W - TR‖ ≤ Ctail * (N : ℝ) ^ (-20 : ℤ) := by
      have h := (hTail N hNtail W hWmem hWsep).2
      rw [hTRdef]
      simpa only [Klev] using h
    have hnormTR : ‖TR‖ ≤ TRn := by
      rw [hTRdef, hTRndef]
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m₁ _ => ?_)
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m₂ _ => ?_)
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m₃ _ => ?_)
      split_ifs with hc
      · exact le_rfl
      · simp
    have hSumBound : TRn ≤ Csum * (N : ℝ) ^ δ' * cellSum N W δ' (δ' / 2) (cellJ N δ') ψ₁ ψ₂ +
        Csum * (N : ℝ) ^ δ' * (M N) ^ (3 * (δ' / 2)) * (W.card : ℝ) ^ 3 +
        Csum * (N : ℝ) ^ (-10 : ℤ) := by
      have h := hSum' N hNsum W hWmem hWsep ψ₁ ψ₂ hb1 hb2 hψ1maj hψ2maj
      rw [hTRndef]
      simpa only [Klev] using h
    have hcomb : ‖Submission.GM.Spart 3 N W‖ ≤
        Ctail * (N : ℝ) ^ (-20 : ℤ) +
          (Csum * (N : ℝ) ^ δ' * cellSum N W δ' (δ' / 2) (cellJ N δ') ψ₁ ψ₂ +
            Csum * (N : ℝ) ^ δ' * (M N) ^ (3 * (δ' / 2)) * (W.card : ℝ) ^ 3 +
            Csum * (N : ℝ) ^ (-10 : ℤ)) := by
      have h1 : ‖Submission.GM.Spart 3 N W‖ ≤
          ‖Submission.GM.Spart 3 N W - TR‖ + ‖TR‖ := by
        have h := norm_add_le (Submission.GM.Spart 3 N W - TR) TR
        rwa [sub_add_cancel] at h
      exact h1.trans (add_le_add htailbound (hnormTR.trans hSumBound))
    have hNhalf : 0 ≤ (N : ℝ) ^ (δ / 2) := Real.rpow_nonneg hNnn _
    have hNs : (N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2) = (N : ℝ) ^ δ := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    -- ## claim B: the cell sum
    have hcellpoint : ∀ p ∈ cellFam N δ' (δ' / 2) (cellJ N δ'),
        S30g N W (Bdy N δ' (δ' / 2) p.2.1) (Mdy N δ' p.1) (Mdy N δ' p.2.1)
            (Mdy N δ' p.2.2) ψ₁ ψ₂ ≤
          Ccell * (N : ℝ) ^ δ' * ((Mdy N δ' p.2.1) ^ 3 * A + (Mdy N δ' p.2.1) ^ 2 * B) := by
      intro p hp
      obtain ⟨-, hp2⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp21, hp23, hp32⟩ := hp2
      have hji : Mdy N δ' p.1 ≤ Mdy N δ' p.2.1 := Mdy_mono hN1 hp21
      have hjk : Mdy N δ' p.2.2 ≤ Mdy N δ' p.2.1 := Mdy_mono hN1 hp23
      have hcellapp := hCell' N hNcell W hWmem hsepεc
        (Bdy N δ' (δ' / 2) p.2.1) (Mdy N δ' p.1) (Mdy N δ' p.2.1) (Mdy N δ' p.2.2)
        (Mdy N δ' p.2.1) hp32 (csMdy_pos hN1 δ' p.1) hji (csMdy_pos hN1 δ' p.2.1) le_rfl
        (csMdy_pos hN1 δ' p.2.2) hjk
      have hNle : (N : ℝ) ^ εc ≤ (N : ℝ) ^ δ' :=
        Real.rpow_le_rpow_of_exponent_le hN3r hεcleδ'
      have hbr : 0 ≤ (Mdy N δ' p.2.1) ^ 3 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
          (Mdy N δ' p.2.1) ^ 2 * (W.card : ℝ) ^ (1 / 2 : ℝ) *
            (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ) := by
        have h1 : 0 ≤ (Mdy N δ' p.2.1) ^ 3 := pow_nonneg (csMdy_pos hN1 δ' _).le 3
        have h2 : 0 ≤ (Mdy N δ' p.2.1) ^ 2 := pow_nonneg (csMdy_pos hN1 δ' _).le 2
        have h3 : 0 ≤ (W.card : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg hcardnn _
        have h4 : 0 ≤ (W.card : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hcardnn _
        have h5 : 0 ≤ (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        nlinarith [h1, h2, h3, h4, h5]
      calc S30g N W (Bdy N δ' (δ' / 2) p.2.1) (Mdy N δ' p.1) (Mdy N δ' p.2.1)
            (Mdy N δ' p.2.2) ψ₁ ψ₂
          ≤ Ccell * (N : ℝ) ^ εc * ((Mdy N δ' p.2.1) ^ 3 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
              (Mdy N δ' p.2.1) ^ 2 * (W.card : ℝ) ^ (1 / 2 : ℝ) *
                (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ)) := hcellapp
        _ ≤ Ccell * (N : ℝ) ^ δ' * ((Mdy N δ' p.2.1) ^ 3 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
              (Mdy N δ' p.2.1) ^ 2 * (W.card : ℝ) ^ (1 / 2 : ℝ) *
                (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNle hCcellnn) hbr
        _ = Ccell * (N : ℝ) ^ δ' *
              ((Mdy N δ' p.2.1) ^ 3 * A + (Mdy N δ' p.2.1) ^ 2 * B) := by
            rw [hAdef, hBdef]
            ring
    have hB : Csum * (N : ℝ) ^ δ' * cellSum N W δ' (δ' / 2) (cellJ N δ') ψ₁ ψ₂ ≤
        (1 / 8) * X := by
      have hmaj := cellSum_le_majorant N hN1 δ' (cellJ N δ') W ψ₁ ψ₂ hCcellnn hA0 hB0
        hcellpoint
      have hmul : Csum * (N : ℝ) ^ δ' * cellSum N W δ' (δ' / 2) (cellJ N δ') ψ₁ ψ₂ ≤
          Csum * (N : ℝ) ^ δ' * (4 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' * (M N) ^ (δ' / 2) *
            (cellJ N δ') ^ 2 * ((Klev N δ') ^ 2 * A + Klev N δ' * B)) :=
        mul_le_mul_of_nonneg_left hmaj (mul_nonneg hCsumnn (Real.rpow_nonneg hNnn _))
      refine hmul.trans ?_
      have hNsq : (N : ℝ) ^ δ' * (N : ℝ) ^ δ' = (N : ℝ) ^ (2 * δ') := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      have hKsq := N_sq_mul_Klev_sq N hN1 δ'
      have hK1 := N_sq_mul_Klev N hN1 δ'
      have hLHS : Csum * (N : ℝ) ^ δ' * (4 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' *
            (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
            ((Klev N δ') ^ 2 * A + Klev N δ' * B)) =
          4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
            ((M N) ^ (2 + 2 * δ') * A + (N : ℝ) * (M N) ^ (1 + δ') * B) := by
        have h1 : Csum * (N : ℝ) ^ δ' * (4 * Ccell * (N : ℝ) ^ 2 * (N : ℝ) ^ δ' *
              (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
              ((Klev N δ') ^ 2 * A + Klev N δ' * B)) =
            4 * Csum * Ccell * ((N : ℝ) ^ δ' * (N : ℝ) ^ δ') * (N : ℝ) ^ 2 * (M N) ^ (δ' / 2) *
              (cellJ N δ') ^ 2 * ((Klev N δ') ^ 2 * A + Klev N δ' * B) := by ring
        have h2 : 4 * Csum * Ccell * ((N : ℝ) ^ δ' * (N : ℝ) ^ δ') * (N : ℝ) ^ 2 *
              (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 * ((Klev N δ') ^ 2 * A + Klev N δ' * B) =
            4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
              ((N : ℝ) ^ 2 * (Klev N δ') ^ 2 * A + (N : ℝ) ^ 2 * Klev N δ' * B) := by
          rw [hNsq]
          ring
        rw [h1, h2, hKsq, hK1]
      rw [hLHS]
      -- the two power splittings
      have hTsplit1 : (M N) ^ (δ' / 2) * (M N) ^ (2 + 2 * δ') =
          (M N) ^ 2 * (M N) ^ (2.5 * δ') := by
        rw [hT2r, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
        congr 1
        ring
      have hTsplit2 : (M N) ^ (δ' / 2) * (M N) ^ (1 + δ') =
          (M N) ^ 1 * (M N) ^ (1.5 * δ') := by
        have h1 : (M N) ^ 1 = (M N) ^ ((1 : ℝ)) := by rw [pow_one, Real.rpow_one]
        rw [h1, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
        congr 1
        ring
      -- the coefficient bounds
      have hNA' : 64 * Csum * Ccell * (cellJ N δ') ^ 2 ≤ (N : ℝ) ^ (δ - 5 * δ') :=
        (hNA N hNAle).trans (Real.rpow_le_rpow_of_exponent_le hN3r (by linarith))
      have hcore1 : 4 * Csum * Ccell * (cellJ N δ') ^ 2 * (N : ℝ) ^ (2 * δ') *
          (M N) ^ (2.5 * δ') ≤ (1 / 16) * (N : ℝ) ^ δ := by
        have hT3 : (M N) ^ (2.5 * δ') = (N : ℝ) ^ (3 * δ') := by
          rw [hTpow]
          congr 1
          ring
        rw [hT3]
        have hN5 : (N : ℝ) ^ (δ - 5 * δ') * (N : ℝ) ^ (5 * δ') = (N : ℝ) ^ δ := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
        have h4 : 4 * Csum * Ccell * (cellJ N δ') ^ 2 ≤ (N : ℝ) ^ (δ - 5 * δ') / 16 := by
          linarith
        calc 4 * Csum * Ccell * (cellJ N δ') ^ 2 * (N : ℝ) ^ (2 * δ') * (N : ℝ) ^ (3 * δ')
            = 4 * Csum * Ccell * (cellJ N δ') ^ 2 *
                ((N : ℝ) ^ (2 * δ') * (N : ℝ) ^ (3 * δ')) := by ring
          _ = 4 * Csum * Ccell * (cellJ N δ') ^ 2 * (N : ℝ) ^ (5 * δ') := by
              rw [← Real.rpow_add hNpos]
              congr 2
              ring
          _ ≤ ((N : ℝ) ^ (δ - 5 * δ') / 16) * (N : ℝ) ^ (5 * δ') :=
              mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hNnn _)
          _ = (N : ℝ) ^ δ / 16 := by rw [div_mul_eq_mul_div, hN5]
          _ = (1 / 16) * (N : ℝ) ^ δ := by ring
      have hcore2 : 4 * Csum * Ccell * (cellJ N δ') ^ 2 * (N : ℝ) ^ (2 * δ') *
          (M N) ^ (1.5 * δ') ≤ (1 / 16) * (N : ℝ) ^ δ := by
        have hT4 : (M N) ^ (1.5 * δ') = (N : ℝ) ^ (1.8 * δ') := by
          rw [hTpow]
          congr 1
          ring
        rw [hT4]
        have hNA'' : 64 * Csum * Ccell * (cellJ N δ') ^ 2 ≤ (N : ℝ) ^ (δ - 3.8 * δ') :=
          (hNA N hNAle).trans
            (Real.rpow_le_rpow_of_exponent_le hN3r (by linarith [h5δ']))
        have hN5 : (N : ℝ) ^ (δ - 3.8 * δ') * (N : ℝ) ^ (3.8 * δ') = (N : ℝ) ^ δ := by
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
        have h4 : 4 * Csum * Ccell * (cellJ N δ') ^ 2 ≤ (N : ℝ) ^ (δ - 3.8 * δ') / 16 := by
          linarith
        calc 4 * Csum * Ccell * (cellJ N δ') ^ 2 * (N : ℝ) ^ (2 * δ') * (N : ℝ) ^ (1.8 * δ')
            = 4 * Csum * Ccell * (cellJ N δ') ^ 2 *
                ((N : ℝ) ^ (2 * δ') * (N : ℝ) ^ (1.8 * δ')) := by ring
          _ = 4 * Csum * Ccell * (cellJ N δ') ^ 2 * (N : ℝ) ^ (3.8 * δ') := by
              rw [← Real.rpow_add hNpos]
              congr 2
              ring
          _ ≤ ((N : ℝ) ^ (δ - 3.8 * δ') / 16) * (N : ℝ) ^ (3.8 * δ') :=
              mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hNnn _)
          _ = (N : ℝ) ^ δ / 16 := by rw [div_mul_eq_mul_div, hN5]
          _ = (1 / 16) * (N : ℝ) ^ δ := by ring
      have hterm1 : 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) *
            (cellJ N δ') ^ 2 * ((M N) ^ (2 + 2 * δ') * A) ≤ (1 / 16) * X := by
        calc 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
              ((M N) ^ (2 + 2 * δ') * A)
            = 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') *
                ((M N) ^ (δ' / 2) * (M N) ^ (2 + 2 * δ')) * (cellJ N δ') ^ 2 * A := by ring
          _ = 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * ((M N) ^ 2 * (M N) ^ (2.5 * δ')) *
                (cellJ N δ') ^ 2 * A := by rw [hTsplit1]
          _ = ((M N) ^ 2 * A) * (4 * Csum * Ccell * (cellJ N δ') ^ 2 * (N : ℝ) ^ (2 * δ') *
                (M N) ^ (2.5 * δ')) := by ring
          _ ≤ ((M N) ^ 2 * A) * ((1 / 16) * (N : ℝ) ^ δ) :=
              mul_le_mul_of_nonneg_left hcore1 (mul_nonneg (sq_nonneg _) hA0)
          _ = (1 / 16) * ((N : ℝ) ^ δ * ((M N) ^ 2 * A)) := by ring
          _ ≤ (1 / 16) * X := by linarith [hXlow]
      have hterm2 : 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) *
            (cellJ N δ') ^ 2 * ((N : ℝ) * (M N) ^ (1 + δ') * B) ≤ (1 / 16) * X := by
        calc 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
              ((N : ℝ) * (M N) ^ (1 + δ') * B)
            = 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') *
                ((M N) ^ (δ' / 2) * (M N) ^ (1 + δ')) * (cellJ N δ') ^ 2 * ((N : ℝ) * B) := by
              ring
          _ = 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * ((M N) ^ 1 * (M N) ^ (1.5 * δ')) *
                (cellJ N δ') ^ 2 * ((N : ℝ) * B) := by rw [hTsplit2]
          _ = ((M N) ^ 1 * (N : ℝ) * B) * (4 * Csum * Ccell * (cellJ N δ') ^ 2 *
                (N : ℝ) ^ (2 * δ') * (M N) ^ (1.5 * δ')) := by ring
          _ ≤ ((M N) ^ 1 * (N : ℝ) * B) * ((1 / 16) * (N : ℝ) ^ δ) :=
              mul_le_mul_of_nonneg_left hcore2
                (mul_nonneg (mul_nonneg (pow_nonneg hTnn 1) hNnn) hB0)
          _ = (1 / 16) * ((N : ℝ) ^ δ * ((M N) * (N : ℝ) * B)) := by
              rw [pow_one]
              ring
          _ ≤ (1 / 16) * X := by linarith [hXlow2]
      calc 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
            ((M N) ^ (2 + 2 * δ') * A + (N : ℝ) * (M N) ^ (1 + δ') * B)
          = 4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
              ((M N) ^ (2 + 2 * δ') * A) +
            4 * Csum * Ccell * (N : ℝ) ^ (2 * δ') * (M N) ^ (δ' / 2) * (cellJ N δ') ^ 2 *
              ((N : ℝ) * (M N) ^ (1 + δ') * B) := by ring
        _ ≤ (1 / 16) * X + (1 / 16) * X := add_le_add hterm1 hterm2
        _ = (1 / 8) * X := by ring
    -- ## claim C: the middle term
    have hC : Csum * (N : ℝ) ^ δ' * (M N) ^ (3 * (δ' / 2)) * (W.card : ℝ) ^ 3 ≤
        (1 / 8) * X := by
      have hexp3 : (3 : ℝ) * (δ' / 2) = 1.5 * δ' := by ring
      rw [hexp3]
      have hcube : (W.card : ℝ) ^ 3 ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * (M N) ^ (3 / 2 : ℝ) * A := by
        have hsplit : (W.card : ℝ) ^ 3 =
            (W.card : ℝ) ^ (3 / 2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_natCast (W.card : ℝ) 3, ← Real.rpow_add hcardposr (3 / 2) (3 / 2)]
          norm_num
        rw [hsplit, hAdef]
        calc (W.card : ℝ) ^ (3 / 2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ)
            ≤ (2 * M N) ^ (3 / 2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow hcardnn hcardT (by norm_num))
                (Real.rpow_nonneg hcardnn _)
          _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (M N) ^ (3 / 2 : ℝ) * (W.card : ℝ) ^ (3 / 2 : ℝ) := by
              rw [Real.mul_rpow (by norm_num) hTnn]
      have hTsplitC : (M N) ^ (1.5 * δ') * (M N) ^ (3 / 2 : ℝ) =
          (M N) ^ 2 * (M N) ^ (1.5 * δ' - 1 / 2) := by
        rw [hT2r, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
        congr 1
        ring
      have hTsmall : (M N) ^ (1.5 * δ' - 1 / 2) ≤ (N : ℝ) ^ (δ / 2 - δ') := by
        rw [hTpow]
        rw [show (6 / 5 : ℝ) * (1.5 * δ' - 1 / 2) = 1.8 * δ' - 0.6 by ring]
        exact Real.rpow_le_rpow_of_exponent_le hN3r (by linarith)
      have hNN : (N : ℝ) ^ δ' * (N : ℝ) ^ (δ / 2 - δ') = (N : ℝ) ^ (δ / 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      have hNB' : 8 * (2 : ℝ) ^ (3 / 2 : ℝ) * Csum ≤ (N : ℝ) ^ (δ / 2) := hNB N hNBle
      calc Csum * (N : ℝ) ^ δ' * (M N) ^ (1.5 * δ') * (W.card : ℝ) ^ 3
          ≤ Csum * (N : ℝ) ^ δ' * (M N) ^ (1.5 * δ') *
              ((2 : ℝ) ^ (3 / 2 : ℝ) * (M N) ^ (3 / 2 : ℝ) * A) :=
            mul_le_mul_of_nonneg_left hcube
              (mul_nonneg (mul_nonneg hCsumnn (Real.rpow_nonneg hNnn _))
                (Real.rpow_nonneg hTnn _))
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * Csum * (N : ℝ) ^ δ' *
              ((M N) ^ (1.5 * δ') * (M N) ^ (3 / 2 : ℝ)) * A := by ring
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * Csum * (N : ℝ) ^ δ' *
              ((M N) ^ 2 * (M N) ^ (1.5 * δ' - 1 / 2)) * A := by rw [hTsplitC]
        _ ≤ (2 : ℝ) ^ (3 / 2 : ℝ) * Csum * (N : ℝ) ^ δ' *
              ((M N) ^ 2 * (N : ℝ) ^ (δ / 2 - δ')) * A := by
            refine mul_le_mul_of_nonneg_right ?_ hA0
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left hTsmall (sq_nonneg _)
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * Csum * ((N : ℝ) ^ δ' * (N : ℝ) ^ (δ / 2 - δ')) *
              ((M N) ^ 2 * A) := by ring
        _ = (2 : ℝ) ^ (3 / 2 : ℝ) * Csum * (N : ℝ) ^ (δ / 2) * ((M N) ^ 2 * A) := by rw [hNN]
        _ ≤ (1 / 8) * ((N : ℝ) ^ δ * ((M N) ^ 2 * A)) := by
            have h8 : (2 : ℝ) ^ (3 / 2 : ℝ) * Csum ≤ (N : ℝ) ^ (δ / 2) / 8 := by
              linarith [hNB']
            calc (2 : ℝ) ^ (3 / 2 : ℝ) * Csum * (N : ℝ) ^ (δ / 2) * ((M N) ^ 2 * A)
                = ((2 : ℝ) ^ (3 / 2 : ℝ) * Csum) * ((N : ℝ) ^ (δ / 2) * ((M N) ^ 2 * A)) := by
                  ring
              _ ≤ ((N : ℝ) ^ (δ / 2) / 8) * ((N : ℝ) ^ (δ / 2) * ((M N) ^ 2 * A)) := by
                  refine mul_le_mul_of_nonneg_right h8 ?_
                  exact mul_nonneg hNhalf (mul_nonneg (sq_nonneg _) hA0)
              _ = (1 / 8) * ((N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (δ / 2)) * ((M N) ^ 2 * A) := by
                  ring
              _ = (1 / 8) * ((N : ℝ) ^ δ * ((M N) ^ 2 * A)) := by rw [hNs]; ring
        _ ≤ (1 / 8) * X := by linarith [hXlow]
    -- ## claim D: the two tails
    have hD : Ctail * (N : ℝ) ^ (-20 : ℤ) + Csum * (N : ℝ) ^ (-10 : ℤ) ≤ (1 / 4) * X := by
      have hNδ1 : (1 : ℝ) ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN3r hδ.le
      have hXge : (N : ℝ) ^ δ ≤ X := by
        have h1 : (1 : ℝ) ≤ (M N) ^ 2 * A := by
          have h2 : (1 : ℝ) ≤ (M N) ^ 2 := one_le_pow₀ hT1
          nlinarith [h2, hA1]
        have h3 : (N : ℝ) ^ δ * 1 ≤ (N : ℝ) ^ δ * ((M N) ^ 2 * A) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hNnn _)
        linarith [hXlow]
      have hz1 : (N : ℝ) ^ (-20 : ℤ) ≤ (N : ℝ) ^ (-10 : ℤ) := by
        rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
        exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hN3r (by norm_num))
      have hz10nn : (0 : ℝ) ≤ (N : ℝ) ^ (-10 : ℤ) := by positivity
      have hkey : (N : ℝ) ^ (-10 : ℤ) * (N : ℝ) ^ (δ / 2) ≤ 2 * (N : ℝ) ^ δ := by
        have h1 : (N : ℝ) ^ (-10 : ℤ) ≤ 1 := by
          rw [show (N : ℝ) ^ (-10 : ℤ) = (N : ℝ) ^ ((-10 : ℤ) : ℝ) from
            (Real.rpow_intCast (N : ℝ) (-10)).symm]
          exact Real.rpow_le_one_of_one_le_of_nonpos hN3r (by norm_num)
        have h2 : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 2) := Real.one_le_rpow hN3r (by linarith)
        have h3 : (N : ℝ) ^ (δ / 2) ≤ 2 * (N : ℝ) ^ δ := by
          nlinarith [hNs, h2, hNhalf]
        calc (N : ℝ) ^ (-10 : ℤ) * (N : ℝ) ^ (δ / 2)
            ≤ 1 * (N : ℝ) ^ (δ / 2) := mul_le_mul_of_nonneg_right h1 hNhalf
          _ ≤ 2 * (N : ℝ) ^ δ := by linarith [h3]
      have hND' : 8 * (Ctail + Csum) ≤ (N : ℝ) ^ (δ / 2) := hND N hNDle
      calc Ctail * (N : ℝ) ^ (-20 : ℤ) + Csum * (N : ℝ) ^ (-10 : ℤ)
          ≤ (Ctail + Csum) * (N : ℝ) ^ (-10 : ℤ) := by nlinarith [hz1, hCtailnn, hCsumnn]
        _ ≤ (1 / 4) * X := by
            have hstep : (Ctail + Csum) * (N : ℝ) ^ (-10 : ℤ) ≤
                ((N : ℝ) ^ (δ / 2) / 8) * (N : ℝ) ^ (-10 : ℤ) := by
              refine mul_le_mul_of_nonneg_right ?_ hz10nn
              linarith [hND']
            calc (Ctail + Csum) * (N : ℝ) ^ (-10 : ℤ)
                ≤ ((N : ℝ) ^ (δ / 2) / 8) * (N : ℝ) ^ (-10 : ℤ) := hstep
              _ = (1 / 8) * ((N : ℝ) ^ (-10 : ℤ) * (N : ℝ) ^ (δ / 2)) := by ring
              _ ≤ (1 / 8) * (2 * (N : ℝ) ^ δ) := by
                  exact mul_le_mul_of_nonneg_left hkey (by norm_num)
              _ = (1 / 4) * (N : ℝ) ^ δ := by ring
              _ ≤ (1 / 4) * X := by linarith [hXge]
    -- ## the final assembly
    have hgoal : ‖Submission.GM.Spart 3 N W‖ ≤ 1 * X := by
      refine hcomb.trans ?_
      have h1 : Ctail * (N : ℝ) ^ (-20 : ℤ) + Csum * (N : ℝ) ^ (-10 : ℤ) ≤ (1 / 4) * X := hD
      have h2 : Csum * (N : ℝ) ^ δ' * cellSum N W δ' (δ' / 2) (cellJ N δ') ψ₁ ψ₂ ≤
          (1 / 8) * X := hB
      have h3 : Csum * (N : ℝ) ^ δ' * (M N) ^ (3 * (δ' / 2)) * (W.card : ℝ) ^ 3 ≤
          (1 / 8) * X := hC
      have h4 : Ctail * (N : ℝ) ^ (-20 : ℤ) +
            (Csum * (N : ℝ) ^ δ' * cellSum N W δ' (δ' / 2) (cellJ N δ') ψ₁ ψ₂ +
              Csum * (N : ℝ) ^ δ' * (M N) ^ (3 * (δ' / 2)) * (W.card : ℝ) ^ 3 +
              Csum * (N : ℝ) ^ (-10 : ℤ)) ≤
          (1 / 4) * X + ((1 / 8) * X + (1 / 8) * X) := by linarith
      refine h4.trans ?_
      have h5 : (1 / 4) * X + ((1 / 8) * X + (1 / 8) * X) = (1 / 2) * X := by ring
      rw [h5]
      linarith [hX0]
    have hRHS : (1 : ℝ) * ((N : ℝ) ^ δ * ((M N) ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
          (M N) * (N : ℝ) * ((W.card : ℝ) ^ (1 / 2 : ℝ) *
            (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ))))
        = (1 : ℝ) * (N : ℝ) ^ δ * ((M N) ^ 2 * (W.card : ℝ) ^ (3 / 2 : ℝ) +
          (M N) * (N : ℝ) * (W.card : ℝ) ^ (1 / 2 : ℝ) *
            (Submission.GM.energy W : ℝ) ^ (1 / 2 : ℝ)) := by
      ring
    rw [hXdef, hAdef, hBdef] at hgoal
    rw [← hRHS]
    exact hgoal

end Work.GM.S3.Gen
