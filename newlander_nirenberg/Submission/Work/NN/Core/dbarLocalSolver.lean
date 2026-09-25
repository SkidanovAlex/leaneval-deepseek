import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.dbarHonestOne
import Submission.Work.NN.Core.dbarHonestOneCk
import Submission.Work.NN.Core.dbarOneshotCk
import Submission.Work.NN.Core.dbarOneshotC0
import Submission.Work.NN.Core.T1Lin_holderNorm_zero

/-!
# The local `∂̄`-solver with a gain of one derivative

This file proves `Work.NN.Core.dbarLocalSolver`: on a polydisc `polydisc 0 ρ` inside which the
`(0,1)`-form `f` is `C¹` and closed, there is a linear operator `T1` solving `∂̄ (T1 f) = f` on the
strictly smaller polydisc `polydisc 0 ρ'`, together with constants `C k` such that

* `holderNorm 1 α (T1 f) (polydisc 0 ρ') ≤ ofReal (C 0) * ∑ j holderNorm 0 α (f j) (polydisc 0 ρ)`
  for `C¹` closed data (a gain of one derivative at the bottom of the scale), and
* `holderNorm (k+1) α (T1 f) (polydisc 0 ρ') ≤ ofReal (C k) * ∑ j holderNorm k α (f j) (polydisc 0 ρ)`
  for `C^k` closed data with `k ≥ 1` (the Schauder gain on the higher levels),

and `T1` maps smooth closed data to smooth data.  The operator is the telescoping solution operator
`Work.NN.Core.T1Lin` of `Work.NN.Core.dbarHonestOneCk`, whose a priori estimate on the tracking
polydisc holds on every level.

The two Schauder ingredients are

* `Work.NN.Core.dbarOneshotC0` — the one-step interior estimate on the level `0` (the general
  `C^{1,α}` estimate for `∂̄ u = f` from `C^{0,α}` bounds on `f` and `u`);
* `Work.NN.Core.T1Lin_holderNorm_zero` — the level-zero a priori estimate for the operator
  `T1Lin` on a polydisc strictly inside the equation region;

they combine exactly as in `Work.NN.Core.dbarHonestOneCk`, with `Work.NN.Core.dbarOneshotCk` and
`Work.NN.Core.T1_holderNorm_le` supplying the levels `k ≥ 1`.
-/

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

theorem dbarLocalSolver {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ' : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ' : ∀ j, 0 < ρ' j) (hlt : ∀ j, ρ' j < ρ j) :
    ∃ (T1 : (Fin n → Work.NN.Core.Cn n → ℂ) →ₗ[ℝ] (Work.NN.Core.Cn n → ℂ)) (C : ℕ → ℝ),
      (∀ k, 0 < C k) ∧
      (∀ f, (∀ j, ContDiffOn ℝ 1 (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        ∀ j (z : Work.NN.Core.Cn n), z ∈ Work.CR.Flat.polydisc 0 ρ' →
          Work.CR.Flat.dbarCoord j (T1 f) z = f j z) ∧
      (∀ f, (∀ j, ContDiffOn ℝ 1 (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        Work.CR.Flat.holderNorm 1 α (T1 f) (Work.CR.Flat.polydisc 0 ρ')
          ≤ ENNReal.ofReal (C 0) *
              ∑ j, Work.CR.Flat.holderNorm 0 α (f j) (Work.CR.Flat.polydisc 0 ρ)) ∧
      (∀ (k : ℕ) (hk : 1 ≤ k) (f : Fin n → Work.NN.Core.Cn n → ℂ),
        (∀ j, ContDiffOn ℝ k (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        Work.CR.Flat.holderNorm (k + 1) α (T1 f) (Work.CR.Flat.polydisc 0 ρ')
          ≤ ENNReal.ofReal (C k) *
              ∑ j, Work.CR.Flat.holderNorm k α (f j) (Work.CR.Flat.polydisc 0 ρ)) ∧
      (∀ f, (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (f j) (Work.CR.Flat.polydisc 0 ρ)) →
        (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 ρ →
          Work.CR.Flat.dbarCoord j (f l) z = Work.CR.Flat.dbarCoord l (f j) z) →
        ContDiffOn ℝ (⊤ : ℕ∞) (T1 f) (Work.CR.Flat.polydisc 0 ρ')) := by
  classical
  obtain ⟨η, hη0, hηhalf, hηrho⟩ := Work.NN.Ratio.exists_eta hn hρ hlt
  have hρ'geo : ∀ j, ρ' j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j :=
    fun j => Work.NN.Ratio.rho''_lt_thre_mul_scale hη0 hηhalf hρ hηrho j
  have hthre_ρ : ∀ j, Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j < ρ j := fun j =>
    lt_of_lt_of_le (mul_lt_mul_of_pos_right (Work.NN.Ratio.thre_lt_thrT hη0)
      (Work.NN.Ratio.scale_pos hη0 hηhalf hρ j)) (le_of_lt (Work.NN.Ratio.thrT_mul_scale_lt hη0 hηhalf hρ j))
  set ρm : Fin n → ℝ := fun j =>
    ρ' j + (Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j - ρ' j) / 2 with hρm
  have hρ'm : ∀ j, ρ' j < ρm j := fun j => by
    rw [hρm]; have := hρ'geo j; simp only; linarith
  have hmgeo : ∀ j, ρm j < Work.NN.Ratio.thre η * Work.NN.Ratio.scale η ρ j := fun j => by
    rw [hρm]; have := hρ'geo j; simp only; linarith
  have hmρ : ∀ j, ρm j < ρ j := fun j => lt_trans (hmgeo j) (hthre_ρ j)
  have hmpos : ∀ j, 0 < ρm j := fun j => lt_trans (hρ' j) (hρ'm j)
  obtain ⟨Cz, hCzpos, hCz⟩ := T1Lin_holderNorm_zero (n := n) (α := α) hα hα1 hη0 hηhalf hρ hmpos hmgeo
  obtain ⟨Co, hCopos, hCo⟩ := dbarOneshotC0 (n := n) hn (c := 0) (ρi := ρ') (ρo := ρm) hρ'm hmpos hα hα1
  have hsum_mono0 : ∀ f : Fin n → (Fin n → ℂ) → ℂ,
      (∑ j, holderNorm 0 α (f j) (polydisc 0 ρm)) ≤ ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
    intro f
    exact Finset.sum_le_sum fun j _ => holderNorm_mono_set (isOpen_polydisc 0 ρ)
      (isOpen_polydisc 0 ρm) (fun z hz l => lt_trans (hz l) (hmρ l)) 0 α (f j)
  have hsum_mono1 : ∀ (k : ℕ) (f : Fin n → (Fin n → ℂ) → ℂ),
      (∑ j, holderNorm k α (f j) (polydisc 0 ρm)) ≤ ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
    intro k f
    exact Finset.sum_le_sum fun j _ => holderNorm_mono_set (isOpen_polydisc 0 ρ)
      (isOpen_polydisc 0 ρm) (fun z hz l => lt_trans (hz l) (hmρ l)) k α (f j)
  -- clause 2
  have hclause2 : ∀ f, (∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ)) →
      (∀ j l z, z ∈ polydisc 0 ρ → dbarCoord j (f l) z = dbarCoord l (f j) z) →
      holderNorm 1 α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ')
        ≤ ENNReal.ofReal (Co * (1 + Cz) + 1) *
            ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by
    intro f hf hfcl
    have hu_sm : ContDiffOn ℝ 1 (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρm) :=
      T1_contDiffOn η hη0 hηhalf hρ hmgeo hf
    have hf_mono : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρm) := fun j =>
      (hf j).mono (polydisc_mono (fun l => le_of_lt (hmρ l)))
    have hfcl_mono : ∀ j l z, z ∈ polydisc 0 ρm →
        dbarCoord l (f j) z = dbarCoord j (f l) z := fun j l z hz =>
      (hfcl j l z (fun m => lt_trans (hz m) (hmρ m))).symm
    have hu_eq : ∀ j (z : Fin n → ℂ), z ∈ polydisc 0 ρm →
        dbarCoord j (T1Lin η hη0 hηhalf hρ f) z = f j z :=
      T1_solves η hη0 hηhalf hρ hmgeo f hf hfcl
    have h1 := hCo (T1Lin η hη0 hηhalf hρ f) f hu_sm hf_mono hfcl_mono hu_eq
    have h2 := hCz f hf
    set S : ℝ≥0∞ := ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) with hS
    have hSm : (∑ j, holderNorm 0 α (f j) (polydisc 0 ρm)) ≤ S := by
      rw [hS]; exact hsum_mono0 f
    have h1S0 : S + ENNReal.ofReal Cz * S = ENNReal.ofReal (1 + Cz) * S := by
      rw [ENNReal.ofReal_add (by norm_num) (le_of_lt hCzpos), ENNReal.ofReal_one,
        add_mul, one_mul]
    calc holderNorm 1 α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ')
        ≤ ENNReal.ofReal Co * ((∑ j, holderNorm 0 α (f j) (polydisc 0 ρm))
            + holderNorm 0 α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρm)) := h1
      _ ≤ ENNReal.ofReal Co * (S + ENNReal.ofReal Cz * S) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hSm ?_) (zero_le : (0 : ℝ≥0∞) ≤ _)
          calc holderNorm 0 α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρm)
              ≤ ENNReal.ofReal Cz * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := h2
            _ = ENNReal.ofReal Cz * S := by rw [hS]
      _ = ENNReal.ofReal (Co * (1 + Cz)) * S := by
          rw [h1S0, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hCopos)]
      _ ≤ ENNReal.ofReal (Co * (1 + Cz) + 1) * S := by
          have h4 : 0 < 1 + Cz := by linarith
          have hle : ENNReal.ofReal (Co * (1 + Cz))
              ≤ ENNReal.ofReal (Co * (1 + Cz) + 1) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hCopos h4])
          exact mul_le_mul_of_nonneg_right hle (zero_le : (0 : ℝ≥0∞) ≤ S)
      _ = ENNReal.ofReal (Co * (1 + Cz) + 1) *
            ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ) := by rw [hS]
  -- clause 3, k ≥ 1
  have hclaim : ∀ (k : ℕ), 1 ≤ k → ∃ c : ℝ, 0 < c ∧
      ∀ (f : Fin n → (Fin n → ℂ) → ℂ),
        (∀ j, ContDiffOn ℝ k (f j) (polydisc 0 ρ)) →
        (∀ j l z, z ∈ polydisc 0 ρ → dbarCoord j (f l) z = dbarCoord l (f j) z) →
        holderNorm (k + 1) α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ')
          ≤ ENNReal.ofReal c * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by
    intro k hk
    obtain ⟨C1, hC1pos, hC1⟩ := dbarOneshotCk (n := n) hn (c := 0) (ρi := ρ') (ρo := ρm)
      hρ'm hmpos hα hα1 k hk
    obtain ⟨C0, hC0pos, hC0⟩ := T1_holderNorm_le (n := n) (α := α) hα hα1 η hη0 hηhalf hρ hmpos hmgeo
    refine ⟨C1 * (1 + C0 k) + 1, ?_, ?_⟩
    · have h4 : 0 < 1 + C0 k := by linarith [hC0pos k]
      nlinarith [hC1pos, h4]
    intro f hf hfcl
    have hf1 : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ) := fun j =>
      (hf j).of_le (by exact_mod_cast hk)
    have hf_mono : ∀ j, ContDiffOn ℝ k (f j) (polydisc 0 ρm) := fun j =>
      (hf j).mono (polydisc_mono (fun l => le_of_lt (hmρ l)))
    have hfcl_mono : ∀ j l z, z ∈ polydisc 0 ρm →
        dbarCoord l (f j) z = dbarCoord j (f l) z := fun j l z hz =>
      (hfcl j l z (fun m => lt_trans (hz m) (hmρ m))).symm
    have hu_sm : ContDiffOn ℝ k (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρm) :=
      T1_contDiffOn η hη0 hηhalf hρ hmgeo hf
    have hu_eq : ∀ j (z : Fin n → ℂ), z ∈ polydisc 0 ρm →
        dbarCoord j (T1Lin η hη0 hηhalf hρ f) z = f j z :=
      T1_solves η hη0 hηhalf hρ hmgeo f hf1 hfcl
    have h1 := hC1 (T1Lin η hη0 hηhalf hρ f) f hu_sm hf_mono hfcl_mono hu_eq
    have h2 := hC0 k hk f hf
    set S : ℝ≥0∞ := ∑ j, holderNorm k α (f j) (polydisc 0 ρ) with hS
    have hSm : (∑ j, holderNorm k α (f j) (polydisc 0 ρm)) ≤ S := by
      rw [hS]; exact hsum_mono1 k f
    have h1S1 : S + ENNReal.ofReal (C0 k) * S = ENNReal.ofReal (1 + C0 k) * S := by
      rw [ENNReal.ofReal_add (by norm_num) (le_of_lt (hC0pos k)), ENNReal.ofReal_one,
        add_mul, one_mul]
    calc holderNorm (k + 1) α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ')
        ≤ ENNReal.ofReal C1 * ((∑ j, holderNorm k α (f j) (polydisc 0 ρm))
            + holderNorm k α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρm)) := h1
      _ ≤ ENNReal.ofReal C1 * (S + ENNReal.ofReal (C0 k) * S) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hSm ?_) (zero_le : (0 : ℝ≥0∞) ≤ _)
          calc holderNorm k α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρm)
              ≤ ENNReal.ofReal (C0 k) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := h2
            _ = ENNReal.ofReal (C0 k) * S := by rw [hS]
      _ = ENNReal.ofReal (C1 * (1 + C0 k)) * S := by
          rw [h1S1, ← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hC1pos)]
      _ ≤ ENNReal.ofReal (C1 * (1 + C0 k) + 1) * S := by
          have h4 : 0 < 1 + C0 k := by linarith [hC0pos k]
          have hle : ENNReal.ofReal (C1 * (1 + C0 k))
              ≤ ENNReal.ofReal (C1 * (1 + C0 k) + 1) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hC1pos h4])
          exact mul_le_mul_of_nonneg_right hle (zero_le : (0 : ℝ≥0∞) ≤ S)
      _ = ENNReal.ofReal (C1 * (1 + C0 k) + 1) *
            ∑ j, holderNorm k α (f j) (polydisc 0 ρ) := by rw [hS]
  refine ⟨T1Lin η hη0 hηhalf hρ,
    fun k => if h : 1 ≤ k then Classical.choose (hclaim k h) else (Co * (1 + Cz) + 1),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : 1 ≤ k
    · show 0 < (if h : 1 ≤ k then Classical.choose (hclaim k h) else (Co * (1 + Cz) + 1))
      rw [dif_pos hk]
      exact (Classical.choose_spec (hclaim k hk)).1
    · show 0 < (if h : 1 ≤ k then Classical.choose (hclaim k h) else (Co * (1 + Cz) + 1))
      rw [dif_neg hk]
      have h4 : 0 < 1 + Cz := by linarith
      nlinarith [hCopos, h4]
  · intro f hf hfcl j z hz
    exact T1_solves η hη0 hηhalf hρ hρ'geo f hf hfcl j z hz
  · intro f hf hfcl
    have h := hclause2 f hf hfcl
    show holderNorm 1 α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ')
        ≤ ENNReal.ofReal (if h : 1 ≤ 0 then Classical.choose (hclaim 0 h)
            else (Co * (1 + Cz) + 1)) * ∑ j, holderNorm 0 α (f j) (polydisc 0 ρ)
    rw [dif_neg (show ¬ (1 ≤ 0) by norm_num)]
    exact h
  · intro k hk f hf hfcl
    have h := (Classical.choose_spec (hclaim k hk)).2 f hf hfcl
    show holderNorm (k + 1) α (T1Lin η hη0 hηhalf hρ f) (polydisc 0 ρ')
        ≤ ENNReal.ofReal (if h : 1 ≤ k then Classical.choose (hclaim k h)
            else (Co * (1 + Cz) + 1)) * ∑ j, holderNorm k α (f j) (polydisc 0 ρ)
    rw [dif_pos hk]
    exact h
  · intro f hf hfcl
    exact T1_contDiffOn_infty η hη0 hηhalf hρ hρ'geo f hf hfcl

end Work.NN.Core
