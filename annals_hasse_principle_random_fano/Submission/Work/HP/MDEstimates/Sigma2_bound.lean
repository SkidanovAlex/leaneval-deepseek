import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDBasic.nonneg_basic
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.Sig2.EE_lower
import Submission.Work.HP.Sig2.Sigma2_caseF
import Submission.Work.HP.Sig2.Sigma2_caseI

/-!
# `Work.HP.MDEstimates.Sigma2_bound`

The large-`μ` half `Σ^{(2)}` of the second moment of `N_V(B)`, Browning--Le Boudec--Sawin,
*The Hasse principle for random Fano hypersurfaces*, Annals 2023, Lemma D:

`Σ^{(2)}_{d,n}(A,B) ≤ K · mainTerm_{d,n}(A,B) / A^{1/3}` for `(d,n) ∉ {(2,2),(3,3),(4,4)}`.

The analytic content (the two halves `𝔡₂/𝔡₃ ≤ ‖x‖‖y‖/𝔡₂²` and its complement, each bounded by
`K A^{N-2-1/3} B²`) is delegated to `Work.HP.Sig2.Sigma2_caseF` and
`Work.HP.Sig2.Sigma2_caseI`; the lower bound `B² ≪ E_{d,n}(B)` to `Work.HP.Sig2.EE_lower`.
This file assembles them:

`Σ^{(2)} = ¼ (Σ_ℱ + Σ_ℐ) ≤ ¼(K₁+K₂)A^{N-2-1/3}B² ≤ ((K₁+K₂)K₃/(8ι))·mainTerm/A^{1/3}`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset MeasureTheory
open scoped BigOperators

namespace Work.HP.MDEstimates
open Work.HP

/-! ## Positivity of `ι_{d,n}` -/

/-- The volume of the unit ball in `ℝ^R` is positive for `R ≥ 1`. -/
private lemma ballVol_pos (R : ℕ) (hR : 1 ≤ R) : 0 < ballVol R := by
  haveI : Nonempty (Fin R) := ⟨⟨0, by omega⟩⟩
  have hg : 0 < Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1) := by
    have h1 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h2 : 0 < Real.Gamma ((R : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
    positivity
  have h := EuclideanSpace.volume_closedBall (Fin R) (0 : EuclideanSpace ℝ (Fin R)) 1
  simp only [Fintype.card_fin] at h
  have h2 : ballVol R = Real.sqrt Real.pi ^ R / Real.Gamma ((R : ℝ) / 2 + 1) := by
    unfold ballVol
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1), one_pow,
      ENNReal.toReal_ofReal (le_of_lt hg)]
    ring
  rw [h2]; exact hg

/-- The `ζ`-series at an integer `m > 1` is positive. -/
private lemma zeta_tail_pos (m : ℕ) (hm : 1 < m) : 0 < ∑' k : ℕ, (1:ℝ) / ((k : ℝ) + 1) ^ m := by
  have hsum : Summable (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1) ^ m) := by
    have hf : Summable (fun j : ℕ => (1:ℝ) / (j : ℝ) ^ m) := Real.summable_one_div_nat_pow.mpr hm
    have := (summable_nat_add_iff (f := fun j : ℕ => (1:ℝ) / (j : ℝ) ^ m) 1).mpr hf
    simpa [Nat.cast_add, Nat.cast_one] using this
  exact Summable.tsum_pos hsum (fun i => by positivity) 0 (by norm_num)

/-- `ι_{d,n} = V_{N-2}/(8 ζ(N-2))` is positive for `2 ≤ d ≤ n`. -/
private lemma iotaDN_pos (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : 0 < iotaDN d n := by
  have h6 := Work.HP.six_le_NN d n hd hdn
  have hN : 1 ≤ NN d n - 2 := by omega
  have hm : 1 < NN d n - 2 := by omega
  unfold iotaDN
  have h1 := ballVol_pos (NN d n - 2) hN
  have h2 := zeta_tail_pos (NN d n - 2) hm
  positivity

/-! ## Assembly -/

theorem Sigma2_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) (h44 : (d, n) ≠ (4, 4)) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      Sigma2 d n A B ≤ K * mainTerm d n A B / A ^ ((1 : ℝ) / 3) := by
  obtain ⟨K₁, B₁, hK₁, hF⟩ := Work.HP.Sig2.Sigma2_caseF d n hd hdn h22 h33 h44
  obtain ⟨K₂, B₂, hK₂, hI⟩ := Work.HP.Sig2.Sigma2_caseI d n hd hdn h22 h33 h44
  obtain ⟨K₃, B₃, hK₃, hEE⟩ := Work.HP.Sig2.EE_lower d n hd hdn h22
  have hic : 0 < iotaDN d n := iotaDN_pos d n hd hdn
  refine ⟨(K₁ + K₂) * K₃ / (8 * iotaDN d n), max (max B₁ B₂) (max B₃ 2) + 1, ?_⟩
  intro A B hB hAB hAB2
  have hBmax : max (max B₁ B₂) (max B₃ 2) ≤ B :=
    le_trans (le_add_of_nonneg_right zero_le_one) hB
  have hBB₁ : B₁ ≤ B := le_trans (le_trans (le_max_left B₁ B₂) (le_max_left _ _)) hBmax
  have hBB₂ : B₂ ≤ B := le_trans (le_trans (le_max_right B₁ B₂) (le_max_left _ _)) hBmax
  have hBB₃ : B₃ ≤ B := le_trans (le_trans (le_max_left B₃ 2) (le_max_right _ _)) hBmax
  have hB2 : (2:ℝ) ≤ B := le_trans (le_trans (le_max_right B₃ 2) (le_max_right _ _)) hBmax
  have hBpos : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hApos : 0 < A := lt_of_lt_of_le (div_pos hBpos hlogB) hAB
  have hK12 : 0 < K₁ + K₂ := by linarith
  -- the two halves of the `μ > A` range
  set t₁ : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    {p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A) ∧
      dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
        ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2)} with ht₁
  set t₂ : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    {p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A) ∧
      ¬ (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
        ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2))} with ht₂
  have hsfin : ({p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A)} :
      Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))).Finite :=
    (MDBasic.finite_sets d n A B (fun _ => True)).2.2.subset (fun p hp => hp.1)
  have ht₁fin : t₁.Finite := hsfin.subset (fun p hp => by
    rw [ht₁] at hp
    exact ⟨hp.1, hp.2.1⟩)
  have ht₂fin : t₂.Finite := hsfin.subset (fun p hp => by
    rw [ht₂] at hp
    exact ⟨hp.1, hp.2.1⟩)
  have hunion : ({p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A)} :
      Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))) = t₁ ∪ t₂ := by
    rw [ht₁, ht₂]
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))
            * dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * (eNorm p.1 * eNorm p.2)
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, h⟩
    · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩) <;> exact ⟨h1, h2⟩
  have hdisj : Disjoint t₁ t₂ := by
    rw [ht₁, ht₂, Set.disjoint_left]
    rintro p ⟨_, _, h⟩ ⟨_, _, h'⟩
    exact h' h
  have hsplit : (∑ᶠ p ∈ ({p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A)} :
        Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))), pairS0 d n A p)
      = (∑ᶠ p ∈ t₁, pairS0 d n A p) + (∑ᶠ p ∈ t₂, pairS0 d n A p) := by
    rw [hunion, finsum_mem_union hdisj ht₁fin ht₂fin]
  have hcase₁ : (∑ᶠ p ∈ t₁, pairS0 d n A p)
      ≤ K₁ * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
    rw [ht₁]
    exact hF A B hBB₁ hAB hAB2
  have hcase₂ : (∑ᶠ p ∈ t₂, pairS0 d n A p)
      ≤ K₂ * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
    rw [ht₂]
    exact hI A B hBB₂ hAB hAB2
  have hsum : (∑ᶠ p ∈ ({p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A)} :
        Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))), pairS0 d n A p)
      ≤ (K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by
    rw [hsplit]
    calc (∑ᶠ p ∈ t₁, pairS0 d n A p) + (∑ᶠ p ∈ t₂, pairS0 d n A p)
        ≤ K₁ * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2
          + K₂ * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := add_le_add hcase₁ hcase₂
      _ = (K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2 := by ring
  have hEEB : B ^ 2 ≤ K₃ * EE d n B := hEE B hBB₃
  have hexp : ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) = ((NN d n : ℝ) - 2) - ((1 : ℝ) / 3) := rfl
  have hN2 : 2 ≤ NN d n := le_trans (by norm_num) (Work.HP.six_le_NN d n hd hdn)
  have hpower : A ^ (NN d n - 2) = A ^ ((NN d n : ℝ) - 2) := by
    rw [← Real.rpow_natCast A (NN d n - 2), Nat.cast_sub hN2]
    norm_num
  have hsplitpow : A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3)
      = A ^ ((NN d n : ℝ) - 2) / A ^ ((1 : ℝ) / 3) := by
    rw [Real.rpow_sub hApos]
  have hmain : mainTerm d n A B / A ^ ((1 : ℝ) / 3)
      = 2 * iotaDN d n * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * EE d n B := by
    rw [mainTerm, hpower, hsplitpow]
    ring
  have hpow_nonneg : 0 ≤ A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) := Real.rpow_nonneg hApos.le _
  have hgoal : Sigma2 d n A B
      ≤ ((K₁ + K₂) * K₃ / (8 * iotaDN d n)) * (mainTerm d n A B / A ^ ((1 : ℝ) / 3)) := by
    rw [Sigma2, hmain]
    have h1 : (1 / 4 : ℝ) * (∑ᶠ p ∈ ({p | p ∈ Omega d n B ∧ ¬ (muXY n p.1 p.2 ≤ A)} :
          Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ))), pairS0 d n A p)
        ≤ (1 / 4 : ℝ) * ((K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    have h2 : (1 / 4 : ℝ) * ((K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2)
        ≤ (1 / 4 : ℝ)
            * ((K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * (K₃ * EE d n B)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hb : (K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2
          ≤ (K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * (K₃ * EE d n B) := by
        have hm1 : (K₁ + K₂) * B ^ 2 ≤ (K₁ + K₂) * (K₃ * EE d n B) :=
          mul_le_mul_of_nonneg_left hEEB hK12.le
        have hm2 := mul_le_mul_of_nonneg_left hm1 hpow_nonneg
        calc (K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * B ^ 2
            = A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * ((K₁ + K₂) * B ^ 2) := by ring
          _ ≤ A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * ((K₁ + K₂) * (K₃ * EE d n B)) := hm2
          _ = (K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * (K₃ * EE d n B) := by ring
      exact hb
    have h3 : (1 / 4 : ℝ)
          * ((K₁ + K₂) * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * (K₃ * EE d n B))
        = ((K₁ + K₂) * K₃ / (8 * iotaDN d n))
            * (2 * iotaDN d n * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 3) * EE d n B) := by
      field_simp
      ring
    linarith [h1, h2, h3]
  rw [mul_div_assoc]
  exact hgoal

end Work.HP.MDEstimates
