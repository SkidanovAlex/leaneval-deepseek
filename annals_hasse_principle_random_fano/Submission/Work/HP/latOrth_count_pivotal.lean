import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.FM.veronese_lat
import Submission.Work.HP.Vero.finrank_latOrth

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Auxiliary: explicit vectors in `Λ_c` and the rank of `Λ_c`

For primitive `c` and any `i₀` with `c i₀ ≠ 0`, the `card ι - 1` vectors
`c i₀ • eᵢ - cᵢ • e_{i₀}` (`i ≠ i₀`) are ℤ-independent elements of `Λ_c`; consequently
`rk (latOrth c) ≥ card ι - 1`, so that the hypothesis `lam (latOrth c) (card ι - 1) ≤ T`
is not vacuous and can be unfolded into explicit witnesses.
(Not needed for the proof of `latOrth_count_pivotal` below, which uses the rank formula
`Vero.finrank_latOrth` instead.) -/

private lemma dotZ_sub (x y b : ι → ℤ) : dotZ (x - y) b = dotZ x b - dotZ y b := by
  simp only [dotZ, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma dotZ_single_one (i : ι) (x : ι → ℤ) : dotZ (Pi.single i (1 : ℤ)) x = x i := by
  rw [dotZ, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_apply, if_neg hj, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The vector `c i₀ • eᵢ - cᵢ • e_{i₀}`. -/
def wvec (c : ι → ℤ) (i₀ i : ι) : ι → ℤ :=
  c i₀ • (Pi.single i (1 : ℤ)) - c i • (Pi.single i₀ (1 : ℤ))

lemma dotZ_wvec (c : ι → ℤ) (i₀ i : ι) : dotZ (wvec c i₀ i) c = 0 := by
  rw [wvec, dotZ_sub, dotZ_smul, dotZ_smul, dotZ_single_one, dotZ_single_one]
  ring

lemma wvec_mem_latOrth (c : ι → ℤ) (i₀ i : ι) : wvec c i₀ i ∈ latOrth c := by
  rw [mem_latOrth]
  exact dotZ_wvec c i₀ i

lemma wvec_coord {c : ι → ℤ} (i₀ i : ι) {j : ι} (hj : j ≠ i₀) :
    wvec c i₀ i j = c i₀ * (if j = i then 1 else 0) := by
  simp only [wvec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [if_neg hj]
  ring

/-- The vectors `c i₀ • eᵢ - cᵢ • e_{i₀}` (`i ≠ i₀`) are ℤ-linearly independent when `c i₀ ≠ 0`. -/
lemma linearIndependent_wvec (c : ι → ℤ) (i₀ : ι) (h : c i₀ ≠ 0) :
    LinearIndependent ℤ (fun i : {i : ι // i ≠ i₀} => wvec c i₀ i) := by
  rw [linearIndependent_iff']
  intro s g hg j hj
  have hcoord : ((∑ i ∈ s, g i • wvec c i₀ i) : ι → ℤ) j = g j * c i₀ := by
    rw [Finset.sum_apply]
    have hterm : ∀ i ∈ s, (g i • wvec c i₀ i) j = g i * c i₀ * (if j = i then 1 else 0) := by
      intro i _
      have h1 : wvec c i₀ (i : ι) (j : ι) = c i₀ * (if (j : ι) = (i : ι) then 1 else 0) :=
        wvec_coord (c := c) i₀ (i : ι) j.2
      rw [Pi.smul_apply, smul_eq_mul, h1]
      simp only [Subtype.coe_inj]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single j]
    · rw [if_pos rfl, mul_one]
    · intro b _ hb; rw [if_neg (fun h : j = b => hb h.symm), mul_zero]
    · intro hjs; exact absurd hj hjs
  have h0 : ((∑ i ∈ s, g i • wvec c i₀ i) : ι → ℤ) j = 0 := by rw [hg]; rfl
  have hzero : g j * c i₀ = 0 := hcoord.symm.trans h0
  rcases mul_eq_zero.mp hzero with h1 | h1
  · exact h1
  · exact absurd h1 h

/-- `rk (latOrth c) ≥ card ι - 1` for primitive `c`. -/
lemma card_sub_one_le_rk_latOrth (c : ι → ℤ) (hc : IsPrim c) :
    Fintype.card ι - 1 ≤ rk (latOrth c) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    refine isPrim_ne_zero hc (funext fun i => ?_)
    exact not_not.mp (not_exists.mp h i)
  have hli : LinearIndependent ℤ (fun i : {i : ι // i ≠ i₀} => wvec c i₀ i) :=
    linearIndependent_wvec c i₀ hi₀
  have hli' : LinearIndependent ℤ
      (fun i : {i : ι // i ≠ i₀} => (⟨wvec c i₀ i, wvec_mem_latOrth c i₀ i⟩ : latOrth c)) := by
    refine LinearIndependent.of_comp (Submodule.subtype (latOrth c)) ?_
    have : (Submodule.subtype (latOrth c)) ∘
        (fun i : {i : ι // i ≠ i₀} => (⟨wvec c i₀ i, wvec_mem_latOrth c i₀ i⟩ : latOrth c))
        = fun i : {i : ι // i ≠ i₀} => wvec c i₀ i := rfl
    rw [this]
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  rw [Fintype.card_subtype_compl (fun i : ι => i = i₀), Fintype.card_subtype_eq] at hcard
  exact hcard

/-- Witnesses for `lam`: from `lam (latOrth c) (card ι - 1) ≤ T` (`T ≥ 1`) we get `card ι - 1`
independent vectors of `Λ_c` of norm at most `2T`. -/
theorem lam_latOrth_witness (c : ι → ℤ) (hc : IsPrim c) {T : ℝ} (hT : 1 ≤ T)
    (hlam : lam (latOrth c) (Fintype.card ι - 1) ≤ T) :
    ∃ v : Fin (Fintype.card ι - 1) → ι → ℤ,
      (∀ i, v i ∈ latOrth c) ∧ LinearIndependent ℤ v ∧ ∀ i, eNorm (v i) ≤ 2 * T :=
  lam_witness (latOrth c) (card_sub_one_le_rk_latOrth c hc) (by linarith)

/-! ## The counting lemma

The proof combines three ingredients that are available in the workspace.

* `Sig2.schmidt_bound` (Schmidt's bound, product form):
  `#(L ∩ B(T)) ≤ K · ∏_{i < rk L} (T/λ_{i+1}(L) + 1)` for `T ≥ 1`.
* `lam_mono`/`lam_pos`: `λ_i(L) ≤ λ_R(L) ≤ T` and `λ_i(L) > 0` for `1 ≤ i ≤ R = rk L`.
  Hence each factor is `≤ 2T/λ_i`, and the product is `≤ 2^R T^R/∏_i λ_i`.
* `FM.minkowski_lower`: `detL L ≤ ∏_{i < rk L} λ_{i+1}(L)` (the elementary half of Minkowski's
  second theorem), so `2^R T^R/∏_i λ_i ≤ 2^R T^R/detL L`.
* `FM.detL_latOrth_of_prim` and `Vero.finrank_latOrth`: `detL (latOrth c) = ‖c‖` and
  `rk (latOrth c) = card ι - 1` for primitive `c`, giving the exponent `card ι - 1` and the
  normalisation by `‖c‖`. -/

theorem latOrth_count_pivotal (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ι → ℤ), IsPrim c → ∀ T : ℝ, 1 ≤ T →
      lam (latOrth c) (Fintype.card ι - 1) ≤ T →
      (ballCount (latOrth c) T : ℝ) ≤ K * T ^ (Fintype.card ι - 1) / eNorm c := by
  classical
  obtain ⟨K, hKpos, hK⟩ := Sig2.schmidt_bound (ι := ι)
  refine ⟨K * 2 ^ Fintype.card ι, by positivity, ?_⟩
  intro c hc T hT hlam
  have hc0 : c ≠ 0 := isPrim_ne_zero hc
  have hec : 0 < eNorm c := eNorm_pos_of_ne_zero hc0
  set R : ℕ := Fintype.card ι - 1 with hR
  have hrk : rk (latOrth c) = R := by
    simp only [hR, rk]
    exact Vero.finrank_latOrth c hc0
  have hdet : detL (latOrth c) = eNorm c := FM.detL_latOrth_of_prim c hc
  have hdetpos : 0 < detL (latOrth c) := lt_of_lt_of_le zero_lt_one (Lat.detL_ge_one _)
  have hlamR : lam (latOrth c) R ≤ T := by rw [hR]; exact hlam
  have hmink : detL (latOrth c) ≤ ∏ i ∈ Finset.range R, lam (latOrth c) (i + 1) := by
    have := FM.minkowski_lower (latOrth c)
    rwa [hrk] at this
  have hb : (ballCount (latOrth c) T : ℝ)
      ≤ K * ∏ i ∈ Finset.range R, (T / lam (latOrth c) (i + 1) + 1) := by
    have := hK (latOrth c) T hT
    rwa [hrk] at this
  -- each factor is at most `2T/λ`
  have hfac : ∀ i ∈ Finset.range R,
      T / lam (latOrth c) (i + 1) + 1 ≤ 2 * T / lam (latOrth c) (i + 1) := by
    intro i hi
    have h1 : i + 1 ≤ R := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have hle : lam (latOrth c) (i + 1) ≤ T :=
      (lam_mono _ h1 (by rw [hrk])).trans hlamR
    have hpos : 0 < lam (latOrth c) (i + 1) := lam_pos _ (by omega) (by rw [hrk]; exact h1)
    have hone : 1 ≤ T / lam (latOrth c) (i + 1) := (one_le_div hpos).mpr hle
    calc T / lam (latOrth c) (i + 1) + 1 ≤ T / lam (latOrth c) (i + 1) + T / lam (latOrth c) (i + 1) :=
          by linarith
      _ = 2 * T / lam (latOrth c) (i + 1) := by ring
  have hprod : ∏ i ∈ Finset.range R, (T / lam (latOrth c) (i + 1) + 1)
      ≤ 2 ^ R * T ^ R / ∏ i ∈ Finset.range R, lam (latOrth c) (i + 1) := by
    have hstep : ∏ i ∈ Finset.range R, (T / lam (latOrth c) (i + 1) + 1)
        ≤ ∏ i ∈ Finset.range R, (2 * T / lam (latOrth c) (i + 1)) := by
      refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => hfac i hi)
      have hpos : 0 < lam (latOrth c) (i + 1) :=
        lam_pos _ (by omega) (by rw [hrk]; exact Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      have : 0 ≤ T / lam (latOrth c) (i + 1) := div_nonneg (by linarith) hpos.le
      linarith
    refine hstep.trans (le_of_eq ?_)
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, mul_pow]
  calc (ballCount (latOrth c) T : ℝ)
      ≤ K * ∏ i ∈ Finset.range R, (T / lam (latOrth c) (i + 1) + 1) := hb
    _ ≤ K * (2 ^ R * T ^ R / ∏ i ∈ Finset.range R, lam (latOrth c) (i + 1)) :=
        mul_le_mul_of_nonneg_left hprod hKpos.le
    _ ≤ K * (2 ^ R * T ^ R / detL (latOrth c)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKpos.le
        exact div_le_div_of_nonneg_left (by positivity) hdetpos hmink
    _ = K * (2 ^ R * T ^ R / eNorm c) := by rw [hdet]
    _ ≤ (K * 2 ^ Fintype.card ι) * T ^ R / eNorm c := by
        have h2le : (2 : ℝ) ^ R ≤ 2 ^ Fintype.card ι :=
          pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
        calc K * (2 ^ R * T ^ R / eNorm c) = K * 2 ^ R * T ^ R / eNorm c := by ring
          _ ≤ K * 2 ^ Fintype.card ι * T ^ R / eNorm c := by
              refine div_le_div_of_nonneg_right ?_ hec.le
              have hTnn : (0 : ℝ) ≤ T ^ R := pow_nonneg (by linarith) _
              have := mul_le_mul_of_nonneg_right h2le hTnn
              nlinarith [hKpos.le, this]

end Work.HP
