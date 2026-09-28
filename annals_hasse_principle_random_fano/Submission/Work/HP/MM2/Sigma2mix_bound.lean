import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.FM4.xi_sum_vero
import Submission.Work.HP.MM2.S1ball_le
import Submission.Work.HP.MM2.degen_shell_sum
import Submission.Work.HP.MM2.Sigma2mix_reindex
import Submission.Work.HP.MM2.Sigma2mix_pair_sum_le
import Submission.Work.HP.MM2.Sigma2mix_arith
import Submission.Work.HP.Vero.lam_latOrth_veronese_le
import Submission.Work.HP.Vero.lamR_witness
import Submission.Work.HP.FM3.transf_extreme
import Submission.Work.FM.dual_min_latOrth
import Submission.Work.HP.HP3.dmin_two_singleton_pos
import Submission.Work.HP.HP3.discreteTopology_realify
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MMReindex
import Submission.Work.HP.Sig2.EE_lower

/-!
# `Σ₂^{mix}`, the degenerate part of `D^mix` (node L3d of the N09 design)

`Work.HP.MM2.Sigma2mix_bound` bounds the weighted sum over the pairs `p ∈ Ω(B)` with `x = p.1`
degenerate (`W·λ(x) > A^{3/4}`, `λ(x) = λ_{N-1}(Λ_{ν(x)})`, `W = bigW (wOf B)`) by
`K·mainTerm/A^{1/20}`.

Route (design review §1, node L3d):

* `Sstar 1 (GamMix x y W) (TmixSet y A α) ≤ S1ball d n x A`: the index set of the former is
  contained in that of the latter (`GamMix ⊆ Λ_{ν(x)}`, `TmixSet ⊆ {‖a‖ ≤ A}`,
  `IsPrim a ⟹ a ≠ 0`), with the same weight `‖a‖⁻¹` (`Sigma2mix_reindex`);
* `Ω_bad ⊆ {x bad} × Ξ(B)` and `Σ_{y ∈ Ξ(B)} ‖ν(y)‖⁻¹ ≪ B` (`FM4.xi_sum_vero`), giving the
  weighted sum over the bad `x`;
* `S1ball_le` with `μ = max A (C‖x‖/𝔡₂(x))`, using the key result one vector
  `λ(x) ≤ C‖x‖/𝔡₂(x)`.  That result is reconstructed below from the sorry-free twins
  `Work.HP.Vero.lam_latOrth_veronese_le` (the `Θ`-lift) and `Work.HP.FM3.transf_extreme`
  (the transference bound), because `Work.HP.FM.key_lemma_one_vector` is sorry-tainted and the
  sources of two of its imports have been removed;
* the resulting pair sum is bounded by the single-vector degenerate shells
  (`Sigma2mix_pair_sum_le`, whose proof uses `degen_shell_sum` with `s ∈ {-d, n-1-d, 0}`);
* the exponent arithmetic (`Sigma2mix_arith`), worst case `n = d = 3` with `B`-exponent `-1/3`;
* `B² ≪ E_{d,n}(B)` (`Sig2.EE_lower`) to replace `B²` by `mainTerm`.
-/

set_option autoImplicit false

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## The key result "one vector", reconstructed without the sorry-tainted imports -/

section helpers

/-- `intCastPi` commutes with finite sums of `ℤ`-multiples. -/
private lemma intCastPi_sum_smul {κ ι : Type*} [Fintype κ] [Fintype ι]
    (c : κ → ℤ) (v : κ → ι → ℤ) :
    intCastPi (∑ k, c k • v k) = ∑ k, (c k : ℝ) • intCastPi (v k) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by ext i; simp [intCastPi, zsmul_eq_mul]

/-- `ℤ`-linear independence follows from `ℝ`-linear independence of the realification. -/
private lemma linearIndependent_int_of_intCastPi {κ ι : Type*} [Fintype κ] [Fintype ι]
    {f : κ → ι → ℤ} (h : LinearIndependent ℝ (fun k => intCastPi (f k))) :
    LinearIndependent ℤ f := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have key : ∑ k, (g k : ℝ) • intCastPi (f k) = 0 := by
    rw [← intCastPi_sum_smul g f, hg, map_zero]
  intro k
  exact_mod_cast h _ key k

end helpers

/-- BLBS "key result, one vector", in the form needed by `Sigma2mix_bound`: for primitive `x` the
`(N-1)`-st successive minimum of `Λ_{ν(x)}` is `≤ C‖x‖/𝔡₂(x)`. -/
theorem lamX_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Fin (n + 1) → ℤ, IsPrim x →
      lamX d n x ≤ C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
  have hn1 : 1 ≤ n := by omega
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, hCpos, hC⟩ := FM3.transf_extreme (ι := Fin (n + 1)) n
  refine ⟨C, hCpos, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := Vero.isPrim_ne_zero hx
  have hEx : 0 < eNorm x := eNorm_pos_of_ne_zero hx0
  have hρ_ge : dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) / eNorm x
      ≤ lamR (dualLat (realify (latOrth x))) 1 := Work.FM.dual_min_latOrth n hn1 x hx
  have hdmin_pos : 0 < dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) :=
    HP3.dmin_two_singleton_pos hn1 x hx0
  have hρpos : 0 < lamR (dualLat (realify (latOrth x))) 1 :=
    lt_of_lt_of_le (div_pos hdmin_pos hEx) hρ_ge
  have hrank : n ≤ Module.finrank ℝ
      (Submodule.span ℝ (realify (latOrth x) : Set (Fin (n + 1) → ℝ))) := by
    have h1 : Module.finrank ℤ (latOrth x) = n := by
      rw [Vero.finrank_latOrth x hx0]
      simp [Fintype.card_fin]
    have h2 := Vero.finrank_span_image_intCastPi (latOrth x)
    rw [h1] at h2
    have h3 : Submodule.span ℝ (realify (latOrth x) : Set (Fin (n + 1) → ℝ))
        = Submodule.span ℝ (⇑intCastPi '' (latOrth x : Set (Fin (n + 1) → ℤ))) := by congr 1
    rw [h3, h2]
  obtain ⟨f, hfL, hfLI, hfB⟩ := hC (realify (latOrth x)) (HP3.discreteTopology_realify _) hrank
  have hlamR : lamR (realify (latOrth x)) n
      ≤ C / lamR (dualLat (realify (latOrth x))) 1 := by
    refine csInf_le ⟨0, fun r hr => hr.1⟩ ?_
    exact ⟨div_nonneg (le_of_lt hCpos) (le_of_lt hρpos), f, hfL, hfLI, fun j => by
      rw [le_div_iff₀ hρpos]
      exact hfB j⟩
  have hne : ∃ g' : Fin n → (Fin (n + 1) → ℤ),
      (∀ j, g' j ∈ latOrth x) ∧ LinearIndependent ℤ g' := by
    choose g' hgmem hgeq using fun j => Submodule.mem_map.mp (hfL j)
    refine ⟨g', hgmem, ?_⟩
    have h2 : LinearIndependent ℝ (fun j => intCastPi (g' j)) := by
      have h3 : (fun j => intCastPi (g' j)) = f := funext hgeq
      rw [h3]; exact hfLI
    exact linearIndependent_int_of_intCastPi h2
  obtain ⟨c, hcL, hcLI, hcB⟩ := Vero.lamR_witness (latOrth x) n hne hlamR
  have hlift := Vero.lam_latOrth_veronese_le d n hd1 hn1 x hx
    (C / lamR (dualLat (realify (latOrth x))) 1)
    (div_nonneg (le_of_lt hCpos) (le_of_lt hρpos)) c hcL hcLI hcB
  have hρ : 1 / lamR (dualLat (realify (latOrth x))) 1
      ≤ eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
    rw [div_le_iff₀ hρpos]
    have h := hρ_ge
    rw [div_le_iff₀ hEx] at h
    have h2 : 1 ≤ lamR (dualLat (realify (latOrth x))) 1 * eNorm x
        / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
      rw [le_div_iff₀ hdmin_pos, one_mul]
      exact h
    have h3 : eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))
        * lamR (dualLat (realify (latOrth x))) 1
        = lamR (dualLat (realify (latOrth x))) 1 * eNorm x
          / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by ring
    rw [h3]
    exact h2
  calc lamX d n x
      = lam (latOrth (veronese d n x)) (NN d n - 1) := rfl
    _ ≤ C / lamR (dualLat (realify (latOrth x))) 1 := hlift
    _ = C * (1 / lamR (dualLat (realify (latOrth x))) 1) := by rw [mul_one_div]
    _ ≤ C * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) :=
        mul_le_mul_of_nonneg_left hρ (le_of_lt hCpos)
    _ = C * eNorm x / dmin 2 {x} := by ring

/-! ## The bad set, finsum bookkeeping and the positivity of `ι_{d,n}` -/

section aux

/-- The bad `x`-set of `Σ₂^{mix}`: primitive `x ∈ Ξ(B)` with `W·λ(x) > A^{3/4}`. -/
def BadX (d n : ℕ) (A B : ℝ) : Set (Fin (n + 1) → ℤ) :=
  {x | x ∈ Xi d n B ∧ IsPrim x ∧ A ^ ((3 : ℝ) / 4) < (bigW (wOf B) : ℝ) * lamX d n x}

private lemma sg2_BadX_finite (d n : ℕ) (A B : ℝ) : (BadX d n A B).Finite :=
  (Xi_finite d n B).subset fun _ hx => hx.1

private lemma sg2_finsum_le {α : Type*} {s : Set α} (hs : s.Finite) {f g : α → ℝ}
    (h : ∀ x ∈ s, f x ≤ g x) : (∑ᶠ x ∈ s, f x) ≤ ∑ᶠ x ∈ s, g x := by
  rw [finsum_mem_eq_finite_toFinset_sum f hs, finsum_mem_eq_finite_toFinset_sum g hs]
  exact Finset.sum_le_sum fun i hi => h i (hs.mem_toFinset.mp hi)

private lemma sg2_finsum_mul {α : Type*} {s : Set α} (hs : s.Finite) (c : ℝ) (f : α → ℝ) :
    (∑ᶠ x ∈ s, c * f x) = c * ∑ᶠ x ∈ s, f x := by
  rw [finsum_mem_eq_finite_toFinset_sum (fun x => c * f x) hs,
    finsum_mem_eq_finite_toFinset_sum f hs]
  exact (Finset.mul_sum _ _ _).symm

/-- The volume of the unit ball in `ℝ^R` is positive for `R ≥ 1`. -/
private lemma sg2_ballVol_pos (R : ℕ) (hR : 1 ≤ R) : 0 < ballVol R := by
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
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1), one_pow,
      ENNReal.toReal_ofReal (le_of_lt hg)]
    ring
  rw [h2]; exact hg

/-- The `ζ`-series at an integer `m > 1` is positive. -/
private lemma sg2_zeta_pos (m : ℕ) (hm : 1 < m) : 0 < ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ m := by
  have hsum : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ m) := by
    have hf : Summable (fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ m) := Real.summable_one_div_nat_pow.mpr hm
    have := (summable_nat_add_iff (f := fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ m) 1).mpr hf
    simpa [Nat.cast_add, Nat.cast_one] using this
  exact Summable.tsum_pos hsum (fun i => by positivity) 0 (by norm_num)

/-- `ι_{d,n} = V_{N-2}/(8 ζ(N-2))` is positive for `2 ≤ d ≤ n`. -/
private lemma sg2_iotaDN_pos (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : 0 < iotaDN d n := by
  have h6 := six_le_NN d n hd hdn
  have hN : 1 ≤ NN d n - 2 := by omega
  have hm : 1 < NN d n - 2 := by omega
  unfold iotaDN
  have h1 := sg2_ballVol_pos (NN d n - 2) hN
  have h2 := sg2_zeta_pos (NN d n - 2) hm
  positivity

end aux

/-! ## Assembly -/

/-- (L3d) `Σ₂^{mix}` (upper bound only): `Sstar1 ≤ S1ball(x, A)`; `S1ball_le` with
`μ = max(A, C‖x‖/𝔡₂(x))`; `Σ_y 1/‖ν(y)‖ ≪ B` (`FM4.xi_sum_vero`); `degen_shell_sum` with
`s ∈ {-d, n-1-d, 0}`. Worst exponent (at `n = d = 3`) is `A^{-9/20}`. -/
theorem Sigma2mix_bound (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      Sigma2mix d n A B ≤ K * mainTerm d n A B / A ^ ((1 : ℝ) / 20) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hd1 : 1 ≤ d := by omega
  -- the constant of the key estimate
  obtain ⟨C₀, hC₀pos, hkey₀⟩ := lamX_le d n hd hdn
  set C : ℝ := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hkeyC : ∀ x : Fin (n + 1) → ℤ, IsPrim x →
      lamX d n x ≤ C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by
    intro x hx
    have hm : 0 < dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) :=
      HP3.dmin_two_singleton_pos hn1 x (Vero.isPrim_ne_zero hx)
    have h2 : 0 ≤ eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) :=
      div_nonneg (eNorm_nonneg x) hm.le
    calc lamX d n x ≤ C₀ * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := hkey₀ x hx
      _ = C₀ * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) := by ring
      _ ≤ C * (eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) h2
      _ = C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := by ring
  -- the ingredients
  obtain ⟨K_S, hKSpos, hS1⟩ := S1ball_le d n hd hdn
  obtain ⟨K_R, B_R, hKRpos, hBRpos, hR⟩ := Sigma2mix_reindex d n hd hdn
  obtain ⟨K_P, hKPpos, hP⟩ := Sigma2mix_pair_sum_le d n hd hdn
  obtain ⟨K_E, B_E, hKEpos, hE⟩ := Sig2.EE_lower d n hd hdn h22
  obtain ⟨B_W, hWle⟩ := bigW_le_pow (1 / 16) (by norm_num)
  set Kc : ℝ := max 1 (K_R * K_S * K_P) with hKcdef
  have hKc1 : 1 ≤ Kc := le_max_left _ _
  obtain ⟨K_A, B_A, hKApos, hA⟩ := Sigma2mix_arith d n hd hdn h22 C hC1 Kc hKc1
  have hι : 0 < iotaDN d n := sg2_iotaDN_pos d n hd hdn
  refine ⟨K_A * K_E / (2 * iotaDN d n),
    max (max (max B_R B_A) (max B_E (max B_W (max (C ^ 16) 2)))) 2, ?_⟩
  intro A B hB hAB hAB2
  -- unpack the threshold
  have hM0 : max (max (max B_R B_A) (max B_E (max B_W (max (C ^ 16) 2)))) 2 ≤ B := hB
  have hM : max (max B_R B_A) (max B_E (max B_W (max (C ^ 16) 2))) ≤ B :=
    le_trans (le_max_left _ _) hM0
  have hM1 : max B_R B_A ≤ B := le_trans (le_max_left _ _) hM
  have hBR : B_R ≤ B := le_trans (le_max_left _ _) hM1
  have hBA : B_A ≤ B := le_trans (le_max_right _ _) hM1
  have hM2 : max B_E (max B_W (max (C ^ 16) 2)) ≤ B := le_trans (le_max_right _ _) hM
  have hBE : B_E ≤ B := le_trans (le_max_left _ _) hM2
  have hM3 : max B_W (max (C ^ 16) 2) ≤ B := le_trans (le_max_right _ _) hM2
  have hBW : B_W ≤ B := le_trans (le_max_left _ _) hM3
  have hM4 : max (C ^ 16) 2 ≤ B := le_trans (le_max_right _ _) hM3
  have hC16 : C ^ 16 ≤ B := le_trans (le_max_left _ _) hM4
  have hB2 : (2 : ℝ) ≤ B := le_trans (le_max_right _ _) hM4
  -- elementary consequences
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hA1 : 1 ≤ A := le_trans (Real.one_le_rpow hB1 (by norm_num : (0 : ℝ) ≤ 5 / 6)) hAB
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hA0' : 0 ≤ A := le_trans zero_le_one hA1
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hC0' : 0 ≤ C := le_trans zero_le_one hC1
  have hW1 : 1 ≤ (bigW (wOf B) : ℝ) := by exact_mod_cast one_le_bigW (wOf B)
  have hW0 : 0 < (bigW (wOf B) : ℝ) := lt_of_lt_of_le zero_lt_one hW1
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hlogA : 0 ≤ 1 + Real.log A := by have := Real.log_nonneg hA1; linarith
  have hj1 : (1 : ℝ) ≤ (n : ℝ) + 1 - d := by
    have hdn' : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  -- the two abbreviations `X`, `t`
  set X : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hXdef
  have hX1 : 1 ≤ X := by
    rw [hXdef]
    exact Real.one_le_rpow hB1 (le_of_lt (one_div_pos.mpr (by linarith)))
  have hX0 : 0 ≤ X := le_trans zero_le_one hX1
  set t : ℝ := A ^ ((3 : ℝ) / 4) / (C * (bigW (wOf B) : ℝ)) with htdef
  have hCW0 : 0 < C * (bigW (wOf B) : ℝ) := mul_pos hC0 hW0
  -- `C ≤ B^{1/16}`, `W ≤ B^{1/16}`, hence `t ≥ 1`
  have hC_le : C ≤ B ^ ((1 : ℝ) / 16) := by
    by_contra hcon
    push_neg at hcon
    have h16 : (B ^ ((1 : ℝ) / 16)) ^ 16 = B := by
      rw [← Real.rpow_natCast (B ^ ((1 : ℝ) / 16)) 16, ← Real.rpow_mul hB0.le]
      norm_num
    have h1 : (B ^ ((1 : ℝ) / 16)) ^ 16 < C ^ 16 :=
      pow_lt_pow_left₀ hcon (Real.rpow_nonneg hB0.le _) (by norm_num : (16 : ℕ) ≠ 0)
    rw [h16] at h1
    linarith
  have hW16 : (bigW (wOf B) : ℝ) ≤ B ^ ((1 : ℝ) / 16) := hWle B hBW
  have hCW : C * (bigW (wOf B) : ℝ) ≤ B ^ ((1 : ℝ) / 8) := by
    calc C * (bigW (wOf B) : ℝ) ≤ B ^ ((1 : ℝ) / 16) * B ^ ((1 : ℝ) / 16) :=
          mul_le_mul hC_le hW16 (le_of_lt hW0) (Real.rpow_nonneg hB0.le _)
      _ = B ^ ((1 : ℝ) / 16 + 1 / 16) := (Real.rpow_add hB0 _ _).symm
      _ = B ^ ((1 : ℝ) / 8) := by norm_num
  have ht1 : 1 ≤ t := by
    have hA34 : B ^ ((5 : ℝ) / 8) ≤ A ^ ((3 : ℝ) / 4) := by
      have h1 : (B ^ ((5 : ℝ) / 6)) ^ ((3 : ℝ) / 4) ≤ A ^ ((3 : ℝ) / 4) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hB0.le _) hAB (by norm_num)
      have h2 : (B ^ ((5 : ℝ) / 6)) ^ ((3 : ℝ) / 4) = B ^ ((5 : ℝ) / 8) := by
        rw [← Real.rpow_mul hB0.le]
        norm_num
      rwa [h2] at h1
    have h2 : B ^ ((1 : ℝ) / 8) ≤ B ^ ((5 : ℝ) / 8) :=
      Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
    have h3 : C * (bigW (wOf B) : ℝ) ≤ A ^ ((3 : ℝ) / 4) := le_trans (le_trans hCW h2) hA34
    rw [htdef, le_div_iff₀ hCW0]
    simpa using h3
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  -- the three shells and the arithmetic bracket
  set Y₁ : ℝ := X ^ ((n : ℝ) + 2 - d) * (1 + Real.log X) / t ^ n with hY1def
  set Y₂ : ℝ := X ^ (2 * (n : ℝ) + 1 - d) * (1 + Real.log X) / t ^ n with hY2def
  set Y₃ : ℝ := X ^ ((n : ℝ) + 2) * (1 + Real.log X) / t ^ n with hY3def
  set br : ℝ := (2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * Y₁
      + A ^ (NN d n - n - 1) * C ^ (n - 1) * Y₂
      + A ^ (NN d n - n - 2) * (1 + Real.log A) * Y₃ with hbrdef
  set Tm : (Fin (n + 1) → ℤ) → ℝ := fun x =>
      (A ^ (NN d n - 2) + A ^ (NN d n - n - 1) *
        (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
        eNorm (veronese d n x) + A ^ (NN d n - n - 2) * (1 + Real.log A) with hTmdef
  have hlogX : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX1; linarith
  have hY1nn : 0 ≤ Y₁ := by
    rw [hY1def]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hX0 _) hlogX) (pow_pos ht0 n).le
  have hY2nn : 0 ≤ Y₂ := by
    rw [hY2def]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hX0 _) hlogX) (pow_pos ht0 n).le
  have hY3nn : 0 ≤ Y₃ := by
    rw [hY3def]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hX0 _) hlogX) (pow_pos ht0 n).le
  have hbrNN : 0 ≤ br := by
    rw [hbrdef]
    have h1 : 0 ≤ 2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1) :=
      add_nonneg (mul_nonneg (by norm_num) (pow_nonneg hA0' _))
        (mul_nonneg (pow_nonneg hA0' _) (pow_nonneg hC0' _))
    have h2 : 0 ≤ A ^ (NN d n - n - 1) * C ^ (n - 1) :=
      mul_nonneg (pow_nonneg hA0' _) (pow_nonneg hC0' _)
    have h3 : 0 ≤ A ^ (NN d n - n - 2) * (1 + Real.log A) :=
      mul_nonneg (pow_nonneg hA0' _) hlogA
    linarith [mul_nonneg h1 hY1nn, mul_nonneg h2 hY2nn, mul_nonneg h3 hY3nn]
  -- 1. the reindexing
  have h1 : Sigma2mix d n A B ≤ K_R * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B *
      ∑ᶠ x ∈ BadX d n A B, S1ball d n x A := by
    simpa only [BadX] using hR A B hBR hA1
  -- 2. `S1ball_le` pointwise, summed
  have h2 : (∑ᶠ x ∈ BadX d n A B, S1ball d n x A) ≤ K_S * (∑ᶠ x ∈ BadX d n A B, Tm x) := by
    have hpt : ∀ x ∈ BadX d n A B, S1ball d n x A ≤ K_S * Tm x := by
      intro x hx
      simp only [BadX, Set.mem_setOf_eq] at hx
      simp only [hTmdef]
      exact hS1 x hx.2.1 A (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))))
        hA1 (le_trans hA1 (le_max_left _ _)) (le_trans (hkeyC x hx.2.1) (le_max_right _ _))
    exact le_trans (sg2_finsum_le (sg2_BadX_finite d n A B) hpt)
      (le_of_eq (sg2_finsum_mul (sg2_BadX_finite d n A B) K_S Tm))
  -- 3. the pair-sum bound
  have h3 : (∑ᶠ x ∈ BadX d n A B, Tm x) ≤ K_P * br := by
    have h := hP A B C hA1 hB1 hAB hC1 hkeyC
    dsimp only at h
    rw [← hXdef, ← htdef] at h
    simp only [BadX, hTmdef, hY1def, hY2def, hY3def, hbrdef] at h ⊢
    exact h
  -- 4. the coefficient bookkeeping and the arithmetic step
  have hl4 : 0 ≤ Real.log B * (bigW (wOf B) : ℝ) / 4 :=
    div_nonneg (mul_nonneg hlogB (by positivity)) (by norm_num)
  have hcoef1 : 0 ≤ K_R * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B :=
    mul_nonneg (mul_nonneg hKRpos.le hl4) hB0.le
  have hcoef2 : 0 ≤ K_R * K_S * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B :=
    mul_nonneg (mul_nonneg (mul_nonneg hKRpos.le hKSpos.le) hl4) hB0.le
  have hcoef4 : 0 ≤ (Real.log B * (bigW (wOf B) : ℝ) / 4) * B * br :=
    mul_nonneg (mul_nonneg hl4 hB0.le) hbrNN
  have hKP : K_R * K_S * K_P ≤ Kc := le_max_right _ _
  have hmain4 : Sigma2mix d n A B ≤ K_A * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20) * B ^ 2 := by
    have har := hA A B X t Y₁ Y₂ Y₃ hBA hAB hAB2 hX1 ht1 hXdef htdef
      (le_refl Y₁) (le_refl Y₂) (le_refl Y₃)
    calc Sigma2mix d n A B
        ≤ K_R * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B *
            (∑ᶠ x ∈ BadX d n A B, S1ball d n x A) := h1
      _ ≤ K_R * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B *
            (K_S * (∑ᶠ x ∈ BadX d n A B, Tm x)) := mul_le_mul_of_nonneg_left h2 hcoef1
      _ = K_R * K_S * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B *
            (∑ᶠ x ∈ BadX d n A B, Tm x) := by ring
      _ ≤ K_R * K_S * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B * (K_P * br) :=
          mul_le_mul_of_nonneg_left h3 hcoef2
      _ = K_R * K_S * K_P * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B * br := by ring
      _ ≤ Kc * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B * br := by
          have hthis : K_R * K_S * K_P * ((Real.log B * (bigW (wOf B) : ℝ) / 4) * B * br)
              ≤ Kc * ((Real.log B * (bigW (wOf B) : ℝ) / 4) * B * br) :=
            mul_le_mul_of_nonneg_right hKP hcoef4
          linarith [hthis]
      _ = Kc * (Real.log B * (bigW (wOf B) : ℝ) / 4) * B *
            ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * Y₁
              + A ^ (NN d n - n - 1) * C ^ (n - 1) * Y₂
              + A ^ (NN d n - n - 2) * (1 + Real.log A) * Y₃) := by rw [hbrdef]
      _ ≤ K_A * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20) * B ^ 2 := har
  -- 5. replace `B²` by `mainTerm`
  have hmain : mainTerm d n A B / A ^ ((1 : ℝ) / 20)
      = 2 * iotaDN d n * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20) * EE d n B := by
    have hN2 : 2 ≤ NN d n := le_trans (by norm_num) (six_le_NN d n hd hdn)
    have hpower : A ^ (NN d n - 2) = A ^ ((NN d n : ℝ) - 2) := by
      rw [← Real.rpow_natCast A (NN d n - 2), Nat.cast_sub hN2]
      norm_num
    have hsplitpow : A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20)
        = A ^ ((NN d n : ℝ) - 2) / A ^ ((1 : ℝ) / 20) := Real.rpow_sub hA0 _ _
    rw [mainTerm, hpower, hsplitpow]
    ring
  have hEE : B ^ 2 ≤ K_E * EE d n B := hE B hBE
  have hstep : K_A * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20) * B ^ 2
      ≤ K_A * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20) * (K_E * EE d n B) :=
    mul_le_mul_of_nonneg_left hEE (mul_nonneg hKApos.le (Real.rpow_nonneg hA0.le _))
  calc Sigma2mix d n A B
      ≤ K_A * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20) * B ^ 2 := hmain4
    _ ≤ K_A * A ^ ((NN d n : ℝ) - 2 - (1 : ℝ) / 20) * (K_E * EE d n B) := hstep
    _ = (K_A * K_E / (2 * iotaDN d n)) * mainTerm d n A B / A ^ ((1 : ℝ) / 20) := by
        rw [← mul_div_assoc', hmain]
        field_simp [ne_of_gt hι]

end Work.HP.MM2
