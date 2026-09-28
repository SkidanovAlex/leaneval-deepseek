import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.deg_pair_sum
import Submission.Work.HP.lam_latOrth_veronese_le
import Submission.Work.HP.detGam_pt
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Sig2.log_pow_le_rpow
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.MMReindex
import Submission.Work.HP.HP3.dmin_two_singleton_pos

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## Helper lemmas -/

/-- `detL` is nonnegative (it is a square root). -/
private lemma detL_nonneg' {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) :
    0 ≤ detL L := by
  rw [detL]; exact Real.sqrt_nonneg _

/-- `𝔡_r(S) ≥ 0` (an infimum of nonnegative covolumes). -/
private lemma dmin_nonneg' {ι : Type*} [Fintype ι] (r : ℕ) (S : Set (ι → ℤ)) :
    0 ≤ dmin r S := by
  rw [dmin]
  exact Real.sInf_nonneg (fun D hD => by
    obtain ⟨L, -, -, rfl⟩ := hD
    exact detL_nonneg' L)

/-- Monotonicity of a `finsum` over a set: if `s ⊆ t` and `f ≤ g` on `s`, while `g ≥ 0` on `t`,
then `∑ᶠ a ∈ s, f a ≤ ∑ᶠ a ∈ t, g a`. -/
private lemma finsum_mem_le_of_subset {α : Type*} {s t : Set α} {f g : α → ℝ}
    (hs : s.Finite) (ht : t.Finite)
    (hf : ∀ a ∈ s, 0 ≤ f a) (hg : ∀ a ∈ t, 0 ≤ g a)
    (hst : s ⊆ t) (h : ∀ a ∈ s, f a ≤ g a) :
    (∑ᶠ a ∈ s, f a) ≤ ∑ᶠ a ∈ t, g a := by
  rw [finsum_mem_def, finsum_mem_def]
  refine finsum_le_finsum ?_ ?_ ?_
  · exact hs.subset (fun a ha => by
      by_contra hcon
      rw [Function.mem_support] at ha
      rw [Set.indicator_of_notMem hcon] at ha
      exact ha rfl)
  · exact ht.subset (fun a ha => by
      by_contra hcon
      rw [Function.mem_support] at ha
      rw [Set.indicator_of_notMem hcon] at ha
      exact ha rfl)
  · intro a
    by_cases has : a ∈ s
    · rw [Set.indicator_of_mem has, Set.indicator_of_mem (hst has)]
      exact h a has
    · rw [Set.indicator_of_notMem has]
      by_cases hat : a ∈ t
      · rw [Set.indicator_of_mem hat]
        exact hg a hat
      · rw [Set.indicator_of_notMem hat]

/-- Growth of `bigW (wOf B)`: eventually `W (1 + log B)^3 ≤ 2 B^{1/12}` and
`K₁ n W ≤ B^{5/8}`, with `W = bigW (wOf B)`.  Both follow from `bigW (wOf B) ≤ B^{1/24}` and
`(1 + log B)^3 ≤ B^{1/24}`. -/
private lemma bigW_growth (K₁ : ℝ) (hK₁ : 0 < K₁) (n : ℕ) (hn : 1 ≤ n) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      (bigW (wOf B) : ℝ) * (1 + Real.log B) ^ 3 ≤ 2 * B ^ ((1 : ℝ) / 12) ∧
      K₁ * (n : ℝ) * (bigW (wOf B) : ℝ) ≤ B ^ ((5 : ℝ) / 8) := by
  have hev : ∀ᶠ B : ℝ in Filter.atTop,
      (bigW (wOf B) : ℝ) * (1 + Real.log B) ^ 3 ≤ 2 * B ^ ((1 : ℝ) / 12) ∧
      K₁ * (n : ℝ) * (bigW (wOf B) : ℝ) ≤ B ^ ((5 : ℝ) / 8) := by
    obtain ⟨B₁, hB₁⟩ := bigW_le_pow (1 / 24) (by norm_num)
    obtain ⟨B₂, hB₂1, hB₂⟩ := Sig2.log_pow_le_rpow 3 (1 / 24) (by norm_num)
    filter_upwards [Filter.eventually_ge_atTop B₁, Filter.eventually_ge_atTop B₂,
      Filter.eventually_ge_atTop (1 : ℝ),
      (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 24 by norm_num)).eventually_ge_atTop
        (K₁ * (n : ℝ))]
      with B hBB₁ hBB₂ hB1 hKB
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
    have hBnn : (0 : ℝ) ≤ B := le_of_lt hBpos
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
    have hW : (bigW (wOf B) : ℝ) ≤ B ^ ((1 : ℝ) / 24) := hB₁ B hBB₁
    have hWnn : (0 : ℝ) ≤ (bigW (wOf B) : ℝ) := Nat.cast_nonneg _
    have hlog : (1 + Real.log B) ^ 3 ≤ B ^ ((1 : ℝ) / 24) := by
      have := hB₂ B hBB₂
      simpa [add_comm] using this
    have hlogpos : (0 : ℝ) ≤ (1 + Real.log B) ^ 3 := pow_nonneg (by linarith) 3
    have hB124 : (0 : ℝ) ≤ B ^ ((1 : ℝ) / 24) := Real.rpow_nonneg hBnn _
    have hB112 : (0 : ℝ) ≤ B ^ ((1 : ℝ) / 12) := Real.rpow_nonneg hBnn _
    constructor
    · calc (bigW (wOf B) : ℝ) * (1 + Real.log B) ^ 3
          ≤ B ^ ((1 : ℝ) / 24) * (1 + Real.log B) ^ 3 :=
            mul_le_mul_of_nonneg_right hW hlogpos
        _ ≤ B ^ ((1 : ℝ) / 24) * B ^ ((1 : ℝ) / 24) := mul_le_mul_of_nonneg_left hlog hB124
        _ = B ^ ((1 : ℝ) / 12) := by rw [← Real.rpow_add hBpos]; norm_num
        _ ≤ 2 * B ^ ((1 : ℝ) / 12) := by linarith
    · calc K₁ * (n : ℝ) * (bigW (wOf B) : ℝ)
          ≤ B ^ ((1 : ℝ) / 24) * (bigW (wOf B) : ℝ) := mul_le_mul_of_nonneg_right hKB hWnn
        _ ≤ B ^ ((1 : ℝ) / 24) * B ^ ((1 : ℝ) / 24) := mul_le_mul_of_nonneg_left hW hB124
        _ = B ^ ((1 : ℝ) / 12) := by rw [← Real.rpow_add hBpos]; norm_num
        _ ≤ B ^ ((5 : ℝ) / 8) := Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
  obtain ⟨B₀, hB₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨max B₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun B hB => hB₀ B (le_trans (le_max_left _ _) hB)⟩

/-! ## The main lemma -/

/-- (L3a) Main-term mass of the degenerate pairs: key result one vector
(`λ(x) ≤ C‖x‖/𝔡₂(x)`, so `OmegaBad ⊆ {t𝔡₂(x) ≤ ‖x‖}` with `t = A^{3/4}/(CW)`), `detGam_pt`,
`deg_pair_sum`; `X^{1/n} ≤ B^{1/3} ≤ A^{2/5}`. -/
theorem OmegaBad_mass (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      (∑ᶠ p ∈ OmegaBad d n A B, 1 / detL (Gam d n p.1 p.2))
        ≤ K * B ^ 2 / A ^ ((1 : ℝ) / 4) := by
  -- `n ≥ 3`: for `n = 2` we would have `d = 2`.
  have hn3 : 3 ≤ n := by
    by_contra hcon
    have hd2 : d = 2 := by omega
    have hn2 : n = 2 := by omega
    exact h22 (by rw [hd2, hn2])
  have hn1 : 1 ≤ n := by omega
  -- the three ingredients
  obtain ⟨K₁, hK₁pos, hK₁⟩ := lam_latOrth_veronese_le d n hd hdn
  obtain ⟨C₂, hC₂pos, hC₂⟩ := detGam_pt d n hd
  obtain ⟨C₃, hC₃pos, hC₃⟩ := deg_pair_sum d n hd hdn hn3
  obtain ⟨Bg, hBgpos, hBg⟩ := bigW_growth K₁ hK₁pos n hn1
  refine ⟨2 * C₂ * C₃ * K₁ * (n : ℝ), max Bg (max ((2 : ℝ) ^ (n + 1)) 1), by positivity, ?_⟩
  intro A B hB hA56 hAB2
  have hBBg : Bg ≤ B := le_trans (le_max_left _ _) hB
  have hB2n : (2 : ℝ) ^ (n + 1) ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB1 : (1 : ℝ) ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hBnn : (0 : ℝ) ≤ B := le_of_lt hBpos
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  obtain ⟨hgro, hK1nW⟩ := hBg B hBBg
  have hdn' : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    linarith
  have hWpos : 0 < (bigW (wOf B) : ℝ) := by
    have := one_le_bigW (wOf B)
    exact_mod_cast (show 0 < bigW (wOf B) by omega)
  have hWnn : (0 : ℝ) ≤ (bigW (wOf B) : ℝ) := le_of_lt hWpos
  have hApos : 0 < A := lt_of_lt_of_le (Real.rpow_pos_of_pos hBpos ((5 : ℝ) / 6)) hA56
  have hAnn : (0 : ℝ) ≤ A := le_of_lt hApos
  -- the two parameters of the comparison set
  set X : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hXdef
  set T : ℝ := A ^ ((3 : ℝ) / 4) / (K₁ * (n : ℝ) * (bigW (wOf B) : ℝ)) with hTdef
  -- `2 ≤ X`
  have hX2 : 2 ≤ X := by
    rw [hXdef]
    have hmn : (0 : ℝ) < (n : ℝ) + 1 - d := by linarith
    have hc1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1 - d) :=
      one_div_le_one_div_of_le hmn (by linarith)
    have hceil : (2 : ℝ) ≤ B ^ ((1 : ℝ) / ((n : ℝ) + 1)) := by
      have h1 : (2 : ℝ) ^ ((n : ℝ) + 1) ≤ B := by
        have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        have hnat : (2 : ℝ) ^ (((n + 1 : ℕ)) : ℝ) = (2 : ℝ) ^ (n + 1) :=
          Real.rpow_natCast 2 (n + 1)
        rw [← hcast, hnat]
        exact hB2n
      have h2 : ((2 : ℝ) ^ ((n : ℝ) + 1)) ^ ((1 : ℝ) / ((n : ℝ) + 1))
          ≤ B ^ ((1 : ℝ) / ((n : ℝ) + 1)) :=
        Real.rpow_le_rpow (by positivity) h1 (by positivity)
      have h3 : ((2 : ℝ) ^ ((n : ℝ) + 1)) ^ ((1 : ℝ) / ((n : ℝ) + 1)) = 2 := by
        rw [← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
        have hone : ((n : ℝ) + 1) * ((1 : ℝ) / ((n : ℝ) + 1)) = 1 := by field_simp
        rw [hone, Real.rpow_one]
      linarith [h2, h3]
    exact le_trans hceil (Real.rpow_le_rpow_of_exponent_le hB1 hc1)
  -- `1 ≤ T`
  have hA34 : B ^ ((5 : ℝ) / 8) ≤ A ^ ((3 : ℝ) / 4) := by
    have h1 : (B ^ ((5 : ℝ) / 6)) ^ ((3 : ℝ) / 4) ≤ A ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hBnn _) hA56 (by norm_num)
    have h2 : (B ^ ((5 : ℝ) / 6)) ^ ((3 : ℝ) / 4) = B ^ ((5 : ℝ) / 8) := by
      rw [← Real.rpow_mul hBnn]; norm_num
    rwa [h2] at h1
  have hT1 : 1 ≤ T := by
    rw [hTdef, le_div_iff₀ (by positivity)]
    have := le_trans hK1nW hA34
    linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  -- the comparison set and its finiteness
  set S : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
      {p | LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ X ∧ eNorm p.2 ≤ X ∧
          T * dmin 2 ({p.1} : Set (Fin (n + 1) → ℤ)) ≤ eNorm p.1} with hSdef
  have hSfin : S.Finite := by
    rw [hSdef]
    exact ((finite_of_eNorm_le (ι := Fin (n + 1)) X).prod
      (finite_of_eNorm_le (ι := Fin (n + 1)) X)).subset
        (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)
  have hOBfin : (OmegaBad d n A B).Finite :=
    (Omega_finite (d := d) (n := n) B).subset (fun p hp => hp.1)
  -- pointwise bound from `detGam_pt`
  have hpt : ∀ p ∈ OmegaBad d n A B,
      1 / detL (Gam d n p.1 p.2) ≤
        C₂ * (1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))) := by
    intro p hp
    obtain ⟨hOm, -⟩ := hp
    obtain ⟨hxX, hyX, hxy, hxyn⟩ := hOm
    obtain ⟨hxprim, -⟩ := hxX
    obtain ⟨hyprim, -⟩ := hyX
    have h := (hC₂ p.1 p.2 hxprim hyprim hxy hxyn).1
    have hz : C₂ / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * eNorm p.1 ^ (d - 1)
              * eNorm p.2 ^ (d - 1))
        = C₂ * (1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
              eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))) := by rw [div_eq_mul_one_div]
    rw [hz] at h
    exact h
  -- membership in the comparison set
  have hsub : OmegaBad d n A B ⊆ S := by
    intro p hp
    obtain ⟨hOm, hbad⟩ := hp
    obtain ⟨hxX, hyX, hxy, hxyn⟩ := hOm
    obtain ⟨hxprim, hxe⟩ := hxX
    obtain ⟨hyprim, hye⟩ := hyX
    have hx0 : p.1 ≠ 0 := isPrim_ne_zero hxprim
    have hd2pos : 0 < dmin 2 ({p.1} : Set (Fin (n + 1) → ℤ)) :=
      HP3.dmin_two_singleton_pos hn1 p.1 hx0
    have hlt : A ^ ((3 : ℝ) / 4) < (bigW (wOf B) : ℝ) * lamX d n p.1 := lt_of_not_ge hbad
    rw [lamX] at hlt
    have h2 := hK₁ p.1 hxprim
    have h3 : (bigW (wOf B) : ℝ) * lam (latOrth (veronese d n p.1)) (NN d n - 1)
        ≤ (bigW (wOf B) : ℝ) *
          (K₁ * ((n : ℝ) * eNorm p.1 / dmin 2 ({p.1} : Set (Fin (n + 1) → ℤ)))) :=
      mul_le_mul_of_nonneg_left h2 hWnn
    have h4 := lt_of_lt_of_le hlt h3
    have h5 : (bigW (wOf B) : ℝ) *
          (K₁ * ((n : ℝ) * eNorm p.1 / dmin 2 ({p.1} : Set (Fin (n + 1) → ℤ))))
        = ((bigW (wOf B) : ℝ) * K₁ * (n : ℝ) * eNorm p.1)
          / dmin 2 ({p.1} : Set (Fin (n + 1) → ℤ)) := by ring
    rw [h5] at h4
    have h6 : A ^ ((3 : ℝ) / 4) * dmin 2 ({p.1} : Set (Fin (n + 1) → ℤ))
        < (bigW (wOf B) : ℝ) * K₁ * (n : ℝ) * eNorm p.1 :=
      (lt_div_iff₀ hd2pos).mp h4
    have hpos : 0 < K₁ * (n : ℝ) * (bigW (wOf B) : ℝ) := by positivity
    rw [hSdef]
    refine ⟨Sig2.li_of_prim_ne_pm p.1 p.2 hxprim hyprim hxy hxyn, hxe, hye, ?_⟩
    rw [hTdef, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith [h6]
  -- monotonicity and the constant
  have hstep1 : (∑ᶠ p ∈ OmegaBad d n A B, 1 / detL (Gam d n p.1 p.2))
      ≤ ∑ᶠ p ∈ S, C₂ * (1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))) :=
    finsum_mem_le_of_subset hOBfin hSfin
      (fun p _ => div_nonneg zero_le_one (detL_nonneg' _))
      (fun p _ => mul_nonneg hC₂pos.le (div_nonneg zero_le_one
        (mul_nonneg (mul_nonneg (dmin_nonneg' 2 _) (pow_nonneg (eNorm_nonneg _) _))
          (pow_nonneg (eNorm_nonneg _) _))))
      hsub hpt
  have hstep2 : (∑ᶠ p ∈ S, C₂ * (1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))))
      = C₂ * ∑ᶠ p ∈ S, 1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1)) :=
    (mul_finsum_mem' (s := S) (fun p => 1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))) C₂ hSfin).symm
  -- the pair sum
  have hpair : (∑ᶠ p ∈ S, 1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
          eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1)))
      ≤ C₃ * X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3 / T := by
    have h := hC₃ X T hX2 hT1
    rwa [← hSdef] at h
  have hsum3 : (∑ᶠ p ∈ OmegaBad d n A B, 1 / detL (Gam d n p.1 p.2))
      ≤ C₂ * (C₃ * X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3 / T) := by
    calc (∑ᶠ p ∈ OmegaBad d n A B, 1 / detL (Gam d n p.1 p.2))
        ≤ ∑ᶠ p ∈ S, C₂ * (1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
            eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))) := hstep1
      _ = C₂ * ∑ᶠ p ∈ S, 1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) *
            eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1)) := hstep2
      _ ≤ C₂ * (C₃ * X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3 / T) :=
          mul_le_mul_of_nonneg_left hpair hC₂pos.le
  -- arithmetic
  have hA12 : B ^ ((5 : ℝ) / 12) ≤ A ^ ((1 : ℝ) / 2) := by
    have h1 : (B ^ ((5 : ℝ) / 6)) ^ ((1 : ℝ) / 2) ≤ A ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hBnn _) hA56 (by norm_num)
    have h2 : (B ^ ((5 : ℝ) / 6)) ^ ((1 : ℝ) / 2) = B ^ ((5 : ℝ) / 12) := by
      rw [← Real.rpow_mul hBnn]; norm_num
    rwa [h2] at h1
  have hE : X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ))
      = B ^ (2 + 1 / ((n : ℝ) * ((n : ℝ) + 1 - d))) := by
    rw [hXdef, ← Real.rpow_mul hBnn]
    congr 1
    have h1 : ((n : ℝ) + 1 - d) ≠ 0 := by linarith
    have h2 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    field_simp
    try ring
  have hX1 : (1 : ℝ) ≤ X := by
    rw [hXdef]
    exact Real.one_le_rpow hB1 (div_nonneg zero_le_one (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1 - d))
  have hlogX : (1 + Real.log X) ^ 3 ≤ (1 + Real.log B) ^ 3 := by
    have hlogXle : Real.log X ≤ Real.log B := by
      rw [hXdef, Real.log_rpow hBpos]
      have hmn : (0 : ℝ) < (n : ℝ) + 1 - d := by linarith
      have he1 : (1 : ℝ) / ((n : ℝ) + 1 - d) ≤ 1 := by
        rw [div_le_one hmn]; linarith
      nlinarith [hlogB]
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hX1, hlogXle, hlogB])
      (by linarith [hlogXle]) 3
  have hc13 : (1 : ℝ) / ((n : ℝ) * ((n : ℝ) + 1 - d)) ≤ 1 / 3 := by
    have hn3' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hmn : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1 - d) := by
      have h3 : (0 : ℝ) < (n : ℝ) + 1 - d := by linarith
      positivity
    rw [div_le_div_iff₀ hmn (by norm_num : (0 : ℝ) < 3)]
    have hm3 : 3 ≤ (n : ℝ) * ((n : ℝ) + 1 - d) := by
      have h2 : (1 : ℝ) ≤ (n : ℝ) + 1 - d := by linarith
      nlinarith
    linarith
  have hkey1 : X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3
      * (bigW (wOf B) : ℝ) ≤ 2 * B ^ 2 * A ^ ((1 : ℝ) / 2) := by
    have hB2c : 0 ≤ B ^ (2 + 1 / ((n : ℝ) * ((n : ℝ) + 1 - d))) := Real.rpow_nonneg hBnn _
    have hLW : (1 + Real.log X) ^ 3 * (bigW (wOf B) : ℝ) ≤ 2 * B ^ ((1 : ℝ) / 12) := by
      calc (1 + Real.log X) ^ 3 * (bigW (wOf B) : ℝ)
          ≤ (1 + Real.log B) ^ 3 * (bigW (wOf B) : ℝ) :=
            mul_le_mul_of_nonneg_right hlogX hWnn
        _ = (bigW (wOf B) : ℝ) * (1 + Real.log B) ^ 3 := by ring
        _ ≤ 2 * B ^ ((1 : ℝ) / 12) := hgro
    have hB2eq : B ^ 2 = B ^ (2 : ℝ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hstep : X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3
        * (bigW (wOf B) : ℝ) ≤ 2 * B ^ (2 : ℝ) * A ^ ((1 : ℝ) / 2) := by
      calc X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3
            * (bigW (wOf B) : ℝ)
          = B ^ (2 + 1 / ((n : ℝ) * ((n : ℝ) + 1 - d)))
            * ((1 + Real.log X) ^ 3 * (bigW (wOf B) : ℝ)) := by rw [hE]; ring
        _ ≤ B ^ (2 + 1 / ((n : ℝ) * ((n : ℝ) + 1 - d))) * (2 * B ^ ((1 : ℝ) / 12)) :=
            mul_le_mul_of_nonneg_left hLW hB2c
        _ = 2 * (B ^ (2 + 1 / ((n : ℝ) * ((n : ℝ) + 1 - d))) * B ^ ((1 : ℝ) / 12)) := by ring
        _ = 2 * B ^ (2 + 1 / ((n : ℝ) * ((n : ℝ) + 1 - d)) + (1 : ℝ) / 12) := by
            rw [← Real.rpow_add hBpos]
        _ ≤ 2 * B ^ ((29 : ℝ) / 12) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
        _ = 2 * (B ^ (2 : ℝ) * B ^ ((5 : ℝ) / 12)) := by
            rw [← Real.rpow_add hBpos]; norm_num
        _ = 2 * B ^ (2 : ℝ) * B ^ ((5 : ℝ) / 12) := by ring
        _ ≤ 2 * B ^ (2 : ℝ) * A ^ ((1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left hA12 (by positivity)
    rw [hB2eq]
    exact hstep
  have hkey2 : X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3
        * (bigW (wOf B) : ℝ) / A ^ ((3 : ℝ) / 4) ≤ 2 * B ^ 2 / A ^ ((1 : ℝ) / 4) := by
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hApos _) (Real.rpow_pos_of_pos hApos _)]
    have hA34eq : A ^ ((3 : ℝ) / 4) = A ^ ((1 : ℝ) / 2) * A ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hApos]; norm_num
    calc X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3
          * (bigW (wOf B) : ℝ) * A ^ ((1 : ℝ) / 4)
        ≤ (2 * B ^ 2 * A ^ ((1 : ℝ) / 2)) * A ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hkey1 (Real.rpow_nonneg hAnn _)
      _ = (2 * B ^ 2) * A ^ ((3 : ℝ) / 4) := by rw [hA34eq]; ring
  have hTeq : C₂ * (C₃ * X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3 / T)
      = (C₂ * C₃ * K₁ * (n : ℝ)) *
        (X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3
          * (bigW (wOf B) : ℝ) / A ^ ((3 : ℝ) / 4)) := by
    rw [hTdef]
    field_simp
    try ring
  calc (∑ᶠ p ∈ OmegaBad d n A B, 1 / detL (Gam d n p.1 p.2))
      ≤ C₂ * (C₃ * X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3 / T) :=
        hsum3
    _ = (C₂ * C₃ * K₁ * (n : ℝ)) *
        (X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3
          * (bigW (wOf B) : ℝ) / A ^ ((3 : ℝ) / 4)) := hTeq
    _ ≤ (C₂ * C₃ * K₁ * (n : ℝ)) * (2 * B ^ 2 / A ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left hkey2 (by positivity)
    _ = 2 * C₂ * C₃ * K₁ * (n : ℝ) * B ^ 2 / A ^ ((1 : ℝ) / 4) := by ring

end Work.HP.MM2
