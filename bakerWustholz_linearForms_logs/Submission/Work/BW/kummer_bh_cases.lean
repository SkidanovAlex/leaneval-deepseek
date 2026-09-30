import Mathlib
import Submission.Work.BW.kummer_state
import Submission.Work.BW.kummer_bh_data
import Submission.Work.BW.kummer_cond_unimodular
import Submission.Work.BW.kummer_modifiedHeight_le
import Submission.Work.BW.kummer_log_norm_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# BW §9: the two final cases

Given a state of the Kummer descent (see `Submission.Work.BW.kummer_state`) satisfying the
Kummer condition, we build the basic hypothesis `BH`: either directly from the state (case
`2^v ≤ c`) or from the Minkowski-reduced basis (case `2^v > c`).
-/

namespace Work.BW

open Complex
open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-! ### The product of BW's weights -/

private lemma prod_range_two (m : ℕ) :
    ∏ k ∈ Finset.range m, ((k:ℝ)+2) = ((m+1).factorial : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      have hfac : ((m+1)+1).factorial = ((m+1)+1) * (m+1).factorial :=
        Nat.factorial_succ (m+1)
      rw [hfac]
      push_cast
      ring

private lemma prod_range_weight (n : ℕ) :
    ∏ k ∈ Finset.range n, max (1:ℝ) (((k:ℝ)+1)/2) = (n.factorial : ℝ) / 2^(n-1) := by
  rcases n with _ | m
  · simp
  · rw [Finset.prod_range_succ']
    have h0 : max (1:ℝ) ((((0:ℕ):ℝ)+1)/2) = 1 := by norm_num
    rw [h0, mul_one]
    have hcongr : ∏ k ∈ Finset.range m, max (1:ℝ) ((((k+1:ℕ):ℝ)+1)/2)
        = ∏ k ∈ Finset.range m, (((k:ℝ)+2)/2) := by
      apply Finset.prod_congr rfl
      intro k _
      have hk2 : (1:ℝ) ≤ ((k:ℝ)+2)/2 := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      have hke : ((↑(k+1) + 1)/2 : ℝ) = ((k:ℝ)+2)/2 := by push_cast; ring
      rw [hke, max_eq_right hk2]
    rw [hcongr, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, prod_range_two m]
    simp

/-- BW §9: `∏_j σ_j = (n!/2^{n-1}) ∏_j h'(α_j)`. -/
theorem sig_prod (φ : K →+* ℂ) (α : Fin n → K) :
    ∏ j, sig φ α j = ((n.factorial : ℝ) / 2^(n-1)) * ∏ j, hp φ (α j) := by
  have hsig : ∀ j : Fin n, sig φ α j = max (1:ℝ) (((j:ℝ)+1)/2) * hp φ (α j) := by
    intro j
    rw [sig, max_mul_of_nonneg (1:ℝ) (((j:ℝ)+1)/2) (le_of_lt (hp_pos φ (α j))), one_mul]
  calc ∏ j, sig φ α j
      = ∏ j : Fin n, (max (1:ℝ) ((((j : ℕ) : ℝ)+1)/2) * hp φ (α j)) :=
        Finset.prod_congr rfl (fun j _ => hsig j)
    _ = (∏ j : Fin n, max (1:ℝ) (((j:ℝ)+1)/2)) * ∏ j, hp φ (α j) :=
        Finset.prod_mul_distrib
    _ = ((n.factorial : ℝ) / 2^(n-1)) * ∏ j, hp φ (α j) := by
        rw [Fin.prod_univ_eq_prod_range (α := ℝ) (fun k => max (1:ℝ) (((k:ℝ)+1)/2)) n,
            prod_range_weight n]

/-! ### Linear independence of the columns of an integral matrix -/

lemma linearIndependent_cols_of_det_ne_zero {M : Matrix (Fin n) (Fin n) ℤ} (h : M.det ≠ 0) :
    LinearIndependent ℚ (fun j i => (M i j : ℚ)) := by
  have h' : ((Int.castRingHom ℚ).mapMatrix M).det ≠ 0 := by
    rw [← RingHom.map_det]
    exact Int.cast_ne_zero.mpr h
  have hinj : Function.Injective ((Int.castRingHom ℚ).mapMatrix M).mulVec :=
    (Matrix.mulVec_injective_iff_isUnit).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h'))
  have hcol := (Matrix.mulVec_injective_iff).mp hinj
  have h2 : ((Int.castRingHom ℚ).mapMatrix M).col = fun j i => (M i j : ℚ) := by
    funext j i
    simp only [Matrix.col_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    rfl
  rwa [h2] at hcol

lemma det_ne_zero_of_inv {M : Matrix (Fin n) (Fin n) ℤ} (h : M.det ≠ 0) :
    M.det ≠ 0 := h

/-! ### The bound on `‖lamP‖` -/

lemma lamP_norm_le (φ : K →+* ℂ) (α : Fin n → K) (v : ℕ) (L : Fin n → ℤ) (j : Fin n)
    (c : ℝ) (hc : (((2:ℝ)^v)⁻¹) * ∑ i, |(L i : ℝ)| * hp φ (α i) ≤ c) :
    ‖lamP φ α v (fun _ i => L i) j‖ ≤ (Module.finrank ℚ K : ℝ) * c := by
  have hd : (0:ℝ) ≤ (Module.finrank ℚ K : ℝ) := by positivity
  have h1 : ‖lamP φ α v (fun _ i => L i) j‖
      ≤ (((2:ℝ)^v)⁻¹) * ∑ i, |(L i : ℝ)| * ‖Complex.log (φ (α i))‖ := by
    rw [lamP]
    have h2 : ‖(((2:ℂ)^v)⁻¹)‖ = (((2:ℝ)^v)⁻¹) := by
      rw [norm_inv, norm_pow]
      norm_num
    rw [norm_mul, h2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ‖∑ i, (L i : ℂ) * Complex.log (φ (α i))‖
        ≤ ∑ i, ‖(L i : ℂ) * Complex.log (φ (α i))‖ := norm_sum_le _ _
      _ = ∑ i, |(L i : ℝ)| * ‖Complex.log (φ (α i))‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, Complex.norm_intCast]
  refine le_trans h1 ?_
  have h3 : ∀ i : Fin n, |(L i : ℝ)| * ‖Complex.log (φ (α i))‖
      ≤ |(L i : ℝ)| * ((Module.finrank ℚ K : ℝ) * hp φ (α i)) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h' := log_div_le_hp φ (α i)
    rw [div_le_iff₀ (by exact_mod_cast Module.finrank_pos : (0:ℝ) < _)] at h'
    simpa [mul_comm] using h'
  calc (((2:ℝ)^v)⁻¹) * ∑ i, |(L i : ℝ)| * ‖Complex.log (φ (α i))‖
      ≤ (((2:ℝ)^v)⁻¹) * ∑ i, |(L i : ℝ)| * ((Module.finrank ℚ K : ℝ) * hp φ (α i)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h3 i) (by positivity)
    _ = (((2:ℝ)^v)⁻¹) * ((Module.finrank ℚ K : ℝ) * ∑ i, |(L i : ℝ)| * hp φ (α i)) := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = (Module.finrank ℚ K : ℝ) * ((((2:ℝ)^v)⁻¹) * ∑ i, |(L i : ℝ)| * hp φ (α i)) := by ring
    _ ≤ (Module.finrank ℚ K : ℝ) * c := mul_le_mul_of_nonneg_left hc hd

/-! ### BW §9: the two cases -/

theorem kummer_case1_state {φ : K →+* ℂ} {α : Fin n → K} (hn : 0 < n) (hα : ∀ i, α i ≠ 0)
    (b : Fin n → ℤ) {s : KSt K n} (hs : Inv φ α s) (hK : KummerCond s.β)
    (c : ℝ) (hc : (2:ℝ)^s.v ≤ c) :
    ∃ (L : Fin n → Fin n → ℤ) (α' : Fin n → K) (σ : Fin n → ℝ),
      BH φ α b s.v c n L α' σ := by
  have hdet : s.m.det ≠ 0 := by
    rw [kummer_state_det hs]
    exact pow_ne_zero _ (by norm_num)
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨fun j i => s.m i j, s.β, sig φ α, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact linearIndependent_cols_of_det_ne_zero hdet
  · have htop := LinearIndependent.span_eq_top_of_card_eq_finrank
      (linearIndependent_cols_of_det_ne_zero hdet) (by simp [Module.finrank_fin_fun])
    rw [htop]
    exact Submodule.mem_top
  · intro j; exact ⟨hs.beta_ne j, hs.exp_eq j⟩
  · exact hK
  · intro j; exact sig_pos φ α j
  · intro j
    have h1d : 1 / (Module.finrank ℚ K : ℝ) ≤ sig φ α j :=
      le_trans (one_div_finrank_le_hp φ (α j)) (hp_le_sig φ α j)
    have hX : ((((2:ℝ)^s.v)⁻¹) * ∑ i, |(s.m i j : ℝ)| * hp φ (α i)) ≤ sig φ α j := by
      have h1 : ∑ i, |(s.m i j : ℝ)| * hp φ (α i) ≤ (2:ℝ)^s.v * sig φ α j := hs.colsum j
      calc (((2:ℝ)^s.v)⁻¹) * ∑ i, |(s.m i j : ℝ)| * hp φ (α i)
          ≤ (((2:ℝ)^s.v)⁻¹) * ((2:ℝ)^s.v * sig φ α j) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = sig φ α j := by
            rw [← mul_assoc, inv_mul_cancel₀ (by positivity : ((2:ℝ)^s.v) ≠ 0), one_mul]
    have hh := kummer_modifiedHeight_le φ α hα (fun i => s.m i j) s.v (s.β j)
      (hs.beta_ne j) (hs.exp_eq j)
    have hmodle : BakerWustholz.modifiedHeight φ (s.β j) ≤ sig φ α j :=
      le_trans hh (max_le h1d hX)
    have hA : Height.logHeight₁ (s.β j) / (Module.finrank ℚ K : ℝ) ≤ sig φ α j :=
      le_trans (le_max_left _ _) hmodle
    have hB : ‖lamP φ α s.v (fun j i => s.m i j) j‖ / (Module.finrank ℚ K : ℝ) ≤ sig φ α j := by
      rw [div_le_iff₀ (by exact_mod_cast Module.finrank_pos : (0:ℝ) < Module.finrank ℚ K)]
      rw [mul_comm]
      exact lamP_norm_le φ α s.v (fun i => s.m i j) j (sig φ α j) hX
    show hmod (s.β j) (lamP φ α s.v (fun j i => s.m i j) j) ≤ sig φ α j
    rw [show hmod (s.β j) (lamP φ α s.v (fun j i => s.m i j) j)
        = max (Height.logHeight₁ (s.β j) / (Module.finrank ℚ K : ℝ))
            (max (‖lamP φ α s.v (fun j i => s.m i j) j‖ / (Module.finrank ℚ K : ℝ))
              (1 / (Module.finrank ℚ K : ℝ))) from rfl]
    exact max_le hA (max_le hB h1d)
  · intro j; exact hs.colsum j
  · have hk : kappa n (Module.finrank ℚ K) n s.v c = ((n.factorial : ℝ) / 2^(n-1)) := by
      rw [kappa]
      have h1 : ((64 : ℝ) * n * (Module.finrank ℚ K : ℝ)) ^ (n - n) = 1 := by
        rw [Nat.sub_self, pow_zero]
      rw [h1, one_mul]
      have h2 : min (c / (2:ℝ)^s.v) 1 = 1 := by
        rw [min_eq_right]
        rw [le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^s.v)]
        simpa using hc
      rw [h2, mul_one]
    rw [sig_prod φ α, hk]

theorem kummer_case2_state {φ : K →+* ℂ} {α : Fin n → K} (hn : 0 < n) (hα : ∀ i, α i ≠ 0)
    (hind : LinearIndependent ℚ (fun i => Complex.log (φ (α i))))
    (c' : ℝ) (hc' : 1 < c')
    (hLeh : ∀ (β : K) (ℓ : ℂ), β ≠ 0 → Complex.exp ℓ = φ β → ℓ ≠ 0 →
      1 < c' * max (Height.logHeight₁ β) ‖ℓ‖)
    (b : Fin n → ℤ) {s : KSt K n} (hs : Inv φ α s) (hK : KummerCond s.β)
    (hc : c' ^ n * (n.factorial : ℝ) < (2:ℝ)^s.v) :
    ∃ (L : Fin n → Fin n → ℤ) (α' : Fin n → K) (σ : Fin n → ℝ),
      BH φ α b s.v (c' ^ n * (n.factorial : ℝ)) n L α' σ := by
  obtain ⟨U, μ, hU, hμpos, hμdef, hμlow, hexp, hh, hprod⟩ :=
    kummer_minkowski_data hn hα hind c' hc' hLeh hs
  have hdet : s.m.det ≠ 0 := by
    rw [kummer_state_det hs]
    exact pow_ne_zero _ (by norm_num)
  have hdet2 : (s.m * U).det ≠ 0 := by
    rw [Matrix.det_mul]
    rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> simp [hdet]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨fun j i => (s.m * U) i j, fun j => ∏ l, (s.β l) ^ (U l j), fun j => c' * μ j,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact linearIndependent_cols_of_det_ne_zero hdet2
  · have htop := LinearIndependent.span_eq_top_of_card_eq_finrank
      (linearIndependent_cols_of_det_ne_zero hdet2) (by simp [Module.finrank_fin_fun])
    rw [htop]
    exact Submodule.mem_top
  · intro j
    exact ⟨Finset.prod_ne_zero_iff.mpr fun l _ => zpow_ne_zero _ (hs.beta_ne l), hexp j⟩
  · exact kummer_cond_unimodular s.β hK U hU
  · intro j; exact mul_pos (lt_trans zero_lt_one hc') (hμpos j)
  · intro j
    have hd : (0:ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
    have hA : Height.logHeight₁ (∏ l, (s.β l) ^ (U l j)) / (Module.finrank ℚ K : ℝ)
        ≤ c' * μ j :=
      le_trans (le_max_left _ _) (hh j)
    have hμeq : (((2:ℝ)^s.v)⁻¹) * ∑ i, |((s.m * U) i j : ℝ)| * hp φ (α i) ≤ μ j := by
      rw [← hμdef j]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity : ((2:ℝ)^s.v) ≠ 0), one_mul]
    have hB : ‖lamP φ α s.v (fun j i => (s.m * U) i j) j‖ / (Module.finrank ℚ K : ℝ)
        ≤ c' * μ j := by
      have h2 : ‖lamP φ α s.v (fun j i => (s.m * U) i j) j‖ ≤ (Module.finrank ℚ K : ℝ) * μ j :=
        lamP_norm_le φ α s.v (fun i => (s.m * U) i j) j (μ j) hμeq
      have h3 : (Module.finrank ℚ K : ℝ) * μ j ≤ (Module.finrank ℚ K : ℝ) * (c' * μ j) :=
        mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_left (le_of_lt (hμpos j)) (le_of_lt hc')) (le_of_lt hd)
      rw [div_le_iff₀ hd]
      calc ‖lamP φ α s.v (fun j i => (s.m * U) i j) j‖ ≤ (Module.finrank ℚ K : ℝ) * μ j := h2
        _ ≤ (Module.finrank ℚ K : ℝ) * (c' * μ j) := h3
        _ = (c' * μ j) * (Module.finrank ℚ K : ℝ) := by ring
    have hC : 1 / (Module.finrank ℚ K : ℝ) ≤ c' * μ j := by
      have h1 := hμlow j
      rw [div_lt_iff₀ (mul_pos (lt_trans zero_lt_one hc') hd)] at h1
      rw [div_le_iff₀ hd]
      nlinarith [h1, hd, lt_trans zero_lt_one hc', hμpos j]
    show hmod (∏ l, (s.β l) ^ (U l j)) (lamP φ α s.v (fun j i => (s.m * U) i j) j) ≤ c' * μ j
    rw [show hmod (∏ l, (s.β l) ^ (U l j)) (lamP φ α s.v (fun j i => (s.m * U) i j) j)
        = max (Height.logHeight₁ (∏ l, (s.β l) ^ (U l j)) / (Module.finrank ℚ K : ℝ))
            (max (‖lamP φ α s.v (fun j i => (s.m * U) i j) j‖ / (Module.finrank ℚ K : ℝ))
              (1 / (Module.finrank ℚ K : ℝ))) from rfl]
    exact max_le hA (max_le hB hC)
  · intro j
    rw [show (∑ i, |((fun j i => (s.m * U) i j) j i : ℝ)| * BakerWustholz.modifiedHeight φ (α i))
        = (2:ℝ)^s.v * μ j from (hμdef j).symm]
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (le_of_lt (hμpos j)) (le_of_lt hc')) (by positivity)
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hk : kappa n (Module.finrank ℚ K) n s.v (c' ^ n * (n.factorial : ℝ))
        = ((n.factorial : ℝ) / 2^(n-1)) * ((c' ^ n * (n.factorial : ℝ)) / (2:ℝ)^s.v) := by
      rw [kappa]
      have h1 : ((64 : ℝ) * n * (Module.finrank ℚ K : ℝ)) ^ (n - n) = 1 := by
        rw [Nat.sub_self, pow_zero]
      rw [h1, one_mul]
      have h2 : min ((c' ^ n * (n.factorial : ℝ)) / (2:ℝ)^s.v) 1
          = (c' ^ n * (n.factorial : ℝ)) / (2:ℝ)^s.v := by
        rw [min_eq_left]
        rw [div_le_one (by positivity : (0:ℝ) < (2:ℝ)^s.v)]
        exact le_of_lt hc
      rw [h2]
    rw [hk]
    have h2 : ((n.factorial : ℝ) / 2^(n-1)) * ((c' ^ n * (n.factorial : ℝ)) / (2:ℝ)^s.v)
          * ∏ i, hp φ (α i)
        = c' ^ n * (((n.factorial : ℝ)^2 / 2^(n-1)) * (((2:ℝ)^s.v)⁻¹) * ∏ i, hp φ (α i)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hprod (le_of_lt (pow_pos (lt_trans zero_lt_one hc') n))

end Work.BW
