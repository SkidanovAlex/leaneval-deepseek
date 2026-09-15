/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Projection
import Submission.Vinogradov.TentShift
import Submission.Commons.Analysis.MomentCurve.gammaDeriv_taylor_tail

/-!
# The `H`-ball sits inside a fixed multiple of the polar plate

GLYZ (arXiv:1912.09798) Lemma 3.8 step 2 needs the containment

  `B_H(0, δ^{-b'l}) ⊆ C · 𝒰^o_{I'}`   (`H = V^{k-l}(ξ')^⊥`, `r = δ^{-(k-l+1)b} = |I'|^{-(k-l+1)}`),

which is what makes the `I'`-factor `(|f_{I'}|^{p_k-p_l} ∗ ϕ_{I'})` essentially constant on the
translate ball.  The content is the **vanishing order** of the projected derivative vectors:

  `Π_H γ^{(m)}(c) = O(|c - ξ'|^{k-l+1-m})`   for `1 ≤ m ≤ k-l`,

because `γ^{(m)}(ξ') ∈ V^{k-l}(ξ')` for `m ≤ k-l`, while `‖Π_H γ^{(m)}(c)‖ = O(1)` for `m > k-l`.

The two inequalities combine (with `d = plateHalf m' ≈ |I'|/2` and `r = (1/d)^{k-l+1}`) to give
`d^m |⟪Ψ w, γ^{(m)}(c')⟫| ≤ ρ` for `‖w‖ ≤ r`, i.e. `gauge (plateGaugeLin k d c' (Ψ w)) ≤ ρ` with
`ρ` a fixed constant depending only on `k` and `l`.  That is `gauge_plateGaugeLin_projEmbed_le`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Submission.Vinogradov

/-! ## 1. Elementary bounds for the moment curve -/

/-- The `m`-th derivative vector of the moment curve is bounded by `k!` on the unit interval. -/
lemma norm_gam_le_factorial (k : ℕ) {t : ℝ} (ht : |t| ≤ 1) (m : ℕ) :
    ‖Commons.Analysis.MomentCurve.gam k t m‖ ≤ (k.factorial : ℝ) := by
  rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
  intro j
  rw [Real.norm_eq_abs, Commons.Analysis.MomentCurve.gam_apply, abs_mul]
  have hj : j.val + 1 ≤ k := by have := j.isLt; omega
  have hdesc : (((j.val + 1).descFactorial m : ℕ) : ℝ) ≤ (k.factorial : ℝ) := by
    refine le_trans (Nat.cast_le.mpr ?_) (Nat.cast_le.mpr (Nat.factorial_le hj))
    by_cases hm : m ≤ j.val + 1
    · rw [Nat.descFactorial_eq_div hm]; exact Nat.div_le_self _ _
    · rw [not_le] at hm
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr hm]; exact Nat.zero_le _
  have hp : |t ^ (j.val + 1 - m)| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg t) ht
  have hk0 : (0 : ℝ) ≤ (k.factorial : ℝ) := Nat.cast_nonneg _
  calc |(((j.val + 1).descFactorial m : ℕ) : ℝ)| * |t ^ (j.val + 1 - m)|
      = (((j.val + 1).descFactorial m : ℕ) : ℝ) * |t ^ (j.val + 1 - m)| := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (k.factorial : ℝ) * 1 := mul_le_mul hdesc hp (abs_nonneg _) hk0
    _ = (k.factorial : ℝ) := by ring

lemma norm_gammaDeriv_le (k : ℕ) {t : ℝ} (ht : |t| ≤ 1) (m : ℕ) :
    ‖gammaDeriv k m t‖ ≤ Real.sqrt k * (k.factorial : ℝ) := by
  rw [gammaDeriv_eq_lpSymm_gam]
  exact le_trans (norm_lpSymm_le k _) (mul_le_mul_of_nonneg_left
    (norm_gam_le_factorial k ht m) (Real.sqrt_nonneg k))

/-! ## 2. The projected derivative vectors of order `≤ k - l` vanish at `ξ'` -/

lemma projMapLin_gammaDeriv_eq_zero {k l : ℕ} (hlk : l ≤ k) {ξ' : ℝ}
    {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ k - l) :
    projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m ξ') = 0 := by
  have hmem : gammaDeriv k m ξ' ∈ torsionSpan k l ξ' := by
    rw [torsionSpan]
    refine Submodule.subset_span ⟨⟨m - 1, by omega⟩, ?_⟩
    simp only []
    congr 1
    omega
  have hinner : ∀ i : Fin l, ⟪torsionVec k l hlk ξ' i, gammaDeriv k m ξ'⟫ = 0 := by
    intro i
    have hb : torsionVec k l hlk ξ' i ∈ torsionCompl k l ξ' := by
      simp only [torsionVec]
      exact (torsionBasis k l hlk ξ' i).2
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal (torsionSpan k l ξ') (torsionVec k l hlk ξ' i)).mp hb
      (gammaDeriv k m ξ') hmem
  ext i
  rw [projMapLin_apply_coord]
  exact hinner i

/-! ## 3. The vanishing order of the projected derivative vectors -/

/-- **The vanishing order**: for `1 ≤ m ≤ k-l`, the projection of `γ^{(m)}(c)` onto `H`
vanishes to order `k-l+1-m` at `ξ'`. -/
theorem norm_projMapLin_gammaDeriv_le {k l : ℕ} (hlk : l ≤ k) {ξ' : ℝ}
    (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → m ≤ k - l → ∀ c ∈ Set.Icc (0 : ℝ) 1,
      ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c)‖
        ≤ C * |c - ξ'| ^ (k - l + 1 - m) := by
  refine ⟨((k : ℝ) + 1) * (Real.sqrt k * (k.factorial : ℝ)) + 1, by positivity, ?_⟩
  intro m hm1 hmkl c hc
  have hc1 : |c| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hc.1], hc.2⟩
  have hξ'1 : |ξ'| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hξ'.1], hξ'.2⟩
  have hint : |c - ξ'| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, hξ'.1, hξ'.2]
  -- expand the derivative vector around `ξ'`
  have hexp : gammaDeriv k m c
      = ∑ e ∈ Finset.range (k + 1),
          ((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ' := by
    have h : c = ξ' + (c - ξ') := by ring
    rw [h, gammaDeriv_eq_lpSymm_gam, Commons.Analysis.MomentCurve.gam_add]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [gammaDeriv_eq_lpSymm_gam]
    norm_num
  rw [hexp, map_sum]
  -- the surviving index set
  set S : Finset ℕ := (Finset.range (k + 1)).filter (fun e => k - l - m < e) with hS
  have hsplit : ∑ e ∈ Finset.range (k + 1),
        projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ')
      = ∑ e ∈ S, projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ') := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro e he hes
    have hes2 : e ≤ k - l - m := by
      by_contra hcon
      exact hes (Finset.mem_filter.mpr ⟨he, Nat.lt_of_not_le hcon⟩)
    have hme : m + e ≤ k - l := by
      have h1 : m + e ≤ m + (k - l - m) := Nat.add_le_add_left hes2 m
      have h2 : m + (k - l - m) = k - l := Nat.add_sub_of_le hmkl
      omega
    rw [map_smul, projMapLin_gammaDeriv_eq_zero hlk (by omega) hme, smul_zero]
  rw [hsplit]
  -- bound each surviving term
  have hterm : ∀ e ∈ S,
      ‖projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ')‖
        ≤ |c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)) := by
    intro e he
    rw [hS, Finset.mem_filter, Finset.mem_range] at he
    obtain ⟨hek, hlt⟩ := he
    rw [map_smul, norm_smul]
    have hpow : |c - ξ'| ^ e ≤ |c - ξ'| ^ (k - l + 1 - m) :=
      pow_le_pow_of_le_one (abs_nonneg _) hint (by omega)
    have hfac : (1 : ℝ) ≤ (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
    have hfac0 : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
    have hc0 : (0 : ℝ) ≤ |c - ξ'| ^ e := pow_nonneg (abs_nonneg _) e
    have hcoeff : ‖(((c - ξ') ^ e / ((e.factorial : ℝ))) : ℝ)‖
        ≤ |c - ξ'| ^ (k - l + 1 - m) := by
      rw [Real.norm_eq_abs]
      have hfacabs : |(((e.factorial : ℕ) : ℝ))| = (e.factorial : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [abs_div, abs_pow, hfacabs]
      rw [div_le_iff₀ hfac0]
      calc |c - ξ'| ^ e ≤ |c - ξ'| ^ (k - l + 1 - m) := hpow
        _ = |c - ξ'| ^ (k - l + 1 - m) * 1 := by ring
        _ ≤ |c - ξ'| ^ (k - l + 1 - m) * (e.factorial : ℝ) :=
            mul_le_mul_of_nonneg_left hfac (pow_nonneg (abs_nonneg _) _)
    calc ‖(((c - ξ') ^ e / ((e.factorial : ℝ))) : ℝ)‖
          * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k (m + e) ξ')‖
        ≤ |c - ξ'| ^ (k - l + 1 - m)
            * (Real.sqrt k * (k.factorial : ℝ)) := by
          refine mul_le_mul hcoeff ?_ (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
          exact le_trans (norm_projMapLin_le k l
            (orthonormal_torsionVec k l hlk ξ') _) (norm_gammaDeriv_le k hξ'1 (m + e))
    _ = |c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)) := rfl
  calc ‖∑ e ∈ S, projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ')‖
      ≤ ∑ e ∈ S, ‖projMapLin k l (torsionVec k l hlk ξ')
          (((c - ξ') ^ e / ((e.factorial : ℝ))) • gammaDeriv k (m + e) ξ')‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ S, |c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (|c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((k : ℝ) + 1) * (Real.sqrt k * (k.factorial : ℝ)) + 1)
          * |c - ξ'| ^ (k - l + 1 - m) := by
        have hcard : (S.card : ℝ) ≤ (k : ℝ) + 1 := by
          have h1 : S.card ≤ (Finset.range (k + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
          have h2 : (Finset.range (k + 1)).card = k + 1 := Finset.card_range _
          rw [h2] at h1
          exact_mod_cast h1
        have hnn : (0 : ℝ) ≤ |c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)) :=
          mul_nonneg (pow_nonneg (abs_nonneg _) _) (by positivity)
        calc (S.card : ℝ) * (|c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ)))
            ≤ ((k : ℝ) + 1) * (|c - ξ'| ^ (k - l + 1 - m) * (Real.sqrt k * (k.factorial : ℝ))) :=
              mul_le_mul_of_nonneg_right hcard hnn
          _ ≤ (((k : ℝ) + 1) * (Real.sqrt k * (k.factorial : ℝ)) + 1)
                * |c - ξ'| ^ (k - l + 1 - m) := by
              nlinarith [pow_nonneg (abs_nonneg (c - ξ')) (k - l + 1 - m),
                Real.sqrt_nonneg k, Nat.cast_nonneg (α := ℝ) k.factorial]

/-! ## 4. The `H`-ball sits inside a fixed multiple of the polar plate -/

lemma plateHalf_pos (m' : ℕ) : 0 < plateHalf m' := by
  rw [plateHalf]; positivity

lemma plateHalf_le_one (m' : ℕ) : plateHalf m' ≤ 1 := by
  rw [plateHalf, one_div]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (a := (2 : ℝ)) (by norm_num))

/-- The radius of the `H`-ball at level `m'`:  `d^{-(k-l+1)}` with `d = plateHalf m'`. -/
noncomputable def hBallR (k l m' : ℕ) : ℝ := ((plateHalf m')⁻¹) ^ (k - l + 1)

lemma one_le_inv_plateHalf (m' : ℕ) : 1 ≤ (plateHalf m')⁻¹ :=
  one_le_inv₀ (plateHalf_pos m') |>.mpr (plateHalf_le_one m')

lemma hBallR_pos (k l m' : ℕ) : 0 < hBallR k l m' :=
  pow_pos (inv_pos.mpr (plateHalf_pos m')) _

/-- **The containment `B_H(0,r) ⊆ ρ · 𝒰^o_{I'}`**:  the gauge of `projEmbedLin w` in the gauge
coordinates of the polar plate of `plate k (plateHalf m') c'` is bounded by a constant `ρ`
depending only on `k` and `l`, for `‖w‖ ≤ d^{-(k-l+1)}` and `|c' - ξ'| ≤ plateHalf m'`. -/
theorem gauge_plateGaugeLin_projEmbed_le {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k)
    {ξ' : ℝ} (hξ' : ξ' ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ (m' : ℕ) (c' : ℝ), c' ∈ Set.Icc (0 : ℝ) 1 →
      |c' - ξ'| ≤ plateHalf m' → ∀ w : E l, ‖w‖ ≤ hBallR k l m' →
        gauge k hk (plateGaugeLin k (plateHalf m') c'
          (projEmbedLin k l (torsionVec k l hlk ξ') w)) ≤ ρ := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := norm_projMapLin_gammaDeriv_le hlk hξ'
  refine ⟨max C₁ (Real.sqrt k * (k.factorial : ℝ)), by positivity, ?_⟩
  intro m' c' hc' hsep w hw
  have hd0 : 0 < plateHalf m' := plateHalf_pos m'
  have hdle : plateHalf m' ≤ 1 := plateHalf_le_one m'
  have hc'1 : |c'| ≤ 1 := by
    rw [abs_le]; exact ⟨by linarith [hc'.1], hc'.2⟩
  refine gauge_plateGaugeLin_le hk hd0 (ρ := max C₁ (Real.sqrt k * (k.factorial : ℝ)))
    (fun i => ?_)
  set m : ℕ := i.val + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmk : m ≤ k := by have := i.isLt; omega
  have hinner : ⟪projEmbedLin k l (torsionVec k l hlk ξ') w, gammaDeriv k m c'⟫
      = ⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')⟫ :=
    inner_projEmbed_projMap k l (torsionVec k l hlk ξ') w _
  rw [hinner]
  rcases le_or_gt m (k - l) with hmle | hmgt
  · -- vanishing order case
    have hmul : (plateHalf m') ^ (k - l + 1 - m) * ((plateHalf m')⁻¹) ^ (k - l + 1)
        = ((plateHalf m') ^ m)⁻¹ := by
      rw [inv_pow]
      have hpow : (plateHalf m') ^ (k - l + 1)
          = (plateHalf m') ^ (k - l + 1 - m) * (plateHalf m') ^ m := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow, mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt (plateHalf_pos m'))), one_mul]
    have hbound := hC₁ m hm1 hmle c' hc'
    have hdK : |c' - ξ'| ^ (k - l + 1 - m) ≤ (plateHalf m') ^ (k - l + 1 - m) :=
      pow_le_pow_left₀ (abs_nonneg _) hsep _
    calc |⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')⟫|
        ≤ ‖w‖ * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ hBallR k l m' * (C₁ * |c' - ξ'| ^ (k - l + 1 - m)) :=
          mul_le_mul hw hbound (norm_nonneg _) (hBallR_pos k l m').le
      _ = C₁ * (|c' - ξ'| ^ (k - l + 1 - m) * hBallR k l m') := by ring
      _ ≤ C₁ * ((plateHalf m') ^ (k - l + 1 - m) * ((plateHalf m')⁻¹) ^ (k - l + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdK (hBallR_pos k l m').le) hC₁pos.le
      _ = C₁ * ((plateHalf m') ^ m)⁻¹ := by rw [hmul]
      _ ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m') ^ m)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · -- bounded case
    have hbound : ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')‖
        ≤ Real.sqrt k * (k.factorial : ℝ) :=
      le_trans (norm_projMapLin_le k l (orthonormal_torsionVec k l hlk ξ') _)
        (norm_gammaDeriv_le k hc'1 m)
    have hone : (1 : ℝ) ≤ (plateHalf m')⁻¹ := one_le_inv_plateHalf m'
    have hpow : ((plateHalf m')⁻¹) ^ (k - l + 1) ≤ ((plateHalf m')⁻¹) ^ m :=
      pow_le_pow_right₀ hone (by omega)
    have hinv : ((plateHalf m')⁻¹) ^ m = ((plateHalf m') ^ m)⁻¹ := inv_pow _ _
    calc |⟪w, projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')⟫|
        ≤ ‖w‖ * ‖projMapLin k l (torsionVec k l hlk ξ') (gammaDeriv k m c')‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ hBallR k l m' * (Real.sqrt k * (k.factorial : ℝ)) :=
          mul_le_mul hw hbound (norm_nonneg _) (hBallR_pos k l m').le
      _ = (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m')⁻¹) ^ (k - l + 1) := by
          rw [hBallR]; ring
      _ ≤ (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m')⁻¹) ^ m :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m') ^ m)⁻¹ := by rw [hinv]
      _ ≤ max C₁ (Real.sqrt k * (k.factorial : ℝ)) * ((plateHalf m') ^ m)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)


end Submission.Vinogradov
