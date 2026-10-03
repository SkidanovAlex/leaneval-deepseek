import Mathlib
import Submission.Work.Peluse.SwapA.SwapProps
import Submission.Work.Peluse.LadderP.p3HeartWin
import Submission.Work.Peluse.SwapA.genPair_scaled
import Submission.Work.Peluse.SwapA.sparseToDense
import Submission.Work.Peluse.SwapA.eta_lower
import Submission.Work.Peluse.SwapA.endgame_prod_le
import Submission.Work.Peluse.SwapA.M_ratio_lower
import Submission.Work.Peluse.SwapA.inv_le_of_nondegenerate
import Submission.Work.Peluse.SwapA.slotCard_pos
import Submission.Work.Peluse.SwapA.boxNormPow_eq_pbox_raw
import Submission.Work.Peluse.SwapA.genericCount

/-!
# The heart at every level: the assembly of the regime-swap route

`Work.Peluse.LadderP.p3Heart t` (the `c = 1` heart of the level-`(t+1)` induction step) is proved
directly at *every* level `t ≥ 1`, with no induction hypothesis, from the nodes of the route:

* `ConcatAllP`  (KKL Prop. 6.2, the full concatenation) -- subproject `Peluse/SwapC`;
* `DenseEndgameP` (the linear-in-law endgame)          -- subproject `Peluse/SwapE`;
* the regime swap `Work.Peluse.SwapA.sparseToDense` and the genericity count
  `Work.Peluse.SwapA.genericCount`, proved in this subproject.

The chain: the arbitrary window `S` of the heart is replaced by `symIcc N`
(`p3BoxAvg_eq_mul_card`), the sparse level-`(t+1)` average becomes the dense average
(`sparseToDense`), the dense average is the averaged multiset box (`boxNormPow_eq_pbox_raw`), the
slots are concatenated (`concatAll`), the generic ones are separated by the count (`genericCount`),
and the endgame closes the uniformity norm at the window `D ≤ (t+1)M₂M'` (`denseEndgame`).  Every
loss is a power of `γ`; the only regime factors are the window ratio (bounded by `4`) and
`M'/(M' + (t+1)M₂)`.

The extra power `γ^(2^(t+1))` in the final exponent absorbs the window ratio of the uniformity norm
(`uNorm_eq_mul_card`): the hypothesis at the small window `S` forces
`(|symIcc N|/|S|) ≥ γ^(2^(t+1))`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP (p3BoxAvg p3Heart p3good)
open Work.Peluse.LadderP.Swap (pbox pboxSum avg denseAvg slotSet slotCard slotAt genPair pdir)

/-! ## Elementary helpers -/

/-- The averaged box norm is nonnegative. -/
theorem p3BoxAvg_nonneg {s M₁ M₂ : ℕ} (b : Fin s → ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    0 ≤ p3BoxAvg s M₁ M₂ b S f := by
  rw [Work.Peluse.LadderP.p3BoxAvg]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (norm_nonneg _) _))

/-- **The power identity of the assembly's constants.** -/
theorem delta_pow_eq (γ r₁ C_R : ℝ) (K_R e_P : ℕ) :
    r₁ * (r₁ * (C_R * (γ / 4) ^ K_R) ^ e_P) ^ e_P
      = r₁ ^ (1 + e_P) * (C_R * ((1 : ℝ) / 4) ^ K_R) ^ (e_P ^ 2) * γ ^ (K_R * e_P ^ 2) := by
  have hδ : (γ / 4) ^ K_R = ((1 : ℝ) / 4) ^ K_R * γ ^ K_R := by
    rw [← mul_pow, show (1 : ℝ) / 4 * γ = γ / 4 by ring]
  rw [hδ]
  ring

/-- **The dense average is the average of the multiset boxes** (`boxNormPow_eq_pbox_raw` summed). -/
theorem denseAvg_eq_avg_pbox (t H M N : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) (hH : 1 ≤ H)
    (hsup : Work.Peluse.SupportIn f N) (hM : 1 ≤ M) :
    denseAvg t H M S f =
      avg (fun i : (Fin t → Fin H) × (Fin t → Fin H) =>
        pbox (2 ^ t - 1)
          (fun k => Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf t k)
            (Work.Peluse.Concat.tupSub i.1 i.2)) (fun _ => 0) M S f) := by
  have hcard : (Fintype.card ((Fin t → Fin H) × (Fin t → Fin H)) : ℝ) = (H : ℝ) ^ (2 * t) := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  rw [denseAvg, avg, hcard, inv_pow]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only
  refine Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => ?_))
  exact boxNormPow_eq_pbox_raw (2 ^ t - 1)
    (fun k => Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf t k)
      (Work.Peluse.Concat.tupSub h h')) M hM S f (Work.Peluse.FinSuppZ.of_supportIn hsup)

/-- The element of `q₁ ι k` is bounded by `(t+1)M₂` in absolute value: each slot is a sum of at
most `t+1` differences of elements of `[0, M₂-1]`. -/
theorem dotZ_tupSub_abs_le (t M₂ : ℕ) (x y : Fin (t + 1) → Fin M₂) (ω : Fin (t + 1) → Bool)
    (hM₂ : 1 ≤ M₂) :
    |Work.Peluse.Concat.dotZ ω (Work.Peluse.Concat.tupSub x y)| ≤ (((t + 1) * M₂ : ℕ) : ℤ) := by
  have hterm : ∀ i : Fin (t + 1), |Work.Peluse.Concat.tupSub x y i| ≤ (M₂ : ℤ) := by
    intro i
    rw [Work.Peluse.Concat.tupSub]
    have h1 : ((x i : ℕ) : ℤ) ≤ (M₂ : ℤ) := by
      have := (x i).isLt; omega
    have h2 : ((y i : ℕ) : ℤ) ≤ (M₂ : ℤ) := by
      have := (y i).isLt; omega
    rw [abs_le]
    constructor <;> omega
  rw [Work.Peluse.Concat.dotZ]
  calc |∑ i : Fin (t + 1), (if ω i then Work.Peluse.Concat.tupSub x y i else 0)|
      ≤ ∑ i : Fin (t + 1), |if ω i then Work.Peluse.Concat.tupSub x y i else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (t + 1), (M₂ : ℤ) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases h : ω i
        · rw [if_pos h]; exact hterm i
        · rw [if_neg h, abs_zero]; positivity
    _ = (((t + 1) * M₂ : ℕ) : ℤ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## The assembly -/

/-- **The heart at every level**, from the two dense-concatenation nodes. -/
theorem p3Heart_all_of (hAll : ConcatAllP) (hEnd : DenseEndgameP) :
    ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.p3Heart t := by
  intro t ht B₀
  have ht1 : 1 ≤ t + 1 := by omega
  have h2tp : 1 ≤ 2 ^ (t + 1) := Nat.one_le_two_pow
  have hs1 : 1 ≤ 2 ^ (t + 1) - 1 := by
    have hp : 2 ≤ 2 ^ (t + 1) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- the three node statements
  obtain ⟨C_P, hC_P0, e_P, he_P1, hConcat⟩ := hAll (2 ^ (t + 1) - 1) hs1
  obtain ⟨C_G, hC_G0, hGen⟩ := genericCount (t + 1) ht1
  obtain ⟨K_R, hK_R1, C_R, hC_R0, hC_R1, hSparse⟩ := sparseToDense (t + 1) ht1 B₀
  obtain ⟨K_E, hK_E1, s'_E, hs'_E2, C_E, hC_E0, hEndgm⟩ :=
    hEnd (slotCard (2 ^ (t + 1) - 1)) (slotCard_pos _ hs1)
  -- the constants of the assembly
  set r₁ : ℝ := min 1 C_P with hr₁
  set Bc : ℝ := r₁ ^ (1 + e_P) * (C_R * ((1 : ℝ) / 4) ^ K_R) ^ (e_P ^ 2) with hBc
  set G₀ : ℝ := min 1 (Bc / (4 * C_G)) with hG₀
  set M₀ : ℝ := C_R * ((1 : ℝ) / 4) ^ K_R / ((t : ℝ) + 2) with hM₀
  set K' : ℕ := max K_R K_E with hK'
  set e : ℕ := 2 ^ (t + 1) + (3 * (K_R * e_P ^ 2) + K') * K' with he
  set C : ℝ := min 1 (min (C_R * ((1 : ℝ) / 4) ^ K_R)
    (min (Bc / (4 * C_G)) (C_E * (Bc * (G₀ / ((t : ℝ) + 1)) ^ 2 * M₀) ^ K'))) with hC
  have hr₁0 : 0 < r₁ := lt_min (by norm_num) hC_P0
  have hr₁1 : r₁ ≤ 1 := min_le_left _ _
  have hr₁C : r₁ ≤ C_P := min_le_right _ _
  have hBc0 : 0 < Bc := by
    rw [hBc]
    exact mul_pos (pow_pos hr₁0 _) (pow_pos (mul_pos hC_R0 (pow_pos (by norm_num) _)) _)
  have hG₀0 : 0 < G₀ := lt_min (by norm_num) (div_pos hBc0 (by positivity))
  have hM₀0 : 0 < M₀ := div_pos (mul_pos hC_R0 (pow_pos (by norm_num) _)) (by positivity)
  have hC0 : 0 < C := by
    rw [hC]
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min (div_pos hBc0 (by positivity)) ?_))
    exact mul_pos hC_E0 (pow_pos (mul_pos (mul_pos hBc0 (pow_pos (div_pos hG₀0 (by positivity)) 2))
      hM₀0) _)
  have hC1 : C ≤ 1 := by rw [hC]; exact min_le_left _ _
  have hC_le_CR : C ≤ C_R * ((1 : ℝ) / 4) ^ K_R := by
    rw [hC]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hC_le_B4G : C ≤ Bc / (4 * C_G) := by
    rw [hC]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hC_le_end : C ≤ C_E * (Bc * (G₀ / ((t : ℝ) + 1)) ^ 2 * M₀) ^ K' := by
    rw [hC]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have he1 : 1 ≤ e := by
    rw [he]
    omega
  have hK'1 : 1 ≤ K' := by rw [hK']; exact le_trans hK_R1 (le_max_left _ _)
  have he_ge_K' : K' ≤ e := by
    rw [he]
    nlinarith [Nat.zero_le (3 * (K_R * e_P ^ 2) + K'), hK'1]
  have he_ge_KR : K_R ≤ e := by
    rw [hK'] at he_ge_K'
    exact le_trans (le_max_left _ _) he_ge_K'
  have he_ge_EΔ : K_R * e_P ^ 2 ≤ e := by
    rw [he]
    nlinarith [Nat.zero_le (3 * (K_R * e_P ^ 2) + K'), hK'1]
  have hs'_E1 : 1 ≤ s'_E := le_trans (by norm_num : 1 ≤ 2) hs'_E2
  refine ⟨s'_E, hs'_E1, e, he1, C, hC0, hC1, ?_⟩
  intro M₁ M₂ D N S b γ η ε f hM₂ hM₂M₁ hD1 hN hsup hS hMN hb hbd hγ0 hγ1 hη0 hηC hε0 hεC
    hDs hDn hbad hbox
  classical
  have hM₁ : 1 ≤ M₁ := le_trans (by norm_num : (1 : ℕ) ≤ 2) (le_trans hM₂ hM₂M₁)
  have hM₁R : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
  have hM₂R : (1 : ℝ) ≤ (M₂ : ℝ) := by
    have h : (1 : ℕ) ≤ M₂ := le_trans (by norm_num : 1 ≤ 2) hM₂
    exact_mod_cast h
  have hM₂M₁R : (M₂ : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₂M₁
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  -- the window `S` is nonempty
  have hS_card_pos : (0 : ℝ) < (S.card : ℝ) := by
    have h4 : ((2 * N + 1 : ℕ) : ℝ) ≤ 4 * (S.card : ℝ) := hS
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    by_contra hcon
    have hle : (S.card : ℝ) ≤ 0 := le_of_not_gt hcon
    have hz : (S.card : ℝ) = 0 := le_antisymm hle (by positivity)
    have hS0 : S.card = 0 := by exact_mod_cast hz
    rw [hS0] at h4
    push_cast at h4
    simp only [mul_zero] at h4
    linarith
  have hsym_ne : (Work.Peluse.symIcc N).Nonempty := Work.Peluse.LadderP.symIcc_nonempty hN
  have hsym_card : (((Work.Peluse.symIcc N).card : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [Work.Peluse.LadderP.card_symIcc]
    push_cast
    ring
  set X : ℝ := ((Work.Peluse.symIcc N).card : ℝ) / (S.card : ℝ) with hX
  have hX_pos : 0 < X := by rw [hX]; positivity
  have hX_le : X ≤ 4 := by
    rw [hX, div_le_iff₀ hS_card_pos, hsym_card]
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by push_cast; ring
    rw [← hcast]
    exact hS
  set rw_ : ℝ := X ^ (1 / (2 : ℝ) ^ (t + 1)) with hrw
  have hrw_pos : 0 < rw_ := Real.rpow_pos_of_pos hX_pos _
  have hrw_le4 : rw_ ≤ 4 := by
    rw [hrw]
    have h1 : X ^ (1 / (2 : ℝ) ^ (t + 1)) ≤ (4 : ℝ) ^ (1 / (2 : ℝ) ^ (t + 1)) :=
      Real.rpow_le_rpow hX_pos.le hX_le (by positivity)
    have hexp : (1 : ℝ) / (2 : ℝ) ^ (t + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (1 : ℕ) ≤ 2 ^ (t + 1) := Nat.one_le_two_pow
      exact_mod_cast this
    have h2 : (4 : ℝ) ^ (1 / (2 : ℝ) ^ (t + 1)) ≤ (4 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    rw [Real.rpow_one] at h2
    linarith
  have hA1_le : p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.symIcc N) f ≤ 1 :=
    Work.Peluse.LadderP.p3BoxAvg_symIcc_le_one hsup hbd
  have hA1_nonneg : 0 ≤ p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.symIcc N) f :=
    p3BoxAvg_nonneg b _ f
  have hscale : p3BoxAvg (t + 1) M₁ M₂ b S f
      = rw_ * p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.symIcc N) f := by
    rw [hrw, hX]
    exact Work.Peluse.LadderP.p3BoxAvg_eq_mul_card (s := t + 1) (S := S)
      (S' := Work.Peluse.symIcc N) M₁ M₂ b f hsym_ne
  have hγ_le_rw : γ ≤ rw_ := by
    calc γ ≤ p3BoxAvg (t + 1) M₁ M₂ b S f := hbox
      _ = rw_ * p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.symIcc N) f := hscale
      _ ≤ rw_ * 1 := mul_le_mul_of_nonneg_left hA1_le hrw_pos.le
      _ = rw_ := mul_one rw_
  have hA1_ge : γ / 4 ≤ p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.symIcc N) f := by
    have h1 : γ ≤ rw_ * p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.symIcc N) f := by
      calc γ ≤ p3BoxAvg (t + 1) M₁ M₂ b S f := hbox
        _ = rw_ * p3BoxAvg (t + 1) M₁ M₂ b (Work.Peluse.symIcc N) f := hscale
    nlinarith [h1, hrw_le4, hA1_nonneg]
  have hX_ge : γ ^ (2 ^ (t + 1)) ≤ X := by
    have h1 : γ ^ (2 ^ (t + 1)) ≤ rw_ ^ (2 ^ (t + 1)) :=
      pow_le_pow_left₀ hγ0.le hγ_le_rw _
    have h2 : rw_ ^ (2 ^ (t + 1)) = X := by
      rw [hrw, ← Real.rpow_natCast (X ^ (1 / (2 : ℝ) ^ (t + 1))) (2 ^ (t + 1)),
        ← Real.rpow_mul hX_pos.le]
      have h3 : (1 / (2 : ℝ) ^ (t + 1)) * ((2 ^ (t + 1) : ℕ) : ℝ) = 1 := by
        push_cast
        field_simp
      rw [h3, Real.rpow_one]
    linarith
  -- the uniformity-norm factor at the window `S`
  have huNorm_scale : Work.Peluse.uNorm s'_E (Work.Peluse.arithIcc 1 D) S f
      = X ^ (1 / (2 : ℝ) ^ s'_E)
        * Work.Peluse.uNorm s'_E (Work.Peluse.arithIcc 1 D) (Work.Peluse.symIcc N) f := by
    rw [hX]
    exact Work.Peluse.LadderP.uNorm_eq_mul_card s'_E (Work.Peluse.arithIcc 1 D)
      (S := S) (S' := Work.Peluse.symIcc N) f hsym_ne
  have hXpow_ge : γ ^ (2 ^ (t + 1)) ≤ X ^ (1 / (2 : ℝ) ^ s'_E) := by
    have hγp1 : γ ^ (2 ^ (t + 1)) ≤ 1 := pow_le_one₀ hγ0.le hγ1
    by_cases h : (1 : ℝ) ≤ X
    · have hone : (1 : ℝ) ≤ X ^ (1 / (2 : ℝ) ^ s'_E) := Real.one_le_rpow h (by positivity)
      linarith
    · have hexp : (1 : ℝ) / (2 : ℝ) ^ s'_E ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : (1 : ℕ) ≤ 2 ^ s'_E := Nat.one_le_two_pow
        exact_mod_cast this
      have hlt : X < 1 := not_le.mp h
      have h1 : X ^ (1 : ℝ) ≤ X ^ (1 / (2 : ℝ) ^ s'_E) :=
        Real.rpow_le_rpow_of_exponent_ge hX_pos hlt.le hexp
      rw [Real.rpow_one] at h1
      linarith
  -- the nondegeneracy gives `M₂` large
  have hη1 : η ≤ 1 := by
    have hle : C * γ ^ e ≤ 1 := mul_le_one₀ hC1 (pow_nonneg hγ0.le _) (pow_le_one₀ hγ0.le hγ1)
    linarith [hηC]
  have hM₂inv : (M₂ : ℝ)⁻¹ ≤ C * γ ^ e :=
    inv_le_of_nondegenerate (M₁ := (M₁ : ℝ)) (M₂ := (M₂ : ℝ)) (D := (D : ℝ))
      hγ0 hγ1 hη0 hη1 hC0 hC1 he1 hD1R hM₂R hM₂M₁R hDs hDn
  have hCγ_pos : 0 < C * γ ^ e := mul_pos hC0 (pow_pos hγ0 e)
  have hM₁inv : (M₁ : ℝ)⁻¹ ≤ C * γ ^ e :=
    le_trans (inv_anti₀ (by positivity : (0 : ℝ) < (M₂ : ℝ)) hM₂M₁R) hM₂inv
  have hM₁_ge : (C * γ ^ e)⁻¹ ≤ (M₁ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₁ : ℝ) * (C * γ ^ e) := by
      have h := mul_le_mul_of_nonneg_left hM₁inv (by positivity : (0 : ℝ) ≤ (M₁ : ℝ))
      rwa [mul_inv_cancel₀ (by positivity : ((M₁ : ℝ)) ≠ 0)] at h
    rw [← one_div, div_le_iff₀ hCγ_pos]
    exact h1
  -- the regime swap
  have hγ4pos : 0 < γ / 4 := by positivity
  have hγ4le1 : γ / 4 ≤ 1 := by linarith
  have hC_RM : (1 : ℝ) ≤ C_R * (γ / 4) ^ K_R * (M₁ : ℝ) := by
    have hkey : C * γ ^ e ≤ C_R * (γ / 4) ^ K_R := by
      have hpow : C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R = C_R * (γ / 4) ^ K_R := by
        have h1 : ((1 : ℝ) / 4) ^ K_R * γ ^ K_R = (γ / 4) ^ K_R := by
          rw [← mul_pow, show (1 : ℝ) / 4 * γ = γ / 4 by ring]
        calc C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R
            = C_R * (((1 : ℝ) / 4) ^ K_R * γ ^ K_R) := by ring
          _ = C_R * (γ / 4) ^ K_R := by rw [h1]
      calc C * γ ^ e
          ≤ C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ e :=
            mul_le_mul_of_nonneg_right hC_le_CR (pow_nonneg hγ0.le e)
        _ ≤ C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact pow_le_pow_of_le_one hγ0.le hγ1 he_ge_KR
        _ = C_R * (γ / 4) ^ K_R := hpow
    have h2 := mul_le_mul hkey hM₁_ge (by positivity) (by positivity)
    rw [mul_inv_cancel₀ (a := C * γ ^ e) (ne_of_gt hCγ_pos)] at h2
    exact h2
  obtain ⟨M', hM'1, hM'M₁, hM'ge, hdense_ge⟩ :=
    hSparse M₁ M₂ N b (γ / 4) f (le_trans (by norm_num : (1 : ℕ) ≤ 2) hM₂) hM₂M₁ hMN
      hsup hbd hb hγ4pos hγ4le1 hC_RM hA1_ge
  have hM'R1 : (1 : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hM'1
  have hM'Rpos : (0 : ℝ) < (M' : ℝ) := by linarith
  -- the dense average is the averaged multiset boxes
  set δ₁ : ℝ := C_R * (γ / 4) ^ K_R with hδ₁
  have hδ₁0 : 0 < δ₁ := by rw [hδ₁]; positivity
  have hδ₁1 : δ₁ ≤ 1 := by
    rw [hδ₁]
    exact mul_le_one₀ hC_R1 (by positivity) (pow_le_one₀ (by positivity) hγ4le1)
  have hδ₁_avg : δ₁ ≤ avg (fun i : (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂) =>
      pbox (2 ^ (t + 1) - 1)
        (fun k => Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1) k)
          (Work.Peluse.Concat.tupSub i.1 i.2)) (fun _ => 0) M' (Work.Peluse.symIcc N) f) := by
    rw [hδ₁]
    rw [denseAvg_eq_avg_pbox (t + 1) M₂ M' N (Work.Peluse.symIcc N) f (by omega) hsup hM'1]
      at hdense_ge
    exact hdense_ge
  -- the concatenation
  set δ₂ : ℝ := r₁ * δ₁ ^ e_P with hδ₂
  have hδ₂0 : 0 < δ₂ := by rw [hδ₂]; positivity
  have hδ₂_le_δ₁ : δ₂ ≤ δ₁ := by
    rw [hδ₂]
    calc r₁ * δ₁ ^ e_P ≤ 1 * δ₁ ^ e_P := mul_le_mul_of_nonneg_right hr₁1 (by positivity)
      _ = δ₁ ^ e_P := one_mul _
      _ ≤ δ₁ := Work.Peluse.LadderP.pow_le_self_of_le_one hδ₁0.le hδ₁1 he_P1
  have hδ₂_avg := le_trans hδ₂_le_δ₁ hδ₁_avg
  haveI hIxne : Nonempty ((Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂)) :=
    ⟨(fun _ => ⟨0, by omega⟩, fun _ => ⟨0, by omega⟩)⟩
  obtain hConcl := hConcat ((Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂))
    (fun i k => Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1) k)
      (Work.Peluse.Concat.tupSub i.1 i.2)) M' N δ₂ f hM'1 hsup hbd hδ₂0 hδ₂_avg
  set Δ : ℝ := r₁ * δ₂ ^ e_P with hΔ
  have hΔ0 : 0 < Δ := by rw [hΔ]; positivity
  have hΔ_le_avg : Δ ≤ avg (fun ι : (Fin (2 ^ (t + 1) - 1) → Bool) →
        (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂) =>
      pbox (slotCard (2 ^ (t + 1) - 1))
        (fun k => Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).1
            (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).2))
        (fun k => Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).1
            (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).2)) M' (Work.Peluse.symIcc N) f) := by
    rw [hΔ]
    exact le_trans (mul_le_mul_of_nonneg_right hr₁C (pow_nonneg hδ₂0.le _)) hConcl
  -- the density parameters of the endgame
  have hpowCR : C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R = C_R * (γ / 4) ^ K_R := by
    have h1 : ((1 : ℝ) / 4) ^ K_R * γ ^ K_R = (γ / 4) ^ K_R := by
      rw [← mul_pow, show (1 : ℝ) / 4 * γ = γ / 4 by ring]
    calc C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R
        = C_R * (((1 : ℝ) / 4) ^ K_R * γ ^ K_R) := by ring
      _ = C_R * (γ / 4) ^ K_R := by rw [h1]
  set H_E : ℕ := (t + 1) * M₂ with hH_E
  have hH_E1 : 1 ≤ H_E := by
    rw [hH_E]
    have h1 : 1 ≤ t + 1 := by omega
    have h2 : 1 ≤ M₂ := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hH_ER : ((H_E : ℕ) : ℝ) = ((t : ℝ) + 1) * (M₂ : ℝ) := by
    rw [hH_E]; push_cast; ring
  set η₀ : ℝ := min 1 (Δ / (4 * C_G)) with hη₀
  set η' : ℝ := η₀ / ((t : ℝ) + 1) with hη'
  have hη₀_pos : 0 < η₀ := lt_min (by norm_num) (div_pos hΔ0 (by positivity))
  have hη₀_le1 : η₀ ≤ 1 := min_le_left _ _
  have hη'_pos : 0 < η' := by rw [hη']; positivity
  have hη'_le1 : η' ≤ 1 := by
    rw [hη']
    exact div_le_one_of_le₀ (by linarith [hη₀_le1]) (by positivity)
  have hΔ_lower : Bc * γ ^ (K_R * e_P ^ 2) ≤ Δ := by
    rw [hΔ, hδ₂, hδ₁, hBc, delta_pow_eq]
  have hη₀_lower : G₀ * γ ^ (K_R * e_P ^ 2) ≤ η₀ := by
    rw [hG₀, hη₀]
    exact eta_lower hγ0 hγ1 hBc0 hC_G0 hΔ_lower
  have hη'_lower : G₀ / ((t : ℝ) + 1) * γ ^ (K_R * e_P ^ 2) ≤ η' := by
    rw [hη']
    have h := div_le_div_of_nonneg_right hη₀_lower (by positivity : (0 : ℝ) ≤ (t : ℝ) + 1)
    calc G₀ / ((t : ℝ) + 1) * γ ^ (K_R * e_P ^ 2)
        = (G₀ * γ ^ (K_R * e_P ^ 2)) / ((t : ℝ) + 1) := by ring
      _ ≤ η₀ / ((t : ℝ) + 1) := h
  have hM'_ratio_R : M₀ * γ ^ K_R ≤ (M' : ℝ) / ((M' : ℝ) + ((t : ℝ) + 1) * (M₂ : ℝ)) := by
    rw [hM₀]
    exact M_ratio_lower γ hγ0 hγ1 hC_R0 hC_R1 hM₂R hM₂M₁R (by exact_mod_cast hM'M₁)
      hM'ge
  have hM'_ratio : M₀ * γ ^ K' ≤ (M' : ℝ) / ((M' : ℝ) + ((t : ℝ) + 1) * (M₂ : ℝ)) := by
    have h1 : γ ^ K' ≤ γ ^ K_R := by
      rw [hK']
      exact pow_le_pow_of_le_one hγ0.le hγ1 (le_max_left _ _)
    calc M₀ * γ ^ K' ≤ M₀ * γ ^ K_R := mul_le_mul_of_nonneg_left h1 hM₀0.le
      _ ≤ _ := hM'_ratio_R
  -- the endgame product, bounded by a power of `γ`
  have hprodle := endgame_prod_le (γ := γ) (Δ := Δ) (η' := η') (M := (M' : ℝ)) (H := (H_E : ℝ))
    (B := Bc) (G := G₀ / ((t : ℝ) + 1)) (M₀ := M₀) (C_E := C_E) (E := K_R * e_P ^ 2) (K := K')
    hγ0 hγ1 hBc0 (div_pos hG₀0 (by positivity)) hM₀0 hC_E0 hΔ_lower hη'_lower
    (by rw [hH_ER]; exact hM'_ratio) hM'Rpos (by positivity)
  -- the dense average is bounded by `D`
  have hD_le_C : (D : ℝ) ≤ C * γ ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) := by
    have hηe : (γ * η) ^ e ≤ γ ^ e := by
      have hγη : γ * η ≤ γ := by nlinarith [hη0, hη1, hγ0]
      exact pow_le_pow_left₀ (by positivity) hγη e
    calc (D : ℝ) ≤ C * (γ * η) ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) := hDs
      _ ≤ C * γ ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηe hC0.le) (by positivity)
  have hDN : D ≤ N := by
    have h1 : (D : ℝ) ≤ (N : ℝ) := by
      have hCγ1 : C * γ ^ e ≤ 1 :=
        mul_le_one₀ hC1 (pow_nonneg hγ0.le _) (pow_le_one₀ hγ0.le hγ1)
      nlinarith [hD_le_C, hMN, hCγ1, hM₁R, hM₂R]
    exact_mod_cast h1
  have hDHM : D ≤ H_E * M' := by
    have h1 : (D : ℝ) ≤ ((H_E * M' : ℕ) : ℝ) := by
      have hcast : ((H_E * M' : ℕ) : ℝ) = ((t : ℝ) + 1) * (M₂ : ℝ) * (M' : ℝ) := by
        rw [hH_E]; push_cast; ring
      rw [hcast]
      have hM'g : C_R * (γ / 4) ^ K_R * (M₁ : ℝ) ≤ (M' : ℝ) := hM'ge
      have h2 : (D : ℝ) ≤ C_R * (γ / 4) ^ K_R * ((M₁ : ℝ) * (M₂ : ℝ)) := by
        calc (D : ℝ) ≤ C * γ ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) := hD_le_C
          _ ≤ C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R * ((M₁ : ℝ) * (M₂ : ℝ)) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc C * γ ^ e ≤ C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ e :=
                    mul_le_mul_of_nonneg_right hC_le_CR (pow_nonneg hγ0.le e)
                _ ≤ C_R * ((1 : ℝ) / 4) ^ K_R * γ ^ K_R := by
                    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                    exact pow_le_pow_of_le_one hγ0.le hγ1 he_ge_KR
          _ = C_R * (γ / 4) ^ K_R * ((M₁ : ℝ) * (M₂ : ℝ)) := by rw [hpowCR]
      nlinarith [h2, hM'g, hM₂R, hM'Rpos, hγ4pos, hC_R0]
    exact_mod_cast h1
  -- the good set and the genericity count
  have hq_bound : ∀ (ω : (Fin (2 ^ (t + 1) - 1) → Bool) →
        (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂)) (k : Fin (slotCard (2 ^ (t + 1) - 1))),
      |Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ω (slotAt (2 ^ (t + 1) - 1) k).2.1).1
            (ω (slotAt (2 ^ (t + 1) - 1) k).2.1).2)| ≤ ((H_E : ℕ) : ℤ) ∧
      |Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ω (slotAt (2 ^ (t + 1) - 1) k).2.2).1
            (ω (slotAt (2 ^ (t + 1) - 1) k).2.2).2)| ≤ ((H_E : ℕ) : ℤ) := by
    intro ω k
    have hM₂1 : 1 ≤ M₂ := by omega
    refine ⟨?_, ?_⟩
    · have h := dotZ_tupSub_abs_le t M₂ (ω (slotAt (2 ^ (t + 1) - 1) k).2.1).1
        (ω (slotAt (2 ^ (t + 1) - 1) k).2.1).2
        (Work.Peluse.Holds.omegaOf (t + 1) (slotAt (2 ^ (t + 1) - 1) k).1) hM₂1
      rwa [hH_E]
    · have h := dotZ_tupSub_abs_le t M₂ (ω (slotAt (2 ^ (t + 1) - 1) k).2.2).1
        (ω (slotAt (2 ^ (t + 1) - 1) k).2.2).2
        (Work.Peluse.Holds.omegaOf (t + 1) (slotAt (2 ^ (t + 1) - 1) k).1) hM₂1
      rwa [hH_E]
  set Good : Finset ((Fin (2 ^ (t + 1) - 1) → Bool) →
      (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂)) :=
    Finset.univ.filter (fun ι => ∀ k : Fin (slotCard (2 ^ (t + 1) - 1)),
      genPair H_E η'
        (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).1
            (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).2))
        (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).1
            (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).2))) with hGood
  have hgood_gen : ∀ ω ∈ Good, ∀ k : Fin (slotCard (2 ^ (t + 1) - 1)),
      genPair H_E η'
        (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ω (slotAt (2 ^ (t + 1) - 1) k).2.1).1
            (ω (slotAt (2 ^ (t + 1) - 1) k).2.1).2))
        (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ω (slotAt (2 ^ (t + 1) - 1) k).2.2).1
            (ω (slotAt (2 ^ (t + 1) - 1) k).2.2).2)) := by
    intro ω hω k
    rw [hGood, Finset.mem_filter] at hω
    exact hω.2 k
  letI : DecidableEq ((Fin (2 ^ (t + 1) - 1) → Bool) →
      (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂)) := Classical.decEq _
  have hbad_le : (((Finset.univ \ Good).card : ℕ) : ℝ) ≤ Δ / 2 *
      (Fintype.card ((Fin (2 ^ (t + 1) - 1) → Bool) →
        (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂)) : ℝ) := by
    have hsub : Finset.univ \ Good ⊆
        Finset.univ.filter (fun ι : (Fin (2 ^ (t + 1) - 1) → Bool) →
            (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂) =>
          ∃ k : Fin (slotCard (2 ^ (t + 1) - 1)),
            ¬ genPair M₂ η₀
              (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
                  (slotAt (2 ^ (t + 1) - 1) k).1)
                (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).1
                  (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).2))
              (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
                  (slotAt (2 ^ (t + 1) - 1) k).1)
                (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).1
                  (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).2))) := by
      intro ι hι
      rw [Finset.mem_sdiff, hGood, Finset.mem_filter] at hι
      obtain ⟨-, hι⟩ := hι
      simp only [Finset.mem_univ, true_and] at hι
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hcon
      push_neg at hcon
      exact hι (fun k => by
        have h := genPair_scaled (t + 1) (by omega) (hcon k)
        rw [hH_E, hη']
        simpa only [Nat.cast_add, Nat.cast_one] using h)
    have hgen := hGen M₂ η₀ (by omega) hη₀_pos hη₀_le1
    have hsum : C_G * (η₀ + 1 / (M₂ : ℝ)) ≤ Δ / 2 := by
      have h1 : C_G * η₀ ≤ Δ / 4 := by
        rw [hη₀]
        calc C_G * min 1 (Δ / (4 * C_G)) ≤ C_G * (Δ / (4 * C_G)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hC_G0.le
          _ = Δ / 4 := by field_simp
      have h2 : C_G * (1 / (M₂ : ℝ)) ≤ Δ / 4 := by
        have hB : C_G * C ≤ Bc / 4 := by
          have h1 : C * C_G ≤ Bc / (4 * C_G) * C_G :=
            mul_le_mul_of_nonneg_right hC_le_B4G hC_G0.le
          have h2 : Bc / (4 * C_G) * C_G = Bc / 4 := by field_simp
          rw [h2] at h1
          linarith [h1]
        have h3 : C_G * (1 / (M₂ : ℝ)) ≤ C_G * (C * γ ^ e) := by
          rw [one_div]
          exact mul_le_mul_of_nonneg_left hM₂inv hC_G0.le
        have h4 : C_G * (C * γ ^ e) ≤ Δ / 4 := by
          calc C_G * (C * γ ^ e) = (C_G * C) * γ ^ e := by ring
            _ ≤ (Bc / 4) * γ ^ e := mul_le_mul_of_nonneg_right hB (pow_nonneg hγ0.le e)
            _ ≤ (Bc / 4) * γ ^ (K_R * e_P ^ 2) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact pow_le_pow_of_le_one hγ0.le hγ1 he_ge_EΔ
            _ ≤ Δ / 4 := by linarith [hΔ_lower]
        linarith [h3, h4]
      linarith [h1, h2]
    calc (((Finset.univ \ Good).card : ℕ) : ℝ)
        ≤ (((Finset.univ.filter (fun ι : (Fin (2 ^ (t + 1) - 1) → Bool) →
            (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂) =>
          ∃ k : Fin (slotCard (2 ^ (t + 1) - 1)),
            ¬ genPair M₂ η₀
              (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
                  (slotAt (2 ^ (t + 1) - 1) k).1)
                (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).1
                  (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).2))
              (Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
                  (slotAt (2 ^ (t + 1) - 1) k).1)
                (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).1
                  (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).2)))).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ C_G * (η₀ + 1 / (M₂ : ℝ)) *
          (Fintype.card ((Fin (2 ^ (t + 1) - 1) → Bool) →
            (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂)) : ℝ) := hgen
      _ ≤ Δ / 2 * (Fintype.card ((Fin (2 ^ (t + 1) - 1) → Bool) →
            (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂)) : ℝ) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
  -- the endgame
  haveI hΩne : Nonempty ((Fin (2 ^ (t + 1) - 1) → Bool) →
      (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂)) :=
    ⟨fun _ => Classical.arbitrary _⟩
  have hEndres := hEndgm ((Fin (2 ^ (t + 1) - 1) → Bool) →
        (Fin (t + 1) → Fin M₂) × (Fin (t + 1) → Fin M₂))
      (fun ι k => Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).1
            (ι (slotAt (2 ^ (t + 1) - 1) k).2.1).2))
      (fun ι k => Work.Peluse.Concat.dotZ (Work.Peluse.Holds.omegaOf (t + 1)
            (slotAt (2 ^ (t + 1) - 1) k).1)
          (Work.Peluse.Concat.tupSub (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).1
            (ι (slotAt (2 ^ (t + 1) - 1) k).2.2).2))
      Good H_E M' D N η' Δ f hH_E1 hM'1 hD1 hDHM hDN hsup hbd hη'_pos hη'_le1 hΔ0
      hq_bound hgood_gen hbad_le hΔ_le_avg
  -- the final chain
  have huNorm_nonneg : 0 ≤ Work.Peluse.uNorm s'_E (Work.Peluse.arithIcc 1 D)
      (Work.Peluse.symIcc N) f := by
    rw [Work.Peluse.uNorm]
    exact Real.rpow_nonneg (norm_nonneg _) _
  calc C * γ ^ e
      ≤ C_E * (Bc * (G₀ / ((t : ℝ) + 1)) ^ 2 * M₀) ^ K' * γ ^ e := by
        have h := mul_le_mul_of_nonneg_right hC_le_end (pow_nonneg hγ0.le e)
        linarith [h]
    _ ≤ C_E * (Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ))) ^ K' * γ ^ (2 ^ (t + 1)) := by
        have hexp : γ ^ e = γ ^ ((3 * (K_R * e_P ^ 2) + K') * K') * γ ^ (2 ^ (t + 1)) := by
          rw [he, pow_add]
          ring
        calc C_E * (Bc * (G₀ / ((t : ℝ) + 1)) ^ 2 * M₀) ^ K' * γ ^ e
            = C_E * (Bc * (G₀ / ((t : ℝ) + 1)) ^ 2 * M₀) ^ K'
                * γ ^ ((3 * (K_R * e_P ^ 2) + K') * K') * γ ^ (2 ^ (t + 1)) := by
              rw [hexp]; ring
          _ ≤ C_E * (Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ))) ^ K'
                * γ ^ (2 ^ (t + 1)) :=
              mul_le_mul_of_nonneg_right hprodle (pow_nonneg hγ0.le _)
    _ ≤ C_E * (Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ))) ^ K_E * γ ^ (2 ^ (t + 1)) := by
        have hx0 : 0 ≤ Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ)) := by positivity
        have hx1 : Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ)) ≤ 1 := by
          have hΔ1 : Δ ≤ 1 := by
            have hδ₁pow : δ₁ ^ e_P ≤ 1 := pow_le_one₀ hδ₁0.le hδ₁1
            have hinner : (r₁ * δ₁ ^ e_P) ^ e_P ≤ 1 :=
              pow_le_one₀ (by positivity) (mul_le_one₀ hr₁1 (by positivity) hδ₁pow)
            rw [hΔ, hδ₂]
            exact mul_le_one₀ hr₁1 (by positivity) hinner
          have hη1 : η' ^ 2 ≤ 1 := pow_le_one₀ hη'_pos.le hη'_le1
          have hfrac : (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ)) ≤ 1 := by
            rw [div_le_one (by positivity)]
            exact le_add_of_nonneg_right (by positivity)
          have hsplit : Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ))
              = (Δ * η' ^ 2) * ((M' : ℝ) / ((M' : ℝ) + (H_E : ℝ))) := by ring
          rw [hsplit]
          exact mul_le_one₀ (mul_le_one₀ hΔ1 (pow_nonneg hη'_pos.le 2) hη1) (by positivity) hfrac
        have hpow : (Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ))) ^ K'
            ≤ (Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ))) ^ K_E :=
          pow_le_pow_of_le_one hx0 hx1 (le_max_right K_R K_E)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC_E0.le)
          (pow_nonneg hγ0.le _)
    _ ≤ X ^ (1 / (2 : ℝ) ^ s'_E) * Work.Peluse.uNorm s'_E (Work.Peluse.arithIcc 1 D)
          (Work.Peluse.symIcc N) f := by
        calc C_E * (Δ * η' ^ 2 * (M' : ℝ) / ((M' : ℝ) + (H_E : ℝ))) ^ K_E * γ ^ (2 ^ (t + 1))
            ≤ Work.Peluse.uNorm s'_E (Work.Peluse.arithIcc 1 D) (Work.Peluse.symIcc N) f
                * γ ^ (2 ^ (t + 1)) :=
              mul_le_mul_of_nonneg_right hEndres (pow_nonneg hγ0.le _)
          _ ≤ Work.Peluse.uNorm s'_E (Work.Peluse.arithIcc 1 D) (Work.Peluse.symIcc N) f
                * X ^ (1 / (2 : ℝ) ^ s'_E) :=
              mul_le_mul_of_nonneg_left hXpow_ge huNorm_nonneg
          _ = X ^ (1 / (2 : ℝ) ^ s'_E) * Work.Peluse.uNorm s'_E (Work.Peluse.arithIcc 1 D)
                (Work.Peluse.symIcc N) f := by ring
    _ = Work.Peluse.uNorm s'_E (Work.Peluse.arithIcc 1 D) S f := by rw [huNorm_scale]

/-- **The heart at every level**, from all three frozen nodes of the route.  The `concatStep`
hypothesis is carried for the case where the sibling subproject `SwapC` delivers `concatAll`
*conditionally* on `concatStep`; the assembly itself only consumes `concatAll` and `denseEndgame`. -/
theorem p3Heart_all_of_step (hStep : ConcatStepP) (hAll : ConcatAllP) (hEnd : DenseEndgameP) :
    ∀ t : ℕ, 1 ≤ t → Work.Peluse.LadderP.p3Heart t :=
  p3Heart_all_of hAll hEnd

end

end Work.Peluse.SwapA
