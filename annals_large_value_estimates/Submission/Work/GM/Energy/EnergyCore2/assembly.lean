import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.LocalConstancy.localize_smoothedPoly
import Submission.Work.GM.Energy.LocalConstancy.localize_dirichlet
import Submission.Work.GM.Energy.Moments.second_moment_Rfun
import Submission.Work.GM.Energy.EnergyCore.fourth_moment_Rfun
import Submission.Work.GM.Energy.EnergyCore.gcd_small
import Submission.Work.GM.Energy.RMoments.Rfun_integral_sq
import Submission.Work.GM.Energy.RMoments.Rfun_integral_pow4
import Submission.Work.GM.Energy.Basic.energy_le_three_mul_cube
import Submission.Work.GM.Energy.Basic.card_sq_le_energy
import Submission.Work.GM.Trace.sep_card_le
import Submission.Work.GM.Energy.EnergyCore2.kpow_facts
import Submission.Work.GM.Energy.EnergyCore2.beta_le
import Submission.Work.GM.Energy.EnergyCore2.arith_A
import Submission.Work.GM.Energy.EnergyCore2.arith_B

namespace Work.GM.Energy.EnergyCore2

open Complex Finset MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Rearrangement of `E ≤ A √E + B` into `E ≤ 2A² + 2B` (for `A, B ≥ 0`). -/
lemma le_two_mul_sq_add_two_mul_of_le_mul_sqrt_add {E A B : ℝ} (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (h : E ≤ A * Real.sqrt E + B) : E ≤ 2 * A ^ 2 + 2 * B := by
  set x := Real.sqrt E with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg E
  have hx2 : x ^ 2 = E := Real.sq_sqrt hE
  rw [← hx2] at h ⊢
  have h1 : x ≤ A + Real.sqrt B := by
    by_contra hcon
    push Not at hcon
    have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
    have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
    nlinarith [sq_nonneg (x - A - Real.sqrt B), sq_nonneg (x - A + Real.sqrt B)]
  have hy0 : 0 ≤ A + Real.sqrt B := le_trans hx0 h1
  calc x ^ 2 ≤ (A + Real.sqrt B) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (add_nonneg hy0 hx0)]
    _ ≤ 2 * A ^ 2 + 2 * B := by
        have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
        have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
        nlinarith [sq_nonneg (A - Real.sqrt B)]

/-- The additive energy is at most `|W|⁴` (it counts a subset of `W⁴`). -/
lemma energy_le_card_pow_four (W : Finset ℝ) : (Submission.GM.energy W : ℝ) ≤ (W.card : ℝ) ^ 4 := by
  classical
  have h : Submission.GM.energy W ≤ W.card ^ 4 := by
    unfold Submission.GM.energy
    calc ((W ×ˢ W ×ˢ W ×ˢ W).filter
            (fun q : ℝ × ℝ × ℝ × ℝ => |q.1 + q.2.1 - q.2.2.1 - q.2.2.2| ≤ 1)).card
        ≤ (W ×ˢ W ×ˢ W ×ˢ W).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = W.card ^ 4 := by
          rw [Finset.card_product, Finset.card_product, Finset.card_product]
          ring
  calc (Submission.GM.energy W : ℝ) ≤ ((W.card ^ 4 : ℕ) : ℝ) := by exact_mod_cast h
    _ = (W.card : ℝ) ^ 4 := by push_cast; ring

/-- `M N ^ 3 ≤ N ^ 4` for `N ≥ 1` (since `M N = N^{6/5}`). -/
lemma M_pow_three_le (N : ℕ) (hN : 1 ≤ N) :
    (Submission.LargeValues.M N) ^ 3 ≤ (N : ℝ) ^ 4 := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h2 : ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ((3 : ℝ)) = (N : ℝ) ^ (18 / 5 : ℝ) := by
    rw [← Real.rpow_mul hN0 (6 / 5 : ℝ) (3 : ℝ)]
    norm_num
  have h1 : (Submission.LargeValues.M N) ^ 3 = ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ((3 : ℝ)) := by
    rw [Submission.LargeValues.M]
    exact (Real.rpow_natCast ((N : ℝ) ^ (6 / 5 : ℝ)) 3).symm
  have h3 : (N : ℝ) ^ (18 / 5 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num)
  have h4 : (N : ℝ) ^ ((4 : ℝ)) = (N : ℝ) ^ 4 := Real.rpow_natCast (N : ℝ) 4
  calc (Submission.LargeValues.M N) ^ 3 = ((N : ℝ) ^ (6 / 5 : ℝ)) ^ ((3 : ℝ)) := h1
    _ = (N : ℝ) ^ (18 / 5 : ℝ) := h2
    _ ≤ (N : ℝ) ^ ((4 : ℝ)) := h3
    _ = (N : ℝ) ^ 4 := h4


/-- The locality hypothesis of `gcd_small` with the constant `C7` upgraded to `CR ≥ C7`. -/
lemma loc_of_big {m : ℕ} {C7 CR : ℝ} (hC7CR : C7 ≤ CR)
    (hL7c : ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → ∀ (v : ℝ), v ∈ Set.Icc (1 / 2 : ℝ) 2 →
      ∀ (K : ℝ), 1 ≤ K →
      ‖Submission.GM.Rfun W v‖ ≤
        C7 * T * (∫ v' in v - K / T..v + K / T, ‖Submission.GM.Rfun W v'‖)
          + C7 / K ^ (m : ℝ) * (W.card : ℝ)) :
    ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
      (∀ t ∈ W, t ∈ Set.Icc 0 T) → ∀ (v : ℝ), v ∈ Set.Icc (1 / 2 : ℝ) 2 →
      ∀ (K : ℝ), 1 ≤ K →
      ‖Submission.GM.Rfun W v‖ ≤
        CR * T * (∫ v' in v - K / T..v + K / T, ‖Submission.GM.Rfun W v'‖)
          + CR / K ^ (m : ℝ) * (W.card : ℝ) := by
  intro T hT W hW v hv K hK
  have h7 := hL7c T hT W hW v hv K hK
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hK0 : 0 ≤ K / T := div_nonneg (by linarith) (le_of_lt hTpos)
  have hle : v - K / T ≤ v + K / T := by linarith
  have hI0 : 0 ≤ ∫ v' in v - K / T..v + K / T, ‖Submission.GM.Rfun W v'‖ :=
    intervalIntegral.integral_nonneg hle fun x _ => norm_nonneg _
  refine h7.trans (add_le_add ?_ ?_)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC7CR (le_of_lt hTpos)) hI0
  · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hC7CR (by positivity)) (by positivity)

/-- The `L²` bound of `gcd_small` with the constant upgraded. -/
lemma l2_of_big {Cm2 CR : ℝ} (hCm2CR : Cm2 ≤ CR)
    (hL2c : ∀ (W : Finset ℝ) (T : ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      Submission.GM.Separated W 1 → (∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2) ≤ Cm2 * (W.card : ℝ)) :
    ∀ (W : Finset ℝ) (T : ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      Submission.GM.Separated W 1 →
      (∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 2) ≤ CR * (W.card : ℝ) := by
  intro W T hW hs
  exact (hL2c W T hW hs).trans (mul_le_mul_of_nonneg_right hCm2CR (by positivity))

/-- The `L⁴` bound of `gcd_small` with the constant upgraded. -/
lemma l4_of_big {Cm4 CR : ℝ} (hCm4CR : Cm4 ≤ CR)
    (hL4c : ∀ (W : Finset ℝ) (T : ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      Submission.GM.Separated W 1 →
      (∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4) ≤ Cm4 * (Submission.GM.energy W : ℝ)) :
    ∀ (W : Finset ℝ) (T : ℝ), (∀ t ∈ W, t ∈ Set.Icc 0 T) →
      Submission.GM.Separated W 1 →
      (∫ v in (1 : ℝ)..2, ‖Submission.GM.Rfun W v‖ ^ 4) ≤ CR * (Submission.GM.energy W : ℝ) := by
  intro W T hW hs
  exact (hL4c W T hW hs).trans (mul_le_mul_of_nonneg_right hCm4CR (by positivity))

/-- The trivial case `V < 1` of the assembly: the additive energy is at most `|W|⁴`, and
`|W| ≤ T + 1 ≤ 2T` by `1`-separation, so `E(W) ≤ 8 κ N⁴/V⁴`. -/
theorem energy_trivial {N : ℕ} {T V κ E CF δ : ℝ} (hN1 : 1 ≤ N)
    {W : Finset ℝ} (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T) (hsep : Submission.GM.Separated W 1)
    (hκ : κ = (W.card : ℝ)) (hE : E = (Submission.GM.energy W : ℝ))
    (hT1 : 1 ≤ T) (hT3 : T ^ 3 ≤ (N : ℝ) ^ 4)
    (hVpos : 0 < V) (hVlt : V < 1) (hF8 : 8 ≤ CF) (hδ : 0 < δ) :
    E ≤ CF * (N : ℝ) ^ δ *
      (κ * (N : ℝ) ^ 4 / V ^ 4 + κ ^ ((21 : ℝ) / 8) * T ^ ((1 : ℝ) / 4) * (N : ℝ) / V ^ 2
        + κ ^ 3 * (N : ℝ) / V ^ 2) := by
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hκnn : 0 ≤ κ := by rw [hκ]; positivity
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hV4le : V ^ 4 ≤ 1 := by
    have h1 : V ^ 2 ≤ 1 := by nlinarith [hVlt, le_of_lt hVpos]
    nlinarith [h1, sq_nonneg (V ^ 2)]
  have hV4pos : 0 < V ^ 4 := by positivity
  have hV4inv : 1 ≤ 1 / V ^ 4 := by
    rw [one_le_div hV4pos]
    exact hV4le
  have hκT : κ ≤ T + 1 := by
    have h := Work.GM.Trace.sep_card_le W T 1 (le_of_lt hTpos) le_rfl hW hsep
    rw [hκ]
    exact h
  have hκ2T : κ ≤ 2 * T := by linarith
  have hE4 : E ≤ κ ^ 4 := by
    rw [hE, hκ]
    exact energy_le_card_pow_four W
  have hNδ1 : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1R (le_of_lt hδ)
  have hmain : E ≤ 8 * κ * (N : ℝ) ^ 4 / V ^ 4 := by
    have h1 : κ ^ 4 ≤ κ * (2 * T) ^ 3 := by
      rw [show κ ^ 4 = κ * κ ^ 3 by ring]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hκnn hκ2T 3) hκnn
    have h2 : κ * (2 * T) ^ 3 = 8 * κ * T ^ 3 := by ring
    rw [h2] at h1
    have h3 : 8 * κ * T ^ 3 ≤ 8 * κ * (N : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hT3 (by positivity)
    have h4 : 8 * κ * (N : ℝ) ^ 4 ≤ 8 * κ * (N : ℝ) ^ 4 / V ^ 4 := by
      have h5 : (8 * κ * (N : ℝ) ^ 4) * (1 / V ^ 4) = 8 * κ * (N : ℝ) ^ 4 / V ^ 4 := by ring
      calc 8 * κ * (N : ℝ) ^ 4 = 8 * κ * (N : ℝ) ^ 4 * 1 := by ring
        _ ≤ 8 * κ * (N : ℝ) ^ 4 * (1 / V ^ 4) :=
            mul_le_mul_of_nonneg_left hV4inv (by positivity)
        _ = 8 * κ * (N : ℝ) ^ 4 / V ^ 4 := h5
    linarith [hE4, h1, h3, h4]
  have hXnn : 0 ≤ κ * (N : ℝ) ^ 4 / V ^ 4 := by
    have : (0:ℝ) ≤ κ * (N : ℝ) ^ 4 := mul_nonneg hκnn (by positivity)
    positivity
  have hYnn : 0 ≤ κ ^ ((21 : ℝ) / 8) * T ^ ((1 : ℝ) / 4) * (N : ℝ) / V ^ 2
      + κ ^ 3 * (N : ℝ) / V ^ 2 := by
    have h1 : (0:ℝ) ≤ κ ^ ((21 : ℝ) / 8) := Real.rpow_nonneg hκnn _
    have h2 : (0:ℝ) ≤ κ ^ 3 := by positivity
    have h3 : (0:ℝ) ≤ T ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
    have h4 : (0:ℝ) ≤ (N : ℝ) := by positivity
    positivity
  have hNδnn : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (by positivity) δ
  have hgoal1 : 8 * κ * (N : ℝ) ^ 4 / V ^ 4 ≤ CF * (N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4) := by
    have hYX : 0 ≤ (N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4) := mul_nonneg hNδnn hXnn
    have h0 : κ * (N : ℝ) ^ 4 / V ^ 4 ≤ (N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4) := by
      simpa using mul_le_mul_of_nonneg_right hNδ1 hXnn
    have h1 : 8 * (κ * (N : ℝ) ^ 4 / V ^ 4) ≤ 8 * ((N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4)) :=
      mul_le_mul_of_nonneg_left h0 (by norm_num)
    have h2 : 8 * ((N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4))
        ≤ CF * ((N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4)) :=
      mul_le_mul_of_nonneg_right hF8 hYX
    calc 8 * κ * (N : ℝ) ^ 4 / V ^ 4 = 8 * (κ * (N : ℝ) ^ 4 / V ^ 4) := by ring
      _ ≤ 8 * ((N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4)) := h1
      _ ≤ CF * ((N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4)) := h2
      _ = CF * (N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4) := by ring
  have hgoal2 : CF * (N : ℝ) ^ δ * (κ * (N : ℝ) ^ 4 / V ^ 4)
      ≤ CF * (N : ℝ) ^ δ *
        (κ * (N : ℝ) ^ 4 / V ^ 4 + κ ^ ((21 : ℝ) / 8) * T ^ ((1 : ℝ) / 4) * (N : ℝ) / V ^ 2
          + κ ^ 3 * (N : ℝ) / V ^ 2) := by
    have h3 : κ * (N : ℝ) ^ 4 / V ^ 4
        ≤ κ * (N : ℝ) ^ 4 / V ^ 4 + κ ^ ((21 : ℝ) / 8) * T ^ ((1 : ℝ) / 4) * (N : ℝ) / V ^ 2
          + κ ^ 3 * (N : ℝ) / V ^ 2 := by linarith [hYnn]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith [hmain, hgoal1, hgoal2]

/-- **The arithmetic core of the assembly.** Given the instantiated bounds coming from GM Lemma
11.4 (`hL4`), GM Lemma 11.8 (`hgs`) and GM Lemma 11.9 (`hL9`), the split `Stot = Ssmall + Slarge`,
and the parameters `K = Θ N^{1/m}`, `Λ = N^{12/m+4ε} ≤ N^δ`, this produces the bound of Proposition
11.1 for the total third moment.  All conversions of the raw bounds into the shape needed by the
arithmetic lemmas `arith_A`, `arith_B` happen here. -/
theorem energy_core {N : ℕ} (hN100 : 100 ≤ N) {δ ε : ℝ} {m : ℕ}
    {T V D κ E Stot Ssmall Slarge a1 g1 l1 Θ K Λ Cg CR C9 C2 C4b CD : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hm2 : 2 ≤ m) (hT1 : 1 ≤ T)
    (hV : 1 ≤ V) (hκ : 0 ≤ κ) (hE : 0 ≤ E)
    (ha1 : 0 ≤ a1) (hg1 : 0 ≤ g1) (hl1 : 0 ≤ l1) (hΘ1 : 1 ≤ Θ)
    (hg1eq : g1 = Cg * (CR + 1) ^ 4)
    (hl1eq : l1 = C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b + 1) ^ ((1 : ℝ) / 2) * (CD + 1))
    (hDTeq : D * T = (N : ℝ) ^ 2)
    (hK : K = Θ * (N : ℝ) ^ (1 / (m : ℝ)))
    (hΛ : Λ = (N : ℝ) ^ ((12 : ℝ) / (m : ℝ) + 4 * ε)) (hΛle : Λ ≤ (N : ℝ) ^ δ)
    (hsplit : Stot = Ssmall + Slarge)
    (hL4 : E ≤ a1 * (K + 1) ^ 2 / V ^ 2 * Stot
        + a1 * ((2 * (N : ℝ) + 1) / K ^ (m : ℝ)) ^ 2 / V ^ 2 * E)
    (hβ : a1 * ((2 * (N : ℝ) + 1) / K ^ (m : ℝ)) ^ 2 / V ^ 2 ≤ 1 / 2)
    (hgs : Ssmall ≤ Cg * (CR + 1) ^ 4 * (K + 1) ^ 4 * (N : ℝ) ^ ε * (D * T + (N : ℝ) ^ 2)
              * κ ^ ((1 : ℝ) / 2) * Real.sqrt E
            + Cg * (CR + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2 * κ ^ 3 / K ^ (3 * (m : ℝ)))
    (hL9 : Slarge ≤ C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b + 1) ^ ((1 : ℝ) / 2) * (CD + 1)
              * (N : ℝ) ^ (2 * ε)
              * ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
                  + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2)) :
    E ≤ max 8 (262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12
             + 512 * (a1 + 1) * (g1 + 1) * (l1 + 1) * (Θ + 1) ^ 6) * (N : ℝ) ^ δ
        * (κ * (N : ℝ) ^ 4 / V ^ 4 + κ ^ ((21 : ℝ) / 8) * T ^ ((1 : ℝ) / 4) * (N : ℝ) / V ^ 2
            + κ ^ 3 * (N : ℝ) / V ^ 2) := by
  -- ### the error term of `hL4` is absorbed
  have hE2 : E ≤ 2 * (a1 * (K + 1) ^ 2 / V ^ 2) * Stot := by
    have hβE : (a1 * ((2 * (N : ℝ) + 1) / K ^ (m : ℝ)) ^ 2 / V ^ 2) * E ≤ (1 / 2) * E :=
      mul_le_mul_of_nonneg_right hβ hE
    linarith [hL4, hβE]
  -- ### the four pieces of the `√E` / constant bounds
  set A1 : ℝ := 2 * g1 * (K + 1) ^ 4 * (N : ℝ) ^ ε * (N : ℝ) ^ 2 * κ ^ ((1 : ℝ) / 2)
    with hA1def
  set A2 : ℝ := l1 * (N : ℝ) ^ (2 * ε) * (N : ℝ) ^ 2 * κ ^ ((1 : ℝ) / 2) with hA2def
  set B1 : ℝ := g1 * (N : ℝ) ^ ε * (N : ℝ) ^ 2 * κ ^ 3 / K ^ (3 * (m : ℝ)) with hB1def
  set B23 : ℝ := l1 * (N : ℝ) ^ (2 * ε) *
    ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)) with hB23def
  have hN22 : (N : ℝ) ^ 2 + (N : ℝ) ^ 2 = 2 * (N : ℝ) ^ 2 := by ring
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hK]; positivity
  have hκr : ∀ z : ℝ, 0 ≤ κ ^ z := fun z => Real.rpow_nonneg hκ z
  have hNr : ∀ z : ℝ, 0 ≤ (N : ℝ) ^ z := fun z => Real.rpow_nonneg hN0 z
  have hTr : ∀ z : ℝ, 0 ≤ T ^ z := fun z => Real.rpow_nonneg hT0 z
  have hA1nn : 0 ≤ A1 := by
    rw [hA1def]
    have h1 : (0:ℝ) ≤ g1 := hg1
    have h2 : (0:ℝ) ≤ (N : ℝ) ^ ε := hNr ε
    have h3 : (0:ℝ) ≤ κ ^ ((1:ℝ)/2) := hκr _
    positivity
  have hA2nn : 0 ≤ A2 := by
    rw [hA2def]
    have h1 : (0:ℝ) ≤ l1 := hl1
    have h2 : (0:ℝ) ≤ (N : ℝ) ^ (2 * ε) := hNr _
    have h3 : (0:ℝ) ≤ κ ^ ((1:ℝ)/2) := hκr _
    positivity
  have hB1nn : 0 ≤ B1 := by
    rw [hB1def]
    have h1 : (0:ℝ) ≤ g1 := hg1
    have h2 : (0:ℝ) ≤ (N : ℝ) ^ ε := hNr ε
    have h3 : (0:ℝ) ≤ κ ^ 3 := by positivity
    positivity
  have hB23nn : 0 ≤ B23 := by
    rw [hB23def]
    have h1 : (0:ℝ) ≤ l1 := hl1
    have h2 : (0:ℝ) ≤ (N : ℝ) ^ (2 * ε) := hNr _
    have h3 : (0:ℝ) ≤ (N : ℝ) * κ ^ 3 := by positivity
    have h4 : (0:ℝ) ≤ (N : ℝ) * T ^ ((1:ℝ)/4) * κ ^ ((21:ℝ)/8) := by positivity
    positivity
  have hSsmall_bound : Ssmall ≤ A1 * Real.sqrt E + B1 := by
    have h := hgs
    rw [← hg1eq, hDTeq, hN22] at h
    refine h.trans (le_of_eq ?_)
    rw [hA1def, hB1def]
    ring
  have hSlarge_bound : Slarge ≤ A2 * Real.sqrt E + B23 := by
    have h := hL9
    rw [← hl1eq] at h
    refine h.trans (le_of_eq ?_)
    rw [hA2def, hB23def]
    ring
  have hStot_bound : Stot ≤ (A1 + A2) * Real.sqrt E + (B1 + B23) := by
    rw [hsplit]
    have h := add_le_add hSsmall_bound hSlarge_bound
    have heq : (A1 * Real.sqrt E + B1) + (A2 * Real.sqrt E + B23)
        = (A1 + A2) * Real.sqrt E + (B1 + B23) := by ring
    rw [heq] at h
    exact h
  -- ### rearrangement
  have hEAB : E ≤ (2 * (a1 * (K + 1) ^ 2 / V ^ 2) * (A1 + A2)) * Real.sqrt E
      + 2 * (a1 * (K + 1) ^ 2 / V ^ 2) * (B1 + B23) := by
    have hcoef : 0 ≤ 2 * (a1 * (K + 1) ^ 2 / V ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hStot_bound hcoef
    have heq : 2 * (a1 * (K + 1) ^ 2 / V ^ 2) * ((A1 + A2) * Real.sqrt E + (B1 + B23))
        = (2 * (a1 * (K + 1) ^ 2 / V ^ 2) * (A1 + A2)) * Real.sqrt E
          + 2 * (a1 * (K + 1) ^ 2 / V ^ 2) * (B1 + B23) := by ring
    rw [heq] at hmul
    linarith [hE2, hmul]
  have hAnn : 0 ≤ 2 * (a1 * (K + 1) ^ 2 / V ^ 2) * (A1 + A2) :=
    mul_nonneg (by positivity) (by linarith [hA1nn, hA2nn])
  have hBnn : 0 ≤ 2 * (a1 * (K + 1) ^ 2 / V ^ 2) * (B1 + B23) :=
    mul_nonneg (by positivity) (by linarith [hB1nn, hB23nn])
  have hrearr := le_two_mul_sq_add_two_mul_of_le_mul_sqrt_add hE hAnn hBnn hEAB
  -- ### the two arithmetic lemmas
  have hA := arith_A (N := N) (mm := m) (ε := ε) (δ := δ) (V := V) (κ := κ) (Λ := Λ) (Θ := Θ)
    (a1 := a1) (g1 := g1) (l1 := l1) (K := K)
    hN100 hm2 hε hδ hV hκ ha1 hg1 hl1 hΘ1 hK hΛ hΛle
  have hB := arith_B (N := N) (mm := m) (ε := ε) (δ := δ) (V := V) (κ := κ) (T := T) (Λ := Λ)
    (Θ := Θ) (a1 := a1) (g1 := g1) (l1 := l1) (K := K)
    hN100 hm2 hε hδ hV hκ hT1 ha1 hg1 hl1 hΘ1 hK hΛ hΛle
  set CA : ℝ := 262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 with hCAdef
  set CB : ℝ := 512 * (a1 + 1) * (g1 + 1) * (l1 + 1) * (Θ + 1) ^ 6 with hCBdef
  set CF : ℝ := max 8 (CA + CB) with hCFdef
  rw [← hA1def, ← hA2def] at hA
  rw [← hB1def, ← hB23def] at hB
  have hCAnn : 0 ≤ CA := by rw [hCAdef]; positivity
  have hCBnn : 0 ≤ CB := by rw [hCBdef]; positivity
  have hCFge : CA + CB ≤ CF := by rw [hCFdef]; exact le_max_right _ _
  have hNδnn : 0 ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (by positivity) δ
  set X : ℝ := κ * (N : ℝ) ^ 4 / V ^ 4 with hXdef
  set Y1 : ℝ := κ ^ ((21 : ℝ) / 8) * T ^ ((1 : ℝ) / 4) * (N : ℝ) / V ^ 2 with hY1def
  set Y2 : ℝ := κ ^ 3 * (N : ℝ) / V ^ 2 with hY2def
  have hXnn : 0 ≤ X := by
    rw [hXdef]
    have h1 : (0:ℝ) ≤ κ * (N : ℝ) ^ 4 := mul_nonneg hκ (by positivity)
    positivity
  have hY1nn : 0 ≤ Y1 := by
    rw [hY1def]
    have h1 : (0:ℝ) ≤ κ ^ ((21 : ℝ) / 8) := hκr _
    have h2 : (0:ℝ) ≤ T ^ ((1 : ℝ) / 4) := hTr _
    positivity
  have hY2nn : 0 ≤ Y2 := by
    rw [hY2def]
    have h1 : (0:ℝ) ≤ κ ^ 3 := by positivity
    positivity
  have h1 : E ≤ CA * (N : ℝ) ^ δ * X + CB * (N : ℝ) ^ δ * (Y1 + Y2) := by
    linarith [hrearr, hA, hB]
  have h2 : CA * (N : ℝ) ^ δ * X + CB * (N : ℝ) ^ δ * (Y1 + Y2)
      ≤ CF * (N : ℝ) ^ δ * (X + (Y1 + Y2)) := by
    have hCA_le : CA ≤ CF := by linarith [hCAnn, hCBnn, hCFge]
    have hCB_le : CB ≤ CF := by linarith [hCAnn, hCBnn, hCFge]
    have h12nn : 0 ≤ Y1 + Y2 := by linarith [hY1nn, hY2nn]
    have hE1 : CA * (N : ℝ) ^ δ * X ≤ CF * (N : ℝ) ^ δ * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA_le hNδnn) hXnn
    have hE2 : CB * (N : ℝ) ^ δ * (Y1 + Y2) ≤ CF * (N : ℝ) ^ δ * (Y1 + Y2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB_le hNδnn) h12nn
    linarith [hE1, hE2]
  linarith [h1, h2]

/-- **GM §11, Proposition 11.1 (assembly).** From the three remaining ingredients, each taken as a
hypothesis — GM Lemma 11.4 (`energy_le_R_cube`, the discrete third moment), GM Lemma 11.7
(`Rfun_local`, local constancy of `R`) and GM Lemma 11.9 (`gcd_large_K`, the large-GCD bound in the
form taking the *K-exposed* fourth moment) — GM's Proposition 11.1 follows using the gcd split at
`D = N²/T`, the locality Lemma 11.3 (`localize_smoothedPoly`, `localize_dirichlet`), Lemmas
11.5/11.6 (`second_moment_Rfun`, `fourth_moment_Rfun`), Lemma 11.8 (`gcd_small`) and the
rearrangement `E ≤ A√E + B ⟹ E ≤ 2A² + 2B`. -/
theorem assembly
    (hHB : Submission.GM.HBStatement)
    (hL4 : ∀ (m : ℕ), 2 ≤ m → ∃ C : ℝ, 0 < C ∧
      ∀ (Cloc : ℝ), 0 < Cloc →
      ∀ (N : ℕ), 1 ≤ N → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) → Submission.GM.Separated W 1 →
      ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      (∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
        ‖Submission.LargeValues.smoothedPoly N b t‖ ≤
          Cloc * (∫ u in t - K..t + K, ‖Submission.LargeValues.smoothedPoly N b u‖)
            + Cloc / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖)) →
      ∀ (V K : ℝ), 1 ≤ K → 0 < V →
        (∀ t ∈ W, V ≤ ‖Submission.LargeValues.smoothedPoly N b t‖) →
        (Submission.GM.energy W : ℝ) ≤
          C * (Cloc + 1) ^ 2 * (K + 1) ^ 2 / V ^ 2 *
              (∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
                ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
          + C * (Cloc + 1) ^ 2 * ((2 * N + 1 : ℝ) / K ^ (m : ℝ)) ^ 2 / V ^ 2
              * (Submission.GM.energy W))
    (hL7 : ∀ (m : ℕ), 2 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 T) → ∀ (v : ℝ), v ∈ Set.Icc (1 / 2 : ℝ) 2 → ∀ (K : ℝ), 1 ≤ K →
          ‖Submission.GM.Rfun W v‖ ≤
            C * T * (∫ v' in v - K / T..v + K / T, ‖Submission.GM.Rfun W v'‖)
              + C / K ^ (m : ℝ) * (W.card : ℝ))
    (hL9 : ∀ (m : ℕ), 2 ≤ m → ∀ (ε : ℝ), 0 < ε → 3 ≤ 5 * (m : ℝ) * ε →
        ∃ C : ℝ, 0 < C ∧
        ∀ (C₂ : ℝ), 0 < C₂ →
        (∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
          (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
          (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
              ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
            ≤ C₂ * T ^ ε * ((W.card : ℝ) ^ 2 * (M : ℝ) + (W.card : ℝ) * (M : ℝ) ^ 2
                + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * (M : ℝ))) →
        ∀ (C₄ Cloc : ℝ), 0 < C₄ → 0 < Cloc →
        (∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
          (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 → ∀ (K : ℝ), 1 ≤ K →
          (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
              ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
            ≤ C₄ * (Cloc + 1) ^ 2 * T ^ ε * (K + 1) ^ 2 *
                  ((W.card : ℝ) ^ 4 * (M : ℝ)
                    + (M : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
                    + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
                        * T ^ ((1 : ℝ) / 2) * (M : ℝ))
              + C₄ * (Cloc + 1) ^ 2 * T ^ ε * (((M : ℝ) + 1) / K ^ (m : ℝ)) ^ 2
                  * (Submission.GM.energy W : ℝ) * (W.card : ℝ) ^ 2) →
        ∀ (N : ℕ), 100 ≤ N → ∀ (W : Finset ℝ),
          (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
          Submission.GM.Separated W 1 →
          (∑ n1 ∈ Finset.Icc N (2 * N),
              ∑ n2 ∈ (Finset.Icc N (2 * N)).filter
                (fun n2 => (N : ℝ) ^ 2 / Submission.LargeValues.M N ≤ (Nat.gcd n1 n2 : ℝ)),
              ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
            ≤ C * (C₂ + 1) ^ ((1 : ℝ) / 2) * (C₄ + 1) ^ ((1 : ℝ) / 2)
                * (Cloc + 1) * (N : ℝ) ^ (2 * ε) *
                ((N : ℝ) * (W.card : ℝ) ^ 3
                  + (N : ℝ) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 4)
                      * (W.card : ℝ) ^ ((21 : ℝ) / 8)
                  + (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2) * (W.card : ℝ) ^ ((1 : ℝ) / 2)
                      * (N : ℝ) ^ 2)) :

    Submission.GM.EnergyStatement := by
  intro δ hδ
  obtain ⟨m, hm2, hmge⟩ : ∃ m : ℕ, 2 ≤ m ∧ 16 / δ ≤ (m : ℝ) := by
    obtain ⟨m₀, hm₀⟩ := exists_nat_ge (16 / δ)
    exact ⟨max 2 m₀, le_max_left 2 m₀, le_trans hm₀ (by exact_mod_cast le_max_right 2 m₀)⟩
  set ε : ℝ := δ / 16 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hmeps : 3 ≤ 5 * (m : ℝ) * ε := by
    have h2 : 16 ≤ (m : ℝ) * δ := by
      have h1 : 16 / δ ≤ (m : ℝ) := hmge
      rw [div_le_iff₀ hδ] at h1
      linarith
    rw [hεdef]
    nlinarith
  have hexp : (12 : ℝ) / (m : ℝ) + 4 * ε ≤ δ := by
    rw [hεdef]
    have hmpos : (0 : ℝ) < (m : ℝ) := by positivity
    have h1 : (12 : ℝ) / (m : ℝ) ≤ 3 * δ / 4 := by
      rw [div_le_iff₀ hmpos]
      have h3 : (3 * δ / 4) * (16 / δ) = 12 := by field_simp; ring
      have h4 := mul_le_mul_of_nonneg_left hmge (by positivity : (0 : ℝ) ≤ 3 * δ / 4)
      linarith [h3, h4]
    linarith
  obtain ⟨C4, hC4pos, hL4c⟩ := hL4 m hm2
  obtain ⟨CS, hCSpos, hCSb⟩ := Work.GM.Energy.LocalConstancy.localize_smoothedPoly m hm2
  obtain ⟨CD, hCDpos, hCDb⟩ := Work.GM.Energy.LocalConstancy.localize_dirichlet m hm2
  obtain ⟨C4b, hC4bpos, hfourthc⟩ :=
    Work.GM.Energy.EnergyCore.fourth_moment_Rfun hHB m hm2 ε hεpos
  obtain ⟨C2, hC2pos, hsecondc⟩ := Work.GM.Energy.Moments.second_moment_Rfun hHB ε hεpos
  obtain ⟨C9, hC9pos, hL9c⟩ := hL9 m hm2 ε hεpos hmeps
  obtain ⟨Cg, hCgpos, hgcdsc⟩ := Work.GM.Energy.EnergyCore.gcd_small m hm2 ε hεpos
  obtain ⟨C7, hC7pos, hL7c⟩ := hL7 m hm2
  obtain ⟨Cm2, hCm2pos, hL2c⟩ := Work.GM.Energy.RMoments.Rfun_integral_sq
  obtain ⟨Cm4, hCm4pos, hL4ic⟩ := Work.GM.Energy.RMoments.Rfun_integral_pow4
  clear hHB hL4 hL7 hL9
  set CR : ℝ := max C7 (max Cm2 (max Cm4 1)) with hCRdef
  have hC7CR : C7 ≤ CR := by rw [hCRdef]; exact le_max_left _ _
  have hCm2CR : Cm2 ≤ CR := by
    rw [hCRdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCm4CR : Cm4 ≤ CR := by
    rw [hCRdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCRpos : 0 < CR := lt_of_lt_of_le hC7pos hC7CR
  set Θ : ℝ := 20 * (C4 + 1) * (CS + 1) + 1 with hΘdef
  have hΘ1 : 1 ≤ Θ := by rw [hΘdef]; nlinarith [hC4pos, hCSpos]
  have hΘsq : 400 * C4 * (CS + 1) ^ 2 ≤ Θ ^ 2 := by
    rw [hΘdef]
    nlinarith [hC4pos, hCSpos, mul_pos hC4pos hCSpos, sq_nonneg (C4 + 1), sq_nonneg (CS + 1),
      sq_nonneg ((C4 + 1) * (CS + 1))]
  set a1 : ℝ := C4 * (CS + 1) ^ 2 with ha1def
  have ha1nn : 0 ≤ a1 := by rw [ha1def]; positivity
  set g1 : ℝ := Cg * (CR + 1) ^ 4 with hg1def
  have hg1nn : 0 ≤ g1 := by rw [hg1def]; positivity
  set l1 : ℝ := C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b + 1) ^ ((1 : ℝ) / 2) * (CD + 1) with hl1def
  have hl1nn : 0 ≤ l1 := by rw [hl1def]; positivity
  set CA : ℝ := 262144 * (a1 + 1) ^ 2 * (g1 + 1) ^ 2 * (l1 + 1) ^ 2 * (Θ + 1) ^ 12 with hCAdef
  set CB : ℝ := 512 * (a1 + 1) * (g1 + 1) * (l1 + 1) * (Θ + 1) ^ 6 with hCBdef
  set CF : ℝ := max 8 (CA + CB) with hCFdef
  have hCF8 : 8 ≤ CF := by rw [hCFdef]; exact le_max_left _ _
  refine ⟨CF, lt_of_lt_of_le (by norm_num) hCF8, 100, ?_⟩
  intro N hN100 W hWsub hsep b hb V hVpos hbig
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hWsubMN : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N) := hWsub
  set T : ℝ := Submission.LargeValues.M N with hTdef
  have hWsubT : ∀ t ∈ W, t ∈ Set.Icc 0 T := by
    intro t ht; rw [hTdef]; exact hWsubMN t ht
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Submission.LargeValues.M_ge_one hN1
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hT3 : T ^ 3 ≤ (N : ℝ) ^ 4 := by rw [hTdef]; exact M_pow_three_le N hN1
  set κ : ℝ := (W.card : ℝ) with hκdef
  have hκnn : 0 ≤ κ := by rw [hκdef]; positivity
  set E : ℝ := (Submission.GM.energy W : ℝ) with hEdef
  have hEnn : 0 ≤ E := by rw [hEdef]; positivity
  set K : ℝ := Θ * (N : ℝ) ^ (1 / (m : ℝ)) with hKdef
  set Λ : ℝ := (N : ℝ) ^ ((12 : ℝ) / (m : ℝ) + 4 * ε) with hΛdef
  have hΛle : Λ ≤ (N : ℝ) ^ δ := by
    rw [hΛdef]
    exact Real.rpow_le_rpow_of_exponent_le hN1R hexp
  have hK1 : 1 ≤ K := by
    rw [hKdef]
    exact (kpow_facts (Θ := Θ) (N := (N : ℝ)) (mm := m) hΘ1 hN1R (by omega)).1
  by_cases hVge : 1 ≤ V
  · -- ### Main case
    have hloc : ∀ (K' : ℝ), 1 ≤ K' → ∀ t : ℝ,
        ‖Submission.LargeValues.smoothedPoly N b t‖ ≤
          CS * (∫ u in t - K'..t + K', ‖Submission.LargeValues.smoothedPoly N b u‖)
            + CS / K' ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖b n‖) :=
      fun K' hK' t => hCSb N hN1 b hb K' hK' t
    have hL4app := hL4c CS hCSpos N hN1 W hWsubMN hsep b hb hloc V K hK1 hVpos hbig
    rw [← hEdef, ← ha1def] at hL4app
    set Stot : ℝ := ∑ n1 ∈ Finset.Icc N (2 * N), ∑ n2 ∈ Finset.Icc N (2 * N),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 with hStotdef
    have hβ : a1 * ((2 * (N : ℝ) + 1) / K ^ (m : ℝ)) ^ 2 / V ^ 2 ≤ 1 / 2 := by
      have hb := beta_le (N := (N : ℝ)) (C4 := C4) (CS := CS) (Θ := Θ) (V := V) (mm := m)
        (le_of_lt hC4pos) (le_of_lt hCSpos) hΘ1 hVge hN1R (by omega) hΘsq
      rw [← ha1def, ← hKdef] at hb
      exact hb
    set D : ℝ := (N : ℝ) ^ 2 / T with hDdef
    have hDTeq : D * T = (N : ℝ) ^ 2 := by
      rw [hDdef, div_mul_cancel₀ _ (ne_of_gt hTpos)]
    have hD1 : 1 ≤ D := by
      have h1 : D = (N : ℝ) ^ (4 / 5 : ℝ) := by
        have h2 : (N : ℝ) ^ 2 = (N : ℝ) ^ ((2 : ℝ)) := (Real.rpow_natCast (N : ℝ) 2).symm
        have h3 : (N : ℝ) ^ ((2 : ℝ)) / (N : ℝ) ^ (6 / 5 : ℝ)
            = (N : ℝ) ^ ((2 : ℝ) - 6 / 5) := (Real.rpow_sub hNpos (2 : ℝ) (6 / 5 : ℝ)).symm
        have h4 : (N : ℝ) ^ ((2 : ℝ) - 6 / 5) = (N : ℝ) ^ (4 / 5 : ℝ) := by norm_num
        rw [hDdef, hTdef, Submission.LargeValues.M, h2, h3, h4]
      rw [h1]
      exact Real.one_le_rpow hN1R (by norm_num)
    have hlocR := loc_of_big (m := m) hC7CR hL7c
    have hL2R := l2_of_big hCm2CR hL2c
    have hL4R := l4_of_big hCm4CR hL4ic
    have hgs := hgcdsc CR hCRpos hlocR hL2R hL4R N hN1 W hWsubMN hsep K hK1 D hD1
    set Ssmall : ℝ := ∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => (Nat.gcd n1 n2 : ℝ) ≤ D),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 with hSsmalldef
    have hL9app : (∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => D ≤ (Nat.gcd n1 n2 : ℝ)),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3)
        ≤ C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b + 1) ^ ((1 : ℝ) / 2) * (CD + 1)
            * (N : ℝ) ^ (2 * ε) *
            ((N : ℝ) * (W.card : ℝ) ^ 3
              + (N : ℝ) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 4)
                  * (W.card : ℝ) ^ ((21 : ℝ) / 8)
              + (Submission.GM.energy W : ℝ) ^ ((1 : ℝ) / 2) * (W.card : ℝ) ^ ((1 : ℝ) / 2)
                  * (N : ℝ) ^ 2) := by
      have h := hL9c C2 hC2pos hsecondc C4b CD hC4bpos hCDpos (hfourthc CD hCDpos hCDb)
        N hN100 W hWsubMN hsep
      rw [← hTdef] at h
      exact h
    set Slarge : ℝ := ∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => ¬((Nat.gcd n1 n2 : ℝ) ≤ D)),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3 with hSlargedef
    have hSlarge_le : Slarge ≤ (∑ n1 ∈ Finset.Icc N (2 * N),
        ∑ n2 ∈ (Finset.Icc N (2 * N)).filter (fun n2 => D ≤ (Nat.gcd n1 n2 : ℝ)),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 3) := by
      rw [hSlargedef]
      refine Finset.sum_le_sum fun n1 _ => ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro n2 hn2
        simp only [Finset.mem_filter] at hn2 ⊢
        exact ⟨hn2.1, le_of_lt (lt_of_not_ge hn2.2)⟩
      · intro n2 _ _
        positivity
    have hsplit : Stot = Ssmall + Slarge := by
      rw [hStotdef, hSsmalldef, hSlargedef]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n1 _ => ?_
      exact (Finset.sum_filter_add_sum_filter_not _ (fun n2 => (Nat.gcd n1 n2 : ℝ) ≤ D) _).symm
    have hsqrtE : E ^ ((1 : ℝ) / 2) = Real.sqrt E := (Real.sqrt_eq_rpow E).symm
    rw [← hκdef] at hgs
    rw [← hEdef] at hgs
    rw [hsqrtE] at hgs
    have hL9comb : Slarge ≤ C9 * (C2 + 1) ^ ((1 : ℝ) / 2) * (C4b + 1) ^ ((1 : ℝ) / 2)
        * (CD + 1) * (N : ℝ) ^ (2 * ε) *
        ((N : ℝ) * κ ^ 3 + (N : ℝ) * T ^ ((1 : ℝ) / 4) * κ ^ ((21 : ℝ) / 8)
          + Real.sqrt E * κ ^ ((1 : ℝ) / 2) * (N : ℝ) ^ 2) := by
      refine hSlarge_le.trans ?_
      rw [← hκdef] at hL9app
      rw [← hEdef] at hL9app
      rw [hsqrtE] at hL9app
      rw [← hTdef] at hL9app
      exact hL9app
    have hcore := energy_core (N := N) (δ := δ) (ε := ε) (m := m) (T := T) (V := V) (D := D)
      (κ := κ) (E := E) (Stot := Stot) (Ssmall := Ssmall) (Slarge := Slarge)
      (a1 := a1) (g1 := g1) (l1 := l1) (Θ := Θ) (K := K) (Λ := Λ)
      (Cg := Cg) (CR := CR) (C9 := C9) (C2 := C2) (C4b := C4b) (CD := CD)
      hN100 hδ hεpos hm2 hT1 hVge hκnn hEnn ha1nn hg1nn hl1nn hΘ1 hg1def hl1def hDTeq hKdef
      hΛdef hΛle hsplit hL4app hβ hgs hL9comb
    rw [← hCAdef, ← hCBdef, ← hCFdef] at hcore
    exact hcore
  · -- ### Trivial case `V < 1`
    have hVlt : V < 1 := lt_of_not_ge hVge
    exact energy_trivial (N := N) (T := T) (V := V) (κ := κ) (E := E) (CF := CF) (δ := δ)
      hN1 hWsubT hsep hκdef hEdef hT1 hT3 hVpos hVlt hCF8 hδ


end Work.GM.Energy.EnergyCore2
