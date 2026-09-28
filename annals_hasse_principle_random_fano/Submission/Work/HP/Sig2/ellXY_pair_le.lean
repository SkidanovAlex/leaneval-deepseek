import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.window_sum_ge3
import Submission.Work.HP.ball_prod_window_ge3
import Submission.Work.HP.ball_prod_window_r2
import Submission.Work.HP.dyadic_sum_r2
import Submission.Work.HP.window_arith_r2
import Submission.Work.HP.dmin_le_exists_prim
import Submission.Work.HP.Sig2.ellXY_le_sum
import Submission.Work.HP.Sig2.minkowski_prod
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.Sig2.dyadic_sum_ge3
import Submission.Work.HP.Sig2.window_sum_arith
import Submission.Work.HP.Sig2.window_sum_r2
import Submission.Work.HP.Sig2.Tset_finite

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.Sig2

open Work.HP

/-! ## Elementary helpers about the successive minima -/

/-- In an integral lattice every non-zero vector has Euclidean norm `≥ 1`, hence every
successive minimum `lam L j` with `1 ≤ j ≤ rk L` is `≥ 1`. -/
lemma lam_ge_one' {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) {j : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ rk L) : 1 ≤ lam L j := by
  obtain ⟨g, hg, hgind⟩ := exists_linIndep_card L hjk
  have hne : ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin j → (ι → ℤ), (∀ i, f i ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ i, eNorm (f i) ≤ r}).Nonempty :=
    ⟨(∑ i, eNorm (g i)) + 1, by
        have h0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => eNorm_nonneg (g i))
        linarith, g, hg, hgind, fun i => by
      have h1 := Finset.single_le_sum (fun i _ => eNorm_nonneg (g i)) (Finset.mem_univ i)
      linarith⟩
  rw [lam]
  refine le_csInf hne ?_
  rintro r ⟨hr0, f, hf, hind, hfr⟩
  exact le_trans (one_le_eNorm_of_ne_zero (hind.ne_zero ⟨0, by omega⟩)) (hfr ⟨0, by omega⟩)

/-- The dyadic window `kwin` of the successive minima: the exponents `⌈log₂ λ_{j+1}(L)⌉`. -/
lemma kwin_spec' {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (L : Submodule ℤ (ι → ℤ)) (hr2 : 2 ≤ r)
    (hr : rk L = r) :
    (∀ j : Fin r, lam L (j.1 + 1) ≤ (2 : ℝ) ^ (kwin r L j)) ∧
    (∀ j : Fin r, (2 : ℝ) ^ (kwin r L j) ≤ 2 * lam L (j.1 + 1)) ∧
    Monotone (kwin r L) ∧
    (∀ M : ℝ, 1 ≤ M → (∏ j : Fin r, (2 : ℝ) ^ (kwin r L j)) ≤ M →
      (∑ j : Fin r, kwin r L j) ≤ ⌈Real.logb 2 M⌉₊) := by
  have hle : ∀ j : Fin r, j.1 + 1 ≤ rk L := by
    intro j; rw [hr]; exact Nat.succ_le_of_lt j.2
  have hpos : ∀ j : Fin r, 0 < lam L (j.1 + 1) := fun j => lam_pos L (by omega) (hle j)
  have hg1 : ∀ j : Fin r, 1 ≤ lam L (j.1 + 1) := fun j => lam_ge_one' L (by omega) (hle j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have h1 : Real.logb 2 (lam L (j.1 + 1)) ≤ ((kwin r L j : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : (2:ℝ) ^ (Real.logb 2 (lam L (j.1+1))) ≤ (2:ℝ) ^ ((kwin r L j : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    rw [Real.rpow_logb (show (0:ℝ) < 2 by norm_num) (by norm_num) (hpos j),
        Real.rpow_natCast] at h3
    exact h3
  · intro j
    have hlog0 : (0:ℝ) ≤ Real.logb 2 (lam L (j.1 + 1)) :=
      Real.logb_nonneg (show (1:ℝ) < 2 by norm_num) (hg1 j)
    have h1 : ((kwin r L j : ℕ) : ℝ) < Real.logb 2 (lam L (j.1 + 1)) + 1 :=
      Nat.ceil_lt_add_one hlog0
    have h3 : (2:ℝ) ^ ((kwin r L j : ℕ) : ℝ) ≤ (2:ℝ) ^ (Real.logb 2 (lam L (j.1+1)) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt h1)
    rw [Real.rpow_natCast, Real.rpow_add (show (0:ℝ) < 2 by norm_num),
        Real.rpow_logb (show (0:ℝ) < 2 by norm_num) (by norm_num) (hpos j), Real.rpow_one] at h3
    linarith
  · intro a b hab
    simp only [kwin]
    apply Nat.ceil_mono
    apply (Real.logb_le_logb (show (1:ℝ) < 2 by norm_num) (hpos a) (hpos b)).mpr
    exact lam_mono L (by omega) (hle b)
  · intro M hM hprod
    rw [Finset.prod_pow_eq_pow_sum] at hprod
    have h2 : ((∑ j : Fin r, kwin r L j : ℕ) : ℝ) ≤ Real.logb 2 M := by
      rw [Real.le_logb_iff_rpow_le (show (1:ℝ) < 2 by norm_num) (by linarith)]
      rw [Real.rpow_natCast]
      exact hprod
    have := le_trans h2 (Nat.le_ceil (Real.logb 2 M))
    exact_mod_cast this


/-! ## Ball-count bounds derived from Schmidt's bound -/

/-- `(2 T/b)^{r-1} (2 T/a) = 2^r T^r/(a b^{r-1})`. -/
lemma two_mul_div_pow_mul' {a b T : ℝ} {r : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hr : 1 ≤ r) :
    (2 * (T / b)) ^ (r - 1) * (2 * (T / a)) = 2 ^ r * T ^ r / (a * b ^ (r - 1)) := by
  have h : r - 1 + 1 = r := by omega
  rw [show (2 : ℝ) ^ r = 2 ^ (r - 1) * 2 from by rw [← pow_succ, h],
      show T ^ r = T ^ (r - 1) * T from by rw [← pow_succ, h],
      mul_pow, div_pow]
  field_simp

/-- Schmidt's bound specialised to `T = X ≥ λ₁`: `#(L ∩ B_X) ≤ K X^{rk L} / λ₁^{rk L}`. -/
lemma hsmallX_of {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hsch : ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (X : ℝ), 1 ≤ X → lam L 1 ≤ X →
      (ballCount L X : ℝ) ≤ K * X ^ rk L / lam L 1 ^ rk L := by
  obtain ⟨Kc, hKc, hKc'⟩ := hsch
  refine ⟨Kc * 2 ^ (Fintype.card ι), by positivity, ?_⟩
  intro L X hX hlX
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have h2c : (1:ℝ) ≤ 2 ^ (Fintype.card ι) := one_le_pow₀ (by norm_num)
  rcases Nat.eq_zero_or_pos (rk L) with hrk | hrk
  · have h := hKc' L X hX
    rw [hrk, Finset.range_zero, Finset.prod_empty, mul_one] at h
    rw [hrk]
    simp only [pow_zero, div_one, mul_one]
    exact le_trans h (le_mul_of_one_le_right hKc.le h2c)
  · have hlam1 : 0 < lam L 1 := lam_pos L le_rfl hrk
    have hprod : (∏ i ∈ Finset.range (rk L), (X / lam L (i + 1) + 1))
        ≤ 2 ^ (rk L) * X ^ (rk L) / lam L 1 ^ (rk L) := by
      have hpt : ∀ i ∈ Finset.range (rk L), (X / lam L (i + 1) + 1) ≤ 2 * (X / lam L 1) := by
        intro i hi
        have hi' : i + 1 ≤ rk L := by have := Finset.mem_range.mp hi; omega
        have h1' : lam L 1 ≤ lam L (i + 1) := lam_mono L (by omega) hi'
        have h2' : 0 < lam L (i + 1) := lam_pos L (by omega) hi'
        have h3 : X / lam L (i + 1) ≤ X / lam L 1 := div_le_div_of_nonneg_left hX0 hlam1 h1'
        have h4 : 1 ≤ X / lam L 1 := (one_le_div hlam1).mpr hlX
        linarith
      calc (∏ i ∈ Finset.range (rk L), (X / lam L (i + 1) + 1))
          ≤ ∏ i ∈ Finset.range (rk L), (2 * (X / lam L 1)) := by
            refine Finset.prod_le_prod₀ (fun i hi => ?_) hpt
            have h2' : 0 < lam L (i + 1) :=
              lam_pos L (by omega) (by have := Finset.mem_range.mp hi; omega)
            have : 0 ≤ X / lam L (i + 1) := div_nonneg hX0 h2'.le
            linarith
        _ = (2 * (X / lam L 1)) ^ (rk L) := by rw [Finset.prod_const, Finset.card_range]
        _ = 2 ^ (rk L) * X ^ (rk L) / lam L 1 ^ (rk L) := by rw [mul_pow, div_pow]; ring
    have h2 : (2:ℝ) ^ (rk L) ≤ 2 ^ (Fintype.card ι) :=
      pow_le_pow_right₀ (by norm_num) (rk_le_card L)
    have hD : (0:ℝ) ≤ Kc * X ^ (rk L) / lam L 1 ^ (rk L) := by positivity
    calc (ballCount L X : ℝ)
        ≤ Kc * (2 ^ (rk L) * X ^ (rk L) / lam L 1 ^ (rk L)) :=
          le_trans (hKc' L X hX) (mul_le_mul_of_nonneg_left hprod hKc.le)
      _ = (Kc * X ^ (rk L) / lam L 1 ^ (rk L)) * 2 ^ (rk L) := by ring
      _ ≤ (Kc * X ^ (rk L) / lam L 1 ^ (rk L)) * 2 ^ (Fintype.card ι) :=
          mul_le_mul_of_nonneg_left h2 hD
      _ = Kc * 2 ^ (Fintype.card ι) * X ^ (rk L) / lam L 1 ^ (rk L) := by ring

/-- Schmidt's bound specialised to `T ≥ λ₂`: `#(L ∩ B_T) ≤ K T^{rk L}/(λ₁ λ₂^{rk L - 1})`. -/
lemma hsmallY_of {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hsch : ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L → lam L 2 ≤ Y →
      (ballCount L Y : ℝ) ≤ K * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
  obtain ⟨Kc, hKc, hKc'⟩ := hsch
  refine ⟨Kc * 2 ^ (Fintype.card ι), by positivity, ?_⟩
  intro L Y hY hrk hlY
  have hY0 : 0 ≤ Y := le_trans zero_le_one hY
  have h1 : 0 < lam L 1 := lam_pos L le_rfl (by omega)
  have h2 : 0 < lam L 2 := lam_pos L (by norm_num) hrk
  have hmono : lam L 1 ≤ lam L 2 := lam_mono L (by norm_num) hrk
  have hss := hKc' L Y hY
  have hpb : (∏ i ∈ Finset.range (rk L), (Y / lam L (i + 1) + 1))
      ≤ 2 ^ (rk L) * Y ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
    have hsplit : (∏ i ∈ Finset.range (rk L), (Y / lam L (i + 1) + 1))
        = (∏ i ∈ Finset.range (rk L - 1), (Y / lam L (i + 1 + 1) + 1))
          * (Y / lam L 1 + 1) := by
      have h := Finset.prod_range_succ' (fun i => Y / lam L (i + 1) + 1) (rk L - 1)
      rw [show rk L - 1 + 1 = rk L from by omega] at h
      exact h
    have hstep : (∏ i ∈ Finset.range (rk L - 1), (Y / lam L (i + 1 + 1) + 1))
        ≤ (∏ i ∈ Finset.range (rk L - 1), (2 * (Y / lam L 2))) := by
      refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
      · have hi' : i + 1 + 1 ≤ rk L := by have := Finset.mem_range.mp hi; omega
        have hpos : 0 < lam L (i + 1 + 1) := lam_pos L (by omega) hi'
        have : 0 ≤ Y / lam L (i + 1 + 1) := div_nonneg hY0 hpos.le
        linarith
      · have hi' : i + 1 + 1 ≤ rk L := by have := Finset.mem_range.mp hi; omega
        have hle : lam L 2 ≤ lam L (i + 1 + 1) := lam_mono L (by omega) hi'
        have h3 : Y / lam L (i + 1 + 1) ≤ Y / lam L 2 := div_le_div_of_nonneg_left hY0 h2 hle
        have h4 : 1 ≤ Y / lam L 2 := (one_le_div h2).mpr hlY
        linarith
    have hconst : (∏ i ∈ Finset.range (rk L - 1), (2 * (Y / lam L 2)))
        = (2 * (Y / lam L 2)) ^ (rk L - 1) := by rw [Finset.prod_const, Finset.card_range]
    have hf0 : (Y / lam L 1 + 1) ≤ 2 * (Y / lam L 1) := by
      have hge : 1 ≤ Y / lam L 1 := (one_le_div h1).mpr (le_trans hmono hlY)
      linarith
    have hid := two_mul_div_pow_mul' (a := lam L 1) (b := lam L 2) (T := Y) (r := rk L)
      h1.ne' h2.ne' (by omega)
    have hstep' : (∏ i ∈ Finset.range (rk L - 1), (Y / lam L (i + 1 + 1) + 1))
        ≤ (2 * (Y / lam L 2)) ^ (rk L - 1) := le_trans hstep (le_of_eq hconst)
    calc (∏ i ∈ Finset.range (rk L), (Y / lam L (i + 1) + 1))
        = (∏ i ∈ Finset.range (rk L - 1), (Y / lam L (i + 1 + 1) + 1)) * (Y / lam L 1 + 1) := hsplit
      _ ≤ (2 * (Y / lam L 2)) ^ (rk L - 1) * (2 * (Y / lam L 1)) := by
          refine le_trans (mul_le_mul_of_nonneg_right hstep' (by positivity)) ?_
          exact mul_le_mul_of_nonneg_left hf0 (by positivity)
      _ = 2 ^ (rk L) * Y ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1)) := hid
  have h2c : (2:ℝ) ^ (rk L) ≤ 2 ^ (Fintype.card ι) :=
    pow_le_pow_right₀ (by norm_num) (rk_le_card L)
  have hD : (0:ℝ) ≤ Kc * Y ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1)) := by positivity
  calc (ballCount L Y : ℝ)
      ≤ Kc * (2 ^ (rk L) * Y ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1))) :=
        le_trans hss (mul_le_mul_of_nonneg_left hpb hKc.le)
    _ = Kc * Y ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1)) * 2 ^ (rk L) := by ring
    _ ≤ Kc * Y ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1)) * 2 ^ (Fintype.card ι) :=
        mul_le_mul_of_nonneg_left h2c hD
    _ = Kc * 2 ^ (Fintype.card ι) * Y ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1)) := by ring


/-! ## The rank-`≥ 3` lattice sum, from `window_sum_ge3` -/

lemma hws_ge3_of (n r : ℕ) (hn : 2 ≤ n) (hr : 3 ≤ r) (hrn : r ≤ n + 1)
    (hnum : ∃ Knum : ℝ, 0 < Knum ∧ ∀ (s : Fin r → ℝ)
      (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j) →
      (F.card : ℝ) ≤ Knum * ∏ j : Fin r, s j ^ (n + 1 + r + 1 - 2 * (j.1 + 1)))
    (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (hmink : ∀ L : Submodule ℤ (Fin (n + 1) → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L)
    (hsch : ∃ Kc : ℝ, 0 < Kc ∧ ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ Kc * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
    (harith : ∃ Karith : ℝ, 0 < Karith ∧ ∀ (Δ : ℝ), 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r =>
          Finset.range (⌈Real.logb 2 ((2:ℝ)^r * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈Real.logb 2 ((2:ℝ)^r * Kmink * (Δ + 1))⌉₊ then
          (2:ℝ)^(∑ j : Fin r, k j * (n + 1 + r + 1 - 2 * (j.1 + 1))) /
            ((2:ℝ)^(r * k ⟨0, by omega⟩) *
              (2:ℝ)^(k ⟨0, by omega⟩ + (r - 1) * k ⟨1, by omega⟩))
        else 0))
      ≤ Karith * Δ^(n-1) * Real.log (2*Δ)^(2*min (r-2) 1)) :
    ∃ Kws : ℝ, 0 < Kws ∧ ∀ (X Y Δ : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ Δ → X ≤ Y →
      ∀ (T : Finset (Submodule ℤ (Fin (n + 1) → ℤ))),
      (∀ L ∈ T, IsPrimLat L ∧ rk L = r ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ X ∧ lam L 2 ≤ Y) →
      (∑ L ∈ T, (ballCount L X : ℝ) * (ballCount L Y : ℝ)) ≤
        Kws * X^r * Y^r * Δ^(n-1) * Real.log (2*Δ)^(2*min (r-2) 1) := by
  obtain ⟨Knum, hKnum, hnum'⟩ := hnum
  obtain ⟨Karith, hKarith, harith'⟩ := harith
  obtain ⟨K1, hK1, hK1'⟩ := hsmallX_of hsch
  obtain ⟨K2, hK2, hK2'⟩ := hsmallY_of hsch
  have hKs : 0 < max K1 K2 := lt_of_lt_of_le hK1 (le_max_left _ _)
  have hsX : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), 1 ≤ X → lam L 1 ≤ X →
      (ballCount L X : ℝ) ≤ max K1 K2 * X ^ rk L / lam L 1 ^ rk L := by
    intro L X hX hlX
    refine le_trans (hK1' L X hX hlX) ?_
    have hZ : (0:ℝ) ≤ X ^ rk L / lam L 1 ^ rk L :=
      div_nonneg (pow_nonneg (le_trans zero_le_one hX) _) (pow_nonneg (lam_nonneg L 1) _)
    calc K1 * X ^ rk L / lam L 1 ^ rk L = K1 * (X ^ rk L / lam L 1 ^ rk L) := by ring
      _ ≤ max K1 K2 * (X ^ rk L / lam L 1 ^ rk L) :=
          mul_le_mul_of_nonneg_right (le_max_left K1 K2) hZ
      _ = max K1 K2 * X ^ rk L / lam L 1 ^ rk L := by ring
  have hsY : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L → lam L 2 ≤ Y →
      (ballCount L Y : ℝ) ≤ max K1 K2 * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
    intro L Y hY hrk hlY
    refine le_trans (hK2' L Y hY hrk hlY) ?_
    have hZ : (0:ℝ) ≤ Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) :=
      div_nonneg (pow_nonneg (le_trans zero_le_one hY) _)
        (mul_nonneg (lam_nonneg L 1) (pow_nonneg (lam_nonneg L 2) _))
    calc K2 * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))
        = K2 * (Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))) := by ring
      _ ≤ max K1 K2 * (Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))) :=
          mul_le_mul_of_nonneg_right (le_max_right K1 K2) hZ
      _ = max K1 K2 * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by ring
  refine ⟨Knum * (max K1 K2)^2 * 2^(2*r) * Karith, by positivity, ?_⟩
  intro X Y Δ hX hY hΔ hXY T hT
  exact window_sum_ge3 n r hn hr hrn Knum hKnum hnum' Kmink hKmink hmink
    (fun L hrL => kwin_spec' r L (by omega) hrL) (max K1 K2) hKs hsX hsY
    (fun L k X Y hrL hk2 hX hY hlX hlY =>
      ball_prod_window_ge3 n r hn hr hrn (max K1 K2) hKs hsX hsY L hrL k hk2 X Y hX hY hlX hlY)
    Karith hKarith harith' X Y Δ hX hY hΔ hXY T hT


/-! ## Assembling the lattice sums -/

/-- A finset contained in `Tset` has cardinality at most the `ncard` of `Tset`. -/
lemma card_le_ncard_Tset {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (s : Fin r → ℝ)
    (F : Finset (Submodule ℤ (ι → ℤ)))
    (hF : ∀ L ∈ F, IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j)
    (hfin : ({L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = r ∧
      ∀ j : Fin r, lam L (j.1 + 1) ≤ s j}).Finite) :
    (F.card : ℝ) ≤ (({L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = r ∧
      ∀ j : Fin r, lam L (j.1 + 1) ≤ s j}).ncard : ℝ) := by
  have hsub : (F : Set (Submodule ℤ (ι → ℤ))) ⊆
      {L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = r ∧
        ∀ j : Fin r, lam L (j.1 + 1) ≤ s j} := by
    intro L hL
    exact hF L (by simpa using hL)
  have h := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset] at h
  exact_mod_cast h

/-- The reduction hypothesis for `ellXY_le_sum`, from `dmin_le_exists_prim`. -/
lemma hred' (n r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n + 1) :
    ∀ (x y : Fin (n + 1) → ℤ) (D : ℝ), LinearIndependent ℤ ![x, y] → dmin r {x, y} ≤ D →
      ∃ L : Submodule ℤ (Fin (n + 1) → ℤ), IsPrimLat L ∧ rk L = r ∧ x ∈ L ∧ y ∈ L ∧
        detL L ≤ D + 1 :=
  fun x y D hxy hd => Work.HP.dmin_le_exists_prim (Fin (n + 1)) r x y D hxy hr
    (by rw [Fintype.card_fin]; omega) hd

/-- The refined rank-`2` ball-count bound `#(L ∩ B_X) ≤ K (X²/(λ₁λ₂) + X/λ₁ + 1)`. -/
lemma hsmall2_r2_of {n : ℕ}
    (hsch : ∃ Kc : ℝ, 0 < Kc ∧ ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (T : ℝ), 1 ≤ T →
      (ballCount L T : ℝ) ≤ Kc * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), rk L = 2 → 1 ≤ X →
      (ballCount L X : ℝ) ≤ K * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1) := by
  obtain ⟨Kc, hKc, hKc'⟩ := hsch
  refine ⟨2 * Kc, by positivity, ?_⟩
  intro L X h2 hX
  have hX0 : 0 ≤ X := le_trans zero_le_one hX
  have hn2 : 2 ≤ rk L := by omega
  have h1 : 0 < lam L 1 := lam_pos L le_rfl (by omega)
  have h2' : 0 < lam L 2 := lam_pos L (by norm_num) (by omega)
  have hmono : lam L 1 ≤ lam L 2 := lam_mono L (by norm_num) (by omega)
  have hss := hKc' L X hX
  have hprod : (∏ i ∈ Finset.range (rk L), (X / lam L (i + 1) + 1))
      = (X / lam L 1 + 1) * (X / lam L 2 + 1) := by
    rw [h2, Finset.prod_range_succ, Finset.prod_range_succ]; simp
  rw [hprod] at hss
  have hdiv : X / lam L 2 ≤ X / lam L 1 := div_le_div_of_nonneg_left hX0 h1 hmono
  have hexp : (X / lam L 1 + 1) * (X / lam L 2 + 1)
      = X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + X / lam L 2 + 1 := by
    field_simp; ring
  have hmain : (X / lam L 1 + 1) * (X / lam L 2 + 1)
      ≤ 2 * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1) := by
    have hA : (0:ℝ) ≤ X ^ 2 / (lam L 1 * lam L 2) :=
      div_nonneg (sq_nonneg X) (le_of_lt (mul_pos h1 h2'))
    rw [hexp]; linarith [hdiv, hA]
  calc (ballCount L X : ℝ) ≤ Kc * ((X / lam L 1 + 1) * (X / lam L 2 + 1)) := hss
    _ ≤ Kc * (2 * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1)) :=
        mul_le_mul_of_nonneg_left hmain hKc.le
    _ = 2 * Kc * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1) := by ring

/-- The rank-`2` pair count: `ℓ_{2,n}(X,Y;Δ) ≪ X²Y²Δ^{n-1}`. -/
lemma ellXY_pair_le_two (n : ℕ) (hn : 2 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n 2 X Y Δ : ℝ) ≤ K * X ^ 2 * Y ^ 2 * Δ ^ (n - 1) := by
  obtain ⟨Kmink0, hKmink0, hmink0⟩ := minkowski_prod (ι := Fin (n + 1))
  obtain ⟨Kc, hKc, hKc'⟩ := schmidt_bound (ι := Fin (n + 1))
  set Kmink : ℝ := max Kmink0 1 with hKminkdef
  have hKmink : 1 ≤ Kmink := le_max_right _ _
  have hmink : ∀ L : Submodule ℤ (Fin (n + 1) → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L := by
    intro L
    exact le_trans (hmink0 L) (mul_le_mul_of_nonneg_right (le_max_left _ _) (detL_nonneg L))
  obtain ⟨Knum, hKnum, hnum'⟩ := num_lattices_of (ι := Fin (n + 1)) Kmink (by linarith) hmink
  have hnum : ∀ (s : Fin 2 → ℝ) (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j) →
      (F.card : ℝ) ≤ Knum * ∏ j : Fin 2, s j ^ (n + 1 + 2 + 1 - 2 * (j.1 + 1)) := by
    intro s F hs hF
    have hkey := hnum' 2 s hs
    simp only [Fintype.card_fin] at hkey
    exact le_trans (card_le_ncard_Tset (ι := Fin (n + 1)) 2 s F hF
      (Tset_finite (ι := Fin (n + 1)) 2 s)) hkey
  obtain ⟨K1, hK1, hK1'⟩ := hsmallX_of (ι := Fin (n + 1)) ⟨Kc, hKc, hKc'⟩
  obtain ⟨K2, hK2, hK2'⟩ := hsmallY_of (ι := Fin (n + 1)) ⟨Kc, hKc, hKc'⟩
  obtain ⟨K3, hK3, hK3'⟩ := hsmall2_r2_of (n := n) ⟨Kc, hKc, hKc'⟩
  set Ksmall : ℝ := max (max K1 K2) K3 with hKsmalldef
  have hKs : 0 < Ksmall := lt_of_lt_of_le hK1 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hsX : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), 1 ≤ X → lam L 1 ≤ X →
      (ballCount L X : ℝ) ≤ Ksmall * X ^ rk L / lam L 1 ^ rk L := by
    intro L X hX hlX
    refine le_trans (hK1' L X hX hlX) ?_
    have hZ : (0:ℝ) ≤ X ^ rk L / lam L 1 ^ rk L :=
      div_nonneg (pow_nonneg (le_trans zero_le_one hX) _) (pow_nonneg (lam_nonneg L 1) _)
    calc K1 * X ^ rk L / lam L 1 ^ rk L = K1 * (X ^ rk L / lam L 1 ^ rk L) := by ring
      _ ≤ Ksmall * (X ^ rk L / lam L 1 ^ rk L) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_left K1 K2) (le_max_left _ _)) hZ
      _ = Ksmall * X ^ rk L / lam L 1 ^ rk L := by ring
  have hsY : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (Y : ℝ), 1 ≤ Y → 2 ≤ rk L → lam L 2 ≤ Y →
      (ballCount L Y : ℝ) ≤ Ksmall * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
    intro L Y hY hrk hlY
    refine le_trans (hK2' L Y hY hrk hlY) ?_
    have hZ : (0:ℝ) ≤ Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) :=
      div_nonneg (pow_nonneg (le_trans zero_le_one hY) _)
        (mul_nonneg (lam_nonneg L 1) (pow_nonneg (lam_nonneg L 2) _))
    calc K2 * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))
        = K2 * (Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))) := by ring
      _ ≤ Ksmall * (Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1))) :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right K1 K2) (le_max_left _ _)) hZ
      _ = Ksmall * Y ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by ring
  have hs2 : ∀ (L : Submodule ℤ (Fin (n + 1) → ℤ)) (X : ℝ), rk L = 2 → 1 ≤ X →
      (ballCount L X : ℝ) ≤ Ksmall * (X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1) := by
    intro L X hrL hX
    refine le_trans (hK3' L X hrL hX) ?_
    have hZ : (0:ℝ) ≤ X ^ 2 / (lam L 1 * lam L 2) + X / lam L 1 + 1 := by
      have h1 : 0 < lam L 1 := lam_pos L le_rfl (by omega)
      have h2 : 0 < lam L 2 := lam_pos L (by norm_num) (by omega)
      have : 0 ≤ X ^ 2 / (lam L 1 * lam L 2) := div_nonneg (by positivity) (by positivity)
      have : 0 ≤ X / lam L 1 := div_nonneg (le_trans zero_le_one hX) h1.le
      linarith
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hZ
  obtain ⟨Cdy, hCdy, hdy'⟩ := dyadic_sum_r2 (n + 1) (by omega)
  obtain ⟨Karith, hKarith, harith2⟩ := window_arith_r2 n hn Kmink hKmink Cdy hCdy
    (fun X Y L' hX hY hL => by
      have h := hdy' X Y L' hX hY hL
      have he : ((n + 1 : ℕ) : ℝ) - 2 = (↑n : ℝ) + 1 - 2 := by push_cast; ring
      rw [he] at h
      exact h)
  refine ⟨Knum * Ksmall ^ 2 * 16 * Karith, by positivity, ?_⟩
  intro X Y Δ hX hY hΔ
  rcases le_total X Y with hXY | hYX
  · obtain ⟨T, hT, hle⟩ := ellXY_le_sum n 2 (by norm_num) (by omega)
      (hred' n 2 (by norm_num) (by omega)) X Y Δ hX hY hΔ hXY
    refine le_trans hle ?_
    exact window_sum_r2 n hn Knum hKnum hnum Kmink hKmink hmink
      (fun L hrL => kwin_spec' 2 L (by norm_num) hrL) Ksmall hKs hs2 hsY
      (fun L k X Y hrL hk2 hX hY hXY hlX hlY =>
        ball_prod_window_r2 n hn Ksmall hKs hs2 hsY L hrL k hk2 X Y hX hY hXY hlX hlY)
      Karith hKarith harith2 X Y Δ hX hY hΔ hXY T hT
  · rw [ellXY_comm n 2 X Y Δ]
    obtain ⟨T, hT, hle⟩ := ellXY_le_sum n 2 (by norm_num) (by omega)
      (hred' n 2 (by norm_num) (by omega)) Y X Δ hY hX hΔ hYX
    refine le_trans hle ?_
    refine le_trans (window_sum_r2 n hn Knum hKnum hnum Kmink hKmink hmink
      (fun L hrL => kwin_spec' 2 L (by norm_num) hrL) Ksmall hKs hs2 hsY
      (fun L k X Y hrL hk2 hX hY hXY hlX hlY =>
        ball_prod_window_r2 n hn Ksmall hKs hs2 hsY L hrL k hk2 X Y hX hY hXY hlX hlY)
      Karith hKarith harith2 Y X Δ hY hX hΔ hYX T hT) (le_of_eq ?_)
    ring

/-- The rank-`≥ 3` pair count at `X = Y`. -/
lemma ellXY_pair_le_ge3 (n r : ℕ) (hn : 2 ≤ n) (hr : 3 ≤ r) (hrn : r ≤ n + 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      (ellXY n r X X Δ : ℝ)
        ≤ K * X ^ (2 * r) * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
  obtain ⟨Kmink0, hKmink0, hmink0⟩ := minkowski_prod (ι := Fin (n + 1))
  obtain ⟨Kc, hKc, hKc'⟩ := schmidt_bound (ι := Fin (n + 1))
  set Kmink : ℝ := max Kmink0 1 with hKminkdef
  have hKmink : 1 ≤ Kmink := le_max_right _ _
  have hmink : ∀ L : Submodule ℤ (Fin (n + 1) → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L := by
    intro L
    exact le_trans (hmink0 L) (mul_le_mul_of_nonneg_right (le_max_left _ _) (detL_nonneg L))
  obtain ⟨Knum, hKnum, hnum'⟩ := num_lattices_of (ι := Fin (n + 1)) Kmink (by linarith) hmink
  have hnum : ∃ (Knum : ℝ), 0 < Knum ∧ ∀ (s : Fin r → ℝ)
      (F : Finset (Submodule ℤ (Fin (n + 1) → ℤ))), (∀ j, 1 ≤ s j) →
      (∀ L ∈ F, IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j) →
      (F.card : ℝ) ≤ Knum * ∏ j : Fin r, s j ^ (n + 1 + r + 1 - 2 * (j.1 + 1)) := by
    refine ⟨Knum, hKnum, ?_⟩
    intro s F hs hF
    have hkey := hnum' r s hs
    simp only [Fintype.card_fin] at hkey
    exact le_trans (card_le_ncard_Tset (ι := Fin (n + 1)) r s F hF
      (Tset_finite (ι := Fin (n + 1)) r s)) hkey
  obtain ⟨Cdya, hCdya, hdya'⟩ := dyadic_sum_ge3 (n + 1) r hr (by omega)
  obtain ⟨Karith, hKarith, harith'⟩ := window_sum_arith n r hn hr hrn Kmink hKmink Cdya hCdya
    (fun L' hL => by
      have h := hdya' L' hL
      have he : ((n + 1 : ℕ) : ℝ) - 2 = (↑n : ℝ) + 1 - 2 := by push_cast; ring
      rw [he] at h
      exact h)
  obtain ⟨Kws, hKws, hws⟩ := hws_ge3_of n r hn hr hrn hnum Kmink hKmink hmink
    ⟨Kc, hKc, hKc'⟩ ⟨Karith, hKarith, harith'⟩
  refine ⟨Kws, hKws, ?_⟩
  intro X Δ hX hΔ
  obtain ⟨T, hT, hle⟩ := ellXY_le_sum n r (by omega) hrn (hred' n r (by omega) hrn) X X Δ hX hX hΔ le_rfl
  refine le_trans hle ?_
  have h := hws X X Δ hX hX hΔ le_rfl T hT
  have hpow : X ^ (2 * r) = X ^ r * X ^ r := by
    rw [show 2 * r = r + r from by ring, pow_add]
  rw [hpow]
  refine le_trans h (le_of_eq ?_)
  ring

/-- **Target lemma.**  Pair counts at `X = Y`: `ℓ_{r,n}(X,X;Δ) ≪ X^{2r} Δ^{n-1} (log Δ)^{2 min(r-2,1)}`. -/
theorem ellXY_pair_le (n : ℕ) (hn : 2 ≤ n) (r : ℕ) (hr : 2 ≤ r) (hrn : r ≤ n + 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      (Work.HP.ellXY n r X X Δ : ℝ) ≤
        K * X ^ (2 * r) * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
  rcases eq_or_lt_of_le hr with h2 | h3
  · subst h2
    obtain ⟨K, hK, hK'⟩ := ellXY_pair_le_two n hn
    refine ⟨K, hK, ?_⟩
    intro X Δ hX hΔ
    have h := hK' X X Δ hX hX hΔ
    have hmin : 2 * min (2 - 2) 1 = 0 := by norm_num
    have hlog : Real.log (2 * Δ) ^ (2 * min (2 - 2) 1) = 1 := by rw [hmin, pow_zero]
    rw [hlog, mul_one]
    have hpow : X ^ (2 * 2) = X ^ 2 * X ^ 2 := by ring
    rw [hpow]
    refine le_trans h (le_of_eq ?_)
    ring
  · have hr3 : 3 ≤ r := by omega
    exact ellXY_pair_le_ge3 n r hn hr3 hrn

end Work.HP.Sig2
