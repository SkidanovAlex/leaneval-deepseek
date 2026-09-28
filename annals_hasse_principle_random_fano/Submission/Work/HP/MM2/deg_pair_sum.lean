import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.FM3.ell_two_count_free
import Submission.Work.HP.EE.ellXY_two_pub
import Submission.Work.HP.DegSq.ball_sum_inv_pow
import Submission.Work.HP.Sig2.key_lemma_two_vectors
import Submission.Work.HP.degen_sum
import Submission.Work.HP.Sig2.DminPairLe
import Submission.Work.HP.MM2.deg_pair_sum_arith

/-! Guidance from the project lead (the requester):
this is node L0j `deg_pair_sum` of DESIGN_REVIEW.md §1 (the paper's `G_{d,n}` pair sum,
specialised, unweighted).  The proof reduces to
* `FM3.ell_two_count_free` (the `𝔡₂`-count of `x`),
* `EE.ellXY_two_pub` (the `r = 2` pair count `ℓ_{2,n}(X,Y;Δ) ≪ X²Y²Δ^{n-1}`),
* `Work.HP.MM2.deg_pair_sum_arith` (pure dyadic arithmetic, proved separately),
* the interpolation `min(a,b) ≤ a^{1/n} b^{1-1/n}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset MeasureTheory
open scoped BigOperators

namespace Work.HP.MM2

open Work.HP

namespace DegPairSum

/-- The dyadic index of a real.  For `a ≥ 1`, `2 ^ shIdx a ≤ a < 2 ^ (shIdx a + 1)`. -/
def shIdx (a : ℝ) : ℕ := Nat.floor (Real.logb 2 a)

/-- The set of pairs summed over in `deg_pair_sum`. -/
def PSet (n : ℕ) (X t : ℝ) : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
  {p | LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ X ∧ eNorm p.2 ≤ X ∧
    t * dmin 2 ({p.1} : Set (Fin (n + 1) → ℤ)) ≤ eNorm p.1}

/-- The weight of a pair in `deg_pair_sum`. -/
def PW (d n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℝ :=
  1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * eNorm p.1 ^ (d - 1) * eNorm p.2 ^ (d - 1))

/-- The triple of dyadic indices of a pair. -/
def shP (n : ℕ) (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) : ℕ × ℕ × ℕ :=
  (shIdx (eNorm p.1), shIdx (eNorm p.2),
    shIdx (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))))

/-- The box of dyadic triples; the third index is coupled to the first two because
`𝔡₂(x,y) ≤ ‖x‖ ‖y‖`. -/
def triBox (K : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (K + 1)).product
    ((Finset.range (K + 1)).product (Finset.range (2 * K + 3)))).filter
    (fun k => k.2.2 ≤ k.1 + k.2.1 + 2)

lemma mem_triBox {K : ℕ} {k : ℕ × ℕ × ℕ} :
    k ∈ triBox K ↔ k.1 ≤ K ∧ k.2.1 ≤ K ∧ k.2.2 ≤ 2 * K + 2 ∧
      k.2.2 ≤ k.1 + k.2.1 + 2 := by
  simp only [triBox, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_range]
  omega

/-! ## Elementary dyadic facts -/

lemma two_pow_shIdx_le (a : ℝ) (ha : 1 ≤ a) : (2 : ℝ) ^ (shIdx a) ≤ a := by
  have hpos : 0 < a := lt_of_lt_of_le one_pos ha
  have hfloor : ((shIdx a : ℕ) : ℝ) ≤ Real.logb 2 a := by
    rw [shIdx]
    exact Nat.floor_le (Real.logb_nonneg (by norm_num) ha)
  have h := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hfloor
  rw [Real.rpow_logb (by norm_num) (by norm_num) hpos] at h
  rwa [Real.rpow_natCast] at h

lemma lt_two_pow_shIdx (a : ℝ) (ha : 0 < a) : a < (2 : ℝ) ^ (shIdx a + 1) := by
  have hlt : Real.logb 2 a < (shIdx a : ℝ) + 1 := by
    rw [shIdx]
    exact Nat.lt_floor_add_one _
  have h := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hlt
  rw [Real.rpow_logb (by norm_num) (by norm_num) ha] at h
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_natCast,
    ← pow_succ] at h
  exact h

lemma shIdx_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : shIdx a ≤ shIdx b := by
  rw [shIdx, shIdx]
  exact Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ha hab)

/-! ## Ball count -/

lemma ncard_ball_le (m : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    (({v : Fin m → ℤ | eNorm v ≤ R} : Set (Fin m → ℤ)).ncard : ℝ) ≤ 5 ^ m * R ^ m := by
  have hbox : ({v : Fin m → ℤ | eNorm v ≤ R} : Set (Fin m → ℤ)) ⊆
      ↑(Fintype.piFinset (fun _ : Fin m => Finset.Icc (-(((⌈R⌉₊ : ℕ) : ℤ))) ((⌈R⌉₊ : ℕ) : ℤ))) := by
    intro v hv
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 : |(v i : ℝ)| ≤ eNorm v := MDBasic.abs_apply_le_eNorm v i
    have h2 : |(v i : ℝ)| ≤ R := le_trans h1 hv
    have h3 : |(v i : ℝ)| ≤ (⌈R⌉₊ : ℝ) := le_trans h2 (Nat.le_ceil R)
    exact ⟨by exact_mod_cast (abs_le.mp h3).1, by exact_mod_cast (abs_le.mp h3).2⟩
  have hcard : ((Fintype.piFinset
        (fun _ : Fin m => Finset.Icc (-(((⌈R⌉₊ : ℕ) : ℤ))) ((⌈R⌉₊ : ℕ) : ℤ))).card : ℝ)
      = (2 * (⌈R⌉₊ : ℝ) + 1) ^ m := by
    rw [(box_card (ι := Fin m) (⌈R⌉₊ : ℕ)).1, Fintype.card_fin]
  have hle : (({v : Fin m → ℤ | eNorm v ≤ R} : Set (Fin m → ℤ)).ncard : ℝ)
      ≤ ((Fintype.piFinset
        (fun _ : Fin m => Finset.Icc (-(((⌈R⌉₊ : ℕ) : ℤ))) ((⌈R⌉₊ : ℕ) : ℤ))).card : ℕ) := by
    have h := Set.ncard_le_ncard hbox (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  have h2R : (⌈R⌉₊ : ℝ) ≤ 2 * R := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ R by linarith)
    linarith
  have h5 : 2 * (⌈R⌉₊ : ℝ) + 1 ≤ 5 * R := by linarith
  calc (({v : Fin m → ℤ | eNorm v ≤ R} : Set (Fin m → ℤ)).ncard : ℝ)
      ≤ ((Fintype.piFinset
        (fun _ : Fin m => Finset.Icc (-(((⌈R⌉₊ : ℕ) : ℤ))) ((⌈R⌉₊ : ℕ) : ℤ))).card : ℕ) := hle
    _ = (2 * (⌈R⌉₊ : ℝ) + 1) ^ m := hcard
    _ ≤ (5 * R) ^ m := pow_le_pow_left₀ (by positivity) h5 m
    _ = 5 ^ m * R ^ m := by rw [mul_pow]

/-! ## Two facts about `𝔡₂` -/

lemma dmin_pair_le_mul (n : ℕ) (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℤ ![x, y]) :
    dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x * eNorm y := by
  obtain ⟨h1, h2⟩ := Sig2.DminPairLe x y h
  have hg : (1 : ℝ) ≤ (gcdMinors2 x y : ℝ) := by
    have h2' : (0 : ℤ) < gcdMinors2 x y := h2
    have : (1 : ℤ) ≤ gcdMinors2 x y := by omega
    exact_mod_cast this
  have hw : wedgeNorm x y ≤ eNorm x * eNorm y := by
    rw [wedgeNorm]
    calc Real.sqrt (eNorm x ^ 2 * eNorm y ^ 2 - dotR (toR x) (toR y) ^ 2)
        ≤ Real.sqrt (eNorm x ^ 2 * eNorm y ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          nlinarith [sq_nonneg (dotR (toR x) (toR y))]
      _ = eNorm x * eNorm y := by
          rw [show eNorm x ^ 2 * eNorm y ^ 2 = (eNorm x * eNorm y) ^ 2 by ring]
          exact Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))
      ≤ wedgeNorm x y / (gcdMinors2 x y : ℝ) := h1
    _ ≤ wedgeNorm x y / 1 := by
        refine div_le_div_of_nonneg_left (Real.sqrt_nonneg _) one_pos hg
    _ = wedgeNorm x y := by rw [div_one]
    _ ≤ eNorm x * eNorm y := hw

/-! ## Weights bound -/

lemma PW_le_shell (d n : ℕ) {X t : ℝ} {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)}
    (hp : p ∈ PSet n X t) (k : ℕ × ℕ × ℕ) (hk : shP n p = k) :
    PW d n p ≤ 1 / ((2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) *
      (2 : ℝ) ^ k.2.2) := by
  obtain ⟨hli, -, -, -⟩ := hp
  have hx0 : p.1 ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
  have hy0 : p.2 ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
  have hk1 : shIdx (eNorm p.1) = k.1 := by
    simpa [shP] using congrArg Prod.fst hk
  have hk2 : shIdx (eNorm p.2) = k.2.1 := by
    simpa [shP] using congrArg (fun q : ℕ × ℕ × ℕ => q.2.1) hk
  have hk3 : shIdx (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) = k.2.2 := by
    simpa [shP] using congrArg (fun q : ℕ × ℕ × ℕ => q.2.2) hk
  have hx : (2 : ℝ) ^ k.1 ≤ eNorm p.1 := by
    rw [← hk1]; exact two_pow_shIdx_le _ (DegSq.one_le_eNorm hx0)
  have hy : (2 : ℝ) ^ k.2.1 ≤ eNorm p.2 := by
    rw [← hk2]; exact two_pow_shIdx_le _ (DegSq.one_le_eNorm hy0)
  have hD : (2 : ℝ) ^ k.2.2 ≤ dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) := by
    rw [← hk3]; exact two_pow_shIdx_le _ (Sig2.one_le_dmin_two_pair _ _ hli)
  have hxnn : (0 : ℝ) ≤ eNorm p.1 := Real.sqrt_nonneg _
  have hynn : (0 : ℝ) ≤ eNorm p.2 := Real.sqrt_nonneg _
  have hDnn : (0 : ℝ) ≤ dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) :=
    le_of_lt (lt_of_lt_of_le zero_lt_one (Sig2.one_le_dmin_two_pair _ _ hli))
  have h1 : (2 : ℝ) ^ (k.1 * (d - 1)) ≤ eNorm p.1 ^ (d - 1) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hx (d - 1)
  have h2 : (2 : ℝ) ^ (k.2.1 * (d - 1)) ≤ eNorm p.2 ^ (d - 1) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hy (d - 1)
  rw [PW]
  refine one_div_le_one_div_of_le (by positivity) ?_
  rw [show (2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) * (2 : ℝ) ^ k.2.2
      = (2 : ℝ) ^ k.2.2 * (2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) by ring]
  exact mul_le_mul (mul_le_mul hD h1 (by positivity) hDnn) h2 (by positivity)
    (mul_nonneg hDnn (pow_nonneg hxnn _))

/-! ## Per-shell cardinality bound -/

/-- The fibre of a dyadic shell has at most `min(a,b)` elements, where `a` is the bound
obtained from the `𝔡₂`-count of `x` and the ball count of `y`, and `b` is the bound obtained
from the rank-`2` pair count at level `2 ^ (k.2.2 + 1)`. -/
lemma shell_card_le (d n : ℕ) (K₁ K₂ : ℝ) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hn : 3 ≤ n)
    (h₁ : ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      (({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧
          dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ}).ncard : ℝ)
        ≤ K₁ * X ^ 2 * Δ ^ n * Real.log (2 * Δ))
    (h₂ : ∀ X Y Δ : ℝ, 1 ≤ X → 1 ≤ Y → 1 ≤ Δ →
      (ellXY n 2 X Y Δ : ℝ) ≤ K₂ * X ^ 2 * Y ^ 2 * Δ ^ (n - 1))
    {X t : ℝ} (hX : 2 ≤ X) (ht : 1 ≤ t) (k : ℕ × ℕ × ℕ) :
    ((PSet n X t ∩ {p | shP n p = k}).ncard : ℝ)
      ≤ min (K₁ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * (((2 : ℝ) ^ (k.1 + 1)) / t) ^ n *
            Real.log (2 * (((2 : ℝ) ^ (k.1 + 1)) / t) + 1) *
            ((5 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (k.2.1 + 1)) ^ (n + 1)))
          (K₂ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * ((2 : ℝ) ^ (k.2.1 + 1)) ^ 2 *
            ((2 : ℝ) ^ (k.2.2 + 1)) ^ (n - 1)) := by
  classical
  set u₁ : ℝ := (2 : ℝ) ^ (k.1 + 1) with hu₁def
  set u₂ : ℝ := (2 : ℝ) ^ (k.2.1 + 1) with hu₂def
  set D₁ : ℝ := (2 : ℝ) ^ (k.2.2 + 1) with hD₁def
  set Δ₁ : ℝ := u₁ / t with hΔ₁def
  have hu₁le : 1 ≤ u₁ := by rw [hu₁def]; exact one_le_pow₀ (by norm_num)
  have hu₂le : 1 ≤ u₂ := by rw [hu₂def]; exact one_le_pow₀ (by norm_num)
  have hD₁le : 1 ≤ D₁ := by rw [hD₁def]; exact one_le_pow₀ (by norm_num)
  have ht0 : 0 < t := by linarith
  have hu₁pos : 0 < u₁ := by rw [hu₁def]; positivity
  have hΔ₁pos : 0 < Δ₁ := by rw [hΔ₁def]; exact div_pos hu₁pos ht0
  refine le_min ?_ ?_
  · -- the `x`-count times the `y`-ball bound
    have hsub : PSet n X t ∩ {p | shP n p = k} ⊆
        ({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ u₁ ∧
            dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ₁} ×ˢ
          {y : Fin (n + 1) → ℤ | eNorm y ≤ u₂}) := by
      rintro ⟨x, y⟩ ⟨hpS, hpk⟩
      obtain ⟨hli, h1X, h2X, hcon⟩ := hpS
      have hk1 : shIdx (eNorm x) = k.1 := by
        simpa [shP] using congrArg Prod.fst hpk
      have hk2 : shIdx (eNorm y) = k.2.1 := by
        simpa [shP] using congrArg (fun q : ℕ × ℕ × ℕ => q.2.1) hpk
      have hx0 : x ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
      have hxpos : 0 < eNorm x := lt_of_lt_of_le zero_lt_one (DegSq.one_le_eNorm hx0)
      have hxlt : eNorm x < u₁ := by
        have h := lt_two_pow_shIdx (eNorm x) hxpos
        rw [hk1] at h
        rwa [hu₁def]
      have hylt : eNorm y < u₂ := by
        have hy0 : y ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
        have hypos : 0 < eNorm y := lt_of_lt_of_le zero_lt_one (DegSq.one_le_eNorm hy0)
        have h := lt_two_pow_shIdx (eNorm y) hypos
        rw [hk2] at h
        rwa [hu₂def]
      have hdle : dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ₁ := by
        have h : t * dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) < u₁ := lt_of_le_of_lt hcon hxlt
        rw [hΔ₁def, le_div_iff₀ ht0]
        linarith
      exact ⟨⟨hx0, le_of_lt hxlt, hdle⟩, le_of_lt hylt⟩
    have hfinA : (({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ u₁ ∧
          dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ₁} ×ˢ
        {y : Fin (n + 1) → ℤ | eNorm y ≤ u₂})).Finite :=
      ((MDBasic.finite_eNorm_le (ι := Fin (n + 1)) u₁).subset
        (fun v hv => hv.2.1)).prod (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) u₂)
    have hn1 := Set.ncard_le_ncard hsub hfinA
    rw [Set.ncard_prod] at hn1
    have hxbd : (({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ u₁ ∧
          dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ₁}).ncard : ℝ)
        ≤ K₁ * u₁ ^ 2 * Δ₁ ^ n * Real.log (2 * Δ₁ + 1) := by
      by_cases hΔ : 1 ≤ Δ₁
      · have h := h₁ u₁ Δ₁ hu₁le hΔ
        refine le_trans ?_ (le_of_eq rfl)
        refine le_trans ?_ (le_of_eq rfl)
        exact le_trans h (mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith) (by linarith)) (by positivity))
      · push_neg at hΔ
        have hemp : ({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ u₁ ∧
            dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ₁} : Set (Fin (n + 1) → ℤ)) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro x ⟨hx0, -, hxd⟩
          have h1 := one_le_dmin_two_single n (by omega) x hx0
          linarith
        rw [hemp, Set.ncard_empty]
        simp only [Nat.cast_zero]
        have hlog : (0 : ℝ) ≤ Real.log (2 * Δ₁ + 1) := Real.log_nonneg (by linarith)
        have hAn : (0 : ℝ) ≤ K₁ * u₁ ^ 2 * Δ₁ ^ n := by positivity
        positivity
    have hybd : (({y : Fin (n + 1) → ℤ | eNorm y ≤ u₂} : Set (Fin (n + 1) → ℤ)).ncard : ℝ)
        ≤ (5 : ℝ) ^ (n + 1) * u₂ ^ (n + 1) := ncard_ball_le (n + 1) u₂ hu₂le
    calc ((PSet n X t ∩ {p | shP n p = k}).ncard : ℝ)
        ≤ (({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ u₁ ∧
              dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Δ₁}).ncard : ℝ) *
            (({y : Fin (n + 1) → ℤ | eNorm y ≤ u₂} : Set (Fin (n + 1) → ℤ)).ncard : ℝ) := by
          exact_mod_cast hn1
      _ ≤ (K₁ * u₁ ^ 2 * Δ₁ ^ n * Real.log (2 * Δ₁ + 1)) *
            ((5 : ℝ) ^ (n + 1) * u₂ ^ (n + 1)) := by
          refine mul_le_mul hxbd hybd ?_ ?_
          · positivity
          · exact le_of_lt (mul_pos (by positivity) (Real.log_pos (by linarith)))
  · -- the rank-two pair count
    have hsub : PSet n X t ∩ {p | shP n p = k} ⊆
        {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
          eNorm p.1 ≤ u₁ ∧ eNorm p.2 ≤ u₂ ∧
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ D₁} := by
      rintro ⟨x, y⟩ ⟨hpS, hpk⟩
      obtain ⟨hli, h1X, h2X, hcon⟩ := hpS
      have hk1 : shIdx (eNorm x) = k.1 := by
        simpa [shP] using congrArg Prod.fst hpk
      have hk2 : shIdx (eNorm y) = k.2.1 := by
        simpa [shP] using congrArg (fun q : ℕ × ℕ × ℕ => q.2.1) hpk
      have hk3 : shIdx (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) = k.2.2 := by
        simpa [shP] using congrArg (fun q : ℕ × ℕ × ℕ => q.2.2) hpk
      have hx0 : x ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
      have hy0 : y ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
      have hxpos : 0 < eNorm x := lt_of_lt_of_le zero_lt_one (DegSq.one_le_eNorm hx0)
      have hypos : 0 < eNorm y := lt_of_lt_of_le zero_lt_one (DegSq.one_le_eNorm hy0)
      have hDpos : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) :=
        lt_of_lt_of_le zero_lt_one (Sig2.one_le_dmin_two_pair _ _ hli)
      have hxlt : eNorm x < u₁ := by
        have h := lt_two_pow_shIdx (eNorm x) hxpos
        rw [hk1] at h
        rwa [hu₁def]
      have hylt : eNorm y < u₂ := by
        have h := lt_two_pow_shIdx (eNorm y) hypos
        rw [hk2] at h
        rwa [hu₂def]
      have hDlt : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) < D₁ := by
        have h := lt_two_pow_shIdx (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) hDpos
        rw [hk3] at h
        rwa [hD₁def]
      exact ⟨hli, le_of_lt hxlt, le_of_lt hylt, le_of_lt hDlt⟩
    have hfinB : ({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
          LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ u₁ ∧ eNorm p.2 ≤ u₂ ∧
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ D₁} : Set _).Finite :=
      ((MDBasic.finite_eNorm_le (ι := Fin (n + 1)) u₁).prod
        (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) u₂)).subset
        (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)
    have hn2 := Set.ncard_le_ncard hsub hfinB
    have hE : (({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
          LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ u₁ ∧ eNorm p.2 ≤ u₂ ∧
          dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ D₁} : Set _).ncard)
        = ellXY n 2 u₁ u₂ D₁ := rfl
    calc ((PSet n X t ∩ {p | shP n p = k}).ncard : ℝ)
        ≤ (({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
            LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ u₁ ∧ eNorm p.2 ≤ u₂ ∧
            dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ D₁} : Set _).ncard : ℝ) := by
          exact_mod_cast hn2
      _ = (ellXY n 2 u₁ u₂ D₁ : ℝ) := by rw [hE]
      _ ≤ K₂ * u₁ ^ 2 * u₂ ^ 2 * D₁ ^ (n - 1) := h₂ u₁ u₂ D₁ hu₁le hu₂le hD₁le

end DegPairSum

open DegPairSum in
/-- (L0j) THE pair summation (the paper's `G_{d,n}` interpolation, specialised). Dyadic in
`‖x‖, ‖y‖, 𝔡₂(x,y)`; box count `≤ min(ℓ₁(X; X/t)·#B(Y), ℓ₂(X,Y;Δ))` from
`FM3.ell_two_count_free` and `EE.ellXY_two_pub`; `min(a,b) ≤ a^{1/n} b^{1-1/n}`. -/
theorem deg_pair_sum (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (hn : 3 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ X t : ℝ, 2 ≤ X → 1 ≤ t →
      (∑ᶠ p ∈ {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
          LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ X ∧ eNorm p.2 ≤ X ∧
          t * dmin 2 ({p.1} : Set (Fin (n + 1) → ℤ)) ≤ eNorm p.1},
        1 / (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) * eNorm p.1 ^ (d - 1) *
          eNorm p.2 ^ (d - 1)))
        ≤ K * X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3 / t := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := FM3.ell_two_count_free n (by omega)
  obtain ⟨K₂, hK₂pos, hK₂⟩ := ellXY_two_pub n (by omega)
  have harith := deg_pair_sum_arith d n K₁ K₂ hK₁pos hK₂pos hd hdn hn
  obtain ⟨K₃, hK₃pos, hK₃⟩ := harith
  refine ⟨K₃, hK₃pos, ?_⟩
  intro X t hX ht
  have hX1 : 1 ≤ X := by linarith
  have ht0 : 0 < t := by linarith
  -- dyadic total index
  set K : ℕ := Nat.floor (Real.logb 2 X) with hKdef
  have hKX : shIdx X = K := by rw [shIdx, hKdef]
  have h2K : (2 : ℝ) ^ K ≤ X := by
    have h0 : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX1
    have hfl : ((K : ℕ) : ℝ) ≤ Real.logb 2 X := by rw [hKdef]; exact Nat.floor_le h0
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hfl
    rw [Real.rpow_natCast, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)] at h
    exact h
  have hfin : (PSet n X t).Finite :=
    ((MDBasic.finite_eNorm_le (ι := Fin (n + 1)) X).prod
      (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) X)).subset
      (fun p hp => ⟨hp.2.1, hp.2.2.1⟩)
  change (∑ᶠ p ∈ PSet n X t, PW d n p) ≤
    K₃ * X ^ (2 * ((n : ℝ) + 1 - (d : ℝ)) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3 / t
  rw [finsum_mem_eq_finite_toFinset_sum (PW d n) hfin]
  have hmap : ∀ p ∈ hfin.toFinset, shP n p ∈ triBox K := by
    intro p hp
    have hpS : p ∈ PSet n X t := by rwa [Set.Finite.mem_toFinset] at hp
    obtain ⟨hli, h1X, h2X, hcon⟩ := hpS
    have hx0 : p.1 ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
    have hy0 : p.2 ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
    have hxx : 0 < eNorm p.1 := lt_of_lt_of_le zero_lt_one (DegSq.one_le_eNorm hx0)
    have hyy : 0 < eNorm p.2 := lt_of_lt_of_le zero_lt_one (DegSq.one_le_eNorm hy0)
    have hd1 : 1 ≤ dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) :=
      Sig2.one_le_dmin_two_pair _ _ hli
    have hk1 : shIdx (eNorm p.1) ≤ K := by
      have h := shIdx_mono hxx h1X
      rwa [hKX] at h
    have hk2 : shIdx (eNorm p.2) ≤ K := by
      have h := shIdx_mono hyy h2X
      rwa [hKX] at h
    have hk3 : shIdx (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)))
        ≤ shIdx (eNorm p.1) + shIdx (eNorm p.2) + 2 := by
      have hdd : dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) ≤ eNorm p.1 * eNorm p.2 :=
        dmin_pair_le_mul n p.1 p.2 hli
      have hxlt : eNorm p.1 < (2 : ℝ) ^ (shIdx (eNorm p.1) + 1) := lt_two_pow_shIdx _ hxx
      have hylt : eNorm p.2 < (2 : ℝ) ^ (shIdx (eNorm p.2) + 1) := lt_two_pow_shIdx _ hyy
      have h2 : (2 : ℝ) ^ (shIdx (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))))
          < (2 : ℝ) ^ (shIdx (eNorm p.1) + shIdx (eNorm p.2) + 2) := by
        calc (2 : ℝ) ^ (shIdx (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))))
            ≤ dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)) := two_pow_shIdx_le _ hd1
          _ ≤ eNorm p.1 * eNorm p.2 := hdd
          _ < (2 : ℝ) ^ (shIdx (eNorm p.1) + 1) * (2 : ℝ) ^ (shIdx (eNorm p.2) + 1) :=
              mul_lt_mul hxlt (le_of_lt hylt) (by positivity) (by positivity)
          _ = (2 : ℝ) ^ (shIdx (eNorm p.1) + shIdx (eNorm p.2) + 2) := by
              rw [← pow_add]; congr 1; ring
      have h2n : (2 : ℕ) ^ (shIdx (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))))
          < (2 : ℕ) ^ (shIdx (eNorm p.1) + shIdx (eNorm p.2) + 2) := by
        exact_mod_cast h2
      have h3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2n
      omega
    change (shIdx (eNorm p.1), shIdx (eNorm p.2),
      shIdx (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ)))) ∈ triBox K
    rw [mem_triBox]
    refine ⟨hk1, hk2, ?_, hk3⟩
    show shIdx (dmin 2 ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ≤ 2 * K + 2
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap (PW d n)]
  have hshell : ∀ k ∈ triBox K,
      (∑ p ∈ hfin.toFinset.filter (fun p => shP n p = k), PW d n p)
        ≤ min (K₁ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * (((2 : ℝ) ^ (k.1 + 1)) / t) ^ n *
              Real.log (2 * (((2 : ℝ) ^ (k.1 + 1)) / t) + 1) *
              ((5 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (k.2.1 + 1)) ^ (n + 1)))
            (K₂ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * ((2 : ℝ) ^ (k.2.1 + 1)) ^ 2 *
              ((2 : ℝ) ^ (k.2.2 + 1)) ^ (n - 1)) *
          (1 / ((2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) *
            (2 : ℝ) ^ k.2.2)) := by
    intro k _
    have hcard : ((hfin.toFinset.filter (fun p => shP n p = k)).card : ℝ)
        ≤ min (K₁ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * (((2 : ℝ) ^ (k.1 + 1)) / t) ^ n *
              Real.log (2 * (((2 : ℝ) ^ (k.1 + 1)) / t) + 1) *
              ((5 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (k.2.1 + 1)) ^ (n + 1)))
            (K₂ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * ((2 : ℝ) ^ (k.2.1 + 1)) ^ 2 *
              ((2 : ℝ) ^ (k.2.2 + 1)) ^ (n - 1)) := by
      have hbridge : (hfin.toFinset.filter (fun p => shP n p = k)).card
          = (PSet n X t ∩ {p | shP n p = k}).ncard := by
        have hfin' : (PSet n X t ∩ {p | shP n p = k}).Finite :=
          hfin.subset Set.inter_subset_left
        rw [Set.ncard_eq_toFinset_card _ hfin']
        congr 1
        ext p
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff,
          Set.mem_setOf_eq]
      rw [hbridge]
      exact shell_card_le d n K₁ K₂ hK₁pos hK₂pos (by omega) hK₁ hK₂ hX ht k
    calc (∑ p ∈ hfin.toFinset.filter (fun p => shP n p = k), PW d n p)
        ≤ ∑ p ∈ hfin.toFinset.filter (fun p => shP n p = k),
            1 / ((2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) *
              (2 : ℝ) ^ k.2.2) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
          have hpS : p ∈ PSet n X t := by rwa [Set.Finite.mem_toFinset] at hp1
          exact PW_le_shell d n hpS k hp2
      _ = ((hfin.toFinset.filter (fun p => shP n p = k)).card : ℝ) *
            (1 / ((2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) *
              (2 : ℝ) ^ k.2.2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ min (K₁ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * (((2 : ℝ) ^ (k.1 + 1)) / t) ^ n *
              Real.log (2 * (((2 : ℝ) ^ (k.1 + 1)) / t) + 1) *
              ((5 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (k.2.1 + 1)) ^ (n + 1)))
            (K₂ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * ((2 : ℝ) ^ (k.2.1 + 1)) ^ 2 *
              ((2 : ℝ) ^ (k.2.2 + 1)) ^ (n - 1)) *
          (1 / ((2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) *
            (2 : ℝ) ^ k.2.2)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  calc (∑ k ∈ triBox K, ∑ p ∈ hfin.toFinset.filter (fun p => shP n p = k), PW d n p)
      ≤ ∑ k ∈ triBox K,
          min (K₁ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * (((2 : ℝ) ^ (k.1 + 1)) / t) ^ n *
              Real.log (2 * (((2 : ℝ) ^ (k.1 + 1)) / t) + 1) *
              ((5 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ (k.2.1 + 1)) ^ (n + 1)))
            (K₂ * ((2 : ℝ) ^ (k.1 + 1)) ^ 2 * ((2 : ℝ) ^ (k.2.1 + 1)) ^ 2 *
              ((2 : ℝ) ^ (k.2.2 + 1)) ^ (n - 1)) *
          (1 / ((2 : ℝ) ^ (k.1 * (d - 1)) * (2 : ℝ) ^ (k.2.1 * (d - 1)) *
            (2 : ℝ) ^ k.2.2)) := Finset.sum_le_sum hshell
    _ ≤ K₃ * (1 + Real.log X) ^ (1 / (n : ℝ)) *
          X ^ (2 * ((n : ℝ) + 1 - (d : ℝ)) + 1 / (n : ℝ)) *
          (1 + Real.log X) ^ 2 / t := hK₃ X t K hX ht h2K
    _ ≤ K₃ * X ^ (2 * ((n : ℝ) + 1 - d) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 3 / t := by
        have hb : (1 : ℝ) ≤ 1 + Real.log X := by
          have := Real.log_nonneg hX1
          linarith
        have hstep : (1 + Real.log X) ^ (1 / (n : ℝ)) * (1 + Real.log X) ^ 2
            ≤ (1 + Real.log X) ^ 3 := by
          rw [show (1 + Real.log X) ^ (2 : ℕ) = (1 + Real.log X) ^ (((2 : ℕ) : ℝ)) by
                rw [Real.rpow_natCast],
              show (1 + Real.log X) ^ (3 : ℕ) = (1 + Real.log X) ^ (((3 : ℕ) : ℝ)) by
                rw [Real.rpow_natCast],
              ← Real.rpow_add (by linarith : (0 : ℝ) < 1 + Real.log X)]
          refine Real.rpow_le_rpow_of_exponent_le hb ?_
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
          have h1n : (1 : ℝ) / (n : ℝ) ≤ 1 := by
            rw [div_le_one (by linarith)]
            linarith
          linarith
        have hXnn : (0 : ℝ) ≤ X ^ (2 * ((n : ℝ) + 1 - (d : ℝ)) + 1 / (n : ℝ)) :=
          Real.rpow_nonneg (by linarith) _
        calc K₃ * (1 + Real.log X) ^ (1 / (n : ℝ)) *
              X ^ (2 * ((n : ℝ) + 1 - (d : ℝ)) + 1 / (n : ℝ)) * (1 + Real.log X) ^ 2 / t
            = K₃ * X ^ (2 * ((n : ℝ) + 1 - (d : ℝ)) + 1 / (n : ℝ)) *
                ((1 + Real.log X) ^ (1 / (n : ℝ)) * (1 + Real.log X) ^ 2) / t := by ring
          _ ≤ K₃ * X ^ (2 * ((n : ℝ) + 1 - (d : ℝ)) + 1 / (n : ℝ)) *
                (1 + Real.log X) ^ 3 / t := by
              refine div_le_div_of_nonneg_right ?_ (le_of_lt ht0)
              exact mul_le_mul_of_nonneg_left hstep (by positivity)

end Work.HP.MM2
