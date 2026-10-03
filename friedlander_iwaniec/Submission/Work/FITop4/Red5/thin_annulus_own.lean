/-
# `Submission.Work.FITop4.Red5.thin_annulus_own`

The **thin annulus** square-indicator count: for a *primitive* Gaussian integer `z` and an
annulus `X₁ < |w|² ≤ X₂` inside the box `gBox (2·Mn)`,

  `Σ_{X₁ < |w|² ≤ X₂} Z(Re w z)  ≪  (X₂ - X₁)·(X₁·|z|²)^{-1/4} + (X₂·|z|²)^{1/4}`.

The proof is assembled from
* the double counting `rz2_sum_Zint_eq_fiber_sum`,
* the per-fibre bound `rz2_fibre_card_le` (the companion coordinate `ψ = Im(wz)` is injective on a
  fibre and congruent modulo `|z|²`),
* the real-variable estimates `thin_real_sum_core` and `sqrt_delta_over_u_lemma`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FIArea2.sum_gBox_eq_sum_congruences
import Submission.Work.FITop4.Red5.thin_real_sum_core
import Submission.Work.FITop4.Red5.sqrt_delta_over_u_lemma
import Submission.Work.FIArea1.count_annulus
import Submission.Work.FIArea2.hits_card_le
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Per-fibre preliminaries (self-contained copies) -/

/-! ## 1. Double counting of the square indicator over an arbitrary `w`-set -/

/-- `Z(b) = #{c : c² = b}` turned into a sum: for any finite set `A` of Gaussian integers whose
`cForm · z`-square roots all lie in `[-K,K]`, the sum of `Z(cForm w z)` is the sum over `c` of the
fibre cardinalities.  (The `annM`-specialised form is `Zint_sum_eq_fiber_sum`.) -/
lemma rz2_sum_Zint_eq_fiber_sum (A : Finset GaussianInt) (z : GaussianInt) (K : ℕ)
    (hroot : ∀ w ∈ A, ∀ c : ℤ, c ^ 2 = Work.FIPlan.cForm w z →
      c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ)) :
    (∑ w ∈ A, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      = ∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (((A.filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℕ) : ℝ) := by
  classical
  have h1 : ∀ w ∈ A, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
      = ∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (if c ^ 2 = Work.FIPlan.cForm w z then (1 : ℝ) else 0) :=
    fun w hw => Work.FIArea2.Zint_eq_Cnt K (Work.FIPlan.cForm w z) (hroot w hw)
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_boole _ _

/-! ## 2. Integers in an interval and in one arithmetic progression -/

/-- A finite set of integers contained in the real interval `[lo,hi]` and in a single class
modulo `m` has at most `(hi-lo)/m + 1` elements. -/
lemma rz2_card_int_le_shifted_ap_interval {U : Finset ℤ} {t0 : ℤ} {m : ℕ} {lo hi : ℝ}
    (hm : 0 < m) (hlohi : lo ≤ hi) (hdiv : ∀ t ∈ U, (m : ℤ) ∣ (t - t0))
    (hint : ∀ t ∈ U, lo ≤ (t : ℝ) ∧ (t : ℝ) ≤ hi) :
    (U.card : ℝ) ≤ (hi - lo) / m + 1 := by
  have hmZ : (m : ℤ) ≠ 0 := by
    have : (0 : ℤ) < m := by exact_mod_cast hm
    omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set f : ℤ → ℤ := fun t => (t - t0) / (m : ℤ) with hf
  have hfmul : ∀ t ∈ U, f t * (m : ℤ) = t - t0 := by
    intro t ht
    rw [hf]
    exact ((Int.ediv_eq_iff_eq_mul_left hmZ (hdiv t ht)).mp rfl).symm
  have hinj : Set.InjOn f (U : Set ℤ) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    have h1 := hfmul a ha
    have h2 := hfmul b hb
    rw [hab] at h1
    linarith [h1, h2]
  have himg : (U.image f).card = U.card := Finset.card_image_of_injOn hinj
  have hcast : ∀ t ∈ U, ((f t : ℤ) : ℝ) * (m : ℝ) = (t : ℝ) - t0 := by
    intro t ht
    have := hfmul t ht
    exact_mod_cast congrArg (fun x : ℤ => (x : ℝ)) this
  have hinterval : ∀ t' ∈ U.image f,
      ((lo - t0) / m : ℝ) ≤ (t' : ℝ) ∧ (t' : ℝ) ≤ ((hi - t0) / m : ℝ) := by
    intro t' ht'
    rw [Finset.mem_image] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    have hb := hcast t ht
    have ht1 : lo ≤ (t : ℝ) := (hint t ht).1
    have ht2 : (t : ℝ) ≤ hi := (hint t ht).2
    have hft : ((f t : ℤ) : ℝ) = ((t : ℝ) - (t0 : ℝ)) / m := by
      rw [eq_div_iff (ne_of_gt hmR)]
      linarith [hb]
    rw [hft]
    constructor
    · rw [div_le_div_iff_of_pos_right hmR]; linarith
    · rw [div_le_div_iff_of_pos_right hmR]; linarith
  have hmain := Work.FIArea1.card_int_le_of_interval (U := U.image f)
    (lo := (lo - t0) / m) (hi := (hi - t0) / m)
    (by rw [div_le_div_iff_of_pos_right hmR]; linarith) hinterval
  rw [himg] at hmain
  have heq : (hi - (t0 : ℝ)) / m - (lo - (t0 : ℝ)) / m = (hi - lo) / m := by ring
  linarith [hmain, heq]

/-! ## 3. The per-fibre bound -/

/-- **Perimeter bound for a single fibre.**  On the set of `w` with `cForm w z = c²` and
`X₁ < |w|² ≤ X₂`, the companion coordinate `ψ(w) = Im(wz)` is injective and lies in one class
modulo `N = |z|²`; since `|w|²·N = ψ(w)² + c⁴`, the admissible `ψ` lie in the two intervals
`±[√(max(X₁N - c⁴,0)), √(X₂N - c⁴)]`, each contributing at most `(length)/N + 1` integers of the
class. -/
lemma rz2_fibre_card_le (z : GaussianInt) (X₁ X₂ : ℕ) (c : ℤ) (T : Finset GaussianInt)
    (hcop : IsCoprime z.re z.im) (hN : 1 ≤ Work.FIPlan.gnorm z) (hX : X₁ ≤ X₂)
    (hT : ∀ w ∈ T, (X₁ : ℝ) < (Work.FIPlan.gnorm w : ℝ) ∧
        (Work.FIPlan.gnorm w : ℝ) ≤ (X₂ : ℝ) ∧ c ^ 2 = Work.FIPlan.cForm w z) :
    (T.card : ℝ) ≤ 2 * (Real.sqrt (max ((X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ) - (c : ℝ) ^ 4) 0)
        - Real.sqrt (max ((X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ) - (c : ℝ) ^ 4) 0))
        / (Work.FIPlan.gnorm z : ℝ) + 2 := by
  classical
  have hMz : (0 : ℝ) < (Work.FIPlan.gnorm z : ℝ) := by
    have : (1 : ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hN
    linarith
  have hnz : (Work.FIPlan.gnorm z : ℤ) ≠ 0 := by
    have h : Work.FIPlan.gnorm z ≠ 0 := Nat.one_le_iff_ne_zero.mp hN
    exact_mod_cast h
  set lo : ℝ := Real.sqrt (max ((X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ) - (c : ℝ) ^ 4) 0) with hlod
  set hi : ℝ := Real.sqrt (max ((X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ) - (c : ℝ) ^ 4) 0) with hhid
  have hX' : (X₁ : ℝ) ≤ (X₂ : ℝ) := by exact_mod_cast hX
  have hlohi : lo ≤ hi := by
    rw [hlod, hhid]
    apply Real.sqrt_le_sqrt
    exact max_le_max (by nlinarith [hMz.le, hX']) le_rfl
  have key : ∀ (B : Finset ℤ) (t0 : ℤ), (∀ t ∈ B, lo ≤ (t : ℝ) ∧ (t : ℝ) ≤ hi) →
      (∀ t ∈ B, ((Work.FIPlan.gnorm z : ℕ) : ℤ) ∣ (t - t0)) →
      (B.card : ℝ) ≤ (hi - lo) / (Work.FIPlan.gnorm z : ℝ) + 1 := by
    intro B t0 hB hdv
    exact rz2_card_int_le_shifted_ap_interval (U := B) (t0 := t0) (m := Work.FIPlan.gnorm z)
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hN) hlohi hdv hB
  by_cases hne : T.Nonempty
  · obtain ⟨w₀, hw₀⟩ := hne
    set B : Finset ℤ := T.image (Work.FIArea1.psi z) with hBdef
    have hinj : Set.InjOn (Work.FIArea1.psi z) (T : Set GaussianInt) := by
      intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      refine Work.FIArea1.psi_eq_of_cForm_eq hcop hnz ?_ hab
      rw [← (hT a ha).2.2, ← (hT b hb).2.2]
    have hBcard : B.card = T.card := by rw [hBdef]; exact Finset.card_image_of_injOn hinj
    have hmem : ∀ t ∈ B, lo ≤ |(t : ℝ)| ∧ |(t : ℝ)| ≤ hi := by
      intro t ht
      rw [hBdef, Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      have hw1 : (X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ)
          < (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) :=
        mul_lt_mul_of_pos_right (hT w hw).1 hMz
      have hw2 : (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ)
          ≤ (X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ) :=
        mul_le_mul_of_nonneg_right (hT w hw).2.1 hMz.le
      have hL := Work.FIArea1.gnorm_mul_eq w z
      have hc : (Work.FIPlan.cForm w z) ^ 2 = c ^ 4 := by rw [← (hT w hw).2.2]; ring
      have hsq : ((Work.FIArea1.psi z w : ℤ) : ℝ) ^ 2
          = (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) - (c : ℝ) ^ 4 := by
        have h2 : ((Work.FIArea1.psi z w) ^ 2 + (Work.FIPlan.cForm w z) ^ 2 : ℤ)
            = (Work.FIPlan.gnorm w : ℤ) * (Work.FIPlan.gnorm z : ℤ) := hL.symm
        rw [hc] at h2
        have h3 : ((Work.FIArea1.psi z w : ℤ) : ℝ) ^ 2 + (c : ℝ) ^ 4
            = (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
          have := congrArg (fun x : ℤ => (x : ℝ)) h2
          push_cast at this
          linarith [this]
        linarith [h3]
      have hlow : max ((X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ) - (c : ℝ) ^ 4) 0
          ≤ ((Work.FIArea1.psi z w : ℤ) : ℝ) ^ 2 :=
        max_le (by rw [hsq]; linarith [hw1]) (sq_nonneg _)
      have hhigh : ((Work.FIArea1.psi z w : ℤ) : ℝ) ^ 2
          ≤ (X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ) - (c : ℝ) ^ 4 := by
        rw [hsq]; linarith [hw2]
      rw [← Real.sqrt_sq_eq_abs, hlod, hhid]
      exact ⟨Real.sqrt_le_sqrt hlow,
        Real.sqrt_le_sqrt (le_trans hhigh (le_max_left _ _))⟩
    have hdivB : ∀ t ∈ B, ((Work.FIPlan.gnorm z : ℕ) : ℤ) ∣ (t - Work.FIArea1.psi z w₀) := by
      intro t ht
      rw [hBdef, Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      exact Work.FIArea1.nz_dvd_psi_sub hcop (by rw [← (hT w hw).2.2, ← (hT w₀ hw₀).2.2])
    set Bp : Finset ℤ := B.filter (fun t => 0 ≤ t) with hBpdef
    set Bn : Finset ℤ := B.filter (fun t => t < 0) with hBndef
    have hsplit : Bp.card + Bn.card = B.card := by
      rw [hBpdef, hBndef]
      have h := Finset.card_filter_add_card_filter_not (s := B) (p := fun t : ℤ => 0 ≤ t)
      have he : (B.filter (fun t => ¬ (0 ≤ t))).card = (B.filter (fun t => t < 0)).card := by
        congr 1; ext t; simp [not_le]
      omega
    have hBp_bd : (Bp.card : ℝ) ≤ (hi - lo) / (Work.FIPlan.gnorm z : ℝ) + 1 := by
      refine key Bp (Work.FIArea1.psi z w₀) ?_ ?_
      · intro t ht
        rw [hBpdef, Finset.mem_filter] at ht
        have h := hmem t ht.1
        rwa [abs_of_nonneg (by exact_mod_cast ht.2 : (0:ℝ) ≤ (t:ℝ))] at h
      · intro t ht
        rw [hBpdef, Finset.mem_filter] at ht
        exact hdivB t ht.1
    have hBn_bd : (Bn.card : ℝ) ≤ (hi - lo) / (Work.FIPlan.gnorm z : ℝ) + 1 := by
      have hneg : Set.InjOn (fun t : ℤ => -t) (Bn : Set ℤ) := by
        intro a _ b _ h; simpa using h
      have hcard : (Bn.image (fun t => -t)).card = Bn.card := Finset.card_image_of_injOn hneg
      have hkey := key (Bn.image (fun t => -t)) (-(Work.FIArea1.psi z w₀)) ?_ ?_
      · rwa [hcard] at hkey
      · intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        rw [hBndef, Finset.mem_filter] at hs
        have h := hmem s hs.1
        rw [abs_of_neg (by exact_mod_cast hs.2 : (s:ℝ) < 0)] at h
        simpa using h
      · intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        rw [hBndef, Finset.mem_filter] at hs
        have h := hdivB s hs.1
        have he : ((-s : ℤ) - (-(Work.FIArea1.psi z w₀))) = -(s - Work.FIArea1.psi z w₀) := by ring
        rw [he]
        obtain ⟨k, hk⟩ := h
        exact ⟨-k, by rw [hk]; ring⟩
    rw [← hBcard, ← hsplit]
    push_cast
    rw [show (2:ℝ) * (hi - lo) / (Work.FIPlan.gnorm z : ℝ)
          = 2 * ((hi - lo) / (Work.FIPlan.gnorm z : ℝ)) by ring]
    linarith [hBp_bd, hBn_bd]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hdiv0 : 0 ≤ (hi - lo) / (Work.FIPlan.gnorm z : ℝ) :=
      div_nonneg (by linarith [hlohi]) hMz.le
    rw [show (2:ℝ) * (hi - lo) / (Work.FIPlan.gnorm z : ℝ)
          = 2 * ((hi - lo) / (Work.FIPlan.gnorm z : ℝ)) by ring]
    linarith

/-- The thin-annulus count, given the two real-variable estimates. -/
theorem thin_annulus_Zint_count_aux (Cs : ℝ) (hCs : 0 < Cs)
    (hs : ∀ (A B : ℝ) (K : ℕ), (1 : ℝ) ≤ A → A ≤ B → B ≤ 2 * A →
      B ^ ((1 : ℝ) / 4) ≤ (K : ℝ) →
      (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (Real.sqrt (max (B - (c : ℝ) ^ 4) 0) - Real.sqrt (max (A - (c : ℝ) ^ 4) 0)))
        ≤ Cs * ((B - A) * A ^ (-(1 : ℝ) / 4) + Real.sqrt (B - A))) :
    ∀ (z : GaussianInt) (X₁ X₂ Mn : ℕ) (θ : ℝ),
      Work.FIPlan.IsPrimitive z → 1 ≤ Work.FIPlan.gnorm z → 1 ≤ Mn →
      Mn ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 2 * Mn → (X₂ - X₁ : ℝ) ≤ 2 * θ * Mn →
      (∑ w ∈ (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
          (fun w => X₁ < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ X₂),
          (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ (6 * Cs + 10) * ((X₂ - X₁ : ℝ) * ((X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) := by
  intro z X₁ X₂ Mn θ hprim hz1 hMn hX1 hX12 hX2 hθ
  have hprim' : IsCoprime z (star z) := hprim
  have hcop' : IsCoprime z.re z.im := Work.FIArea2.isCoprime_re_im_of_isCoprime_star hprim'
  set u : ℝ := (Work.FIPlan.gnorm z : ℝ) with hudef
  have hu1 : (1 : ℝ) ≤ u := by rw [hudef]; exact_mod_cast hz1
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu1
  have hX1R : (1 : ℝ) ≤ (X₁ : ℝ) := by exact_mod_cast (le_trans hMn hX1)
  have hX12R : (X₁ : ℝ) ≤ (X₂ : ℝ) := by exact_mod_cast hX12
  have hX2X1 : (X₂ : ℝ) ≤ 2 * (X₁ : ℝ) := by
    have h : X₂ ≤ 2 * X₁ := le_trans hX2 (Nat.mul_le_mul_left 2 hX1)
    exact_mod_cast h
  set S : Finset GaussianInt := (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
      (fun w => X₁ < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ X₂) with hSdef
  set K : ℕ := ⌈((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4)⌉₊ with hKdef
  have hKge : ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4) ≤ (K : ℝ) := by
    rw [hKdef]; exact Nat.le_ceil _
  have hX2u1 : (1 : ℝ) ≤ (X₂ : ℝ) * u := by
    have h : (1 : ℝ) ≤ (X₂ : ℝ) := by exact_mod_cast (le_trans hMn (le_trans hX1 hX12))
    nlinarith [hu1, h]
  have hK1 : 1 ≤ K := by
    have h2 : (1 : ℝ) ≤ ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hX2u1 (by norm_num)
    have h3 : (1 : ℝ) ≤ (K : ℝ) := le_trans h2 hKge
    exact_mod_cast h3
  -- ### the range of the square roots
  have hroot : ∀ w ∈ S, ∀ c : ℤ, c ^ 2 = Work.FIPlan.cForm w z →
      c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro w hw c hc
    rw [hSdef, Finset.mem_filter] at hw
    obtain ⟨-, hwlo, hwhi⟩ := hw
    have hgnw : (Work.FIPlan.gnorm w : ℝ) ≤ (X₂ : ℝ) := by exact_mod_cast hwhi
    have hcq : ((c : ℝ)) ^ 2 = (Work.FIPlan.cForm w z : ℝ) := by
      rw [← hc]; push_cast; ring
    have hlag : (Work.FIPlan.cForm w z : ℝ) ^ 2
        ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
      have h2 : ((Work.FIArea1.psi z w : ℤ) : ℝ) ^ 2 + (Work.FIPlan.cForm w z : ℝ) ^ 2
          = (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := by
        have hL := congrArg (fun x : ℤ => (x : ℝ)) (Work.FIArea1.gnorm_mul_eq w z).symm
        push_cast at hL
        exact hL
      nlinarith [h2, sq_nonneg ((Work.FIArea1.psi z w : ℤ) : ℝ)]
    have hbd : (|(c : ℝ)|) ^ 4 ≤ (X₂ : ℝ) * u := by
      have he : (|(c : ℝ)|) ^ 4 = (Work.FIPlan.cForm w z : ℝ) ^ 2 := by
        rw [show (|(c : ℝ)|) ^ 4 = ((|(c : ℝ)|) ^ 2) ^ 2 by ring, sq_abs, hcq]
      rw [he]
      calc (Work.FIPlan.cForm w z : ℝ) ^ 2
          ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := hlag
        _ ≤ (X₂ : ℝ) * u := mul_le_mul_of_nonneg_right hgnw hu0.le
    have hpow : (((|(c : ℝ)|) ^ 4 : ℝ)) ^ ((1 : ℝ) / 4) = |(c : ℝ)| := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
          show (((4:ℕ):ℝ) * ((1:ℝ)/4)) = 1 by norm_num, Real.rpow_one]
    have hle : |(c : ℝ)| ≤ ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow (z := (1 : ℝ) / 4)
        (by positivity : (0 : ℝ) ≤ (|(c : ℝ)|) ^ 4) hbd (by norm_num)
      rwa [hpow] at h
    have hcabs : |(c : ℝ)| ≤ (K : ℝ) := le_trans hle hKge
    have hzi : |c| ≤ (K : ℤ) := by exact_mod_cast hcabs
    rw [Finset.mem_Icc]
    exact abs_le.mp hzi
  -- ### the per-fibre bound
  have hfib : ∀ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (((S.filter (fun w => c ^ 2 = Work.FIPlan.cForm w z)).card : ℕ) : ℝ)
        ≤ 2 * (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
            - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0)) / u + 2 := by
    intro c _
    have hT : ∀ w ∈ S.filter (fun w => c ^ 2 = Work.FIPlan.cForm w z),
        (X₁ : ℝ) < (Work.FIPlan.gnorm w : ℝ) ∧ (Work.FIPlan.gnorm w : ℝ) ≤ (X₂ : ℝ)
          ∧ c ^ 2 = Work.FIPlan.cForm w z := by
      intro w hw
      rw [Finset.mem_filter, hSdef, Finset.mem_filter] at hw
      refine ⟨?_, ?_, hw.2⟩
      · exact_mod_cast hw.1.2.1
      · exact_mod_cast hw.1.2.2
    exact rz2_fibre_card_le z X₁ X₂ c (S.filter (fun w => c ^ 2 = Work.FIPlan.cForm w z))
      hcop' hz1 hX12 hT
  have hsum := Finset.sum_le_sum hfib
  -- ### the real-variable estimate
  have hreal : (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
          - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0)))
      ≤ Cs * (((X₂ : ℝ) - (X₁ : ℝ)) * u * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
          + Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u)) := by
    have h := hs ((X₁ : ℝ) * u) ((X₂ : ℝ) * u) K
      (by nlinarith [hX1R, hu1])
      (by nlinarith [hX12R, hu0.le])
      (by nlinarith [hX2X1, hu0.le])
      hKge
    rwa [show (X₂ : ℝ) * u - (X₁ : ℝ) * u = ((X₂ : ℝ) - (X₁ : ℝ)) * u by ring] at h
  -- ### splitting the per-fibre sum
  have hsplit : (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        (2 * (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
            - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0)) / u + 2))
      = 2 * (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
            - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0))) / u
        + 2 * (2 * (K : ℝ) + 1) := by
    rw [Finset.sum_add_distrib]
    have h1 : (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (2 * (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
              - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0)) / u))
        = 2 * (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
              - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0))) / u := by
      rw [show (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (2 * (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
                - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0)) / u))
          = (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (2 / u) * (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
                - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0)))
          from Finset.sum_congr rfl (fun c _ => by ring)]
      rw [← Finset.mul_sum]
      ring
    rw [h1]
    have hc : (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
      rw [Int.card_Icc]
      have h : (K : ℤ) + 1 - (-(K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [h, Int.toNat_natCast]
    rw [Finset.sum_const, nsmul_eq_mul, hc]
    push_cast
    ring
  -- ### the `2(2K+1)` term
  have hKb : 2 * (2 * (K : ℝ) + 1) ≤ 10 * ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4) := by
    have h1 : (K : ℝ) ≤ ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4) + 1 := by
      rw [hKdef]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have h2 : (1 : ℝ) ≤ ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hX2u1 (by norm_num)
    linarith
  -- ### the `√(Δu)/u` term
  have hsq : Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u) / u
      ≤ 2 * (((X₂ : ℝ) - (X₁ : ℝ)) * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
          + ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4)) :=
    sqrt_delta_over_u_lemma hX1R hX12R hu1 (by linarith [hX12R])
  -- ### assembly
  have hDlnn : (0 : ℝ) ≤ (X₂ : ℝ) - (X₁ : ℝ) := by linarith [hX12R]
  have hQ1nn : (0 : ℝ) ≤ ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hQ2nn : (0 : ℝ) ≤ ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hZsum : (∑ w ∈ S, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ 2 * Cs * (((X₂ : ℝ) - (X₁ : ℝ)) * u * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
            + Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u)) / u
        + 10 * ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4) := by
    rw [rz2_sum_Zint_eq_fiber_sum S z K hroot]
    refine le_trans hsum ?_
    rw [hsplit]
    have h1 : 2 * (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
            - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0))) / u
        ≤ 2 * Cs * (((X₂ : ℝ) - (X₁ : ℝ)) * u * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
            + Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u)) / u := by
      have hm := mul_le_mul_of_nonneg_right hreal (by positivity : (0 : ℝ) ≤ 2 / u)
      rw [show (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
              - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0))) * (2 / u)
          = 2 * (∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
            (Real.sqrt (max ((X₂ : ℝ) * u - (c : ℝ) ^ 4) 0)
              - Real.sqrt (max ((X₁ : ℝ) * u - (c : ℝ) ^ 4) 0))) / u by ring] at hm
      rw [show (Cs * (((X₂ : ℝ) - (X₁ : ℝ)) * u * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
            + Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u))) * (2 / u)
          = 2 * Cs * (((X₂ : ℝ) - (X₁ : ℝ)) * u * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
            + Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u)) / u by ring] at hm
      exact hm
    linarith [h1, hKb]
  have hZbound : 2 * Cs * (((X₂ : ℝ) - (X₁ : ℝ)) * u * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
          + Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u)) / u
        + 10 * ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4)
      ≤ (6 * Cs + 10) * (((X₂ : ℝ) - (X₁ : ℝ)) * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
          + ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4)) := by
    have hAQ : (((X₂ : ℝ) - (X₁ : ℝ)) * u * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)) / u
        = ((X₂ : ℝ) - (X₁ : ℝ)) * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4) := by field_simp
    have hstep : 2 * Cs * (((X₂ : ℝ) - (X₁ : ℝ)) * u * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
          + Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u)) / u
        = 2 * Cs * (((X₂ : ℝ) - (X₁ : ℝ)) * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
          + Real.sqrt (((X₂ : ℝ) - (X₁ : ℝ)) * u) / u) := by
      rw [mul_div_assoc, add_div, hAQ]
    rw [hstep]
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 2 * Cs)
    have hprod : (0 : ℝ) ≤ ((X₂ : ℝ) - (X₁ : ℝ)) * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4) :=
      mul_nonneg hDlnn hQ1nn
    nlinarith [hmul, hprod, hQ2nn, hCs]
  have hfin : (∑ w ∈ S, (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      ≤ (6 * Cs + 10) * (((X₂ : ℝ) - (X₁ : ℝ)) * ((X₁ : ℝ) * u) ^ (-(1 : ℝ) / 4)
          + ((X₂ : ℝ) * u) ^ ((1 : ℝ) / 4)) := le_trans hZsum hZbound
  exact hfin

/-- **The thin-annulus count.** -/
theorem thin_annulus_Zint_count_own :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : GaussianInt) (X₁ X₂ Mn : ℕ) (θ : ℝ),
      Work.FIPlan.IsPrimitive z → 1 ≤ Work.FIPlan.gnorm z → 1 ≤ Mn →
      Mn ≤ X₁ → X₁ ≤ X₂ → X₂ ≤ 2 * Mn → (X₂ - X₁ : ℝ) ≤ 2 * θ * Mn →
      (∑ w ∈ (Work.FIPlan.gBox (2 * (Mn : ℤ))).filter
          (fun w => X₁ < Work.FIPlan.gnorm w ∧ Work.FIPlan.gnorm w ≤ X₂),
          (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        ≤ C * ((X₂ - X₁ : ℝ) * ((X₁ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ (-(1 : ℝ) / 4)
            + ((X₂ : ℝ) * (Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4)) := by
  obtain ⟨Cs, hCs, hs⟩ := thin_real_sum_core
  exact ⟨6 * Cs + 10, by positivity, thin_annulus_Zint_count_aux Cs hCs hs⟩

end

end Work.FITop4.Red5
