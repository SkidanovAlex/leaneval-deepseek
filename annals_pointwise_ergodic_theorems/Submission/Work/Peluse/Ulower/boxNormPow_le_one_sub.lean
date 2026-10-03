import Mathlib
import Submission.Work.Peluse.Ulower.oneDim

/-!
# `Work.Peluse.Ulower.boxNormPow_le_one_sub`

For a function `F : ℤ → ℂ` with `‖F‖ ≤ 1` supported in the interval `symIcc L`, a direction set
`arithIcc c₀ D` (`c₀ ≠ 0`, `D ≥ 2`) and `t ≥ 1`, the `2^t`-th power of the Gowers box norm of `F`
with `t` copies of the arithmetic progression `c₀ [D]` and support box `symIcc L` is at most
`1 - min (t|c₀|D/(4·2^t (2L+1))) (2^-t)`.

The proof: the box sum is bounded by the "spread sum"
`∑_{h,h' ∈ (c₀[D])^t} (W - ∑_i |h_i - h'_i|)₊ / (W · D^{2t})` (`W = |symIcc L|`),
the spread sum dominates `D^{2(t-1)} · ∑_{a,b ∈ c₀[D]} min(|a-b|, W)`, and the latter is at least
`min (|c₀| D³/8) (W D²/2)` (`Work.Peluse.Ulower.arithIcc_pairMin_bound`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-! ## Auxiliary elementary lemmas -/

lemma abs_max_sub_min (x y : ℝ) : |x - y| = max x y - min x y := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_right h, min_eq_left h]; try ring
  · rw [abs_of_nonneg (by linarith), max_eq_left h, min_eq_right h]; try ring

lemma int_toNat_cast_max (n : ℤ) : ((n.toNat : ℕ) : ℝ) = max 0 (n : ℝ) := by
  rcases le_total 0 n with h | h
  · rw [max_eq_right (by exact_mod_cast h)]
    exact_mod_cast (Int.toNat_of_nonneg h)
  · rw [Int.toNat_of_nonpos h, max_eq_left (by exact_mod_cast h)]
    norm_num

lemma two_mul_le_two_pow : ∀ t : ℕ, 1 ≤ t → 2 * t ≤ 2 ^ t := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0; norm_num
    · have h1 : 2 * t ≤ 2 ^ t := ih (by omega)
      have h2 : (2 : ℕ) ≤ 2 ^ t := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 2 * (t + 1) = 2 * t + 2 := by ring
      rw [h3, pow_succ, mul_two]
      omega

/-! ## (1) The `t`-dimensional reduction -/

lemma piSpread_min_ge {t : ℕ} (ht : 1 ≤ t) (A : Finset ℤ) {W : ℝ} (hW : 0 ≤ W) :
    (A.card : ℝ) ^ (2 * (t - 1)) *
        (∑ a : {x : ℤ // x ∈ A}, ∑ b : {x : ℤ // x ∈ A},
          min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) W)
      ≤ ∑ h : Fin t → {x : ℤ // x ∈ A}, ∑ h' : Fin t → {x : ℤ // x ∈ A},
          min (∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|) W := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hpow : 2 * ((n + 1) - 1) = 2 * n := by omega
  rw [hpow]
  have hfin : (Fintype.card {x : ℤ // x ∈ A} : ℝ) = (A.card : ℝ) := by
    rw [Fintype.card_coe]
  have hkey : (∑ h : Fin (n + 1) → {x : ℤ // x ∈ A},
        ∑ h' : Fin (n + 1) → {x : ℤ // x ∈ A},
          min (|((h 0).1 : ℝ) - ((h' 0).1 : ℝ)|) W)
      = (Fintype.card {x : ℤ // x ∈ A} : ℝ) ^ (2 * n) *
        (∑ a : {x : ℤ // x ∈ A}, ∑ b : {x : ℤ // x ∈ A},
          min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) W) := by
    have h1 : ∀ h : Fin (n + 1) → {x : ℤ // x ∈ A},
        (∑ h' : Fin (n + 1) → {x : ℤ // x ∈ A},
            min (|((h 0).1 : ℝ) - ((h' 0).1 : ℝ)|) W)
          = (Fintype.card {x : ℤ // x ∈ A} : ℝ) ^ n *
            ∑ b : {x : ℤ // x ∈ A}, min (|((h 0).1 : ℝ) - ((b : ℤ) : ℝ)|) W := by
      intro h
      exact sum_pi_apply_zero (n := n)
        (φ := fun b : {x : ℤ // x ∈ A} => min (|((h 0).1 : ℝ) - ((b : ℤ) : ℝ)|) W)
    have h2 : (∑ h : Fin (n + 1) → {x : ℤ // x ∈ A},
          ∑ b : {x : ℤ // x ∈ A}, min (|((h 0).1 : ℝ) - ((b : ℤ) : ℝ)|) W)
        = (Fintype.card {x : ℤ // x ∈ A} : ℝ) ^ n *
          (∑ a : {x : ℤ // x ∈ A}, ∑ b : {x : ℤ // x ∈ A},
            min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) W) :=
      sum_pi_apply_zero (n := n)
        (φ := fun a : {x : ℤ // x ∈ A} =>
          ∑ b : {x : ℤ // x ∈ A}, min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) W)
    calc (∑ h : Fin (n + 1) → {x : ℤ // x ∈ A},
          ∑ h' : Fin (n + 1) → {x : ℤ // x ∈ A},
            min (|((h 0).1 : ℝ) - ((h' 0).1 : ℝ)|) W)
        = ∑ h : Fin (n + 1) → {x : ℤ // x ∈ A},
            (Fintype.card {x : ℤ // x ∈ A} : ℝ) ^ n *
              ∑ b : {x : ℤ // x ∈ A}, min (|((h 0).1 : ℝ) - ((b : ℤ) : ℝ)|) W :=
          Finset.sum_congr rfl (fun h _ => h1 h)
      _ = (Fintype.card {x : ℤ // x ∈ A} : ℝ) ^ n *
            ∑ h : Fin (n + 1) → {x : ℤ // x ∈ A},
              ∑ b : {x : ℤ // x ∈ A}, min (|((h 0).1 : ℝ) - ((b : ℤ) : ℝ)|) W := by
          rw [Finset.mul_sum]
      _ = (Fintype.card {x : ℤ // x ∈ A} : ℝ) ^ n *
            ((Fintype.card {x : ℤ // x ∈ A} : ℝ) ^ n *
              (∑ a : {x : ℤ // x ∈ A}, ∑ b : {x : ℤ // x ∈ A},
                min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) W)) := by
          rw [h2]
      _ = (Fintype.card {x : ℤ // x ∈ A} : ℝ) ^ (2 * n) *
            (∑ a : {x : ℤ // x ∈ A}, ∑ b : {x : ℤ // x ∈ A},
              min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) W) := by
          rw [← mul_assoc, ← pow_add, show n + n = 2 * n by omega]
  rw [← hfin]
  rw [← hkey]
  refine Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun h' _ => ?_))
  refine min_le_min ?_ le_rfl
  have := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin (n + 1) => |((h i).1 : ℝ) - ((h' i).1 : ℝ)|)
    (fun i _ => abs_nonneg _) (Finset.mem_univ 0)
  simpa using this

/-! ## (2) The analytic bound: the box sum is a spread sum -/

theorem boxNormPow_le_spreadSum {t : ℕ} (A S : Finset ℤ) (F : ℤ → ℂ)
    (hS : ∃ lo hi : ℤ, S = Finset.Icc lo hi)
    (hF : ∀ x : ℤ, ‖F x‖ ≤ 1) (hsupp : ∀ x : ℤ, x ∉ S → F x = 0) :
    boxNormPow t (fun _ : Fin t => A) S F
      ≤ (∑ h : Fin t → {x : ℤ // x ∈ A}, ∑ h' : Fin t → {x : ℤ // x ∈ A},
          max 0 ((S.card : ℝ) - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|))
        / ((S.card : ℝ) * (A.card : ℝ) ^ (2 * t)) := by
  classical
  obtain ⟨lo, hi, rfl⟩ := hS
  have hstar : ∀ (n : ℕ) (z : ℂ), ‖(star^[n]) z‖ = ‖z‖ := by
    intro n z
    induction n with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', norm_star, ih]
  have hstar0 : ∀ n : ℕ, (star^[n]) (0 : ℂ) = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih]; simp
  have hcube : ∀ (h h' : Fin t → ℤ) (x : ℤ),
      ‖∏ ω : Fin t → Bool, (star^[weight ω]) (F (x + cornerShift h h' ω))‖ ≤ 1 := by
    intro h h' x
    rw [norm_prod]
    refine Finset.prod_le_one₀ (fun ω _ => norm_nonneg _) (fun ω _ => ?_)
    rw [hstar]
    exact hF _
  have hcorner_lo : ∀ h h' : Fin t → ℤ, ∃ ω : Fin t → Bool,
      cornerShift h h' ω = ∑ i, min (h i) (h' i) := by
    intro h h'
    refine ⟨fun i => decide (h i ≤ h' i), ?_⟩
    simp only [cornerShift]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hle : h i ≤ h' i
    · simp [hle]
    · have hlt : h' i < h i := not_le.mp hle
      simp [hle, min_eq_right hlt.le]
  have hcorner_hi : ∀ h h' : Fin t → ℤ, ∃ ω : Fin t → Bool,
      cornerShift h h' ω = ∑ i, max (h i) (h' i) := by
    intro h h'
    refine ⟨fun i => decide (h' i ≤ h i), ?_⟩
    simp only [cornerShift]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hle : h' i ≤ h i
    · simp [hle]
    · have hlt : h i < h' i := not_le.mp hle
      simp [hle, max_eq_right hlt.le]
  have hpair : ∀ h h' : (i : Fin t) → {x : ℤ // x ∈ A},
      ‖∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
          (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
        ≤ max 0 (((Finset.Icc lo hi).card : ℝ)
            - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|) := by
    intro h h'
    set emin : ℤ := ∑ i, min ((h i).1) ((h' i).1) with hmin
    set emax : ℤ := ∑ i, max ((h i).1) ((h' i).1) with hmax
    set Wnd : Finset ℤ := Finset.Icc (lo - emin) (hi - emax) with hWnd
    have hvanish : ∀ x : ℤ, x ∉ Wnd →
        (∏ ω : Fin t → Bool, (star^[weight ω])
          (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))) = 0 := by
      intro x hx
      rw [hWnd, Finset.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · obtain ⟨ω, hω⟩ := hcorner_lo (fun i => (h i).1) (fun i => (h' i).1)
        refine Finset.prod_eq_zero (Finset.mem_univ ω) ?_
        have hz : F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω) = 0 := by
          refine hsupp _ ?_
          have hlt : x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω < lo := by
            rw [hω]; linarith
          intro hmem
          exact absurd (Finset.mem_Icc.mp hmem).1 (not_le.mpr hlt)
        rw [hz, hstar0]
      · obtain ⟨ω, hω⟩ := hcorner_hi (fun i => (h i).1) (fun i => (h' i).1)
        refine Finset.prod_eq_zero (Finset.mem_univ ω) ?_
        have hz : F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω) = 0 := by
          refine hsupp _ ?_
          have hgt : hi < x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω := by
            rw [hω]; linarith
          intro hmem
          exact absurd (Finset.mem_Icc.mp hmem).2 (not_le.mpr hgt)
        rw [hz, hstar0]
    rw [tsum_eq_sum (s := Wnd) hvanish]
    have hcard : ((Wnd.card : ℕ) : ℝ)
        ≤ max 0 (((Finset.Icc lo hi).card : ℝ)
            - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|) := by
      have hsc : (((Finset.Icc lo hi).card : ℕ) : ℝ) = max 0 ((hi + 1 - lo : ℤ) : ℝ) := by
        rw [Int.card_Icc]
        exact int_toNat_cast_max _
      have hwc : ((Wnd.card : ℕ) : ℝ)
          = max 0 ((hi - emax + 1 - (lo - emin) : ℤ) : ℝ) := by
        rw [hWnd, Int.card_Icc]
        exact int_toNat_cast_max _
      have hcm : ∀ a b : ℤ, ((max a b : ℤ) : ℝ) = max (a : ℝ) (b : ℝ) := by
        intro a b
        rcases le_total a b with h | h
        · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
        · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]
      have hcn : ∀ a b : ℤ, ((min a b : ℤ) : ℝ) = min (a : ℝ) (b : ℝ) := by
        intro a b
        rcases le_total a b with h | h
        · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
        · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
      have habs : (∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|)
          = (emax : ℝ) - (emin : ℝ) := by
        have h1 : ∀ i : Fin t, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|
            = ((max ((h i).1) ((h' i).1) : ℤ) : ℝ)
              - ((min ((h i).1) ((h' i).1) : ℤ) : ℝ) := by
          intro i
          have h2 := abs_max_sub_min (((h i).1 : ℝ)) (((h' i).1 : ℝ))
          rw [hcm, hcn]
          exact h2
        have h2 : (∑ i : Fin t, (((max ((h i).1) ((h' i).1) : ℤ)) : ℝ)) = (emax : ℝ) := by
          rw [hmax]
          exact (map_sum (Int.castAddHom ℝ) _ _).symm
        have h3 : (∑ i : Fin t, (((min ((h i).1) ((h' i).1) : ℤ)) : ℝ)) = (emin : ℝ) := by
          rw [hmin]
          exact (map_sum (Int.castAddHom ℝ) _ _).symm
        calc (∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|)
            = ∑ i, (((max ((h i).1) ((h' i).1) : ℤ)) : ℝ)
                - ∑ i, (((min ((h i).1) ((h' i).1) : ℤ)) : ℝ) := by
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl (fun i _ => h1 i)
          _ = (emax : ℝ) - (emin : ℝ) := by rw [h2, h3]
      rw [hsc, hwc, habs]
      have hcast : ((hi - emax + 1 - (lo - emin) : ℤ) : ℝ)
          = ((hi + 1 - lo : ℤ) : ℝ) - ((emax : ℝ) - (emin : ℝ)) := by
        push_cast; ring
      rw [hcast]
      exact max_le_max (le_refl 0) (sub_le_sub_right (le_max_right 0 _) _)
    calc ‖∑ x ∈ Wnd, ∏ ω : Fin t → Bool, (star^[weight ω])
          (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
        ≤ ∑ x ∈ Wnd, ‖∏ ω : Fin t → Bool, (star^[weight ω])
            (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ Wnd, (1 : ℝ) := Finset.sum_le_sum (fun x _ =>
            hcube (fun i => (h i).1) (fun i => (h' i).1) x)
      _ = ((Wnd.card : ℕ) : ℝ) := by simp
      _ ≤ max 0 (((Finset.Icc lo hi).card : ℝ)
            - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|) := hcard
  have hRbound : ‖(∑ h : (i : Fin t) → {x : ℤ // x ∈ A},
        ∑ h' : (i : Fin t) → {x : ℤ // x ∈ A},
        ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
          (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))‖
      ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ A}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ A},
          max 0 (((Finset.Icc lo hi).card : ℝ)
            - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum (fun h _ => ?_)
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum (fun h' _ => hpair h h')
  unfold boxNormPow boxSumPow
  rw [prodCubeSum_eq]
  set R : ℂ := ∑ h : (i : Fin t) → {x : ℤ // x ∈ A}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ A},
      ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω])
        (F (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)) with hR
  have hAinv : ∀ _i : Fin t, ‖(((A.card : ℂ))⁻¹)‖ = ((A.card : ℝ))⁻¹ := by
    intro i
    rw [norm_inv, Complex.norm_natCast]
  have he1 : ‖(∏ _i : Fin t, ((A.card : ℂ))⁻¹)‖ = (((A.card : ℝ))⁻¹) ^ t := by
    rw [norm_prod]
    rw [Finset.prod_congr rfl (fun i _ => hAinv i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  calc ‖((((Finset.Icc lo hi).card : ℂ))⁻¹) * (∏ _i : Fin t, ((A.card : ℂ))⁻¹)
        * (∏ _i : Fin t, ((A.card : ℂ))⁻¹) * R‖
      = ‖((((Finset.Icc lo hi).card : ℂ))⁻¹)‖ * ‖(∏ _i : Fin t, ((A.card : ℂ))⁻¹)‖
        * ‖(∏ _i : Fin t, ((A.card : ℂ))⁻¹)‖ * ‖R‖ := by rw [norm_mul, norm_mul, norm_mul]
    _ = (((Finset.Icc lo hi).card : ℝ))⁻¹ * (((A.card : ℝ))⁻¹) ^ t
        * (((A.card : ℝ))⁻¹) ^ t * ‖R‖ := by
        rw [norm_inv, Complex.norm_natCast, he1]
    _ ≤ (((Finset.Icc lo hi).card : ℝ))⁻¹ * (((A.card : ℝ))⁻¹) ^ t
        * (((A.card : ℝ))⁻¹) ^ t *
          (∑ h : (i : Fin t) → {x : ℤ // x ∈ A}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ A},
            max 0 (((Finset.Icc lo hi).card : ℝ)
              - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|)) := by
        refine mul_le_mul_of_nonneg_left hRbound ?_
        positivity
    _ = (∑ h : (i : Fin t) → {x : ℤ // x ∈ A}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ A},
            max 0 (((Finset.Icc lo hi).card : ℝ)
              - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|))
          / (((Finset.Icc lo hi).card : ℝ) * ((A.card : ℝ)) ^ (2 * t)) := by
        have hkey : ((Finset.Icc lo hi).card : ℝ)⁻¹ * ((A.card : ℝ)⁻¹) ^ t
            * ((A.card : ℝ)⁻¹) ^ t
            = (((Finset.Icc lo hi).card : ℝ) * (A.card : ℝ) ^ (2 * t))⁻¹ := by
          rw [inv_pow, mul_assoc, ← mul_inv, ← pow_add, show t + t = 2 * t by ring]
          exact (mul_inv _ _).symm
        rw [hkey, div_eq_mul_inv]
        ring

/-! ## (3) The target theorem -/

theorem boxNormPow_le_one_sub (t : ℕ) (ht : 1 ≤ t) {c₀ : ℤ} (hc₀ : c₀ ≠ 0) {D L : ℕ}
    (hD : 2 ≤ D) {F : ℤ → ℂ} (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1)
    (hFspan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → F x = 0) :
    Work.Peluse.boxNormPow t (fun _ : Fin t => Work.Peluse.arithIcc c₀ D) (Work.Peluse.symIcc L) F
      ≤ 1 - min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ)) / (4 * 2 ^ t * ((2 * L + 1 : ℕ) : ℝ)))
              (1 / (2 : ℝ) ^ t) := by
  classical
  have hcardA : (((arithIcc c₀ D).card : ℕ) : ℝ) = (D : ℝ) := by rw [card_arithIcc hc₀]
  have hcardS : (((symIcc L).card : ℕ) : ℝ) = ((2 * L + 1 : ℕ) : ℝ) := by rw [card_symIcc]
  have hWpos : (0 : ℝ) < ((symIcc L).card : ℝ) := by rw [hcardS]; positivity
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hD2pos : (0 : ℝ) < (D : ℝ) ^ 2 := by positivity
  have hD2tpos : (0 : ℝ) < (D : ℝ) ^ (2 * t) := by positivity
  have hdenpos : (0 : ℝ) < ((symIcc L).card : ℝ) * (D : ℝ) ^ (2 * t) := mul_pos hWpos hD2tpos
  have hcardF : (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D}) : ℝ)
      = (D : ℝ) ^ t := by
    rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
    push_cast
    rw [hcardA]
  -- the sums
  set sp : ℝ := ∑ h : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
        max 0 (((symIcc L).card : ℝ) - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|) with hsp
  set T : ℝ := ∑ h : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
        min (∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|) ((symIcc L).card : ℝ) with hT
  set μ : ℝ := ∑ a : {x : ℤ // x ∈ arithIcc c₀ D}, ∑ b : {x : ℤ // x ∈ arithIcc c₀ D},
      min (|((a : ℤ) : ℝ) - ((b : ℤ) : ℝ)|) ((symIcc L).card : ℝ) with hμ
  -- (A) the analytic bound
  have hanal : boxNormPow t (fun _ : Fin t => arithIcc c₀ D) (symIcc L) F
      ≤ sp / (((symIcc L).card : ℝ) * (D : ℝ) ^ (2 * t)) := by
    have h := boxNormPow_le_spreadSum (t := t) (arithIcc c₀ D) (symIcc L) F
      ⟨-(L : ℤ), (L : ℤ), rfl⟩ hF1 hFspan
    rw [hcardA] at h
    rwa [← hsp] at h
  -- (B) `sp = W * D^{2t} - T`
  have hpt : ∀ x : ℝ, max 0 (((symIcc L).card : ℝ) - x)
      = ((symIcc L).card : ℝ) - min x ((symIcc L).card : ℝ) := by
    intro x
    have h := min_eq_sub_max x ((symIcc L).card : ℝ)
    linarith
  have hconst : (∑ h : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
        ∑ _h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D}, ((symIcc L).card : ℝ))
      = ((symIcc L).card : ℝ) * (D : ℝ) ^ (2 * t) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcardF]
    rw [← mul_assoc, ← pow_add, show t + t = 2 * t by omega]
    ring
  have hspT : sp = ((symIcc L).card : ℝ) * (D : ℝ) ^ (2 * t) - T := by
    rw [hsp, hT]
    have h1 : ∀ h : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
        (∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
          max 0 (((symIcc L).card : ℝ) - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|))
        = (∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D}, ((symIcc L).card : ℝ))
          - ∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
              min (∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|) ((symIcc L).card : ℝ) := by
      intro h
      rw [show (∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
            max 0 (((symIcc L).card : ℝ) - ∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|))
          = ∑ h' : (i : Fin t) → {x : ℤ // x ∈ arithIcc c₀ D},
              (((symIcc L).card : ℝ) - min (∑ i, |((h i).1 : ℝ) - ((h' i).1 : ℝ)|)
                ((symIcc L).card : ℝ)) from Finset.sum_congr rfl (fun h' _ => hpt _),
        Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun h _ => h1 h), Finset.sum_sub_distrib, hconst]
  -- (C) `D^{2(t-1)} μ ≤ T`
  have hTμ : (D : ℝ) ^ (2 * (t - 1)) * μ ≤ T := by
    have h := piSpread_min_ge (t := t) ht (arithIcc c₀ D) (le_of_lt hWpos)
    rw [hT]
    rwa [hcardA] at h
  -- (D) `min (|c₀| D³/8) (W D²/2) ≤ μ`
  have hμ : min ((|(c₀ : ℝ)| * (D : ℝ) ^ 3) / 8)
      (((symIcc L).card : ℝ) * (D : ℝ) ^ 2 / 2) ≤ μ := by
    rw [hμ]
    exact arithIcc_pairMin_bound hc₀ hD (le_of_lt hWpos)
  -- (E) the arithmetic
  have hWD2 : (0 : ℝ) ≤ ((symIcc L).card : ℝ) * (D : ℝ) ^ 2 := by positivity
  have h2t : (2 : ℝ) * (t : ℝ) ≤ (2 : ℝ) ^ t := by
    exact_mod_cast two_mul_le_two_pow t ht
  have h2tpos : (0 : ℝ) < (2 : ℝ) ^ t := by positivity
  have h2le : (2 : ℝ) ≤ (2 : ℝ) ^ t := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
      _ ≤ (2 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) ht
  have hE1 : ((symIcc L).card : ℝ) * (D : ℝ) ^ 2 *
      min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ)) / (4 * (2 : ℝ) ^ t * ((symIcc L).card : ℝ)))
        (1 / (2 : ℝ) ^ t)
      ≤ min ((|(c₀ : ℝ)| * (D : ℝ) ^ 3) / 8) (((symIcc L).card : ℝ) * (D : ℝ) ^ 2 / 2) := by
    rw [mul_min_eq _ hWD2]
    refine min_le_min ?_ ?_
    · have h1 : (4 : ℝ) * (2 : ℝ) ^ t ≠ 0 := by positivity
      have h2 : ((symIcc L).card : ℝ) ≠ 0 := ne_of_gt hWpos
      have hbl : ((symIcc L).card : ℝ) * (D : ℝ) ^ 2
          * (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ)) / (4 * (2 : ℝ) ^ t * ((symIcc L).card : ℝ)))
          = ((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ) ^ 3) / (4 * (2 : ℝ) ^ t) := by
        field_simp
        try ring
      rw [hbl]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (2 : ℝ) ^ t)]
      have hrw : (|(c₀ : ℝ)| * (D : ℝ) ^ 3 / 8) * (4 * (2 : ℝ) ^ t)
          = |(c₀ : ℝ)| * (D : ℝ) ^ 3 * (2 : ℝ) ^ t / 2 := by ring
      rw [hrw]
      have hnn : (0 : ℝ) ≤ |(c₀ : ℝ)| * (D : ℝ) ^ 3 := mul_nonneg (abs_nonneg _) (by positivity)
      nlinarith [h2t, hnn]
    · have hbl : ((symIcc L).card : ℝ) * (D : ℝ) ^ 2 * (1 / (2 : ℝ) ^ t)
          = ((symIcc L).card : ℝ) * (D : ℝ) ^ 2 / (2 : ℝ) ^ t := by ring
      rw [hbl]
      rw [div_le_iff₀ h2tpos]
      have hrw : ((symIcc L).card : ℝ) * (D : ℝ) ^ 2 / 2 * (2 : ℝ) ^ t
          = ((symIcc L).card : ℝ) * (D : ℝ) ^ 2 * ((2 : ℝ) ^ t / 2) := by ring
      rw [hrw]
      nlinarith [hWD2, h2le]
  have hWm : ((symIcc L).card : ℝ) * (D : ℝ) ^ 2 *
      min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ)) / (4 * (2 : ℝ) ^ t * ((symIcc L).card : ℝ)))
        (1 / (2 : ℝ) ^ t)
      ≤ μ := le_trans hE1 hμ
  have hE3 : (D : ℝ) ^ (2 * (t - 1)) * (((symIcc L).card : ℝ) * (D : ℝ) ^ 2) *
      min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ)) / (4 * (2 : ℝ) ^ t * ((symIcc L).card : ℝ)))
        (1 / (2 : ℝ) ^ t)
      ≤ T := by
    refine le_trans ?_ hTμ
    calc (D : ℝ) ^ (2 * (t - 1)) * (((symIcc L).card : ℝ) * (D : ℝ) ^ 2) *
          min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ)) / (4 * (2 : ℝ) ^ t * ((symIcc L).card : ℝ)))
            (1 / (2 : ℝ) ^ t)
        = (D : ℝ) ^ (2 * (t - 1)) *
            (((symIcc L).card : ℝ) * (D : ℝ) ^ 2 *
              min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ))
                / (4 * (2 : ℝ) ^ t * ((symIcc L).card : ℝ))) (1 / (2 : ℝ) ^ t)) := by ring
      _ ≤ (D : ℝ) ^ (2 * (t - 1)) * μ := mul_le_mul_of_nonneg_left hWm (by positivity)
  -- conclusion
  have hpowid : (D : ℝ) ^ (2 * (t - 1)) * (D : ℝ) ^ 2 = (D : ℝ) ^ (2 * t) := by
    rw [← pow_add, show 2 * (t - 1) + 2 = 2 * t by omega]
  have hpowid2 : (D : ℝ) ^ (2 * (t - 1)) * (((symIcc L).card : ℝ) * (D : ℝ) ^ 2)
      = (D : ℝ) ^ (2 * t) * ((symIcc L).card : ℝ) := by
    calc (D : ℝ) ^ (2 * (t - 1)) * (((symIcc L).card : ℝ) * (D : ℝ) ^ 2)
        = ((D : ℝ) ^ (2 * (t - 1)) * (D : ℝ) ^ 2) * ((symIcc L).card : ℝ) := by ring
      _ = (D : ℝ) ^ (2 * t) * ((symIcc L).card : ℝ) := by rw [hpowid]
  have hfinal : boxNormPow t (fun _ : Fin t => arithIcc c₀ D) (symIcc L) F
      ≤ 1 - min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ))
          / (4 * (2 : ℝ) ^ t * ((symIcc L).card : ℝ))) (1 / (2 : ℝ) ^ t) := by
    refine le_trans hanal ?_
    rw [div_le_iff₀ hdenpos]
    rw [hspT]
    have hkey : (D : ℝ) ^ (2 * t) * ((symIcc L).card : ℝ) *
        min (((t : ℝ) * |(c₀ : ℝ)| * (D : ℝ)) / (4 * (2 : ℝ) ^ t * ((symIcc L).card : ℝ)))
          (1 / (2 : ℝ) ^ t)
        ≤ T := by
      have h := hE3
      rw [hpowid2] at h
      exact h
    nlinarith [hkey]
  rwa [hcardS] at hfinal

end

end Work.Peluse.Ulower
