import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detL_inf_latOrth
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.MDEstimates.detL_one_le
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.prim_box_lower
import Submission.Work.HP.box_card

/-!
# `Work.HP.EE_lower2`

The lower half of Browning--Le Boudec--Sawin, Lemma E: `B² ≪ E_{d,n}(B)`.

`E_{d,n}(B) = Σ_{(x,y) ∈ Ω_{d,n}(B)} 1/det Γ_{x,y}` is a sum of positive terms over the pairs
of primitive vectors `x ≠ ±y` of norm at most `T = B^{1/(n+1-d)}`.  Two facts give the bound:

* each term is at least `1/(‖ν(x)‖‖ν(y)‖) ≫ T^{-2d}`, since the covolume of
  `Γ_{x,y}` is at most `‖ν(x)‖‖ν(y)‖` (`detL_Gam_le_norm`) and `‖ν(z)‖ ≍ ‖z‖^d`;
* `Ω_{d,n}(B)` is `Ξ × Ξ` with the diagonal and anti-diagonal removed
  (`Omega_ncard_lower`), and `#Ξ ≫ T^{n+1}` (`prim_ball_lower`).

Hence `E_{d,n}(B) ≫ T^{2n+2-2d} · T^{-2d} = T^{2(n+1-d)} = B²`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP

/-! ## 1. Two elementary norm bounds -/

lemma eNorm_nonneg' {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v := Real.sqrt_nonneg _

/-- `wedgeNorm v w ≤ ‖v‖‖w‖`: the covolume of `ℤv ⊕ ℤw` is at most the product of the norms. -/
lemma wedgeNorm_le_mul {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    wedgeNorm v w ≤ eNorm v * eNorm w := by
  have hv : 0 ≤ eNorm v := eNorm_nonneg' v
  have hw : 0 ≤ eNorm w := eNorm_nonneg' w
  have h1 : eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2
      ≤ (eNorm v * eNorm w) ^ 2 := by
    rw [mul_pow]; linarith [sq_nonneg (dotR (toR v) (toR w))]
  calc wedgeNorm v w
      = Real.sqrt (eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2) := rfl
    _ ≤ Real.sqrt ((eNorm v * eNorm w) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm v * eNorm w := Real.sqrt_sq (mul_nonneg hv hw)

/-- The covolume of `Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)}` is at most `‖ν(x)‖‖ν(y)‖` for
primitive `x ≠ ±y`.  (The paper's determinant formula gives the sharper
`‖ν(x)‖‖ν(y)‖/𝒢(x,y)`; only the upper bound is needed here.) -/
lemma detL_Gam_le_norm (d n : ℕ) (hd : 2 ≤ d) (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (h1 : x ≠ y) (h2 : x ≠ -y) :
    detL (Gam d n x y) ≤ eNorm (veronese d n x) * eNorm (veronese d n y) := by
  have hν : LinearIndependent ℤ ![veronese d n x, veronese d n y] :=
    Sig2.nu_indep d n hd x y hx hy h1 h2
  have hkey := Lat.detL_inf_latOrth (veronese d n x) (veronese d n y) hν
  rw [show Gam d n x y = latOrth (veronese d n x) ⊓ latOrth (veronese d n y) from rfl, hkey]
  have hwnn : 0 ≤ wedgeNorm (veronese d n x) (veronese d n y) := Real.sqrt_nonneg _
  rcases eq_or_ne (gcdMinors2 (veronese d n x) (veronese d n y)) 0 with hg | hg
  · rw [hg, Int.cast_zero, abs_zero, div_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · have hg1 : (1 : ℝ) ≤ |((gcdMinors2 (veronese d n x) (veronese d n y) : ℤ) : ℝ)| := by
      have h := Int.one_le_abs hg
      exact_mod_cast h
    refine le_trans ?_ (wedgeNorm_le_mul _ _)
    rw [div_le_iff₀ (lt_of_lt_of_le zero_lt_one hg1)]
    exact le_mul_of_one_le_right hwnn hg1

/-! ## 2. The arithmetic of the box count -/

private lemma inv_pow4_step (g : ℕ) (hg : 3 ≤ g) :
    (1 : ℝ) / (g : ℝ) ^ 4
      ≤ (1 / 3) * (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3) := by
  have hg1 : 1 ≤ g := by omega
  set x : ℝ := ((g - 1 : ℕ) : ℝ) with hxdef
  have hx : 0 < x := by
    rw [hxdef]; exact_mod_cast (by omega : 0 < g - 1)
  have hg' : (g : ℝ) = x + 1 := by
    rw [hxdef]
    have h : g - 1 + 1 = g := Nat.sub_add_cancel hg1
    rw [← h]; push_cast; ring
  rw [hg']
  have hp1 : (0 : ℝ) < (x + 1) ^ 4 := by positivity
  rw [div_le_iff₀ hp1]
  have hval : (1 / 3 : ℝ) * (1 / x ^ 3 - 1 / (x + 1) ^ 3) * (x + 1) ^ 4
      = ((x + 1) ^ 3 - x ^ 3) * (x + 1) / (3 * x ^ 3) := by
    field_simp
    first | ring | ring_nf | skip
  rw [hval]
  have hden : (0 : ℝ) < 3 * x ^ 3 := by positivity
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg x, hx]

private lemma sum_Icc_sub_eq (f : ℕ → ℝ) {a B : ℕ} (ha : 1 ≤ a) (haB : a ≤ B) :
    ∑ g ∈ Finset.Icc a B, (f (g - 1) - f g) = f (a - 1) - f B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le haB
  induction k with
  | zero => simp
  | succ k ih =>
    have haB' : a ≤ a + k := by omega
    rw [Nat.add_succ, Finset.sum_Icc_succ_top (by omega)]
    rw [ih haB']
    have h1 : (a + k + 1 - 1 : ℕ) = a + k := by omega
    rw [h1]
    ring

private lemma sum_inv_pow4_le (H : ℕ) :
    ∑ g ∈ Finset.Icc 2 H, (1 : ℝ) / (g : ℝ) ^ 4 ≤ 5 / 48 := by
  rcases lt_or_ge H 2 with hH | hH
  · have hempty : Finset.Icc 2 H = ∅ := by rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty]; norm_num
  · rcases lt_or_ge H 3 with hH3 | hH3
    · have h2 : H = 2 := by omega
      subst h2
      rw [Finset.Icc_self, Finset.sum_singleton]
      norm_num
    · have hsplit : Finset.Icc 2 H = insert 2 (Finset.Icc 3 H) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have htele : ∑ g ∈ Finset.Icc 3 H,
          (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3)
          = 1 / (2 : ℝ) ^ 3 - 1 / (H : ℝ) ^ 3 := by
        have h := sum_Icc_sub_eq (fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 3) (a := 3) (B := H)
          (by norm_num) hH3
        simpa using h
      have hle : ∑ g ∈ Finset.Icc 3 H, (1 : ℝ) / (g : ℝ) ^ 4 ≤ 1 / 24 := by
        calc ∑ g ∈ Finset.Icc 3 H, (1 : ℝ) / (g : ℝ) ^ 4
            ≤ ∑ g ∈ Finset.Icc 3 H,
                (1 / 3) * (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3) :=
              Finset.sum_le_sum (fun g hg => inv_pow4_step g (Finset.mem_Icc.mp hg).1)
          _ = (1 / 3) * ∑ g ∈ Finset.Icc 3 H,
                (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3) := by rw [Finset.mul_sum]
          _ = (1 / 3) * (1 / (2 : ℝ) ^ 3 - 1 / (H : ℝ) ^ 3) := by rw [htele]
          _ ≤ 1 / 24 := by
              have hH0 : (0 : ℝ) < (H : ℝ) ^ 3 := by
                have : 0 < H := by omega
                positivity
              have hpos : (0 : ℝ) < 1 / (H : ℝ) ^ 3 := one_div_pos.mpr hH0
              linarith
      rw [hsplit, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
      have h2 : (1 : ℝ) / (((2 : ℕ) : ℝ)) ^ 4 = 1 / 16 := by norm_num
      rw [h2]
      linarith

private lemma sum_inv_pow_le (k H : ℕ) (hk : 4 ≤ k) :
    ∑ g ∈ Finset.Icc 2 H, (1 : ℝ) / (g : ℝ) ^ k ≤ 5 / (3 * (2 : ℝ) ^ k) := by
  have hmain : ∑ g ∈ Finset.Icc 2 H, (1 : ℝ) / (g : ℝ) ^ k
      ≤ (1 / 2 : ℝ) ^ (k - 4) * (5 / 48) := by
    have hterm : ∀ g ∈ Finset.Icc 2 H,
        (1 : ℝ) / (g : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (k - 4) * (1 / (g : ℝ) ^ 4) := by
      intro g hg
      have hg2 : 2 ≤ g := (Finset.mem_Icc.mp hg).1
      have h2g : (2 : ℝ) ^ (k - 4) ≤ (g : ℝ) ^ (k - 4) := by
        apply pow_le_pow_left₀ (by norm_num)
        exact_mod_cast hg2
      have hgk : (g : ℝ) ^ k = (g : ℝ) ^ 4 * (g : ℝ) ^ (k - 4) := by
        rw [← pow_add]; congr 1; omega
      have hkey : (1 : ℝ) / (g : ℝ) ^ k
          ≤ (1 : ℝ) / ((g : ℝ) ^ 4 * (2 : ℝ) ^ (k - 4)) := by
        rw [hgk]
        exact one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left h2g (by positivity))
      have heq : (1 : ℝ) / ((g : ℝ) ^ 4 * (2 : ℝ) ^ (k - 4))
          = (1 / 2 : ℝ) ^ (k - 4) * (1 / (g : ℝ) ^ 4) := by
        rw [show ((1 : ℝ) / 2) ^ (k - 4) = ((2 : ℝ) ^ (k - 4))⁻¹ by rw [one_div, inv_pow],
          one_div, one_div, mul_inv]
        ring
      rw [← heq]
      exact hkey
    calc ∑ g ∈ Finset.Icc 2 H, (1 : ℝ) / (g : ℝ) ^ k
        ≤ ∑ g ∈ Finset.Icc 2 H, (1 / 2 : ℝ) ^ (k - 4) * (1 / (g : ℝ) ^ 4) :=
          Finset.sum_le_sum hterm
      _ = (1 / 2 : ℝ) ^ (k - 4) * ∑ g ∈ Finset.Icc 2 H, (1 / (g : ℝ) ^ 4) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ (k - 4) * (5 / 48) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_pow4_le H)
          positivity
  have hconst : (1 / 2 : ℝ) ^ (k - 4) * (5 / 48) = 5 / (3 * (2 : ℝ) ^ k) := by
    rw [show ((1 : ℝ) / 2) ^ (k - 4) = ((2 : ℝ) ^ (k - 4))⁻¹ by rw [one_div, inv_pow]]
    have hk4 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 4) * 16 := by
      have h : k = (k - 4) + 4 := by omega
      rw [h, pow_add]; norm_num
    rw [hk4]
    field_simp
    ring
  linarith [hmain]

/-- The `g`-sum of `(2⌊M/g⌋+1)^k` is at most `(135/256)(2M+1)^k` for `k ≥ 4`. -/
private lemma box_prim_arith (k M : ℕ) (hk : 4 ≤ k) :
    ∑ g ∈ Finset.Icc 2 M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      ≤ (135 / 256) * (2 * (M : ℝ) + 1) ^ k := by
  rcases lt_or_ge M 2 with hM | hM
  · have hempty : Finset.Icc 2 M = ∅ := by rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty]
    positivity
  · have hterm : ∀ g ∈ Finset.Icc 2 M,
        (2 * ((M / g : ℕ) : ℝ) + 1) ^ k ≤ ((3 / 2) * (2 * (M : ℝ) + 1) / g) ^ k := by
      intro g hg
      obtain ⟨hg2, hgM⟩ := Finset.mem_Icc.mp hg
      have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
      have h1 : ((M / g : ℕ) : ℝ) ≤ (M : ℝ) / g := Nat.cast_div_le
      have h3 : 2 * ((M / g : ℕ) : ℝ) + 1 ≤ (3 / 2) * (2 * (M : ℝ) + 1) / g := by
        rw [le_div_iff₀ hg0]
        have hgM' : (g : ℝ) ≤ (M : ℝ) := by exact_mod_cast hgM
        have step1 : (2 * ((M / g : ℕ) : ℝ) + 1) * g ≤ (2 * ((M : ℝ) / g) + 1) * g :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hg0)
        have step2 : (2 * ((M : ℝ) / g) + 1) * g = 2 * (M : ℝ) + g := by
          field_simp
        rw [step2] at step1
        linarith
      exact pow_le_pow_left₀ (by positivity) h3 k
    calc ∑ g ∈ Finset.Icc 2 M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
        ≤ ∑ g ∈ Finset.Icc 2 M, ((3 / 2) * (2 * (M : ℝ) + 1) / g) ^ k :=
          Finset.sum_le_sum hterm
      _ = ((3 / 2) * (2 * (M : ℝ) + 1)) ^ k
            * ∑ g ∈ Finset.Icc 2 M, (1 : ℝ) / (g : ℝ) ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun g hg => ?_)
          rw [div_pow, div_eq_mul_inv, one_div]
      _ ≤ ((3 / 2) * (2 * (M : ℝ) + 1)) ^ k * (5 / (3 * (2 : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left (sum_inv_pow_le k M hk) (by positivity)
      _ = ((3 / 2) ^ k * (5 / (3 * (2 : ℝ) ^ k))) * (2 * (M : ℝ) + 1) ^ k := by
          rw [mul_pow]; ring
      _ ≤ (135 / 256) * (2 * (M : ℝ) + 1) ^ k := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hfac : (3 / 2 : ℝ) ^ k * (5 / (3 * (2 : ℝ) ^ k)) = (5 / 3) * (3 / 4) ^ k := by
            rw [div_pow, div_pow]
            have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
            rw [h4]
            field_simp
            ring
          rw [hfac]
          calc (5 / 3) * (3 / 4 : ℝ) ^ k ≤ (5 / 3) * (3 / 4) ^ 4 := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
            _ = 135 / 256 := by norm_num

/-! ## 3. Counting primitive vectors in a ball -/

/-- A positive proportion of the primitive vectors of `ℤ^{n+1}` have norm at most `T`:
`#{x primitive : ‖x‖ ≤ T} ≫ T^{n+1}` for `T` large. -/
private theorem prim_ball_lower (n : ℕ) (hn : 3 ≤ n) :
    ∃ c T₀ : ℝ, 0 < c ∧ 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      c * T ^ (n + 1) ≤
        ((({x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ T}).ncard : ℕ) : ℝ) := by
  classical
  set k : ℕ := n + 1 with hkdef
  have hk4 : 4 ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  refine ⟨1 / (4 * (2 * (k : ℝ)) ^ k), 8 * (k : ℝ), by positivity, by linarith, ?_⟩
  intro T hT
  set M : ℕ := ⌊T / (k : ℝ)⌋₊ with hMdef
  have hTpos : (0 : ℝ) < T := by linarith
  have hMle : (M : ℝ) ≤ T / (k : ℝ) := Nat.floor_le (by positivity)
  have hMgt : T / (k : ℝ) - 1 < (M : ℝ) := by
    have := Nat.lt_floor_add_one (T / (k : ℝ))
    linarith
  have h2k_le : 2 * (k : ℝ) ≤ T := by linarith
  have hMg : T / (2 * (k : ℝ)) ≤ (M : ℝ) := by
    have h2 : (2 : ℝ) ≤ T / (k : ℝ) := by
      rw [le_div_iff₀ hkpos]; linarith
    have h3 : T / (2 * (k : ℝ)) ≤ T / (k : ℝ) - 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ))]
      have hid : (T / (k : ℝ) - 1) * (2 * (k : ℝ)) = 2 * T - 2 * (k : ℝ) := by
        field_simp
      rw [hid]; linarith
    linarith
  have hM1 : 1 ≤ M := by
    have h1 : (1 : ℝ) ≤ (M : ℝ) := by
      have h2 : (1 : ℝ) ≤ T / (2 * (k : ℝ)) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ))]; linarith
      linarith
    exact_mod_cast h1
  set Bx : Finset (Fin (n + 1) → ℤ) :=
    Fintype.piFinset (fun _ : Fin (n + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ)) with hBxdef
  have hbox : ∀ x ∈ Bx, eNorm x ≤ T := by
    intro x hx
    have hcoord : ∀ i, ((x i : ℝ)) ^ 2 ≤ (M : ℝ) ^ 2 := by
      intro i
      have hi := Fintype.mem_piFinset.mp hx i
      rw [Finset.mem_Icc] at hi
      have h1 : |(x i : ℝ)| ≤ (M : ℝ) := by
        rw [abs_le]
        exact ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩
      nlinarith [abs_nonneg (x i : ℝ), sq_abs (x i : ℝ)]
    have hsum : ∑ i : Fin (n + 1), ((x i : ℝ)) ^ 2 ≤ (k : ℝ) * (M : ℝ) ^ 2 := by
      calc ∑ i : Fin (n + 1), ((x i : ℝ)) ^ 2 ≤ ∑ _i : Fin (n + 1), (M : ℝ) ^ 2 :=
            Finset.sum_le_sum (fun i _ => hcoord i)
        _ = (k : ℝ) * (M : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hkdef]
    have h1 : eNorm x ≤ Real.sqrt ((k : ℝ) * (M : ℝ) ^ 2) := Real.sqrt_le_sqrt hsum
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (k : ℝ)),
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (M : ℝ))] at h1
    have h2 : Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
      have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hk1' (by positivity : (0 : ℝ) ≤ (k : ℝ))
        simpa [pow_two, mul_comm] using this
      calc Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) ^ 2) := Real.sqrt_le_sqrt hkk
        _ = (k : ℝ) := Real.sqrt_sq (by positivity)
    have h3 : (k : ℝ) * (M : ℝ) ≤ T := by
      have h4 := mul_le_mul_of_nonneg_left hMle (le_of_lt hkpos)
      rwa [mul_div_cancel₀ _ hkpos.ne'] at h4
    nlinarith [h1, h2, Real.sqrt_nonneg (k : ℝ), (by positivity : (0 : ℝ) ≤ (M : ℝ))]
  have hfin : ({x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ T}).Finite :=
    (MDBasic.finite_eNorm_le T).subset (fun x hx => hx.2)
  have hsub : Bx.filter (fun a => Finset.univ.gcd a = 1) ⊆ hfin.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset]
    exact ⟨(Finset.mem_filter.mp hx).2, hbox x (Finset.mem_filter.mp hx).1⟩
  have hcardle : ((Bx.filter (fun a => Finset.univ.gcd a = 1)).card : ℕ)
      ≤ ({x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ T}).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact Finset.card_le_card hsub

  have hbc : ((Bx.card : ℕ) : ℝ) = (2 * (M : ℝ) + 1) ^ k := by
    have h := (box_card (ι := Fin (n + 1)) M).1
    rw [show ((Bx.card : ℕ) : ℝ)
        = ((Fintype.piFinset (fun _ : Fin (n + 1) => Finset.Icc (-(M : ℤ)) (M : ℤ))).card : ℝ)
        from rfl] at *
    rw [h, hkdef, Fintype.card_fin]
  have hpb := prim_box_lower (ι := Fin (n + 1)) M
  have hpb' : ((Bx.card : ℕ) : ℝ) - 1
      - ∑ g ∈ Finset.Icc 2 M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      ≤ (((Bx.filter (fun a => Finset.univ.gcd a = 1)).card : ℕ) : ℝ) := by
    rw [hBxdef]
    have h := hpb
    have hsum_eq : (∑ g ∈ Finset.Icc 2 M,
          (2 * ((M / g : ℕ) : ℝ) + 1) ^ Fintype.card (Fin (n + 1)))
        = ∑ g ∈ Finset.Icc 2 M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k := by
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [Fintype.card_fin, ← hkdef]
    rw [hsum_eq] at h
    exact h
  have harith := box_prim_arith k M hk4
  have hlow : (1 / 4) * (2 * (M : ℝ) + 1) ^ k
      ≤ (((Bx.filter (fun a => Finset.univ.gcd a = 1)).card : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) ≤ (57 / 256) * (2 * (M : ℝ) + 1) ^ k := by
      have h2 : (9 : ℝ) ≤ 2 * (M : ℝ) + 1 := by
        have h4 : (4 : ℝ) ≤ T / (2 * (k : ℝ)) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (k : ℝ))]
          linarith
        linarith
      have h3 : (9 : ℝ) ^ k ≤ (2 * (M : ℝ) + 1) ^ k :=
        pow_le_pow_left₀ (by norm_num) h2 k
      have h4 : (9 : ℝ) ^ 4 ≤ (9 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk4
      have h5 : (1 : ℝ) ≤ (57 / 256) * (9 : ℝ) ^ 4 := by norm_num
      calc (1 : ℝ) ≤ (57 / 256) * (9 : ℝ) ^ 4 := h5
        _ ≤ (57 / 256) * (9 : ℝ) ^ k := by
            apply mul_le_mul_of_nonneg_left h4 (by norm_num)
        _ ≤ (57 / 256) * (2 * (M : ℝ) + 1) ^ k := by
            apply mul_le_mul_of_nonneg_left h3 (by norm_num)
    linarith [hpb', harith, hbc, h1]
  have hfinal : (1 / (4 * (2 * (k : ℝ)) ^ k)) * T ^ k
      ≤ (((Bx.filter (fun a => Finset.univ.gcd a = 1)).card : ℕ) : ℝ) := by
    have h1 : T / (2 * (k : ℝ)) ≤ 2 * (M : ℝ) + 1 := by linarith [hMg]
    have h2 : (T / (2 * (k : ℝ))) ^ k ≤ (2 * (M : ℝ) + 1) ^ k :=
      pow_le_pow_left₀ (by positivity) h1 k
    have h3 : (1 / (4 * (2 * (k : ℝ)) ^ k)) * T ^ k
        = (1 / 4) * (T / (2 * (k : ℝ))) ^ k := by
      rw [div_pow]
      field_simp
    rw [h3]
    linarith [h2, hlow]
  calc (1 / (4 * (2 * (k : ℝ)) ^ k)) * T ^ (n + 1)
      = (1 / (4 * (2 * (k : ℝ)) ^ k)) * T ^ k := by rw [hkdef]
    _ ≤ (((Bx.filter (fun a => Finset.univ.gcd a = 1)).card : ℕ) : ℝ) := hfinal
    _ ≤ ((({x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ T}).ncard : ℕ) : ℝ) := by
        exact_mod_cast hcardle

/-! ## 4. `Ω` versus `Ξ` -/

private lemma natCast_sub_le (a b : ℕ) : (a : ℝ) - (b : ℝ) ≤ ((a - b : ℕ) : ℝ) := by
  rcases lt_or_ge a b with h | h
  · have h0 : a - b = 0 := Nat.sub_eq_zero_of_le (le_of_lt h)
    rw [h0, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast le_of_lt h
    linarith
  · rw [Nat.cast_sub h]

/-- `Ω_{d,n}(B)` is `Ξ × Ξ` with the diagonal and the anti-diagonal removed, hence has at
least `#Ξ² - 2 #Ξ` elements. -/
private theorem Omega_ncard_lower (d n : ℕ) (B : ℝ) :
    ((Xi d n B).ncard : ℝ) ^ 2 - 2 * ((Xi d n B).ncard : ℝ)
      ≤ ((Omega d n B).ncard : ℝ) := by
  classical
  set S : Set (Fin (n + 1) → ℤ) := Xi d n B with hS
  set D : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 = p.2} with hD
  set A : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 = -p.2} with hA
  have hSfin : S.Finite := by
    rw [hS]; exact (MDBasic.finite_sets d n 0 B fun _ => True).2.1
  have hOm : Omega d n B = (S ×ˢ S) \ (D ∪ A) := by
    rw [hS, hD, hA]
    ext p
    simp only [Omega, Set.mem_prod, Set.mem_setOf_eq, Set.mem_diff, Set.mem_union]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2⟩, fun h => h.elim (fun hh => h3 hh.2.2) (fun hh => h4 hh.2.2)⟩
    · rintro ⟨⟨h1, h2⟩, h5⟩
      exact ⟨h1, h2, fun h => h5 (Or.inl ⟨h1, h2, h⟩), fun h => h5 (Or.inr ⟨h1, h2, h⟩)⟩
  have hDsub : D ⊆ (fun x : Fin (n + 1) → ℤ => (x, x)) '' S := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨p.1, h1, Prod.ext rfl h3⟩
  have hAsub : A ⊆ (fun x : Fin (n + 1) → ℤ => (x, -x)) '' S := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨p.1, h1, Prod.ext rfl (by simp only [h3, neg_neg])⟩
  have hDle : D.ncard ≤ S.ncard :=
    le_trans (Set.ncard_le_ncard hDsub (hSfin.image _)) (Set.ncard_image_le hSfin)
  have hAle : A.ncard ≤ S.ncard :=
    le_trans (Set.ncard_le_ncard hAsub (hSfin.image _)) (Set.ncard_image_le hSfin)
  have hUn : (D ∪ A).ncard ≤ 2 * S.ncard := by
    have h1 := Set.ncard_union_le D A
    omega
  have hDfin : D.Finite := (hSfin.prod hSfin).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  have hAfin : A.Finite := (hSfin.prod hSfin).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  have hsub : D ∪ A ⊆ S ×ˢ S := by
    rintro p (hp | hp) <;> exact ⟨hp.1, hp.2.1⟩
  have hdiff : ((S ×ˢ S) \ (D ∪ A)).ncard = (S ×ˢ S).ncard - (D ∪ A).ncard :=
    Set.ncard_sdiff hsub (hDfin.union hAfin)
  have hprod : (S ×ˢ S).ncard = S.ncard * S.ncard := Set.ncard_prod
  have hstep1 : (((S ×ˢ S).ncard - (D ∪ A).ncard : ℕ) : ℝ) ≤ ((Omega d n B).ncard : ℝ) := by
    rw [hOm, hdiff]
  have hstep2 : ((S ×ˢ S).ncard : ℝ) - ((D ∪ A).ncard : ℝ)
      ≤ (((S ×ˢ S).ncard - (D ∪ A).ncard : ℕ) : ℝ) := natCast_sub_le _ _
  have hstep3 : ((S ×ˢ S).ncard : ℝ) - 2 * ((S.ncard : ℕ) : ℝ)
      ≤ ((S ×ˢ S).ncard : ℝ) - ((D ∪ A).ncard : ℝ) := by
    have : (((D ∪ A).ncard : ℕ) : ℝ) ≤ 2 * ((S.ncard : ℕ) : ℝ) := by exact_mod_cast hUn
    linarith
  have hSsq : ((S ×ˢ S).ncard : ℝ) = ((S.ncard : ℕ) : ℝ) ^ 2 := by
    rw [hprod]; push_cast; ring
  calc ((Xi d n B).ncard : ℝ) ^ 2 - 2 * ((Xi d n B).ncard : ℝ)
      = ((S.ncard : ℕ) : ℝ) ^ 2 - 2 * ((S.ncard : ℕ) : ℝ) := by rw [← hS]
    _ = ((S ×ˢ S).ncard : ℝ) - 2 * ((S.ncard : ℕ) : ℝ) := by rw [hSsq]
    _ ≤ ((S ×ˢ S).ncard : ℝ) - ((D ∪ A).ncard : ℝ) := hstep3
    _ ≤ (((S ×ˢ S).ncard - (D ∪ A).ncard : ℕ) : ℝ) := hstep2
    _ ≤ ((Omega d n B).ncard : ℝ) := hstep1

/-! ## 5. The lower bound for `E_{d,n}(B)` -/

theorem EE_lower2 (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∃ c B₀ : ℝ, 0 < c ∧ ∀ B : ℝ, B₀ ≤ B → c * B ^ 2 ≤ EE d n B := by
  have hn3 : 3 ≤ n := by
    rcases lt_or_ge n 3 with h | h
    · exfalso
      have hn2 : n = 2 := by omega
      have hd2 : d = 2 := by omega
      exact h22 (by simp [hn2, hd2])
    · exact h
  obtain ⟨c₁, T₀, hc₁pos, hT₀1, hc₁⟩ := prim_ball_lower n hn3
  obtain ⟨k₁, k₂, hk₁, hk₂, hver⟩ := eNorm_veronese_bounds d n (by omega)
  set m : ℕ := n + 1 - d with hmdef
  have hmpos : 0 < m := by omega
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by positivity
  have hexp : (1 : ℝ) / ((n : ℝ) + 1 - d) = 1 / (m : ℝ) := by
    congr 1
    rw [hmdef]
    push_cast [Nat.cast_sub (by omega : d ≤ n + 1)]
    ring
  set T₁ : ℝ := max (max 1 (4 / c₁)) T₀ with hT₁
  have hT₁pos : (0 : ℝ) < T₁ := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _))
  have hT₁1 : (1 : ℝ) ≤ T₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT₁4 : 4 / c₁ ≤ T₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hT₁T₀ : T₀ ≤ T₁ := le_max_right _ _
  refine ⟨c₁ ^ 2 / (2 * k₂ ^ 2), T₁ ^ m, by positivity, ?_⟩
  intro B hB
  have hpowm : (1 : ℝ) ≤ T₁ ^ m := one_le_pow₀ hT₁1
  have hBmax : (0 : ℝ) < B := lt_of_lt_of_le one_pos (le_trans hpowm hB)
  set T : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hT
  have hTge : T₁ ≤ T := by
    rw [hT, hexp]
    calc T₁ = (T₁ ^ m) ^ (1 / (m : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hT₁pos), mul_one_div_cancel hmR,
            Real.rpow_one]
      _ ≤ B ^ (1 / (m : ℝ)) := Real.rpow_le_rpow (by positivity) hB (by positivity)
  have hT1 : 1 ≤ T := le_trans hT₁1 hTge
  have hT4 : 4 / c₁ ≤ T := le_trans hT₁4 hTge
  have hTm : T ^ m = B := by
    rw [hT, hexp, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hBmax),
      one_div_mul_cancel hmR, Real.rpow_one]
  have hXieq : Xi d n B = {x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ T} := by
    rw [hT]; rfl
  have hP : c₁ * T ^ (n + 1) ≤ ((Xi d n B).ncard : ℝ) := by
    rw [hXieq]; exact hc₁ T (le_trans hT₁T₀ hTge)
  have hP4 : (4 : ℝ) ≤ ((Xi d n B).ncard : ℝ) := by
    have hTle : T ≤ T ^ (n + 1) := by
      calc T = T ^ 1 := (pow_one T).symm
        _ ≤ T ^ (n + 1) := pow_le_pow_right₀ hT1 (by omega)
    have h4T : (4 : ℝ) ≤ c₁ * T := by
      have h1 : c₁ * (4 / c₁) = 4 := by field_simp
      calc (4 : ℝ) = c₁ * (4 / c₁) := h1.symm
        _ ≤ c₁ * T := mul_le_mul_of_nonneg_left hT4 (le_of_lt hc₁pos)
    linarith [mul_le_mul_of_nonneg_left hTle (le_of_lt hc₁pos)]
  have hOm2 : ((Xi d n B).ncard : ℝ) ^ 2 / 2 ≤ ((Omega d n B).ncard : ℝ) := by
    have h := Omega_ncard_lower d n B
    nlinarith [h, hP4, Nat.cast_nonneg (α := ℝ) (Xi d n B).ncard]
  have hterm : ∀ p, p ∈ Omega d n B →
      1 / (k₂ ^ 2 * T ^ (2 * d)) ≤ 1 / detL (Gam d n p.1 p.2) := by
    intro p hp
    obtain ⟨hp1, hp2, hne, hne'⟩ := hp
    have hdet : detL (Gam d n p.1 p.2) ≤ k₂ ^ 2 * T ^ (2 * d) := by
      refine le_trans (detL_Gam_le_norm d n hd p.1 p.2 hp1.1 hp2.1 hne hne') ?_
      have he1 : eNorm (veronese d n p.1) ≤ k₂ * T ^ d := by
        calc eNorm (veronese d n p.1) ≤ k₂ * (eNorm p.1) ^ d := (hver p.1).2
          _ ≤ k₂ * T ^ d := mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (eNorm_nonneg' _) (by rw [hT]; exact hp1.2) d) (le_of_lt hk₂)
      have he2 : eNorm (veronese d n p.2) ≤ k₂ * T ^ d := by
        calc eNorm (veronese d n p.2) ≤ k₂ * (eNorm p.2) ^ d := (hver p.2).2
          _ ≤ k₂ * T ^ d := mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (eNorm_nonneg' _) (by rw [hT]; exact hp2.2) d) (le_of_lt hk₂)
      calc eNorm (veronese d n p.1) * eNorm (veronese d n p.2)
          ≤ (k₂ * T ^ d) * (k₂ * T ^ d) := mul_le_mul he1 he2 (eNorm_nonneg' _) (by positivity)
        _ = k₂ ^ 2 * T ^ (2 * d) := by
            have hsq : T ^ d * T ^ d = T ^ (2 * d) := by rw [← pow_add]; ring_nf
            rw [show (k₂ * T ^ d) * (k₂ * T ^ d) = k₂ ^ 2 * (T ^ d * T ^ d) by ring, hsq]
    exact one_div_le_one_div_of_le
      (lt_of_lt_of_le zero_lt_one (MDEstimates.detL_one_le _)) hdet
  have hEEge : ((Omega d n B).ncard : ℝ) * (1 / (k₂ ^ 2 * T ^ (2 * d))) ≤ EE d n B := by
    have hOmfin : (Omega d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.2
    set f : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) → ℝ :=
      fun p => 1 / detL (Gam d n p.1 p.2) with hfdef
    have hCpos : 0 < 1 / (k₂ ^ 2 * T ^ (2 * d)) := by positivity
    have hsupp : Omega d n B ⊆ Function.support f := by
      intro p hp
      rw [Function.mem_support]
      change ¬ ((1 : ℝ) / detL (Gam d n p.1 p.2) = 0)
      intro hz
      have h1 := hterm p hp
      rw [hz] at h1
      linarith
    have hf : (Omega d n B ∩ Function.support f).Finite := hOmfin.inter_of_left _
    have heq : hf.toFinset = hOmfin.toFinset :=
      Set.Finite.toFinset_inj.mpr (Set.inter_eq_left.mpr hsupp)
    have h1 : EE d n B = ∑ p ∈ hf.toFinset, f p := by
      rw [EE]
      exact finsum_mem_eq_sum f hf
    calc ((Omega d n B).ncard : ℝ) * (1 / (k₂ ^ 2 * T ^ (2 * d)))
        = ((hOmfin.toFinset.card : ℕ) : ℝ) * (1 / (k₂ ^ 2 * T ^ (2 * d))) := by
          rw [Set.ncard_eq_toFinset_card _ hOmfin]
      _ = ∑ p ∈ hOmfin.toFinset, (1 / (k₂ ^ 2 * T ^ (2 * d))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ hOmfin.toFinset, f p := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          exact hterm p ((Set.Finite.mem_toFinset hOmfin).mp hp)
      _ = EE d n B := by rw [h1, heq]
  have hA : c₁ * T ^ d * B ≤ ((Xi d n B).ncard : ℝ) := by
    have hpow : T ^ (n + 1) = T ^ d * T ^ m := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, hTm] at hP
    simpa only [mul_assoc] using hP
  have hA2 : (c₁ * T ^ d * B) ^ 2 / 2 ≤ ((Omega d n B).ncard : ℝ) := by
    have h1 : (c₁ * T ^ d * B) ^ 2 / 2 ≤ ((Xi d n B).ncard : ℝ) ^ 2 / 2 := by
      have hnn : 0 ≤ c₁ * T ^ d * B := by positivity
      have := pow_le_pow_left₀ hnn hA 2
      linarith
    linarith [hOm2]
  have hD : 0 < k₂ ^ 2 * T ^ (2 * d) := by positivity
  have hkey : c₁ ^ 2 / (2 * k₂ ^ 2) * B ^ 2 * (k₂ ^ 2 * T ^ (2 * d))
      = (c₁ * T ^ d * B) ^ 2 / 2 := by
    have hsq : (T ^ d) ^ 2 = T ^ (2 * d) := by rw [sq, ← pow_add]; ring_nf
    rw [mul_pow, mul_pow, hsq]
    field_simp
  have hEE2 : ((Omega d n B).ncard : ℝ) / (k₂ ^ 2 * T ^ (2 * d)) ≤ EE d n B := by
    have h := hEEge
    rwa [mul_one_div] at h
  calc c₁ ^ 2 / (2 * k₂ ^ 2) * B ^ 2
      = c₁ ^ 2 / (2 * k₂ ^ 2) * B ^ 2 * (k₂ ^ 2 * T ^ (2 * d)) / (k₂ ^ 2 * T ^ (2 * d)) := by
        field_simp
      _ ≤ ((Omega d n B).ncard : ℝ) / (k₂ ^ 2 * T ^ (2 * d)) := by
        rw [hkey]
        exact div_le_div_of_nonneg_right hA2 (le_of_lt hD)
      _ ≤ EE d n B := hEE2

end Work.HP
