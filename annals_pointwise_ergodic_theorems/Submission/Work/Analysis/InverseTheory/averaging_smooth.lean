import Mathlib
import Submission.Work.Analysis.InverseTheory.calc_approx
import Submission.Work.Analysis.InverseTheory.halfLine_approx

set_option autoImplicit false
set_option maxHeartbeats 16000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.Analysis.InverseTheory

/-!
# The smoothing step of Proposition `lip`

Proof of `Work.Analysis.InverseTheory.averaging_smooth`: for `ψ ∈ 𝓢(ℝ,ℂ)` with `∫ψ = 1`,
`0 < ε ≤ 1`, `1 ≤ N'`, `f` bounded by `1` and `q, x ∈ ℤ`, the averaged polynomial progression
`m ↦ (N')⁻¹ ∑_{m' ∈ [1,N']} f(x + q m')` agrees with its `ψ`-smoothed version up to
`calcConst ψ (ε^10 + (εN')^{-1})`.

The analytic input is the *pointwise* smoothing approximation of an averaging window:
on the interior `m ∈ [1,N']` the Poisson-summation/tail approximation `halfLine_approx`
(used twice, for the half-lines `y ≥ 1` and `y ≥ N'+1`) gives an error of size
`2^41 C² ε^10 + 2^40 C²(⟨ε(m-1)⟩^{-10} + ⟨ε(m-N'-1)⟩^{-10})`, whose `ℓ¹`-mass over the window is
`N' ε^10 + O(1/ε)`.  Outside the window only the rapid decay `⟨ε(m-y)⟩^{-12}` of `ψ` is used,
and the two half-lines `m ≤ 0`, `m ≥ N'+1` contribute `O(1/ε)`.  Since each `f (x + q m)` has
norm at most `1`, the whole smoothing error is bounded by the `ℓ¹`-mass of the coefficient
error.
-/

/-! ## Auxiliary estimates -/

/-- `⟨0⟩^{-n} = 1`. -/
lemma jbDecay_n_zero (n : ℕ) : jbDecay n (0 : ℝ) = 1 := by simp [jbDecay]

/-- The norm of a nonnegative real, viewed as a complex number. -/
lemma norm_real_coe {r : ℝ} (hr : 0 ≤ r) : ‖((r:ℂ))‖ = r := by
  rw [Complex.norm_real, Real.norm_of_nonneg hr]

/-- A finite sum of summable families is summable. -/
lemma summable_finset_sum {ι β M : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    (s : Finset ι) {f : ι → β → M} (h : ∀ i ∈ s, Summable (f i)) :
    Summable (fun b => ∑ i ∈ s, f i b) := by
  classical
  induction s using Finset.induction with
  | empty => exact summable_zero
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Reindex

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [T2Space M]

/-- A `ℤ`-sum of a function vanishing below `y₀` is the `ℕ`-indexed sum along `y₀ + j`
(generic version of the `ℂ`-valued statement of `halfLine_approx`). -/
lemma tsum_eq_tsum_nat_of_vanishes_below' {F : ℤ → M} {y₀ : ℤ}
    (hvan : ∀ y : ℤ, y < y₀ → F y = 0)
    (hsum : Summable fun j : ℕ => F (y₀ + (j:ℤ))) :
    (∑' y : ℤ, F y) = ∑' j : ℕ, F (y₀ + (j:ℤ)) := by
  have hshift : (∑' y : ℤ, F (y₀ + y)) = ∑' y : ℤ, F y :=
    Equiv.tsum_eq (Equiv.addLeft y₀) F
  have h1 : Summable (fun j : ℕ => F (y₀ + ((j : ℤ) + 1))) :=
    ((summable_nat_add_iff (f := fun j : ℕ => F (y₀ + (j : ℤ))) 1).mpr hsum).congr
      (fun j => by rw [show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by push_cast; ring])
  have h2 : Summable (fun j : ℕ => F (y₀ + (-((j : ℤ) + 1)))) :=
    summable_zero.congr fun j => by
      have hlt : y₀ + (-((j : ℤ) + 1)) < y₀ := by
        have h2 := Int.natCast_nonneg j
        linarith
      rw [hvan _ hlt]
  have hsplit := tsum_of_add_one_of_neg_add_one (f := fun z : ℤ => F (y₀ + z)) h1 h2
  have hz0 : F (y₀ + (0 : ℤ)) = F y₀ := by norm_num
  have hz3 : (∑' j : ℕ, F (y₀ + (-((j : ℤ) + 1)))) = 0 :=
    (tsum_congr fun j => hvan _ (by
      have h2 := Int.natCast_nonneg j
      linarith)).trans tsum_zero
  have hnat : (∑' j : ℕ, F (y₀ + (j : ℤ))) = F y₀ + ∑' j : ℕ, F (y₀ + ((j : ℤ) + 1)) := by
    have hs := hsum.sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one] at hs
    have h0 : F (y₀ + (((0 : ℕ)) : ℤ)) = F y₀ := by norm_num
    have hc : (∑' i : ℕ, F (y₀ + ((i + 1 : ℕ) : ℤ)))
        = ∑' j : ℕ, F (y₀ + ((j : ℤ) + 1)) := by
      refine tsum_congr fun i => ?_
      rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by push_cast; ring]
    rw [h0, hc] at hs
    exact hs.symm
  rw [← hshift, hsplit, hz0, hz3, hnat]
  abel

/-- A sum over the upper half-line `{y₀ ≤ y}` is the `ℕ`-indexed sum along `y₀ + j`. -/
lemma tsum_Ici_ite_eq_tsum_nat' (G : ℤ → M) (y₀ : ℤ)
    (hsum : Summable fun j : ℕ => G (y₀ + (j:ℤ))) :
    (∑' y : ℤ, (if y₀ ≤ y then G y else 0)) = ∑' j : ℕ, G (y₀ + (j:ℤ)) := by
  have hle : ∀ j : ℕ, y₀ ≤ y₀ + (j : ℤ) := fun j =>
    Int.le_add_of_nonneg_right (Int.natCast_nonneg j)
  have hvan : ∀ y : ℤ, y < y₀ → (fun y : ℤ => if y₀ ≤ y then G y else 0) y = 0 := by
    intro y hy
    change (if y₀ ≤ y then G y else 0) = 0
    rw [if_neg (by linarith)]
  have h := tsum_eq_tsum_nat_of_vanishes_below' hvan
    (hsum.congr fun j => by rw [if_pos (hle j)])
  rw [h]
  exact tsum_congr fun j => by rw [if_pos (hle j)]

/-- A sum over the lower half-line `{y ≤ z₁}` is the `ℕ`-indexed sum along `z₁ - j`. -/
lemma tsum_Iic_ite_eq_tsum_nat' (G : ℤ → M) (z₁ : ℤ)
    (hsum : Summable fun j : ℕ => G (z₁ - (j:ℤ))) :
    (∑' y : ℤ, (if y ≤ z₁ then G y else 0)) = ∑' j : ℕ, G (z₁ - (j:ℤ)) := by
  have h1 : (∑' y : ℤ, (if y ≤ z₁ then G y else 0))
      = ∑' y : ℤ, (if -z₁ ≤ y then G (-y) else 0) := by
    rw [← Equiv.tsum_eq (Equiv.neg ℤ)]
    simp only [Equiv.neg_apply]
    refine tsum_congr fun c => ?_
    by_cases h : (-z₁ : ℤ) ≤ c
    · rw [if_pos (show -c ≤ z₁ by omega), if_pos h]
    · rw [if_neg (show ¬(-c ≤ z₁) by omega), if_neg h]
  have hG : Summable fun j : ℕ => (fun y : ℤ => G (-y)) (-z₁ + (j : ℤ)) :=
    hsum.congr fun j => by congr 1; ring
  have h2 : (∑' y : ℤ, (if -z₁ ≤ y then G (-y) else 0))
      = ∑' j : ℕ, G (z₁ - (j : ℤ)) := by
    rw [tsum_Ici_ite_eq_tsum_nat' (fun y : ℤ => G (-y)) (-z₁) hG]
    refine tsum_congr fun j => ?_
    congr 1
    ring
  exact h1.trans h2

end Reindex

/-- `m ↦ ⟨ε m⟩^{-12}` is summable on `ℤ`. -/
lemma summable_jbDecay_twelve_int {ε : ℝ} (hε0 : 0 < ε) :
    Summable (fun m : ℤ => jbDecay 12 (ε * (m:ℝ))) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · have h := summable_eps_jbDecay_shift (ε := ε) hε0 0
    refine (h.mul_left (ε⁻¹)).congr (fun j => ?_)
    rw [zero_add]
    push_cast
    field_simp
  · have h := summable_eps_jbDecay_shift (ε := ε) hε0 1
    refine (h.mul_left (ε⁻¹)).congr (fun j => ?_)
    have hcast : ((↑(-(↑j + 1) : ℤ) : ℝ)) = -(1 + (j:ℝ)) := by push_cast; ring
    rw [hcast, mul_neg, jbDecay_neg]
    field_simp

/-- The shifted version: `m ↦ ⟨ε (m - y)⟩^{-12}` is summable on `ℤ`. -/
lemma summable_jbDecay_twelve_shift {ε : ℝ} (hε0 : 0 < ε) (y : ℤ) :
    Summable (fun m : ℤ => jbDecay 12 (ε * ((m:ℝ) - (y:ℝ)))) := by
  have h := summable_jbDecay_twelve_int (ε := ε) hε0
  have h2 : Summable (fun m : ℤ => jbDecay 12 (ε * (((m - y : ℤ)):ℝ))) :=
    (Equiv.summable_iff (f := fun m : ℤ => jbDecay 12 (ε * (m:ℝ))) (Equiv.subRight y)).mpr h
  refine h2.congr (fun m => ?_)
  congr 1
  push_cast
  ring

/-! ## The finite Riemann bound `∑_{m ∈ [1,N]} ⟨εm⟩^{-10} ≤ 2^60/ε` -/

/-- `k ↦ ⟨ε k⟩^{-10}` is summable on `ℕ` (comparison with `(k+1)^{-10}`). -/
lemma summable_jbDecay_ten_nat {ε : ℝ} (hε0 : 0 < ε) :
    Summable (fun k : ℕ => jbDecay 10 (ε * (k:ℝ))) := by
  set C : ℝ := max 1 (ε⁻¹^10 * 2^10) with hC
  have hbase : Summable (fun k : ℕ => (((k:ℝ)+1)⁻¹)^10) := by
    have h1 : Summable (fun k : ℕ => 1 / ((k:ℝ))^10) :=
      (Real.summable_one_div_nat_pow (p := 10)).mpr (by norm_num)
    have h2 : Summable (fun k : ℕ => 1 / (((k+1:ℕ):ℝ))^10) :=
      (summable_nat_add_iff 1).mpr h1
    refine h2.congr (fun k => ?_)
    push_cast
    rw [one_div, inv_pow]
  have hbase' : Summable (fun k : ℕ => C * (((k:ℝ)+1)⁻¹)^10) := hbase.mul_left C
  refine Summable.of_nonneg_of_le (fun k => jbDecay_nonneg 10 _) (fun k => ?_) hbase'
  have hC1 : (1:ℝ) ≤ C := le_max_left _ _
  have hC2 : ε⁻¹^10 * 2^10 ≤ C := le_max_right _ _
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [Nat.cast_zero, mul_zero, jbDecay_n_zero]
    simpa using hC1
  · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hkpos : 0 < (k:ℝ) := lt_of_lt_of_le zero_lt_one hk1
    have hek : 0 < ε * (k:ℝ) := mul_pos hε0 hkpos
    have hstep1 : (jb (ε*(k:ℝ)))⁻¹ ≤ (ε*(k:ℝ))⁻¹ := by
      rw [inv_le_inv₀ (jb_pos _) hek]
      calc ε*(k:ℝ) = |ε*(k:ℝ)| := (abs_of_pos hek).symm
        _ ≤ jb (ε*(k:ℝ)) := abs_le_jb _
    have hstep2 : jbDecay 10 (ε*(k:ℝ)) ≤ (ε*(k:ℝ))⁻¹^10 := by
      rw [jbDecay]
      exact pow_le_pow_left₀ (jb_inv_nonneg _) hstep1 10
    have hstep3 : (ε*(k:ℝ))⁻¹^10 = ε⁻¹^10 * ((k:ℝ)⁻¹)^10 := by
      rw [mul_inv, mul_pow]
    have h2 : (k:ℝ)⁻¹ ≤ 2 * ((k:ℝ)+1)⁻¹ := by
      rw [inv_eq_one_div]
      rw [show (2:ℝ) * ((k:ℝ)+1)⁻¹ = 2 / ((k:ℝ)+1) by rw [div_eq_mul_inv]]
      rw [div_le_div_iff₀ hkpos (by positivity)]
      linarith
    have hstep4 : ((k:ℝ)⁻¹)^10 ≤ 2^10 * (((k:ℝ)+1)⁻¹)^10 := by
      calc ((k:ℝ)⁻¹)^10 ≤ (2 * ((k:ℝ)+1)⁻¹)^10 :=
            pow_le_pow_left₀ (by positivity) h2 10
        _ = 2^10 * (((k:ℝ)+1)⁻¹)^10 := by rw [mul_pow]
    calc jbDecay 10 (ε*(k:ℝ)) ≤ (ε*(k:ℝ))⁻¹^10 := hstep2
      _ = ε⁻¹^10 * ((k:ℝ)⁻¹)^10 := hstep3
      _ ≤ ε⁻¹^10 * (2^10 * (((k:ℝ)+1)⁻¹)^10) :=
            mul_le_mul_of_nonneg_left hstep4 (by positivity)
      _ = (ε⁻¹^10 * 2^10) * (((k:ℝ)+1)⁻¹)^10 := by ring
      _ ≤ C * (((k:ℝ)+1)⁻¹)^10 :=
            mul_le_mul_of_nonneg_right hC2 (by positivity)

lemma sum_Icc_nat_jbDecay_ten_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, jbDecay 10 (ε * (k:ℝ)) ≤ (2:ℝ)^60 / ε := by
  have hsum : Summable (fun k : ℕ => ε * jbDecay 10 (ε * (k:ℝ))) :=
    (summable_jbDecay_ten_nat hε0).mul_left ε
  have h1 : ∑ k ∈ Finset.Icc 1 N, ε * jbDecay 10 (ε * (k:ℝ))
      ≤ ∑' k : ℕ, ε * jbDecay 10 (ε * (k:ℝ)) :=
    hsum.sum_le_tsum _ (fun i _ => mul_nonneg hε0.le (jbDecay_nonneg 10 _))
  have h2 : ∑' k : ℕ, ε * jbDecay 10 (ε * (k:ℝ)) ≤ (2:ℝ)^60 := by
    have hr := riemann_shift 9 (by norm_num) hε0 hε1 (le_refl (0:ℝ))
    simpa [jbDecay] using hr
  rw [← Finset.mul_sum] at h1
  have := h1.trans h2
  rw [le_div_iff₀ hε0]
  linarith [this]

/-- `∑_{m ∈ [1,N]} ⟨ε m⟩^{-10} ≤ 2^60/ε` for `0 < ε ≤ 1`, with the summation index in `ℤ`. -/
lemma sum_Icc_int_jbDecay_ten_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (N : ℕ) :
    ∑ m ∈ Finset.Icc (1:ℤ) (N:ℤ), jbDecay 10 (ε * (m:ℝ)) ≤ (2:ℝ)^60 / ε := by
  have hmap : (Finset.Icc 1 N).image (fun k : ℕ => (k:ℤ)) = Finset.Icc (1:ℤ) (N:ℤ) := by
    ext m
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
      exact ⟨by exact_mod_cast hk1, by exact_mod_cast hkN⟩
    · intro hm
      have h0 : (0:ℤ) ≤ m := by omega
      exact ⟨m.toNat, by omega, by omega⟩
  rw [← hmap, Finset.sum_image]
  · exact sum_Icc_nat_jbDecay_ten_le hε0 hε1 N
  · intro a _ b _ hab
    exact Int.ofNat_inj.mp hab

/-! ## The pointwise interior smoothing bound -/

/-- **Pointwise smoothing on the averaging window.**  For `m ∈ [1,N']`, the window sum
`∑_{y ∈ [1,N']} ε ψ(ε(m-y))` differs from `1` by at most
`2^41 C² ε^10 + 2^40 C² (⟨ε(m-1)⟩^{-10} + ⟨ε(m-N'-1)⟩^{-10})`.

This is `halfLine_approx` applied to the two half-lines `y ≥ 1` and `y ≥ N'+1` (whose difference
is the finite window sum), the two error terms being the tails
`∑_{y ≥ N'+1}` and `∑_{y < 1}` of the Poisson approximation. -/
theorem smoothing_interior_pointwise (ψ : ℝ → ℂ) (hcont : Continuous ψ) (C : ℝ) (hC : 1 ≤ C)
    (hint : ∫ t, ψ t = 1)
    (hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * jbDecay 12 t)
    (hFdecay : ∀ t : ℝ, ‖realFourier ψ t‖ ≤ C * jbDecay 12 t)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {N' : ℕ} (hN' : 1 ≤ N') {m : ℤ} (hm1 : 1 ≤ m)
    (hmN : m ≤ N') :
    ‖(∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), calcS ψ ε m y) - 1‖
      ≤ (2:ℝ)^41 * C^2 * ε^10
        + (2:ℝ)^40 * C^2 * (jbDecay 10 (ε * ((m:ℝ) - 1))
            + jbDecay 10 (ε * ((m:ℝ) - (N'+1)))) := by
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hN1 : (1:ℤ) ≤ (N':ℤ) := by exact_mod_cast hN'
  have hthr1 : ∀ y : ℤ, ((1:ℝ) ≤ (y:ℝ)) ↔ (1:ℤ) ≤ y := by
    intro y; constructor <;> intro h <;> exact_mod_cast h
  have hthr2 : ∀ y : ℤ, (((N':ℝ)+1) ≤ (y:ℝ)) ↔ ((N':ℤ)+1) ≤ y := by
    intro y
    have hc : (((N':ℤ)+1 : ℤ) : ℝ) = (N':ℝ)+1 := by push_cast; ring
    rw [← hc]
    constructor <;> intro h <;> exact_mod_cast h
  have hA := halfLine_approx ψ hcont C hC hint hdecay hFdecay (1:ℝ) hε0 hε1 m
  have hB := halfLine_approx ψ hcont C hC hint hdecay hFdecay ((N':ℝ)+1) hε0 hε1 m
  have hAind : (if (1:ℝ) ≤ (m:ℝ) then (1:ℂ) else 0) = 1 := by
    rw [if_pos (by exact_mod_cast hm1)]
  have hBind : (if ((N':ℝ)+1) ≤ (m:ℝ) then (1:ℂ) else 0) = 0 := by
    rw [if_neg]
    have hm : (m:ℝ) ≤ (N':ℝ) := by exact_mod_cast hmN
    linarith
  rw [hAind] at hA
  rw [hBind] at hB
  have hsumA : (∑' y : ℤ, (if (1:ℝ) ≤ (y:ℝ) then (ε:ℂ) * ψ (ε * ((m:ℝ) - y)) else 0))
      = ∑' j : ℕ, calcS ψ ε m (1 + (j:ℤ)) := by
    rw [show (∑' y : ℤ, (if (1:ℝ) ≤ (y:ℝ) then (ε:ℂ) * ψ (ε * ((m:ℝ) - y)) else 0))
        = ∑' y : ℤ, (if (1:ℤ) ≤ y then calcS ψ ε m y else 0) from
        tsum_congr fun y => by simp only [hthr1 y, calcS]]
    exact tsum_Ici_ite_eq_tsum_nat (fun y => calcS ψ ε m y) 1
      (summable_calcS_right hdecay hC0 hε0 1)
  have hsumB : (∑' y : ℤ, (if ((N':ℝ)+1) ≤ (y:ℝ) then (ε:ℂ) * ψ (ε * ((m:ℝ) - y)) else 0))
      = ∑' j : ℕ, calcS ψ ε m ((N':ℤ)+1 + (j:ℤ)) := by
    rw [show (∑' y : ℤ, (if ((N':ℝ)+1) ≤ (y:ℝ) then (ε:ℂ) * ψ (ε * ((m:ℝ) - y)) else 0))
        = ∑' y : ℤ, (if ((N':ℤ)+1) ≤ y then calcS ψ ε m y else 0) from
        tsum_congr fun y => by simp only [hthr2 y, calcS]]
    exact tsum_Ici_ite_eq_tsum_nat (fun y => calcS ψ ε m y) ((N':ℤ)+1)
      (summable_calcS_right hdecay hC0 hε0 ((N':ℤ)+1))
  rw [hsumA] at hA
  rw [hsumB] at hB
  have hsplit := tsum_calcS_eq_sum_Icc_add (ψ := ψ) (C := C) (ε := ε) (x := m)
    hdecay hC0 hε0 (n := (1:ℤ)) (m := (N':ℤ)) hN1
  have hAB : (∑' j : ℕ, calcS ψ ε m (1 + (j:ℤ))) - (∑' j : ℕ, calcS ψ ε m ((N':ℤ)+1 + (j:ℤ)))
      = ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), calcS ψ ε m y := by
    rw [hsplit]; ring
  rw [← hAB]
  have h1 := norm_sub_le (∑' j : ℕ, calcS ψ ε m (1 + (j:ℤ)) - 1)
    (∑' j : ℕ, calcS ψ ε m ((N':ℤ)+1 + (j:ℤ)))
  have h2 : ‖∑' j : ℕ, calcS ψ ε m ((N':ℤ)+1 + (j:ℤ))‖
      ≤ (2:ℝ)^40 * C^2 * (ε^10 + jbDecay 10 (ε * ((m:ℝ) - (N'+1)))) := by
    have hB' := hB
    rw [sub_zero] at hB'
    exact hB'
  have h3 : ‖∑' j : ℕ, calcS ψ ε m (1 + (j:ℤ)) - 1‖
      ≤ (2:ℝ)^40 * C^2 * (ε^10 + jbDecay 10 (ε * ((m:ℝ) - 1))) := hA
  calc ‖(∑' j : ℕ, calcS ψ ε m (1 + (j:ℤ)) - ∑' j : ℕ, calcS ψ ε m ((N':ℤ)+1 + (j:ℤ))) - 1‖
      = ‖(∑' j : ℕ, calcS ψ ε m (1 + (j:ℤ)) - 1)
          - (∑' j : ℕ, calcS ψ ε m ((N':ℤ)+1 + (j:ℤ)))‖ := by
        congr 1; ring
    _ ≤ ‖∑' j : ℕ, calcS ψ ε m (1 + (j:ℤ)) - 1‖
          + ‖∑' j : ℕ, calcS ψ ε m ((N':ℤ)+1 + (j:ℤ))‖ := h1
    _ ≤ (2:ℝ)^40 * C^2 * (ε^10 + jbDecay 10 (ε * ((m:ℝ) - 1)))
        + (2:ℝ)^40 * C^2 * (ε^10 + jbDecay 10 (ε * ((m:ℝ) - (N'+1)))) := add_le_add h3 h2
    _ ≤ (2:ℝ)^41 * C^2 * ε^10
        + (2:ℝ)^40 * C^2 * (jbDecay 10 (ε * ((m:ℝ) - 1))
            + jbDecay 10 (ε * ((m:ℝ) - (N'+1)))) := by
        have hC2 : (0:ℝ) ≤ C^2 := sq_nonneg C
        have he10 : (0:ℝ) ≤ ε^10 := by positivity
        nlinarith [hC2, he10, jbDecay_nonneg 10 (ε * ((m:ℝ) - 1)),
          jbDecay_nonneg 10 (ε * ((m:ℝ) - (N'+1)))]

/-! ## The two exterior tails -/

/-- The lower tail: `∑_{m ≤ 0} ∑_{y ∈ [1,N']} ε⟨ε(m-y)⟩^{-12} ≤ 8 ∑_{y ∈ [1,N']} ⟨εy⟩^{-10}`. -/
lemma exterior_left_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (N' : ℕ) :
    (∑' m : ℤ, (if m ≤ 0 then
        ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), ε * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))) else 0))
      ≤ 8 * ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), jbDecay 10 (ε * (y:ℝ)) := by
  set F : ℤ → ℝ := fun m => ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
    ε * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))) with hF
  have hyt : ∀ y ∈ Finset.Icc (1:ℤ) (N':ℤ), (0:ℝ) ≤ ε * (y:ℝ) := by
    intro y hy
    refine mul_nonneg hε0.le ?_
    have : (0:ℤ) ≤ y := le_trans (by norm_num) (Finset.mem_Icc.mp hy).1
    exact_mod_cast this
  have hsum2 : Summable (fun j : ℕ => ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
      ε * jbDecay 12 (ε * (y:ℝ) + ε * (j:ℝ))) :=
    summable_finset_sum (β := ℕ) (s := Finset.Icc (1:ℤ) (N':ℤ))
      (f := fun (y : ℤ) (j : ℕ) => ε * jbDecay 12 (ε * (y:ℝ) + ε * (j:ℝ)))
      (fun y hy => summable_eps_jbDecay_shift' hε0 (hyt y hy))
  have hpt : ∀ j : ℕ, F (0 - (j:ℤ)) ≤ ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
      ε * jbDecay 12 (ε * (y:ℝ) + ε * (j:ℝ)) := by
    intro j
    rw [hF]
    refine Finset.sum_le_sum (fun y hy => ?_)
    have harg : ε * ((↑(0 - (j:ℤ)) : ℝ) - (y:ℝ)) = -(ε * (y:ℝ) + ε * (j:ℝ)) := by
      push_cast; ring
    rw [harg, jbDecay_neg]
  have hsum : Summable (fun j : ℕ => F (0 - (j:ℤ))) :=
    Summable.of_nonneg_of_le (fun j => by
        rw [hF]
        exact Finset.sum_nonneg (fun y hy => mul_nonneg hε0.le (jbDecay_nonneg 12 _)))
      hpt hsum2
  rw [tsum_Iic_ite_eq_tsum_nat' F 0 hsum]
  calc ∑' j : ℕ, F (0 - (j:ℤ))
      ≤ ∑' j : ℕ, ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), ε * jbDecay 12 (ε * (y:ℝ) + ε * (j:ℝ)) :=
        Summable.tsum_le_tsum hpt hsum hsum2
    _ = ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), ∑' j : ℕ, ε * jbDecay 12 (ε * (y:ℝ) + ε * (j:ℝ)) :=
        Summable.tsum_finsetSum (fun y hy => summable_eps_jbDecay_shift' hε0 (hyt y hy))
    _ ≤ ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), 8 * jbDecay 10 (ε * (y:ℝ)) := by
        refine Finset.sum_le_sum (fun y hy => ?_)
        exact sum_eps_jbDecay_le hε0 hε1 (hyt y hy)
    _ = 8 * ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), jbDecay 10 (ε * (y:ℝ)) := by rw [Finset.mul_sum]

/-- The upper tail: `∑_{m ≥ N'+1} ∑_{y ∈ [1,N']} ε⟨ε(m-y)⟩^{-12} ≤ 8 ∑_{y ∈ [1,N']} ⟨εy⟩^{-10}`. -/
lemma exterior_right_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (N' : ℕ) :
    (∑' m : ℤ, (if (N':ℤ)+1 ≤ m then
        ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), ε * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))) else 0))
      ≤ 8 * ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ), jbDecay 10 (ε * (y:ℝ)) := by
  set F : ℤ → ℝ := fun m => ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
    ε * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))) with hF
  have hyt : ∀ y ∈ Finset.Icc (1:ℤ) (N':ℤ), (0:ℝ) ≤ ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ) := by
    intro y hy
    refine mul_nonneg hε0.le ?_
    have : (0:ℤ) ≤ (N':ℤ)+1 - y := by
      have h2 := (Finset.mem_Icc.mp hy).2
      omega
    exact_mod_cast this
  have hsum2 : Summable (fun j : ℕ => ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
      ε * jbDecay 12 (ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ) + ε * (j:ℝ))) :=
    summable_finset_sum (β := ℕ) (s := Finset.Icc (1:ℤ) (N':ℤ))
      (f := fun (y : ℤ) (j : ℕ) =>
        ε * jbDecay 12 (ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ) + ε * (j:ℝ)))
      (fun y hy => summable_eps_jbDecay_shift' hε0 (hyt y hy))
  have hpt : ∀ j : ℕ, F (((N':ℤ)+1) + (j:ℤ)) ≤ ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
      ε * jbDecay 12 (ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ) + ε * (j:ℝ)) := by
    intro j
    rw [hF]
    refine Finset.sum_le_sum (fun y hy => ?_)
    have harg : ε * ((↑(((N':ℤ)+1) + (j:ℤ)) : ℝ) - (y:ℝ))
        = ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ) + ε * (j:ℝ) := by
      push_cast; ring
    rw [harg]
  have hsum : Summable (fun j : ℕ => F (((N':ℤ)+1) + (j:ℤ))) :=
    Summable.of_nonneg_of_le (fun j => by
        rw [hF]
        exact Finset.sum_nonneg (fun y hy => mul_nonneg hε0.le (jbDecay_nonneg 12 _)))
      hpt hsum2
  rw [tsum_Ici_ite_eq_tsum_nat' F ((N':ℤ)+1) hsum]
  calc ∑' j : ℕ, F (((N':ℤ)+1) + (j:ℤ))
      ≤ ∑' j : ℕ, ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
          ε * jbDecay 12 (ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ) + ε * (j:ℝ)) :=
        Summable.tsum_le_tsum hpt hsum hsum2
    _ = ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
          ∑' j : ℕ, ε * jbDecay 12 (ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ) + ε * (j:ℝ)) :=
        Summable.tsum_finsetSum (fun y hy => summable_eps_jbDecay_shift' hε0 (hyt y hy))
    _ ≤ ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
          8 * jbDecay 10 (ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ)) := by
        refine Finset.sum_le_sum (fun y hy => ?_)
        exact sum_eps_jbDecay_le hε0 hε1 (hyt y hy)
    _ = 8 * ∑ y ∈ Finset.Icc (1:ℤ) (N':ℤ),
          jbDecay 10 (ε * ((((N':ℤ)+1 - y : ℤ)) : ℝ)) := by rw [Finset.mul_sum]
    _ = 8 * ∑ k ∈ Finset.Icc (1:ℤ) (N':ℤ), jbDecay 10 (ε * (k:ℝ)) := by
        congr 1
        refine Finset.sum_bij (fun y _ => ((N':ℤ)+1 - y)) ?_ ?_ ?_ ?_
        · intro y hy
          simp only [Finset.mem_Icc] at hy ⊢
          omega
        · intro y1 h1 y2 h2 heq
          omega
        · intro k hk
          refine ⟨((N':ℤ)+1 - k), ?_, ?_⟩
          · simp only [Finset.mem_Icc] at hk ⊢
            omega
          · omega
        · intro y hy
          rfl

/-! ## Arithmetic with `calcConst` -/

lemma pow_mul_sq_le_calcConst {S : ℝ} (hS : 1 ≤ S) {k : ℕ} (hk : k ≤ 132) :
    (2:ℝ)^k * (S+1)^2 ≤ (S+2)^100 := by
  have h3 : (3:ℝ) ≤ S + 2 := by linarith
  have h2 : (2:ℝ)^k ≤ 3^98 := by
    calc (2:ℝ)^k ≤ (2:ℝ)^132 := pow_le_pow_right₀ (by norm_num) hk
      _ ≤ 3^98 := by norm_num
  have h5 : (S+1)^2 ≤ (S+2)^2 := by nlinarith
  calc (2:ℝ)^k * (S+1)^2 ≤ 3^98 * (S+2)^2 :=
        mul_le_mul h2 h5 (by positivity) (by positivity)
    _ ≤ (S+2)^98 * (S+2)^2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact pow_le_pow_left₀ (by norm_num) h3 98
    _ = (S+2)^100 := by ring

/-! ## The main theorem -/

/-- **The smoothing step of Proposition `lip` (Krause–Mirek–Tao, §6).**  If `ψ ∈ 𝓢(ℝ, ℂ)` has
`∫ψ = 1`, `0 < ε ≤ 1`, `1 ≤ N'`, `f` is bounded by `1` pointwise and `q ∈ ℤ`, then the averaged
polynomial progression `m ↦ (1/N') ∑_{m' ∈ [N']} f(x + q m)` agrees, up to
`calcConst ψ · (ε^10 + (εN')^{-1})`, with its smoothed version
`ε ∑_m ((1/N') ∑_{m' ∈ [N']} ψ(ε(m - m'))) f(x + q m)`. -/
theorem averaging_smooth (ψ : SchwartzR) (hψ : ∫ y, ψ y = 1) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {N' : ℕ} (hN' : 1 ≤ N') (f : ℤ → ℂ) (hf : ∀ y : ℤ, ‖f y‖ ≤ 1) (q : ℤ) (x : ℤ) :
    ‖(N' : ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 N', f (x + q * (m : ℤ))
      - ε * ∑' m : ℤ, ((N' : ℝ)⁻¹ * ∑ m' ∈ Finset.Icc 1 N', ψ (ε * ((m : ℝ) - (m' : ℝ))))
          * f (x + q * (m : ℤ))‖
      ≤ calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) := by
  classical
  -- ### constants
  have hS1 : (1:ℝ) ≤ schwartzSeminormSum ψ := one_le_schwartzSeminormSum ψ hψ
  set C : ℝ := (2:ℝ)^12 * (schwartzSeminormSum ψ + 1) with hCdef
  have hC1 : (1:ℝ) ≤ C := by rw [hCdef]; nlinarith [hS1]
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC1
  have hKpos : (0:ℝ) < calcConst ψ := calcConst_pos ψ
  have hNpos : (0:ℝ) < (N' : ℝ) := by
    have : (1:ℝ) ≤ (N':ℝ) := by exact_mod_cast hN'
    linarith
  have hdecay : ∀ t : ℝ, ‖(ψ : ℝ → ℂ) t‖ ≤ C * jbDecay 12 t := fun t => by
    rw [hCdef]; exact schwartz_decay ψ t
  have hFdecay : ∀ t : ℝ, ‖realFourier (ψ : ℝ → ℂ) t‖ ≤ C * jbDecay 12 t := fun t => by
    rw [hCdef]; exact schwartz_fourier_decay ψ t
  have hcont : Continuous (ψ : ℝ → ℂ) := ψ.continuous
  have hint : ∫ t, (ψ : ℝ → ℂ) t = 1 := hψ
  set I : Finset ℤ := Finset.Icc (1:ℤ) (N':ℤ) with hI
  have hIcard : I.card = N' := by rw [hI, Int.card_Icc]; simp
  have hImap : (Finset.Icc (1:ℕ) N').image (fun k : ℕ => (k:ℤ)) = I := by
    rw [hI]
    ext m
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
      exact ⟨by exact_mod_cast hk1, by exact_mod_cast hkN⟩
    · intro hm
      have h0 : (0:ℤ) ≤ m := by omega
      exact ⟨m.toNat, by omega, by omega⟩
  have hsum_nat : ∀ (F : ℤ → ℂ), (∑ m ∈ Finset.Icc 1 N', F (m:ℤ)) = ∑ m ∈ I, F m := by
    intro F
    rw [← (Finset.sum_image (f := F) (g := fun k : ℕ => (k:ℤ))
      (fun a _ b _ h => Int.ofNat_inj.mp h)), hImap]
  -- ### the summands
  set L : ℤ → ℂ := fun m => ∑ y ∈ I, (ε:ℂ) * ψ (ε * ((m:ℝ) - (y:ℝ))) with hL
  have hLmul : ∀ m : ℤ, L m = (ε:ℂ) * ∑ y ∈ I, ψ (ε * ((m:ℝ) - (y:ℝ))) := by
    intro m; rw [hL, Finset.mul_sum]
  set R : ℤ → ℂ := fun m => (if m ∈ I then (1:ℂ) else 0) - L m with hR
  set A : ℤ → ℝ := fun m => ∑ y ∈ I, ε * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))) with hA
  set G₁ : ℤ → ℂ := fun m => (if m ∈ I then (((N':ℝ)⁻¹ : ℝ) : ℂ) else 0) * f (x + q*m) with hG1
  set G₂ : ℤ → ℂ := fun m =>
    (ε:ℂ) * ((((N':ℝ)⁻¹ : ℝ) : ℂ) * (∑ y ∈ I, ψ (ε * ((m:ℝ) - (y:ℝ))))) * f (x + q*m) with hG2
  have hA0 : ∀ m : ℤ, 0 ≤ A m := by
    intro m; rw [hA]
    exact Finset.sum_nonneg (fun y hy => mul_nonneg hε0.le (jbDecay_nonneg 12 _))
  have hnorm_inv : ‖((((N':ℝ)⁻¹ : ℝ)) : ℂ)‖ = (N':ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  -- ### basic pointwise bound for `L`
  have hLbound : ∀ m : ℤ, ‖L m‖ ≤ C * A m := by
    intro m
    simp only [hL, hA]
    calc ‖∑ y ∈ I, (ε:ℂ) * ψ (ε * ((m:ℝ) - (y:ℝ)))‖
        ≤ ∑ y ∈ I, ‖(ε:ℂ) * ψ (ε * ((m:ℝ) - (y:ℝ)))‖ := norm_sum_le _ _
      _ ≤ ∑ y ∈ I, ε * (C * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ)))) := by
          refine Finset.sum_le_sum (fun y hy => ?_)
          rw [norm_mul, norm_real_coe hε0.le]
          exact mul_le_mul_of_nonneg_left (hdecay _) hε0.le
      _ = C * ∑ y ∈ I, ε * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y hy => by ring)
  -- ### summability
  have hA_summ : Summable A := by
    rw [hA]
    exact summable_finset_sum I
      (fun y hy => (summable_jbDecay_twelve_shift (ε := ε) hε0 y).mul_left ε)
  have hRs : Summable (fun m : ℤ => ‖R m‖) := by
    have hmaj : Summable (fun m : ℤ => (if m ∈ I then (1:ℝ) else 0) + C * A m) := by
      refine (summable_of_ne_finset_zero (s := I) (fun m hm => by simp [hm])).add ?_
      exact hA_summ.mul_left C
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hmaj
    by_cases hm : m ∈ I
    · simp only [hR, if_pos hm]
      have h1 : ‖(1:ℂ) - L m‖ ≤ 1 + ‖L m‖ := by
        calc ‖(1:ℂ) - L m‖ ≤ ‖(1:ℂ)‖ + ‖L m‖ := norm_sub_le _ _
          _ = 1 + ‖L m‖ := by norm_num
      linarith [h1, hLbound m]
    · simp only [hR, if_neg hm, zero_sub, norm_neg, zero_add]
      exact hLbound m
  have hG2summable : Summable G₂ := by
    refine Summable.of_norm_bounded
      (g := fun m : ℤ => ε * ((N':ℝ)⁻¹ * ∑ y ∈ I, C * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ)))))
      ?_ (fun m => ?_)
    · exact (((summable_finset_sum I (fun y hy =>
        (summable_jbDecay_twelve_shift (ε := ε) hε0 y).mul_left C)).mul_left ((N':ℝ)⁻¹))).mul_left ε
    calc ‖G₂ m‖ = ε * ((N':ℝ)⁻¹ * ‖∑ y ∈ I, ψ (ε * ((m:ℝ) - (y:ℝ)))‖) * ‖f (x+q*m)‖ := by
          simp only [hG2]
          rw [norm_mul, norm_mul, norm_mul, norm_real_coe hε0.le, hnorm_inv]
      _ ≤ ε * ((N':ℝ)⁻¹ * (∑ y ∈ I, ‖ψ (ε * ((m:ℝ) - (y:ℝ)))‖)) * ‖f (x+q*m)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)) hε0.le
      _ ≤ ε * ((N':ℝ)⁻¹ * (∑ y ∈ I, ‖ψ (ε * ((m:ℝ) - (y:ℝ)))‖)) * 1 := by
          exact mul_le_mul_of_nonneg_left (hf _) (by positivity)
      _ = ε * ((N':ℝ)⁻¹ * (∑ y ∈ I, ‖ψ (ε * ((m:ℝ) - (y:ℝ)))‖)) := by ring
      _ ≤ ε * ((N':ℝ)⁻¹ * (∑ y ∈ I, C * jbDecay 12 (ε * ((m:ℝ) - (y:ℝ))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun y hy => hdecay _)) (by positivity)
  have hG1summable : Summable G₁ :=
    summable_of_ne_finset_zero (s := I) (fun m hm => by rw [hG1]; simp [hm])
  -- ### the two sums equal the two sides of the statement
  have hG1tsum : (∑' m : ℤ, G₁ m)
      = (N':ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 N', f (x + q * (m:ℤ)) := by
    have h1 : (∑' m : ℤ, G₁ m) = (N':ℝ)⁻¹ * ∑ m ∈ I, f (x + q*m) := by
      rw [tsum_eq_sum (s := I) (f := G₁)
        (fun m hm => by simp only [hG1, if_neg hm, zero_mul])]
      rw [show (∑ m ∈ I, (if m ∈ I then (((N':ℝ)⁻¹ : ℝ) : ℂ) else 0) * f (x + q*m))
          = ∑ m ∈ I, ((((N':ℝ)⁻¹ : ℝ) : ℂ)) * f (x + q*m) from
          Finset.sum_congr rfl (fun m hm => by rw [if_pos hm])]
      rw [Finset.mul_sum]
    rw [h1, ← hsum_nat (fun k => f (x + q*k))]
  have hG2tsum : (∑' m : ℤ, G₂ m)
      = ε * ∑' m : ℤ, ((N':ℝ)⁻¹ * ∑ m' ∈ Finset.Icc 1 N', ψ (ε * ((m:ℝ) - (m':ℝ))))
          * f (x + q * (m:ℤ)) := by
    rw [show (∑' m : ℤ, G₂ m) = ∑' m : ℤ, (ε:ℂ) * ((((N':ℝ)⁻¹ : ℝ) : ℂ)
          * (∑ y ∈ I, ψ (ε * ((m:ℝ) - (y:ℝ)))) * f (x + q*m)) from
        tsum_congr (fun m => by simp only [hG2]; ring)]
    rw [tsum_mul_left]
    congr 1
    refine tsum_congr (fun m => ?_)
    have hcoef : ((N':ℝ)⁻¹ * ∑ m' ∈ Finset.Icc 1 N', ψ (ε * ((m:ℝ) - (m':ℝ))))
        = (((N':ℝ)⁻¹ : ℝ) : ℂ) * (∑ y ∈ I, ψ (ε * ((m:ℝ) - (y:ℝ)))) := by
      rw [← hsum_nat (fun k : ℤ => ψ (ε * ((m:ℝ) - (k:ℝ))))]
      first | done | congr 1
    rw [hcoef]
  have hΔ : (N':ℝ)⁻¹ * ∑ m ∈ Finset.Icc 1 N', f (x + q * (m : ℤ))
      - ε * ∑' m : ℤ, ((N' : ℝ)⁻¹
          * ∑ m' ∈ Finset.Icc 1 N', ψ (ε * ((m : ℝ) - (m' : ℝ)))) * f (x + q * (m : ℤ))
      = ∑' m : ℤ, (G₁ m - G₂ m) := by
    rw [← hG1tsum, ← hG2tsum]
    exact (hG1summable.tsum_sub hG2summable).symm
  -- ### pointwise comparison of the summands with the error weight `R`
  have hdiff_bound : ∀ m : ℤ, ‖G₁ m - G₂ m‖ ≤ (N':ℝ)⁻¹ * ‖R m‖ := by
    intro m
    have hkey : G₁ m - G₂ m = ((((N':ℝ)⁻¹ : ℝ) : ℂ)) * R m * f (x + q*m) := by
      simp only [hG1, hG2, hR, hLmul m]
      by_cases hm : m ∈ I
      · rw [if_pos hm, if_pos hm]; ring
      · rw [if_neg hm, if_neg hm]; ring
    calc ‖G₁ m - G₂ m‖ = ‖((((N':ℝ)⁻¹ : ℝ) : ℂ)) * R m‖ * ‖f (x + q*m)‖ := by
          rw [hkey, norm_mul]
      _ = (N':ℝ)⁻¹ * ‖R m‖ * ‖f (x + q*m)‖ := by rw [norm_mul, hnorm_inv]
      _ ≤ (N':ℝ)⁻¹ * ‖R m‖ * 1 := by
          refine mul_le_mul_of_nonneg_left (hf _) (by positivity)
      _ = (N':ℝ)⁻¹ * ‖R m‖ := by ring
  have hsumm_diff : Summable (fun m : ℤ => ‖G₁ m - G₂ m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hdiff_bound (hRs.mul_left _)
  -- ### splitting the error mass
  have hsplitR : (∑' m : ℤ, ‖R m‖)
      = (∑ m ∈ I, ‖R m‖) + ∑' m : ℤ, (if m ∈ I then 0 else ‖R m‖) := by
    have hin : Summable (fun m : ℤ => if m ∈ I then ‖R m‖ else 0) :=
      summable_of_ne_finset_zero (s := I) (fun m hm => by simp [hm])
    have hout : Summable (fun m : ℤ => if m ∈ I then 0 else ‖R m‖) := by
      refine Summable.of_nonneg_of_le (fun m => by split <;> positivity) (fun m => ?_) hRs
      by_cases hm : m ∈ I <;> simp [hm]
    rw [show (∑' m : ℤ, ‖R m‖) = ∑' m : ℤ,
        ((if m ∈ I then ‖R m‖ else 0) + (if m ∈ I then 0 else ‖R m‖)) from
        tsum_congr (fun m => by by_cases hm : m ∈ I <;> simp [hm])]
    rw [Summable.tsum_add hin hout]
    rw [tsum_eq_sum (s := I) (f := fun m : ℤ => if m ∈ I then ‖R m‖ else 0)
      (fun m hm => by simp [hm])]
    congr 1
    exact Finset.sum_congr rfl (fun m hm => by rw [if_pos hm])
  -- ### the interior estimate
  have hpt_int : ∀ m ∈ I, ‖R m‖ ≤ (2:ℝ)^41 * C^2 * ε^10
      + (2:ℝ)^40 * C^2 * (jbDecay 10 (ε * ((m:ℝ) - 1))
          + jbDecay 10 (ε * ((m:ℝ) - (N'+1)))) := by
    intro m hm
    have hm1 : (1:ℤ) ≤ m := (Finset.mem_Icc.mp (by rwa [hI] at hm)).1
    have hmN : m ≤ (N':ℤ) := (Finset.mem_Icc.mp (by rwa [hI] at hm)).2
    have h := smoothing_interior_pointwise ψ hcont C hC1 hint hdecay hFdecay hε0 hε1 hN' hm1 hmN
    have hLc : L m = ∑ y ∈ I, calcS ψ ε m y := by
      simp only [hL, calcS]
    simp only [hR, if_pos hm]
    rw [hLc, norm_sub_rev]
    exact h
  have hSig : ∑ k ∈ I, jbDecay 10 (ε * (k:ℝ)) ≤ (2:ℝ)^60 / ε := by
    rw [hI]; exact sum_Icc_int_jbDecay_ten_le hε0 hε1 N'
  have hSig1 : ∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - 1)) ≤ 1 + (2:ℝ)^60 / ε := by
    have hcongr : ∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - 1))
        = ∑ m ∈ I, jbDecay 10 (ε * (((m - 1 : ℤ)) : ℝ)) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      congr 2
      push_cast
      ring
    rw [hcongr, hI]
    have himg : (Finset.Icc (1:ℤ) (N':ℤ)).image (fun m : ℤ => m - 1)
        = Finset.Icc (0:ℤ) ((N':ℤ) - 1) := by
      ext k
      simp only [Finset.mem_image, Finset.mem_Icc]
      constructor
      · rintro ⟨m, ⟨hm1, hmN⟩, rfl⟩
        omega
      · intro hk
        exact ⟨k+1, ⟨by omega, by omega⟩, by ring⟩
    have hinj : Set.InjOn (fun m : ℤ => m - 1) (↑(Finset.Icc (1:ℤ) (N':ℤ)) : Set ℤ) :=
      fun a _ b _ h => by
        have h' : a - 1 = b - 1 := h
        omega
    rw [← Finset.sum_image (f := fun k : ℤ => jbDecay 10 (ε * (k:ℝ))) (g := fun m : ℤ => m - 1)
      hinj, himg]
    have hsub : Finset.Icc (0:ℤ) ((N':ℤ) - 1) ⊆ Finset.Icc (0:ℤ) (N':ℤ) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    calc ∑ k ∈ Finset.Icc (0:ℤ) ((N':ℤ) - 1), jbDecay 10 (ε * (k:ℝ))
        ≤ ∑ k ∈ Finset.Icc (0:ℤ) (N':ℤ), jbDecay 10 (ε * (k:ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun k hk1 hk2 => jbDecay_nonneg 10 _)
      _ = jbDecay 10 (0:ℝ) + ∑ k ∈ I, jbDecay 10 (ε * (k:ℝ)) := by
          have hIcc0 : Finset.Icc (0:ℤ) (N':ℤ) = insert 0 I := by
            rw [hI]
            ext k
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          have hnot : (0:ℤ) ∉ I := by
            rw [hI]; simp only [Finset.mem_Icc]; omega
          rw [hIcc0, Finset.sum_insert hnot, Int.cast_zero, mul_zero]
      _ ≤ 1 + (2:ℝ)^60 / ε := by
          rw [jbDecay_n_zero]
          linarith [hSig]
  have hSig2 : ∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - (N'+1))) = ∑ k ∈ I, jbDecay 10 (ε * (k:ℝ)) := by
    rw [hI]
    refine Finset.sum_bij (fun m _ => ((N':ℤ)+1 - m)) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro m1 h1 m2 h2 heq
      omega
    · intro k hk
      refine ⟨((N':ℤ)+1 - k), ?_, ?_⟩
      · simp only [Finset.mem_Icc] at hk ⊢
        omega
      · omega
    · intro m hm
      have harg : ε * ((m:ℝ) - (N'+1)) = -(ε * ((((N':ℤ)+1 - m : ℤ)) : ℝ)) := by
        push_cast; ring
      rw [harg, jbDecay_neg]
  have hinter : ∑ m ∈ I, ‖R m‖ ≤ (N':ℝ) * ((2:ℝ)^41 * C^2 * ε^10)
      + (2:ℝ)^40 * C^2 * (1 + 2 * ((2:ℝ)^60 / ε)) := by
    have hstep : ∑ m ∈ I, ((2:ℝ)^41 * C^2 * ε^10
        + (2:ℝ)^40 * C^2 * (jbDecay 10 (ε * ((m:ℝ) - 1))
            + jbDecay 10 (ε * ((m:ℝ) - (N'+1)))))
        = (I.card : ℝ) * ((2:ℝ)^41 * C^2 * ε^10)
          + (2:ℝ)^40 * C^2 * ((∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - 1)))
              + (∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - (N'+1))))) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      try ring
    calc ∑ m ∈ I, ‖R m‖ ≤ ∑ m ∈ I, ((2:ℝ)^41 * C^2 * ε^10
        + (2:ℝ)^40 * C^2 * (jbDecay 10 (ε * ((m:ℝ) - 1))
            + jbDecay 10 (ε * ((m:ℝ) - (N'+1))))) := Finset.sum_le_sum hpt_int
      _ = (I.card : ℝ) * ((2:ℝ)^41 * C^2 * ε^10)
          + (2:ℝ)^40 * C^2 * ((∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - 1)))
              + (∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - (N'+1))))) := hstep
      _ ≤ (N':ℝ) * ((2:ℝ)^41 * C^2 * ε^10)
          + (2:ℝ)^40 * C^2 * (1 + 2 * ((2:ℝ)^60 / ε)) := by
          rw [hIcard]
          have h6 : ∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - (N'+1))) ≤ (2:ℝ)^60 / ε := by
            rw [hSig2]; exact hSig
          have hC2 : (0:ℝ) ≤ (2:ℝ)^40 * C^2 := by positivity
          have hsum_le : (∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - 1)))
              + (∑ m ∈ I, jbDecay 10 (ε * ((m:ℝ) - (N'+1)))) ≤ 1 + 2 * ((2:ℝ)^60 / ε) := by
            linarith [hSig1, h6]
          exact add_le_add (le_refl ((N':ℝ) * ((2:ℝ)^41 * C^2 * ε^10)))
            (mul_le_mul_of_nonneg_left hsum_le hC2)
  -- ### the exterior estimate
  have hRout : (∑' m : ℤ, (if m ∈ I then 0 else ‖R m‖)) ≤ 16 * C * ((2:ℝ)^60 / ε) := by
    have hpt : ∀ m : ℤ, (if m ∈ I then 0 else ‖R m‖)
        ≤ C * ((if m ≤ 0 then A m else 0) + (if (N':ℤ)+1 ≤ m then A m else 0)) := by
      intro m
      by_cases hm : m ∈ I
      · rw [if_pos hm]
        refine mul_nonneg hC0 (add_nonneg ?_ ?_)
        · by_cases h : m ≤ 0
          · rw [if_pos h]; exact hA0 m
          · rw [if_neg h]
        · by_cases h : (N':ℤ)+1 ≤ m
          · rw [if_pos h]; exact hA0 m
          · rw [if_neg h]
      · rw [if_neg hm]
        have hle : m ≤ 0 ∨ (N':ℤ)+1 ≤ m := by
          have h1 : ¬ ((1:ℤ) ≤ m ∧ m ≤ (N':ℤ)) := by
            intro hc; exact hm (by rw [hI]; exact Finset.mem_Icc.mpr hc)
          omega
        have hRm : ‖R m‖ = ‖L m‖ := by simp only [hR, if_neg hm, zero_sub, norm_neg]
        rcases hle with h0 | hN
        · rw [if_pos h0, if_neg (by omega)]
          calc ‖R m‖ = ‖L m‖ := hRm
            _ ≤ C * A m := hLbound m
            _ = C * (A m + 0) := by ring
        · rw [if_neg (by omega), if_pos hN]
          calc ‖R m‖ = ‖L m‖ := hRm
            _ ≤ C * A m := hLbound m
            _ = C * (0 + A m) := by ring
    have hleft : Summable (fun m : ℤ => if m ≤ 0 then A m else 0) :=
      Summable.of_nonneg_of_le (fun m => by
          by_cases h : m ≤ 0
          · simp only [if_pos h]; exact hA0 m
          · simp only [if_neg h]; exact le_refl 0)
        (fun m => by
          by_cases h : m ≤ 0
          · simp only [if_pos h]; exact le_refl (A m)
          · simp only [if_neg h]; exact hA0 m) hA_summ
    have hright : Summable (fun m : ℤ => if (N':ℤ)+1 ≤ m then A m else 0) :=
      Summable.of_nonneg_of_le (fun m => by
          by_cases h : (N':ℤ)+1 ≤ m
          · simp only [if_pos h]; exact hA0 m
          · simp only [if_neg h]; exact le_refl 0)
        (fun m => by
          by_cases h : (N':ℤ)+1 ≤ m
          · simp only [if_pos h]; exact le_refl (A m)
          · simp only [if_neg h]; exact hA0 m) hA_summ
    have hRHSsumm : Summable (fun m : ℤ => C * ((if m ≤ 0 then A m else 0)
        + (if (N':ℤ)+1 ≤ m then A m else 0))) := (hleft.add hright).mul_left C
    have hRout_summ : Summable (fun m : ℤ => if m ∈ I then 0 else ‖R m‖) :=
      Summable.of_nonneg_of_le (fun m => by
        by_cases h : m ∈ I
        · simp only [if_pos h]; exact le_refl 0
        · simp only [if_neg h]; exact norm_nonneg _) hpt hRHSsumm
    calc (∑' m : ℤ, (if m ∈ I then 0 else ‖R m‖))
        ≤ ∑' m : ℤ, C * ((if m ≤ 0 then A m else 0) + (if (N':ℤ)+1 ≤ m then A m else 0)) :=
          Summable.tsum_le_tsum hpt hRout_summ hRHSsumm
      _ = C * ((∑' m : ℤ, (if m ≤ 0 then A m else 0))
            + (∑' m : ℤ, (if (N':ℤ)+1 ≤ m then A m else 0))) := by
          rw [tsum_mul_left, Summable.tsum_add hleft hright]
      _ ≤ C * (8 * (∑ y ∈ I, jbDecay 10 (ε * (y:ℝ)))
            + 8 * (∑ y ∈ I, jbDecay 10 (ε * (y:ℝ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ hC0
          refine add_le_add ?_ ?_
          · have h := exterior_left_le hε0 hε1 N'
            simpa only [hA, hI] using h
          · have h := exterior_right_le hε0 hε1 N'
            simpa only [hA, hI] using h
      _ = 16 * C * (∑ y ∈ I, jbDecay 10 (ε * (y:ℝ))) := by ring
      _ ≤ 16 * C * ((2:ℝ)^60 / ε) := by
          refine mul_le_mul_of_nonneg_left hSig (by positivity)
  -- ### assembly
  have hcollapse : (N':ℝ)⁻¹ * ((N':ℝ) * ((2:ℝ)^41 * C^2 * ε^10)
      + (2:ℝ)^40 * C^2 * (1 + 2 * ((2:ℝ)^60 / ε)) + 16 * C * ((2:ℝ)^60 / ε))
      = (2:ℝ)^41 * C^2 * ε^10 + ((2:ℝ)^40 * C^2) / (N':ℝ)
        + (((2:ℝ)^101 * C^2 + (2:ℝ)^64 * C)) / (ε * (N':ℝ)) := by
    field_simp
    ring
  have hComb : (2:ℝ)^40 * C^2 + (2:ℝ)^101 * C^2 + (2:ℝ)^64 * C ≤ calcConst ψ := by
    have hcs : C^2 = (2:ℝ)^24 * (schwartzSeminormSum ψ + 1)^2 := by rw [hCdef]; ring
    have hcl : C = (2:ℝ)^12 * (schwartzSeminormSum ψ + 1) := hCdef
    have e1 : (2:ℝ)^40 * C^2 = (2:ℝ)^64 * (schwartzSeminormSum ψ + 1)^2 := by rw [hcs]; ring
    have e2 : (2:ℝ)^101 * C^2 = (2:ℝ)^125 * (schwartzSeminormSum ψ + 1)^2 := by rw [hcs]; ring
    have e3 : (2:ℝ)^64 * C = (2:ℝ)^76 * (schwartzSeminormSum ψ + 1) := by rw [hcl]; ring
    rw [e1, e2, e3]
    set S : ℝ := schwartzSeminormSum ψ with hSdef
    have hS2 : (2:ℝ) ≤ S + 1 := by linarith
    have h4 : (2:ℝ)^76 * (S+1) ≤ (2:ℝ)^125 * (S+1)^2 := by
      rw [show (2:ℝ)^125 * (S+1)^2 = ((2:ℝ)^125 * (S+1)) * (S+1) by ring]
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      nlinarith [hS2]
    have h5 : (2:ℝ)^64 * (S+1)^2 ≤ (2:ℝ)^125 * (S+1)^2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
    have h6 : (2:ℝ)^125 * (S+1)^2 * 4 ≤ (2:ℝ)^130 * (S+1)^2 := by
      rw [show (2:ℝ)^130 * (S+1)^2 = (2:ℝ)^125 * (S+1)^2 * 32 by ring]
      nlinarith [sq_nonneg (S+1), pow_pos (by norm_num : (0:ℝ) < 2) 125]
    have hK := pow_mul_sq_le_calcConst hS1 (k := 130) (by norm_num)
    rw [calcConst]
    linarith
  have hfinal : (2:ℝ)^41 * C^2 * ε^10 + ((2:ℝ)^40 * C^2) / (N':ℝ)
      + (((2:ℝ)^101 * C^2 + (2:ℝ)^64 * C)) / (ε * (N':ℝ))
      ≤ calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) := by
    have h1 : (2:ℝ)^41 * C^2 * ε^10 ≤ calcConst ψ * ε^10 := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hcs : C^2 = (2:ℝ)^24 * (schwartzSeminormSum ψ + 1)^2 := by rw [hCdef]; ring
      have : (2:ℝ)^41 * C^2 = (2:ℝ)^65 * (schwartzSeminormSum ψ + 1)^2 := by rw [hcs]; ring
      rw [this, calcConst]
      exact pow_mul_sq_le_calcConst hS1 (k := 65) (by norm_num)
    have h2 : ((2:ℝ)^40 * C^2) / (N':ℝ) + (((2:ℝ)^101 * C^2 + (2:ℝ)^64 * C)) / (ε * (N':ℝ))
        ≤ calcConst ψ * (ε * (N':ℝ))⁻¹ := by
      have hεN : ε * (N':ℝ) ≤ (N':ℝ) := by nlinarith [hε1, hNpos]
      have hone : (0:ℝ) < ε * (N':ℝ) := mul_pos hε0 hNpos
      have hfirst : ((2:ℝ)^40 * C^2) / (N':ℝ) ≤ ((2:ℝ)^40 * C^2) / (ε * (N':ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) hone hεN
      calc ((2:ℝ)^40 * C^2) / (N':ℝ) + (((2:ℝ)^101 * C^2 + (2:ℝ)^64 * C)) / (ε * (N':ℝ))
          ≤ ((2:ℝ)^40 * C^2) / (ε * (N':ℝ))
              + (((2:ℝ)^101 * C^2 + (2:ℝ)^64 * C)) / (ε * (N':ℝ)) := by linarith [hfirst]
        _ = (((2:ℝ)^40 * C^2) + ((2:ℝ)^101 * C^2 + (2:ℝ)^64 * C)) / (ε * (N':ℝ)) := by
            rw [← add_div]
        _ ≤ calcConst ψ / (ε * (N':ℝ)) :=
            div_le_div_of_nonneg_right (by linarith [hComb]) hone.le
        _ = calcConst ψ * (ε * (N':ℝ))⁻¹ := by rw [div_eq_mul_inv]
    have h3 : calcConst ψ * ε^10 + calcConst ψ * (ε * (N':ℝ))⁻¹
        = calcConst ψ * (ε^10 + (ε * (N' : ℝ))⁻¹) := by ring
    linarith [h1, h2, h3]
  rw [hΔ]
  calc ‖∑' m : ℤ, (G₁ m - G₂ m)‖
      ≤ ∑' m : ℤ, ‖G₁ m - G₂ m‖ := norm_tsum_le_tsum_norm hsumm_diff
    _ ≤ ∑' m : ℤ, (N':ℝ)⁻¹ * ‖R m‖ :=
        Summable.tsum_le_tsum hdiff_bound hsumm_diff (hRs.mul_left _)
    _ = (N':ℝ)⁻¹ * ∑' m : ℤ, ‖R m‖ := tsum_mul_left
    _ = (N':ℝ)⁻¹ * ((∑ m ∈ I, ‖R m‖) + ∑' m : ℤ, (if m ∈ I then 0 else ‖R m‖)) := by
        rw [hsplitR]
    _ ≤ (N':ℝ)⁻¹ * ((N':ℝ) * ((2:ℝ)^41 * C^2 * ε^10)
        + (2:ℝ)^40 * C^2 * (1 + 2 * ((2:ℝ)^60 / ε)) + 16 * C * ((2:ℝ)^60 / ε)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact add_le_add hinter hRout
    _ = (2:ℝ)^41 * C^2 * ε^10 + ((2:ℝ)^40 * C^2) / (N':ℝ)
        + (((2:ℝ)^101 * C^2 + (2:ℝ)^64 * C)) / (ε * (N':ℝ)) := hcollapse
    _ ≤ calcConst ψ * (ε ^ 10 + (ε * (N' : ℝ))⁻¹) := hfinal

end Work.Analysis.InverseTheory
