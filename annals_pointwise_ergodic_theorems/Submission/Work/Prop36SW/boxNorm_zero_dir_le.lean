import Mathlib
import Submission.Work.Peluse.Prop36SW.uNormPowGeMeanPow

/-!
# The uniformity norm at the degenerate direction family `0[L] = {0}` dominates the box norm

For `1 ≤ L` the arithmetic progression `arithIcc 0 L = {0 · 1, …, 0 · L}` is the singleton `{0}`.
At a singleton direction family the `2 ^ s`-th box-norm power collapses to the plain `2 ^ s`-th
moment of `‖f‖` over the window (`Work.Peluse.Ulower.uNormPow_singleton_symIcc`), i.e. the
level-`s` *uniformity* norm there is the `L^{2^s}` norm of `f` on the window.

The lemma `Work.Prop36SW.boxNorm_zero_dir_le` says that this degenerate `U^{s'}`-norm still
dominates the Gowers box norm of *any* level-`t` direction family, `t ≤ s'`, on the same window:
if `δ` is a lower bound for `‖f‖_{□^t_{Q}(symIcc N)}` with `Q i = d i[M₁]`, then `δ` is also a
lower bound for `‖f‖_{U^{s'}_{0[L]}(symIcc N)}`.

The proof has three ingredients, all elementary.

1. **The box norm is bounded by the `2^t`-th moment** (the special case `Q = {0}` of the standard
   fact `‖f‖_{□^t} ≤ ‖f‖_{L^{2^t}}`): the cube average is a mean of the `2^t` shifted values
   `‖f (x + ω·h + (1-ω)·h')‖`, and the geometric mean of `2^t` nonnegative numbers is at most
   their arithmetic mean (`Real.geom_mean_le_arith_mean_weighted` with equal weights `2^{-t}`),
   while the sum over `x ∈ ℤ` is translation invariant; hence

   `‖f‖_{□^t_Q(S)}^{2^t} ≤ |S|⁻¹ ∑_x ‖f x‖^{2^t}`.

2. **The power-mean (Jensen) step**: since `2 ^ t ∣ 2 ^ s'` for `t ≤ s'` and the summand
   `g x = ‖f x‖^{2^t}` is nonnegative, the `q = 2^{s'-t}`-th power of the mean is at most the mean
   of the `q`-th powers (`Work.Peluse.Prop36SW.sum_pow_le_card_pow_mul_sum_pow`).

3. **The collapse at the singleton direction family**: `uNormPow s' {0} S f` is the `2^{s'}`-th
   moment of `‖f‖` over `S` (`Work.Peluse.Ulower.uNormPow_singleton_symIcc`, for `1 ≤ s'`).

Putting the three together, `δ^{2^t} ≤ |S|⁻¹ ∑ ‖f‖^{2^t}` gives
`δ^{2^{s'}} ≤ |S|⁻¹ ∑ ‖f‖^{2^{s'}} = ‖f‖^{2^{s'}}_{U^{s'}_{0[L]}(S)}`, and taking `2^{s'}`-th roots
gives the claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Prop36SW

/-! Auxiliary lemmas for `Work.Prop36SW.boxNorm_zero_dir_le`.  The pieces are self-contained and
stated in the vocabulary of `Work.Peluse`; they are kept in a separate namespace so as not to
interfere with the sibling modules of this directory. -/
namespace ZeroDirAux

open Work.Peluse

noncomputable section

/-- The modulus is preserved by iterated conjugation. -/
private lemma norm_star_iterate' (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- **AM–GM with equal weights.**  For `b ω ≥ 0` the product of the `2^t` numbers `b ω` is at most
their arithmetic mean.  This is `Real.geom_mean_le_arith_mean_weighted` at the weights `2^{-t}`
applied to the numbers `b ω ^ (2^t)`. -/
private lemma prod_le_inv_card_mul_sum_pow {t : ℕ} (b : (Fin t → Bool) → ℝ)
    (hb : ∀ ω, 0 ≤ b ω) :
    ∏ ω : Fin t → Bool, b ω ≤ (((2 ^ t : ℕ) : ℝ))⁻¹ * ∑ ω : Fin t → Bool, b ω ^ (2 ^ t) := by
  have hNne : (2 ^ t : ℕ) ≠ 0 := by positivity
  have hcard : (Finset.univ : Finset (Fin t → Bool)).card = 2 ^ t := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp [Fintype.card_bool, Fintype.card_fin]
  have hw : ∑ _i ∈ (Finset.univ : Finset (Fin t → Bool)), (((2 ^ t : ℕ) : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
      (w := fun _ : Fin t → Bool => (((2 ^ t : ℕ) : ℝ))⁻¹)
      (z := fun ω => b ω ^ (2 ^ t))
      (fun i _ => by positivity) hw (fun i _ => pow_nonneg (hb i) _)
  rw [Finset.prod_congr rfl (fun ω _ => Real.pow_rpow_inv_natCast (hb ω) hNne)] at hgm
  rw [← Finset.mul_sum] at hgm
  exact hgm

/-- A product of `2^t` shifted moduli is summable (the function is finitely supported). -/
private lemma summable_prod_norm_shift {t : ℕ} (c : (Fin t → Bool) → ℤ) (f : ℤ → ℂ)
    (hf : FinSuppZ f) :
    Summable (fun x : ℤ => ∏ ω : Fin t → Bool, ‖f (x + c ω)‖) := by
  obtain ⟨N₀, hN₀⟩ := hf
  have hvan : ∀ x : ℤ, x ∉ symIcc N₀ → f x = 0 :=
    fun x hx => hN₀ x (Ulower.lt_natAbs_of_notMem_symIcc hx)
  set ω₀ : Fin t → Bool := fun _ => false with hω₀
  refine summable_of_ne_finset_zero (s := (Finset.univ : Finset (Fin t → Bool)).biUnion
      (fun ω => (symIcc N₀).image (fun y => y - c ω))) ?_
  intro x hx
  have hxc : x ∉ (symIcc N₀).image (fun y => y - c ω₀) :=
    fun h => hx (Finset.mem_biUnion.mpr ⟨ω₀, Finset.mem_univ ω₀, h⟩)
  have hx' : x + c ω₀ ∉ symIcc N₀ :=
    fun h => hxc (Finset.mem_image.mpr ⟨x + c ω₀, h, by ring⟩)
  exact Finset.prod_eq_zero (Finset.mem_univ ω₀) (by rw [hvan (x + c ω₀) hx', norm_zero])

/-- **The `L^{2^t}`-bound for a shift product.**  For any shifts `c : (Fin t → Bool) → ℤ` and any
finitely supported `f : ℤ → ℂ`,

`∑'_x ∏_ω ‖f (x + c ω)‖ ≤ ∑'_x ‖f x‖^{2^t}`.

This is the pointwise AM–GM estimate summed over `x ∈ ℤ`, using the translation invariance of the
sum over `ℤ`. -/
private lemma tsum_prod_norm_shift_le {t : ℕ} (c : (Fin t → Bool) → ℤ) (f : ℤ → ℂ)
    (hf : FinSuppZ f) :
    ∑' x : ℤ, ∏ ω : Fin t → Bool, ‖f (x + c ω)‖ ≤ ∑' x : ℤ, ‖f x‖ ^ (2 ^ t) := by
  obtain ⟨N₀, hN₀⟩ := hf
  have hNne : (2 ^ t : ℕ) ≠ 0 := by positivity
  have hcard : (Finset.univ : Finset (Fin t → Bool)).card = 2 ^ t := by
    rw [Finset.card_univ, Fintype.card_fun]
    simp [Fintype.card_bool, Fintype.card_fin]
  have hvan : ∀ x : ℤ, x ∉ symIcc N₀ → f x = 0 :=
    fun x hx => hN₀ x (Ulower.lt_natAbs_of_notMem_symIcc hx)
  have hsumm_shift : ∀ ω : Fin t → Bool,
      Summable (fun x : ℤ => ‖f (x + c ω)‖ ^ (2 ^ t)) := by
    intro ω
    refine summable_of_ne_finset_zero (s := (symIcc N₀).image (fun y => y - c ω)) ?_
    intro x hx
    have hx' : x + c ω ∉ symIcc N₀ :=
      fun h => hx (Finset.mem_image.mpr ⟨x + c ω, h, by ring⟩)
    rw [hvan (x + c ω) hx', norm_zero, zero_pow hNne]
  have hsumm_rhs : Summable (fun x : ℤ =>
      (((2 ^ t : ℕ) : ℝ))⁻¹ * ∑ ω : Fin t → Bool, ‖f (x + c ω)‖ ^ (2 ^ t)) := by
    refine summable_of_ne_finset_zero
      (s := (Finset.univ : Finset (Fin t → Bool)).biUnion
        (fun ω => (symIcc N₀).image (fun y => y - c ω))) ?_
    intro x hx
    have hzω : ∀ ω : Fin t → Bool, ‖f (x + c ω)‖ ^ (2 ^ t) = 0 := by
      intro ω
      have hxc : x ∉ (symIcc N₀).image (fun y => y - c ω) :=
        fun h => hx (Finset.mem_biUnion.mpr ⟨ω, Finset.mem_univ ω, h⟩)
      have hx' : x + c ω ∉ symIcc N₀ :=
        fun h => hxc (Finset.mem_image.mpr ⟨x + c ω, h, by ring⟩)
      rw [hvan (x + c ω) hx', norm_zero, zero_pow hNne]
    rw [Finset.sum_eq_zero (fun ω _ => hzω ω), mul_zero]
  have hAM : ∀ x : ℤ, ∏ ω : Fin t → Bool, ‖f (x + c ω)‖
      ≤ (((2 ^ t : ℕ) : ℝ))⁻¹ * ∑ ω : Fin t → Bool, ‖f (x + c ω)‖ ^ (2 ^ t) :=
    fun x => prod_le_inv_card_mul_sum_pow (fun ω => ‖f (x + c ω)‖) (fun ω => norm_nonneg _)
  have hsumm_prod : Summable (fun x : ℤ => ∏ ω : Fin t → Bool, ‖f (x + c ω)‖) :=
    Summable.of_nonneg_of_le (fun x => Finset.prod_nonneg fun ω _ => norm_nonneg _)
      (fun x => hAM x) hsumm_rhs
  calc ∑' x : ℤ, ∏ ω : Fin t → Bool, ‖f (x + c ω)‖
      ≤ ∑' x : ℤ, (((2 ^ t : ℕ) : ℝ))⁻¹ * ∑ ω : Fin t → Bool, ‖f (x + c ω)‖ ^ (2 ^ t) :=
        hsumm_prod.tsum_le_tsum hAM hsumm_rhs
    _ = (((2 ^ t : ℕ) : ℝ))⁻¹ * ∑' x : ℤ, ∑ ω : Fin t → Bool, ‖f (x + c ω)‖ ^ (2 ^ t) :=
        tsum_mul_left
    _ = (((2 ^ t : ℕ) : ℝ))⁻¹ * ∑ ω : Fin t → Bool, ∑' x : ℤ, ‖f (x + c ω)‖ ^ (2 ^ t) := by
        rw [Summable.tsum_finsetSum (fun ω _ => hsumm_shift ω)]
    _ = (((2 ^ t : ℕ) : ℝ))⁻¹ * ∑ ω : Fin t → Bool, ∑' x : ℤ, ‖f x‖ ^ (2 ^ t) := by
        congr 1
        exact Finset.sum_congr rfl
          (fun ω _ => Equiv.tsum_eq (Equiv.addRight (c ω)) (fun x => ‖f x‖ ^ (2 ^ t)))
    _ = (((2 ^ t : ℕ) : ℝ))⁻¹ * ((2 ^ t : ℕ) * ∑' x : ℤ, ‖f x‖ ^ (2 ^ t)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = ∑' x : ℤ, ‖f x‖ ^ (2 ^ t) := by
        have : (((2 ^ t : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp

/-- **The box-norm power is bounded by the `2^t`-th moment.**  For every finitely supported
`f : ℤ → ℂ`, every direction family `Q` and every window `S`,

`‖f‖_{□^t_Q(S)}^{2^t} ≤ |S|⁻¹ ∑_x ‖f x‖^{2^t}`.

This is the `Q = {0}`-monotonicity of the box norm, proved by expanding the cube average and
applying `tsum_prod_norm_shift_le` to each pair of shift tuples. -/
private lemma boxNormPow_le_normAvg (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hf : FinSuppZ f) :
    boxNormPow t Q S f ≤ ((S.card : ℝ))⁻¹ * ∑' x : ℤ, ‖f x‖ ^ (2 ^ t) := by
  classical
  set Lp : ℝ := ∑' x : ℤ, ‖f x‖ ^ (2 ^ t) with hLp
  have hLpnn : 0 ≤ Lp := tsum_nonneg (fun x => pow_nonneg (norm_nonneg _) _)
  set P : ℝ := ∏ i : Fin t, ((Q i).card : ℝ) with hP
  set Pin : ℝ := ∏ i : Fin t, ((Q i).card : ℝ)⁻¹ with hPin
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)
  have hPinnn : 0 ≤ Pin := Finset.prod_nonneg (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  set Raw : ℂ := ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))
    with hRaw
  have hinner : ∀ h h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
      ‖∑' x : ℤ, ∏ ω : Fin t → Bool,
        (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
        ≤ Lp := by
    intro h h'
    set c : (Fin t → Bool) → ℤ :=
      fun ω => cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω with hc
    have hsummp : Summable (fun x : ℤ => ∏ ω : Fin t → Bool, ‖f (x + c ω)‖) :=
      summable_prod_norm_shift c f hf
    have hnorm_eq : (fun x : ℤ => ‖∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + c ω))‖)
        = fun x : ℤ => ∏ ω : Fin t → Bool, ‖f (x + c ω)‖ := by
      funext x
      rw [norm_prod]
      exact Finset.prod_congr rfl
        (fun ω _ => norm_star_iterate' (weight ω) (f (x + c ω)))
    calc ‖∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + c ω))‖
        ≤ ∑' x : ℤ, ‖∏ ω : Fin t → Bool, (star^[weight ω]) (f (x + c ω))‖ :=
          norm_tsum_le_tsum_norm (by rw [hnorm_eq]; exact hsummp)
      _ = ∑' x : ℤ, ∏ ω : Fin t → Bool, ‖f (x + c ω)‖ := by rw [hnorm_eq]
      _ ≤ Lp := tsum_prod_norm_shift_le c f hf
  have hcardα : (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) = P := by
    rw [hP, Fintype.card_pi]
    push_cast
    exact Finset.prod_congr rfl (fun i _ => by rw [Fintype.card_coe])
  have hRaw_le : ‖Raw‖ ≤ (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
      (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * Lp := by
    rw [hRaw]
    calc ‖∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, ∏ ω : Fin t → Bool,
              (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖
        ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ‖∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ∑' x : ℤ, ∏ ω : Fin t → Bool,
              (star^[weight ω])
                (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
            ‖∑' x : ℤ, ∏ ω : Fin t → Bool,
              (star^[weight ω])
                (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))‖ :=
          Finset.sum_le_sum (fun h _ => norm_sum_le _ _)
      _ ≤ ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i},
          ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i}, Lp :=
          Finset.sum_le_sum (fun h _ => Finset.sum_le_sum (fun h' _ => hinner h h'))
      _ = (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
          ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * Lp) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
          (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * Lp := by ring
  have hnormA : ‖(∏ i : Fin t, (((Q i).card : ℂ))⁻¹)‖ = Pin := by
    rw [hPin, norm_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [norm_inv, Complex.norm_natCast]
  have hbox : boxNormPow t Q S f
      = ‖((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
          (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * Raw‖ := by
    rw [boxNormPow, boxSumPow, prodCubeSum_eq, hRaw]
  have hnormbox : ‖((S.card : ℂ))⁻¹ * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
        (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * Raw‖
      = ((S.card : ℝ))⁻¹ * Pin * Pin * ‖Raw‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, hnormA]
  have hPP : Pin * Pin * P * P ≤ 1 := by
    have hPP1 : Pin * P ≤ 1 := by
      rw [hPin, hP, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_one₀ (fun i _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)) (fun i _ => ?_)
      rcases eq_or_ne ((Q i).card) 0 with h | h
      · simp [h]
      · rw [inv_mul_cancel₀ (by exact_mod_cast h)]
    have hnn : 0 ≤ Pin * P := mul_nonneg hPinnn hPnn
    have h4 : (Pin * P) * (Pin * P) ≤ 1 * 1 := mul_le_mul hPP1 hPP1 hnn (by norm_num)
    nlinarith [h4]
  have hSinvnn : (0 : ℝ) ≤ ((S.card : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hlast : ((S.card : ℝ))⁻¹ * Pin * Pin * (P * P * Lp) ≤ ((S.card : ℝ))⁻¹ * Lp := by
    have h1 : ((S.card : ℝ))⁻¹ * Pin * Pin * (P * P * Lp)
        = ((S.card : ℝ))⁻¹ * ((Pin * Pin * P * P) * Lp) := by ring
    rw [h1]
    calc ((S.card : ℝ))⁻¹ * ((Pin * Pin * P * P) * Lp)
        ≤ ((S.card : ℝ))⁻¹ * (1 * Lp) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPP hLpnn) hSinvnn
      _ = ((S.card : ℝ))⁻¹ * Lp := by ring
  rw [hbox, hnormbox]
  calc ((S.card : ℝ))⁻¹ * Pin * Pin * ‖Raw‖
      ≤ ((S.card : ℝ))⁻¹ * Pin * Pin *
          ((Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) *
            (Fintype.card ((i : Fin t) → {x : ℤ // x ∈ Q i}) : ℝ) * Lp) := by
        have : (0 : ℝ) ≤ ((S.card : ℝ))⁻¹ * Pin * Pin :=
          mul_nonneg (mul_nonneg hSinvnn hPinnn) hPinnn
        exact mul_le_mul_of_nonneg_left hRaw_le this
    _ = ((S.card : ℝ))⁻¹ * Pin * Pin * (P * P * Lp) := by rw [hcardα]
    _ ≤ ((S.card : ℝ))⁻¹ * Lp := hlast

/-- For `1 ≤ L` the degenerate arithmetic progression `arithIcc 0 L` is the singleton `{0}`. -/
lemma arithIcc_zero_eq_singleton {L : ℕ} (hL : 1 ≤ L) : arithIcc 0 L = ({0} : Finset ℤ) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨n, -, hn⟩
    rw [← hn]
    simp
  · intro hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hL⟩, by simp⟩

end

end ZeroDirAux

/-- **The level-`s'` uniformity norm at the degenerate direction family `0[L] = {0}` dominates the
level-`t` box norm, for `t ≤ s'`.** -/
theorem boxNorm_zero_dir_le {t s' : ℕ} (hs' : 1 ≤ s') (hts : t ≤ s') :
    ∀ (N M₁ L : ℕ) (d : Fin t → ℤ) (δ : ℝ) (f : ℤ → ℂ),
      1 ≤ L → Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < δ →
      δ ≤ Work.Peluse.boxNorm t (fun i => Work.Peluse.arithIcc (d i) M₁) (Work.Peluse.symIcc N) f →
      δ ≤ Work.Peluse.uNorm s' (Work.Peluse.arithIcc 0 L) (Work.Peluse.symIcc N) f
:= by
  intro N M₁ L d δ f hL hsup hbd hδpos hδ
  have _ := hbd
  have hδ0 : 0 ≤ δ := le_of_lt hδpos
  have hNtne : (2 ^ t : ℕ) ≠ 0 := by positivity
  have hNsne : (2 ^ s' : ℕ) ≠ 0 := by positivity
  have hpowt : (1 : ℝ) / ((2 : ℝ) ^ t) = (((2 ^ t : ℕ) : ℝ))⁻¹ := by
    have h : ((2 : ℝ) ^ t) = ((2 ^ t : ℕ) : ℝ) := by rw [Nat.cast_pow]; norm_num
    rw [one_div, h]
  have hpows : (1 : ℝ) / ((2 : ℝ) ^ s') = (((2 ^ s' : ℕ) : ℝ))⁻¹ := by
    have h : ((2 : ℝ) ^ s') = ((2 ^ s' : ℕ) : ℝ) := by rw [Nat.cast_pow]; norm_num
    rw [one_div, h]
  have hvan : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 :=
    fun x hx => hsup x (Work.Peluse.Ulower.lt_natAbs_of_notMem_symIcc hx)
  have hfin : Work.Peluse.FinSuppZ f := Work.Peluse.FinSuppZ.of_supportIn hsup
  have hcardS : (0 : ℝ) < ((Work.Peluse.symIcc N).card : ℝ) := by
    have hpos : 0 < (Work.Peluse.symIcc N).card :=
      Finset.card_pos.mpr ⟨0, by simp [Work.Peluse.symIcc]⟩
    exact_mod_cast hpos
  -- ## Step 1: raise the box-norm lower bound to the `2 ^ t`-th power
  have hδ' : δ ≤ (Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (d i) M₁)
        (Work.Peluse.symIcc N) f) ^ (((2 ^ t : ℕ) : ℝ))⁻¹ := by
    have h := hδ
    unfold Work.Peluse.boxNorm at h
    rwa [hpowt] at h
  have hbnonneg : (0 : ℝ) ≤ Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (d i) M₁)
      (Work.Peluse.symIcc N) f := norm_nonneg _
  have hδ2 : δ ^ (2 ^ t)
      ≤ Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (d i) M₁)
          (Work.Peluse.symIcc N) f := by
    have h2 := pow_le_pow_left₀ hδ0 hδ' (2 ^ t)
    rw [Real.rpow_inv_natCast_pow hbnonneg hNtne] at h2
    exact h2
  -- ## Step 2: bound the box norm by the `2 ^ t`-th moment of `f`
  have hδ3 : δ ^ (2 ^ t)
      ≤ ((Work.Peluse.symIcc N).card : ℝ)⁻¹
        * ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ (2 ^ t) := by
    have h1 := ZeroDirAux.boxNormPow_le_normAvg t (fun i => Work.Peluse.arithIcc (d i) M₁)
      (Work.Peluse.symIcc N) f hfin
    rw [tsum_eq_sum (s := Work.Peluse.symIcc N) (f := fun x : ℤ => ‖f x‖ ^ (2 ^ t))
      (fun x hx => by rw [hvan x hx, norm_zero, zero_pow hNtne])] at h1
    exact hδ2.trans h1
  -- ## Step 3: the power-mean (Jensen) step
  have hjensen : (((Work.Peluse.symIcc N).card : ℝ)⁻¹
        * ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ (2 ^ t)) ^ (2 ^ (s' - t))
      ≤ ((Work.Peluse.symIcc N).card : ℝ)⁻¹
        * ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ (2 ^ s') := by
    have hq1 : 1 ≤ 2 ^ (s' - t) := Nat.one_le_two_pow
    have hj := Work.Peluse.Prop36SW.sum_pow_le_card_pow_mul_sum_pow (Work.Peluse.symIcc N)
      (fun x : ℤ => ‖f x‖ ^ (2 ^ t)) hq1 (fun x _ => pow_nonneg (norm_nonneg _) _)
    have hmul := mul_le_mul_of_nonneg_left hj
      (by positivity : (0 : ℝ) ≤ ((Work.Peluse.symIcc N).card : ℝ)⁻¹ ^ (2 ^ (s' - t)))
    have hpow : ∀ x : ℤ, (‖f x‖ ^ (2 ^ t)) ^ (2 ^ (s' - t)) = ‖f x‖ ^ (2 ^ s') := by
      intro x
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hts]
    have hsum : ∑ x ∈ Work.Peluse.symIcc N, (‖f x‖ ^ (2 ^ t)) ^ (2 ^ (s' - t))
        = ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ (2 ^ s') :=
      Finset.sum_congr rfl (fun x _ => hpow x)
    rw [hsum, ← mul_pow, ← mul_assoc,
      Work.Peluse.Prop36SW.inv_pow_mul_pow_sub hcardS hq1] at hmul
    exact hmul
  have hδ4 : δ ^ (2 ^ s')
      ≤ ((Work.Peluse.symIcc N).card : ℝ)⁻¹
        * ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ (2 ^ s') := by
    have h2 := pow_le_pow_left₀ (pow_nonneg hδ0 _) hδ3 (2 ^ (s' - t))
    have h3 : (δ ^ (2 ^ t)) ^ (2 ^ (s' - t)) = δ ^ (2 ^ s') := by
      rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hts]
    rw [h3] at h2
    exact h2.trans hjensen
  -- ## Step 4: identify the uniformity-norm power at the degenerate direction family
  have huNorm : Work.Peluse.uNormPow s' (Work.Peluse.arithIcc 0 L) (Work.Peluse.symIcc N) f
      = ((Work.Peluse.symIcc N).card : ℝ)⁻¹
        * ∑ x ∈ Work.Peluse.symIcc N, ‖f x‖ ^ (2 ^ s') := by
    rw [ZeroDirAux.arithIcc_zero_eq_singleton hL]
    exact Work.Peluse.Ulower.uNormPow_singleton_symIcc (t := s') hs' (c := 0) (L := N) (F := f)
      hvan
  have hroot : δ ≤ (Work.Peluse.uNormPow s' (Work.Peluse.arithIcc 0 L)
        (Work.Peluse.symIcc N) f) ^ (((2 ^ s' : ℕ) : ℝ))⁻¹ := by
    rw [huNorm, ← Real.pow_rpow_inv_natCast hδ0 hNsne]
    exact Real.rpow_le_rpow (pow_nonneg hδ0 _) hδ4 (by positivity)
  unfold Work.Peluse.uNorm
  rw [hpows]
  exact hroot

end Work.Prop36SW
