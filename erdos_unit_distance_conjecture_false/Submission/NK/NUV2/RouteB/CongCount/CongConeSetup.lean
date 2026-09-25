import Mathlib
import Submission.NK.NUV2.RouteB.CongCount.CongRayAux
import Submission.NK.NUV2.RouteB.RayCount.Defs
import Submission.NK.NUV2.RouteB.RayCount.mem_unitCongSubgroup_iff
import Submission.NK.NUV2.RouteB.Sharp.exists_mem_fractionalIdeal_congr
import Submission.NK.GlobalCFT.IdeleClassGroup.count_spanSingleton_eq

/-!
# The ray-class/lattice dictionary for the congruence subgroup `U(𝔪)`: setup

For a number field `K`, a modulus `𝔪` with `𝔪.pos = ∅` and a nonzero integral ideal `𝔡` coprime to
the support of `𝔪`, we fix the objects and the elementary facts used in the proof of
`NK.NUV2.RouteB.CongCount.torsionOrder_mul_rayClassCnt_eq_sum`.

* `magIdeal 𝔪 𝔡` — the (nonzero) fractional ideal `𝔪.ideal · 𝔡⁻¹`;
* `count_magIdeal` — its `q`-adic `count`s: `𝔪.exps q - count q 𝔡` (so `𝔪.exps q` at the support
  primes, by coprimality);
* `mem_iff_count_le` — the characterisation of membership in a nonzero fractional ideal by the
  `count`s: `x ∈ M ↔ ∀ q, count q M ≤ -log (v_q x)`;
* `mem_magIdeal_iff_mem_ideal` — an *algebraic integer* lies in `𝔪.ideal · 𝔡⁻¹` iff it lies in
  `𝔪.ideal`;
* `isCongElem_iff_sub_mem_magIdeal` — the *dictionary*: for `β ∈ 𝔡⁻¹` and a unit `u`, the element
  `uβ` is `≡ 1 (mod 𝔪)` iff `β - u⁻¹` lies in the lattice `𝔪.ideal · 𝔡⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors

noncomputable section

namespace NK.NUV2.RouteB.CongCount

open NK.NUV2.RouteB
open NK.GlobalCFT.IdeleClassGroup (count_spanSingleton_eq)

variable {K : Type} [Field K] [NumberField K]

/-! ## The lattice fractional ideal `𝔪.ideal · 𝔡⁻¹` -/

/-- The inverse of a unit of `𝓞 K`, viewed as an element of `K`. -/
def unitInvK (u : (𝓞 K)ˣ) : K := (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)

@[simp]
theorem unitInvK_def (u : (𝓞 K)ˣ) : unitInvK u = (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) := rfl

/-- The lattice `𝔪.ideal · 𝔡⁻¹` of the modulus `𝔪` and the base ideal `𝔡`, as a fractional ideal
(nonzero). -/
noncomputable def magIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Modulus.fracIdeal 𝔪 𝔡

@[simp]
theorem coe_magIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K)
        * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [magIdeal, Modulus.fracIdeal, Units.val_mul, Units.val_inv_eq_inv_val,
    FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0]
  rfl

/-- The base ideal is nonzero. -/
theorem baseIdeal_ne_zero (𝔡 : (Ideal (𝓞 K))⁰) : (𝔡 : Ideal (𝓞 K)) ≠ 0 :=
  mem_nonZeroDivisors_iff_ne_zero.mp 𝔡.2

theorem magIdeal_ne_zero (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
  Units.ne_zero _

/-! ## The `count`s of the modulus ideal and of the lattice -/

/-- The `q`-adic `count` of the integral ideal of the modulus is the exponent of the modulus. -/
theorem count_modulusIdeal (𝔪 : Modulus K) (q : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K q (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K) = (𝔪.exps q : ℤ) := by
  classical
  have hne : ∀ q' ∈ 𝔪.supportFinset,
      ((q'.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ (𝔪.exps q') ≠ 0 := by
    intro q' _
    exact pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr q'.ne_bot)
  rw [Modulus.ideal, NK.NUV2.RouteB.Sharp.coeIdeal_finset_prod]
  simp only [FractionalIdeal.coeIdeal_pow]
  rw [FractionalIdeal.count_prod K q 𝔪.supportFinset
    (fun q' => ((q'.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ (𝔪.exps q')) hne]
  have hkey : ∀ q' ∈ 𝔪.supportFinset,
      FractionalIdeal.count K q
        (((q'.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ (𝔪.exps q'))
      = if q' = q then (𝔪.exps q' : ℤ) else 0 := by
    intro q' _
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
    by_cases h : q' = q
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hkey,
    Finset.sum_ite_eq' 𝔪.supportFinset q fun q' => (𝔪.exps q' : ℤ)]
  by_cases hq : q ∈ 𝔪.supportFinset
  · rw [if_pos hq]
  · rw [if_neg hq, Modulus.exps_eq_zero_of_not_mem 𝔪 hq]
    simp

/-- A prime not dividing an integral ideal has `count` zero there. -/
theorem count_coe_eq_zero_of_not_dvd {𝔠 : Ideal (𝓞 K)} (h𝔠 : 𝔠 ≠ 0)
    {q : HeightOneSpectrum (𝓞 K)} (h : ¬ q.asIdeal ∣ 𝔠) :
    FractionalIdeal.count K q (𝔠 : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [FractionalIdeal.count_coe K q h𝔠, Ideal.count_associates_factors_eq h𝔠 q.isPrime q.ne_bot]
  have hz : Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors 𝔠) = 0 := by
    rw [Multiset.count_eq_zero]
    intro hmem
    exact h (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)
  rw [hz]
  norm_num

/-- The `count`s of the lattice `𝔪.ideal · 𝔡⁻¹`. -/
theorem count_magIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) (q : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K q
        ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (𝔪.exps q : ℤ) - FractionalIdeal.count K q
          ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [coe_magIdeal,
    FractionalIdeal.count_mul K q (FractionalIdeal.coeIdeal_ne_zero.mpr 𝔪.ideal_ne_zero)
      (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr (baseIdeal_ne_zero 𝔡))),
    FractionalIdeal.count_inv, count_modulusIdeal]
  ring

/-- The `count`s of the lattice at the support primes of the modulus, where `𝔡` is a unit. -/
theorem count_magIdeal_of_exp_ne_zero (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    {q : HeightOneSpectrum (𝓞 K)} (hq : 𝔪.exps q ≠ 0) :
    FractionalIdeal.count K q
        ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = (𝔪.exps q : ℤ) := by
  have h0 : FractionalIdeal.count K q ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
    count_coe_eq_zero_of_not_dvd (baseIdeal_ne_zero 𝔡) (hcop q hq)
  rw [count_magIdeal]
  rw [h0]
  ring

/-! ## Membership in a nonzero fractional ideal, by `count`s -/

/-- **Membership in a nonzero fractional ideal, read off from the `count`s.**  For `x ≠ 0`,
`x` lies in `M` iff the `count` of `M` at every prime is at most the order of vanishing of `x`. -/
theorem mem_iff_count_le {M : FractionalIdeal (𝓞 K)⁰ K} (hM : M ≠ 0) {x : K} (hx : x ≠ 0) :
    x ∈ M ↔ ∀ q : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K q M ≤ -((q.valuation K) x).log := by
  constructor
  · intro hxM q
    have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≤ M :=
      FractionalIdeal.spanSingleton_le_iff_mem.mpr hxM
    have h1 : FractionalIdeal.count K q M ≤
        FractionalIdeal.count K q (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) :=
      FractionalIdeal.count_mono K q (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) hle
    rwa [count_spanSingleton_eq q hx] at h1
  · intro h
    have hS : FractionalIdeal.spanSingleton (𝓞 K)⁰ x ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx
    have hN : M * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹ ≠ 0 :=
      mul_ne_zero hM (inv_ne_zero hS)
    have hcount : ∀ q : HeightOneSpectrum (𝓞 K),
        FractionalIdeal.count K q (M * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹) ≤ 0 := by
      intro q
      rw [FractionalIdeal.count_mul K q hM (inv_ne_zero hS), FractionalIdeal.count_inv,
        count_spanSingleton_eq q hx]
      have := h q
      linarith
    have hone : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤
        M * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹ :=
      NK.NUV2.RouteB.Sharp.one_le_of_count_nonpos hN hcount
    have hle := mul_le_mul_right hone (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)
    have hsimp : FractionalIdeal.spanSingleton (𝓞 K)⁰ x *
        (M * (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹) = M := by
      rw [mul_comm M (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)⁻¹, ← mul_assoc,
        mul_inv_cancel₀ hS, one_mul]
    rw [mul_one, hsimp] at hle
    exact FractionalIdeal.spanSingleton_le_iff_mem.mp hle

/-! ## The order of vanishing of an algebraic integer -/

/-- The `q`-adic order of vanishing of an algebraic integer, via its `q`-adic integer
valuation. -/
theorem log_valuation_algebraMap (q : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K) :
    ((q.valuation K) ((z : 𝓞 K) : K)).log = (q.intValuation z).log := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]

/-- An algebraic integer is integral at every finite place: its order of vanishing is
nonnegative. -/
theorem neg_log_valuation_nonneg (q : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K) :
    0 ≤ -((q.valuation K) ((z : 𝓞 K) : K)).log := by
  rw [log_valuation_algebraMap]
  rcases eq_or_ne (q.intValuation z) 0 with hz | hz
  · rw [hz, WithZero.log_zero]
    simp
  · have h1 : (q.intValuation z).log ≤ 0 := by
      have h := IsDedekindDomain.HeightOneSpectrum.intValuation_le_one q z
      have h2 : (q.intValuation z).log ≤ (WithZero.exp (0 : ℤ)).log :=
        (WithZero.log_le_log hz (WithZero.exp_ne_zero (a := (0 : ℤ)))).mpr (by
          simpa using h)
      rwa [WithZero.log_exp] at h2
    linarith

/-- If `z ∈ q ^ n` then the order of vanishing of `z` at `q` is at least `n`. -/
theorem le_neg_log_valuation_of_mem_pow (q : HeightOneSpectrum (𝓞 K)) {z : 𝓞 K}
    (hz : z ≠ 0) (n : ℕ) (h : z ∈ q.asIdeal ^ n) :
    (n : ℤ) ≤ -((q.valuation K) ((z : 𝓞 K) : K)).log := by
  rw [log_valuation_algebraMap]
  have h1 := (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem q z n).mpr h
  have hz' : q.intValuation z ≠ 0 := q.intValuation_ne_zero z hz
  have h2 : (q.intValuation z).log ≤ (-(n : ℤ)) := by
    have h3 := (WithZero.log_le_log hz' (WithZero.exp_ne_zero (a := (-(n : ℤ))))).mpr h1
    rwa [WithZero.log_exp] at h3
  linarith

/-! ## The lattice, the modulus ideal and the integral ideals -/

/-- An integral ideal, as a fractional ideal, is at most one. -/
theorem coeIdeal_le_one (𝔠 : Ideal (𝓞 K)) :
    ((𝔠 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 := by
  have h : ((𝔠 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≤
      ((⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr le_top
  simpa using h

/-- The integral ideal of the modulus, as a fractional ideal, is at most one. -/
theorem modulusIdeal_le_one (𝔪 : Modulus K) :
    (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K) ≤ 1 :=
  coeIdeal_le_one 𝔪.ideal

/-- The inverse of a nonzero integral ideal contains one. -/
theorem one_le_inv_coeIdeal (𝔠 : Ideal (𝓞 K)) (h𝔠 : 𝔠 ≠ 0) :
    (1 : FractionalIdeal (𝓞 K)⁰ K) ≤
      ((𝔠 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  refine NK.NUV2.RouteB.Sharp.one_le_of_count_nonpos
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr h𝔠)) (fun q => ?_)
  rw [FractionalIdeal.count_inv]
  exact neg_nonpos.mpr (FractionalIdeal.count_coe_nonneg K q 𝔠)

/-- The lattice is contained in `𝔡⁻¹`. -/
theorem magIdeal_le_inv_base (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      ≤ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coe_magIdeal]
  calc (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K)
        * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      ≤ 1 * ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
        mul_le_mul_left (modulusIdeal_le_one 𝔪) _
    _ = _ := one_mul _

/-- The lattice contains the modulus ideal. -/
theorem modulusIdeal_le_magIdeal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰) :
    (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K)
      ≤ ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  have h := mul_le_mul_right (one_le_inv_coeIdeal (𝔡 : Ideal (𝓞 K)) (baseIdeal_ne_zero 𝔡))
    (𝔪.ideal : FractionalIdeal (𝓞 K)⁰ K)
  rw [mul_one] at h
  rw [coe_magIdeal]
  exact h

/-- The inverse of an integral ideal `𝔡`, as a fractional ideal. -/
def invBaseFrac (𝔡 : (Ideal (𝓞 K))⁰) : FractionalIdeal (𝓞 K)⁰ K :=
  ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹

@[simp]
theorem mem_invBaseFrac_iff {𝔡 : (Ideal (𝓞 K))⁰} {x : K} :
    x ∈ invBaseFrac 𝔡 ↔ x ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
  Iff.rfl

/-- The inverse of a nonzero integral ideal is an additive subgroup. -/
theorem add_mem_inv_coeIdeal (𝔡 : (Ideal (𝓞 K))⁰) {x y : K}
    (hx : x ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    (hy : y ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    x + y ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
  Submodule.add_mem (invBaseFrac 𝔡 : Submodule (𝓞 K) K) hx hy

/-- Membership in the lattice implies membership in `𝔡⁻¹`. -/
theorem mem_inv_base_of_mem_magSet {𝔪 : Modulus K} {𝔡 : (Ideal (𝓞 K))⁰} {x : K}
    (hx : x ∈ ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
    x ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
  (magIdeal_le_inv_base 𝔪 𝔡) hx

/-- **An algebraic integer lies in `𝔪.ideal · 𝔡⁻¹` iff it lies in `𝔪.ideal`.** -/
theorem mem_magIdeal_iff_mem_ideal (𝔪 : Modulus K) (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (z : 𝓞 K) :
    ((z : K) ∈ ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K))
      ↔ z ∈ 𝔪.ideal := by
  classical
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [RingOfIntegers.coe_eq_algebraMap, map_zero]
    constructor <;> intro _ <;> exact Submodule.zero_mem _
  have hz' : ((z : 𝓞 K) : K) ≠ 0 := by simpa using hz
  constructor
  · -- `z ∈ M` ⟹ `z ∈ 𝔪.ideal`
    intro hzM
    have hspan : Ideal.span {z} ≤ 𝔪.ideal := by
      refine NK.NUV2.RouteB.Sharp.ideal_le_of_count_le (I := Ideal.span {z}) (J := 𝔪.ideal)
        (by simpa [Ideal.span_singleton_eq_bot] using hz) 𝔪.ideal_ne_zero (fun v => ?_)
      rw [FractionalIdeal.coeIdeal_span_singleton, count_modulusIdeal,
        count_spanSingleton_eq v hz']
      by_cases hv : 𝔪.exps v ≠ 0
      · have h := (mem_iff_count_le (magIdeal_ne_zero 𝔪 𝔡) hz').mp hzM v
        rw [count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hv] at h
        exact h
      · rw [show 𝔪.exps v = 0 from not_not.mp hv, Nat.cast_zero]
        exact neg_log_valuation_nonneg v z
    exact hspan (Ideal.mem_span_singleton_self z)
  · -- `z ∈ 𝔪.ideal` ⟹ `z ∈ M`
    intro hzI
    refine (mem_iff_count_le (magIdeal_ne_zero 𝔪 𝔡) hz').mpr (fun v => ?_)
    by_cases hv : 𝔪.exps v ≠ 0
    · rw [count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hv]
      have hmem : z ∈ v.asIdeal ^ (𝔪.exps v) :=
        (NK.NUV2.RouteB.Sharp.finset_prod_le_pow_of_mem 𝔪.exps 𝔪.supportFinset
          (𝔪.mem_supportFinset hv)) (by rw [← Modulus.ideal]; exact hzI)
      exact le_neg_log_valuation_of_mem_pow v hz (𝔪.exps v) hmem
    · have hM : FractionalIdeal.count K v
          ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
          = -FractionalIdeal.count K v ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
        rw [count_magIdeal, show 𝔪.exps v = 0 from not_not.mp hv, Nat.cast_zero, zero_sub]
      rw [hM]
      exact le_trans (neg_le_neg (FractionalIdeal.count_coe_nonneg K v (𝔡 : Ideal (𝓞 K))))
        (neg_log_valuation_nonneg v z)

/-! ## The dictionary: congruence modulo `𝔪` versus membership in `𝔪.ideal · 𝔡⁻¹` -/

/-- One is an element of `𝔡⁻¹` for a nonzero integral ideal `𝔡`. -/
theorem one_mem_inv_coeIdeal (𝔡 : (Ideal (𝓞 K))⁰) :
    (1 : K) ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤
      ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
    one_le_inv_coeIdeal (𝔡 : Ideal (𝓞 K)) (baseIdeal_ne_zero 𝔡)
  exact h1 (by rw [FractionalIdeal.mem_one_iff]; exact ⟨1, map_one _⟩)

/-- Multiplication by a unit of `𝓞 K` preserves membership in a fractional ideal. -/
theorem unit_mul_mem_iff (M : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ) {y : K} :
    (((u : 𝓞 K) : K) * y ∈ M) ↔ y ∈ M := by
  constructor
  · intro hy
    have hy' : ((u : 𝓞 K)) • y ∈ M := by simpa [Algebra.smul_def] using hy
    have h1 : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • (((u : 𝓞 K)) • y) ∈ M :=
      Submodule.smul_mem (M : Submodule (𝓞 K) K) ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) hy'
    have h2 : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) • (((u : 𝓞 K)) • y) = y := by
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rwa [h2] at h1
  · intro hy
    have h1 : ((u : 𝓞 K)) • y ∈ M :=
      Submodule.smul_mem (M : Submodule (𝓞 K) K) ((u : 𝓞 K)) hy
    simpa [Algebra.smul_def] using h1

/-- **The dictionary.**  Let `𝔪` be a modulus with `𝔪.pos = ∅`, let `𝔡 ≠ 0` be an integral ideal
coprime to the support of `𝔪`, let `u` be a unit of `𝓞 K` and `β ∈ 𝔡⁻¹`.  Then `u · β` is
`≡ 1 (mod 𝔪)` (in the sense of `IsCongElem`) if and only if `β - u⁻¹` lies in the fractional ideal
`𝔪.ideal · 𝔡⁻¹`.  This is the correspondence between the congruence condition and the lattice
cosets used for the ray-class/lattice dictionary. -/
theorem isCongElem_mul_unit_iff_sub_mem_magIdeal (𝔪 : Modulus K) (hpos : 𝔪.pos = ∅)
    (𝔡 : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q : HeightOneSpectrum (𝓞 K), 𝔪.exps q ≠ 0 → ¬ q.asIdeal ∣ (𝔡 : Ideal (𝓞 K)))
    (u : (𝓞 K)ˣ) {β : K}
    (hβ : β ∈ ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) :
    IsCongElem K 𝔪 (((u : 𝓞 K) : K) * β) ↔
      β - (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) ∈
        ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
  set 𝔡I : FractionalIdeal (𝓞 K)⁰ K := ((𝔡 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) with h𝔡I
  set M : FractionalIdeal (𝓞 K)⁰ K :=
    ((magIdeal 𝔪 𝔡 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) with hM
  have hM0 : M ≠ 0 := magIdeal_ne_zero 𝔪 𝔡
  have hstep1 : (β - (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) ∈ M) ↔
      (((u : 𝓞 K) : K) * β - 1) ∈ M := by
    have hu : ((u : 𝓞 K) : K) ≠ 0 :=
      fun h => Units.ne_zero u (RingOfIntegers.coe_injective h)
    have hEq : ((u : 𝓞 K) : K) * β - 1
        = ((u : 𝓞 K) : K) * (β - (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) := by
      rw [mul_sub]
      congr 1
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [hEq]
    exact (unit_mul_mem_iff M u).symm
  -- `u β - 1` lies in `𝔡⁻¹`
  have hx_inv : (((u : 𝓞 K) : K) * β - 1) ∈ 𝔡I⁻¹ := by
    have huβ : ((u : 𝓞 K) : K) * β ∈ 𝔡I⁻¹ := by
      have h : ((u : 𝓞 K)) • β ∈ (((𝔡I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
        Submodule.smul_mem (((𝔡I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
          ((u : 𝓞 K)) hβ
      simpa [Algebra.smul_def] using h
    exact Submodule.sub_mem (((𝔡I)⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) huβ
      (one_mem_inv_coeIdeal 𝔡)
  constructor
  · -- `≡ 1` modulo `𝔪` implies membership in the lattice
    intro hcong
    rw [hstep1]
    by_cases hx : ((u : 𝓞 K) : K) * β - 1 = 0
    · rw [hx]
      exact Submodule.zero_mem (M : Submodule (𝓞 K) K)
    · refine (mem_iff_count_le hM0 hx).mpr (fun q => ?_)
      by_cases hq : 𝔪.exps q ≠ 0
      · rw [count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hq]
        have hval : (q.valuation K) (((u : 𝓞 K) : K) * β - 1)
            ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
          have h := hcong.1 q hq
          rwa [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq] at h
        have hne : (q.valuation K) (((u : 𝓞 K) : K) * β - 1) ≠ 0 :=
          (Valuation.ne_zero_iff _).mpr hx
        have hlog : ((q.valuation K) (((u : 𝓞 K) : K) * β - 1)).log ≤ -(𝔪.exps q : ℤ) := by
          have h := (WithZero.log_le_log hne
            (WithZero.exp_ne_zero (a := (-(𝔪.exps q : ℤ))))).mpr hval
          rwa [WithZero.log_exp] at h
        linarith
      · rw [count_magIdeal, show 𝔪.exps q = 0 from not_not.mp hq, Nat.cast_zero, zero_sub]
        have h1 : FractionalIdeal.count K q (𝔡I⁻¹)
            ≤ FractionalIdeal.count K q
              (FractionalIdeal.spanSingleton (𝓞 K)⁰ (((u : 𝓞 K) : K) * β - 1)) :=
          FractionalIdeal.count_mono K q
            (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
            (FractionalIdeal.spanSingleton_le_iff_mem.mpr hx_inv)
        rw [FractionalIdeal.count_inv, count_spanSingleton_eq q hx] at h1
        simpa using h1
  · -- membership in the lattice implies `≡ 1` modulo `𝔪`
    intro hmem
    have hxmem : (((u : 𝓞 K) : K) * β - 1) ∈ M := hstep1.mp hmem
    refine ⟨fun q hq => ?_, fun w hw hwpos => ?_⟩
    · by_cases hx : ((u : 𝓞 K) : K) * β - 1 = 0
      · rw [hx, map_zero]
        simp
      · have h := (mem_iff_count_le hM0 hx).mp hxmem q
        rw [count_magIdeal_of_exp_ne_zero 𝔪 𝔡 hcop hq] at h
        have hne : (q.valuation K) (((u : 𝓞 K) : K) * β - 1) ≠ 0 :=
          (Valuation.ne_zero_iff _).mpr hx
        have hlog : ((q.valuation K) (((u : 𝓞 K) : K) * β - 1)).log ≤ -(𝔪.exps q : ℤ) := by
          linarith
        have hval : (q.valuation K) (((u : 𝓞 K) : K) * β - 1)
            ≤ WithZero.exp (-(𝔪.exps q : ℤ)) := by
          rw [← WithZero.exp_log hne]
          exact WithZero.exp_le_exp.mpr hlog
        rwa [Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq]
    · rw [hpos] at hwpos
      exact absurd hwpos (Set.notMem_empty w)

end NK.NUV2.RouteB.CongCount
