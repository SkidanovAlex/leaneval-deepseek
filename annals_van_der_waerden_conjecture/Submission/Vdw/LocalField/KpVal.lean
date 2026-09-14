import Mathlib
import Submission.Vdw.LocalField.WildDifferent
import Submission.Vdw.LocalField.ResidueInstances

open Classical
open IsLocalRing
open scoped NumberField WithZero Valued

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# KpVal — the 𝔪-adic filtration degree (DVR exponent) on `kpInt p P`

For the completed valuation ring `kpInt p P` of `K_P = kpAdic p P`
(𝔪 := maximal ideal, ϖ := uniformizer, 𝔪^k = (ϖ^k)), every nonzero
`x : kpInt` has a DVR decomposition `x = u·ϖ^m` with `u` a unit;
`kpVal p P x` is that exponent `m` (`kpVal 0 = 0`).  The API:

* `kpVal_spec` — the decomposition `∃ u, x = u·ϖ^(kpVal x)` for `x ≠ 0`;
* `kpVal_eq_of_unit_mul_pow` — uniqueness: any unit-factorization with
  exponent `m` forces `kpVal x = m`; `kpVal_unit`, `kpVal_uniformizer_pow`,
  `kpVal_unit_mul_pow` are the immediate consequences;
* `kpVal_mul` — additivity `kpVal (x·y) = kpVal x + kpVal y`;
* `kpVal_eq_iff_exact` — `x ∈ 𝔪^m \ 𝔪^(m+1) ↔ x ≠ 0 ∧ kpVal x = m`;
* integer values: `kpVal_natCast_eq_mul_ramIdx` — `kpVal (n : kpInt) =
  e · padicValNat p n` (`e := P.ramificationIdx ℤ`): the valuation of an
  integer is an `e`-multiple (the completed tower has ramification `e`,
  `p = unit·ϖ^e`).

This is the valuation infrastructure of the WildDifferent (e) sub-stone
(the derivative bound `v_P(f_ϖ'(ϖ)) ≤ e·v_p(e)+e−1`): the term-valuation
congruence `v(i·c_i·ϖ^{i−1}) ≡ (i−1) mod e` needs `kpVal` of the integer
coefficients (`∈ e·ℤ`), of the uniformizer powers (`= i−1`), and of the
coefficient witnesses (`∈ e·ℤ` — the restriction of the valuation to `W`,
proved in `OW_witness_kpVal_dvd` of Eisenstein.lean).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The 𝔪-adic filtration degree (DVR exponent) of an element of the
valuation ring `kpInt p P`: `kpVal x = m` when `x = u·ϖ^m` for a unit
`u` (and `kpVal 0 = 0`). -/
noncomputable def kpVal (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : kpInt p P) : ℕ :=
  if hx : x = 0 then 0 else
    Classical.choose (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := x) hx (uniformizer_irreducible p P))

/-- The unit factor in the DVR decomposition of a nonzero element. -/
noncomputable def kpUnit (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : kpInt p P) (hx : x ≠ 0) : (kpInt p P)ˣ :=
  Classical.choose (Classical.choose_spec
    (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := x) hx (uniformizer_irreducible p P)))

/-- The DVR decomposition: for `x ≠ 0`, `x = (kpUnit x)·ϖ^(kpVal x)`. -/
lemma kpVal_spec (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : kpInt p P) (hx : x ≠ 0) :
    x = (kpUnit p P x hx : kpInt p P) * uniformizer p P ^ kpVal p P x := by
  classical
  dsimp [kpVal]
  rw [dif_neg hx]
  exact Classical.choose_spec (Classical.choose_spec
    (IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := x) hx (uniformizer_irreducible p P)))

/-- The uniformizer is nonzero in any power (domain). -/
lemma uniformizer_pow_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (k : ℕ) :
    uniformizer p P ^ k ≠ 0 :=
  pow_ne_zero k (uniformizer_ne_zero p P)

/-- Nonzero natural numbers are nonzero in `kpInt` (the ring has
characteristic 0). -/
lemma natCast_ne_zero_kpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) (hn : n ≠ 0) : (n : kpInt p P) ≠ 0 := by
  classical
  intro hz
  have hpx : algebraMap (QpInt p) (kpInt p P) ((n : ℤ) : QpInt p) =
      ((n : ℤ) : kpInt p P) := algebraMap_QpInt_int p P (n : ℤ)
  have hz0 : algebraMap (QpInt p) (kpInt p P) ((n : ℤ) : QpInt p) = 0 := by
    rw [hpx]
    simpa using hz
  have hz0' : algebraMap (QpInt p) (kpInt p P) ((n : ℤ) : QpInt p) =
      algebraMap (QpInt p) (kpInt p P) (0 : QpInt p) := by
    simpa using hz0
  have hq0 : ((n : ℤ) : QpInt p) = 0 := algebraMap_qpInt_injective p P hz0'
  have hq0' : ((n : ℤ) : QpAdic p) = 0 := congrArg (fun z : QpInt p => (z : QpAdic p)) hq0
  have hinj : Function.Injective (algebraMap ℚ (QpAdic p)) := RingHom.injective _
  have hq0'' : (n : QpAdic p) = 0 := by
    simpa using hq0'
  have hq : (n : ℚ) = 0 := by
    apply hinj
    have hcast : (n : QpAdic p) = algebraMap ℚ (QpAdic p) (n : ℚ) := by
      exact (map_natCast (algebraMap ℚ (QpAdic p)) n).symm
    rw [← hcast]
    exact hq0''
  exact (Rat.cast_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) hq

/-- Uniqueness of the DVR exponent: if `x ≠ 0` and `x = u·ϖ^m` for a
unit `u`, then `kpVal x = m`. -/
lemma kpVal_eq_of_unit_mul_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : kpInt p P) (hx : x ≠ 0) (u : (kpInt p P)ˣ) (m : ℕ)
    (h : x = (u : kpInt p P) * uniformizer p P ^ m) : kpVal p P x = m := by
  classical
  have hv := kpVal_spec p P x hx
  let v : (kpInt p P)ˣ := kpUnit p P x hx
  have hEq : (v : kpInt p P) * uniformizer p P ^ kpVal p P x
      = (u : kpInt p P) * uniformizer p P ^ m := by
    -- hv : x = (v : kpInt) * ϖ^(kpVal x)
    simpa [v] using hv.symm.trans h
  by_contra hne
  have hkm : kpVal p P x ≠ m := by
    intro hk
    exact hne hk
  rcases Nat.lt_or_gt_of_ne hkm with hklt | hmlt
  · -- kpVal x < m: cancel ϖ^(kpVal x): v = u·ϖ^(m−k) ∈ 𝔪 — contradiction (v a unit)
    have hre : (u : kpInt p P) * uniformizer p P ^ m
        = ((u : kpInt p P) * uniformizer p P ^ (m - kpVal p P x)) * uniformizer p P ^ kpVal p P x := by
      rw [mul_assoc]
      congr 1
      rw [← pow_add]
      congr 1
      omega
    have hEq1 : (v : kpInt p P) * uniformizer p P ^ kpVal p P x
        = ((u : kpInt p P) * uniformizer p P ^ (m - kpVal p P x)) * uniformizer p P ^ kpVal p P x :=
      hEq.trans hre
    have hEq'' : uniformizer p P ^ kpVal p P x * (v : kpInt p P)
        = uniformizer p P ^ kpVal p P x * ((u : kpInt p P) * uniformizer p P ^ (m - kpVal p P x)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hEq1
    have hcancel : (v : kpInt p P) = (u : kpInt p P) * uniformizer p P ^ (m - kpVal p P x) :=
      mul_left_cancel₀ (uniformizer_pow_ne_zero p P (kpVal p P x)) hEq''
    have hpos : 0 < m - kpVal p P x := Nat.sub_pos_of_lt hklt
    have hnot : (v : kpInt p P) ∉ maximalIdeal (kpInt p P) := by
      rw [IsLocalRing.mem_maximalIdeal]
      rw [mem_nonunits_iff]
      exact not_not.mpr (Units.isUnit v)
    apply hnot
    rw [hcancel]
    refine Ideal.mul_mem_left (maximalIdeal (kpInt p P)) (u : kpInt p P) ?_
    have hϖm : uniformizer p P ^ (m - kpVal p P x) ∈ maximalIdeal (kpInt p P) := by
      rw [show m - kpVal p P x = (m - kpVal p P x - 1) + 1 by omega]
      rw [pow_succ]
      exact Ideal.mul_mem_left (maximalIdeal (kpInt p P)) (uniformizer p P ^ (m - kpVal p P x - 1))
        (uniformizer_mem_maximalIdeal p P)
    exact hϖm
  · -- m < kpVal x: cancel ϖ^m: u = v·ϖ^(kpVal x − m) ∈ 𝔪 — contradiction
    have hre : (v : kpInt p P) * uniformizer p P ^ kpVal p P x
        = ((v : kpInt p P) * uniformizer p P ^ (kpVal p P x - m)) * uniformizer p P ^ m := by
      rw [mul_assoc]
      congr 1
      rw [← pow_add]
      congr 1
      omega
    have hEq1 : ((v : kpInt p P) * uniformizer p P ^ (kpVal p P x - m)) * uniformizer p P ^ m
        = (u : kpInt p P) * uniformizer p P ^ m :=
      hre.symm.trans hEq
    have hEq'' : uniformizer p P ^ m * ((v : kpInt p P) * uniformizer p P ^ (kpVal p P x - m))
        = uniformizer p P ^ m * (u : kpInt p P) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hEq1
    have hcancel : (v : kpInt p P) * uniformizer p P ^ (kpVal p P x - m) = (u : kpInt p P) :=
      mul_left_cancel₀ (uniformizer_pow_ne_zero p P m) hEq''
    have hpos : 0 < kpVal p P x - m := Nat.sub_pos_of_lt hmlt
    have hnot : (u : kpInt p P) ∉ maximalIdeal (kpInt p P) := by
      rw [IsLocalRing.mem_maximalIdeal]
      rw [mem_nonunits_iff]
      exact not_not.mpr (Units.isUnit u)
    apply hnot
    rw [← hcancel]
    refine Ideal.mul_mem_left (maximalIdeal (kpInt p P)) (v : kpInt p P) ?_
    have hϖm : uniformizer p P ^ (kpVal p P x - m) ∈ maximalIdeal (kpInt p P) := by
      rw [show kpVal p P x - m = (kpVal p P x - m - 1) + 1 by omega]
      rw [pow_succ]
      exact Ideal.mul_mem_left (maximalIdeal (kpInt p P)) (uniformizer p P ^ (kpVal p P x - m - 1))
        (uniformizer_mem_maximalIdeal p P)
    exact hϖm

/-- Units have value 0. -/
lemma kpVal_unit (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (u : (kpInt p P)ˣ) : kpVal p P (u : kpInt p P) = 0 := by
  classical
  refine kpVal_eq_of_unit_mul_pow p P (u : kpInt p P) (Units.ne_zero u) u 0 ?_
  rw [pow_zero, mul_one]

/-- Uniformizer powers have value equal to the exponent. -/
lemma kpVal_uniformizer_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (k : ℕ) :
    kpVal p P (uniformizer p P ^ k) = k := by
  classical
  refine kpVal_eq_of_unit_mul_pow p P (uniformizer p P ^ k) (uniformizer_pow_ne_zero p P k) 1 k ?_
  simp

/-- A unit times a uniformizer power has value equal to the exponent. -/
lemma kpVal_unit_mul_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (u : (kpInt p P)ˣ) (k : ℕ) :
    kpVal p P ((u : kpInt p P) * uniformizer p P ^ k) = k := by
  classical
  refine kpVal_eq_of_unit_mul_pow p P ((u : kpInt p P) * uniformizer p P ^ k) ?_ u k ?_
  · exact mul_ne_zero (Units.ne_zero u) (uniformizer_pow_ne_zero p P k)
  · rfl

/-- Additivity: `kpVal (x·y) = kpVal x + kpVal y` for nonzero `x, y`. -/
lemma kpVal_mul (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x y : kpInt p P) (hx : x ≠ 0) (hy : y ≠ 0) :
    kpVal p P (x * y) = kpVal p P x + kpVal p P y := by
  classical
  have hu := kpVal_spec p P x hx
  have hv := kpVal_spec p P y hy
  let u : (kpInt p P)ˣ := kpUnit p P x hx
  let v : (kpInt p P)ˣ := kpUnit p P y hy
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx hy
  have hpow : uniformizer p P ^ kpVal p P x * uniformizer p P ^ kpVal p P y
      = uniformizer p P ^ (kpVal p P x + kpVal p P y) := by
    exact (pow_add (uniformizer p P) (kpVal p P x) (kpVal p P y)).symm
  have hxy0' : ((u : kpInt p P) * uniformizer p P ^ kpVal p P x)
          * ((v : kpInt p P) * uniformizer p P ^ kpVal p P y)
        = ((u * v : (kpInt p P)ˣ) : kpInt p P)
            * uniformizer p P ^ (kpVal p P x + kpVal p P y) := by
    rw [← hpow]
    simp [Units.val_mul, mul_assoc, mul_left_comm]
  have hxy : x * y = ((u * v : (kpInt p P)ˣ) : kpInt p P)
      * uniformizer p P ^ (kpVal p P x + kpVal p P y) := by
    conv_lhs =>
      rw [show x = (u : kpInt p P) * uniformizer p P ^ kpVal p P x by simpa [u] using hu,
          show y = (v : kpInt p P) * uniformizer p P ^ kpVal p P y by simpa [v] using hv]
    exact hxy0'
  exact kpVal_eq_of_unit_mul_pow p P (x * y) hxy0 (u * v) (kpVal p P x + kpVal p P y) hxy

/-- Membership in the maximal ideal is `1 ≤ kpVal x` (for `x ≠ 0`):
a nonzero element of the DVR lies in 𝔪 exactly when its value is positive.
-/
lemma mem_maximalIdeal_iff_one_le_kpVal (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : kpInt p P) (hx : x ≠ 0) : x ∈ maximalIdeal (kpInt p P) ↔ 1 ≤ kpVal p P x := by
  classical
  set m : ℕ := kpVal p P x with hm
  have hspec : x = (kpUnit p P x hx : kpInt p P) * uniformizer p P ^ m := by
    simpa [← hm] using (kpVal_spec p P x hx)
  constructor
  · intro hxmem
    by_contra hle
    have hm0 : m = 0 := by omega
    rw [hm0] at hspec
    have hxunit : IsUnit x := by
      rw [hspec]
      simp
    have hxnot : x ∉ maximalIdeal (kpInt p P) := by
      rw [IsLocalRing.mem_maximalIdeal]
      rw [mem_nonunits_iff]
      exact not_not.mpr hxunit
    exact hxnot hxmem
  · intro hle
    have hmem : (kpUnit p P x hx : kpInt p P) * uniformizer p P ^ m
        ∈ (maximalIdeal (kpInt p P)) ^ m :=
      unit_mul_uniformizer_pow_mem_maximalIdeal_pow p P (kpUnit p P x hx) m
    have hsub : (maximalIdeal (kpInt p P)) ^ m ≤ maximalIdeal (kpInt p P) := by
      convert Ideal.pow_le_pow_right hle using 1
      simp
    rw [hspec]
    exact hsub hmem

lemma kpVal_natCast_p (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    kpVal p P (p : kpInt p P) = P.ramificationIdx ℤ := by
  classical
  rcases int_uniformizer_eq p P with ⟨u, hu⟩
  exact kpVal_eq_of_unit_mul_pow p P (p : kpInt p P) (int_p_ne_zero p P) u (P.ramificationIdx ℤ) hu


/-- An integer not divisible by `p` is a unit of `kpInt` (its residue in the
characteristic-`p` residue field is nonzero). -/
lemma natCast_unit_of_not_dvd (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) (hpn : ¬ p ∣ n) : IsUnit (n : kpInt p P) := by
  classical
  have hnot : (n : kpInt p P) ∉ maximalIdeal (kpInt p P) := by
    intro hmem
    have hmk : Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (n : kpInt p P) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal (kpInt p P))).mpr hmem
    have hnκ : (n : kpInt p P ⧸ maximalIdeal (kpInt p P)) = 0 := by
      simpa using hmk
    exact hpn ((CharP.cast_eq_zero_iff (kpInt p P ⧸ maximalIdeal (kpInt p P)) p n).mp hnκ)
  rw [IsLocalRing.mem_maximalIdeal] at hnot
  rw [mem_nonunits_iff] at hnot
  exact not_not.mp hnot

/-- An integer coprime to `p` has value 0 in `kpInt`. -/
lemma kpVal_natCast_eq_zero_of_not_dvd (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) (hpn : ¬ p ∣ n) : kpVal p P (n : kpInt p P) = 0 := by
  classical
  rcases natCast_unit_of_not_dvd p P n hpn with ⟨u, hu⟩
  -- hu : (u : kpInt) = (n : kpInt)
  rw [← hu]
  exact kpVal_unit p P u

/-- The integer `p^a` has value `a·e` in `kpInt`. -/
lemma kpVal_natCast_pow_p (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (a : ℕ) : kpVal p P ((p ^ a : ℕ) : kpInt p P) = P.ramificationIdx ℤ * a := by
  classical
  induction a with
  | zero =>
      -- (1 : kpInt) is the unit 1: kpVal = 0
      simpa using (kpVal_unit p P 1)
  | succ a ih =>
      have hpown : p ^ (a + 1) = p ^ a * p := by
        rw [pow_succ]
      have h : ((p ^ (a + 1) : ℕ) : kpInt p P) =
          ((p ^ a : ℕ) : kpInt p P) * (p : kpInt p P) := by
        rw [hpown, Nat.cast_mul]
      rw [h]
      have hp0 : (p ^ a : ℕ) ≠ 0 := pow_ne_zero a (Nat.Prime.ne_zero (Fact.out (p := Nat.Prime p)))
      rw [kpVal_mul p P ((p ^ a : ℕ) : kpInt p P) (p : kpInt p P)
        (natCast_ne_zero_kpInt p P (p ^ a) hp0) (int_p_ne_zero p P)]
      rw [kpVal_natCast_p p P]
      rw [ih]
      ring

/-- Split a nonzero natural into its `p`-power part and the rest:
`n = p^(padicValNat p n) · m` with `p ∤ m`. -/
lemma padicValNat_decomp (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ} (hn : n ≠ 0) :
    ∃ m : ℕ, n = p ^ padicValNat p n * m ∧ ¬ p ∣ m := by
  classical
  let a : ℕ := padicValNat p n
  refine ⟨n / p ^ a, ?_, ?_⟩
  · have hdiv : p ^ a ∣ n := (padicValNat_dvd_iff a n).mpr (by right; rfl)
    exact (Nat.mul_div_cancel' hdiv).symm
  · intro hpm
    rcases hpm with ⟨m', hm'⟩
    have hdiv' : p ^ (a + 1) ∣ n := by
      refine ⟨m', ?_⟩
      have hmain : n = p ^ (a + 1) * m' := by
        calc
          n = p ^ a * (n / p ^ a) := by
                have hdiv : p ^ a ∣ n := (padicValNat_dvd_iff a n).mpr (by right; rfl)
                exact (Nat.mul_div_cancel' hdiv).symm
          _ = p ^ a * (p * m') := by rw [hm']
          _ = p ^ a * p * m' := by rw [mul_assoc]
          _ = p ^ (a + 1) * m' := by rw [pow_succ]
      simpa using hmain
    have hle : a + 1 ≤ padicValNat p n :=
      ((padicValNat_dvd_iff (a + 1) n).mp hdiv').resolve_left hn
    omega

/-- `padicValNat p (p^b · m) = b` when `p ∤ m`. -/
lemma padicValNat_pow_mul_of_not_dvd (p : ℕ) [Fact (Nat.Prime p)] {b m : ℕ}
    (hpm : ¬ p ∣ m) : padicValNat p (p ^ b * m) = b := by
  classical
  have hb : p ^ b ≠ 0 := pow_ne_zero b (Nat.Prime.ne_zero (Fact.out (p := Nat.Prime p)))
  have hx : p ^ b * m ≠ 0 := by
    intro hz
    exact hpm ⟨0, by
      have hz' : m * p ^ b = 0 := by rwa [mul_comm] at hz
      have hm0 : m = 0 := eq_zero_of_ne_zero_of_mul_right_eq_zero hb hz'
      rw [hm0]
      simp⟩
  have hle : b ≤ padicValNat p (p ^ b * m) := by
    exact ((padicValNat_dvd_iff b (p ^ b * m)).mp
      (⟨m, by rw [mul_comm]⟩ : p ^ b ∣ p ^ b * m)).resolve_left hx
  have hnle : ¬ b + 1 ≤ padicValNat p (p ^ b * m) := by
    intro hb'
    have hdiv : p ^ (b + 1) ∣ p ^ b * m :=
      (padicValNat_dvd_iff (b + 1) (p ^ b * m)).mpr (Or.inr hb')
    rcases hdiv with ⟨c, hc⟩
    -- p^b·m = c·p^(b+1) = (c·p)·p^b: cancel p^b ⟹ m = c·p ⟹ p | m
    have hcancel : m = p * c := by
      -- from p^b·m = c·p^(b+1): commuted: p^b·m = (c·p)·p^b ⟹ (mul_left_cancel on p^b·m = p^b·(p·c)):
      have hmain : p ^ b * m = p ^ b * (p * c) := by
        calc
          p ^ b * m = p ^ (b + 1) * c := hc
          _ = p ^ b * (p * c) := by
                rw [pow_succ]
                ring
      have hcancel' : m = p * c := by
        apply mul_left_cancel₀ hb
        exact hmain
      exact hcancel'
    exact hpm ⟨c, hcancel⟩
  omega

/-- The value of a nonzero natural number in `kpInt`:
`kpVal ((n : ℕ) : kpInt) = e · padicValNat p n`. -/
lemma kpVal_natCast_eq_mul_ramIdx (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) (hn : n ≠ 0) :
    kpVal p P (n : kpInt p P) = P.ramificationIdx ℤ * padicValNat p n := by
  classical
  rcases padicValNat_decomp p hn with ⟨m, hm, hpm⟩
  have hmz : m ≠ 0 := by
    intro hm0
    apply hn
    rw [hm, hm0, mul_zero]
  have hpnz : (p ^ padicValNat p n : ℕ) ≠ 0 :=
    pow_ne_zero (padicValNat p n) (Nat.Prime.ne_zero (Fact.out (p := Nat.Prime p)))
  have hval : padicValNat p (p ^ padicValNat p n * m) = padicValNat p n :=
    padicValNat_pow_mul_of_not_dvd p hpm
  have hsplit : (n : kpInt p P) = ((p ^ padicValNat p n : ℕ) : kpInt p P)
      * (m : kpInt p P) := by
    calc
      (n : kpInt p P) = (((p ^ padicValNat p n * m : ℕ) : kpInt p P)) := by rw [hm, hval]
      _ = ((p ^ padicValNat p n : ℕ) : kpInt p P) * (m : kpInt p P) := by
            rw [Nat.cast_mul]
  calc
    kpVal p P (n : kpInt p P)
        = kpVal p P (((p ^ padicValNat p n : ℕ) : kpInt p P) * (m : kpInt p P)) := by rw [hsplit]
    _ = kpVal p P ((p ^ padicValNat p n : ℕ) : kpInt p P) + kpVal p P (m : kpInt p P) := by
          rw [kpVal_mul p P ((p ^ padicValNat p n : ℕ) : kpInt p P) (m : kpInt p P)
            (natCast_ne_zero_kpInt p P (p ^ padicValNat p n) hpnz) (natCast_ne_zero_kpInt p P m hmz)]
    _ = P.ramificationIdx ℤ * padicValNat p n := by
          rw [kpVal_natCast_pow_p]
          rw [kpVal_natCast_eq_zero_of_not_dvd p P m hpm]
          simp


/-- Exact filtration: a nonzero element lies in `𝔪^(kpVal x)` but not in
`𝔪^(kpVal x + 1)`. -/
lemma kpVal_exact (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (x : kpInt p P) (hx : x ≠ 0) :
    x ∈ (maximalIdeal (kpInt p P)) ^ kpVal p P x ∧
    x ∉ (maximalIdeal (kpInt p P)) ^ (kpVal p P x + 1) := by
  classical
  set m : ℕ := kpVal p P x with hm
  have hspec : x = (kpUnit p P x hx : kpInt p P) * uniformizer p P ^ m := by
    simpa [← hm] using (kpVal_spec p P x hx)
  constructor
  · rw [hspec]
    exact unit_mul_uniformizer_pow_mem_maximalIdeal_pow p P (kpUnit p P x hx) m
  · intro hxmem
    rw [hspec] at hxmem
    exact (unit_mul_uniformizer_pow_not_mem_succ p P (kpUnit p P x hx) m) hxmem


/-- The P-quotient side of the local transport: the ideal of `kpInt`
generated by the integer `p^n` is the `e·n`-th power of the maximal ideal
(`(p)·kpInt = 𝔪^e` from sub-stone (a), raised to `n`), so the quotient
`kpInt/(p^n)` is `kpInt/𝔪^(e·n)`. -/
lemma kpInt_span_pow_eq_maximalIdeal_pow (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (n : ℕ) :
    (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ * n)
      = Ideal.span ({((p ^ n : ℕ) : kpInt p P)} : Set (kpInt p P)) := by
  classical
  have hspan : Ideal.span ({(p : kpInt p P)} : Set (kpInt p P))
      = (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ := by
    exact (mR_map_eq_span_p p P).symm.trans (mR_map_eq_mS_pow_ramIdx p P)
  calc
    (maximalIdeal (kpInt p P)) ^ (P.ramificationIdx ℤ * n)
        = ((maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ) ^ n := by
          exact pow_mul (maximalIdeal (kpInt p P)) (P.ramificationIdx ℤ) n
    _ = (Ideal.span ({(p : kpInt p P)} : Set (kpInt p P))) ^ n := by rw [hspan]
    _ = Ideal.span {((p : kpInt p P) ^ n)} := Ideal.span_singleton_pow (p : kpInt p P) n
    _ = Ideal.span ({((p ^ n : ℕ) : kpInt p P)} : Set (kpInt p P)) := by
          congr 1
          congr 1
          norm_num


end
end Submission.Vdw.LocalField
