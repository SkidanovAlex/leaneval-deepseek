import Mathlib
import Submission.Work.LinnikBurgess.ddLevelDefs
import Submission.Work.LinnikBurgess.ddLog_cast
import Submission.Work.LinnikBurgess.ddLog_one_isUnit
import Submission.Work.LinnikBurgess.scale_cast_injective

namespace Work.LinnikBurgess

open Polynomial Finset

/-- The polynomial form of the truncated `p`-adic logarithm: `∑_{j=1}^{e} c_j X^j`. -/
noncomputable def ddLogPoly (p e : ℕ) : Polynomial (ZMod (p ^ e)) :=
  ∑ j ∈ Finset.Icc 1 e, Polynomial.C (ddLogCoeff p e j) * Polynomial.X ^ j

lemma ddLogPoly_eval (p e : ℕ) (v : ZMod (p ^ e)) :
    (ddLogPoly p e).eval v = ddLog p e v := by
  simp only [ddLogPoly, ddLog, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

lemma coeff_finset_sum {R : Type*} [Semiring R] {ι : Type*} [DecidableEq ι] (n : ℕ)
    (s : Finset ι) (g : ι → Polynomial R) :
    (s.sum g).coeff n = s.sum (fun i => (g i).coeff n) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

lemma ddLogPoly_coeff (p e j : ℕ) :
    (ddLogPoly p e).coeff j = if j ∈ Finset.Icc 1 e then ddLogCoeff p e j else 0 := by
  rw [ddLogPoly, coeff_finset_sum]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.Icc 1 e) j (fun k => ddLogCoeff p e k)]

lemma ddLogPoly_coeff_eq_zero (p e j : ℕ) (hj : e < j) : (ddLogPoly p e).coeff j = 0 := by
  rw [ddLogPoly_coeff, if_neg]
  simp only [Finset.mem_Icc]
  omega

lemma ddLogPoly_coeff_zero (p N : ℕ) (hN : 1 ≤ N) : (ddLogPoly p N).coeff 0 = 0 := by
  rw [ddLogPoly_coeff, if_neg]
  simp only [Finset.mem_Icc]
  omega

lemma natDegree_ddLogPoly_le (p e : ℕ) : (ddLogPoly p e).natDegree ≤ e := by
  rw [ddLogPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro j hj
  exact (Polynomial.natDegree_C_mul_X_pow_le _ j).trans (Finset.mem_Icc.mp hj).2

lemma geom_sum_mul {R : Type*} [CommRing R] (c : R) (N : ℕ) :
    (∑ i ∈ Finset.range N, (-c) ^ i) * (1 + c) = 1 - (-c) ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, add_mul, ih]
      ring

noncomputable def geoP (p N : ℕ) : Polynomial (ZMod (p ^ N)) :=
  ∑ i ∈ Finset.range N, (-(Polynomial.C ((p : ZMod (p ^ N)) ^ 3) * Polynomial.X)) ^ i

lemma geoP_mul (p N : ℕ) :
    geoP p N * (1 + Polynomial.C ((p : ZMod (p ^ N)) ^ 3) * Polynomial.X)
      = 1 - (-(Polynomial.C ((p : ZMod (p ^ N)) ^ 3) * Polynomial.X)) ^ N := by
  rw [geoP]; exact geom_sum_mul _ _

lemma negCpow_eq_zero (p N : ℕ) (h : N ≤ 3 * N) :
    (-(Polynomial.C ((p : ZMod (p ^ N)) ^ 3) * Polynomial.X)) ^ N = 0 := by
  have ha : ((p : ZMod (p ^ N)) ^ 3) ^ N = 0 := by
    rw [← pow_mul, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p h
  have hc : (Polynomial.C ((p : ZMod (p^N)) ^ 3)) ^ N = 0 := by
    rw [← Polynomial.C_pow, ha, Polynomial.C_0]
  rw [neg_pow, mul_pow, hc, zero_mul, mul_zero]

lemma geoP_mul_eq_one (p N : ℕ) :
    geoP p N * (1 + Polynomial.C ((p : ZMod (p ^ N)) ^ 3) * Polynomial.X) = 1 := by
  rw [geoP_mul, negCpow_eq_zero p N (by omega), sub_zero]

lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → M) :
    ∑ j ∈ Finset.Icc 1 N, g j = ∑ i ∈ Finset.range N, g (i + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.sum_range_succ, ih]

lemma geo_term (p N i : ℕ) :
    (-(Polynomial.C ((p : ZMod (p ^ N)) ^ 3) * Polynomial.X)) ^ i
      = Polynomial.C ((-1 : ZMod (p ^ N)) ^ i * (p : ZMod (p ^ N)) ^ (3 * i))
        * Polynomial.X ^ i := by
  have h1 : (-(Polynomial.C ((p : ZMod (p^N))^3) * Polynomial.X))
      = Polynomial.C (-((p : ZMod (p^N))^3)) * Polynomial.X := by
    rw [map_neg]; ring
  rw [h1, mul_pow, ← Polynomial.C_pow]
  congr 2
  rw [neg_pow, ← pow_mul]

lemma ddLogCoeff_mul_self {p N j : ℕ} [Fact p.Prime] (hj : 1 ≤ j) :
    ddLogCoeff p N j * (j : ZMod (p ^ N))
      = (-1) ^ (j-1) * (p : ZMod (p ^ N)) ^ (3 * (j-1)) := by
  have hp : p.Prime := Fact.out
  set v := padicValNat p j with hv
  have hjdvd : p ^ v ∣ j := pow_padicValNat_dvd
  have hdiv : j / p ^ v * p ^ v = j := Nat.div_mul_cancel hjdvd
  have hipos : 0 < j := hj
  have hvlt : v < j := by
    refine lt_of_lt_of_le (Nat.lt_two_pow_self (n := v)) (le_trans ?_ (Nat.le_of_dvd hipos hjdvd))
    exact Nat.pow_le_pow_left hp.two_le v
  have hvle : v ≤ 3 * (j-1) :=
    (by omega : v ≤ j - 1).trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hcop : ((j / p^v : ℕ)).Coprime (p ^ N) := by
    have h1 : padicValNat p (j / p^v) = 0 := by
      rw [padicValNat.div_pow hjdvd, hv, tsub_self]
    have h2 : ¬ p ∣ j / p^v := by
      rcases (padicValNat.eq_zero_iff.mp h1) with hc | hc | hc
      · exact absurd hc hp.ne_one
      · rw [hc, zero_mul] at hdiv; omega
      · exact hc
    exact ((hp.coprime_iff_not_dvd.mpr h2).symm).pow_right N
  have hunit : IsUnit (((j / p^v : ℕ)) : ZMod (p ^ N)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have hmul : (((j/p^v : ℕ)) : ZMod (p^N))⁻¹ * (((j/p^v : ℕ)) : ZMod (p^N)) = 1 :=
    ZMod.inv_mul_of_unit _ hunit
  have hjcast : (j : ZMod (p ^ N)) = ((j / p ^ v : ℕ) : ZMod (p ^ N)) * (p : ZMod (p ^ N))^v := by
    conv_lhs => rw [← hdiv, hv]
    rw [Nat.cast_mul, Nat.cast_pow]
  rw [ddLogCoeff, hjcast]
  have hexp : (-1 : ZMod (p ^ N)) ^ (j-1) * (p : ZMod (p ^ N))^(3*(j-1)-v)
        * (((j/p^v : ℕ)) : ZMod (p ^ N))⁻¹ * ((((j/p^v : ℕ)) : ZMod (p ^ N)) * (p:ZMod (p ^ N))^v)
      = (-1 : ZMod (p ^ N)) ^ (j-1) * (p : ZMod (p ^ N))^(3*(j-1)-v)
        * ((((j/p^v : ℕ)) : ZMod (p ^ N))⁻¹ * (((j/p^v : ℕ)) : ZMod (p ^ N))) * (p:ZMod (p ^ N))^v := by
    ring
  rw [hexp, hmul, mul_one, mul_assoc, ← pow_add, Nat.sub_add_cancel hvle]

lemma ddLogPoly_derivative (p N : ℕ) [Fact p.Prime] :
    (ddLogPoly p N).derivative = geoP p N := by
  rw [ddLogPoly, Polynomial.derivative_sum, sum_Icc_one_eq_sum_range, geoP]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Polynomial.derivative_C_mul_X_pow, geo_term,
    ddLogCoeff_mul_self (p := p) (N := N) (j := i+1) (by omega)]
  rw [show (i+1)-1 = i by omega]

/-! ## The affine substitution `X ↦ 1 + (1+p³)X` and `Φ' = 0` -/

noncomputable def sigma (p m : ℕ) : Polynomial (ZMod (p ^ m)) :=
  1 + Polynomial.C (1 + (p : ZMod (p ^ m)) ^ 3) * Polynomial.X

lemma sigma_derivative (p m : ℕ) :
    (sigma p m).derivative = Polynomial.C (1 + (p : ZMod (p ^ m)) ^ 3) := by
  rw [sigma, Polynomial.derivative_add, Polynomial.derivative_one, zero_add,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_X, mul_one]

lemma sigma_eval_zero (p m : ℕ) : (sigma p m).eval 0 = 1 := by
  rw [sigma, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, mul_zero, add_zero]

lemma natDegree_sigma_le (p m : ℕ) : (sigma p m).natDegree ≤ 1 := by
  rw [sigma]; compute_degree!

lemma map_sigma (p N m : ℕ) [Fact p.Prime] (hmN : m ≤ N) :
    Polynomial.map (ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p ^ m))) (sigma p N)
      = sigma p m := by
  have h : (ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p ^ m))) (1 + (p : ZMod (p^N))^3)
      = 1 + (p : ZMod (p^m))^3 := by
    rw [map_add, map_one, map_pow, map_natCast]
  rw [sigma, sigma, Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C,
    h, Polynomial.map_X]

lemma geoP_comp_sigma (p N : ℕ) :
    (geoP p N).comp (sigma p N) * Polynomial.C (1 + (p : ZMod (p ^ N)) ^ 3) = geoP p N := by
  have h1 : geoP p N * (1 + Polynomial.C ((p : ZMod (p^N))^3) * Polynomial.X) = 1 :=
    geoP_mul_eq_one p N
  have h2 : (geoP p N).comp (sigma p N)
      * (1 + Polynomial.C ((p : ZMod (p^N))^3) * (sigma p N)) = 1 := by
    have hcomp : (1 + Polynomial.C ((p : ZMod (p^N))^3) * Polynomial.X).comp (sigma p N)
        = 1 + Polynomial.C ((p : ZMod (p^N))^3) * (sigma p N) := by
      rw [Polynomial.add_comp, Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_comp]
    rw [← hcomp, ← Polynomial.mul_comp, h1, Polynomial.one_comp]
  have h3 : 1 + Polynomial.C ((p : ZMod (p^N))^3) * (sigma p N)
      = Polynomial.C (1 + (p : ZMod (p^N))^3)
        * (1 + Polynomial.C ((p : ZMod (p^N))^3) * Polynomial.X) := by
    rw [sigma, Polynomial.C_add, Polynomial.C_1]; ring
  have hU : (1 + Polynomial.C ((p : ZMod (p^N))^3) * Polynomial.X) * geoP p N = 1 := by
    rw [mul_comm]; exact h1
  calc (geoP p N).comp (sigma p N) * Polynomial.C (1 + (p : ZMod (p ^ N)) ^ 3)
      = (geoP p N).comp (sigma p N) * Polynomial.C (1 + (p : ZMod (p ^ N)) ^ 3)
        * ((1 + Polynomial.C ((p : ZMod (p^N))^3) * Polynomial.X) * geoP p N) := by
          rw [hU, mul_one]
      _ = (geoP p N).comp (sigma p N)
        * (1 + Polynomial.C ((p : ZMod (p^N))^3) * (sigma p N)) * geoP p N := by
          rw [h3]; ring
      _ = geoP p N := by rw [h2, one_mul]

noncomputable def Phi (p N : ℕ) : Polynomial (ZMod (p ^ N)) :=
  (ddLogPoly p N).comp (sigma p N) - ddLogPoly p N - Polynomial.C ((ddLogPoly p N).eval 1)

lemma Phi_derivative (p N : ℕ) [Fact p.Prime] : (Phi p N).derivative = 0 := by
  rw [Phi, Polynomial.derivative_sub, Polynomial.derivative_sub, Polynomial.derivative_C,
    Polynomial.derivative_comp, ddLogPoly_derivative, sigma_derivative,
    mul_comm (Polynomial.C (1 + (p : ZMod (p ^ N)) ^ 3)) ((geoP p N).comp (sigma p N)),
    geoP_comp_sigma]
  ring

lemma Phi_coeff_zero (p N : ℕ) (hN : 1 ≤ N) : (Phi p N).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Phi, Polynomial.eval_sub, Polynomial.eval_sub,
    Polynomial.eval_comp, Polynomial.eval_C, sigma_eval_zero,
    show (ddLogPoly p N).eval 0 = 0 from by
      rw [← Polynomial.coeff_zero_eq_eval_zero, ddLogPoly_coeff_zero p N hN]]
  simp

lemma Phi_coeff_eq_zero_of_gt (p N i : ℕ) (hi : N < i) : (Phi p N).coeff i = 0 := by
  have hA : ((ddLogPoly p N).comp (sigma p N)).coeff i = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    refine lt_of_le_of_lt ?_ hi
    refine (Polynomial.natDegree_comp_le).trans ?_
    calc (ddLogPoly p N).natDegree * (sigma p N).natDegree
        ≤ N * 1 := Nat.mul_le_mul (natDegree_ddLogPoly_le p N) (natDegree_sigma_le p N)
      _ = N := mul_one N
  have h2 : (ddLogPoly p N).coeff i = 0 := ddLogPoly_coeff_eq_zero p N i (by omega)
  rw [Phi, Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C,
    if_neg (by omega : ¬ i = 0), hA, h2]
  ring

/-! ## The reduction of `Φ` to `ZMod (p^m)`

We work modulo `p^(3m)`: the identity `Φ' = 0` together with the torsion bound shows that `Φ`
has all coefficients divisible by `p^m`.  This is the step that makes the identity available in
`ZMod (p^m)`, where `Φ' = 0` alone would only give torsion.
-/

lemma three_mul_add_one_le_two_pow (m : ℕ) : 3 * m + 1 ≤ 2 ^ (2 * m + 1) := by
  induction m with
  | zero => norm_num
  | succ n ih =>
      have h : 2 ^ (2 * (n+1) + 1) = 4 * 2 ^ (2 * n + 1) := by
        rw [show 2 * (n+1) + 1 = (2*n+1) + 2 by ring, pow_add]; ring
      rw [h]; nlinarith [ih]

lemma padicValNat_le_three_mul {p m i : ℕ} [Fact p.Prime] (hi : i ≤ 3 * m) :
    padicValNat p i ≤ 3 * m - m := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp
  · by_contra hcon
    rw [not_le] at hcon
    have hp : p.Prime := Fact.out
    have h1 : p ^ padicValNat p i ≤ i := Nat.le_of_dvd h pow_padicValNat_dvd
    have h2 : 2 ^ padicValNat p i ≤ p ^ padicValNat p i := Nat.pow_le_pow_left hp.two_le _
    have h3 : 2 ^ (2*m+1) ≤ 2 ^ padicValNat p i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 3*m+1 ≤ 2 ^ (2*m+1) := three_mul_add_one_le_two_pow m
    omega

/-- If `x * i = 0` in `ZMod (p^N)` and `i` is not too large a power of `p`, then `x` reduces to
`0` in `ZMod (p^m)`.  This is the torsion computation of the derivative argument. -/
lemma coeff_cast_eq_zero {p N m i : ℕ} [Fact p.Prime] (hmN : m ≤ N) (hi1 : 1 ≤ i)
    (hiN : i ≤ N) (hbig : padicValNat p i ≤ N - m) {g : ZMod (p ^ N)}
    (h : g * (i : ZMod (p ^ N)) = 0) :
    (ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p ^ m))) g = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.pos.ne'⟩
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero m hp.pos.ne'⟩
  set v := padicValNat p i with hv
  have hvd : p ^ v ∣ i := pow_padicValNat_dvd
  have hdiv : i / p ^ v * p ^ v = i := Nat.div_mul_cancel hvd
  have hipos : 0 < i := hi1
  have hcop : ((i / p^v : ℕ)).Coprime (p ^ N) := by
    have h1 : padicValNat p (i / p^v) = 0 := by
      rw [padicValNat.div_pow hvd, hv, tsub_self]
    have h2 : ¬ p ∣ i / p^v := by
      rcases (padicValNat.eq_zero_iff.mp h1) with hc | hc | hc
      · exact absurd hc hp.ne_one
      · rw [hc, zero_mul] at hdiv; omega
      · exact hc
    exact ((hp.coprime_iff_not_dvd.mpr h2).symm).pow_right N
  have hunit : IsUnit (((i / p^v : ℕ)) : ZMod (p ^ N)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have hu : (((i/p^v : ℕ)) : ZMod (p^N)) * (((i/p^v : ℕ)) : ZMod (p^N))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hcast : (i : ZMod (p^N)) = (((i / p^v : ℕ)) : ZMod (p^N)) * (p : ZMod (p^N))^v := by
    conv_lhs => rw [← hdiv, hv]
    rw [Nat.cast_mul, Nat.cast_pow]
  have hgp : g * (p : ZMod (p ^ N))^v = 0 := by
    have h2 : g * (((i/p^v : ℕ)) : ZMod (p^N)) * (p : ZMod (p^N))^v
        * ((((i/p^v : ℕ)) : ZMod (p^N)))⁻¹ = g * (p : ZMod (p^N))^v := by
      rw [show g * (((i/p^v : ℕ)) : ZMod (p^N)) * (p : ZMod (p^N))^v
            * ((((i/p^v : ℕ)) : ZMod (p^N)))⁻¹
          = g * (p : ZMod (p^N))^v
            * ((((i/p^v : ℕ)) : ZMod (p^N)) * ((((i/p^v : ℕ)) : ZMod (p^N)))⁻¹) by ring,
        hu, mul_one]
    have h3 : g * (((i/p^v : ℕ)) : ZMod (p^N)) * (p : ZMod (p^N))^v
        * ((((i/p^v : ℕ)) : ZMod (p^N)))⁻¹ = g * (i : ZMod (p^N))
        * ((((i/p^v : ℕ)) : ZMod (p^N)))⁻¹ := by
      rw [hcast]; ring
    rw [← h2, h3, h, zero_mul]
  have hvN : v ≤ N := by
    have h1 : v < 2^v := Nat.lt_two_pow_self
    have h2 : 2^v ≤ p^v := Nat.pow_le_pow_left hp.two_le v
    have h3 : p^v ≤ i := Nat.le_of_dvd hipos hvd
    omega
  have hzero : g * (p : ZMod (p ^ N))^v = ((g.val * p^v : ℕ) : ZMod (p ^ N)) := by
    rw [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val]
  have hdvd : p^N ∣ g.val * p^v := by
    rw [← ZMod.natCast_eq_zero_iff, ← hzero]
    exact hgp
  have hdvd2 : p^(N - v) ∣ g.val := by
    have h1 : p^v * p^(N-v) ∣ g.val * p^v := by
      rw [← pow_add, Nat.add_sub_cancel' hvN]; exact hdvd
    rw [mul_comm g.val (p^v)] at h1
    exact (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos v)).mp h1
  have hmle : m ≤ N - v := by omega
  have hfin : p^m ∣ g.val := dvd_trans (pow_dvd_pow p hmle) hdvd2
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  exact hfin

lemma Phi_map_eq_zero (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) :
    Polynomial.map (ZMod.castHom (pow_dvd_pow p (by omega : m ≤ 3 * m)) (ZMod (p ^ m)))
      (Phi p (3 * m)) = 0 := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map, Polynomial.coeff_zero]
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [Phi_coeff_zero p (3*m) (by omega)]; exact map_zero _
  · by_cases hiN : i ≤ 3*m
    · refine coeff_cast_eq_zero (by omega) hi0 hiN (padicValNat_le_three_mul hiN) ?_
      have h := congrArg (fun q : Polynomial (ZMod (p ^ (3*m))) => q.coeff (i-1))
        (Phi_derivative p (3*m))
      rw [Polynomial.coeff_derivative, Polynomial.coeff_zero,
        show i - 1 + 1 = i by omega] at h
      have h2 : ((i-1 : ℕ) : ZMod (p ^ (3*m))) + 1 = (i : ZMod (p ^ (3*m))) := by
        rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]; ring
      rw [h2] at h
      exact h
    · rw [Phi_coeff_eq_zero_of_gt p (3*m) i (by omega)]; exact map_zero _

lemma castHom_ddLogCoeff {p N m j : ℕ} [Fact p.Prime] (hmN : m ≤ N) (hj1 : 1 ≤ j)
    (hjm : j ≤ m) :
    (ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p ^ m))) (ddLogCoeff p N j)
      = ddLogCoeff p m j := by
  have hp : p.Prime := Fact.out
  set v := padicValNat p j with hv
  have hjdvd : p ^ v ∣ j := pow_padicValNat_dvd
  have hdiv : j / p ^ v * p ^ v = j := Nat.div_mul_cancel hjdvd
  have h2 : ¬ p ∣ j / p^v := by
    have h1 : padicValNat p (j / p^v) = 0 := by
      rw [padicValNat.div_pow hjdvd, hv, tsub_self]
    rcases (padicValNat.eq_zero_iff.mp h1) with hc | hc | hc
    · exact absurd hc hp.ne_one
    · rw [hc, zero_mul] at hdiv; omega
    · exact hc
  have hcop : ((j / p^v : ℕ)).Coprime (p ^ N) :=
    ((hp.coprime_iff_not_dvd.mpr h2).symm).pow_right N
  have hunit : IsUnit (((j / p^v : ℕ)) : ZMod (p ^ N)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have hinv : (ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p ^ m)))
        ((((j/p^v : ℕ)) : ZMod (p^N))⁻¹) = ((((j/p^v : ℕ)) : ZMod (p^m)))⁻¹ := by
    have h1 : ((((j/p^v : ℕ)) : ZMod (p^N))) * ((((j/p^v : ℕ)) : ZMod (p^N))⁻¹) = 1 :=
      ZMod.mul_inv_of_unit _ hunit
    have h3 : ((ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p^m))) ((((j/p^v : ℕ)) : ZMod (p^N))))
        * ((ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p^m)))
            ((((j/p^v : ℕ)) : ZMod (p^N))⁻¹)) = 1 := by
      rw [← map_mul, h1, map_one]
    rw [map_natCast] at h3
    exact (ZMod.inv_eq_of_mul_eq_one (p^m) _ _ h3).symm
  rw [ddLogCoeff, ddLogCoeff, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast,
    hinv]

lemma castHom_ddLogCoeff_eq_zero {p N m j : ℕ} [Fact p.Prime] (hmN : m ≤ N) (hjm : m < j)
    (hjN : j ≤ N) :
    (ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p ^ m))) (ddLogCoeff p N j) = 0 := by
  have hp : p.Prime := Fact.out
  set v := padicValNat p j with hv
  have hjdvd : p ^ v ∣ j := pow_padicValNat_dvd
  have hvp : v ≤ j - 1 := by
    have h1 : v < 2^v := Nat.lt_two_pow_self
    have h2 : 2^v ≤ p^v := Nat.pow_le_pow_left hp.two_le v
    have h3 : p^v ≤ j := Nat.le_of_dvd (by omega) hjdvd
    omega
  have hK : m ≤ 3 * (j-1) - v := by omega
  have hzero : (p : ZMod (p ^ m)) ^ (3 * (j-1) - v) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p hK
  rw [ddLogCoeff, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, map_natCast, hzero]
  ring

lemma map_ddLogPoly (p N m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hmN : m ≤ N) :
    Polynomial.map (ZMod.castHom (pow_dvd_pow p hmN) (ZMod (p ^ m))) (ddLogPoly p N)
      = ddLogPoly p m := by
  apply Polynomial.ext
  intro j
  rw [Polynomial.coeff_map, ddLogPoly_coeff, ddLogPoly_coeff]
  by_cases hj : j ∈ Finset.Icc 1 N
  · rw [if_pos hj]
    by_cases hjm : j ≤ m
    · have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      rw [if_pos (Finset.mem_Icc.mpr ⟨hj1, hjm⟩)]
      exact castHom_ddLogCoeff hmN hj1 hjm
    · rw [if_neg (by simp only [Finset.mem_Icc]; omega)]
      exact castHom_ddLogCoeff_eq_zero hmN (by omega) (Finset.mem_Icc.mp hj).2
  · rw [if_neg hj, if_neg (fun h => hj (Finset.Icc_subset_Icc_right hmN h)), map_zero]

/-! ## The polynomial identity in `ZMod (p^m)` -/

lemma ddLogPoly_comp_sigma (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) :
    (ddLogPoly p m).comp (sigma p m)
      = ddLogPoly p m + Polynomial.C ((ddLogPoly p m).eval 1) := by
  have hN : m ≤ 3 * m := by omega
  have heval : (ZMod.castHom (pow_dvd_pow p (by omega : m ≤ 3*m)) (ZMod (p^m)))
        ((ddLogPoly p (3*m)).eval 1) = (ddLogPoly p m).eval 1 := by
    rw [← Polynomial.eval₂_at_one, ← Polynomial.eval_map,
      map_ddLogPoly p (3*m) m hm hN]
  have h0 : (ddLogPoly p m).comp (sigma p m) - ddLogPoly p m
      = Polynomial.C ((ddLogPoly p m).eval 1) := by
    have h := Phi_map_eq_zero p m hm
    rw [Phi, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_comp, Polynomial.map_C,
      map_ddLogPoly p (3*m) m hm hN, map_sigma p (3*m) m hN, heval] at h
    exact sub_eq_zero.mp h
  rw [← h0]; ring

/-- The "logarithm of a product" identity in the special case of multiplication by `1 + p³`. -/
lemma ddLog_add_one (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (a : ZMod (p ^ m)) :
    ddLog p m (a + 1 + (p : ZMod (p ^ m)) ^ 3 * a) = ddLog p m a + ddLog p m 1 := by
  have h := congrArg (fun q : Polynomial (ZMod (p^m)) => q.eval a) (ddLogPoly_comp_sigma p m hm)
  simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_C, ddLogPoly_eval] at h
  have hs : (sigma p m).eval a = a + 1 + (p : ZMod (p ^ m)) ^ 3 * a := by
    rw [sigma, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    ring
  rw [hs] at h
  exact h

/-! ## The assembly: exponentiation by the inverse truncated logarithm -/

/-- Multiplication by `p³` of the "upward" cast `ZMod (p^m) → ZMod (p^e)` agrees with `p³ x`
when `e ≤ m + 3` (in the application `e = m + 3`). -/
lemma p3_mul_castUp_castHom {p e m : ℕ} [Fact p.Prime] (hme : m ≤ e) (hle : e ≤ m + 3)
    (x : ZMod (p ^ e)) :
    (p : ZMod (p ^ e)) ^ 3
        * (ZMod.cast (ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^m)) x) : ZMod (p^e))
      = (p : ZMod (p ^ e)) ^ 3 * x := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p^e) := ⟨pow_ne_zero e hp.pos.ne'⟩
  haveI : NeZero (p^m) := ⟨pow_ne_zero m hp.pos.ne'⟩
  have hcast : (ZMod.cast (ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^m)) x) : ZMod (p^e))
      = ((x.val % p^m : ℕ) : ZMod (p^e)) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val, ZMod.val_natCast]
  have hnatCast : (p : ZMod (p^e))^3 * ((x.val % p^m : ℕ) : ZMod (p^e))
      = (p : ZMod (p^e))^3 * ((x.val : ℕ) : ZMod (p^e)) := by
    have key : ((p^3 * (x.val % p^m) : ℕ) : ZMod (p^e))
        = ((p^3 * x.val : ℕ) : ZMod (p^e)) := by
      rw [ZMod.natCast_eq_natCast_iff]
      have h1 : x.val % p^m ≡ x.val [MOD p^m] := Nat.mod_modEq x.val (p^m)
      refine (h1.mul_left' (p^3)).of_dvd ?_
      rw [← pow_add]
      exact pow_dvd_pow p (by omega)
    simpa only [Nat.cast_mul, Nat.cast_pow] using key
  rw [hcast, hnatCast, ZMod.natCast_zmod_val]

theorem ddLog_pow_eq {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 4 ≤ e) (v : ZMod (p ^ e)) :
    (1 + (p : ZMod (p ^ e)) ^ 3) ^
      (((ZMod.castHom (pow_dvd_pow p (by omega : e - 3 ≤ e)) (ZMod (p ^ (e - 3)))
          (Work.LinnikBurgess.ddLog p e 1))⁻¹
        * ZMod.castHom (pow_dvd_pow p (by omega : e - 3 ≤ e)) (ZMod (p ^ (e - 3)))
          (Work.LinnikBurgess.ddLog p e v)).val)
      = 1 + (p : ZMod (p ^ e)) ^ 3 * v := by
  have hp : p.Prime := Fact.out
  have he3 : 1 ≤ e - 3 := by omega
  have hme : e - 3 ≤ e := by omega
  have hle3 : e ≤ (e - 3) + 3 := by omega
  haveI : NeZero (p ^ (e-3)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hTunit : IsUnit (ddLog p (e-3) 1) := ddLog_one_isUnit he3
  have hTmul : (ddLog p (e-3) 1)⁻¹ * (ddLog p (e-3) 1) = 1 := ZMod.inv_mul_of_unit _ hTunit
  have hTmul' : (ddLog p (e-3) 1) * (ddLog p (e-3) 1)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hTunit
  have hzero : ddLog p (e-3) (0 : ZMod (p^(e-3))) = 0 := by
    rw [ddLog]
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [zero_pow (by have := (Finset.mem_Icc.mp hj).1; omega), mul_zero]
  let g : ZMod (p^e) := 1 + (p : ZMod (p^e))^3
  have hg : g = 1 + (p : ZMod (p^e))^3 := rfl
  let U : ℕ → ZMod (p^e) := fun n => Nat.rec 0 (fun _ un => un + 1 + (p : ZMod (p^e))^3 * un) n
  have hU0 : U 0 = 0 := rfl
  have hUsucc : ∀ n, U (n+1) = U n + 1 + (p : ZMod (p^e))^3 * U n := fun n => rfl
  have hU : ∀ n, 1 + (p : ZMod (p^e))^3 * U n = g ^ n := by
    intro n
    induction n with
    | zero => rw [hU0, mul_zero, add_zero, pow_zero]
    | succ k ih =>
        have hs : g ^ (k+1) = g ^ k * g := by rw [pow_succ]
        rw [hUsucc, hs, ← ih, hg]
        ring
  let u : ℕ → ZMod (p^(e-3)) :=
    fun n => (ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^(e-3)))) (U n)
  have hu0 : u 0 = 0 := by simp only [u, hU0, map_zero]
  have husucc : ∀ n, u (n+1) = u n + 1 + (p : ZMod (p^(e-3)))^3 * u n := by
    intro n
    simp only [u, hUsucc, map_add, map_one, map_mul, map_pow, map_natCast]
  have hlog : ∀ n, ddLog p (e-3) (u n) = (n : ZMod (p^(e-3))) * ddLog p (e-3) 1 := by
    intro n
    induction n with
    | zero => rw [hu0, Nat.cast_zero, zero_mul]; exact hzero
    | succ k ih => rw [husucc k, ddLog_add_one p (e-3) he3 (u k), ih, Nat.cast_succ]; ring
  let W : ZMod (p^(e-3)) → ZMod (p^e) :=
    fun w => 1 + (p : ZMod (p^e))^3 * (ZMod.cast w : ZMod (p^e))
  have hW : ∀ n, W (u n) = g ^ n := by
    intro n
    have h1 : (p : ZMod (p^e))^3 * (ZMod.cast (u n) : ZMod (p^e))
        = (p : ZMod (p^e))^3 * U n := by
      simp only [u]
      exact p3_mul_castUp_castHom hme hle3 (U n)
    simp only [W]
    rw [h1, ← hU n]
  have hWinj : Function.Injective W := by
    intro a b hab
    change 1 + (p : ZMod (p^e))^3 * (ZMod.cast a : ZMod (p^e))
      = 1 + (p : ZMod (p^e))^3 * (ZMod.cast b : ZMod (p^e)) at hab
    exact scale_cast_injective (by omega : (e-3) + 3 ≤ e) (add_left_cancel hab)
  let Φ : ZMod (p^(e-3)) → ZMod (p^e) := fun x => g ^ x.val
  have hPhiW : ∀ x, Φ x = W (u x.val) := by
    intro x; simp only [Φ]; exact (hW x.val).symm
  have hPhi_inj : Function.Injective Φ := by
    intro x y hxy
    have h1 : u x.val = u y.val := by
      apply hWinj
      rw [← hPhiW x, ← hPhiW y, hxy]
    have h2 : (x.val : ZMod (p^(e-3))) * (ddLog p (e-3) 1)
        = (y.val : ZMod (p^(e-3))) * (ddLog p (e-3) 1) := by
      rw [← hlog x.val, ← hlog y.val, h1]
    have h3 : (x.val : ZMod (p^(e-3))) = (y.val : ZMod (p^(e-3))) := by
      have hc := congrArg (fun z => z * (ddLog p (e-3) 1)⁻¹) h2
      rwa [mul_assoc, mul_assoc, hTmul', mul_one, mul_one] at hc
    have h4 : x.val = y.val := by
      have hx : ((x.val : ZMod (p^(e-3)))).val = x.val := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt x)]
      have hy : ((y.val : ZMod (p^(e-3)))).val = y.val := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt y)]
      rw [← hx, ← hy, h3]
    exact ZMod.val_injective _ h4
  have hcard : (Finset.univ.image Φ).card = (Finset.univ.image W).card := by
    rw [Finset.card_image_of_injective _ hPhi_inj, Finset.card_image_of_injective _ hWinj]
  have hsub : Finset.univ.image Φ ⊆ Finset.univ.image W := by
    intro z hz
    rw [Finset.mem_image] at hz ⊢
    obtain ⟨x, -, rfl⟩ := hz
    exact ⟨u x.val, Finset.mem_univ _, (hPhiW x).symm⟩
  have heq : Finset.univ.image Φ = Finset.univ.image W :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have hWv : W ((ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^(e-3)))) v)
      = 1 + (p : ZMod (p^e))^3 * v := by
    simp only [W]
    rw [p3_mul_castUp_castHom hme hle3 v]
  have hmemW : (1 + (p : ZMod (p^e))^3 * v) ∈ Finset.univ.image W :=
    Finset.mem_image.mpr ⟨(ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^(e-3)))) v,
      Finset.mem_univ _, hWv⟩
  have hmemPhi : (1 + (p : ZMod (p^e))^3 * v) ∈ Finset.univ.image Φ := by
    rwa [heq]
  obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hmemPhi
  have huw : u x.val = (ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^(e-3)))) v := by
    apply hWinj
    rw [← hPhiW x, hx, hWv]
  have hcast1 : (ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^(e-3)))) (ddLog p e 1)
      = ddLog p (e-3) 1 := by
    rw [ddLog_cast hme 1, map_one]
  have hcastv : (ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^(e-3)))) (ddLog p e v)
      = ddLog p (e-3) ((ZMod.castHom (pow_dvd_pow p hme) (ZMod (p^(e-3)))) v) :=
    ddLog_cast hme v
  have hk : ((ZMod.castHom (pow_dvd_pow p (by omega : e-3 ≤ e)) (ZMod (p^(e-3))))
        (ddLog p e 1))⁻¹
      * ((ZMod.castHom (pow_dvd_pow p (by omega : e-3 ≤ e)) (ZMod (p^(e-3))))
        (ddLog p e v)) = (x.val : ZMod (p^(e-3))) := by
    rw [hcast1, hcastv, ← huw]
    rw [hlog x.val, mul_comm (x.val : ZMod (p^(e-3))) (ddLog p (e-3) 1), ← mul_assoc, hTmul,
      one_mul]
  have hkval : (((ZMod.castHom (pow_dvd_pow p (by omega : e-3 ≤ e)) (ZMod (p^(e-3))))
        (ddLog p e 1))⁻¹
      * ((ZMod.castHom (pow_dvd_pow p (by omega : e-3 ≤ e)) (ZMod (p^(e-3))))
        (ddLog p e v))).val = x.val := by
    rw [hk, ZMod.val_natCast, Nat.mod_eq_of_lt (ZMod.val_lt x)]
  rw [hkval]
  exact hx

end Work.LinnikBurgess
