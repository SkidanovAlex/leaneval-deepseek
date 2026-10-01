import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Algebra.BigOperators.sum_range_mul_eq
import Submission.Commons.Algebra.Polynomial.eval_add_eq_sum_hasseDeriv
import Submission.Commons.NumberTheory.GaussSum.prime_field_quadratic_bound

namespace Commons.NumberTheory.GaussSum

open scoped BigOperators

/-! ## The additive-character exponential `E` and the range-sum `Tsum` -/

/-- `E N m = exp (2 * π * I * m / N)`, phrased as the standard additive character of `ZMod N`. -/
noncomputable def E (N : ℕ) [NeZero N] (m : ℤ) : ℂ := ZMod.stdAddChar ((m : ℤ) : ZMod N)

lemma E_add (N : ℕ) [NeZero N] (m m' : ℤ) : E N (m + m') = E N m * E N m' := by
  unfold E
  rw [← AddChar.map_add_eq_mul]
  congr 1
  push_cast; ring

lemma E_eq_one_of_dvd (N : ℕ) [NeZero N] (m : ℤ) (h : (N : ℤ) ∣ m) : E N m = 1 := by
  unfold E
  have hm : ((m : ℤ) : ZMod N) = 0 := by
    obtain ⟨k, rfl⟩ := h
    push_cast
    rw [ZMod.natCast_self]
    ring
  rw [hm, AddChar.map_zero_eq_one]

lemma E_eq_of_dvd_sub (N : ℕ) [NeZero N] (m m' : ℤ) (h : (N : ℤ) ∣ m - m') :
    E N m = E N m' := by
  have h1 : m = m' + (m - m') := by ring
  conv_lhs => rw [h1]
  rw [E_add, E_eq_one_of_dvd N _ h, mul_one]

lemma E_norm (N : ℕ) [NeZero N] (m : ℤ) : ‖E N m‖ = 1 := by
  unfold E
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe (ZMod.toCircle ((m : ℤ) : ZMod N))

lemma E_one (m : ℤ) : E 1 m = 1 := by
  unfold E
  rw [show ((m : ℤ) : ZMod 1) = 0 from Subsingleton.elim _ _, AddChar.map_zero_eq_one]

/-- The complete exponential sum over the integers `0, …, N-1`. -/
noncomputable def Tsum (N : ℕ) [NeZero N] (H : Polynomial ℤ) : ℂ :=
  ∑ j ∈ Finset.range N, E N (Polynomial.eval (j : ℤ) H)

/-- The complete exponential sum over `ZMod N` (the form appearing in the target). -/
noncomputable def gsum (N : ℕ) [NeZero N] (H : Polynomial ℤ) : ℂ :=
  ∑ x : ZMod N, ZMod.stdAddChar (Polynomial.eval₂ (Int.castRingHom (ZMod N)) x H)

noncomputable def finEquivZMod (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun i := (i : ZMod N)
  invFun x := ⟨x.val, ZMod.val_lt x⟩
  left_inv i := by
    apply Fin.ext
    simpa using ZMod.val_cast_of_lt i.isLt
  right_inv x := by
    show ((x.val : ℕ) : ZMod N) = x
    exact ZMod.natCast_zmod_val x

theorem zmod_sum_range (N : ℕ) [NeZero N] (g : ZMod N → ℂ) :
    ∑ x : ZMod N, g x = ∑ j ∈ Finset.range N, g (j : ZMod N) := by
  have key : ∑ i : Fin N, g (i : ZMod N) = ∑ x : ZMod N, g x :=
    Fintype.sum_bijective (fun i : Fin N => (i : ZMod N)) (finEquivZMod N).bijective
      (fun i => g (i : ZMod N)) g (fun _ => rfl)
  rw [← key]
  exact Fin.sum_univ_eq_sum_range (fun j => g (j : ZMod N)) N

theorem gsum_eq_Tsum (N : ℕ) [NeZero N] (H : Polynomial ℤ) : gsum N H = Tsum N H := by
  rw [gsum, Tsum, zmod_sum_range]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have h2 : Polynomial.eval₂ (Int.castRingHom (ZMod N)) ((j : ℤ) : ZMod N) H
      = ((Polynomial.eval (j : ℤ) H : ℤ) : ZMod N) := Polynomial.eval₂_at_apply _ _
  rw [show (j : ZMod N) = ((j : ℤ) : ZMod N) from by push_cast; rfl, h2]
  rfl


lemma E_exp (N : ℕ) [NeZero N] (m : ℤ) :
    E N m = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (N : ℂ)) := by
  unfold E
  rw [ZMod.stdAddChar_coe]

lemma E_pow_mul (p N : ℕ) [NeZero p] (hN : 1 ≤ N) (m : ℤ) :
    E (p ^ N) (m * (p : ℤ) ^ (N - 1)) = E p m := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  rw [E_exp, E_exp]
  have hpN : (p : ℂ) ^ N = (p : ℂ) ^ (N - 1) * (p : ℂ) := by
    rw [← pow_succ]; congr 1; omega
  push_cast
  rw [hpN]
  congr 1
  field_simp

lemma E_sq_mul (p N : ℕ) [NeZero p] (hN : 2 ≤ N) (m : ℤ) :
    E (p ^ N) ((p : ℤ) ^ 2 * m) = E (p ^ (N - 2)) m := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  rw [E_exp, E_exp]
  have hpN : (p : ℂ) ^ N = (p : ℂ) ^ 2 * (p : ℂ) ^ (N - 2) := by
    rw [← pow_add]; congr 1; omega
  push_cast
  rw [hpN]
  congr 1
  field_simp

lemma E_neg (N : ℕ) [NeZero N] (m : ℤ) : E N (-m) = (E N m)⁻¹ := by
  unfold E
  nth_rewrite 1 [show ((-m : ℤ) : ZMod N) = -((m : ℤ) : ZMod N) by push_cast; ring]
  rw [AddChar.map_neg_eq_inv]


/-- The Taylor/stationary-phase step: replacing `u` by `u + p^(N-2) * w` changes the
exponential by a factor `E p (w * H'(a))`. -/
lemma E_taylor (p N : ℕ) [NeZero p] (hN : 2 ≤ N)
    (H : Polynomial ℤ) (a u w : ℕ)
    (hdvd : (p : ℤ) ∣ Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) (Polynomial.derivative H)
              - Polynomial.eval (a : ℤ) (Polynomial.derivative H)) :
    E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (N - 2) * (w : ℤ))) H)
      = E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) H)
        * E p (w * Polynomial.eval (a : ℤ) (Polynomial.derivative H)) := by
  set x : ℤ := (a : ℤ) + (p : ℤ) * (u : ℤ) with hx
  set y : ℤ := (p : ℤ) ^ (N - 1) * (w : ℤ) with hy
  have hxy : (a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (N - 2) * (w : ℤ)) = x + y := by
    rw [hx, hy]
    have hpp : (p : ℤ) ^ (N - 1) = (p : ℤ) * (p : ℤ) ^ (N - 2) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpp]; ring
  obtain ⟨c, hc⟩ := Polynomial.exists_mul_sq_add_linear_part_eq_eval_add H x y
  rw [hxy, ← hc]
  rw [show c * y ^ 2 + Polynomial.eval x (Polynomial.derivative H) * y + Polynomial.eval x H
      = Polynomial.eval x H + (c * y ^ 2 + Polynomial.eval x (Polynomial.derivative H) * y)
      by ring]
  rw [E_add]
  congr 1
  rw [E_add]
  have hcy : E (p ^ N) (c * y ^ 2) = 1 := by
    apply E_eq_one_of_dvd
    rw [hy]
    have h1 : (p : ℤ) ^ N ∣ ((p : ℤ) ^ (N - 1) * (w : ℤ)) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      apply dvd_mul_of_dvd_left
      apply pow_dvd_pow
      omega
    exact dvd_mul_of_dvd_right h1 c
  rw [hcy, one_mul]
  have hxy2 : Polynomial.eval x (Polynomial.derivative H) * y
      = (Polynomial.eval x (Polynomial.derivative H) * (w : ℤ)) * (p : ℤ) ^ (N - 1) := by
    rw [hy]; ring
  rw [hxy2, E_pow_mul p N (by omega)]
  apply E_eq_of_dvd_sub
  rw [show Polynomial.eval x (Polynomial.derivative H) * (w : ℤ)
        - w * Polynomial.eval (a : ℤ) (Polynomial.derivative H)
      = (w : ℤ) * (Polynomial.eval x (Polynomial.derivative H)
          - Polynomial.eval (a : ℤ) (Polynomial.derivative H)) by ring]
  exact dvd_mul_of_dvd_right (by rw [hx]; exact hdvd) _


/-- Orthogonality of the additive character: a complete linear exponential sum over `ZMod p`. -/
theorem orth_sum (p : ℕ) [Fact p.Prime] [NeZero p] (c : ℤ) :
    ∑ w ∈ Finset.range p, E p (w * c) = if (p : ℤ) ∣ c then (p : ℂ) else 0 := by
  have hpt : ∀ w : ℕ, E p (w * c) = ZMod.stdAddChar ((w : ZMod p) * ((c : ℤ) : ZMod p)) := by
    intro w
    unfold E
    rw [show ((w : ZMod p) * ((c : ℤ) : ZMod p)) = (((w : ℤ) * c : ℤ) : ZMod p) by
      push_cast; ring]
  have h1 : ∑ w ∈ Finset.range p, E p (w * c)
      = ∑ z : ZMod p, ZMod.stdAddChar (z * ((c : ℤ) : ZMod p)) := by
    rw [zmod_sum_range p (fun z => ZMod.stdAddChar (z * ((c : ℤ) : ZMod p)))]
    apply Finset.sum_congr rfl
    intro w hw
    exact hpt w
  rw [h1, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  by_cases h : ((c : ℤ) : ZMod p) = 0
  · rw [if_pos h, if_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mpr hh))]
    norm_num

/-- The canonical critical point of `β - 2 δ X` modulo `p`. -/
noncomputable def critPt (p : ℕ) [NeZero p] (β δ : ℤ) : ℕ :=
  ((β : ZMod p) * ((2 : ZMod p) * (δ : ZMod p))⁻¹).val

theorem critPt_lt (p : ℕ) [NeZero p] (β δ : ℤ) : critPt p β δ < p :=
  ZMod.val_lt _

theorem critPt_cast (p : ℕ) [Fact p.Prime] [NeZero p] (β δ : ℤ) :
    (critPt p β δ : ZMod p) = (β : ZMod p) * ((2 : ZMod p) * (δ : ZMod p))⁻¹ := by
  unfold critPt
  rw [ZMod.natCast_zmod_val]

theorem two_ne_zero_zmod (p : ℕ) [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h))
    (Fact.out : p.Prime).two_le)

theorem two_mul_delta_ne_zero (p : ℕ) [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (δ : ℤ)
    (hδ : ¬ (p : ℤ) ∣ δ) : (2 : ZMod p) * (δ : ZMod p) ≠ 0 :=
  mul_ne_zero (two_ne_zero_zmod p hp2) (fun h => hδ ((ZMod.intCast_zmod_eq_zero_iff_dvd δ p).mp h))

theorem critPt_eq (p : ℕ) [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (β δ : ℤ)
    (hδ : ¬ (p : ℤ) ∣ δ) :
    (2 : ZMod p) * (δ : ZMod p) * ((β : ZMod p) * ((2 : ZMod p) * (δ : ZMod p))⁻¹)
      = (β : ZMod p) := by
  rw [mul_comm ((2 : ZMod p) * (δ : ZMod p)) ((β : ZMod p) * ((2 : ZMod p) * (δ : ZMod p))⁻¹),
    mul_assoc, inv_mul_cancel₀ (two_mul_delta_ne_zero p hp2 δ hδ), mul_one]

theorem critPt_spec (p : ℕ) [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (β δ : ℤ)
    (hδ : ¬ (p : ℤ) ∣ δ) :
    (p : ℤ) ∣ β - 2 * δ * (critPt p β δ : ℤ) := by
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_
  have hcp := critPt_cast p β δ
  have hA := critPt_eq p hp2 β δ hδ
  rw [show (((β - 2 * δ * (critPt p β δ : ℤ) : ℤ)) : ZMod p)
        = (β : ZMod p) - (2 : ZMod p) * (δ : ZMod p) * (critPt p β δ : ZMod p) by
      push_cast; ring]
  rw [hcp, hA, sub_self]

theorem critPt_unique (p : ℕ) [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (β δ : ℤ)
    (hδ : ¬ (p : ℤ) ∣ δ) (a : ℕ) (ha : a < p) :
    ((p : ℤ) ∣ β - 2 * δ * (a : ℤ) ↔ a = critPt p β δ) := by
  have hqq := two_mul_delta_ne_zero p hp2 δ hδ
  have hcp := critPt_cast p β δ
  have hA := critPt_eq p hp2 β δ hδ
  have hcast : (((β - 2 * δ * (a : ℤ) : ℤ)) : ZMod p)
      = (β : ZMod p) - (2 : ZMod p) * (δ : ZMod p) * (a : ZMod p) := by push_cast; ring
  have hmod : ((a : ZMod p) = (critPt p β δ : ZMod p)) ↔ a = critPt p β δ := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (critPt_lt p β δ)]
  have hkey : ((β : ZMod p) - (2 : ZMod p) * (δ : ZMod p) * (a : ZMod p) = 0)
      ↔ (a : ZMod p) = (critPt p β δ : ZMod p) := by
    constructor
    · intro h
      have hb : (2 : ZMod p) * (δ : ZMod p) * (a : ZMod p) = (β : ZMod p) :=
        (sub_eq_zero.mp h).symm
      calc (a : ZMod p)
          = ((2 : ZMod p) * (δ : ZMod p))⁻¹ * ((2 : ZMod p) * (δ : ZMod p) * (a : ZMod p)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hqq, one_mul]
        _ = ((2 : ZMod p) * (δ : ZMod p))⁻¹ * (β : ZMod p) := by rw [hb]
        _ = (β : ZMod p) * ((2 : ZMod p) * (δ : ZMod p))⁻¹ := by ring
        _ = (critPt p β δ : ZMod p) := hcp.symm
    · intro h
      rw [h, hcp, hA, sub_self]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (β - 2 * δ * (a : ℤ)) p, hcast]
  exact hkey.trans hmod


/-- The polynomial produced by one stationary-phase step.  If `a0` is the critical point of
`β - 2 δ X` modulo `p`, then `Gpoly p R β δ a0` is the quadratic phase of the reduced sum. -/
noncomputable def Gpoly (p : ℕ) (R : Polynomial ℤ) (β δ : ℤ) (a0 : ℕ) : Polynomial ℤ :=
  Polynomial.C ((β - 2 * δ * (a0 : ℤ)) / (p : ℤ) + (Polynomial.hasseDeriv 1 R).eval (a0 : ℤ))
      * Polynomial.X
    - Polynomial.C δ * Polynomial.X ^ 2
    + Polynomial.C (p : ℤ) *
        (∑ n ∈ Finset.range (R.natDegree - 1),
          Polynomial.C ((Polynomial.hasseDeriv (n + 2) R).eval (a0 : ℤ) * (p : ℤ) ^ n)
            * Polynomial.X ^ (n + 2))

lemma eval_Gpoly (p : ℕ) (R : Polynomial ℤ) (β δ : ℤ) (a0 : ℕ) (u : ℤ) :
    Polynomial.eval u (Gpoly p R β δ a0)
      = ((β - 2 * δ * (a0 : ℤ)) / (p : ℤ) + (Polynomial.hasseDeriv 1 R).eval (a0 : ℤ)) * u
        - δ * u ^ 2
        + (p : ℤ) * (∑ n ∈ Finset.range (R.natDegree - 1),
            (Polynomial.hasseDeriv (n + 2) R).eval (a0 : ℤ) * (p : ℤ) ^ n * u ^ (n + 2)) := by
  simp only [Gpoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_finsetSum]

lemma Gpoly_id (p : ℕ) (R : Polynomial ℤ) (β δ : ℤ) (a0 : ℕ) (u : ℤ)
    (hdiv : (p : ℤ) ∣ β - 2 * δ * (a0 : ℤ)) :
    Polynomial.eval ((a0 : ℤ) + (p : ℤ) * u)
        (Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2 + Polynomial.C (p : ℤ) * R)
      = Polynomial.eval (a0 : ℤ)
          (Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2 + Polynomial.C (p : ℤ) * R)
        + (p : ℤ) ^ 2 * Polynomial.eval u (Gpoly p R β δ a0) := by
  have hpp : (p : ℤ) ^ 2 * ((β - 2 * δ * (a0 : ℤ)) / (p : ℤ)) = (p : ℤ) * (β - 2 * δ * (a0 : ℤ)) := by
    rw [pow_two, mul_assoc, mul_comm (p : ℤ) ((β - 2 * δ * (a0 : ℤ)) / (p : ℤ)),
      Int.ediv_mul_cancel hdiv]
  have hRt := Commons.Algebra.Polynomial.eval_add_eq_sum_hasseDeriv R (a0 : ℤ) ((p : ℤ) * u)
  have htail : ∑ n ∈ Finset.range (R.natDegree + 1),
        Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv n) R) * ((p : ℤ) * u) ^ n
      = Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv 0) R) * ((p : ℤ) * u) ^ 0
        + Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv 1) R) * ((p : ℤ) * u) ^ 1
        + ∑ n ∈ Finset.range (R.natDegree - 1),
            Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv (n + 2)) R) * ((p : ℤ) * u) ^ (n + 2) := by
    rcases Nat.eq_zero_or_pos R.natDegree with hd | hd
    · rw [hd, Finset.sum_range_one]
      have hz : Polynomial.hasseDeriv 1 R = 0 :=
        Polynomial.hasseDeriv_eq_zero_of_lt_natDegree (n := 1) R (by rw [hd]; norm_num)
      rw [show Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv 1) R) * ((p : ℤ) * u) ^ 1 = 0 by
            rw [hz, Polynomial.eval_zero, zero_mul],
        add_zero, Finset.sum_range_zero, add_zero]
    · have hd2 : 2 + (R.natDegree - 1) = R.natDegree + 1 := by omega
      rw [← hd2, Finset.sum_range_add
        (fun n => Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv n) R) * ((p : ℤ) * u) ^ n)
        2 (R.natDegree - 1),
        show ∑ x ∈ Finset.range 2,
              Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv x) R) * ((p : ℤ) * u) ^ x
            = Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv 0) R) * ((p : ℤ) * u) ^ 0
              + Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv 1) R) * ((p : ℤ) * u) ^ 1 by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, Finset.sum_range_succ, Finset.sum_range_one]]
      rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.range (R.natDegree - 1)) => by
        show Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv (2 + x)) R) * ((p : ℤ) * u) ^ (2 + x)
            = Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv (x + 2)) R) * ((p : ℤ) * u) ^ (x + 2)
        rw [Nat.add_comm 2 x])]
  rw [show Polynomial.eval ((a0 : ℤ) + (p : ℤ) * u)
        (Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2 + Polynomial.C (p : ℤ) * R)
      = β * ((a0 : ℤ) + (p : ℤ) * u) - δ * ((a0 : ℤ) + (p : ℤ) * u) ^ 2
        + (p : ℤ) * Polynomial.eval ((a0 : ℤ) + (p : ℤ) * u) R by
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_pow]]
  rw [show Polynomial.eval (a0 : ℤ)
        (Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2 + Polynomial.C (p : ℤ) * R)
      = β * (a0 : ℤ) - δ * (a0 : ℤ) ^ 2 + (p : ℤ) * Polynomial.eval (a0 : ℤ) R by
      simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_pow]]
  rw [hRt, htail, eval_Gpoly, Polynomial.hasseDeriv_zero', Polynomial.hasseDeriv_one]
  simp only [pow_zero, mul_one, pow_one]
  set SS2 : ℤ := ∑ n ∈ Finset.range (R.natDegree - 1),
      Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv (n + 2)) R) * ((p : ℤ) * u) ^ (n + 2) with hSS2
  set SS : ℤ := ∑ n ∈ Finset.range (R.natDegree - 1),
      Polynomial.eval (a0 : ℤ) ((Polynomial.hasseDeriv (n + 2)) R) * (p : ℤ) ^ n * u ^ (n + 2) with hSS
  have hsum : (p : ℤ) * SS2 = (p : ℤ) ^ 3 * SS := by
    rw [hSS2, hSS, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_pow, pow_add]
    ring
  rw [show (p : ℤ) ^ 2 * (((β - 2 * δ * (a0 : ℤ)) / (p : ℤ)
          + Polynomial.eval (a0 : ℤ) (Polynomial.derivative R)) * u - δ * u ^ 2 + (p : ℤ) * SS)
      = (p : ℤ) ^ 2 * (((β - 2 * δ * (a0 : ℤ)) / (p : ℤ)
            + Polynomial.eval (a0 : ℤ) (Polynomial.derivative R)) * u - δ * u ^ 2)
        + (p : ℤ) ^ 3 * SS by ring]
  rw [← hsum]
  rw [show (p : ℤ) ^ 2 * (((β - 2 * δ * (a0 : ℤ)) / (p : ℤ)
          + Polynomial.eval (a0 : ℤ) (Polynomial.derivative R)) * u - δ * u ^ 2)
      = ((p : ℤ) ^ 2 * ((β - 2 * δ * (a0 : ℤ)) / (p : ℤ))
          + (p : ℤ) ^ 2 * Polynomial.eval (a0 : ℤ) (Polynomial.derivative R)) * u
        - (p : ℤ) ^ 2 * δ * u ^ 2 by ring]
  rw [hpp]
  ring

/-- The shape of polynomials in the requested theorem. -/
def IsQuad (p : ℕ) (H : Polynomial ℤ) : Prop :=
  ∃ β δ : ℤ, ∃ R : Polynomial ℤ, ¬ (p : ℤ) ∣ δ ∧
    H = Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2 +
      Polynomial.C (p : ℤ) * R

lemma eval_quad (p β δ : ℤ) (R : Polynomial ℤ) (z : ℤ) :
    Polynomial.eval z (Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2
        + Polynomial.C p * R) = β * z - δ * z ^ 2 + p * Polynomial.eval z R := by
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]

lemma deriv_eval_quad (p β δ : ℤ) (R : Polynomial ℤ) (z : ℤ) :
    Polynomial.eval z (Polynomial.derivative (Polynomial.C β * Polynomial.X
        - Polynomial.C δ * Polynomial.X ^ 2 + Polynomial.C p * R))
      = β - 2 * δ * z + p * Polynomial.eval z (Polynomial.derivative R) := by
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.derivative_X_pow,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_zero]
  ring

/-- The stationary-phase recursion: the Gauss sum over `ZMod (p^N)` equals `p` times the
Gauss sum of a reduced quadratic phase over `ZMod (p^(N-2))`. -/
theorem Tsum_rec (p N : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hN : 2 ≤ N)
    (H : Polynomial ℤ) (β δ : ℤ) (hδ : ¬ (p : ℤ) ∣ δ) (R : Polynomial ℤ)
    (hH : H = Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2
      + Polynomial.C (p : ℤ) * R) :
    ∃ G : Polynomial ℤ, IsQuad p G ∧ ‖Tsum (p ^ N) H‖ = (p : ℝ) * ‖Tsum (p ^ (N - 2)) G‖ := by
  subst hH
  have hpN1 : p ^ N = p * p ^ (N - 1) := by rw [← pow_succ']; congr 1; omega
  have hpN2 : p ^ (N - 1) = p ^ (N - 2) * p := by
    rw [show N - 1 = N - 2 + 1 by omega, pow_succ]
  set Q : Polynomial ℤ := Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2
      + Polynomial.C (p : ℤ) * R with hQ
  set a0 : ℕ := critPt p β δ with ha0
  set G : Polynomial ℤ := Gpoly p R β δ a0 with hGdef
  have hdiv : (p : ℤ) ∣ β - 2 * δ * (a0 : ℤ) := critPt_spec p hp2 β δ hδ
  have hderiv : ∀ z : ℤ, Polynomial.eval z (Polynomial.derivative Q)
      = β - 2 * δ * z + (p : ℤ) * Polynomial.eval z (Polynomial.derivative R) := by
    intro z; rw [hQ]; exact deriv_eval_quad (p : ℤ) β δ R z
  refine ⟨G, ?_, ?_⟩
  · exact ⟨(β - 2 * δ * (a0 : ℤ)) / (p : ℤ) + (Polynomial.hasseDeriv 1 R).eval (a0 : ℤ), δ,
      ∑ n ∈ Finset.range (R.natDegree - 1),
        Polynomial.C ((Polynomial.hasseDeriv (n + 2) R).eval (a0 : ℤ) * (p : ℤ) ^ n)
          * Polynomial.X ^ (n + 2), hδ, by rw [hGdef, Gpoly]⟩
  · have hdvd : ∀ a u : ℕ, (p : ℤ) ∣ Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ))
          (Polynomial.derivative Q) - Polynomial.eval (a : ℤ) (Polynomial.derivative Q) := by
      intro a u
      rw [hderiv, hderiv]
      refine ⟨-2 * δ * (u : ℤ) + (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) (Polynomial.derivative R)
          - Polynomial.eval (a : ℤ) (Polynomial.derivative R)), ?_⟩
      ring
    have hcrit : ∀ a ∈ Finset.range p, ((p : ℤ) ∣ Polynomial.eval (a : ℤ) (Polynomial.derivative Q)
        ↔ a = a0) := by
      intro a ha
      rw [hQ, deriv_eval_quad, ha0]
      rw [show β - 2 * δ * (a : ℤ) + (p : ℤ) * Polynomial.eval (a : ℤ) (Polynomial.derivative R)
          = (β - 2 * δ * (a : ℤ)) + (p : ℤ) * Polynomial.eval (a : ℤ) (Polynomial.derivative R) by ring]
      rw [dvd_add_left (dvd_mul_right (p : ℤ) _)]
      exact critPt_unique p hp2 β δ hδ a (Finset.mem_range.mp ha)
    have hmain : Tsum (p ^ N) Q = (p : ℂ) * E (p ^ N) (Polynomial.eval (a0 : ℤ) Q)
        * Tsum (p ^ (N - 2)) G := by
      rw [Tsum]
      rw [show Finset.range (p ^ N) = Finset.range (p * p ^ (N - 1)) by rw [hpN1]]
      rw [Commons.Algebra.BigOperators.sum_range_mul_eq
        (fun j => E (p ^ N) (Polynomial.eval (j : ℤ) Q)) p (p ^ (N - 1))]
      -- normalise the index `↑(a + p*t)` into `↑a + ↑p * ↑t`
      have hcnv : ∑ a ∈ Finset.range p, ∑ t ∈ Finset.range (p ^ (N - 1)),
            E (p ^ N) (Polynomial.eval ((↑(a + p * t) : ℤ)) Q)
          = ∑ a ∈ Finset.range p, ∑ t ∈ Finset.range (p ^ (N - 1)),
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (t : ℤ)) Q) := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro t ht
        rw [show ((↑(a + p * t) : ℤ)) = (a : ℤ) + (p : ℤ) * (t : ℤ) by push_cast; ring]
      rw [hcnv]
      have h1 : ∀ a : ℕ, ∑ t ∈ Finset.range (p ^ (N - 1)),
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (t : ℤ)) Q)
          = ∑ u ∈ Finset.range (p ^ (N - 2)), ∑ w ∈ Finset.range p,
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (N - 2) * (w : ℤ))) Q) := by
        intro a
        rw [show Finset.range (p ^ (N - 1)) = Finset.range (p ^ (N - 2) * p) by rw [hpN2]]
        rw [Commons.Algebra.BigOperators.sum_range_mul_eq
          (fun t => E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (t : ℤ)) Q)) (p ^ (N - 2)) p]
        apply Finset.sum_congr rfl; intro u hu
        apply Finset.sum_congr rfl; intro w hw
        rw [show ((a : ℤ) + (p : ℤ) * ((↑(u + p ^ (N - 2) * w) : ℤ)))
            = (a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (N - 2) * (w : ℤ)) by push_cast; ring]
      rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.range p) => h1 a)]
      have h2 : ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (N - 2)), ∑ w ∈ Finset.range p,
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * ((u : ℤ) + (p : ℤ) ^ (N - 2) * (w : ℤ))) Q)
          = ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (N - 2)), ∑ w ∈ Finset.range p,
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) Q)
              * E p (w * Polynomial.eval (a : ℤ) (Polynomial.derivative Q)) := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro u hu
        apply Finset.sum_congr rfl; intro w hw
        exact E_taylor p N (by omega) Q a u w (hdvd a u)
      rw [h2]
      have h3 : ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (N - 2)), ∑ w ∈ Finset.range p,
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) Q)
              * E p (w * Polynomial.eval (a : ℤ) (Polynomial.derivative Q))
          = ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (N - 2)),
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) Q)
              * (∑ w ∈ Finset.range p, E p (w * Polynomial.eval (a : ℤ) (Polynomial.derivative Q))) := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro u hu
        rw [Finset.mul_sum]
      rw [h3]
      have h4 : ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (N - 2)),
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) Q)
              * (∑ w ∈ Finset.range p, E p (w * Polynomial.eval (a : ℤ) (Polynomial.derivative Q)))
          = ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (N - 2)),
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) Q)
              * (if (p : ℤ) ∣ Polynomial.eval (a : ℤ) (Polynomial.derivative Q) then (p : ℂ) else 0) := by
        apply Finset.sum_congr rfl; intro a ha
        apply Finset.sum_congr rfl; intro u hu
        rw [orth_sum p (Polynomial.eval (a : ℤ) (Polynomial.derivative Q))]
      rw [h4]
      have h5 : ∑ a ∈ Finset.range p, ∑ u ∈ Finset.range (p ^ (N - 2)),
            E (p ^ N) (Polynomial.eval ((a : ℤ) + (p : ℤ) * (u : ℤ)) Q)
              * (if (p : ℤ) ∣ Polynomial.eval (a : ℤ) (Polynomial.derivative Q) then (p : ℂ) else 0)
          = (∑ u ∈ Finset.range (p ^ (N - 2)),
              E (p ^ N) (Polynomial.eval ((a0 : ℤ) + (p : ℤ) * (u : ℤ)) Q)) * (p : ℂ) := by
        have hlt := critPt_lt p β δ
        rw [Finset.sum_eq_single a0]
        · have hcond : (p : ℤ) ∣ Polynomial.eval (a0 : ℤ) (Polynomial.derivative Q) :=
            (hcrit a0 (Finset.mem_range.mpr hlt)).mpr rfl
          rw [if_pos hcond, Finset.sum_mul]
        · intro b hb hbne
          have hnot : ¬ (p : ℤ) ∣ Polynomial.eval (b : ℤ) (Polynomial.derivative Q) :=
            fun hh => hbne ((hcrit b hb).mp hh)
          rw [if_neg hnot]
          simp
        · intro h; exact absurd (Finset.mem_range.mpr hlt) h
      rw [h5]
      have h6 : ∑ u ∈ Finset.range (p ^ (N - 2)),
            E (p ^ N) (Polynomial.eval ((a0 : ℤ) + (p : ℤ) * (u : ℤ)) Q)
          = E (p ^ N) (Polynomial.eval (a0 : ℤ) Q) * Tsum (p ^ (N - 2)) G := by
        rw [Tsum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        have h1u : Polynomial.eval ((a0 : ℤ) + (p : ℤ) * (u : ℤ)) Q
            = Polynomial.eval (a0 : ℤ) Q + (p : ℤ) ^ 2 * Polynomial.eval (u : ℤ) G := by
          rw [hQ, hGdef]
          exact Gpoly_id p R β δ a0 (u : ℤ) hdiv
        rw [h1u, E_add, E_sq_mul p N hN]
      rw [h6]
      ring
    rw [hmain, norm_mul, norm_mul, E_norm, Complex.norm_natCast]
    ring

/-- The main induction: the complete Gauss sum of a quadratic phase over `ZMod (p^K)` is at
most `2 * p^(K/2)`. -/
theorem Tsum_bound (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (K : ℕ) (H : Polynomial ℤ) (hH : IsQuad p H) :
    ‖Tsum (p ^ K) H‖ ≤ 2 * (p : ℝ) ^ ((K : ℝ) / 2) := by
  revert H
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    intro H hH
    rcases Nat.lt_or_ge K 2 with hK | hK
    · interval_cases K
      · have h1 : Tsum (p ^ 0) H = 1 := by
          change Tsum 1 H = 1
          rw [Tsum, Finset.sum_range_one, E_one]
        rw [h1, show (((0 : ℕ) : ℝ)) / 2 = 0 by norm_num, Real.rpow_zero]
        norm_num
      · obtain ⟨β, δ, R, hδ, rfl⟩ := hH
        simp only [pow_one]
        have hT : Tsum p (Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2
              + Polynomial.C (p : ℤ) * R)
            = ∑ x : ZMod p, ZMod.stdAddChar ((β : ZMod p) * x - (δ : ZMod p) * x ^ 2) := by
          rw [Tsum, zmod_sum_range p (fun x => ZMod.stdAddChar ((β : ZMod p) * x - (δ : ZMod p) * x ^ 2))]
          apply Finset.sum_congr rfl
          intro j hj
          unfold E
          rw [show (((Polynomial.eval (j : ℤ) (Polynomial.C β * Polynomial.X
                - Polynomial.C δ * Polynomial.X ^ 2 + Polynomial.C (p : ℤ) * R) : ℤ)) : ZMod p)
              = (β : ZMod p) * (j : ZMod p) - (δ : ZMod p) * (j : ZMod p) ^ 2 by
            rw [eval_quad]
            push_cast
            rw [ZMod.natCast_self]
            ring]
        rw [hT]
        refine (prime_field_quadratic_bound p hp2 β δ hδ).trans_eq ?_
        rw [Real.sqrt_eq_rpow]
        norm_num
    · obtain ⟨β, δ, R, hδ, hH'⟩ := hH
      obtain ⟨G, hG, hnorm⟩ := Tsum_rec p K hp2 hK H β δ hδ R hH'
      rw [hnorm]
      have hrec := ih (K - 2) (by omega) G hG
      have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
      have hexp : ((K : ℝ)) / 2 = ((((K - 2 : ℕ)) : ℝ)) / 2 + 1 := by
        have h2 : (((K - 2 : ℕ)) : ℝ) = (K : ℝ) - 2 := by
          rw [Nat.cast_sub (show 2 ≤ K by omega)]; norm_num
        rw [h2]; ring
      calc (p : ℝ) * ‖Tsum (p ^ (K - 2)) G‖
          ≤ (p : ℝ) * (2 * (p : ℝ) ^ ((((K - 2 : ℕ)) : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hrec hppos.le
        _ = 2 * (p : ℝ) ^ ((K : ℝ) / 2) := by
            rw [hexp, Real.rpow_add hppos, Real.rpow_one]; ring

/-- **Quadratic Gauss-sum bound over `ZMod (p^K)`.** Let `p` be an odd prime and `K ≥ 1`.
If `H ∈ ℤ[X]` reduces modulo `p` to a genuine quadratic with non-vanishing leading
coefficient, i.e. `H = C β * X - C δ * X ^ 2 + C (p:ℤ) * R` with `p ∤ δ`, then the
complete exponential sum of `H` over `ZMod (p^K)` is at most `2 * p ^ (K/2)`. -/
theorem quadratic_phase_prime_pow (p K : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (H : Polynomial ℤ) (β δ : ℤ) (hδ : ¬ (p : ℤ) ∣ δ) (R : Polynomial ℤ)
    (hH : H = Polynomial.C β * Polynomial.X - Polynomial.C δ * Polynomial.X ^ 2 +
      Polynomial.C (p : ℤ) * R) :
    ‖∑ x : ZMod (p ^ K), Complex.exp (((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (((Polynomial.eval ((x.val : ℕ) : ℤ) H : ℤ) : ℂ))) / ((p ^ K : ℕ) : ℂ))‖
      ≤ 2 * (p : ℝ) ^ ((K : ℝ) / 2) := by
  have hkey : (∑ x : ZMod (p ^ K), Complex.exp (((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (((Polynomial.eval ((x.val : ℕ) : ℤ) H : ℤ) : ℂ))) / ((p ^ K : ℕ) : ℂ)))
      = gsum (p ^ K) H := by
    rw [gsum]
    apply Finset.sum_congr rfl
    intro x _
    have hev : Polynomial.eval₂ (Int.castRingHom (ZMod (p ^ K))) x H
        = (((Polynomial.eval ((x.val : ℕ) : ℤ) H : ℤ)) : ZMod (p ^ K)) := by
      have h1 : (Int.castRingHom (ZMod (p ^ K))) ((x.val : ℕ) : ℤ) = x := by
        rw [show (Int.castRingHom (ZMod (p ^ K))) ((x.val : ℕ) : ℤ)
            = ((x.val : ℕ) : ZMod (p ^ K)) from Int.cast_natCast (x.val)]
        exact ZMod.natCast_zmod_val x
      conv_lhs => rw [← h1]
      exact Polynomial.eval₂_at_apply _ _
    rw [hev, ZMod.stdAddChar_coe]
  rw [hkey, gsum_eq_Tsum (p ^ K) H]
  exact Tsum_bound p hp2 K H ⟨β, δ, R, hδ, hH⟩

end Commons.NumberTheory.GaussSum