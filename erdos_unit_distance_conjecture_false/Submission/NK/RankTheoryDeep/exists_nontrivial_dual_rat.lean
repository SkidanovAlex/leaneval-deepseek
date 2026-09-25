import Mathlib
import Submission.NK.Reconstruct.GammaDual
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.infinite_gamma
import Submission.NK.Reconstruct.ellRestrict_comp
import Submission.NK.RankTheoryDeep.exists_addHom_padicInt_lift
import Submission.NK.RankTheoryDeep.continuous_of_toZModPow_comp
import Submission.NK.RankTheoryDeep.exists_zeta_tower
import Submission.NK.RankTheoryDeep.ne_one_comp_subtype

universe u

namespace NK.RankTheoryDeep

open NK.Reconstruct

set_option linter.style.haveILetI false

/-! ## Part A: the structure of `(ℤ/2^k)^×`, and the discrete logarithm to the base `5`

`ZMod.orderOf_five` (Mathlib, `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`) says that the order of `5`
in `ZMod (2 ^ (n + 2))` is `2 ^ n`; it follows that every unit of `ZMod (2^k)`, `k ≥ 3`, is
*uniquely* of the form `± 5 ^ a` with `0 ≤ a < 2^(k-2)`, and that this gives a surjective
homomorphism `(ZMod (2^k))ˣ →* Multiplicative (ZMod (2^(k-2)))`, compatible with the reductions.

This local copy is *not* used by the main theorem (it is a fallback); the character is constructed
through Mathlib's `PadicInt` limit machinery below.
-/

theorem dvd_four_two_pow {k : ℕ} (hk : 2 ≤ k) : 4 ∣ 2^k :=
  ⟨2^(k-2), by rw [show (4:ℕ) = 2^2 from rfl, ← pow_add, Nat.add_sub_of_le hk]⟩

theorem isUnit_five_zmod (k : ℕ) : IsUnit (5 : ZMod (2^k)) :=
  (ZMod.isUnit_iff_coprime 5 (2^k)).mpr (Nat.Coprime.pow_right k (by norm_num))

theorem orderOf_five_zmod (k : ℕ) (hk : 2 ≤ k) : orderOf (5 : ZMod (2^k)) = 2^(k-2) := by
  have h := ZMod.orderOf_five (k - 2)
  rwa [Nat.sub_add_cancel hk] at h

/-- The sign `±1` as an element of `ZMod (2^k)`. -/
def sgnZ (k : ℕ) (s : Bool) : ZMod (2^k) := if s then -1 else 1

theorem sgnZ_sq (k : ℕ) (s : Bool) : sgnZ k s * sgnZ k s = 1 := by
  unfold sgnZ; cases s <;> simp

theorem sgnZ_isUnit (k : ℕ) (s : Bool) : IsUnit (sgnZ k s) := by
  unfold sgnZ; cases s <;> simp

theorem sgnZ_mul (k : ℕ) (s s' : Bool) : sgnZ k s * sgnZ k s' = sgnZ k (s != s') := by
  unfold sgnZ; cases s <;> cases s' <;> simp

theorem sgnZ_cast_succ (k : ℕ) (s : Bool) :
    ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2^k)) (sgnZ (k+1) s) = sgnZ k s := by
  unfold sgnZ
  cases s <;> simp only [Bool.false_eq_true, if_false, if_true]
  · exact map_one _
  · rw [map_neg, map_one]

theorem sgnZ_cast_four (k : ℕ) (hk : 2 ≤ k) (s : Bool) :
    ZMod.castHom (dvd_four_two_pow hk) (ZMod 4) (sgnZ k s) = sgnZ 2 s := by
  unfold sgnZ
  cases s <;> simp only [Bool.false_eq_true, if_false, if_true]
  · exact map_one _
  · rw [map_neg, map_one]

theorem five_cast_four (k : ℕ) (hk : 2 ≤ k) (a : ℕ) :
    ZMod.castHom (dvd_four_two_pow hk) (ZMod 4) ((5 : ZMod (2^k))^a) = 1 := by
  rw [map_pow]
  have h5 : ZMod.castHom (dvd_four_two_pow hk) (ZMod 4) (5 : ZMod (2^k)) = (1 : ZMod 4) := by
    rw [show (5 : ZMod (2^k)) = ((5 : ℕ) : ZMod (2^k)) from rfl, map_natCast]
    decide
  rw [h5, one_pow]

theorem five_pow_mod (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    (5 : ZMod (2^k))^n = (5 : ZMod (2^k))^(n % 2^(k-2)) := by
  conv_lhs => rw [← Nat.mod_add_div n (2^(k-2))]
  rw [pow_add, pow_mul]
  have h1 : (5 : ZMod (2^k))^(2^(k-2)) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, orderOf_five_zmod k (by omega)]
  rw [h1, one_pow, mul_one]

/-- `5` is compatible with the reduction `ZMod (2^(k+1)) → ZMod (2^k)`. -/
theorem five_cast_succ (k : ℕ) :
    ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2^k)) (5 : ZMod (2^(k+1)))
      = (5 : ZMod (2^k)) := map_ofNat _ 5

/-- The reduction of `±5^b` from `ZMod (2^(k+1))` to `ZMod (2^k)`. -/
theorem cast_sgn_five (k : ℕ) (hk : 3 ≤ k) (s : Bool) (b : ℕ) :
    ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2^k))
        (sgnZ (k+1) s * (5 : ZMod (2^(k+1)))^b)
      = sgnZ k s * (5 : ZMod (2^k))^(b % 2^(k-2)) := by
  rw [map_mul, map_pow, five_cast_succ k, sgnZ_cast_succ k, five_pow_mod k hk]

theorem five_pow_inj {k : ℕ} (hk : 3 ≤ k) {a b : ℕ} (ha : a < 2^(k-2)) (hb : b < 2^(k-2))
    (h : (5 : ZMod (2^k))^a = (5 : ZMod (2^k))^b) : a = b := by
  have key : ∀ c, c < 2^(k-2) → (5 : ZMod (2^k))^c = 1 → c = 0 := by
    intro c hc' hc
    have hdvd : 2^(k-2) ∣ c := by
      have h2 := (orderOf_dvd_iff_pow_eq_one).mpr hc
      rwa [orderOf_five_zmod k (by omega)] at h2
    by_contra hne
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
    omega
  rcases le_total a b with hab | hba
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add] at h
    have hc : (5 : ZMod (2^k))^c = 1 :=
      (((isUnit_five_zmod k).pow a).mul_left_cancel (by rw [mul_one]; exact h)).symm
    have := key c (by omega) hc
    omega
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hba
    rw [pow_add] at h
    have hc : (5 : ZMod (2^k))^c = 1 :=
      (((isUnit_five_zmod k).pow b).mul_left_cancel (by rw [mul_one]; exact h.symm)).symm
    have := key c (by omega) hc
    omega

theorem five_sign_injective (k : ℕ) (hk : 3 ≤ k) {s s' : Bool} {a b : ℕ}
    (ha : a < 2^(k-2)) (hb : b < 2^(k-2))
    (h : sgnZ k s * (5 : ZMod (2^k))^a = sgnZ k s' * (5 : ZMod (2^k))^b) :
    s = s' ∧ a = b := by
  have h4 := congrArg (ZMod.castHom (dvd_four_two_pow (by omega : 2 ≤ k)) (ZMod 4)) h
  rw [map_mul, map_mul, sgnZ_cast_four k (by omega) s, sgnZ_cast_four k (by omega) s',
    five_cast_four k (by omega) a, five_cast_four k (by omega) b, mul_one, mul_one] at h4
  have hs : s = s' := by
    cases s <;> cases s'
    · rfl
    · exact absurd h4 (by decide)
    · exact absurd h4 (by decide)
    · rfl
  subst hs
  exact ⟨rfl, five_pow_inj hk ha hb ((sgnZ_isUnit k s).mul_left_cancel h)⟩

/-- The unit `±5^a` of `ZMod (2^k)`. -/
noncomputable def fiveSignUnit (k : ℕ) (s : Bool) (a : ℕ) : (ZMod (2^k))ˣ :=
  (sgnZ_isUnit k s).unit * ((isUnit_five_zmod k).pow a).unit

theorem fiveSignUnit_coe (k : ℕ) (s : Bool) (a : ℕ) :
    ((fiveSignUnit k s a : (ZMod (2^k))ˣ) : ZMod (2^k)) = sgnZ k s * (5 : ZMod (2^k))^a := by
  simp [fiveSignUnit, IsUnit.unit_spec]

theorem fiveSignUnit_injective (k : ℕ) (hk : 3 ≤ k) :
    Function.Injective (fun p : Bool × Fin (2^(k-2)) => fiveSignUnit k p.1 p.2.val) := by
  intro p q hpq
  have hcoe : sgnZ k p.1 * (5 : ZMod (2^k))^(p.2.val)
      = sgnZ k q.1 * (5 : ZMod (2^k))^(q.2.val) := by
    have h1 := congrArg (fun u : (ZMod (2^k))ˣ => (u : ZMod (2^k))) hpq
    rwa [fiveSignUnit_coe, fiveSignUnit_coe] at h1
  obtain ⟨hs, ha⟩ := five_sign_injective k hk p.2.isLt q.2.isLt hcoe
  exact Prod.ext hs (Fin.ext ha)

/-- **Every unit of `ZMod (2^k)` (`k ≥ 3`) is `±5^a`** for some `a < 2^(k-2)`. -/
theorem exists_five_sign (k : ℕ) (hk : 3 ≤ k) (x : (ZMod (2^k))ˣ) :
    ∃ p : Bool × ℕ, p.2 < 2^(k-2) ∧ (x : ZMod (2^k)) = sgnZ k p.1 * (5 : ZMod (2^k))^(p.2) := by
  classical
  have hcard : Fintype.card ((ZMod (2^k))ˣ) = 2 * 2^(k-2) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]
    have h2 : 2 * 2^(k-2) = 2^(k-1) := by
      rw [← pow_succ' 2 (k-2)]
      congr 1
      omega
    rw [h2]
    norm_num
  have himg : (Finset.univ.image (fun p : Bool × Fin (2^(k-2)) => fiveSignUnit k p.1 p.2.val))
      = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_image_of_injective _ (fiveSignUnit_injective k hk), Finset.card_univ,
      Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    rw [hcard]
  have hx : x ∈ Finset.univ.image (fun p : Bool × Fin (2^(k-2)) => fiveSignUnit k p.1 p.2.val) := by
    rw [himg]; exact Finset.mem_univ x
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hx
  refine ⟨(p.1, p.2.val), p.2.isLt, ?_⟩
  rw [← hp, fiveSignUnit_coe]

/-- The chosen representation of a unit as `±5^a`.  (Proof-free, so that all the statements below
are independent of the particular proof of `3 ≤ k`.) -/
noncomputable def dlogData (k : ℕ) (x : (ZMod (2^k))ˣ) : Bool × ℕ :=
  if hk : 3 ≤ k then Classical.choose (exists_five_sign k hk x) else (false, 0)

theorem dlogData_spec (k : ℕ) (hk : 3 ≤ k) (x : (ZMod (2^k))ˣ) :
    (dlogData k x).2 < 2^(k-2) ∧
      (x : ZMod (2^k)) = sgnZ k (dlogData k x).1 * (5 : ZMod (2^k))^((dlogData k x).2) := by
  rw [dlogData, dif_pos hk]
  exact Classical.choose_spec (exists_five_sign k hk x)

/-- **The discrete logarithm to the base `5`**, modulo the sign: `x = ± 5 ^ (dlog x)`. -/
noncomputable def dlog (k : ℕ) (x : (ZMod (2^k))ˣ) : ZMod (2^(k-2)) :=
  ((dlogData k x).2 : ZMod (2^(k-2)))

theorem dlog_spec (k : ℕ) (hk : 3 ≤ k) (x : (ZMod (2^k))ˣ) :
    (x : ZMod (2^k)) = sgnZ k (dlogData k x).1 * (5 : ZMod (2^k))^(dlog k x).val := by
  rw [dlog, ZMod.val_cast_of_lt (dlogData_spec k hk x).1]
  exact (dlogData_spec k hk x).2

theorem dlog_eq_of {k : ℕ} (hk : 3 ≤ k) {x : (ZMod (2^k))ˣ} {s : Bool} {a : ℕ}
    (ha : a < 2^(k-2)) (h : (x : ZMod (2^k)) = sgnZ k s * (5 : ZMod (2^k))^a) :
    s = (dlogData k x).1 ∧ a = (dlogData k x).2 := by
  refine five_sign_injective k hk ha (dlogData_spec k hk x).1 ?_
  rw [← h, (dlogData_spec k hk x).2]

theorem dlog_mul (k : ℕ) (hk : 3 ≤ k) (x y : (ZMod (2^k))ˣ) :
    dlog k (x * y) = dlog k x + dlog k y := by
  have hm : ((x * y : (ZMod (2^k))ˣ) : ZMod (2^k)) =
      sgnZ k ((dlogData k x).1 != (dlogData k y).1)
        * (5 : ZMod (2^k))^(((dlogData k x).2 + (dlogData k y).2) % 2^(k-2)) := by
    rw [Units.val_mul, (dlogData_spec k hk x).2, (dlogData_spec k hk y).2, mul_mul_mul_comm,
      sgnZ_mul, ← pow_add, five_pow_mod k hk]
  obtain ⟨-, haeq⟩ := dlog_eq_of hk (x := x * y) (s := _) (a := _)
    (Nat.mod_lt _ (by positivity)) hm
  rw [dlog, dlog, dlog, ← haeq, ← Nat.cast_add]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by simp [Nat.mod_mod])

theorem dlog_one (k : ℕ) (hk : 3 ≤ k) : dlog k (1 : (ZMod (2^k))ˣ) = 0 := by
  have h := dlog_eq_of hk (x := (1 : (ZMod (2^k))ˣ)) (s := false) (a := 0) (by positivity)
    (by simp [sgnZ])
  rw [dlog, ← h.2]
  simp

theorem dlog_eq_zero_of_not (k : ℕ) (hk : ¬ 3 ≤ k) (x : (ZMod (2^k))ˣ) : dlog k x = 0 := by
  rw [dlog, dlogData, dif_neg hk]
  simp

/-- **The discrete logarithm as a group homomorphism**
`(ZMod (2^k))ˣ →* Multiplicative (ZMod (2^(k-2)))`.  For `k < 3` this is the trivial homomorphism. -/
noncomputable def dlogHom (k : ℕ) : (ZMod (2^k))ˣ →* Multiplicative (ZMod (2^(k-2))) where
  toFun x := Multiplicative.ofAdd (dlog k x)
  map_one' := by
    by_cases hk : 3 ≤ k
    · rw [dlog_one k hk]; rfl
    · rw [dlog_eq_zero_of_not k hk]; simp
  map_mul' x y := by
    by_cases hk : 3 ≤ k
    · rw [dlog_mul k hk x y]; rfl
    · rw [dlog_eq_zero_of_not k hk x, dlog_eq_zero_of_not k hk y,
        dlog_eq_zero_of_not k hk (x * y)]
      simp

theorem dlog_surjective (k : ℕ) (hk : 3 ≤ k) : Function.Surjective (dlog k) := by
  intro t
  refine ⟨fiveSignUnit k false t.val, ?_⟩
  have h := dlog_eq_of hk (x := fiveSignUnit k false t.val) (s := false) (a := t.val)
    (ZMod.val_lt t) (by rw [fiveSignUnit_coe])
  rw [dlog, ← h.2, ZMod.natCast_zmod_val]

/-- **The units of `ZMod (2^k)` are `±5^a`, and `dlog` is compatible with the reduction.**
This is the single-step form of `dlog_units_map_castHom`. -/
theorem dlog_cast (k : ℕ) (hk : 3 ≤ k) (x : (ZMod (2^(k+1)))ˣ) :
    dlog k (Units.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2^k))).toMonoidHom x)
      = ZMod.castHom (pow_dvd_pow 2 (by omega : k-2 ≤ k+1-2)) (ZMod (2^(k-2)))
          (dlog (k+1) x) := by
  have hk1 : 3 ≤ k+1 := by omega
  have hred : ((Units.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2^k))).toMonoidHom x
      : (ZMod (2^k))ˣ) : ZMod (2^k))
      = sgnZ k (dlogData (k+1) x).1
          * (5 : ZMod (2^k))^((dlogData (k+1) x).2 % 2^(k-2)) := by
    rw [Units.coe_map, (dlogData_spec (k+1) hk1 x).2]
    exact cast_sgn_five k hk (dlogData (k+1) x).1 (dlogData (k+1) x).2
  obtain ⟨-, haeq⟩ := dlog_eq_of hk
      (x := Units.map (ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2^k))).toMonoidHom x)
      (s := (dlogData (k+1) x).1) (a := (dlogData (k+1) x).2 % 2^(k-2))
      (Nat.mod_lt _ (by positivity)) hred
  have hrhs : ZMod.castHom (pow_dvd_pow 2 (by omega : k-2 ≤ k+1-2)) (ZMod (2^(k-2)))
      (dlog (k+1) x) = ((dlogData (k+1) x).2 : ZMod (2^(k-2))) := by
    rw [dlog, ZMod.castHom_apply,
      ZMod.cast_natCast (pow_dvd_pow 2 (by omega : k-2 ≤ k+1-2))]
  rw [hrhs, dlog, ← haeq]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
    (by simp [Nat.mod_mod])

/-- **The reduction of `±5^a` from `ZMod (2^n)` to `ZMod (2^m)`** (for arbitrary `m ∣ n`). -/
theorem castHom_sgn_five {m n : ℕ} (hm : 3 ≤ m) (hd : 2^m ∣ 2^n) (s : Bool) (a : ℕ) :
    ZMod.castHom hd (ZMod (2^m)) (sgnZ n s * (5 : ZMod (2^n))^a)
      = sgnZ m s * (5 : ZMod (2^m))^(a % 2^(m-2)) := by
  rw [map_mul, map_pow]
  congr 1
  · unfold sgnZ
    cases s <;> simp only [Bool.false_eq_true, if_false, if_true]
    · exact map_one _
    · rw [map_neg, map_one]
  · rw [show (ZMod.castHom hd (ZMod (2^m))) (5 : ZMod (2^n)) = (5 : ZMod (2^m)) from
      map_ofNat _ 5, five_pow_mod m hm a]

/-- **`dlog` is compatible with the reductions of the unit groups**, in general form. -/
theorem dlog_units_map_castHom {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (h : m ≤ n)
    (x : (ZMod (2^n))ˣ) :
    dlog m (Units.map (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m))).toMonoidHom x)
      = ZMod.castHom (pow_dvd_pow 2 (by omega : m-2 ≤ n-2)) (ZMod (2^(m-2))) (dlog n x) := by
  set s := (dlogData n x).1 with hs
  set a := (dlogData n x).2 with ha
  have hx : (x : ZMod (2^n)) = sgnZ n s * (5 : ZMod (2^n))^a := (dlogData_spec n hn x).2
  have hred : ((Units.map (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m))).toMonoidHom x
      : (ZMod (2^m))ˣ) : ZMod (2^m)) = sgnZ m s * (5 : ZMod (2^m))^(a % 2^(m-2)) := by
    rw [Units.coe_map, hx]
    exact castHom_sgn_five hm (pow_dvd_pow 2 h) s a
  obtain ⟨-, haeq⟩ := dlog_eq_of hm
    (x := Units.map (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m))).toMonoidHom x)
    (s := s) (a := a % 2^(m-2)) (Nat.mod_lt _ (by positivity)) hred
  have hrhs : ZMod.castHom (pow_dvd_pow 2 (by omega : m-2 ≤ n-2)) (ZMod (2^(m-2))) (dlog n x)
      = ((a : ℕ) : ZMod (2^(m-2))) := by
    rw [dlog, ← ha, ZMod.castHom_apply,
      ZMod.cast_natCast (pow_dvd_pow 2 (by omega : m-2 ≤ n-2))]
  rw [hrhs, dlog, ← haeq]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by simp [Nat.mod_mod])

/-! ## Part B: the cyclotomic tower, its levels, and the level characters -/

section Cyc

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsSepClosure ℚ Ω]

/-- The Galois group of a level, with the algebra structure on the level **pinned** to the
`IntermediateField` structure (otherwise the `ℚ`-specific instances make the types below not match
the ones occurring in the workspace's definitions, such as `levelRestrictHom`). -/
abbrev lvlGal (L : FrobLevel ℚ Ω) : Type _ :=
  @AlgEquiv ℚ (↥L.L) (↥L.L) _ _ _ L.L.algebra' L.L.algebra'

/-- **`ζ m` is a power of `ζ n`** when `m ≤ n`: the levels `ℚ(ζ m)` are nested in `ℚ(ζ n)`. -/
theorem zeta_pow (ζ : ℕ → Ω) (hζsq : ∀ n : ℕ, (ζ (n+1))^2 = ζ n) {m n : ℕ} (hmn : m ≤ n) :
    ζ m = (ζ n) ^ (2 ^ (n - m)) := by
  induction n generalizing m with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp hmn
      simp
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · rw [show 2 ^ (n + 1 - m) = 2 * 2 ^ (n - m) by
            rw [show n + 1 - m = (n - m) + 1 by omega, pow_succ]; ring]
        rw [pow_mul, hζsq n]
        exact ih hmn'
      · have hm : m = n + 1 := by omega
        subst hm
        simp

/-- The cyclotomic level `ℚ(ζ n)` as a finite normal number-field level of `Ω` over `ℚ`. -/
noncomputable def cycL (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) (n : ℕ) :
    FrobLevel ℚ Ω :=
  NK.Reconstruct.cycLevel (K := ℚ) (K' := Ω) 2 (n+2) (ζ n) (hζ n)

theorem cycL_L (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) (n : ℕ) :
    (cycL ζ hζ n).L = IntermediateField.adjoin ℚ ({ζ n} : Set Ω) := rfl

theorem zeta_mem_cycL (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) (n : ℕ) :
    ζ n ∈ (cycL ζ hζ n).L := by
  rw [cycL_L ζ hζ n]
  exact IntermediateField.mem_adjoin_simple_self ℚ (ζ n)

/-- The levels of the tower are nested. -/
theorem cycL_le (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2)))
    (hζsq : ∀ n : ℕ, (ζ (n+1))^2 = ζ n) {m n : ℕ} (hmn : m ≤ n) :
    (cycL ζ hζ m).L ≤ (cycL ζ hζ n).L := by
  rw [cycL_L ζ hζ m, cycL_L ζ hζ n, IntermediateField.adjoin_le_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [zeta_pow ζ hζsq hmn]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ (ζ n)) _

/-- **`ζ n`, viewed in the subfield `ℚ(ζ n)`, is still a primitive `2^(n+2)`-th root of unity.** -/
theorem zeta_cycL_prim (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) (n : ℕ) :
    IsPrimitiveRoot (⟨ζ n, zeta_mem_cycL ζ hζ n⟩ : ↥(cycL ζ hζ n).L) (2^(n+2)) := by
  letI : Algebra ℚ ↥(cycL ζ hζ n).L := (cycL ζ hζ n).L.algebra'
  rw [IsPrimitiveRoot.iff_orderOf]
  rw [← orderOf_injective (f := (algebraMap ↥(cycL ζ hζ n).L Ω).toMonoidHom)
    (fun a b h => Subtype.ext h) ⟨ζ n, zeta_mem_cycL ζ hζ n⟩]
  change orderOf (ζ n : Ω) = 2 ^ (n + 2)
  rw [← IsPrimitiveRoot.iff_orderOf]
  exact hζ n

/-- `autToPow` at a level, with the `Algebra` structure on the level pinned to `algebra'`. -/
noncomputable abbrev autToPowLvl (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2)))
    (n : ℕ) : lvlGal (cycL ζ hζ n) →* (ZMod (2^(n+2)))ˣ :=
  @IsPrimitiveRoot.autToPow ℚ (↥(cycL ζ hζ n).L) _ _ ⟨ζ n, zeta_mem_cycL ζ hζ n⟩ (2^(n+2))
    (zeta_cycL_prim ζ hζ n) _ (cycL ζ hζ n).L.algebra' _

theorem autToPowLvl_spec (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) (n : ℕ)
    (f : lvlGal (cycL ζ hζ n)) :
    (⟨ζ n, zeta_mem_cycL ζ hζ n⟩ : ↥(cycL ζ hζ n).L) ^
        ((autToPowLvl ζ hζ n f : (ZMod (2^(n+2)))ˣ) : ZMod (2^(n+2))).val
      = f ⟨ζ n, zeta_mem_cycL ζ hζ n⟩ :=
  @IsPrimitiveRoot.autToPow_spec ℚ (↥(cycL ζ hζ n).L) _ _ ⟨ζ n, zeta_mem_cycL ζ hζ n⟩ (2^(n+2))
    (zeta_cycL_prim ζ hζ n) _ (cycL ζ hζ n).L.algebra' _ f

/-- **The cyclotomic character at the level `ℚ(ζ n)`**: the action on `ζ n` made additive by the
discrete logarithm `dlog`. -/
noncomputable def cycChar (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) (n : ℕ) :
    lvlGal (cycL ζ hζ n) →* Multiplicative (ZMod (2^n)) :=
  (dlogHom (n+2)).comp (autToPowLvl ζ hζ n)

/-- **The reduction of the `n`-th cyclotomic character to the `m`-th**, for `m ≤ n`. -/
noncomputable def redMul {m n : ℕ} (h : m ≤ n) :
    Multiplicative (ZMod (2^n)) →* Multiplicative (ZMod (2^m)) where
  toFun x := Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m))
    (Multiplicative.toAdd x))
  map_one' := by simp
  map_mul' x y := by
    rw [show Multiplicative.toAdd (x * y) = Multiplicative.toAdd x + Multiplicative.toAdd y
      from rfl, map_add]
    rfl

/-- **Two exponents giving the same power of a primitive root of unity are congruent mod the
order.** -/
theorem pow_eq_pow_mod {M : Type*} [CommMonoid M] {k : ℕ} {μ : M} (hμ : IsPrimitiveRoot μ k)
    (hk : k ≠ 0) {x y : ℕ} (h : μ ^ x = μ ^ y) : x % k = y % k := by
  have hx : μ ^ x = μ ^ (x % k) := by
    conv_lhs => rw [← Nat.mod_add_div x k]
    rw [pow_add, pow_mul, hμ.pow_eq_one, one_pow, mul_one]
  have hy : μ ^ y = μ ^ (y % k) := by
    conv_lhs => rw [← Nat.mod_add_div y k]
    rw [pow_add, pow_mul, hμ.pow_eq_one, one_pow, mul_one]
  rw [hx, hy] at h
  exact hμ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero hk))
    (Nat.mod_lt _ (Nat.pos_of_ne_zero hk)) h

theorem coe_pow_lvl (L : FrobLevel ℚ Ω) (x : ↥L.L) (k : ℕ) :
    (((x ^ k : ↥L.L)) : Ω) = (x : Ω) ^ k := by
  push_cast
  rfl

theorem coe_zeta_cycL (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) (n : ℕ) :
    ((⟨ζ n, zeta_mem_cycL ζ hζ n⟩ : ↥(cycL ζ hζ n).L) : Ω) = ζ n := rfl

theorem coe_zeta_cycL_pow (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2)))
    (n k : ℕ) :
    (((⟨ζ n, zeta_mem_cycL ζ hζ n⟩ : ↥(cycL ζ hζ n).L) ^ k : ↥(cycL ζ hζ n).L) : Ω)
      = (ζ n) ^ k := by
  push_cast
  rfl

/-- **The `autToPow` values of the tower are compatible with the restriction maps.** -/
theorem autToPow_compat (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2)))
    (hζsq : ∀ n : ℕ, (ζ (n+1))^2 = ζ n) {m n : ℕ} (hmn : m ≤ n)
    (σ : lvlGal (cycL ζ hζ n)) :
    autToPowLvl ζ hζ m
        (levelRestrictHom (cycL ζ hζ m) (cycL ζ hζ n) (cycL_le ζ hζ hζsq hmn) σ)
      = Units.map (ZMod.castHom (pow_dvd_pow 2 (by omega : m + 2 ≤ n + 2))
          (ZMod (2^(m+2)))).toMonoidHom (autToPowLvl ζ hζ n σ) := by
  set τ := levelRestrictHom (cycL ζ hζ m) (cycL ζ hζ n) (cycL_le ζ hζ hζsq hmn) σ with hτ
  set b' := autToPowLvl ζ hζ n σ with hb'
  -- the key power identity in the level `ℚ(ζ m)`
  have hpow : (⟨ζ m, zeta_mem_cycL ζ hζ m⟩ : ↥(cycL ζ hζ m).L) ^
        (autToPowLvl ζ hζ m τ : ZMod (2^(m+2))).val
      = (⟨ζ m, zeta_mem_cycL ζ hζ m⟩ : ↥(cycL ζ hζ m).L) ^ (b' : ZMod (2^(n+2))).val := by
    rw [autToPowLvl_spec]
    refine Subtype.ext ?_
    rw [coe_zeta_cycL_pow ζ hζ m (b' : ZMod (2^(n+2))).val]
    have hstep : ((τ ⟨ζ m, zeta_mem_cycL ζ hζ m⟩ : ↥(cycL ζ hζ m).L) : Ω)
        = (ζ m : Ω) ^ (b' : ZMod (2^(n+2))).val := by
      rw [hτ, levelRestrictHom_apply_coe]
      have h2 : (⟨(↑(⟨ζ m, zeta_mem_cycL ζ hζ m⟩ : ↥(cycL ζ hζ m).L) : Ω),
            (cycL_le ζ hζ hζsq hmn) (zeta_mem_cycL ζ hζ m)⟩ : ↥(cycL ζ hζ n).L)
          = (⟨ζ n, zeta_mem_cycL ζ hζ n⟩ : ↥(cycL ζ hζ n).L) ^ (2 ^ (n - m)) := by
        apply Subtype.ext
        rw [coe_pow_lvl, coe_zeta_cycL ζ hζ m, coe_zeta_cycL ζ hζ n]
        exact zeta_pow ζ hζsq hmn
      rw [h2]
      have h3 : (((σ ((⟨ζ n, zeta_mem_cycL ζ hζ n⟩ : ↥(cycL ζ hζ n).L) ^ (2 ^ (n - m))) :
            ↥(cycL ζ hζ n).L) : Ω))
          = (ζ n : Ω) ^ ((b' : ZMod (2^(n+2))).val * 2 ^ (n - m)) := by
        rw [map_pow, coe_pow_lvl]
        rw [show (σ (⟨ζ n, zeta_mem_cycL ζ hζ n⟩ : ↥(cycL ζ hζ n).L) : ↥(cycL ζ hζ n).L)
            = (⟨ζ n, zeta_mem_cycL ζ hζ n⟩ : ↥(cycL ζ hζ n).L) ^ (b' : ZMod (2^(n+2))).val from by
          rw [hb', autToPowLvl_spec]]
        rw [coe_pow_lvl, coe_zeta_cycL, ← pow_mul]
      rw [h3, zeta_pow ζ hζsq hmn, ← pow_mul, mul_comm]
    exact hstep
  have hmod := pow_eq_pow_mod (zeta_cycL_prim ζ hζ m) (by positivity : 2^(m+2) ≠ 0) hpow
  have hval : (autToPowLvl ζ hζ m τ : ZMod (2^(m+2))).val
      = (b' : ZMod (2^(n+2))).val % 2^(m+2) := by
    rw [Nat.mod_eq_of_lt (ZMod.val_lt (autToPowLvl ζ hζ m τ : ZMod (2^(m+2))))] at hmod
    exact hmod
  refine Units.ext ?_
  rw [Units.coe_map, ← ZMod.natCast_zmod_val (autToPowLvl ζ hζ m τ : ZMod (2^(m+2))), hval]
  have hcast : (ZMod.castHom (pow_dvd_pow 2 (by omega : m + 2 ≤ n + 2)) (ZMod (2^(m+2)))
      ((b' : (ZMod (2^(n+2)))ˣ) : ZMod (2^(n+2))))
      = (↑(((b' : (ZMod (2^(n+2)))ˣ) : ZMod (2^(n+2))).val % 2^(m+2)) : ZMod (2^(m+2))) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (Nat.mod_mod _ _).symm
  exact hcast.symm

/-- **The level characters are compatible with the restriction maps.** -/
theorem cycChar_compat (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2)))
    (hζsq : ∀ n : ℕ, (ζ (n+1))^2 = ζ n) {m n : ℕ} (hmn : m ≤ n)
    (σ : lvlGal (cycL ζ hζ n)) :
    cycChar ζ hζ m
        (levelRestrictHom (cycL ζ hζ m) (cycL ζ hζ n) (cycL_le ζ hζ hζsq hmn) σ)
      = redMul hmn (cycChar ζ hζ n σ) := by
  by_cases hm0 : m = 0
  · subst hm0
    haveI : Subsingleton (ZMod (2^0)) := by
      rw [show (2:ℕ)^0 = 1 from rfl]
      exact ⟨Fintype.card_le_one_iff.mp (by rw [ZMod.card 1])⟩
    haveI : Subsingleton (Multiplicative (ZMod (2^0))) :=
      Multiplicative.toAdd.injective.subsingleton
    exact Subsingleton.elim _ _
  · have hkey := autToPow_compat ζ hζ hζsq hmn σ
    show (dlogHom (m+2))
        (autToPowLvl ζ hζ m
          (levelRestrictHom (cycL ζ hζ m) (cycL ζ hζ n) (cycL_le ζ hζ hζsq hmn) σ))
      = redMul hmn ((dlogHom (n+2)) (autToPowLvl ζ hζ n σ))
    rw [hkey]
    show Multiplicative.ofAdd (dlog (m+2) (Units.map (ZMod.castHom
          (pow_dvd_pow 2 (by omega : m + 2 ≤ n + 2)) (ZMod (2^(m+2)))).toMonoidHom
          (autToPowLvl ζ hζ n σ)))
      = Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow 2 hmn) (ZMod (2^m))
          (dlog (n+2) (autToPowLvl ζ hζ n σ)))
    rw [dlog_units_map_castHom (m := m+2) (n := n+2) (by omega) (by omega) (by omega)]
    refine congrArg Multiplicative.ofAdd ?_
    exact congrArg (fun hp => ZMod.castHom hp (ZMod (2^m))
      (dlog (n+2) (autToPowLvl ζ hζ n σ))) (Subsingleton.elim _ _)

end Cyc

/-! ## Part C: the compatible family of characters of `Γ_ℚ`, and the cyclotomic character -/

section Assembly

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- Functoriality of `Abelianization.lift` in the source. -/
theorem abelianization_lift_comp_map {G H A : Type*} [Group G] [Group H] [CommGroup A]
    (f : H →* A) (g : G →* H) :
    (Abelianization.lift f).comp (Abelianization.map g) = Abelianization.lift (f.comp g) := by
  apply Abelianization.hom_ext
  ext x
  simp [MonoidHom.comp_apply]

/-- Functoriality of `Abelianization.lift` in the target. -/
theorem abelianization_lift_comp {G A B : Type*} [Group G] [CommGroup A] [CommGroup B]
    (h : A →* B) (f : G →* A) :
    Abelianization.lift (h.comp f) = h.comp (Abelianization.lift f) := by
  apply Abelianization.hom_ext
  ext x
  simp [MonoidHom.comp_apply]

/-- **The `n`-th character of `Γ_ℚ`**: the composite of the projection to the cyclotomic level
`ℚ(ζ n)`, the induced map on the `2`-parts of the abelianisations, and the level character. -/
noncomputable def gammaChar (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2)))
    (n : ℕ) : Gamma ℚ Ω 2 →* Multiplicative (ZMod (2^n)) :=
  ((Abelianization.lift (cycChar ζ hζ n)).comp
    (LevelEllPart (cycL ζ hζ n).L 2).subtype).comp (Gamma.proj (cycL ζ hζ n))

/-- **The characters of `Γ_ℚ` form a compatible family** for the reductions `ℤ/2^n → ℤ/2^m`. -/
theorem gammaChar_compat (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2)))
    (hζsq : ∀ n : ℕ, (ζ (n+1))^2 = ζ n) {m n : ℕ} (hmn : m ≤ n) (x : Gamma ℚ Ω 2) :
    redMul hmn (gammaChar ζ hζ n x) = gammaChar ζ hζ m x := by
  have hlev : (Abelianization.lift (cycChar ζ hζ m)).comp
        (levelRestrict (cycL ζ hζ m) (cycL ζ hζ n) (cycL_le ζ hζ hζsq hmn))
      = (redMul hmn).comp (Abelianization.lift (cycChar ζ hζ n)) := by
    rw [levelRestrict]
    apply Abelianization.hom_ext
    ext σ
    simpa using cycChar_compat ζ hζ hζsq hmn σ
  have hc := Gamma.proj_compatible (K := ℚ) (K' := Ω) (ℓ := 2) (cycL ζ hζ m) (cycL ζ hζ n)
    (cycL_le ζ hζ hζsq hmn) x
  simp only [gammaChar, MonoidHom.comp_apply]
  have hstep1 : ((LevelEllPart (cycL ζ hζ m).L 2).subtype) ((Gamma.proj (cycL ζ hζ m)) x)
      = levelRestrict (cycL ζ hζ m) (cycL ζ hζ n) (cycL_le ζ hζ hζsq hmn)
          (((LevelEllPart (cycL ζ hζ n).L 2).subtype) ((Gamma.proj (cycL ζ hζ n)) x)) := by
    rw [← hc]
    rfl
  rw [hstep1]
  have hkey := congrFun (congrArg DFunLike.coe hlev)
    (((LevelEllPart (cycL ζ hζ n).L 2).subtype) ((Gamma.proj (cycL ζ hζ n)) x))
  simp only [MonoidHom.comp_apply] at hkey
  rw [hkey]

/-- **`cycChar` is non-trivial at the first level `ℚ(ζ 1) = ℚ(ζ_8)`.** -/
theorem cycChar_one_ne_one (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) :
    cycChar ζ hζ 1 ≠ 1 := by
  intro h1
  haveI hcyc : @IsCyclotomicExtension ({2^(1+2)} : Set ℕ) ℚ (↥(cycL ζ hζ 1).L) _ _
      (cycL ζ hζ 1).L.algebra' :=
    hζ 1 |>.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hinj : Function.Injective (autToPowLvl ζ hζ 1) :=
    @IsPrimitiveRoot.autToPow_injective (2^(1+2)) _ ℚ _ (↥(cycL ζ hζ 1).L)
      ⟨ζ 1, zeta_mem_cycL ζ hζ 1⟩ _ _ (zeta_cycL_prim ζ hζ 1)
      (cycL ζ hζ 1).L.algebra' hcyc
  have hsub : ∀ τ : lvlGal (cycL ζ hζ 1),
      autToPowLvl ζ hζ 1 τ = 1 ∨ autToPowLvl ζ hζ 1 τ = -1 := by
    intro τ
    have h2 : dlogHom 3 (autToPowLvl ζ hζ 1 τ) = 1 := by
      have := congrArg
        (fun (φ : lvlGal (cycL ζ hζ 1) →* Multiplicative (ZMod (2^1))) => φ τ) h1
      simpa [cycChar] using this
    have hd : dlog 3 (autToPowLvl ζ hζ 1 τ) = 0 := by
      have := congrArg Multiplicative.toAdd h2
      simpa [dlogHom] using this
    have hspec := dlog_spec 3 (by norm_num) (autToPowLvl ζ hζ 1 τ)
    rw [hd] at hspec
    simp only [ZMod.val_zero, pow_zero, mul_one] at hspec
    rcases hb : (dlogData 3 (autToPowLvl ζ hζ 1 τ)).1 with _ | _
    · left
      apply Units.ext
      simpa [hb, sgnZ] using hspec
    · right
      apply Units.ext
      simpa [hb, sgnZ] using hspec
  -- `Gal(ℚ(ζ_8)/ℚ) ≅ (ℤ/8)^×` has order `4`
  have hcard : 4 ≤ Nat.card (lvlGal (cycL ζ hζ 1)) := by
    have h4 : Nat.card (lvlGal (cycL ζ hζ 1)) = 4 := by
      haveI : NeZero (2^(1+2)) := ⟨by positivity⟩
      let i₂ : Algebra ℚ (↥(cycL ζ hζ 1).L) := (cycL ζ hζ 1).L.algebra'
      have hcyc₂ : @IsCyclotomicExtension ({2^(1+2)} : Set ℕ) ℚ (↥(cycL ζ hζ 1).L) _ _
          i₂ := hcyc
      have heq : (@AlgEquiv ℚ (↥(cycL ζ hζ 1).L) (↥(cycL ζ hζ 1).L) _ _ _ i₂ i₂) ≃*
          (ZMod (2^(1+2)))ˣ :=
        @IsCyclotomicExtension.autEquivPow (2^(1+2)) _ ℚ _ (↥(cycL ζ hζ 1).L) _ _ i₂ hcyc₂
          (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (2^(1+2))))
      have hmain : Nat.card (@AlgEquiv ℚ (↥(cycL ζ hζ 1).L) (↥(cycL ζ hζ 1).L) _ _ _ i₂ i₂)
          = 4 := by
        rw [Nat.card_congr heq.toEquiv, Nat.card_eq_fintype_card,
          ZMod.card_units_eq_totient (2^(1+2)),
          Nat.totient_prime_pow Nat.prime_two (by norm_num : 0 < 1 + 2)]
        norm_num
      exact hmain
    omega
  have himg : 4 ≤ Nat.card (Set.range (autToPowLvl ζ hζ 1)) := by
    rw [← Nat.card_congr (Equiv.ofInjective _ hinj)]
    exact hcard
  have hsub2 : Set.range (autToPowLvl ζ hζ 1) ⊆ ({1, -1} : Set ((ZMod (2^3))ˣ)) := by
    rintro _ ⟨τ, rfl⟩
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hsub τ
  have hle : Nat.card (Set.range (autToPowLvl ζ hζ 1)) ≤ 2 := by
    have h2 : Nat.card ↥({1, -1} : Set ((ZMod (2^3))ˣ)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : Set.range (autToPowLvl ζ hζ 1) =>
        (⟨x.1, hsub2 x.2⟩ : ↥({1, -1} : Set ((ZMod (2^3))ˣ))))
      (fun a b hab => Subtype.ext
        (congrArg (fun z : ↥({1, -1} : Set ((ZMod (2^3))ˣ)) => (z : (ZMod (2^3))ˣ)) hab)))
      (le_of_eq h2)
  omega

/-- **The characters of `Γ_ℚ` at `n = 1` are non-trivial.** -/
theorem gammaChar_one_ne_one (ζ : ℕ → Ω) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) :
    gammaChar ζ hζ 1 ≠ 1 := by
  have hlift : (Abelianization.lift (cycChar ζ hζ 1)).comp
      (LevelEllPart (cycL ζ hζ 1).L 2).subtype ≠ 1 := by
    refine ne_one_comp_subtype (LevelEllPart (cycL ζ hζ 1).L 2)
      (coprime_card_ellPart_quotient (A := LevelAbelianization (cycL ζ hζ 1).L) 2)
      ⟨1, by
        have h : Nat.card (Multiplicative (ZMod (2^1))) = 2 := by
          rw [Nat.card_eq_fintype_card]
          exact ZMod.card 2
        simpa using h⟩
      (Abelianization.lift (cycChar ζ hζ 1)) ?_
    intro hc
    refine cycChar_one_ne_one ζ hζ ?_
    have h1 : Abelianization.lift (1 : lvlGal (cycL ζ hζ 1) →*
        Multiplicative (ZMod (2^1))) = 1 := by
      apply Abelianization.hom_ext
      ext x
      simp
    exact Equiv.injective Abelianization.lift (hc.trans h1.symm)
  intro h
  refine hlift (MonoidHom.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := proj_surjective (K := ℚ) (K' := Ω) 2 (cycL ζ hζ 1) y
  have := congrArg (fun (φ : Gamma ℚ Ω 2 →* Multiplicative (ZMod (2^1))) => φ x) h
  simpa [gammaChar, MonoidHom.comp_apply] using this

/-- **`Γ_ℚ` has a non-zero continuous character into `ℤ_2`** — the cyclotomic character.

The character is assembled from the compatible family
`gammaChar ζ hζ n : Γ_ℚ →* (ℤ/2^n)^×` (the `n`-th level of the cyclotomic tower `ℚ(ζ_{2^{n+2}})`),
which is compatible with the reductions `ℤ/2^n → ℤ/2^m` (`gammaChar_compat`), together with the
additive universal property of `ℤ_2 = lim_n ℤ/2^n` (`exists_addHom_padicInt_lift`).  It is non-zero
because its first component is non-trivial (`gammaChar_one_ne_one`), and continuous by
`continuous_of_toZModPow_comp`, the level projections being continuous
(`NK.Reconstruct.continuous_proj`) out of a discrete finite level. -/
theorem exists_nontrivial_dual_rat (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] :
    ∃ χ : NK.Reconstruct.Dual (NK.Reconstruct.Gamma ℚ Ω 2) 2, χ ≠ 0 := by
  obtain ⟨ζ, hζ, hζsq⟩ := exists_zeta_tower Ω
  -- the compatible family of additive characters of `Γ_ℚ` at the finite levels
  let F : ∀ n : ℕ, Additive (Gamma ℚ Ω 2) →+ ZMod (2^n) :=
    fun n => MonoidHom.toAdditiveLeft (gammaChar ζ hζ n)
  have hFval (n : ℕ) (x : Additive (Gamma ℚ Ω 2)) : F n x = gammaChar ζ hζ n x := rfl
  have hF : ∀ (m n : ℕ) (h : m ≤ n) (x : Additive (Gamma ℚ Ω 2)),
      F m x = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m)) (F n x) := by
    intro m n h x
    show gammaChar ζ hζ m x
      = ZMod.castHom (pow_dvd_pow 2 h) (ZMod (2^m)) (gammaChar ζ hζ n x)
    exact (gammaChar_compat ζ hζ hζsq h x).symm
  obtain ⟨g, hg⟩ := exists_addHom_padicInt_lift F hF
  -- each `F n` is continuous (its target is a discrete finite level); hence so is the limit
  have hcont : Continuous ⇑g := by
    refine continuous_of_toZModPow_comp g F (fun n => ?_) hg
    have hdisc : Continuous (fun y : LevelEllPart (cycL ζ hζ n).L 2 =>
        (Abelianization.lift (cycChar ζ hζ n))
          ((LevelEllPart (cycL ζ hζ n).L 2).subtype y)) :=
      continuous_of_discreteTopology
    have hproj : Continuous ⇑(Gamma.proj (K := ℚ) (K' := Ω) (ℓ := 2) (cycL ζ hζ n)) :=
      continuous_proj 2 (cycL ζ hζ n)
    have hcomp := hdisc.comp hproj
    have hFeq : ⇑(F n) = (fun y : LevelEllPart (cycL ζ hζ n).L 2 =>
        (Abelianization.lift (cycChar ζ hζ n))
          ((LevelEllPart (cycL ζ hζ n).L 2).subtype y)) ∘
          ⇑(Gamma.proj (K := ℚ) (K' := Ω) (ℓ := 2) (cycL ζ hζ n)) := rfl
    rw [hFeq]
    exact hcomp
  -- non-vanishing: the first level character is non-trivial
  have hF1 : F 1 ≠ 0 := by
    intro h
    refine gammaChar_one_ne_one ζ hζ (MonoidHom.ext fun x => ?_)
    exact DFunLike.congr_fun h x
  have hg0 : g ≠ 0 := by
    intro h0
    refine hF1 (AddMonoidHom.ext fun x => ?_)
    have hx := hg 1 x
    rw [h0] at hx
    simpa using hx.symm
  refine ⟨⟨g, hcont⟩, fun h => hg0 ?_⟩
  have h1 := congrArg (fun u : Dual (Gamma ℚ Ω 2) 2 => Subtype.val u) h
  simpa using h1

end Assembly

end NK.RankTheoryDeep
