import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace NK.RankTheoryDeep

/-- A field which is a `ℚ`-algebra has characteristic zero.

(Used only to know that `2` is invertible and that `-1 ≠ 1`.) -/
lemma charZero_of_algebra_rat (Ω : Type*) [Field Ω] [Algebra ℚ Ω] : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hinj : Function.Injective (algebraMap ℚ Ω) := FaithfulSMul.algebraMap_injective ℚ Ω
  have h : algebraMap ℚ Ω (n : ℚ) = algebraMap ℚ Ω (0 : ℚ) := by simpa using hn
  simpa using hinj h

/-- **The square root of a primitive `2^m`-th root of unity is a primitive `2^(m+1)`-th root
of unity.**  If `y ^ 2 = x` and `x` is a primitive `2^m`-th root of unity with `m ≥ 1`, then
`y` is a primitive `2^(m+1)`-th root of unity.  This is the recursion step of the tower:
`x` has order exactly `2^m`, so `y` has order dividing `2^(m+1)` but not `2^m`. -/
lemma isPrimitiveRoot_of_sq {Ω : Type*} [Field Ω] {m : ℕ} (hm : 1 ≤ m) {x y : Ω}
    (hx : IsPrimitiveRoot x (2^m)) (hy : y^2 = x) :
    IsPrimitiveRoot y (2^(m+1)) := by
  refine IsPrimitiveRoot.mk_of_lt y (by positivity) ?_ ?_
  · rw [pow_succ', pow_mul, hy, hx.pow_eq_one]
  · intro l hl0 hl2 hl1
    -- `y ^ l = 1` forces `x ^ l = 1`, hence `2 ^ m ∣ l`
    have hx1 : x^l = 1 := by
      calc x^l = (y^2)^l := by rw [hy]
        _ = y^(2*l) := (pow_mul y 2 l).symm
        _ = (y^l)^2 := by rw [mul_comm, pow_mul]
        _ = 1 := by rw [hl1, one_pow]
    obtain ⟨c, hc⟩ := hx.dvd_of_pow_eq_one l hx1
    -- and `0 < l < 2 ^ (m+1) = 2 ^ m * 2` pins it down to `l = 2 ^ m`
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have hclt : c < 2 := by
      have h2 : (2:ℕ)^(m+1) = 2^m * 2 := by rw [pow_succ]
      rw [h2, hc] at hl2
      exact (Nat.mul_lt_mul_left (pow_pos (by norm_num) m)).mp hl2
    have hc1 : c = 1 := by omega
    have hl_eq : l = 2^m := by rw [hc, hc1, mul_one]
    have hy1 : y^(2^m) = 1 := hl_eq ▸ hl1
    -- which together with `x = y ^ 2` would make `x ^ (2 ^ (m-1)) = 1`,
    -- contradicting the primitivity of `x`
    have h2m : 2 * 2^(m-1) = (2:ℕ)^m := by
      cases m with
      | zero => omega
      | succ k => simp [pow_succ']
    have hx2 : x^(2^(m-1)) = 1 := by
      calc x^(2^(m-1)) = (y^2)^(2^(m-1)) := by rw [hy]
        _ = y^(2*2^(m-1)) := (pow_mul y 2 (2^(m-1))).symm
        _ = y^(2^m) := by rw [h2m]
        _ = 1 := hy1
    exact (hx.pow_ne_one_of_pos_of_lt (pow_ne_zero _ (by norm_num))
      (Nat.pow_lt_pow_right (by norm_num) (by omega))) hx2

/-- In a field of characteristic zero there is a primitive fourth root of unity `i`:
take a square root of `-1`. -/
lemma exists_primitiveRoot_four (Ω : Type*) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] :
    ∃ i : Ω, IsPrimitiveRoot i 4 := by
  have hneg1 : IsPrimitiveRoot (-1 : Ω) 2 := by
    refine IsPrimitiveRoot.mk_of_lt (-1) (by norm_num) (by norm_num) ?_
    intro l hl0 hl2
    interval_cases l
    norm_num
  obtain ⟨i, hi_sq⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Ω) (n := 2) (by norm_num)
  refine ⟨i, ?_⟩
  have h := isPrimitiveRoot_of_sq (m := 1) le_rfl hneg1 hi_sq
  simpa using h

/-- **A coherent tower of primitive `2`-power roots of unity in a separable closure of `ℚ`.**
There is a sequence `ζ` of elements of `Ω` such that `ζ n` is a primitive `2^(n+2)`-th root of unity
and `ζ (n+1) ^ 2 = ζ n` for all `n` (so the cyclotomic levels `ℚ(ζ n)` are nested). -/
theorem exists_zeta_tower (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsSepClosure ℚ Ω] :
    ∃ ζ : ℕ → Ω, (∀ n : ℕ, IsPrimitiveRoot (ζ n) (2^(n+2))) ∧
      (∀ n : ℕ, (ζ (n+1))^2 = ζ n) := by
  haveI : CharZero Ω := charZero_of_algebra_rat Ω
  -- `ℚ` is perfect, so a separable closure of `ℚ` is an algebraic closure:
  -- every polynomial has a root, in particular square roots exist.
  haveI : IsAlgClosed Ω := by
    haveI : IsAlgClosure ℚ Ω := inferInstance
    exact IsAlgClosure.isAlgClosed ℚ
  obtain ⟨i, hi⟩ := exists_primitiveRoot_four Ω
  have exists_sq : ∀ z : Ω, ∃ w : Ω, w^2 = z := fun z =>
    IsAlgClosed.exists_pow_nat_eq z (n := 2) (by norm_num)
  let sqrt : Ω → Ω := fun z => Classical.choose (exists_sq z)
  have sqrt_sq : ∀ z, (sqrt z)^2 = z := fun z => Classical.choose_spec (exists_sq z)
  -- the tower, by recursion: successive square roots of a primitive `4`-th root
  let ζ : ℕ → Ω := fun n => Nat.rec i (fun _ w => sqrt w) n
  refine ⟨ζ, ?_, ?_⟩
  · intro n
    induction n with
    | zero => simpa [ζ] using hi
    | succ n ih =>
      have hstep : IsPrimitiveRoot (sqrt (ζ n)) (2^((n+2)+1)) :=
        isPrimitiveRoot_of_sq (m := n+2) (by omega) ih (sqrt_sq (ζ n))
      show IsPrimitiveRoot (ζ (n+1)) (2^(n+1+2))
      rw [show ζ (n+1) = sqrt (ζ n) from rfl]
      convert hstep using 2
  · intro n
    show (ζ (n+1))^2 = ζ n
    rw [show ζ (n+1) = sqrt (ζ n) from rfl]
    exact sqrt_sq (ζ n)

end NK.RankTheoryDeep
