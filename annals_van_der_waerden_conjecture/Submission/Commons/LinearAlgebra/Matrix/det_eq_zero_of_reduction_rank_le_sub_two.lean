import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section

open Matrix
open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix

set_option linter.style.haveILetI false

/-! ## Mod-p² matrices whose mod-p reduction has corank at least two

If a square matrix `A` over `ZMod (p ^ 2)` reduces, modulo `p`, to a matrix of rank
`≤ m - 2`, then `det A = 0` in `ZMod (p ^ 2)`.

Strategy: over the field `ZMod p` the reduced matrix can be brought, by invertible
row and column operations, to a block form with at least two zero rows
(`Matrix.exists_rank_normal_form`).  Lifting those two operations to
`ZMod (p ^ 2)` entrywise, we obtain a matrix `B = Ṽ A Ũ` whose reduction has two zero
rows; each entry of those two rows of `B` is therefore divisible by `p`, which forces
`det B` to be divisible by `p²` — i.e. zero in `ZMod (p ^ 2)`.  Since `det Ṽ` and
`det Ũ` reduce to units, they are units of `ZMod (p ^ 2)` and can be cancelled,
yielding `det A = 0`.
-/

variable {p : ℕ} [Fact (Nat.Prime p)]

abbrev Rp (p : ℕ) := ZMod (p ^ 2)
abbrev Kp (p : ℕ) := ZMod p

/-- The reduction map `ZMod (p ^ 2) → ZMod p`. -/
def redφ : Rp p →+* Kp p :=
  ZMod.castHom (show p ∣ p ^ 2 by exact ⟨p, by ring⟩) (Kp p)

lemma hp_ne_zero : p ≠ 0 := Nat.Prime.ne_zero (Fact.out (p := Nat.Prime p))
lemma hp2_ne_zero : p ^ 2 ≠ 0 := pow_ne_zero 2 hp_ne_zero

/-- `p * p = 0` inside `ZMod (p ^ 2)`. -/
lemma hp2_mul : (p : Rp p) * (p : Rp p) = 0 := by
  rw [← pow_two, ← Nat.cast_pow, ZMod.natCast_self]

/-- `redφ` sends the `natCast` of a natural number to that same number modulo `p`. -/
lemma redφ_natCast (a : ℕ) : redφ (a : Rp p) = (a : Kp p) := by
  exact map_natCast redφ a

/-- `redφ` reads off the canonical representative of an element of `ZMod (p ^ 2)`. -/
lemma redφ_val (x : Rp p) : redφ x = (x.val : Kp p) := by
  haveI : NeZero (p ^ 2) := ⟨hp2_ne_zero⟩
  haveI : NeZero p := ⟨hp_ne_zero⟩
  conv_lhs => rw [← (ZMod.natCast_zmod_val x)]
  exact redφ_natCast x.val

/-- Every element of the kernel of `redφ` is a multiple of `p`. -/
lemma exists_mul_of_redφ_eq_zero (x : Rp p) (hx : redφ x = 0) :
    ∃ y : Rp p, x = (p : Rp p) * y := by
  haveI : NeZero (p ^ 2) := ⟨hp2_ne_zero⟩
  haveI : NeZero p := ⟨hp_ne_zero⟩
  have hx' : (x.val : Kp p) = 0 := by
    rw [redφ_val] at hx
    exact hx
  have hdiv : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).mp hx'
  rcases hdiv with ⟨t, ht⟩
  refine ⟨(t : Rp p), ?_⟩
  calc
    x = (x.val : Rp p) := (ZMod.natCast_zmod_val x).symm
    _ = ((p * t : ℕ) : Rp p) := by rw [ht]
    _ = (p : Rp p) * (t : Rp p) := by rw [Nat.cast_mul]

/-- Elements of `ZMod (p ^ 2)` not vanishing modulo `p` are units. -/
lemma isUnit_of_redφ_ne_zero (x : Rp p) (hx : redφ x ≠ 0) : IsUnit x := by
  haveI : NeZero (p ^ 2) := ⟨hp2_ne_zero⟩
  haveI : NeZero p := ⟨hp_ne_zero⟩
  have hx' : (x.val : Kp p) ≠ 0 := by
    intro h
    apply hx
    rw [redφ_val]
    exact h
  have hnd : ¬ p ∣ x.val := by
    intro hd
    exact hx' ((ZMod.natCast_eq_zero_iff x.val p).2 hd)
  have hu : IsUnit (x.val : Rp p) := by
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow (hp := Fact.out (p := Nat.Prime p))
      (hd := by norm_num) (a := x.val)).2 hnd
  have hxeq : x = (x.val : Rp p) := (ZMod.natCast_zmod_val x).symm
  rw [hxeq]
  exact hu

/-- A matrix with two rows consisting of elements of the kernel of `redφ`
has determinant zero in `ZMod (p ^ 2)`. -/
lemma det_eq_zero_of_two_rows_ker {m : ℕ} (B : Matrix (Fin m) (Fin m) (Rp p))
    {i j : Fin m} (hij : i ≠ j)
    (hi : ∀ t, redφ (B i t) = 0) (hj : ∀ t, redφ (B j t) = 0) : B.det = 0 := by
  classical
  let v : Fin m → Rp p := fun t => Classical.choose (exists_mul_of_redφ_eq_zero (B i t) (hi t))
  have hv : ∀ t, B i t = (p : Rp p) * v t := fun t =>
    Classical.choose_spec (exists_mul_of_redφ_eq_zero (B i t) (hi t))
  let w : Fin m → Rp p := fun t => Classical.choose (exists_mul_of_redφ_eq_zero (B j t) (hj t))
  have hw : ∀ t, B j t = (p : Rp p) * w t := fun t =>
    Classical.choose_spec (exists_mul_of_redφ_eq_zero (B j t) (hj t))
  have hrowi : B i = (p : Rp p) • v := funext hv
  have hrowj : B j = (p : Rp p) • w := funext hw
  let B1 := B.updateRow i v
  have hB : B.updateRow i ((p : Rp p) • v) = B := by
    rw [← hrowi]
    exact Matrix.updateRow_eq_self B i
  have hdet1 : B.det = (p : Rp p) * B1.det := by
    rw [← hB, det_updateRow_smul]
  have hrowj1 : B1 j = (p : Rp p) • w := by
    dsimp [B1]
    rw [Matrix.updateRow_ne hij.symm]
    exact hrowj
  let B2 := B1.updateRow j w
  have hB2 : B1.updateRow j ((p : Rp p) • w) = B1 := by
    rw [← hrowj1]
    exact Matrix.updateRow_eq_self B1 j
  have hdet2 : B1.det = (p : Rp p) * B2.det := by
    rw [← hB2, det_updateRow_smul]
  calc
    B.det = (p : Rp p) * ((p : Rp p) * B2.det) := by rw [hdet1, hdet2]
    _ = 0 := by
      rw [← mul_assoc, hp2_mul, zero_mul]

/-- Entrywise lift of `ZMod p` to `ZMod (p ^ 2)` through the canonical representatives. -/
def liftVal (x : Kp p) : Rp p := (x.val : Rp p)

/-- The lift is a section of `redφ`. -/
lemma redφ_liftVal (x : Kp p) : redφ (liftVal x) = x := by
  haveI : NeZero p := ⟨hp_ne_zero⟩
  dsimp [liftVal]
  rw [redφ_natCast x.val]
  exact ZMod.natCast_zmod_val x

/-- Entrywise lifting commutes with the reduction map on matrices. -/
lemma map_liftVal_map_redφ {n : ℕ} (X : Matrix (Fin n) (Fin n) (Kp p)) :
    (X.map liftVal).map redφ = X := by
  rw [Matrix.map_map]
  apply Matrix.ext
  intro i j
  simp [redφ_liftVal]

/-- The determinant is compatible with the reduction map. -/
lemma redφ_det_map {n : ℕ} (X : Matrix (Fin n) (Fin n) (Rp p)) :
    (X.map redφ).det = redφ X.det := by
  exact (RingHom.map_det redφ X).symm

/-- If a square matrix over `ZMod (p ^ 2)` of size `m ≥ 2` has a mod-p reduction of
rank at most `m - 2` (i.e. corank at least two over the field `ZMod p`), then its
determinant vanishes in `ZMod (p ^ 2)`. -/
theorem det_eq_zero_of_reduction_rank_le_sub_two (p : ℕ) [Fact (Nat.Prime p)] (m : ℕ) (hm : 2 ≤ m)
    (A : Matrix (Fin m) (Fin m) (ZMod (p ^ 2)))
    (hrank : Matrix.rank (A.map (ZMod.castHom (show p ∣ p ^ 2 by exact ⟨p, by ring⟩) (ZMod p))) ≤ m - 2) :
    A.det = 0 := by
  classical
  let Ā : Matrix (Fin m) (Fin m) (Kp p) := A.map redφ
  have hr : Ā.rank ≤ m - 2 := by
    simpa [Ā, redφ] using hrank
  -- Normal form of the reduction over the field `ZMod p`:
  -- `V * Ā * U` is the identity on `Fin Ā.rank` and zero elsewhere.
  obtain ⟨V, U, e, hV, hU, hC⟩ := Matrix.exists_rank_normal_form Ā
  let NF : Matrix (Fin m) (Fin m) (Kp p) := (fromBlocks 1 0 0 0).submatrix e e
  have hC' : V * Ā * U = NF := by
    simpa [NF] using hC
  -- Since `Ā.rank ≤ m - 2`, the zero block has size at least two: pick two distinct
  -- rows that are zero in the normal form.
  have hbig : 2 ≤ Fintype.card (Fin m) - Ā.rank := by
    rw [Fintype.card_fin]
    omega
  let X := Fintype.card (Fin m) - Ā.rank
  have hu1lt : 0 < X := by omega
  have hu2lt : 1 < X := by omega
  let u1 : Fin X := ⟨0, hu1lt⟩
  let u2 : Fin X := ⟨1, hu2lt⟩
  have hu12 : u1 ≠ u2 := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
  let i0 : Fin m := e.symm (Sum.inr u1)
  let i1 : Fin m := e.symm (Sum.inr u2)
  have hi01 : i0 ≠ i1 := by
    intro h
    have hc := congrArg e h
    simp [i0, i1] at hc
    exact hu12 hc
  -- The rows `i0` and `i1` of the normal form vanish.
  have hrow0 : ∀ t : Fin m, NF i0 t = 0 := by
    intro t
    cases h : e t with
    | inl a => simp [NF, i0, Matrix.submatrix_apply, h, fromBlocks_apply₂₁]
    | inr b => simp [NF, i0, Matrix.submatrix_apply, h, fromBlocks_apply₂₂]
  have hrow1 : ∀ t : Fin m, NF i1 t = 0 := by
    intro t
    cases h : e t with
    | inl a => simp [NF, i1, Matrix.submatrix_apply, h, fromBlocks_apply₂₁]
    | inr b => simp [NF, i1, Matrix.submatrix_apply, h, fromBlocks_apply₂₂]
  -- Lift `V` and `U` to `ZMod (p ^ 2)` and conjugate `A` by them.
  let B' : Matrix (Fin m) (Fin m) (Rp p) := (V.map liftVal) * A * (U.map liftVal)
  have hφB' : (B'.map redφ) = NF := by
    dsimp [B']
    rw [Matrix.map_mul, Matrix.map_mul, map_liftVal_map_redφ, map_liftVal_map_redφ]
    simpa [Ā, redφ, mul_assoc] using hC' 
  -- The two distinguished rows of `B'` lie in the kernel of `redφ`.
  have hi0ker : ∀ t : Fin m, redφ (B' i0 t) = 0 := by
    intro t
    have h := congrArg (fun M : Matrix (Fin m) (Fin m) (Kp p) => M i0 t) hφB'
    rw [Matrix.map_apply] at h
    rw [hrow0 t] at h
    exact h
  have hi1ker : ∀ t : Fin m, redφ (B' i1 t) = 0 := by
    intro t
    have h := congrArg (fun M : Matrix (Fin m) (Fin m) (Kp p) => M i1 t) hφB'
    rw [Matrix.map_apply] at h
    rw [hrow1 t] at h
    exact h
  have hdetB' : B'.det = 0 := det_eq_zero_of_two_rows_ker B' hi01 hi0ker hi1ker
  -- Relate `det B'` to `det A`.
  let dV : Rp p := (V.map liftVal).det
  let dU : Rp p := (U.map liftVal).det
  have hdet' : B'.det = dV * A.det * dU := by
    dsimp [B', dV, dU]
    rw [det_mul, det_mul]
  have hzero : dV * A.det * dU = 0 := by
    rw [← hdet']
    exact hdetB'
  -- The determinants of the lifted operation matrices are units.
  have hVdetne0 : V.det ≠ 0 := by
    have hd : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
    exact (isUnit_iff_ne_zero.mp hd)
  have hUdetne0 : U.det ≠ 0 := by
    have hd : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
    exact (isUnit_iff_ne_zero.mp hd)
  have hφVne0 : redφ dV ≠ 0 := by
    dsimp [dV]
    rw [← redφ_det_map, map_liftVal_map_redφ V]
    exact hVdetne0
  have hφUne0 : redφ dU ≠ 0 := by
    dsimp [dU]
    rw [← redφ_det_map, map_liftVal_map_redφ U]
    exact hUdetne0
  have hVunit : IsUnit dV := isUnit_of_redφ_ne_zero dV hφVne0
  have hUunit : IsUnit dU := isUnit_of_redφ_ne_zero dU hφUne0
  -- Cancel the two units in `dV * A.det * dU = 0`.
  have hstep : A.det * dU = 0 := by
    have hz' : dV * (A.det * dU) = 0 := by
      simpa [mul_assoc] using hzero
    calc
      A.det * dU = (dV⁻¹ * dV) * (A.det * dU) := by
        rw [ZMod.inv_mul_of_unit dV hVunit, one_mul]
      _ = dV⁻¹ * (dV * (A.det * dU)) := by rw [mul_assoc]
      _ = 0 := by rw [hz', mul_zero]
  calc
    A.det = (A.det * dU) * dU⁻¹ := by
      rw [mul_assoc, ZMod.mul_inv_of_unit dU hUunit, mul_one]
    _ = 0 := by
      rw [hstep, zero_mul]

end Commons.LinearAlgebra.Matrix