import Mathlib
import Submission.Work.L2F.Props.OddSubDefs
import Submission.Work.L2F.Props.toPGL_mem_ker_iff

/-!
# The characteristic of `F` is odd, from a unipotent element in an odd subgroup of `PGL(2,F)`

Let `K ≤ PGL(2,F)` be a subgroup of odd order which contains the image of a unipotent element
`g ∈ SL(2,F)` (a non-scalar matrix which is a scalar plus a nonzero nilpotent).  Then the
characteristic of `F` is an odd prime.

The mathematical content is the following classical fact.

* In characteristic `2` a unipotent element satisfies `g² = 1` modulo scalars, so `toPGL g` has
  order dividing `2`; a nontrivial finite group of odd order has no such element, whence
  `toPGL g = 1`, i.e. `g` is a scalar — contradiction.
* In characteristic `0` the image of a unipotent element in `PGL(2,F)` has *infinite* order:
  writing `g = a·1 + N` with `N ≠ 0`, `N² = 0` and `a ≠ 0`, the identity
  `(a·1 + N)^n = a^n·1 + n a^{n-1} N` shows that `g^n` is a scalar matrix only for `n = 0`
  (`N` would be scalar as well, hence `0`).
* Since a field has characteristic `0` or a prime, and `2` is excluded, the characteristic is an
  odd prime.

The main auxiliary identity (`pow_add_nilpotent_aux`) is the binomial expansion for a square-zero
perturbation of a commuting element, valid in any ring.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

variable {F : Type*} [Field F]

/-- Binomial expansion for a square-zero perturbation of a commuting element: if `y * x = x * y`
and `y * y = 0` then `(x + y)^n = x^n + n • (x^(n-1) * y)` for `n > 0`. -/
theorem pow_add_nilpotent_aux {R : Type*} [Ring R] (x y : R) (hyx : y * x = x * y)
    (hy : y * y = 0) (n : ℕ) (hn : 0 < n) :
    (x + y) ^ n = x ^ n + n • (x ^ (n - 1) * y) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hih : (x + y) ^ k = x ^ k + (k : R) * (x ^ (k - 1) * y) := by
      rw [ih, nsmul_eq_mul]
    have hsp : x ^ (k - 1) * x = x ^ k := by
      rw [← pow_succ]
      congr 1
      omega
    have hZx : (x ^ (k - 1) * y) * x = x ^ k * y := by
      calc (x ^ (k - 1) * y) * x = x ^ (k - 1) * (y * x) := by rw [mul_assoc]
        _ = x ^ (k - 1) * (x * y) := by rw [hyx]
        _ = (x ^ (k - 1) * x) * y := by rw [mul_assoc]
        _ = x ^ k * y := by rw [hsp]
    have hZy : (x ^ (k - 1) * y) * y = 0 := by rw [mul_assoc, hy, mul_zero]
    have hX : x ^ k * x = x ^ (k + 1) := by rw [← pow_succ]
    have key : (x + y) ^ (k + 1) = x ^ (k + 1) + ((k : R) + 1) * (x ^ k * y) := by
      rw [pow_succ, hih]
      calc (x ^ k + (k : R) * (x ^ (k - 1) * y)) * (x + y)
          = x ^ k * x + x ^ k * y + (k : R) * ((x ^ (k - 1) * y) * x)
              + (k : R) * ((x ^ (k - 1) * y) * y) := by noncomm_ring
        _ = x ^ (k + 1) + x ^ k * y + (k : R) * (x ^ k * y) + (k : R) * 0 := by
              rw [hZx, hZy, hX]
        _ = x ^ (k + 1) + ((k : R) + 1) * (x ^ k * y) := by
              rw [mul_zero, add_zero]
              noncomm_ring
    have hlast : ((k : R) + 1) * (x ^ k * y) = (k + 1) • (x ^ k * y) := by
      rw [nsmul_eq_mul]
      congr 1
      rw [Nat.cast_add, Nat.cast_one]
    have hgoal : (x + y) ^ (k + 1) = x ^ (k + 1) + (k + 1) • (x ^ (k + 1 - 1) * y) := by
      rw [show (k + 1 - 1 : ℕ) = k from rfl, key, hlast]
    exact hgoal

/-- A scalar matrix is never unipotent. -/
theorem not_unipotent_of_smul_one {g : Matrix (Fin 2) (Fin 2) F} (c : F)
    (h : g = c • (1 : Matrix (Fin 2) (Fin 2) F)) : ¬ UnipotentMatrix g := by
  rintro ⟨a, hne, hsq⟩
  have hsub : g - a • (1 : Matrix (Fin 2) (Fin 2) F) =
      (c - a) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [h, ← sub_smul]
  rw [hsub] at hsq
  have hsq' : ((c - a) * (c - a)) • (1 : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have h' := hsq
    rw [smul_mul_smul_comm, mul_one] at h'
    exact h'
  have hz : (c - a) * (c - a) = 0 := by
    have h00 := congrFun (congrFun hsq' 0) 0
    simpa using h00
  exact hne (by rw [hsub, mul_self_eq_zero.mp hz, zero_smul])

/-- A power of `a • 1` is `a^n • 1`. -/
theorem smul_one_pow (a : F) (m : ℕ) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F)) ^ m = a ^ m • (1 : Matrix (Fin 2) (Fin 2) F) := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, Matrix.smul_mul, one_mul, smul_smul, ← pow_succ]

/-- **Characteristic two.**  In characteristic `2` the image in `PGL(2,F)` of a unipotent element
of `SL(2,F)` is an involution: `g = a·1 + N` with `N² = 0` gives
`g² = a²·1 + 2·(a·N) = a²·1`, a scalar matrix, hence central in `SL(2,F)`. -/
theorem sq_toPGL_eq_one_of_char_two_aux (h2 : (2 : F) = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (hgu : UnipotentMatrix ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    (Matrix.SpecialLinearGroup.toPGL g) ^ 2 = 1 := by
  obtain ⟨a, -, hsq⟩ := hgu
  set N : Matrix (Fin 2) (Fin 2) F :=
    (g : Matrix (Fin 2) (Fin 2) F) - a • (1 : Matrix (Fin 2) (Fin 2) F) with hN
  have hNsq : N * N = 0 := by rw [hN]; exact hsq
  have hga : (g : Matrix (Fin 2) (Fin 2) F) = a • (1 : Matrix (Fin 2) (Fin 2) F) + N := by
    rw [hN]; abel
  have hcomm : N * (a • (1 : Matrix (Fin 2) (Fin 2) F)) =
      (a • (1 : Matrix (Fin 2) (Fin 2) F)) * N := by
    rw [Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one]
  have hpow := pow_add_nilpotent_aux (a • (1 : Matrix (Fin 2) (Fin 2) F)) N hcomm hNsq 2 (by norm_num)
  have h1' : (a • (1 : Matrix (Fin 2) (Fin 2) F)) ^ 1 * N = a • N := by
    rw [pow_one, Matrix.smul_mul, one_mul]
  have hg2 : (g : Matrix (Fin 2) (Fin 2) F) ^ 2 = a ^ 2 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hga, hpow, smul_one_pow, h1']
    rw [show (2 : ℕ) • (a • N) = (2 : F) • (a • N) from
      (Nat.cast_smul_eq_nsmul F 2 (a • N)).symm, h2, zero_smul, add_zero]
  have hcentral : g ^ 2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, hg2, Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one]
  have hker : Matrix.SpecialLinearGroup.toPGL (g ^ 2) = 1 := by
    rw [← MonoidHom.mem_ker, Matrix.SpecialLinearGroup.toPGL_ker]
    exact hcentral
  rwa [map_pow] at hker

/-- **Characteristic zero.**  In characteristic `0` no nonzero power of the image in `PGL(2,F)` of
a unipotent element of `SL(2,F)` is trivial.

Indeed `g = a·1 + N` with `N ≠ 0`, `N² = 0` and `a ≠ 0` (if `a = 0` then `g² = N² = 0`, so
`1 = det g = 0`).  If `g^n` were scalar for some `n > 0`, then
`(n a^{n-1}) • N = g^n - a^n • 1` is a scalar matrix; squaring and using `N² = 0` gives
`0 = (s·1)² = s²·1`, so `s = 0`, whence `(n a^{n-1}) • N = 0` and `N = 0` since `n a^{n-1} ≠ 0`
in characteristic `0`. -/
theorem false_of_charZero_of_toPGL_pow_eq_one (hCZ : CharZero F)
    (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (hgu : UnipotentMatrix ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (n : ℕ) (hn : 0 < n)
    (hpow : (Matrix.SpecialLinearGroup.toPGL g) ^ n = 1) : False := by
  haveI : CharZero F := hCZ
  obtain ⟨a, hne, hsq⟩ := hgu
  set N : Matrix (Fin 2) (Fin 2) F :=
    (g : Matrix (Fin 2) (Fin 2) F) - a • (1 : Matrix (Fin 2) (Fin 2) F) with hN
  have hNne : N ≠ 0 := by rw [hN]; exact hne
  have hNsq : N * N = 0 := by rw [hN]; exact hsq
  have hga : (g : Matrix (Fin 2) (Fin 2) F) = a • (1 : Matrix (Fin 2) (Fin 2) F) + N := by
    rw [hN]; abel
  -- `a ≠ 0`: otherwise `g = N` is square-zero, contradicting `det g = 1`.
  have ha : a ≠ 0 := by
    intro ha0
    have hg2 : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 0 := by
      have h := hNsq
      rw [hN, ha0, zero_smul, sub_zero] at h
      exact h
    have hdet := congrArg Matrix.det hg2
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, Matrix.det_zero, one_mul] at hdet
    exact one_ne_zero hdet
  have hcomm : N * (a • (1 : Matrix (Fin 2) (Fin 2) F)) =
      (a • (1 : Matrix (Fin 2) (Fin 2) F)) * N := by
    rw [Matrix.mul_smul, Matrix.smul_mul, one_mul, mul_one]
  -- the explicit power formula
  have hpoweq : (g : Matrix (Fin 2) (Fin 2) F) ^ n =
      a ^ n • (1 : Matrix (Fin 2) (Fin 2) F) + ((n : F) * a ^ (n - 1)) • N := by
    have h := pow_add_nilpotent_aux (a • (1 : Matrix (Fin 2) (Fin 2) F)) N hcomm hNsq n hn
    rw [hga, h, smul_one_pow, smul_one_pow, Matrix.smul_mul, one_mul,
      ← Nat.cast_smul_eq_nsmul F n (a ^ (n - 1) • N), smul_smul]
  -- `g ^ n` lies in the centre, hence is `±1`, hence a scalar matrix
  have hker : Matrix.SpecialLinearGroup.toPGL (g ^ n) = 1 := by rw [map_pow, hpow]
  have hcent : g ^ n ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [← Matrix.SpecialLinearGroup.toPGL_ker]
    exact MonoidHom.mem_ker.mpr hker
  obtain ⟨r, hr⟩ : ∃ r : F,
      (g : Matrix (Fin 2) (Fin 2) F) ^ n = r • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rcases (Work.L2F.Props.mem_center_SL2_iff F (g ^ n)).mp hcent with h1 | h1
    · refine ⟨1, ?_⟩
      rw [← Matrix.SpecialLinearGroup.coe_pow, h1, Matrix.SpecialLinearGroup.coe_one, one_smul]
    · refine ⟨-1, ?_⟩
      rw [← Matrix.SpecialLinearGroup.coe_pow, h1,
        show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = (-1 : Matrix (Fin 2) (Fin 2) F) from rfl,
        neg_smul, one_smul]
  -- hence `(n a^{n-1}) • N = (r - a^n) • 1`
  have hkey : ((n : F) * a ^ (n - 1)) • N =
      (r - a ^ n) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h := hr
    rw [hpoweq] at h
    rw [sub_smul, eq_sub_iff_add_eq, add_comm]
    exact h
  have hs : r - a ^ n = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M * M) hkey
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_one, hNsq, smul_zero] at h
    have h00 := congrFun (congrFun h 0) 0
    have h00' : (r - a ^ n) * (r - a ^ n) = 0 := by simpa using h00.symm
    exact mul_self_eq_zero.mp h00'
  have hk : (n : F) * a ^ (n - 1) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) (pow_ne_zero _ ha)
  have hN0 : N = 0 := by
    have h := hkey
    rw [hs, zero_smul] at h
    exact (smul_eq_zero.mp h).resolve_left hk
  exact hNne hN0

/-- Let `K ≤ PGL(2,F)` be a subgroup of odd order containing the image of a unipotent element of
`SL(2,F)`.  Then `F` has odd prime characteristic. -/
theorem charP_odd_of_unipotent_in_pgl (F : Type*) [Field F]
    (K : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) (hodd : Odd (Nat.card K))
    (hu : ∃ g : Matrix.SpecialLinearGroup (Fin 2) F, Matrix.SpecialLinearGroup.toPGL g ∈ K ∧
          Work.L2F.Props.UnipotentMatrix ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) :
    ∃ p : ℕ, Nat.Prime p ∧ CharP F p ∧ p ≠ 2 := by
  obtain ⟨g, hgK, hgu⟩ := hu
  have hord_dvd : orderOf (Matrix.SpecialLinearGroup.toPGL g) ∣ Nat.card K :=
    Subgroup.orderOf_dvd_natCard K hgK
  have hodd_ord : Odd (orderOf (Matrix.SpecialLinearGroup.toPGL g)) :=
    Odd.of_dvd_nat hodd hord_dvd
  have hord_pos : 0 < orderOf (Matrix.SpecialLinearGroup.toPGL g) := by
    obtain ⟨k, hk⟩ := hodd_ord
    omega
  have hpow : (Matrix.SpecialLinearGroup.toPGL g) ^ orderOf (Matrix.SpecialLinearGroup.toPGL g) = 1 :=
    pow_orderOf_eq_one _
  -- Characteristic different from `2`
  have h2 : (2 : F) ≠ 0 := by
    intro h2zero
    have hx2 : (Matrix.SpecialLinearGroup.toPGL g) ^ 2 = 1 :=
      sq_toPGL_eq_one_of_char_two_aux h2zero g hgu
    have hdvdtwo : orderOf (Matrix.SpecialLinearGroup.toPGL g) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr hx2
    have hord1 : orderOf (Matrix.SpecialLinearGroup.toPGL g) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvdtwo with h | h
      · exact h
      · rw [h] at hodd_ord
        obtain ⟨k, hk⟩ := hodd_ord
        omega
    have hx1 : Matrix.SpecialLinearGroup.toPGL g = 1 := orderOf_eq_one_iff.mp hord1
    have hcent : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [← Matrix.SpecialLinearGroup.toPGL_ker]
      exact MonoidHom.mem_ker.mpr hx1
    rcases (Work.L2F.Props.mem_center_SL2_iff F g).mp hcent with hg1 | hgm1
    · exact not_unipotent_of_smul_one 1
        (by rw [hg1, Matrix.SpecialLinearGroup.coe_one, one_smul]) hgu
    · refine not_unipotent_of_smul_one (-1) ?_ hgu
      rw [hgm1, show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = (-1 : Matrix (Fin 2) (Fin 2) F) from rfl, neg_smul, one_smul]
  -- Characteristic different from `0`
  have hnotCZ : ¬ CharZero F := by
    intro hCZ
    exact false_of_charZero_of_toPGL_pow_eq_one hCZ g hgu _ hord_pos hpow
  have hpne2 : ringChar F ≠ 2 := by
    intro hrc2
    haveI : CharP F 2 := hrc2 ▸ (inferInstance : CharP F (ringChar F))
    exact h2 CharTwo.two_eq_zero
  rcases CharP.char_is_prime_or_zero F (ringChar F) with hp | h0
  · exact ⟨ringChar F, hp, inferInstance, hpne2⟩
  · exfalso
    haveI : CharP F 0 := h0 ▸ (inferInstance : CharP F (ringChar F))
    exact hnotCZ ((CharP.charP_zero_iff_charZero F).mp inferInstance)

end Work.L2F.Props.oddsub
