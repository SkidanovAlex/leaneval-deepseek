import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.IsqrtSpec

/-!
# `Work.CNum.NrmSpec` — specification of `nrmUp`, `nrmDn`, `sqUp`, `sqDn`, `ratIv`

`nrmUp x y = sqUp (x*x + y*y)` is the *mantissa* of an upper bound of `‖(x + iy)/SC‖`, and
`nrmDn x y` the corresponding lower bound; `sqUp n = isqrt n + 1`, `sqDn n = isqrt n` use the
binary-search integer square root of `Fx` (specified by `IsqrtSpec`).

Also proved here: `ratIv p q` encloses `p/q`, and the norm identity for the point `(x+iy)/SC`.
-/

namespace Work.CNum

open Work.ANum

lemma toNat_eq_natAbs {a : ℤ} (h : 0 ≤ a) : a.toNat = a.natAbs := by
  exact_mod_cast (by rw [Int.toNat_of_nonneg h, Int.natAbs_of_nonneg h] :
    (a.toNat : ℤ) = (a.natAbs : ℤ))

lemma m2r_nonneg_NrmSpec {n : ℤ} (h : 0 ≤ n) : 0 ≤ m2r n := by
  simp only [m2r]
  exact div_nonneg (by exact_mod_cast h) SC_posR.le

/-! ## The integer square root at mantissa level -/

lemma sqrt_toNat_le_sqUp {n : ℤ} (hn : n.toNat < 2 ^ 70) :
    Real.sqrt (n.toNat : ℝ) ≤ ((isqrt n.toNat : ℤ) : ℝ) + 1 := by
  obtain ⟨-, h2⟩ := IsqrtSpec n.toNat hn
  have h2' : (n.toNat : ℝ) < (((isqrt n.toNat : ℕ) : ℝ) + 1) ^ 2 := by
    have hc : ((isqrt n.toNat : ℕ) : ℝ) + 1 = (((isqrt n.toNat + 1 : ℕ)) : ℝ) := by
      push_cast; ring
    rw [hc, ← Nat.cast_pow]
    exact_mod_cast (by simpa [pow_two] using h2)
  calc Real.sqrt (n.toNat : ℝ) ≤ Real.sqrt ((((isqrt n.toNat : ℕ) : ℝ) + 1) ^ 2) :=
        Real.sqrt_le_sqrt h2'.le
    _ = ((isqrt n.toNat : ℕ) : ℝ) + 1 := Real.sqrt_sq (by positivity)
    _ = ((isqrt n.toNat : ℤ) : ℝ) + 1 := by push_cast; ring

lemma sqDn_le_sqrt_toNat {n : ℤ} (hn : n.toNat < 2 ^ 70) :
    ((isqrt n.toNat : ℤ) : ℝ) ≤ Real.sqrt (n.toNat : ℝ) := by
  obtain ⟨h1, -⟩ := IsqrtSpec n.toNat hn
  have h : ((isqrt n.toNat : ℕ) : ℝ) ≤ Real.sqrt (n.toNat : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ ((isqrt n.toNat : ℕ) : ℝ))]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by simpa [pow_two] using h1))
  simpa using h

/-! ## `nrmUp`, `nrmDn` -/

lemma natAbs_sq_add {x y : ℤ} (hx : Int.natAbs x ≤ 2 ^ 34) (hy : Int.natAbs y ≤ 2 ^ 34) :
    (x * x + y * y).toNat < 2 ^ 70 ∧ (x * x + y * y).toNat = x.natAbs ^ 2 + y.natAbs ^ 2 := by
  have hx0 : 0 ≤ x * x := mul_self_nonneg x
  have hy0 : 0 ≤ y * y := mul_self_nonneg y
  have h5 : ((x * x + y * y).toNat) = x.natAbs ^ 2 + y.natAbs ^ 2 := by
    rw [toNat_eq_natAbs (add_nonneg hx0 hy0),
      Int.natAbs_add_of_nonneg hx0 hy0, Int.natAbs_mul, Int.natAbs_mul, ← pow_two, ← pow_two]
  refine ⟨?_, h5⟩
  rw [h5]
  have hx2 : x.natAbs ^ 2 ≤ (2 ^ 34) ^ 2 := Nat.pow_le_pow_left hx 2
  have hy2 : y.natAbs ^ 2 ≤ (2 ^ 34) ^ 2 := Nat.pow_le_pow_left hy 2
  have : x.natAbs ^ 2 + y.natAbs ^ 2 ≤ 2 ^ 69 := by
    calc x.natAbs ^ 2 + y.natAbs ^ 2 ≤ (2^34)^2 + (2^34)^2 := Nat.add_le_add hx2 hy2
      _ = 2 ^ 69 := by norm_num
  omega

lemma cast_sq_add {x y : ℤ} :
    (((x * x + y * y).toNat : ℕ) : ℝ) = (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
  have h0 : ((x * x + y * y).toNat : ℤ) = x * x + y * y :=
    Int.toNat_of_nonneg (add_nonneg (mul_self_nonneg x) (mul_self_nonneg y))
  have h2 : (((x * x + y * y).toNat : ℤ) : ℝ) = (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
    rw [h0]; push_cast; ring
  rw [← h2]; push_cast; ring

/-- The norm of the mantissa point `(x + iy)/SC`. -/
lemma norm_pt (x y : ℤ) :
    ‖((x : ℝ) + (y : ℝ) * Complex.I) / (SC : ℝ)‖
      = Real.sqrt ((x * x + y * y).toNat : ℝ) / SC := by
  have hS' : ((SC : ℝ) : ℂ) ≠ 0 := by
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt SC_posR) : ((SC:ℝ):ℂ) ≠ 0)
  rw [norm_div]
  have h1 : ‖((x:ℝ) + (y:ℝ) * Complex.I : ℂ)‖ = Real.sqrt ((x:ℝ)^2 + (y:ℝ)^2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; simp
  have h2 : ‖(((SC:ℝ) : ℂ))‖ = (SC:ℝ) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp [Complex.ofReal_re, Complex.ofReal_im, Real.sqrt_sq SC_posR.le]
  rw [h1, h2, ← cast_sq_add]

/-- `nrmUp` is an upper bound of `‖(x + iy)/SC‖`. -/
theorem NrmUpSpec {x y : ℤ} (hx : Int.natAbs x ≤ 2 ^ 34) (hy : Int.natAbs y ≤ 2 ^ 34) :
    ‖((x : ℝ) + (y : ℝ) * Complex.I) / (SC : ℝ)‖ ≤ m2r (nrmUp x y) := by
  obtain ⟨hlt, -⟩ := natAbs_sq_add hx hy
  rw [norm_pt, nrmUp]
  have hval : m2r (sqUp (x * x + y * y)) = (((isqrt (x * x + y * y).toNat : ℤ) : ℝ) + 1) / SC := by
    simp only [sqUp, m2r]; push_cast; ring
  rw [hval, div_le_div_iff_of_pos_right SC_posR]
  exact sqrt_toNat_le_sqUp hlt

/-- `nrmDn` is a lower bound of `‖(x + iy)/SC‖`. -/
theorem NrmDnSpec {x y : ℤ} (hx : Int.natAbs x ≤ 2 ^ 34) (hy : Int.natAbs y ≤ 2 ^ 34) :
    m2r (nrmDn x y) ≤ ‖((x : ℝ) + (y : ℝ) * Complex.I) / (SC : ℝ)‖ := by
  obtain ⟨hlt, -⟩ := natAbs_sq_add hx hy
  rw [norm_pt, nrmDn]
  have hval : m2r (sqDn (x * x + y * y)) = (((isqrt (x * x + y * y).toNat : ℤ) : ℝ)) / SC := by
    simp only [sqDn, m2r]; try push_cast; try ring
  rw [hval, div_le_div_iff_of_pos_right SC_posR]
  exact sqDn_le_sqrt_toNat hlt

/-! ## `ratIv` -/

/-- `a ≤ -⌊-a/b⌋·b` for `b > 0` (the "ceiling" corner of `ratIv`). -/
lemma ediv_neg_mul_ge (a b : ℤ) (hb : 0 < b) : a ≤ (-(Int.ediv (-a) b)) * b := by
  have hem : Int.ediv (-a) b * b + (-a) % b = -a := Int.ediv_mul_add_emod (-a) b
  have hnn : 0 ≤ (-a) % b := Int.emod_nonneg (-a) (ne_of_gt hb)
  have hX : Int.ediv (-a) b * b = -a - (-a) % b := by linarith only [hem]
  rw [neg_mul, hX]
  linarith only [hnn]

/-- `ratIv p q` encloses `p/q` (for `0 < q`). -/
theorem RatIvSpec {p : ℤ} {q : ℕ} (hq : 0 < q) : (ratIv p q).Mem ((p : ℝ) / (q : ℝ)) := by
  have hq0 : (0:ℤ) < (q:ℤ) := by exact_mod_cast hq
  have hqne : (q:ℤ) ≠ 0 := ne_of_gt hq0
  have hqr : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  refine ⟨?_, ?_⟩
  · simp only [ratIv, m2r]
    rw [div_le_div_iff₀ SC_posR hqr]
    have h := Int.ediv_mul_le (p * SC) (b := (q:ℤ)) hqne
    push_cast
    exact_mod_cast h
  · simp only [ratIv, m2r]
    rw [div_le_div_iff₀ hqr SC_posR]
    have h := Int.ediv_mul_le (-(p * SC)) (b := (q:ℤ)) hqne
    have h3z : (p * SC : ℤ) ≤ (-(Int.ediv (-(p*SC)) (q:ℤ))) * (q:ℤ) :=
      ediv_neg_mul_ge (p * SC) (q:ℤ) hq0
    have h2 : ((-(Int.ediv (-(p*SC)) (q:ℤ)) : ℤ) : ℝ)
        = -(((Int.ediv (-(p*SC)) (q:ℤ)) : ℤ) : ℝ) := by push_cast; ring
    rw [h2]
    have hg : ((p:ℝ) * SC) = ((p * SC : ℤ) : ℝ) := by push_cast; ring
    have hr : (-(((Int.ediv (-(p*SC)) (q:ℤ)) : ℤ) : ℝ)) * (q:ℝ)
        = (((-(Int.ediv (-(p*SC)) (q:ℤ))) * (q:ℤ) : ℤ) : ℝ) := by push_cast; ring
    rw [hg, hr]
    exact_mod_cast h3z

end Work.CNum
