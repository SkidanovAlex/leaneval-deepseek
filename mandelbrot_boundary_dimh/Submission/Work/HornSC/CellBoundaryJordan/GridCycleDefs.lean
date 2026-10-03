import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.Defs

/-!
# The polygonal curve of a cyclic grid walk

Given a sequence `u : ℕ → ℤ × ℤ` of lattice points and `k : ℕ`, `gridCurve u k : ℝ → ℂ` is the
polygonal curve through `lpt (u 0), lpt (u 1), …, lpt (u k)` parametrised *with constant speed*:
the edge `adjSeg (u i) (u (i+1))` is traversed for the parameters `t ∈ [i/k, (i+1)/k]`, linearly.

The parametrisation is described by

* `cIdx k t`, the index of the edge containing the parameter `t` (clamped to `k - 1`, so that the
  curve ends exactly at the vertex `u k` at `t = 1`), and
* `cFrac k t`, the position of `t` inside that edge,

which satisfy `t * k = cIdx k t + cFrac k t`.

The main structural lemma is `gridCurve_eq_of_mul_eq`: if `t * k = i + τ` with `0 ≤ τ ≤ 1` and
`i < k`, then `gridCurve u k t` is the affine point of `lpt (u i), lpt (u (i+1))` with parameter
`τ`.
-/

namespace Work.HornSC.CellBoundaryJordan

open Set

noncomputable section

/-- The index of the edge of the walk containing the parameter `t` (`t * k` measures the position
along the curve). It is clamped to `k - 1`, so that the curve ends at the vertex `u k` at `t = 1`. -/
def cIdx (k : ℕ) (t : ℝ) : ℕ := min ⌊t * (k : ℝ)⌋.toNat (k - 1)

/-- The position of the parameter `t` inside its edge, as a fraction of that edge. -/
def cFrac (k : ℕ) (t : ℝ) : ℝ := t * (k : ℝ) - (cIdx k t : ℝ)

/-- The polygonal curve through the lattice points `u 0, u 1, …`, parametrised with constant
speed. -/
def gridCurve (u : ℕ → ℤ × ℤ) (k : ℕ) (t : ℝ) : ℂ :=
  AffineMap.lineMap (lpt (u (cIdx k t))) (lpt (u (cIdx k t + 1))) (cFrac k t)

/-! ## Elementary properties of `cIdx` and `cFrac` -/

lemma cIdx_le (k : ℕ) (t : ℝ) : cIdx k t ≤ k - 1 := min_le_right _ _

lemma cIdx_lt {k : ℕ} (hk : 1 ≤ k) (t : ℝ) : cIdx k t < k :=
  lt_of_le_of_lt (cIdx_le k t) (Nat.sub_lt (lt_of_lt_of_le zero_lt_one hk) zero_lt_one)

/-- The natural-number value of the floor of a real number whose floor is a natural number. -/
lemma toNat_floor_eq {a : ℝ} {i : ℕ} (h : ⌊a⌋ = (i : ℤ)) : ⌊a⌋.toNat = i := by
  have := Int.toNat_of_nonneg (show (0 : ℤ) ≤ ⌊a⌋ by rw [h]; exact Int.natCast_nonneg i)
  rw [h] at this
  omega

lemma cIdx_nonneg_le_floor (k : ℕ) (t : ℝ) : cIdx k t ≤ ⌊t * (k : ℝ)⌋.toNat :=
  min_le_left _ _

lemma cIdx_zero (k : ℕ) : cIdx k 0 = 0 := by rw [cIdx]; norm_num

/-- Rewriting the coefficient of the affine combination. -/
theorem gridCurve_apply (u : ℕ → ℤ × ℤ) (k : ℕ) (t : ℝ) :
    gridCurve u k t =
      (1 - cFrac k t) • lpt (u (cIdx k t)) + cFrac k t • lpt (u (cIdx k t + 1)) :=
  AffineMap.lineMap_apply_module _ _ _

lemma mul_eq_cIdx_add_cFrac (k : ℕ) (t : ℝ) : t * (k : ℝ) = (cIdx k t : ℝ) + cFrac k t := by
  rw [cFrac]; ring

lemma cFrac_nonneg {k : ℕ} {t : ℝ} (ht : 0 ≤ t) : 0 ≤ cFrac k t := by
  have hfloor0 : (0 : ℤ) ≤ ⌊t * (k : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
  have h1 : (cIdx k t : ℕ) ≤ (⌊t * (k : ℝ)⌋).toNat := cIdx_nonneg_le_floor k t
  have h2 : ((⌊t * (k : ℝ)⌋).toNat : ℝ) = (⌊t * (k : ℝ)⌋ : ℝ) := by
    have := Int.toNat_of_nonneg hfloor0
    exact_mod_cast this
  have h3 : ((⌊t * (k : ℝ)⌋ : ℤ) : ℝ) ≤ t * k := by exact_mod_cast Int.floor_le (t * (k : ℝ))
  have h4 : (cIdx k t : ℝ) ≤ ((⌊t * (k : ℝ)⌋).toNat : ℝ) := by exact_mod_cast h1
  rw [cFrac]
  linarith

lemma cFrac_le_one {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    cFrac k t ≤ 1 := by
  rw [cFrac]
  rcases le_total ((⌊t * (k : ℝ)⌋).toNat) (k - 1) with h | h
  · rw [cIdx, min_eq_left h]
    have hcast : (((⌊t * (k : ℝ)⌋).toNat : ℕ) : ℝ) = ((⌊t * (k : ℝ)⌋ : ℤ) : ℝ) := by
      have hf : (0 : ℤ) ≤ ⌊t * (k : ℝ)⌋ := Int.floor_nonneg.mpr (by positivity)
      have := Int.toNat_of_nonneg hf
      exact_mod_cast this
    rw [hcast]
    linarith [Int.lt_floor_add_one (t * (k : ℝ))]
  · rw [cIdx, min_eq_right h]
    have hk' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk]; norm_num
    rw [hk']
    have : t * (k : ℝ) ≤ (k : ℝ) := by nlinarith [ht1, (Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    linarith

/-! ## The curve stays on the edges -/

lemma gridCurve_mem_adjSeg {k : ℕ} (hk : 1 ≤ k) {u : ℕ → ℤ × ℤ} {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : gridCurve u k t ∈ adjSeg (u (cIdx k t)) (u (cIdx k t + 1)) := by
  rw [adjSeg, segment_eq_image_lineMap]
  exact ⟨cFrac k t, ⟨cFrac_nonneg ht0, cFrac_le_one hk ht0 ht1⟩, rfl⟩

/-! ## The parametrisation of a single edge -/

/-- **The parametrisation of the `i`-th edge.**  If `t * k = i + τ` with `0 ≤ τ ≤ 1` and `i < k`,
then `gridCurve u k t` is the point of the segment `[lpt (u i), lpt (u (i+1))]` at parameter
`τ`. -/
theorem gridCurve_eq_of_mul_eq {k : ℕ} (hk : 1 ≤ k) {u : ℕ → ℤ × ℤ} {i : ℕ} (hi : i < k)
    {τ t : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (ht : t * (k : ℝ) = (i : ℝ) + τ) :
    gridCurve u k t = AffineMap.lineMap (lpt (u i)) (lpt (u (i + 1))) τ := by
  rcases lt_or_eq_of_le hτ1 with hτ | rfl
  · have hfloor : ⌊t * (k : ℝ)⌋ = (i : ℤ) := by
      rw [Int.floor_eq_iff]
      exact ⟨by push_cast; linarith, by push_cast; linarith⟩
    have htoNat : (⌊t * (k : ℝ)⌋).toNat = i := toNat_floor_eq hfloor
    have hik : i ≤ k - 1 := by omega
    have hidx : cIdx k t = i := by
      rw [cIdx, htoNat]
      exact min_eq_left hik
    have hfrac : cFrac k t = τ := by
      rw [cFrac, hidx]; push_cast; linarith
    rw [gridCurve, hidx, hfrac]
  · have hfloor : ⌊t * (k : ℝ)⌋ = (i : ℤ) + 1 := by
      rw [Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith
    have htoNat : (⌊t * (k : ℝ)⌋).toNat = i + 1 := toNat_floor_eq hfloor
    rcases lt_or_eq_of_le (show i + 1 ≤ k from hi) with hik | hik
    · have hidx : cIdx k t = i + 1 := by
        rw [cIdx, htoNat]
        exact min_eq_left (by omega)
      have hfrac : cFrac k t = 0 := by
        rw [cFrac, hidx]; push_cast; linarith
      rw [gridCurve, hidx, hfrac, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]
    · have hidx : cIdx k t = i := by
        rw [cIdx, htoNat, ← hik]
        simp
      have hfrac : cFrac k t = 1 := by
        rw [cFrac, hidx]; push_cast; linarith
      rw [gridCurve, hidx, hfrac, AffineMap.lineMap_apply_one]

/-! ## The endpoints of the parametrisation -/

lemma gridCurve_zero {k : ℕ} (hk : 1 ≤ k) (u : ℕ → ℤ × ℤ) : gridCurve u k 0 = lpt (u 0) := by
  have h := gridCurve_eq_of_mul_eq (hk := hk) (u := u) (i := 0) (hi := by omega) (τ := 0) (t := 0)
    (hτ0 := le_rfl) (hτ1 := by norm_num) (ht := by push_cast; ring)
  simpa using h

lemma gridCurve_one {k : ℕ} (hk : 1 ≤ k) (u : ℕ → ℤ × ℤ) : gridCurve u k 1 = lpt (u k) := by
  have h := gridCurve_eq_of_mul_eq (hk := hk) (u := u) (i := k - 1) (hi := by omega) (τ := 1) (t := 1)
    (hτ0 := by norm_num) (hτ1 := le_rfl) (ht := by push_cast [Nat.cast_sub hk]; ring)
  simpa [Nat.sub_add_cancel hk] using h

/-! ## Recovering the parameter from the value -/

lemma IsUnitAdj.ne {u v : ℤ × ℤ} (h : IsUnitAdj u v) : u ≠ v := by
  rintro hEq
  subst hEq
  rcases h with h | h | h | h
  · exact absurd (congrArg Prod.fst h) (by omega)
  · exact absurd (congrArg Prod.fst h) (by omega)
  · exact absurd (congrArg Prod.snd h) (by omega)
  · exact absurd (congrArg Prod.snd h) (by omega)

lemma cFrac_eq_zero_of_gridCurve_eq_left {k : ℕ} {u : ℕ → ℤ × ℤ} {t : ℝ}
    (hne : lpt (u (cIdx k t)) ≠ lpt (u (cIdx k t + 1)))
    (hz : gridCurve u k t = lpt (u (cIdx k t))) : cFrac k t = 0 := by
  have h1 : (1 - cFrac k t) • lpt (u (cIdx k t)) + cFrac k t • lpt (u (cIdx k t + 1))
      = lpt (u (cIdx k t)) := by
    rw [← gridCurve_apply]; exact hz
  have h : cFrac k t • (lpt (u (cIdx k t + 1)) - lpt (u (cIdx k t))) = 0 := by
    have e : (1 - cFrac k t) • lpt (u (cIdx k t)) + cFrac k t • lpt (u (cIdx k t + 1))
          - lpt (u (cIdx k t))
        = cFrac k t • (lpt (u (cIdx k t + 1)) - lpt (u (cIdx k t))) := by module
    rw [← e, h1, sub_self]
  rcases smul_eq_zero.mp h with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0).symm hne

lemma cFrac_eq_one_of_gridCurve_eq_right {k : ℕ} {u : ℕ → ℤ × ℤ} {t : ℝ}
    (hne : lpt (u (cIdx k t)) ≠ lpt (u (cIdx k t + 1)))
    (hz : gridCurve u k t = lpt (u (cIdx k t + 1))) : cFrac k t = 1 := by
  have h1 : (1 - cFrac k t) • lpt (u (cIdx k t)) + cFrac k t • lpt (u (cIdx k t + 1))
      = lpt (u (cIdx k t + 1)) := by
    rw [← gridCurve_apply]; exact hz
  have h : (1 - cFrac k t) • (lpt (u (cIdx k t)) - lpt (u (cIdx k t + 1))) = 0 := by
    have e : (1 - cFrac k t) • lpt (u (cIdx k t)) + cFrac k t • lpt (u (cIdx k t + 1))
          - lpt (u (cIdx k t + 1))
        = (1 - cFrac k t) • (lpt (u (cIdx k t)) - lpt (u (cIdx k t + 1))) := by module
    rw [← e, h1, sub_self]
  rcases smul_eq_zero.mp h with h0 | h0
  · linarith
  · exact absurd (sub_eq_zero.mp h0) hne

/-- If `gridCurve u k t` is the *left* (resp. *right*) endpoint of its own edge, then `t` sits at
the corresponding end of that edge: `t * k = α`. -/
lemma mul_eq_of_gridCurve_eq {k : ℕ} {u : ℕ → ℤ × ℤ} {t : ℝ} {α : ℕ}
    (hα : α = cIdx k t ∨ α = cIdx k t + 1)
    (hne : lpt (u (cIdx k t)) ≠ lpt (u (cIdx k t + 1)))
    (hz : gridCurve u k t = lpt (u α)) : t * (k : ℝ) = (α : ℝ) := by
  rcases hα with hα | hα
  · subst hα
    have hc : cFrac k t = 0 := cFrac_eq_zero_of_gridCurve_eq_left hne hz
    rw [mul_eq_cIdx_add_cFrac, hc, add_zero]
  · subst hα
    have hc : cFrac k t = 1 := cFrac_eq_one_of_gridCurve_eq_right hne hz
    rw [mul_eq_cIdx_add_cFrac, hc]
    push_cast
    ring

/-- Two parameter values in the *same* edge with the same image have the same position. -/
lemma cFrac_eq_of_gridCurve_eq_same {k : ℕ} {u : ℕ → ℤ × ℤ} {s t : ℝ}
    (hidx : cIdx k s = cIdx k t) (hne : lpt (u (cIdx k s)) ≠ lpt (u (cIdx k s + 1)))
    (h : gridCurve u k s = gridCurve u k t) : cFrac k s = cFrac k t := by
  have h' : gridCurve u k s = gridCurve u k t := h
  rw [gridCurve_apply u k s, gridCurve_apply u k t, hidx] at h'
  have hsub : (cFrac k s - cFrac k t) • (lpt (u (cIdx k t + 1)) - lpt (u (cIdx k t))) = 0 := by
    have e : (1 - cFrac k s) • lpt (u (cIdx k t)) + cFrac k s • lpt (u (cIdx k t + 1))
          - ((1 - cFrac k t) • lpt (u (cIdx k t)) + cFrac k t • lpt (u (cIdx k t + 1)))
        = (cFrac k s - cFrac k t) • (lpt (u (cIdx k t + 1)) - lpt (u (cIdx k t))) := by module
    rw [← e, h', sub_self]
  rcases smul_eq_zero.mp hsub with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd (sub_eq_zero.mp h0).symm (by rw [hidx] at hne; exact hne)

/-- Two parameter values in the same edge with the same image are equal. -/
lemma mul_eq_of_gridCurve_eq_same {k : ℕ} {u : ℕ → ℤ × ℤ} {s t : ℝ}
    (hidx : cIdx k s = cIdx k t) (hne : lpt (u (cIdx k s)) ≠ lpt (u (cIdx k s + 1)))
    (h : gridCurve u k s = gridCurve u k t) : s * (k : ℝ) = t * (k : ℝ) := by
  have hcs : cFrac k s = cFrac k t := cFrac_eq_of_gridCurve_eq_same hidx hne h
  rw [mul_eq_cIdx_add_cFrac k s, mul_eq_cIdx_add_cFrac k t, hcs, hidx]

end

end Work.HornSC.CellBoundaryJordan
