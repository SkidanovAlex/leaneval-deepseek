import Mathlib
import Submission.Work.FIArea2.R6.WCbasicDefs

/-!
# `FIArea2/R6/wc_minVec_and_parallel` — a shortest nonzero vector of `L = {w : c ∣ A w₁ - B w₂}`

For `c, A ≥ 1` the lattice `L = wcInL c A B` of `ℤ²` contains nonzero vectors (e.g. `(c, 0)`, since
`c ∣ A·c`), so `wcSup` attains a nonzero minimum on `L`; pick `v` attaining it. The main content of
this file is that a lattice vector `z` *parallel* to the shortest vector `v` (`wcDet v z = 0`) must be
an integral multiple of `v`: the lattice points on the line `ℚv` form a subgroup of `ℤv ⊆ ℚv`, and if
`v/m` were such a point with `m ≥ 2`, its sup-norm `wcSup v / m` would contradict minimality of `v`.

The formalised argument is the Euclidean one: choose a coordinate `i` with `|v_i| = wcSup v`, put
`q = z_i / v_i` and `u = z - q·v`. Then `u ∈ L`, `wcDet v u = 0` forces `|u_j| ≤ |u_i|`, and
`u_i = z_i % v_i` has `|u_i| < |v_i| = wcSup v`; minimality of `v` then forces `u = 0`, i.e.
`z = q·v`.

The auxiliary lemmas below are `private`: the proof given here is self-contained, resting only on
`Mathlib` and the definitions of `Submission/Work/FIArea2/R6/WCbasicDefs.lean`.
-/

namespace Work.FIArea2.R6

open Finset

/-- `w ∈ wcBox t ↔ wcSup w ≤ t`. -/
private lemma wcBox_mem_iff' (t : ℕ) (w : ℤ × ℤ) : w ∈ wcBox t ↔ wcSup w ≤ t := by
  have key : ∀ a : ℤ, a.natAbs ≤ t ↔ -((t : ℤ)) ≤ a ∧ a ≤ (t : ℤ) := by
    intro a
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]
  simp only [wcBox, Finset.mem_product, Finset.mem_Icc, wcSup]
  rw [max_le_iff]
  exact ⟨fun ⟨h1, h2⟩ => ⟨(key w.1).mpr h1, (key w.2).mpr h2⟩,
    fun ⟨h1, h2⟩ => ⟨(key w.1).mp h1, (key w.2).mp h2⟩⟩

/-- A nonzero integer vector has positive sup-norm. -/
private lemma wcSup_pos' (w : ℤ × ℤ) (h : w ≠ 0) : 0 < wcSup w := by
  have h1 : w.1 ≠ 0 ∨ w.2 ≠ 0 := by
    rcases eq_or_ne w.1 0 with h1 | h1
    · rcases eq_or_ne w.2 0 with h2 | h2
      · exact absurd (Prod.ext h1 h2) h
      · exact Or.inr h2
    · exact Or.inl h1
  rcases h1 with h1 | h1
  · exact lt_of_lt_of_le (Int.natAbs_pos.mpr h1) (le_max_left _ _)
  · exact lt_of_lt_of_le (Int.natAbs_pos.mpr h1) (le_max_right _ _)

/-- `L = wcInL c A B` is closed under subtracting an integer multiple of one of its elements. -/
private lemma wcInL_sub_smul' (c A B : ℕ) {z v : ℤ × ℤ} (hz : wcInL c A B z)
    (hv : wcInL c A B v) (q : ℤ) : wcInL c A B (z.1 - q * v.1, z.2 - q * v.2) := by
  have hz' : (c : ℤ) ∣ (A : ℤ) * z.1 - (B : ℤ) * z.2 := hz
  have hv' : (c : ℤ) ∣ (A : ℤ) * v.1 - (B : ℤ) * v.2 := hv
  have hid : (A : ℤ) * (z.1 - q * v.1) - (B : ℤ) * (z.2 - q * v.2)
      = ((A : ℤ) * z.1 - (B : ℤ) * z.2) - q * ((A : ℤ) * v.1 - (B : ℤ) * v.2) := by
    ring
  show (c : ℤ) ∣ (A : ℤ) * (z.1 - q * v.1) - (B : ℤ) * (z.2 - q * v.2)
  rw [hid]
  exact dvd_sub hz' (dvd_mul_of_dvd_right hv' q)

/-- `(c, 0)` is a nonzero element of `L = wcInL c A B` (as `c ∣ A · c`). -/
private lemma wc_c_zero_mem' (c A B : ℕ) (hc : 1 ≤ c) :
    wcInL c A B ((c : ℤ), 0) ∧ ((c : ℤ), (0 : ℤ)) ≠ 0 := by
  have hdiv : c ∣ A * c := dvd_mul_left c A
  constructor
  · show (c : ℤ) ∣ (A : ℤ) * (c : ℤ) - (B : ℤ) * 0
    rw [mul_zero, sub_zero]
    exact_mod_cast hdiv
  · intro h
    have h1 : (c : ℤ) = 0 := by simpa using congrArg Prod.fst h
    have h2 : c = 0 := by exact_mod_cast h1
    omega

/-- **Existence of a shortest nonzero vector of `L = {w : c ∣ A w₁ - B w₂}`.** -/
private theorem wc_minVec_exists' (c A B : ℕ) (_hA : 1 ≤ A) (hc : 1 ≤ c) :
    ∃ v : ℤ × ℤ,
      wcInL c A B v ∧ v ≠ 0 ∧
      (∀ w : ℤ × ℤ, wcInL c A B w → w ≠ 0 → wcSup v ≤ wcSup w) := by
  obtain ⟨hL, h0⟩ := wc_c_zero_mem' c A B hc
  set S : Finset (ℤ × ℤ) := (wcBox c).filter (fun w => wcInL c A B w ∧ w ≠ 0) with hS
  have hmemS : ((c : ℤ), (0 : ℤ)) ∈ S := by
    rw [hS]
    simp only [Finset.mem_filter, wcBox_mem_iff']
    refine ⟨?_, hL, h0⟩
    have hcast : (c : ℤ).natAbs = c := Int.natAbs_natCast c
    simp only [wcSup, Int.natAbs_zero, hcast]
    exact max_le le_rfl (Nat.zero_le c)
  obtain ⟨v, hvmem, hmin⟩ :=
    Finset.exists_min_image (β := ℤ × ℤ) (α := ℕ) S wcSup ⟨_, hmemS⟩
  rw [hS] at hvmem
  simp only [Finset.mem_filter, wcBox_mem_iff'] at hvmem
  obtain ⟨hvle, hvL, hv0'⟩ := hvmem
  refine ⟨v, hvL, hv0', fun w hwL hw0 => ?_⟩
  by_cases h : wcSup w ≤ c
  · exact hmin w (by rw [hS]; simp only [Finset.mem_filter, wcBox_mem_iff']; exact ⟨h, hwL, hw0⟩)
  · exact le_trans hvle (le_of_lt (lt_of_not_ge h))

/-- **Division step (first coordinate).** -/
private theorem wc_div_step_fst' (v z : ℤ × ℤ) (hv0 : v ≠ 0) (hv1 : v.1.natAbs = wcSup v)
    (hdet : wcDet v z = 0) :
    wcSup (z.1 - (z.1 / v.1) * v.1, z.2 - (z.1 / v.1) * v.2) < wcSup v := by
  have hv1ne : v.1 ≠ 0 := by
    intro h
    have hz : wcSup v = 0 := by
      have h' := hv1.symm
      rw [h] at h'
      simpa [wcSup] using h'
    exact absurd (wcSup_pos' v hv0) (by rw [hz]; omega)
  set q : ℤ := z.1 / v.1 with hq
  have hu1 : z.1 - q * v.1 = z.1 % v.1 := by
    rw [hq, Int.emod_def]
    ring
  have hmax2 : v.2.natAbs ≤ wcSup v := by simp only [wcSup]; exact le_max_right _ _
  have hlt1 : (z.1 - q * v.1).natAbs < wcSup v := by
    rw [hu1, ← hv1]
    have h1 : 0 ≤ z.1 % v.1 := Int.emod_nonneg _ hv1ne
    have h2 : z.1 % v.1 < ((v.1.natAbs : ℕ) : ℤ) := by simpa using Int.emod_lt_abs _ hv1ne
    have hlt := Int.natAbs_lt_natAbs_of_nonneg_of_lt h1 h2
    rw [Int.natAbs_natCast] at hlt
    exact hlt
  have hpar : v.1 * (z.2 - q * v.2) = v.2 * (z.1 - q * v.1) := by
    have hd : v.1 * z.2 = v.2 * z.1 := by
      have hh : v.1 * z.2 - v.2 * z.1 = 0 := hdet
      linarith
    rw [mul_sub, mul_sub, hd]
    ring
  have hmul : v.1.natAbs * (z.2 - q * v.2).natAbs = v.2.natAbs * (z.1 - q * v.1).natAbs := by
    have hh := congrArg Int.natAbs hpar
    simpa [Int.natAbs_mul] using hh
  have hpos : 0 < wcSup v := wcSup_pos' v hv0
  have hle : wcSup v * (z.2 - q * v.2).natAbs ≤ wcSup v * (z.1 - q * v.1).natAbs := by
    have h1 : wcSup v * (z.2 - q * v.2).natAbs = v.2.natAbs * (z.1 - q * v.1).natAbs := by
      rw [← hv1]; exact hmul
    rw [h1]
    exact Nat.mul_le_mul_right _ hmax2
  have hu2le : (z.2 - q * v.2).natAbs ≤ (z.1 - q * v.1).natAbs :=
    Nat.le_of_mul_le_mul_left hle hpos
  calc wcSup (z.1 - q * v.1, z.2 - q * v.2)
      = max (z.1 - q * v.1).natAbs (z.2 - q * v.2).natAbs := rfl
    _ = (z.1 - q * v.1).natAbs := max_eq_left hu2le
    _ < wcSup v := hlt1

/-- **Division step (second coordinate).** -/
private theorem wc_div_step_snd' (v z : ℤ × ℤ) (hv0 : v ≠ 0) (hv2 : v.2.natAbs = wcSup v)
    (hdet : wcDet v z = 0) :
    wcSup (z.1 - (z.2 / v.2) * v.1, z.2 - (z.2 / v.2) * v.2) < wcSup v := by
  have hv2ne : v.2 ≠ 0 := by
    intro h
    have hz : wcSup v = 0 := by
      have h' := hv2.symm
      rw [h] at h'
      simpa [wcSup] using h'
    exact absurd (wcSup_pos' v hv0) (by rw [hz]; omega)
  set q : ℤ := z.2 / v.2 with hq
  have hu2 : z.2 - q * v.2 = z.2 % v.2 := by
    rw [hq, Int.emod_def]
    ring
  have hmax1 : v.1.natAbs ≤ wcSup v := by simp only [wcSup]; exact le_max_left _ _
  have hlt2 : (z.2 - q * v.2).natAbs < wcSup v := by
    rw [hu2, ← hv2]
    have h1 : 0 ≤ z.2 % v.2 := Int.emod_nonneg _ hv2ne
    have h2 : z.2 % v.2 < ((v.2.natAbs : ℕ) : ℤ) := by simpa using Int.emod_lt_abs _ hv2ne
    have hlt := Int.natAbs_lt_natAbs_of_nonneg_of_lt h1 h2
    rw [Int.natAbs_natCast] at hlt
    exact hlt
  have hpar : v.1 * (z.2 - q * v.2) = v.2 * (z.1 - q * v.1) := by
    have hd : v.1 * z.2 = v.2 * z.1 := by
      have hh : v.1 * z.2 - v.2 * z.1 = 0 := hdet
      linarith
    rw [mul_sub, mul_sub, hd]
    ring
  have hmul : v.1.natAbs * (z.2 - q * v.2).natAbs = v.2.natAbs * (z.1 - q * v.1).natAbs := by
    have hh := congrArg Int.natAbs hpar
    simpa [Int.natAbs_mul] using hh
  have hpos : 0 < wcSup v := wcSup_pos' v hv0
  have hle : wcSup v * (z.1 - q * v.1).natAbs ≤ wcSup v * (z.2 - q * v.2).natAbs := by
    have h1 : wcSup v * (z.1 - q * v.1).natAbs = v.1.natAbs * (z.2 - q * v.2).natAbs := by
      rw [← hv2]; exact hmul.symm
    rw [h1]
    exact Nat.mul_le_mul_right _ hmax1
  have hu1le : (z.1 - q * v.1).natAbs ≤ (z.2 - q * v.2).natAbs :=
    Nat.le_of_mul_le_mul_left hle hpos
  calc wcSup (z.1 - q * v.1, z.2 - q * v.2)
      = max (z.1 - q * v.1).natAbs (z.2 - q * v.2).natAbs := rfl
    _ = (z.2 - q * v.2).natAbs := max_eq_right hu1le
    _ < wcSup v := hlt2

/-- **A shortest nonzero vector of the lattice `L = {w : c ∣ A w₁ - B w₂}`, and integrality of
parallel lattice vectors.**

The lattice `L = wcInL c A B` contains the nonzero vector `(wcI c A B, 0)` (as `wcG c A B ∣ A`), so
its nonzero vectors have a sup-norm minimum `λ`; pick `v` attaining it. Then `v ≠ 0`,
`wcSup v ≤ wcSup w` for every nonzero `w ∈ L`, and — because `v` is minimal — every `z ∈ L`
*parallel* to `v` (`wcDet v z = 0`) is an integral multiple of `v`.

Proof of the last clause: `L ∩ ℚv` is a rank-one subgroup of `ℤ²`, generated by some `u ∈ L` with
`v = k u` for some integer `k ≠ 0` (take `u` a generator of the group `L ∩ ℚv`, which is cyclic).
Since `wcSup (k u) = |k| · wcSup u`, minimality of `v` forces `k = ±1`, so `L ∩ ℚv = ℤ v`.
Concretely one may also argue with division: choose `i` with `|v_i| = wcSup v`, put
`q = z_i / v_i` and `u = z - q • v`; then `u ∈ L`, `wcDet v u = wcSup v u_i = 0`, `|u_i| = z_i % v_i < |v_i|`
and `|u_j| ≤ |u_i|`, so `wcSup u < wcSup v` and `u = 0`, i.e. `z = q • v`.

Existence of `v`: the set `{w ∈ L : w ≠ 0 ∧ wcSup w ≤ wcI c A B}` is finite and nonempty (it
contains `(wcI c A B, 0)`), so `Finset.exists_min_image` gives a minimiser; any nonzero `w ∈ L` with
`wcSup w < wcSup v ≤ wcI c A B` would lie in that set, contradicting minimality. -/
theorem wc_minVec_and_parallel (c A B : ℕ) (hA : 1 ≤ A) (hc : 1 ≤ c) :
    ∃ v : ℤ × ℤ,
      wcInL c A B v ∧ v ≠ 0 ∧
      (∀ w : ℤ × ℤ, wcInL c A B w → w ≠ 0 → wcSup v ≤ wcSup w) ∧
      (∀ z : ℤ × ℤ, wcInL c A B z → wcDet v z = 0 → ∃ k : ℤ, z = (k * v.1, k * v.2)) := by
  obtain ⟨v, hvL, hv0, hmin⟩ := wc_minVec_exists' c A B hA hc
  refine ⟨v, hvL, hv0, hmin, ?_⟩
  intro z hzL hdet
  have finish : ∀ q : ℤ, wcSup (z.1 - q * v.1, z.2 - q * v.2) < wcSup v →
      z = (q * v.1, q * v.2) := by
    intro q hlt
    have huL : wcInL c A B (z.1 - q * v.1, z.2 - q * v.2) := wcInL_sub_smul' c A B hzL hvL q
    have hzero : (z.1 - q * v.1, z.2 - q * v.2) = (0 : ℤ × ℤ) := by
      by_contra hne
      exact absurd (hmin _ huL hne) (not_le.mpr hlt)
    have h1 : z.1 - q * v.1 = 0 := by simpa using congrArg Prod.fst hzero
    have h2 : z.2 - q * v.2 = 0 := by simpa using congrArg Prod.snd hzero
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2)
  have hcoord : v.1.natAbs = wcSup v ∨ v.2.natAbs = wcSup v := by
    rcases le_total v.1.natAbs v.2.natAbs with h | h
    · exact Or.inr (by simp only [wcSup, max_eq_right h])
    · exact Or.inl (by simp only [wcSup, max_eq_left h])
  rcases hcoord with h1 | h2
  · exact ⟨z.1 / v.1, finish (z.1 / v.1) (wc_div_step_fst' v z hv0 h1 hdet)⟩
  · exact ⟨z.2 / v.2, finish (z.2 / v.2) (wc_div_step_snd' v z hv0 h2 hdet)⟩

end Work.FIArea2.R6
