/-
  WilC5 / StepSeqIndep — the arithmetic of the standard real valuation that the independence proof
  of vdDMM Claim 2 consumes.

  Everything here is a statement about an ordered field `K` and the three value-theoretic
  predicates of `Submission/Work/WilC5/Values.lean`:

  * `IsFiniteVal x` (= `Fin(K)`, vdDMM (1.1)),
  * `VLe x y` (`v x ≤ v y`, i.e. `|y| ≤ (N+1)|x|` for some natural `N`),
  * `SameArch x y` (`v x = v y`),

  and none of it uses the `LEc`/`LRc` structure.  The mathematical content is the "min rule": in the
  standard real valuation the value of a sum is the minimum of the values of its summands *as soon
  as that minimum is attained uniquely*; in the notation of `VLe`,

  * `VLe z x → VLe z y → VLe z (x + y)` (`VLe_add`), and
  * if moreover `¬ VLe x z`, then `SameArch (z - x) x` (`SameArch_sub_of_VLe_of_not`), which is the
    form in which the paper uses the rule (`v(log x - β) = v(β)` forces `log x - β` to have the
    value of `β` when `β` dominates `log x`).

  Consequently (i) a finite sum of terms *strictly* dominated by `z` is again strictly dominated by
  `z` (`VLe_sum_strict`), and (ii) an element which dominates every natural number dominates every
  element of finite value, strictly (`VLe_of_isFiniteVal_of_infinite`).
-/
import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValuesLemmas

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG

section ValueOrder

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## 1. `VLe`: retotalisation and the addition rules -/

theorem VLe_zero_right (z : K) : VLe z 0 := ⟨0, by simp⟩

theorem VLe_neg_right (x y : K) : VLe x (-y) ↔ VLe x y := by
  unfold VLe; rw [abs_neg]

theorem VLe_neg_left (x y : K) : VLe (-x) y ↔ VLe x y := by
  unfold VLe; rw [abs_neg]

theorem VLe_abs_abs (x y : K) : VLe |x| |y| ↔ VLe x y := by
  simp only [VLe, abs_abs]

/-- Only `0` is dominated by `0`. -/
theorem not_VLe_zero_left {z : K} (hz : z ≠ 0) : ¬ VLe (0 : K) z := by
  rintro ⟨N, hN⟩
  exact hz (abs_eq_zero.mp (le_antisymm (by simpa using hN) (abs_nonneg z)))

/-- `VLe` is total: of two elements, one dominates the other. -/
theorem VLe_total (x y : K) : VLe x y ∨ VLe y x := by
  rcases le_total |y| |x| with h | h
  · exact Or.inl ⟨0, by simpa using h⟩
  · exact Or.inr ⟨0, by simpa using h⟩

/-- The value order is closed under addition in its first argument: if `z` dominates both summands
it dominates the sum. -/
theorem VLe_add {z x y : K} (hx : VLe z x) (hy : VLe z y) : VLe z (x + y) := by
  obtain ⟨N, hN⟩ := hx
  obtain ⟨M, hM⟩ := hy
  refine ⟨N + M + 1, ?_⟩
  have hcast : (((N + M + 1 : ℕ)) : K) + 1 = ((N : K) + 1) + ((M : K) + 1) := by
    push_cast; ring
  rw [hcast, add_mul]
  exact le_trans (abs_add_le x y) (add_le_add hN hM)

/-- `VLe` is closed under natural scalar multiplication in its second argument. -/
theorem VLe_natCast_mul (n : ℕ) {z x : K} (h : VLe z x) : VLe z ((n : K) * x) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨n * N + n, ?_⟩
  have hcast : (((n * N + n : ℕ)) : K) + 1 = (n : K) * ((N : K) + 1) + 1 := by
    push_cast; ring
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n), hcast]
  calc (n : K) * |x| ≤ (n : K) * (((N : K) + 1) * |z|) :=
        mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg n)
    _ = ((n : K) * ((N : K) + 1)) * |z| := by ring
    _ ≤ ((n : K) * ((N : K) + 1) + 1) * |z| := by nlinarith [abs_nonneg z]

/-- The absolute value of an integer cast. -/
theorem abs_intCast (k : ℤ) : |(k : K)| = (k.natAbs : K) := by
  have h1 : ((|k| : ℤ) : K) = (k.natAbs : K) := by
    rw [← Int.natCast_natAbs k, Int.cast_natCast]
  rw [← h1]
  exact (Int.cast_abs (R := K) (a := k)).symm

/-- Multiplication by an integer cast preserves domination. -/
theorem VLe_intCast_mul_left (k : ℤ) {z x : K} (h : VLe z x) : VLe z ((k : K) * x) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨k.natAbs * N + k.natAbs, ?_⟩
  rw [abs_mul, abs_intCast]
  have hcast2 : (((k.natAbs * N + k.natAbs : ℕ)) : K) + 1
      = (k.natAbs : K) * ((N : K) + 1) + 1 := by push_cast; ring
  rw [hcast2]
  calc (k.natAbs : K) * |x| ≤ (k.natAbs : K) * (((N : K) + 1) * |z|) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = ((k.natAbs : K) * ((N : K) + 1)) * |z| := by ring
    _ ≤ ((k.natAbs : K) * ((N : K) + 1) + 1) * |z| := by
        nlinarith [abs_nonneg z]

/-- Scalar multiples of a nonzero integer have the value of the element. -/
theorem VLe_intCast_mul (k : ℤ) (x : K) : VLe x ((k : K) * x) := by
  refine ⟨k.natAbs, ?_⟩
  rw [abs_mul, abs_intCast]
  calc (k.natAbs : K) * |x| ≤ (((k.natAbs : ℕ)) : K) * |x| := le_refl _
    _ ≤ ((((k.natAbs : ℕ)) : K) + 1) * |x| := by nlinarith [abs_nonneg x]

theorem VLe_intCast_mul_of_ne {k : ℤ} (hk : k ≠ 0) (x : K) : VLe ((k : K) * x) x := by
  have hne : k.natAbs ≠ 0 := fun h => hk (Int.natAbs_eq_zero.mp h)
  have h1 : (1 : K) ≤ (k.natAbs : K) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
  refine ⟨0, ?_⟩
  rw [abs_mul, abs_intCast]
  simpa using mul_le_mul_of_nonneg_right h1 (abs_nonneg x)

/-- **The min rule.**  If `z` dominates `x` and `x` does not dominate `z`, then `z - x` has the
same value as `z` (`v(z - x) = v(z)` when `v x > v z`). -/
theorem SameArch_sub_of_VLe_of_not {z x : K} (h1 : VLe z x) (h2 : ¬ VLe x z) :
    SameArch (z - x) z := by
  have hzx : ∀ M : ℕ, ((M : K) + 1) * |x| < |z| := by
    intro M
    exact not_le.mp fun h => h2 ⟨M, h⟩
  have h2x : 2 * |x| < |z| := by
    have h := hzx 1
    have hc : (((1 : ℕ)) : K) + 1 = 2 := by norm_num
    rwa [hc] at h
  refine ⟨1, ?_, ?_⟩
  · have hkey : |z - x| ≤ |z| + |x| := by
      have h := abs_add_le z (-x)
      rw [← sub_eq_add_neg, abs_neg] at h
      exact h
    have htwo : ((1 : ℕ) : K) + 1 = 2 := by norm_num
    rw [htwo]
    have hxz : |x| ≤ |z| := by linarith [abs_nonneg x]
    linarith [abs_nonneg x]
  · have hsub : |z| ≤ |z - x| + |x| := by
      have h := abs_add_le (z - x) x
      rwa [sub_add_cancel] at h
    have htwo : ((1 : ℕ) : K) + 1 = 2 := by norm_num
    rw [htwo]
    linarith [abs_nonneg (z - x)]

/-! ## 2. Finite sums of strictly dominated terms -/

theorem VLe_finset_sum {ι : Type*} (s : Finset ι) {z : K} (g : ι → K)
    (h : ∀ i ∈ s, VLe z (g i)) : VLe z (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using VLe_zero_right z
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact VLe_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A sum of two terms strictly dominated by `z` is strictly dominated by `z`. -/
theorem VLe_add_strict {z x y : K} (h1 : VLe z x) (h2 : VLe z y)
    (h3 : ¬ VLe x z) (h4 : ¬ VLe y z) : ¬ VLe (x + y) z := by
  intro hcon
  obtain ⟨N, hN⟩ := hcon
  have key : ∀ w : K, ¬ VLe w z → 2 * ((N : K) + 1) * |w| < |z| := by
    intro w hw
    have h := not_le.mp fun h : |z| ≤ (((2 * N + 2 : ℕ)) : K) * |w| =>
      hw ⟨2 * N + 1, by
        have hcast : (((2 * N + 1 : ℕ)) : K) + 1 = ((2 * N + 2 : ℕ) : K) := by push_cast; ring
        rw [hcast]; exact h⟩
    have hcast : (((2 * N + 2 : ℕ)) : K) = 2 * ((N : K) + 1) := by push_cast; ring
    rw [hcast] at h
    simpa only [mul_assoc] using h
  have hx' := key x h3
  have hy' := key y h4
  have hkey : |z| ≤ ((N : K) + 1) * (|x| + |y|) := by
    calc |z| ≤ ((N : K) + 1) * |x + y| := hN
      _ ≤ ((N : K) + 1) * (|x| + |y|) :=
          mul_le_mul_of_nonneg_left (abs_add_le x y) (by positivity)
  have hpos : (0 : K) < 2 * ((N : K) + 1) := by positivity
  nlinarith [hx', hy', hkey]

/-- **A finite sum of terms strictly dominated by `z` is strictly dominated by `z`.** -/
theorem VLe_sum_strict {ι : Type*} (s : Finset ι) {z : K} (hz : z ≠ 0) (g : ι → K)
    (h1 : ∀ i ∈ s, VLe z (g i)) (h2 : ∀ i ∈ s, ¬ VLe (g i) z) :
    VLe z (∑ i ∈ s, g i) ∧ ¬ VLe (∑ i ∈ s, g i) z := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine ⟨by simpa using VLe_zero_right z, ?_⟩
      simpa using not_VLe_zero_left hz
  | insert a s ha ih =>
      have h1' : ∀ i ∈ s, VLe z (g i) := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have h2' : ∀ i ∈ s, ¬ VLe (g i) z := fun i hi => h2 i (Finset.mem_insert_of_mem hi)
      obtain ⟨ih1, ih2⟩ := ih h1' h2'
      have hga1 : VLe z (g a) := h1 a (Finset.mem_insert_self a s)
      have hga2 : ¬ VLe (g a) z := h2 a (Finset.mem_insert_self a s)
      rw [Finset.sum_insert ha]
      exact ⟨VLe_add hga1 ih1,
        VLe_add_strict (x := g a) (y := ∑ i ∈ s, g i) hga1 ih1 hga2 ih2⟩

/-! ## 3. Infinite elements dominate the finite ones -/

/-- **An element dominating every natural number dominates every element of finite value**, and
strictly.  (The hypothesis `∀ N, (N : K) < a` is the form in which `StepSeq.Unbounded` is used.) -/
theorem VLe_of_isFiniteVal_of_infinite {a z : K} (ha : ∀ N : ℕ, (N : K) < a)
    (hz : IsFiniteVal z) : VLe a z ∧ ¬ VLe z a := by
  obtain ⟨M, hM⟩ := hz
  have ha1 : (1 : K) < a := by simpa using ha 1
  have ha0 : 0 < a := by linarith
  have habs : |a| = a := abs_of_pos ha0
  refine ⟨⟨M, ?_⟩, ?_⟩
  · rw [habs]
    have hMz : |z| ≤ ((M : K) + 1) := hM
    have h1a : (1 : K) ≤ a := le_of_lt ha1
    have hMc : (0 : K) ≤ (M : K) := Nat.cast_nonneg M
    calc |z| ≤ ((M : K) + 1) := hMz
      _ ≤ ((M : K) + 1) * a := by nlinarith
  · intro hcon
    obtain ⟨N, hN⟩ := hcon
    rw [habs] at hN
    have hle : ((N : K) + 1) * |z| ≤ ((N : K) + 1) * ((M : K) + 1) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have hcast : ((N : K) + 1) * ((M : K) + 1) = (((N + 1) * (M + 1) : ℕ) : K) := by
      push_cast; ring
    have hlt : (((N + 1) * (M + 1) : ℕ) : K) < a := ha ((N + 1) * (M + 1))
    rw [← hcast] at hlt
    linarith

end ValueOrder

end Work.WilC5
