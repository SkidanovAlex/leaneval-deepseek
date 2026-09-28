import Mathlib
import Submission.Work.HP.Defs

/-!
# A primitive integer vector has a Bézout dual

`Work.HP.IsPrim c` says that the gcd of the coordinates of `c : ι → ℤ` is `1`.  We show that then
`c` admits an integer "dual" vector `w` with `∑ i, w i * c i = 1`.

This is Bézout's identity for a finite family of integers.  The proof is the usual induction on the
finite set: `Int.gcd_eq_gcd_ab` writes `gcd x y` as `a * x + b * y`, and folding this over the
coordinates of `c` produces a `ℤ`-linear combination of the coordinates equal to their gcd.
The result is stated for an arbitrary finite index type, so it applies in particular to the
locations `γ` of the paper.
-/

namespace Work.HP.GamLoc

/-- The `ℤ`-valued gcd of the `NormalizedGCDMonoid` structure on `ℤ` is the cast of `Int.gcd`. -/
private lemma int_gcd_cast (x y : ℤ) : ((Int.gcd x y : ℤ)) = gcd x y := by
  rw [← Int.natAbs_gcd x y]
  exact Int.natAbs_of_nonneg (Int.gcd_nonneg x y)

/-- Bézout for `ℤ`: `gcd x y` is an integer combination of `x` and `y`. -/
private lemma gcd_comb (x y : ℤ) : ∃ a b : ℤ, a * x + b * y = gcd x y := by
  have h := Int.gcd_eq_gcd_ab x y
  rw [int_gcd_cast x y] at h
  exact ⟨Int.gcdA x y, Int.gcdB x y, by rw [h]; ring⟩

/-- The gcd of `u` over a finite set `s` is a `ℤ`-linear combination of the `u i`, `i ∈ s`. -/
private lemma gcd_sum_aux {ι : Type*} [DecidableEq ι] (u : ι → ℤ) (s : Finset ι) :
    ∃ c : ι → ℤ, ∑ i ∈ s, c i * u i = s.gcd u := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨x, y, hxy⟩ := gcd_comb (u a) (s.gcd u)
    refine ⟨fun i => if i = a then x else y * c i, ?_⟩
    have hsum : ∑ i ∈ s, (if i = a then x else y * c i) * u i
        = y * ∑ i ∈ s, c i * u i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_right (by rintro rfl; exact ha hi)]
      ring
    rw [Finset.sum_insert ha, hsum, hc, Finset.gcd_insert]
    simpa using hxy

theorem prim_has_dual {ι : Type*} [Fintype ι] (c : ι → ℤ) (hc : Work.HP.IsPrim c) :
    ∃ w : ι → ℤ, ∑ i, w i * c i = 1 := by
  classical
  obtain ⟨w, hw⟩ := gcd_sum_aux c Finset.univ
  exact ⟨w, by rw [hw]; exact hc⟩

end Work.HP.GamLoc
