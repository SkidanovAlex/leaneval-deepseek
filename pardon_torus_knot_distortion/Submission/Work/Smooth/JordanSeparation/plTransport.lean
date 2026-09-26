import Mathlib
import Submission.Work.Smooth.JordanSeparation.plJoinFrom

/-!
# Index transport for families of paths (step (B))

The gap recorded in `NH_STATE.md`: the chords of the polygonal loop form a family
`F : ∀ k, Path (p k) (p (k+1))`, and the two-sided split of `plJoinFrom` is stated with the target
`p (i + (j+k))` while the right piece naturally ends at `p ((i+j)+k)`.  The two indices differ by
`Nat.add_assoc`, and `0 + l` is not definitionally `l` in this toolchain, so the identification of
the shifted family with the original one cannot be done by `congrArg F` and must go through
`Eq.ndrec`.

This file provides the two elementary facts that make such a transport harmless:

* `cast_index` — transporting a member of the family along an equality of indices;
* `cast_index_apply` — such a transport does not change the **values** of the path (the value type
  `X` is independent of the index, which is the whole point).

Both are proved by `cases h`/`rfl`: no `Path`-level cast is involved.
-/

namespace Work.Smooth.JordanSeparation

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- **Transport of a family member along an equality of indices.** -/
theorem cast_index {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) {a b : ℕ} (h : a = b) :
    (h ▸ F a : Path (p b) (p (b + 1))) = F b := by
  cases h
  rfl

/-- **The transport does not change the values.**  The value type of a path is independent of the
index, so transporting a family member along an index equality leaves its points unchanged. -/
theorem cast_index_apply {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) {a b : ℕ} (h : a = b) :
    ∀ t : unitInterval,
      ((h ▸ F a : Path (p b) (p (b + 1))) : unitInterval → X) t
        = ((F a : Path (p a) (p (a + 1))) : unitInterval → X) t := by
  cases h
  intro t
  rfl


/-- **The zero shift is the original family** (value level). -/
theorem joinNatShift_zero_apply {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (l : ℕ) :
    ∀ t : unitInterval,
      (((joinNatShift F 0 l : Path (p (0 + l)) (p (0 + (l + 1)))) : unitInterval → X) t)
        = ((F l : Path (p l) (p (l + 1))) : unitInterval → X) t := by
  intro t
  rw [show (joinNatShift F 0 l : Path (p (0 + l)) (p (0 + (l + 1))))
      = Path.cast (F (0 + l)) rfl (congrArg p (Nat.add_assoc 0 l 1).symm) from rfl]
  rw [Path.cast_coe]
  rw [← cast_index F (Nat.zero_add l).symm]
  rw [cast_index_apply F (Nat.zero_add l).symm]

/-- **The zero shift is the original family**, as paths (with the endpoint casts). -/
theorem joinNatShift_zero {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (l : ℕ) :
    Path.cast (joinNatShift F 0 l) (congrArg p (Nat.zero_add l).symm)
      (congrArg p (Nat.zero_add (l + 1)).symm) = F l := by
  ext t
  rw [Path.cast_coe]
  exact joinNatShift_zero_apply F l t

end

end Work.Smooth.JordanSeparation

