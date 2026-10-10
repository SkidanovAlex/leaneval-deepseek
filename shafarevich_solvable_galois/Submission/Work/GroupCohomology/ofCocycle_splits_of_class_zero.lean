import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.GroupExtension.Defs
import Submission.Work.GroupCohomology.Extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- If a `2`-cocycle `c : Z²(Q, A)` represents the zero class in `H²(Q, A)`, i.e. `c` is a
coboundary, then the extension of `Q` by `A` it defines (with the prescribed action) splits:
there is a homomorphic section `Q →* E`.

Explicitly, if `c = d¹ f`, then the zeroth cocycle condition for `c` is exactly the identity
making `q ↦ (-f q, q)` multiplicative for the twisted product, and its second coordinate is `q`,
which is the projection of the extension. -/
theorem ofCocycle_splits_of_class_zero {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c : Work.GroupCohomology.Z2 Q A)
    (h : Work.GroupCohomology.H2π Q A c = 0) :
    Nonempty (Work.GroupCohomology.Extension.Splitting
      (Work.GroupCohomology.Extension.ofCocycle Q A c)) := by
  -- `H²π c = 0` means that the cocycle `c` is a coboundary.
  have hcB : (c : Q × Q → A) ∈ B2 Q A := by
    have h' := h
    rw [H2π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap] at h'
    exact h'
  obtain ⟨f0, hf0⟩ := (mem_B2_iff Q A (c : Q × Q → A)).mp hcB
  -- The normalization `normCocycle c = c - (q, r) ↦ c (q, 1)` is again a coboundary: the
  -- `2`-cocycle `(q, r) ↦ c (q, 1) = q • c (1, 1)` is the coboundary of `r ↦ r • c (1, 1)`.
  let g : Q → A := fun r => r • (c : Q × Q → A) (1, 1)
  have hdg : d1 Q A g = fun p : Q × Q => p.1 • (c : Q × Q → A) (1, 1) := by
    funext p
    obtain ⟨q, r⟩ := p
    simp only [d1_apply, g, mul_smul]
    abel
  let f : Q → A := f0 - g
  have hf : d1 Q A f = normCocycle Q A (c : Q × Q → A) := by
    have h1 : d1 Q A f = d1 Q A f0 - d1 Q A g := by
      rw [show f = f0 - g from rfl, map_sub]
    rw [h1, hf0, hdg]
    funext p
    obtain ⟨q, r⟩ := p
    simp only [Pi.sub_apply, normCocycle_apply]
    rw [Z2.map_one_snd Q A c.2 q]
  set_option linter.style.haveILetI false in
  letI : Group (Extension.ofCocycle Q A c).E := (Extension.ofCocycle Q A c).groupE
  refine ⟨{ toFun := fun q => (-(f q), q), map_one' := ?_, map_mul' := ?_, rightInverse_rightHom := ?_ }⟩
  · rw [show (1 : (Extension.ofCocycle Q A c).E) = twOne Q A from rfl, twOne_apply]
    refine Prod.ext ?_ ?_
    · have h1 : f 1 = 0 := by
        have h2 := congrArg (fun w : Q × Q → A => w (1, 1)) hf
        simp only [d1_apply, normCocycle_one] at h2
        simpa using h2
      simp [h1]
    · rfl
  · intro x y
    change (-f (x * y), x * y) = twMul Q A (normCocycle Q A (c : Q × Q → A)) (-f x, x) (-f y, y)
    simp only [twMul_apply]
    refine Prod.ext ?_ ?_
    · have hmul : (normCocycle Q A (c : Q × Q → A)) (x, y) = x • f y - f (x * y) + f x := by
        have h2 := congrArg (fun w : Q × Q → A => w (x, y)) hf
        rw [← h2]
        simp only [d1_apply]
      rw [hmul, smul_neg]
      abel
    · rfl
  · intro q
    rfl

end Work.GroupCohomology
