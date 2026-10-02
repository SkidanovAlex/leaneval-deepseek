import Mathlib
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.ChartFrame
import Submission.Work.Gen.TautDualPuncture
import Submission.Work.Gen.Basic
import Submission.Work.Whitney.Basic
import Submission.Work.ThomBordism.Grassmann.zStdSetup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

/-! ## Index bookkeeping for the probe

`Amb (k+m)` splits (through `finSumFinEquiv`) into the `Fin k`-block and the `Fin m`-block.  The
complex line of `ℂP²` sits in the first two coordinates of the `Fin k`-block and the first four
coordinates of the `Fin m`-block; the fixed `κ = k-2`-plane sits in the coordinates `2, …, k-1` of
the `Fin k`-block. -/

/-- The `a`-th coordinate of the `Fin 2`-block inside the `Fin k`-block. -/
def idxTwo (k : ℕ) (hk : 2 ≤ k) (a : Fin 2) : Fin k := ⟨a.val, lt_of_lt_of_le a.isLt hk⟩

/-- The `l`-th coordinate of the `κ = k-2`-block inside the `Fin k`-block. -/
def idxTail (k : ℕ) (hk : 2 ≤ k) (l : Fin (k - 2)) : Fin k :=
  ⟨l.val + 2, by have h := l.isLt; omega⟩

theorem idxTwo_val (k : ℕ) (hk : 2 ≤ k) (a : Fin 2) : (idxTwo k hk a).val = a.val := rfl

theorem idxTail_val (k : ℕ) (hk : 2 ≤ k) (l : Fin (k - 2)) : (idxTail k hk l).val = l.val + 2 := rfl

theorem idxTwo_injective (k : ℕ) (hk : 2 ≤ k) : Function.Injective (idxTwo k hk) :=
  fun a b h => Fin.ext (by simpa [idxTwo] using congrArg Fin.val h)

theorem idxTail_injective (k : ℕ) (hk : 2 ≤ k) : Function.Injective (idxTail k hk) :=
  fun a b h => Fin.ext (by have := congrArg Fin.val h; simp only [idxTail_val] at this; omega)

theorem idxTwo_ne_idxTail (k : ℕ) (hk : 2 ≤ k) (a : Fin 2) (l : Fin (k - 2)) :
    idxTwo k hk a ≠ idxTail k hk l := by
  intro h
  have h2 : (idxTwo k hk a).val = (idxTail k hk l).val := congrArg Fin.val h
  simp only [idxTwo_val, idxTail_val] at h2
  have := a.isLt
  omega

/-- The index of the `i`-th coordinate of `ℝ⁶` inside `Fin (k+m)`. -/
noncomputable def probeAmbIdx (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) : Fin 6 → Fin (k + m) :=
  fun i => finSumFinEquiv (Sum.map (idxTwo k hk) (Fin.castLE hm)
    ((finSumFinEquiv (m := 2) (n := 4)).symm i))

/-- The index of the `l`-th vector of the fixed complement frame inside `Fin (k+m)`. -/
noncomputable def probeTailIdx (k m : ℕ) (hk : 2 ≤ k) : Fin (k - 2) → Fin (k + m) :=
  fun l => finSumFinEquiv (Sum.inl (idxTail k hk l))

theorem probeAmbIdx_injective (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    Function.Injective (probeAmbIdx k m hk hm) := by
  intro i j hij
  have h1 : Sum.map (idxTwo k hk) (Fin.castLE hm)
      ((finSumFinEquiv (m := 2) (n := 4)).symm i)
      = Sum.map (idxTwo k hk) (Fin.castLE hm)
        ((finSumFinEquiv (m := 2) (n := 4)).symm j) :=
    (finSumFinEquiv (m := k) (n := m)).injective (by simpa only [probeAmbIdx] using hij)
  have h2 : (finSumFinEquiv (m := 2) (n := 4)).symm i
      = (finSumFinEquiv (m := 2) (n := 4)).symm j := by
    rcases hi : (finSumFinEquiv (m := 2) (n := 4)).symm i with a | b <;>
      rcases hj : (finSumFinEquiv (m := 2) (n := 4)).symm j with a' | b'
    · rw [hi, hj] at h1
      exact congrArg Sum.inl (idxTwo_injective k hk (Sum.inl_injective h1))
    · rw [hi, hj] at h1
      exact absurd h1 Sum.inl_ne_inr
    · rw [hi, hj] at h1
      exact absurd h1 Sum.inr_ne_inl
    · rw [hi, hj] at h1
      exact congrArg Sum.inr
        (Fin.ext (by simpa using congrArg Fin.val (Sum.inr_injective h1)))
  exact (finSumFinEquiv (m := 2) (n := 4)).symm.injective h2

theorem probeAmbIdx_ne_probeTailIdx (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 6)
    (l : Fin (k - 2)) : probeAmbIdx k m hk hm i ≠ probeTailIdx k m hk l := by
  intro h
  have h1 : Sum.map (idxTwo k hk) (Fin.castLE hm) ((finSumFinEquiv (m := 2) (n := 4)).symm i)
      = Sum.inl (idxTail k hk l) :=
    (finSumFinEquiv (m := k) (n := m)).injective (by simpa only [probeAmbIdx, probeTailIdx] using h)
  rcases hi : (finSumFinEquiv (m := 2) (n := 4)).symm i with a | b
  · rw [hi] at h1
    simp only [Sum.map_inl] at h1
    exact idxTwo_ne_idxTail k hk a l (Sum.inl_injective h1)
  · rw [hi] at h1
    simp only [Sum.map_inr] at h1
    exact absurd h1 Sum.inr_ne_inl

theorem probeTailIdx_injective (k m : ℕ) (hk : 2 ≤ k) :
    Function.Injective (probeTailIdx k m hk) := by
  intro a b h
  have h1 : Sum.inl (idxTail k hk a) = Sum.inl (idxTail k hk b) :=
    (finSumFinEquiv (m := k) (n := m)).injective (by simpa only [probeTailIdx] using h)
  exact idxTail_injective k hk (Sum.inl_injective h1)

/-! ## The ambient coordinate isometry and its adjoint -/

/-- **The coordinate isometry `ℝ⁶ → ℝ^{k+m}`** of the probe. -/
noncomputable def probeEmb (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) : Amb 6 →L[ℝ] Amb (k + m) :=
  ∑ i : Fin 6, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
    (EuclideanSpace.single (𝕜 := ℝ) (probeAmbIdx k m hk hm i) 1)

/-- **The coordinate extraction adjoint to `probeEmb`**: the orthogonal projection onto its image. -/
noncomputable def probeCy (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) : Amb (k + m) →L[ℝ] Amb 6 :=
  ∑ i : Fin 6, (EuclideanSpace.proj (𝕜 := ℝ) (probeAmbIdx k m hk hm i)).smulRight
    (EuclideanSpace.single (𝕜 := ℝ) i 1)

/-- The `l`-th vector of the fixed complement frame: the standard basis vector at `probeTailIdx l`. -/
noncomputable def probeTailVec (k m : ℕ) (hk : 2 ≤ k) : Fin (k - 2) → Amb (k + m) :=
  fun l => EuclideanSpace.single (𝕜 := ℝ) (probeTailIdx k m hk l) 1

/-- **The extraction of the fixed complement coordinates.** -/
noncomputable def probeUx (k m : ℕ) (hk : 2 ≤ k) : Amb (k + m) →L[ℝ] Amb (k - 2) :=
  ∑ l : Fin (k - 2), (EuclideanSpace.proj (𝕜 := ℝ) (probeTailIdx k m hk l)).smulRight
    (EuclideanSpace.single (𝕜 := ℝ) l 1)

/-- **The recombining map** `u ↦ ∑ l, u_l • probeTailVec l`. -/
noncomputable def probeTailComb (k m : ℕ) (hk : 2 ≤ k) : Amb (k - 2) →L[ℝ] Amb (k + m) :=
  ∑ l : Fin (k - 2), (EuclideanSpace.proj (𝕜 := ℝ) l).smulRight (probeTailVec k m hk l)

/-! ## The complex structure and the probe frame -/

/-- The complex `3`-space `ℂ³`, with its real inner product structure. -/
abbrev E3 : Type := EuclideanSpace ℂ (Fin 3)

/-- **The identification `ℂ³ ≅ ℝ⁶`** (as real inner product spaces) used by the probe.  It is
chosen abstractly (through orthonormal bases), which is harmless: the probe does not depend on
which realification is used. -/
noncomputable def cxE : E3 ≃ₗᵢ[ℝ] Amb 6 :=
  (stdOrthonormalBasis ℝ E3).equiv (stdOrthonormalBasis ℝ (Amb 6))
    (finCongr (by
      rw [← Module.finrank_mul_finrank ℝ ℂ E3, finrank_euclideanSpace_fin,
        Complex.finrank_real_complex, finrank_euclideanSpace_fin]))

/-- The realification of a representative `v : ℂ³ = Fin 3 → ℂ` as an element of `E3`. -/
noncomputable def cxOf (v : Fin 3 → ℂ) : E3 := WithLp.toLp 2 v

/-- **The unit vector in the direction of a nonzero representative.**
(The scalar is the *real* number `‖cxOf v‖⁻¹`; this keeps `cxUnit_norm` and the scaling laws
elementary.) -/
noncomputable def cxUnit (v : Fin 3 → ℂ) : E3 := ((‖cxOf v‖ : ℝ))⁻¹ • cxOf v

/-- The `a`-th of the two orthonormal vectors `u, I • u` of a complex line. -/
noncomputable def cxTwo (a : Fin 2) (u : E3) : E3 := if a.val = 0 then u else Complex.I • u

/-- The equality `2 + (k - 2) = k` used to split `Fin k`. -/
theorem two_add_sub (k : ℕ) (hk : 2 ≤ k) : 2 + (k - 2) = k := by omega

/-- **The splitting `Fin k ≃ Fin 2 ⊕ Fin (k-2)`** of the `Fin k`-block into the plane block and the
fixed complement block. -/
noncomputable def probeSplit (k : ℕ) (hk : 2 ≤ k) : Fin 2 ⊕ Fin (k - 2) ≃ Fin k :=
  finSumFinEquiv.trans (finCongr (two_add_sub k hk))

theorem probeSplit_inl (k : ℕ) (hk : 2 ≤ k) (a : Fin 2) :
    probeSplit k hk (Sum.inl a) = ⟨a.val, lt_of_lt_of_le a.isLt hk⟩ := by
  simp only [probeSplit, Equiv.trans_apply, finSumFinEquiv_apply_left]
  rfl

theorem probeSplit_inr (k : ℕ) (hk : 2 ≤ k) (l : Fin (k - 2)) :
    probeSplit k hk (Sum.inr l) = ⟨2 + l.val, by have h := l.isLt; omega⟩ := by
  simp only [probeSplit, Equiv.trans_apply, finSumFinEquiv_apply_right]
  rfl

/-- **The two plane vectors of the probe frame** of a representative `v`: the orthonormal pair
`cxE u`, `-cxE (I • u)` of the complex line (`u = cxUnit v`). -/
noncomputable def probePairVec (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) :
    Fin 2 → Amb (k + m) :=
  ![probeEmb k m hk hm (cxE (cxUnit v)),
    -(probeEmb k m hk hm (cxE (Complex.I • cxUnit v)))]

@[simp] theorem probePairVec_zero (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) :
    probePairVec k m hk hm v 0 = probeEmb k m hk hm (cxE (cxUnit v)) := rfl

@[simp] theorem probePairVec_one (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) :
    probePairVec k m hk hm v 1
      = -(probeEmb k m hk hm (cxE (Complex.I • cxUnit v))) := rfl

@[simp] theorem probePairVec_neg_zero (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) :
    -probePairVec k m hk hm v 0 = -(probeEmb k m hk hm (cxE (cxUnit v))) := rfl

@[simp] theorem probePairVec_neg_one (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ) :
    -probePairVec k m hk hm v 1
      = probeEmb k m hk hm (cxE (Complex.I • cxUnit v)) := by
  rw [probePairVec_one, neg_neg]

/-- **The frame of the probe on a representative**: the first two vectors are the complex structure
pair `(cxE u, -cxE (I • u))` of the unit vector `u` of the line, the remaining `k-2` are the fixed
standard basis vectors of the complement block. -/
noncomputable def probeFrameRep (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m)
    (v : Fin 3 → ℂ) : Fin k → Amb (k + m) :=
  fun i => match (probeSplit k hk).symm i with
    | Sum.inl a => probePairVec k m hk hm v a
    | Sum.inr l => probeTailVec k m hk l

@[simp] theorem probeFrameRep_inl (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (a : Fin 2) :
    probeFrameRep k m hk hm v (probeSplit k hk (Sum.inl a))
      = probePairVec k m hk hm v a := by
  simp only [probeFrameRep, Equiv.symm_apply_apply]

@[simp] theorem probeFrameRep_inr (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (v : Fin 3 → ℂ)
    (l : Fin (k - 2)) :
    probeFrameRep k m hk hm v (probeSplit k hk (Sum.inr l)) = probeTailVec k m hk l := by
  simp only [probeFrameRep, Equiv.symm_apply_apply]

end

end Work.ThomBordism.Grassmann
