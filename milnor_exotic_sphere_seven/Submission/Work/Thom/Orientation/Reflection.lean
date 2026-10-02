import Mathlib
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The fibre reflection of the trivial bundle of rank `n`

For the model induction of the Thom class (`Work.Thom.Mn`, `Work.Thom.Mpun`) the "orientation
character" of a transition function is measured by the action of a *reflection* of the fibre
`ℝⁿ`: the map negating the first coordinate.  This file sets up that reflection and its elementary
properties.

* `Work.Thom.Orientation.flipFst n` — the continuous linear map of `EuclideanSpace ℝ (Fin n)`
  negating the coordinate `0` (for `n = 0` it is the zero map, which is the identity on the
  one-point space);
* `Work.Thom.Orientation.fibRefl n Y` — the map `id × flipFst n` of `Y × ℝⁿ`;
* the coordinate formulas, `flipFst_norm`, `flipFst_involutive`, and the compatibility
  `flipFst_capMap` with the cap map of the suspension step.

The two facts proved elsewhere are `flipFst_det` (`det = -1`, `Submission/.../ReflectionDet.lean`)
and the naturality of the inductive step under `fibRefl` (`Submission/.../StepFlip.lean`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace Work.Thom.Orientation

open Work.Thom

noncomputable section

/-- The linear map of `Fin m → ℝ` negating the coordinate `0` (and the identity for `m = 0`). -/
def negFst (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  if h : 0 < m then
    { toFun := fun v => Function.update v ⟨0, h⟩ (-(v ⟨0, h⟩))
      map_add' := by
        intro a b; funext i
        by_cases hi : i = ⟨0, h⟩
        · subst hi; simp [Function.update]; ring
        · simp [Function.update, hi]
      map_smul' := by
        intro c a; funext i
        by_cases hi : i = ⟨0, h⟩
        · subst hi; simp [Function.update, smul_eq_mul]
        · simp [Function.update, hi] }
  else 0

/-- **The reflection of `ℝᵐ` in the hyperplane orthogonal to the first coordinate**: the continuous
linear map negating the coordinate `0`. -/
def flipFst (m : ℕ) : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    (((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap).comp
      ((negFst m).comp (EuclideanSpace.equiv (Fin m) ℝ).toLinearMap))

theorem negFst_apply (m : ℕ) (h : 0 < m) (w : Fin m → ℝ) :
    negFst m w = Function.update w ⟨0, h⟩ (-(w ⟨0, h⟩)) := by
  unfold negFst; rw [dif_pos h]; rfl

theorem negFst_apply_pos (m : ℕ) (h : 0 < m) (w : Fin m → ℝ) (i : Fin m) :
    negFst m w i = if i = ⟨0, h⟩ then -(w i) else w i := by
  rw [negFst_apply m h]
  by_cases hi : i = ⟨0, h⟩
  · subst hi; simp [Function.update]
  · simp [Function.update, hi]

theorem negFst_zero (m : ℕ) (h : 0 < m) (w : Fin m → ℝ) :
    negFst m w ⟨0, h⟩ = -(w ⟨0, h⟩) := by
  rw [negFst_apply_pos m h, if_pos rfl]

theorem negFst_ne (m : ℕ) (h : 0 < m) (w : Fin m → ℝ) (i : Fin m) (hi : i ≠ ⟨0, h⟩) :
    negFst m w i = w i := by
  rw [negFst_apply_pos m h, if_neg hi]

theorem negFst_involutive (m : ℕ) (w : Fin m → ℝ) : negFst m (negFst m w) = w := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; exact Subsingleton.elim _ _
  · funext i
    rw [negFst_apply_pos m hm, negFst_apply_pos m hm]
    by_cases hi : i = ⟨0, hm⟩ <;> simp [hi]

theorem flipFst_apply (m : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    flipFst m v = WithLp.toLp 2 (negFst m v.ofLp) := rfl

theorem flipFst_ofLp (m : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    (flipFst m v).ofLp = negFst m v.ofLp := by
  rw [flipFst_apply, WithLp.ofLp_toLp]

theorem flipFst_ofLp_zero (m : ℕ) (h : 0 < m) (v : EuclideanSpace ℝ (Fin m)) :
    (flipFst m v).ofLp ⟨0, h⟩ = -(v.ofLp ⟨0, h⟩) := by
  rw [flipFst_ofLp, negFst_zero m h]

theorem flipFst_ofLp_ne (m : ℕ) (h : 0 < m) (i : Fin m) (hi : i ≠ ⟨0, h⟩)
    (v : EuclideanSpace ℝ (Fin m)) :
    (flipFst m v).ofLp i = v.ofLp i := by
  rw [flipFst_ofLp, negFst_ne m h _ i hi]

theorem flipFst_norm (m : ℕ) (v : EuclideanSpace ℝ (Fin m)) : ‖flipFst m v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = ⟨0, hm⟩
    · subst hi; rw [flipFst_ofLp_zero m hm]; simp
    · rw [flipFst_ofLp_ne m hm i hi]

theorem flipFst_involutive (m : ℕ) (v : EuclideanSpace ℝ (Fin m)) :
    flipFst m (flipFst m v) = v := by
  rw [flipFst_apply, flipFst_ofLp, negFst_involutive, WithLp.toLp_ofLp]

theorem flipFst_injective (m : ℕ) : Function.Injective (flipFst m) :=
  Function.LeftInverse.injective (fun v => flipFst_involutive m v)

/-- **The reflection commutes with the cap map**: the cap map of the suspension step inserts the
last coordinate, and the reflection acts on the first one.  (Requires dimension `n ≥ 1`.) -/
theorem flipFst_capMap (n : ℕ) (hn : 1 ≤ n) (w : EuclideanSpace ℝ (Fin n)) :
    flipFst (n+1) (capMap n w) = capMap n (flipFst n w) := by
  apply WithLp.ofLp_injective 2
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · have hL : (flipFst (n+1) (capMap n w)).ofLp i.castSucc
        = if (i.castSucc : Fin (n+1)) = (⟨0, Nat.succ_pos n⟩ : Fin (n+1))
            then -(w.ofLp i) else w.ofLp i := by
      rw [flipFst_ofLp, negFst_apply_pos (n+1) (Nat.succ_pos n), capMap_castSucc]
    have hR : (capMap n (flipFst n w)).ofLp i.castSucc
        = if i = (⟨0, hn⟩ : Fin n) then -(w.ofLp i) else w.ofLp i := by
      rw [capMap_castSucc, flipFst_ofLp, negFst_apply_pos n hn]
    rw [hL, hR]
    by_cases hi : i = (⟨0, hn⟩ : Fin n)
    · subst hi; rw [if_pos (by exact Fin.ext rfl), if_pos rfl]
    · have hz : (i.castSucc : Fin (n+1)) ≠ (⟨0, Nat.succ_pos n⟩ : Fin (n+1)) := by
        intro h
        apply hi
        apply Fin.ext
        have hv := congrArg Fin.val h
        simpa using hv
      rw [if_neg hz, if_neg hi]
  · have hlast : (Fin.last n : Fin (n+1)) ≠ (⟨0, Nat.succ_pos n⟩ : Fin (n+1)) := by
      intro h
      have hv := Fin.ext_iff.mp h
      simp [Fin.last] at hv
      omega
    rw [flipFst_ofLp, negFst_apply_pos (n+1) (Nat.succ_pos n), if_neg hlast,
      capMap_last, capMap_last, flipFst_norm]

/-- The map `id × flipFst n` of `Y × ℝⁿ`. -/
def fibRefl (m : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(Y × EuclideanSpace ℝ (Fin m), Y × EuclideanSpace ℝ (Fin m)) where
  toFun := fun p => (p.1, flipFst m p.2)
  continuous_toFun := continuous_fst.prodMk ((flipFst m).continuous.comp continuous_snd)

@[simp] theorem fibRefl_apply (m : ℕ) (Y : Type) [TopologicalSpace Y]
    (p : Y × EuclideanSpace ℝ (Fin m)) : fibRefl m Y p = (p.1, flipFst m p.2) := rfl

/-- The restriction of the reflection to the ball bundle `Y × Dᵐ`. -/
def fibReflBall (m : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(Y × MBall m, Y × MBall m) where
  toFun := fun p => (p.1, ⟨flipFst m p.2.1, by
    show ‖flipFst m p.2.1‖ ≤ 1; rw [flipFst_norm]; exact p.2.2⟩)
  continuous_toFun := continuous_fst.prodMk (Continuous.subtype_mk
    ((flipFst m).continuous.comp (continuous_subtype_val.comp continuous_snd))
    (fun p => by
      show ‖flipFst m ((Subtype.val ∘ Prod.snd) p)‖ ≤ 1
      rw [flipFst_norm]
      exact p.2.2))

/-- The restriction of the reflection to the sphere bundle `Y × Sᵐ`. -/
def fibReflMSph (m : ℕ) (Y : Type) [TopologicalSpace Y] :
    C(Y × MSph m, Y × MSph m) where
  toFun := fun p => (p.1, ⟨flipFst m p.2.1, by
    show ‖flipFst m p.2.1‖ = 1; rw [flipFst_norm]; exact p.2.2⟩)
  continuous_toFun := continuous_fst.prodMk (Continuous.subtype_mk
    ((flipFst m).continuous.comp (continuous_subtype_val.comp continuous_snd))
    (fun p => by
      show ‖flipFst m ((Subtype.val ∘ Prod.snd) p)‖ = 1
      rw [flipFst_norm]
      exact p.2.2))

@[simp] theorem fibReflMSph_apply (m : ℕ) (Y : Type) [TopologicalSpace Y] (p : Y × MSph m) :
    (fibReflMSph m Y p).2.1 = flipFst m p.2.1 := rfl

/-- The reflection preserves the sphere bundle `Sph Y m`. -/
theorem fibRefl_mem_sph (m : ℕ) (Y : Type) [TopologicalSpace Y] :
    ∀ p ∈ Sph Y m, fibRefl m Y p ∈ Sph Y m := by
  intro p hp
  show ‖flipFst m p.2‖ = 1
  rw [flipFst_norm]; exact hp

/-- The reflection preserves the punctured bundle `Punct Y m`. -/
theorem fibRefl_mem_punct (m : ℕ) (Y : Type) [TopologicalSpace Y] :
    ∀ p ∈ Punct Y m, fibRefl m Y p ∈ Punct Y m := by
  intro p hp
  show flipFst m p.2 ≠ 0
  intro h
  exact hp (flipFst_injective m (h.trans (map_zero (flipFst m)).symm))

/-- The reflection preserves the "lower region" part `SphB` of the sphere bundle of rank `n+1`
(requires `n ≥ 1`, since the condition defining `mLower` involves the *last* coordinate). -/
theorem fibReflMSph_mem_SphB (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] :
    ∀ p ∈ SphB Y n, fibReflMSph (n+1) Y p ∈ SphB Y n := by
  intro p hp
  obtain ⟨h1, h2⟩ := hp
  refine ⟨?_, ?_⟩
  · show ‖flipFst (n+1) p.2.1‖ = 1
    rw [flipFst_norm]; exact h1
  · have hlast : (Fin.last n : Fin (n+1)) ≠ (⟨0, Nat.succ_pos n⟩ : Fin (n+1)) := by
      intro h
      have hv := Fin.ext_iff.mp h
      simp [Fin.last] at hv
      omega
    show (flipFst (n+1) p.2.1).ofLp (Fin.last n) ≤ 1 / 2
    rw [flipFst_ofLp_ne (n+1) (Nat.succ_pos n) (Fin.last n) hlast]
    exact h2

/-- The disc transfer `discFullMap` commutes with the reflection. -/
theorem discFullMap_comp_fibReflBall (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    (CleanA.discFullMap Y n).comp (fibReflBall n Y)
      = (fibRefl n Y).comp (CleanA.discFullMap Y n) := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · rfl
  · rfl

/-- **The cap map commutes with the reflection**: the reflection acts on the first coordinate, and
the cap map inserts the last one (requires `n ≥ 1`). -/
theorem capMapPairSph_comp_fibReflBall (n : ℕ) (hn : 1 ≤ n) (Y : Type) [TopologicalSpace Y] :
    (fibReflMSph (n+1) Y).comp (capMapPairSph Y n)
      = (capMapPairSph Y n).comp (fibReflBall n Y) := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    show flipFst (n+1) (capMap n p.2.1) = capMap n (flipFst n p.2.1)
    rw [flipFst_capMap n hn]

/-- The homeomorphism `prodSubsetHomeoA` commutes with the reflection. -/
theorem prodSubsetHomeoA_symm_comp_fibRefl (n : ℕ) (Y : Type) [TopologicalSpace Y] :
    (fibReflMSph (n+1) Y).comp
        (((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
          C(↥(Sph Y (n+1)), Y × MSph (n+1))))
      = (((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin (n+1))) (mSph (n+1))).symm :
          C(↥(Sph Y (n+1)), Y × MSph (n+1)))).comp
          (restrictMap (fibRefl (n+1) Y) (Sph Y (n+1)) (Sph Y (n+1))
            (fibRefl_mem_sph (n+1) Y)) := by
  apply ContinuousMap.ext
  intro p
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

/-- The determinant of `negFst m` is `-1` (for `m ≥ 1`). -/
theorem negFst_det (m : ℕ) (hm : 0 < m) : LinearMap.det (negFst m) = -1 := by
  have hfun : negFst m = LinearMap.pi (fun i : Fin m =>
      (if i = ⟨0, hm⟩ then -LinearMap.id else LinearMap.id) ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext
    intro v
    funext i
    rw [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj, negFst_apply_pos m hm]
    by_cases hi : i = ⟨0, hm⟩
    · subst hi; simp
    · simp [hi]
  rw [hfun, LinearMap.det_pi]
  have hprod : ∀ i : Fin m, LinearMap.det
      (if i = ⟨0, hm⟩ then -LinearMap.id else (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) =
      (if i = ⟨0, hm⟩ then (-1 : ℝ) else 1) := by
    intro i
    by_cases hi : i = ⟨0, hm⟩
    · subst hi
      rw [if_pos rfl, if_pos rfl]
      show LinearMap.det (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) = -1
      rw [show (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) = (-1 : ℝ) • LinearMap.id from by ext; simp]
      rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_self]
      norm_num
    · rw [if_neg hi, if_neg hi, LinearMap.det_id]
  rw [Finset.prod_congr rfl (fun i _ => hprod i)]
  rw [Finset.prod_eq_single (⟨0, hm⟩ : Fin m) (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ _) h)]
  simp

/-- **The determinant of the reflection is `-1`**: `flipFst m` reverses the orientation of `ℝᵐ`
(for `m ≥ 1`). -/
theorem flipFst_det (m : ℕ) (hm : 0 < m) : LinearMap.det (flipFst m).toLinearMap < 0 := by
  let e : (Fin m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (((EuclideanSpace.equiv (Fin m) ℝ).symm).toLinearEquiv : (Fin m → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
  let f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] (Fin m → ℝ) :=
    (((EuclideanSpace.equiv (Fin m) ℝ)).toLinearEquiv : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] (Fin m → ℝ))
  have hconj : (flipFst m).toLinearMap = e ∘ₗ negFst m ∘ₗ f := by
    apply LinearMap.ext
    intro v
    rfl
  rw [hconj]
  have hle : LinearMap.det (e ∘ₗ negFst m ∘ₗ f) = -1 := by
    have h := LinearMap.det_conj (negFst m) (((EuclideanSpace.equiv (Fin m) ℝ)).toLinearEquiv.symm)
    rw [negFst_det m hm] at h
    exact h
  rw [hle]
  norm_num

end

end Work.Thom.Orientation
