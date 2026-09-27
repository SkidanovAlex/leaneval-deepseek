import Mathlib
import Submission.Work.Whitney.BumpModel.Defs
import Submission.Work.Whitney.BumpModel.structMap_immersion

namespace Work.Whitney.BumpModel

open Work.Whitney

noncomputable section

/-- Smooth (`C^∞`) version of `contDiff_uhat`: with `ContDiff ℝ (⊤ : ℕ∞)` the function
`û = χ/(1 + ∑xᵢ²)` is again `C^∞`. -/
theorem contDiff_uhat_smooth (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) : ContDiff ℝ (⊤ : ℕ∞) (uhat n χ) := by
  unfold uhat
  exact hχ.div ((contDiff_bumpU n).of_le le_top) fun x => ne_of_gt (bumpU_pos n x)

/-- The structure map is differentiable with the explicit derivative `structMapImmDeriv`, under the
`C^∞` hypothesis. -/
theorem structMap_hasFDerivAt_infty (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (x : Fin n → ℝ) :
    HasFDerivAt (structMap n χ) (structMapImmDeriv n χ x) x := by
  have hu : HasFDerivAt (uhat n χ) (fderiv ℝ (uhat n χ) x) x :=
    ((contDiff_uhat_smooth n hχ).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hp : HasFDerivAt (fun y : Fin n → ℝ => y 0) (structMapImmPt n) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (0 : Fin n)).hasFDerivAt
  have hfst : HasFDerivAt (fun y : Fin n → ℝ => y - (2 * y 0 * uhat n χ y) • e0 n)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ) -
        ((2 : ℝ) • (x 0 • fderiv ℝ (uhat n χ) x + uhat n χ x • structMapImmPt n)).smulRight
          (e0 n)) x := by
    have h1 : HasFDerivAt (fun y : Fin n → ℝ => y 0 * uhat n χ y)
        (x 0 • fderiv ℝ (uhat n χ) x + uhat n χ x • structMapImmPt n) x := hp.mul hu
    have h2 : HasFDerivAt (fun y : Fin n → ℝ => 2 * (y 0 * uhat n χ y))
        ((2 : ℝ) • (x 0 • fderiv ℝ (uhat n χ) x + uhat n χ x • structMapImmPt n)) x :=
      h1.const_mul 2
    have h3 : HasFDerivAt (fun y : Fin n → ℝ => (2 * (y 0 * uhat n χ y)) • e0 n)
        (((2 : ℝ) • (x 0 • fderiv ℝ (uhat n χ) x + uhat n χ x • structMapImmPt n)).smulRight
          (e0 n)) x := h2.smul_const _
    have h4 : HasFDerivAt (fun y : Fin n → ℝ => y - (2 * (y 0 * uhat n χ y)) • e0 n)
        ((ContinuousLinearMap.id ℝ (Fin n → ℝ)) -
          ((2 : ℝ) • (x 0 • fderiv ℝ (uhat n χ) x + uhat n χ x • structMapImmPt n)).smulRight
            (e0 n)) x :=
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)).hasFDerivAt.sub h3
    simpa only [mul_assoc] using h4
  have hsnd : HasFDerivAt
      (fun y : Fin n → ℝ => uhat n χ y • e0 n + (uhat n χ y * y 0) • (y - y 0 • e0 n))
      ((fderiv ℝ (uhat n χ) x).smulRight (e0 n) +
        ((uhat n χ x * x 0) •
            (ContinuousLinearMap.id ℝ (Fin n → ℝ) -
              (structMapImmPt n).smulRight (e0 n)) +
          (uhat n χ x • structMapImmPt n + x 0 • fderiv ℝ (uhat n χ) x).smulRight
            (x - x 0 • e0 n))) x := by
    have hA : HasFDerivAt (fun y : Fin n → ℝ => uhat n χ y • e0 n)
        ((fderiv ℝ (uhat n χ) x).smulRight (e0 n)) x := hu.smul_const _
    have hw : HasFDerivAt (fun y : Fin n → ℝ => y - y 0 • e0 n)
        ((ContinuousLinearMap.id ℝ (Fin n → ℝ)) -
          (structMapImmPt n).smulRight (e0 n)) x :=
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)).hasFDerivAt.sub (hp.smul_const _)
    have hψ : HasFDerivAt (fun y : Fin n → ℝ => uhat n χ y * y 0)
        (uhat n χ x • structMapImmPt n + x 0 • fderiv ℝ (uhat n χ) x) x := hu.mul hp
    have hB : HasFDerivAt (fun y : Fin n → ℝ => (uhat n χ y * y 0) • (y - y 0 • e0 n))
        ((uhat n χ x * x 0) •
            ((ContinuousLinearMap.id ℝ (Fin n → ℝ)) -
              (structMapImmPt n).smulRight (e0 n)) +
          (uhat n χ x • structMapImmPt n + x 0 • fderiv ℝ (uhat n χ) x).smulRight
            (x - x 0 • e0 n)) x := hψ.smul hw
    exact hA.add hB
  exact hfst.prodMk hsnd


/-- The derivative of the structure map at `x`, applied to `v`, under the `C^∞` hypothesis. -/
theorem structMap_fderiv_smooth (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (x v : Fin n → ℝ) :
    (fderiv ℝ (structMap n χ) x) v =
      (v - (2 * (x 0 * (fderiv ℝ (uhat n χ) x) v + uhat n χ x * v 0)) • e0 n,
       (fderiv ℝ (uhat n χ) x) v • e0 n
        + (x 0 * (fderiv ℝ (uhat n χ) x) v + uhat n χ x * v 0) • (x - x 0 • e0 n)
        + (uhat n χ x * x 0) • (v - v 0 • e0 n)) := by
  rw [show fderiv ℝ (structMap n χ) x = structMapImmDeriv n χ x from
    (structMap_hasFDerivAt_infty n hχ x).fderiv]
  simp only [structMapImmDeriv, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, structMapImmPt,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  refine Prod.ext ?_ ?_
  · rfl
  · rw [show uhat n χ x * v 0 + x 0 * (fderiv ℝ (uhat n χ) x) v =
        x 0 * (fderiv ℝ (uhat n χ) x) v + uhat n χ x * v 0 by ring]
    abel


/-- The structure map is an immersion, with the (correct, `C^∞`) smoothness hypothesis `ContDiff ℝ (⊤ : ℕ∞)`; this is `structMap_immersion` with its analyticity hypothesis `ContDiff ℝ ⊤` replaced by smoothness. -/
theorem structMap_immersion_infty (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hcrit : ∀ t : ℝ, Work.Whitney.uhat n χ (t • Work.Whitney.e0 n) = 1 / 2 →
      (fderiv ℝ (Work.Whitney.uhat n χ) (t • Work.Whitney.e0 n)) (Work.Whitney.e0 n) ≠ 0) :
    ∀ x : Fin n → ℝ, Function.Injective (fderiv ℝ (Work.Whitney.structMap n χ) x) := by
  intro x v w hvw
  set d : Fin n → ℝ := v - w with hd
  have h0 : (fderiv ℝ (structMap n χ) x) d = 0 := by rw [hd, map_sub, hvw, sub_self]
  rw [structMap_fderiv_smooth n hχ x d] at h0
  have hfst : d - (2 * (x 0 * (fderiv ℝ (uhat n χ) x) d + uhat n χ x * d 0)) • e0 n = 0 := by
    simpa using congrArg Prod.fst h0
  have hsnd : (fderiv ℝ (uhat n χ) x) d • e0 n
      + (x 0 * (fderiv ℝ (uhat n χ) x) d + uhat n χ x * d 0) • (x - x 0 • e0 n)
      + (uhat n χ x * x 0) • (d - d 0 • e0 n) = 0 := by
    simpa using congrArg Prod.snd h0
  have hd_eq : d = (2 * (x 0 * (fderiv ℝ (uhat n χ) x) d + uhat n χ x * d 0)) • e0 n :=
    sub_eq_zero.mp hfst
  have hd0 : d 0 = 2 * (x 0 * (fderiv ℝ (uhat n χ) x) d + uhat n χ x * d 0) := by
    have h := congrFun hd_eq 0
    simpa [e0] using h
  have hdsub : d - d 0 • e0 n = 0 := by
    have h1 : d = d 0 • e0 n := hd_eq.trans (congrArg (fun s : ℝ => s • e0 n) hd0.symm)
    rw [h1]
    simp [e0]
  have key : (fderiv ℝ (uhat n χ) x) d • e0 n
      + (x 0 * (fderiv ℝ (uhat n χ) x) d + uhat n χ x * d 0) • (x - x 0 • e0 n) = 0 := by
    have h := hsnd
    rw [hdsub] at h
    simpa using h
  have hgd : (fderiv ℝ (uhat n χ) x) d = 0 := by
    have h := congrFun key 0
    simpa [e0] using h
  have hc_eq : x 0 * (fderiv ℝ (uhat n χ) x) d + uhat n χ x * d 0 = uhat n χ x * d 0 := by
    rw [hgd]; ring
  have hdz : d = 0 := by
    by_cases hz : x - x 0 • e0 n = 0
    · have hx : x = x 0 • e0 n := sub_eq_zero.mp hz
      have hd0' : d 0 = 2 * (uhat n χ x * d 0) := by
        have h := hd0
        rw [hgd] at h
        linarith
      by_cases hv0 : d 0 = 0
      · rw [hd_eq, hc_eq, hv0]
        simp
      · have hA2 : uhat n χ x = 1 / 2 := by
          have hmul : d 0 * (2 * uhat n χ x - 1) = 0 := by nlinarith
          rcases mul_eq_zero.mp hmul with h | h
          · exact absurd h hv0
          · linarith
        have hge0 : (fderiv ℝ (uhat n χ) x) (e0 n) = 0 := by
          have h1 : (fderiv ℝ (uhat n χ) x) d = d 0 * (fderiv ℝ (uhat n χ) x) (e0 n) := by
            conv_lhs => rw [hd_eq, hc_eq]
            rw [map_smul, smul_eq_mul]
            rw [show 2 * (uhat n χ x * d 0) = d 0 by linarith]
          rw [h1] at hgd
          rcases mul_eq_zero.mp hgd with h | h
          · exact absurd h hv0
          · exact h
        have hA' : uhat n χ (x 0 • e0 n) = 1 / 2 := by rw [← hx, hA2]
        have hcrit' := hcrit (x 0) hA'
        rw [← hx] at hcrit'
        exact absurd hge0 hcrit'
    · have hc0 : x 0 * (fderiv ℝ (uhat n χ) x) d + uhat n χ x * d 0 = 0 := by
        obtain ⟨i, hi⟩ : ∃ i, (x - x 0 • e0 n) i ≠ 0 := by
          by_contra h
          push Not at h
          exact hz (funext h)
        have hi0 : i ≠ 0 := by
          rintro rfl
          simp [e0] at hi
        have hkey := congrFun key i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hkey
        have hei : (e0 n) i = 0 := by simp [e0, hi0]
        rw [hei, mul_zero, zero_add] at hkey
        rcases mul_eq_zero.mp hkey with h | h
        · exact h
        · exact absurd h hi
      rw [hd_eq, hc0]
      simp
  have : v - w = 0 := by rw [← hd]; exact hdz
  exact sub_eq_zero.mp this

end

end Work.Whitney.BumpModel
