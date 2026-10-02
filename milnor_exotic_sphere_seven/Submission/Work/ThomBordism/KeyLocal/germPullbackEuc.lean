import Mathlib
import Submission.Work.ThomBordism.FrameSigns.germPullbackLocal
import Submission.Work.ThomBordism.linearModelActionN
import Submission.Work.ThomBordism.KeyLocal.germFDerivEuc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped unitInterval Topology
open CategoryTheory

/-!
# The pullback along a germ diffeomorphism of `ℝⁿ` fixed at `0`, in the ambient dimension `n`

This is the general-dimension version of `Work.ThomBordism.FrameSigns.germPullbackLocal` (the case
`n = 8`): for an open set `W ∋ 0` of `ℝⁿ`, a continuous map `F` on `W` with `F 0 = 0`, `F z ≠ 0`
for `z ∈ W ∖ 0`, differentiable at `0` with derivative an invertible linear `L`, the pullback
`(F|_W)^*` on `Hⁿ(W, W∖0; ℤ)` agrees with the pullback along the inclusion up to the sign of
`det L`.

The proof is the same as in dimension `8`, reproduced here with the model space
`ℝⁿ = EuclideanSpace ℝ (Fin n)`:

* excision identifies `(↥W, W∖0)` with an open ball around `0` inside `W`;
* on that ball, `F` is homotopic (through maps of pairs) to the composite of `F` on a smaller closed
  ball with the radial retraction `z ↦ z/2`;
* `germFDerivEuc` (proved in the companion module
  `Submission.Work.ThomBordism.KeyLocal.germFDerivEuc`) says that on a closed ball the germ map
  and its derivative have the same pullback;
* `Work.ThomBordism.FrameSigns.linearModelActionN` computes the action of the linear map as
  `sign (det L)`.
-/

namespace Work.ThomBordism.KeyLocal

noncomputable section

section Defs

variable {n : ℕ}

/-! ## The general-dimension objects of the proof (dimension-`n` copies of `germPullbackDefs`) -/

/-- The punctured model space `ℝⁿ ∖ {0}`. -/
abbrev kpB0 : Set (EuclideanSpace ℝ (Fin n)) := {v : EuclideanSpace ℝ (Fin n) | v ≠ 0}

/-- The puncture, as a subset of `↥W`. -/
abbrev kpBW (W : Set (EuclideanSpace ℝ (Fin n))) : Set ↥W := {z : ↥W | (z : EuclideanSpace ℝ (Fin n)) ≠ 0}

/-- The open ball of radius `r` around the origin, as a subset of `↥W`. -/
abbrev kpU (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) : Set ↥W := {z : ↥W | (z : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r}

/-- The punctured part of `kpU`. -/
abbrev kpAU (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) : Set ↥(kpU r W) :=
  {z : ↥(kpU r W) | ((z : ↥W) : EuclideanSpace ℝ (Fin n)) ≠ 0}

/-- The closed ball of radius `r/2` in `ℝⁿ` (the target of the retraction `kpρ`). -/
abbrev kpCl (n : ℕ) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2)

/-- The punctured part of `kpCl`. -/
abbrev kpACl (n : ℕ) (r : ℝ) : Set ↥(kpCl n r) := {z : ↥(kpCl n r) | (z : EuclideanSpace ℝ (Fin n)) ≠ 0}

/-- The coercion `↥(kpU r W) → ↥W`. -/
def kpc (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) : C(↥(kpU r W), ↥W) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `↥W → ℝⁿ`. -/
def kpiW (W : Set (EuclideanSpace ℝ (Fin n))) : C(↥W, EuclideanSpace ℝ (Fin n)) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The inclusion `↥(kpU r W) → ℝⁿ`. -/
def kpiU (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) : C(↥(kpU r W), EuclideanSpace ℝ (Fin n)) :=
  (kpiW W).comp (kpc r W)

/-- `F` restricted to `W`. -/
def kpFW (W : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hFc : ContinuousOn F W) : C(↥W, EuclideanSpace ℝ (Fin n)) :=
  ⟨fun z => F (z : EuclideanSpace ℝ (Fin n)), continuousOn_iff_continuous_domRestrict.mp hFc⟩

/-- `F` restricted to the open ball `kpU`. -/
def kpFU (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hFc : ContinuousOn F W) :
    C(↥(kpU r W), EuclideanSpace ℝ (Fin n)) :=
  (kpFW W F hFc).comp (kpc r W)

@[simp] theorem kpFU_apply (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hFc : ContinuousOn F W)
    (z : ↥(kpU r W)) : kpFU r W F hFc z = F ((z : ↥W) : EuclideanSpace ℝ (Fin n)) := rfl

/-- `F` restricted to the closed ball `kpCl`, using that `closedBall 0 r ⊆ W`. -/
def kpFCl (r : ℝ) (hr : 0 < r) (W : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hFc : ContinuousOn F W)
    (hrW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ W) : C(↥(kpCl n r), EuclideanSpace ℝ (Fin n)) :=
  ⟨fun z => F (z : EuclideanSpace ℝ (Fin n)), hFc.comp_continuous continuous_subtype_val
    (fun z => hrW (Metric.closedBall_subset_closedBall (by linarith) z.2))⟩

@[simp] theorem kpFCl_apply (r : ℝ) (hr : 0 < r) (W : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hFc : ContinuousOn F W) (hrW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ W) (z : ↥(kpCl n r)) :
    kpFCl r hr W F hFc hrW z = F (z : EuclideanSpace ℝ (Fin n)) := rfl

/-- The pair condition for `kpFU`. -/
theorem kpFUmem (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hFc : ContinuousOn F W)
    (hnz : ∀ z ∈ W, z ≠ 0 → F z ≠ 0) :
    ∀ z ∈ kpAU r W, kpFU r W F hFc z ∈ kpB0 :=
  fun z hz => hnz ((z : ↥W) : EuclideanSpace ℝ (Fin n)) ((z : ↥W).2) hz

/-- The pair condition for `kpFCl`. -/
theorem kpFClmem (r : ℝ) (hr : 0 < r) (W : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hFc : ContinuousOn F W) (hnz : ∀ z ∈ W, z ≠ 0 → F z ≠ 0)
    (hrW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ W) :
    ∀ z ∈ kpACl n r, kpFCl r hr W F hFc hrW z ∈ kpB0 :=
  fun z hz => hnz (z : EuclideanSpace ℝ (Fin n))
    (hrW (Metric.closedBall_subset_closedBall (by linarith) z.2)) hz

/-- The pair condition for `kpiU`. -/
theorem kpiUmem (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) :
    ∀ z ∈ kpAU r W, kpiU r W z ∈ kpB0 := fun z hz => hz

/-- The linear map `L` as a continuous map `ℝⁿ → ℝⁿ`. -/
def kpL (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) := ⟨fun z => L z, L.continuous⟩

/-- `L` restricted to the closed ball `kpCl`. -/
def kpLCl (r : ℝ) (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : C(↥(kpCl n r), EuclideanSpace ℝ (Fin n)) :=
  ⟨fun z => L (z : EuclideanSpace ℝ (Fin n)), L.continuous.comp continuous_subtype_val⟩

@[simp] theorem kpLCl_apply (r : ℝ) (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (z : ↥(kpCl n r)) :
    kpLCl r L z = L (z : EuclideanSpace ℝ (Fin n)) := rfl

/-- `L` restricted to the open ball `kpU`. -/
def kpLU (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : C(↥(kpU r W), EuclideanSpace ℝ (Fin n)) :=
  (kpL L).comp (kpiU r W)

@[simp] theorem kpLU_apply (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (z : ↥(kpU r W)) :
    kpLU r W L z = L ((z : ↥W) : EuclideanSpace ℝ (Fin n)) := rfl

/-- The pair condition for `kpLU`. -/
theorem kpLUmem (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hL : Function.Bijective L) :
    ∀ z ∈ kpAU r W, kpLU r W L z ∈ kpB0 := by
  intro z hz h
  exact hz (hL.1 (by rw [← kpLU_apply r W L z]; exact h.trans (map_zero L).symm))

/-- The pair condition for `kpLCl`. -/
theorem kpLClmem (r : ℝ) (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hL : Function.Bijective L) :
    ∀ z ∈ kpACl n r, kpLCl r L z ∈ kpB0 := by
  intro z hz h
  exact hz (hL.1 (by rw [← kpLCl_apply r L z]; exact h.trans (map_zero L).symm))

/-- The membership of the retraction: `z ↦ z/2` maps the open ball of radius `r` into the closed
ball of radius `r/2`. -/
theorem kpρ_mem (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) (z : ↥(kpU r W)) :
    (1 / 2 : ℝ) • ((z : ↥W) : EuclideanSpace ℝ (Fin n)) ∈ kpCl n r := by
  have hz : ‖((z : ↥W) : EuclideanSpace ℝ (Fin n))‖ < r := by
    have h : ((z : ↥W) : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := z.2
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hs : ‖(1 / 2 : ℝ) • ((z : ↥W) : EuclideanSpace ℝ (Fin n))‖ = (1 / 2) * ‖((z : ↥W) : EuclideanSpace ℝ (Fin n))‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [Metric.mem_closedBall, dist_zero_right, hs]
  linarith

/-- The radial retraction of the open ball of radius `r` onto the closed ball of radius `r/2`,
`z ↦ z/2`. -/
def kpρ (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) : C(↥(kpU r W), ↥(kpCl n r)) :=
  ⟨fun z => ⟨(1 / 2 : ℝ) • ((z : ↥W) : EuclideanSpace ℝ (Fin n)), kpρ_mem r W z⟩,
    Continuous.subtype_mk
      (show Continuous fun z : ↥(kpU r W) => (1 / 2 : ℝ) • ((z : ↥W) : EuclideanSpace ℝ (Fin n)) from
        (continuous_const : Continuous fun _ : ↥(kpU r W) => (1 / 2 : ℝ)).smul
          (continuous_subtype_val.comp continuous_subtype_val))
      (kpρ_mem r W)⟩

@[simp] theorem kpρ_apply (r : ℝ) (W : Set (EuclideanSpace ℝ (Fin n))) (z : ↥(kpU r W)) :
    ((kpρ r W z : ↥(kpCl n r)) : EuclideanSpace ℝ (Fin n)) = (1 / 2 : ℝ) • ((z : ↥W) : EuclideanSpace ℝ (Fin n)) := rfl

end Defs

/-! ## The target -/

theorem germPullbackEuc {n : ℕ} (hn : 1 ≤ n)
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W) (h0 : 0 ∈ W)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hFc : ContinuousOn F W) (hF0 : F 0 = 0)
    (hnz : ∀ z ∈ W, z ≠ 0 → F z ≠ 0)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : Function.Bijective L) (hdF : HasFDerivAt F L 0)
    (hdet : LinearMap.det L.toLinearMap ≠ 0) :
    ∀ ξ : Work.Thom.RelCoh ℤ n (EuclideanSpace ℝ (Fin n))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
      (Work.Thom.relCohMap
          (⟨fun z : W => F z, continuousOn_iff_continuous_domRestrict.mp hFc⟩ :
            C(W, EuclideanSpace ℝ (Fin n)))
          ({z : W | (z : EuclideanSpace ℝ (Fin n)) ≠ 0})
          ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
          (fun z hz => hnz z z.2 hz) ℤ n).hom ξ
        = (if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1) •
          (Work.Thom.relCohMap
            (⟨fun z : W => (z : EuclideanSpace ℝ (Fin n)), continuous_subtype_val⟩ :
              C(W, EuclideanSpace ℝ (Fin n)))
            ({z : W | (z : EuclideanSpace ℝ (Fin n)) ≠ 0})
            ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
            (fun z hz => hz) ℤ n).hom ξ := by
  intro ξ
  set s : ℤ := if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1 with hs_def
  -- a radius whose closed ball lies in `W`
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0)
  set r : ℝ := ε / 2 with hr_def
  have hr : 0 < r := by rw [hr_def]; linarith
  have hrW : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ W := by
    intro z hz
    refine hεW (Metric.mem_ball.mpr ?_)
    have hz' : dist z (0 : EuclideanSpace ℝ (Fin n)) ≤ r := Metric.mem_closedBall.mp hz
    rw [hr_def] at hz'
    linarith
  -- the open ball as a subset of `↥W`, and the excision isomorphism
  have hU : IsOpen (kpU r W) := by
    show IsOpen ((fun z : ↥W => (z : EuclideanSpace ℝ (Fin n))) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
    exact Metric.isOpen_ball.preimage continuous_subtype_val
  have hA : IsOpen (kpBW W) := by
    show IsOpen ((fun z : ↥W => (z : EuclideanSpace ℝ (Fin n))) ⁻¹' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
    exact isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
  have hcov : kpU r W ∪ kpBW W = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hz : (z : EuclideanSpace ℝ (Fin n)) = 0
    · exact Or.inl (by
        show (z : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
        rw [hz]; exact Metric.mem_ball_self hr)
    · exact Or.inr hz
  have hmemUW : ∀ z ∈ kpAU r W, (kpc r W) z ∈ kpBW W := fun z hz => hz
  haveI hIsoK : CategoryTheory.IsIso
      (Work.Thom.relCohMap (kpc r W) (kpAU r W) (kpBW W) (fun z hz => hz) ℤ n) := by
    exact Work.Cohomology.capRel_excision_isIso (TopCat.of ↥W) (kpU r W) (kpBW W) hU hA
      hcov n (fun z hz => hz)
  have hKinj : Function.Injective
      (Work.Thom.relCohMap (kpc r W) (kpAU r W) (kpBW W) (fun z hz => hz) ℤ n).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  -- the coefficient of the first homotopy
  have hcoef1_norm_le : ∀ u : unitInterval, ‖((1 - (u : ℝ)) + (u : ℝ) * (1 / 2))‖ ≤ 1 := by
    intro u
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [u.2.1, u.2.2], by linarith [u.2.1, u.2.2]⟩
  have h1mem : ∀ p : unitInterval × ↥(kpU r W),
      (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2)) • ((p.2 : ↥W) : EuclideanSpace ℝ (Fin n))) ∈ W := by
    intro p
    refine hrW ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz : ‖((p.2 : ↥W) : EuclideanSpace ℝ (Fin n))‖ ≤ r := by
      have h : ((p.2 : ↥W) : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r := p.2.2
      rw [Metric.mem_ball, dist_zero_right] at h
      exact le_of_lt h
    calc ‖((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2)) • ((p.2 : ↥W) : EuclideanSpace ℝ (Fin n))‖
        = ‖((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2))‖ * ‖((p.2 : ↥W) : EuclideanSpace ℝ (Fin n))‖ := norm_smul _ _
      _ ≤ 1 * r := mul_le_mul (hcoef1_norm_le p.1) hz (norm_nonneg _) zero_le_one
      _ = r := one_mul r
  have h1cont : Continuous fun p : unitInterval × ↥(kpU r W) =>
      (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2)) • ((p.2 : ↥W) : EuclideanSpace ℝ (Fin n))) :=
    (((continuous_const : Continuous fun _ : unitInterval × ↥(kpU r W) => (1 : ℝ)).sub
        (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  -- the first homotopy: `F|_U ≃ (F|_cl) ∘ ρ`
  let hH1 : (kpFU r W F hFc).Homotopy ((kpFCl r hr W F hFc hrW).comp (kpρ r W)) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p => F (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2)) • ((p.2 : ↥W) : EuclideanSpace ℝ (Fin n))),
        hFc.comp_continuous h1cont h1mem⟩
      (fun z => by
        show F (((1 - ((0 : unitInterval) : ℝ)) + ((0 : unitInterval) : ℝ) * (1 / 2)) •
          ((z : ↥W) : EuclideanSpace ℝ (Fin n))) = kpFU r W F hFc z
        have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
        rw [h0]
        simp only [sub_zero, zero_mul, zero_add, add_zero, one_mul, zero_smul, one_smul, kpFU_apply])
      (fun z => by
        show F (((1 - ((1 : unitInterval) : ℝ)) + ((1 : unitInterval) : ℝ) * (1 / 2)) •
          ((z : ↥W) : EuclideanSpace ℝ (Fin n))) = ((kpFCl r hr W F hFc hrW).comp (kpρ r W)) z
        have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1]
        simp only [sub_self, zero_mul, one_mul, zero_add, add_zero, zero_smul, one_smul]
        rw [ContinuousMap.comp_apply, kpFCl_apply, kpρ_apply])
  have hH1mem : ∀ (t : unitInterval) (z : ↥(kpU r W)), z ∈ kpAU r W → hH1 (t, z) ∈ kpB0 := by
    intro t z hz
    show F (((1 - (t : ℝ)) + (t : ℝ) * (1 / 2)) • ((z : ↥W) : EuclideanSpace ℝ (Fin n))) ≠ 0
    refine hnz _ (h1mem (t, z)) ?_
    apply smul_ne_zero
    · intro hc
      have h := t.2
      nlinarith [h.1, h.2]
    · exact hz
  -- the second homotopy: `(L|_cl) ∘ ρ ≃ L|_U`
  have h2cont : Continuous fun p : unitInterval × ↥(kpU r W) =>
      (((1 - (p.1 : ℝ)) / 2 + (p.1 : ℝ)) • ((p.2 : ↥W) : EuclideanSpace ℝ (Fin n))) :=
    ((((continuous_const : Continuous fun _ : unitInterval × ↥(kpU r W) => (1 : ℝ)).sub
        (continuous_subtype_val.comp continuous_fst)).div_const 2).add
      (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  let hH2 : ((kpLCl r L).comp (kpρ r W)).Homotopy (kpLU r W L) :=
    ContinuousMap.Homotopy.mk
      ⟨fun p => L (((1 - (p.1 : ℝ)) / 2 + (p.1 : ℝ)) • ((p.2 : ↥W) : EuclideanSpace ℝ (Fin n))),
        L.continuous.comp h2cont⟩
      (fun z => by
        show L (((1 - ((0 : unitInterval) : ℝ)) / 2 + ((0 : unitInterval) : ℝ)) •
          ((z : ↥W) : EuclideanSpace ℝ (Fin n))) = ((kpLCl r L).comp (kpρ r W)) z
        have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
        rw [h0]
        simp only [sub_zero, add_zero, zero_add, zero_smul]
        rw [ContinuousMap.comp_apply, kpLCl_apply, kpρ_apply])
      (fun z => by
        show L (((1 - ((1 : unitInterval) : ℝ)) / 2 + ((1 : unitInterval) : ℝ)) •
          ((z : ↥W) : EuclideanSpace ℝ (Fin n))) = kpLU r W L z
        have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1]
        simp only [sub_self, zero_div, zero_add, one_smul, kpLU_apply])
  have hH2mem : ∀ (t : unitInterval) (z : ↥(kpU r W)), z ∈ kpAU r W → hH2 (t, z) ∈ kpB0 := by
    intro t z hz
    show L (((1 - (t : ℝ)) / 2 + (t : ℝ)) • ((z : ↥W) : EuclideanSpace ℝ (Fin n))) ≠ 0
    intro h
    have hcoef : ((1 - (t : ℝ)) / 2 + (t : ℝ)) ≠ 0 := by
      intro hc
      have h' := t.2
      nlinarith [h'.1, h'.2]
    exact (smul_ne_zero hcoef hz) (hL.1 (by simpa using h))
  -- the pair conditions used below
  have hρmem : ∀ z ∈ kpAU r W, (kpρ r W) z ∈ kpACl n r := by
    intro z hz
    show ((kpρ r W z : ↥(kpCl n r)) : EuclideanSpace ℝ (Fin n)) ≠ 0
    rw [kpρ_apply]
    exact smul_ne_zero (by norm_num) hz
  have hFClρmem : ∀ z ∈ kpAU r W,
      ((kpFCl r hr W F hFc hrW).comp (kpρ r W)) z ∈ kpB0 :=
    fun z hz => kpFClmem r hr W F hFc hnz hrW (kpρ r W z) (hρmem z hz)
  have hLClρmem : ∀ z ∈ kpAU r W,
      ((kpLCl r L).comp (kpρ r W)) z ∈ kpB0 :=
    fun z hz => kpLClmem r L hL (kpρ r W z) (hρmem z hz)
  have hLmem : ∀ z ∈ kpB0, (kpL L) z ∈ kpB0 := by
    intro z hz h
    have h' : L z = 0 := h
    exact hz (hL.1 (by rw [h', map_zero]))
  -- the linear step
  let e₀ : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := LinearEquiv.ofBijective (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) hL
  let A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) := e₀.toContinuousLinearEquiv
  have hAeq : ∀ z : EuclideanSpace ℝ (Fin n), A z = L z := by
    intro z
    change e₀ z = L z
    rw [LinearEquiv.ofBijective_apply]
    rfl
  have hAclm : (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = L := ContinuousLinearMap.ext hAeq
  have hAU : ∀ z ∈ kpB0, (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) z ∈ kpB0 :=
    fun z hz h => hz ((A.map_eq_zero_iff).mp h)
  have hlin : (Work.Thom.relCohMap (kpL L) kpB0 kpB0 hLmem ℤ n).hom ξ = s • ξ := by
    have h1 := Work.ThomBordism.FrameSigns.linearModelActionN hn A (by rw [hAclm]; exact hdet) ξ
    have hmap : (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) = kpL L := by
      apply ContinuousMap.ext
      intro z
      exact hAeq z
    have hmorph : (Work.Thom.relCohMap (A : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n))) kpB0 kpB0 hAU ℤ n)
        = (Work.Thom.relCohMap (kpL L) kpB0 kpB0 hLmem ℤ n) :=
      Work.Thom.relCohMap_congrA kpB0 kpB0 hmap hAU hLmem ℤ n
    have hdetA : (if 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap then (1 : ℤ) else -1)
        = (if 0 < LinearMap.det L.toLinearMap then (1 : ℤ) else -1) := by rw [hAclm]
    rw [hmorph, hdetA] at h1
    rw [h1]
    try exact congrArg (fun t : ℤ => t • ξ) hs_def.symm
  -- the chain of equalities on the open ball
  have hchain : (Work.Thom.relCohMap (kpFU r W F hFc) (kpAU r W) kpB0
        (kpFUmem r W F hFc hnz) ℤ n).hom ξ
      = s • (Work.Thom.relCohMap (kpiU r W) (kpAU r W) kpB0 (kpiUmem r W) ℤ n).hom ξ := by
    have hstep1 := congrArg (fun φ => φ.hom ξ)
      (Work.Thom.relCohMap_homotopic (kpAU r W) kpB0 (kpFUmem r W F hFc hnz) hFClρmem hH1
        hH1mem ℤ n)
    have hstep2 : (Work.Thom.relCohMap ((kpFCl r hr W F hFc hrW).comp (kpρ r W))
          (kpAU r W) kpB0 hFClρmem ℤ n).hom ξ
        = (Work.Thom.relCohMap (kpρ r W) (kpAU r W) (kpACl n r) hρmem ℤ n).hom
            ((Work.Thom.relCohMap (kpFCl r hr W F hFc hrW) (kpACl n r) kpB0
              (kpFClmem r hr W F hFc hnz hrW) ℤ n).hom ξ) := by
      rw [Work.Thom.relCohMap_compA_apply (kpAU r W) (kpACl n r) kpB0 (kpρ r W)
        (kpFCl r hr W F hFc hrW) hρmem (kpFClmem r hr W F hFc hnz hrW) hFClρmem ℤ n ξ]
    have hstep3 : (Work.Thom.relCohMap (kpFCl r hr W F hFc hrW) (kpACl n r) kpB0
          (kpFClmem r hr W F hFc hnz hrW) ℤ n).hom ξ
        = (Work.Thom.relCohMap (kpLCl r L) (kpACl n r) kpB0 (kpLClmem r L hL) ℤ n).hom ξ :=
      germFDerivEuc r hr F L (hFc.mono hrW) hL hF0 hdF
        (fun z hz hz0 => hnz z (hrW hz) hz0) (r / 2) (by linarith) (by linarith) ξ
    have hstep4 : (Work.Thom.relCohMap (kpρ r W) (kpAU r W) (kpACl n r) hρmem ℤ n).hom
          ((Work.Thom.relCohMap (kpLCl r L) (kpACl n r) kpB0 (kpLClmem r L hL) ℤ n).hom ξ)
        = (Work.Thom.relCohMap ((kpLCl r L).comp (kpρ r W)) (kpAU r W) kpB0
            hLClρmem ℤ n).hom ξ := by
      rw [Work.Thom.relCohMap_compA_apply (kpAU r W) (kpACl n r) kpB0 (kpρ r W) (kpLCl r L)
        hρmem (kpLClmem r L hL) hLClρmem ℤ n ξ]
    have hstep5 := congrArg (fun φ => φ.hom ξ)
      (Work.Thom.relCohMap_homotopic (kpAU r W) kpB0 hLClρmem (kpLUmem r W L hL) hH2
        hH2mem ℤ n)
    have hstep6 : (Work.Thom.relCohMap (kpLU r W L) (kpAU r W) kpB0 (kpLUmem r W L hL) ℤ n).hom ξ
        = s • (Work.Thom.relCohMap (kpiU r W) (kpAU r W) kpB0 (kpiUmem r W) ℤ n).hom ξ := by
      have hc := Work.Thom.relCohMap_compA_apply (kpAU r W) kpB0 kpB0 (kpiU r W) (kpL L)
        (kpiUmem r W) hLmem (kpLUmem r W L hL) ℤ n ξ
      have hf : (Work.Thom.relCohMap (kpLU r W L) (kpAU r W) kpB0 (kpLUmem r W L hL) ℤ n).hom ξ
          = (Work.Thom.relCohMap ((kpL L).comp (kpiU r W)) (kpAU r W) kpB0
              (kpLUmem r W L hL) ℤ n).hom ξ := rfl
      rw [hf, ← hc, hlin]
      exact map_zsmul _ s ξ
    calc (Work.Thom.relCohMap (kpFU r W F hFc) (kpAU r W) kpB0 (kpFUmem r W F hFc hnz) ℤ n).hom ξ
        = (Work.Thom.relCohMap ((kpFCl r hr W F hFc hrW).comp (kpρ r W)) (kpAU r W) kpB0
            hFClρmem ℤ n).hom ξ := hstep1
      _ = (Work.Thom.relCohMap (kpρ r W) (kpAU r W) (kpACl n r) hρmem ℤ n).hom
            ((Work.Thom.relCohMap (kpFCl r hr W F hFc hrW) (kpACl n r) kpB0
              (kpFClmem r hr W F hFc hnz hrW) ℤ n).hom ξ) := hstep2
      _ = (Work.Thom.relCohMap (kpρ r W) (kpAU r W) (kpACl n r) hρmem ℤ n).hom
            ((Work.Thom.relCohMap (kpLCl r L) (kpACl n r) kpB0 (kpLClmem r L hL) ℤ n).hom ξ) := by
          rw [hstep3]
      _ = (Work.Thom.relCohMap ((kpLCl r L).comp (kpρ r W)) (kpAU r W) kpB0 hLClρmem ℤ n).hom ξ :=
          hstep4
      _ = (Work.Thom.relCohMap (kpLU r W L) (kpAU r W) kpB0 (kpLUmem r W L hL) ℤ n).hom ξ :=
          hstep5
      _ = s • (Work.Thom.relCohMap (kpiU r W) (kpAU r W) kpB0 (kpiUmem r W) ℤ n).hom ξ :=
          hstep6
  -- transport along the inclusion of the open ball
  have hPW : (Work.Thom.relCohMap (kpc r W) (kpAU r W) (kpBW W) hmemUW ℤ n).hom
        ((Work.Thom.relCohMap (kpFW W F hFc) (kpBW W) kpB0
          (fun z hz => hnz (z : EuclideanSpace ℝ (Fin n)) z.2 hz) ℤ n).hom ξ)
      = s • (Work.Thom.relCohMap (kpc r W) (kpAU r W) (kpBW W) hmemUW ℤ n).hom
        ((Work.Thom.relCohMap (kpiW W) (kpBW W) kpB0 (fun z hz => hz) ℤ n).hom ξ) := by
    rw [Work.Thom.relCohMap_compA_apply (kpAU r W) (kpBW W) kpB0 (kpc r W) (kpFW W F hFc)
      hmemUW (fun z hz => hnz (z : EuclideanSpace ℝ (Fin n)) z.2 hz) (kpFUmem r W F hFc hnz) ℤ n ξ]
    rw [Work.Thom.relCohMap_compA_apply (kpAU r W) (kpBW W) kpB0 (kpc r W) (kpiW W)
      hmemUW (fun z hz => hz) (kpiUmem r W) ℤ n ξ]
    exact hchain
  refine hKinj ?_
  rw [map_zsmul]
  exact hPW
end

end Work.ThomBordism.KeyLocal
