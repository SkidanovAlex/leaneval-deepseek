import Mathlib
import Submission.Work.Whitney.ballPairValSurj
import Submission.Work.Thom.stepDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cone map `Δᵖ → Dᵖ` is a homeomorphism, hence the disc bundle retracts onto the simplex

`Work.Whitney.ballPairVal` is a continuous surjection of the standard `p`-simplex onto the closed
unit ball, carrying `∂Δᵖ` onto `Sᵖ⁻¹`.  Here we prove that it is **injective**, hence (compact
source, Hausdorff target) a homeomorphism, and deduce the existence of the continuous retraction

  `r : Y × Dᵖ → Δᵖ`,  `r (y, ballPairVal z) = z`,  `r (Y × Sᵖ⁻¹) ⊆ ∂Δᵖ`

for `Y` a (possibly empty-but-nonempty) subsingleton, which is the contents of
`Work.Whitney.coneMap_retraction`.

The injectivity rests on the explicit *reconstruction formula*: if `u := ballPairVal p z ≠ 0`,
`d := ballPairDis p z`, `t := ballPairLev p z`, then `d = (‖d‖/t) • u` and

  `z = c + λ · uu`,   `λ = -‖u‖ / ((p+1) · min uu)`,  `uu := (u₀, …, u_{p-1}, -∑uᵢ)`,

because the level of `z` is `t = ‖u‖` and `min z = c + (‖d‖/t) · min uu`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- The zero-sum lift `(u₀, …, u_{p-1}, -∑ᵢ uᵢ) ∈ ℝ^{p+1}` of a vector `u ∈ ℝᵖ`, used to
reconstruct a point of the simplex from its image under the cone map. -/
def ballPairSnoc (p : ℕ) (u : EuclideanSpace ℝ (Fin p)) : Fin (p+1) → ℝ :=
  Fin.snoc (fun j : Fin p => u.ofLp j) (-∑ j : Fin p, u.ofLp j)

/-- The scalar `λ(u) = -‖u‖ / ((p+1)·min (ballPairSnoc u))` of the reconstruction formula. -/
def ballPairLambda (p : ℕ) (u : EuclideanSpace ℝ (Fin p)) : ℝ :=
  -(‖u‖) / ((((p + 1 : ℕ) : ℝ)) * ballPairMin p (ballPairSnoc p u))

@[simp] theorem ballPairSnoc_castSucc (p : ℕ) (u : EuclideanSpace ℝ (Fin p)) (j : Fin p) :
    ballPairSnoc p u j.castSucc = u.ofLp j := by simp [ballPairSnoc]

@[simp] theorem ballPairSnoc_last (p : ℕ) (u : EuclideanSpace ℝ (Fin p)) :
    ballPairSnoc p u (Fin.last p) = -∑ j : Fin p, u.ofLp j := by simp [ballPairSnoc]

/-- The components of `ballPairDis`. -/
@[simp] theorem ballPairDis_apply (p : ℕ) (f : Fin (p+1) → ℝ) (j : Fin p) :
    (ballPairDis p f).ofLp j = f j.castSucc - ballPairCtr p := by
  simp [ballPairDis]

theorem ballPairDis_eq_smul (p : ℕ) (z : stdSimplex ℝ (Fin (p+1)))
    (hu : ballPairVal p (z : Fin (p+1) → ℝ) ≠ 0) :
    ballPairDis p (z : Fin (p+1) → ℝ) =
      (‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)) •
        ballPairVal p (z : Fin (p+1) → ℝ) := by
  have ht : ballPairLev p (z : Fin (p+1) → ℝ) ≠ 0 := by
    rw [← norm_ballPairVal p z]; exact norm_ne_zero_iff.mpr hu
  have hd : ballPairDis p (z : Fin (p+1) → ℝ) ≠ 0 :=
    fun h => ht (ballPairLev_eq_zero_of_dis_eq_zero p z h)
  rw [ballPairVal, smul_smul]
  have hcoef : (‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)) *
      (ballPairLev p (z : Fin (p+1) → ℝ) * ‖ballPairDis p (z : Fin (p+1) → ℝ)‖⁻¹) = 1 := by
    field_simp
  rw [hcoef, one_smul]

theorem ballPairVal_coord (p : ℕ) (z : stdSimplex ℝ (Fin (p+1)))
    (hu : ballPairVal p (z : Fin (p+1) → ℝ) ≠ 0) (j : Fin p) :
    (z : Fin (p+1) → ℝ) j.castSucc = ballPairCtr p +
      (‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)) *
        (ballPairVal p (z : Fin (p+1) → ℝ)).ofLp j := by
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin p) => v.ofLp j) (ballPairDis_eq_smul p z hu)
  rw [ballPairDis_apply] at h
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at h
  linarith

theorem ballPairVal_coord_last (p : ℕ) (z : stdSimplex ℝ (Fin (p+1)))
    (hu : ballPairVal p (z : Fin (p+1) → ℝ) ≠ 0) :
    (z : Fin (p+1) → ℝ) (Fin.last p) = ballPairCtr p +
      (‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)) *
        (- ∑ j : Fin p, (ballPairVal p (z : Fin (p+1) → ℝ)).ofLp j) := by
  set coef : ℝ := ‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)
    with hcoef
  set S : ℝ := ∑ j : Fin p, (ballPairVal p (z : Fin (p+1) → ℝ)).ofLp j with hS
  have hsum : (∑ i : Fin (p+1), (z : Fin (p+1) → ℝ) i) = 1 := z.2.2
  rw [Fin.sum_univ_castSucc] at hsum
  have hterm : ∀ j : Fin p, (z : Fin (p+1) → ℝ) j.castSucc = ballPairCtr p + coef *
      (ballPairVal p (z : Fin (p+1) → ℝ)).ofLp j := by
    intro j
    rw [hcoef]
    exact ballPairVal_coord p z hu j
  have hsplit : (∑ j : Fin p, (z : Fin (p+1) → ℝ) j.castSucc) =
      (p : ℝ) * ballPairCtr p + coef * S := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum, ← hS,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpcast : ((((p+1:ℕ)):ℝ)) = (p:ℝ) + 1 := by push_cast; ring
  have hc : ((((p+1:ℕ)):ℝ)) * ballPairCtr p = 1 := by
    rw [ballPairCtr]; exact mul_inv_cancel₀ (by positivity)
  have hpc : 1 - (p:ℝ) * ballPairCtr p = ballPairCtr p := by nlinarith only [hpcast, hc]
  rw [hsplit] at hsum
  have hgoal : (z : Fin (p+1) → ℝ) (Fin.last p) = 1 - ((p:ℝ) * ballPairCtr p + coef * S) := by
    linarith only [hsum]
  rw [hgoal]
  rw [show (1:ℝ) - ((p:ℝ) * ballPairCtr p + coef * S) =
      (1 - (p:ℝ)*ballPairCtr p) - coef*S by ring, hpc]
  ring

theorem ballPairVal_eq_ctr_add (p : ℕ) (z : stdSimplex ℝ (Fin (p+1)))
    (hu : ballPairVal p (z : Fin (p+1) → ℝ) ≠ 0) :
    (z : Fin (p+1) → ℝ) = fun i => ballPairCtr p +
      (‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)) *
        ballPairSnoc p (ballPairVal p (z : Fin (p+1) → ℝ)) i := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [ballPairSnoc_castSucc]; exact ballPairVal_coord p z hu j
  · rw [ballPairSnoc_last]; exact ballPairVal_coord_last p z hu

theorem ballPairLev_eq_min (p : ℕ) (z : stdSimplex ℝ (Fin (p+1)))
    (hu : ballPairVal p (z : Fin (p+1) → ℝ) ≠ 0) :
    ballPairLev p (z : Fin (p+1) → ℝ) =
      - ((((p+1:ℕ)):ℝ)) *
        (‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)) *
        ballPairMin p (ballPairSnoc p (ballPairVal p (z : Fin (p+1) → ℝ))) := by
  have h1 := ballPairVal_eq_ctr_add p z hu
  have hpos : 0 ≤ ‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ) := by
    have ht : 0 < ballPairLev p (z : Fin (p+1) → ℝ) := by
      rw [← norm_ballPairVal p z]; exact norm_pos_iff.mpr hu
    exact div_nonneg (norm_nonneg _) (le_of_lt ht)
  have hmin : ballPairMin p (z : Fin (p+1) → ℝ) = ballPairCtr p +
      (‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)) *
        ballPairMin p (ballPairSnoc p (ballPairVal p (z : Fin (p+1) → ℝ))) := by
    have hc' := congrArg (ballPairMin p) h1
    rw [ballPairMin_add_mul p (ballPairSnoc p (ballPairVal p (z : Fin (p+1) → ℝ))) hpos
      (ballPairCtr p)] at hc'
    exact hc'
  have hc : ((((p+1:ℕ)):ℝ)) * ballPairCtr p = 1 := by
    rw [ballPairCtr]; exact mul_inv_cancel₀ (by positivity)
  conv_lhs => rw [show ballPairLev p (z : Fin (p+1) → ℝ) =
      1 - ((((p+1:ℕ)):ℝ)) * ballPairMin p (z : Fin (p+1) → ℝ) from rfl]
  rw [hmin]
  nlinarith only [hc]

/-- **The reconstruction formula.**  A point of the simplex with nonvanishing image under the cone
map is determined by that image: `z = c + λ(u)·uu`. -/
theorem ballPairVal_eq_reconstruction (p : ℕ) (z : stdSimplex ℝ (Fin (p+1)))
    (hu : ballPairVal p (z : Fin (p+1) → ℝ) ≠ 0) :
    (z : Fin (p+1) → ℝ) = fun i => ballPairCtr p +
      ballPairLambda p (ballPairVal p (z : Fin (p+1) → ℝ)) *
        ballPairSnoc p (ballPairVal p (z : Fin (p+1) → ℝ)) i := by
  set u : EuclideanSpace ℝ (Fin p) := ballPairVal p (z : Fin (p+1) → ℝ) with hu_def
  set m : ℝ := ballPairMin p (ballPairSnoc p u) with hm
  set coef : ℝ := ‖ballPairDis p (z : Fin (p+1) → ℝ)‖ / ballPairLev p (z : Fin (p+1) → ℝ)
    with hcoef
  have h1 : (z : Fin (p+1) → ℝ) = fun i => ballPairCtr p + coef * ballPairSnoc p u i := by
    rw [hcoef]
    exact ballPairVal_eq_ctr_add p z hu
  have h2 : ballPairLev p (z : Fin (p+1) → ℝ) = - ((((p+1:ℕ)):ℝ)) * coef * m := by
    rw [hcoef, hm]
    exact ballPairLev_eq_min p z hu
  have ht : ballPairLev p (z : Fin (p+1) → ℝ) = ‖u‖ := by
    rw [hu_def]
    exact (norm_ballPairVal p z).symm
  have hm_ne : m ≠ 0 := by
    intro hm0
    have h2' : ballPairLev p (z : Fin (p+1) → ℝ) = 0 := by simpa [hm0] using h2
    rw [h2'] at ht
    exact (norm_ne_zero_iff.mpr hu) ht.symm
  have hpm_ne : ((((p+1:ℕ)):ℝ)) * m ≠ 0 := mul_ne_zero (by positivity) hm_ne
  have hcoef_val : coef = ballPairLambda p u := by
    rw [ballPairLambda, eq_div_iff hpm_ne]
    nlinarith only [h2, ht]
  rw [h1, hcoef_val]

/-- If the cone level vanishes then the point is the barycentre of the simplex. -/
theorem eq_ctr_of_ballPairLev_eq_zero (p : ℕ) (z : stdSimplex ℝ (Fin (p+1)))
    (h : ballPairLev p (z : Fin (p+1) → ℝ) = 0) :
    (z : Fin (p+1) → ℝ) = fun _ => ballPairCtr p := by
  have hNpos : (0:ℝ) < ((((p+1:ℕ)):ℝ)) := by positivity
  have hc : ((((p+1:ℕ)):ℝ)) * ballPairCtr p = 1 := by
    rw [ballPairCtr]; exact mul_inv_cancel₀ (by positivity)
  have hmul : ((((p+1:ℕ)):ℝ)) * ballPairMin p (z : Fin (p+1) → ℝ) = 1 := by
    rw [ballPairLev] at h
    linarith
  have hmin : ballPairMin p (z : Fin (p+1) → ℝ) = ballPairCtr p := by
    rw [ballPairCtr, inv_eq_one_div, eq_div_iff (ne_of_gt hNpos), mul_comm]
    exact hmul
  have hsum : (∑ i : Fin (p+1), ((z : Fin (p+1) → ℝ) i - ballPairCtr p)) = 0 := by
    have hz1 : (∑ i : Fin (p+1), (z : Fin (p+1) → ℝ) i) = 1 := z.2.2
    rw [Finset.sum_sub_distrib, hz1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hc, sub_self]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin (p+1))),
      0 ≤ (z : Fin (p+1) → ℝ) i - ballPairCtr p := by
    intro i _
    have h1 : ballPairCtr p ≤ (z : Fin (p+1) → ℝ) i := by
      rw [← hmin]; exact ballPairMin_le p (z : Fin (p+1) → ℝ) i
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  funext i
  have := hzero i (Finset.mem_univ i)
  linarith

/-- **The cone map is injective.** -/
theorem ballPairVal_injective (p : ℕ) :
    Function.Injective
      (fun z : stdSimplex ℝ (Fin (p+1)) => ballPairVal p (z : Fin (p+1) → ℝ)) := by
  intro z z' h
  change ballPairVal p (z : Fin (p+1) → ℝ) = ballPairVal p (z' : Fin (p+1) → ℝ) at h
  by_cases hu : ballPairVal p (z : Fin (p+1) → ℝ) = 0
  · have hz : (z : Fin (p+1) → ℝ) = fun _ => ballPairCtr p :=
      eq_ctr_of_ballPairLev_eq_zero p z (by
        have hh := norm_ballPairVal p z
        rw [hu, norm_zero] at hh
        exact hh.symm)
    have hz' : (z' : Fin (p+1) → ℝ) = fun _ => ballPairCtr p :=
      eq_ctr_of_ballPairLev_eq_zero p z' (by
        have hh := norm_ballPairVal p z'
        rw [← h, hu, norm_zero] at hh
        exact hh.symm)
    exact Subtype.ext (hz.trans hz'.symm)
  · have hu' : ballPairVal p (z' : Fin (p+1) → ℝ) ≠ 0 := by rw [← h]; exact hu
    have r1 := ballPairVal_eq_reconstruction p z hu
    have r2 := ballPairVal_eq_reconstruction p z' hu'
    rw [← h] at r2
    exact Subtype.ext (r1.trans r2.symm)

/-- **The cone map of the simplex onto the ball is a homeomorphism.** -/
theorem ballPairVal_homeomorph (p : ℕ) (hp : 1 ≤ p) :
    ∃ e : ↥(stdSimplex ℝ (Fin (p+1))) ≃ₜ Work.Thom.MBall p,
      ∀ z : stdSimplex ℝ (Fin (p+1)),
        e z = ⟨ballPairVal p (z : Fin (p+1) → ℝ), ballPairVal_mem_ball p z⟩ := by
  classical
  haveI : CompactSpace ↥(stdSimplex ℝ (Fin (p+1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (p+1)))
  let F : ↥(stdSimplex ℝ (Fin (p+1))) → Work.Thom.MBall p := fun z =>
    ⟨ballPairVal p (z : Fin (p+1) → ℝ), ballPairVal_mem_ball p z⟩
  have hFcont : Continuous F :=
    Continuous.subtype_mk (continuous_ballPairVal_simplex p) (fun z => ballPairVal_mem_ball p z)
  have hFinj : Function.Injective F :=
    fun a b hab => ballPairVal_injective p (congrArg Subtype.val hab)
  have hFbij : Function.Bijective F := ⟨hFinj, ballPairVal_surj p hp⟩
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hFbij) hFcont,
    fun z => rfl⟩

theorem coneMap_retraction (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y]
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ r : C(TopCat.of (Y × Work.Thom.MBall p), TopCat.of (stdSimplex ℝ (Fin (p+1)))),
      (∀ z : stdSimplex ℝ (Fin (p+1)),
        r (Classical.arbitrary Y,
            (⟨Work.Whitney.ballPairVal p (z : Fin (p+1) → ℝ),
              Work.Whitney.ballPairVal_mem_ball p z⟩ : Work.Thom.MBall p)) = z) ∧
      (∀ q : Y × Work.Thom.MBall p, q ∈ Work.Thom.DiscB Y p →
        r q ∈ {z : stdSimplex ℝ (Fin (p+1)) | ∃ i : Fin (p+1), (z : Fin (p+1) → ℝ) i = 0}) := by
  classical
  obtain ⟨e, he⟩ := ballPairVal_homeomorph p hp
  refine ⟨⟨fun q : Y × Work.Thom.MBall p => e.symm q.2,
    e.symm.continuous.comp continuous_snd⟩, ?_, ?_⟩
  · intro z
    show e.symm (⟨ballPairVal p (z : Fin (p+1) → ℝ), ballPairVal_mem_ball p z⟩ :
      Work.Thom.MBall p) = z
    rw [← he z, Homeomorph.symm_apply_apply]
  · intro q hq
    have h1 : (⟨ballPairVal p ((e.symm q.2 : ↥(stdSimplex ℝ (Fin (p+1)))) : Fin (p+1) → ℝ),
        ballPairVal_mem_ball p (e.symm q.2)⟩ : Work.Thom.MBall p) = q.2 :=
      ((he (e.symm q.2)).symm).trans (e.apply_symm_apply q.2)
    have hval : ((ballPairVal p ((e.symm q.2 : ↥(stdSimplex ℝ (Fin (p+1)))) :
        Fin (p+1) → ℝ)) : EuclideanSpace ℝ (Fin p)) = (q.2 : EuclideanSpace ℝ (Fin p)) := by
      simpa using congrArg (fun w : Work.Thom.MBall p => (w : EuclideanSpace ℝ (Fin p))) h1
    have hsph : ‖ballPairVal p ((e.symm q.2 : ↥(stdSimplex ℝ (Fin (p+1)))) :
        Fin (p+1) → ℝ)‖ = 1 := by
      rw [hval]
      exact hq
    exact (ballPairVal_mem_sph_iff p (e.symm q.2)).mp hsph

end

end Work.Whitney
