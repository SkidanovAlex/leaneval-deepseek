import Mathlib
import Submission.Work.Geo.DualStretch.Local
import Submission.Work.Geo.DualStretch.linearIndependent_prod_one
import Submission.Work.Geo.DualStretch.exists_dual_apply_eq
import Submission.Work.PL.Generic.mem_hullOf

/-!
# Continuity of the barycentric coordinates `rcoord` on a simplex

`Work.Geo.DualStretch.rcoord σ x v` is the barycentric coordinate of `x` with respect to the
vertex `v` of the face `σ`.  It is defined by classical choice from *any* representation of `x`
as a convex combination of the vertices of `σ` (and is `0` off `PL.simp σ`):

`rcoord σ x v = (Classical.choose (∃ μ, μ ≥ 0 on σ, ∑ μ = 1, ∑ μ w • w = x)) v` if `v ∈ σ`.

Here we prove that `x ↦ rcoord σ x v` is continuous on `PL.simp σ`.  The classical choice is
harmless because *every* admissible weight function has the same value at `v`: if
`L : E n × ℝ →ₗ[ℝ] ℝ` is a linear functional with `L (w, 1) = 1` for `w = v` and `= 0` for the
other `w ∈ σ`, then for every admissible `μ`

`L (x, 1) = L (∑ μ w • (w, 1)) = ∑ μ w * L (w, 1) = μ v`,

since `∑ μ = 1`.  Such an `L` exists whenever `σ` is affinely independent, because then the
lifted vectors `(w, 1)` are linearly independent in `E n × ℝ`
(`linearIndependent_prod_one`) and a linear functional can be prescribed arbitrarily on a
linearly independent family (`exists_dual_apply_eq`).  Hence on `PL.simp σ` the coordinate is the
restriction of the continuous function `x ↦ L (x, 1)`; if `v ∉ σ` it is identically zero there.
-/

namespace Work.Geo.DualStretch

open Set Metric

variable {n : ℕ}

/-- **A point of a simplex is a convex combination of its vertices** (the existence half of the
barycentric-coordinate representation). -/
theorem exists_weights_of_mem_simp {σ : Finset (PL.E n)} {x : PL.E n} (hx : x ∈ PL.simp σ) :
    ∃ μ : PL.E n → ℝ, (∀ w ∈ σ, 0 ≤ μ w) ∧ (∑ w ∈ σ, μ w = 1) ∧
      (∑ w ∈ σ, μ w • w = x) := by
  have hmem : x ∈ Work.PL.Generic.hullOf (id : PL.E n → PL.E n) σ := by
    rw [Work.PL.Generic.hullOf_eq_simp, Finset.image_id]
    exact hx
  exact (Work.PL.Generic.mem_hullOf (id : PL.E n → PL.E n) σ x).mp hmem

/-- **The functional of the augmented space evaluates the barycentric coordinate.**  If `L` is a
linear functional of `PL.E n × ℝ` that takes the value `1` at `(v, 1)` and `0` at `(w, 1)` for
`w ∈ σ`, and `μ` is any weight function on `σ` with total mass `1` and centre of mass `x`, then
`L (x, 1) = μ v`. -/
theorem dual_apply_eq {σ : Finset (PL.E n)} {x v : PL.E n} (hv : v ∈ σ)
    (L : (PL.E n × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ w ∈ σ, L ((w, 1)) = if w = v then 1 else 0)
    (μ : PL.E n → ℝ) (h1 : ∑ w ∈ σ, μ w = 1) (h2 : ∑ w ∈ σ, μ w • w = x) :
    L (x, 1) = μ v := by
  have hprod :
      (∑ w ∈ σ, μ w • (((w : PL.E n), (1 : ℝ)) : PL.E n × ℝ)) = ((x, 1) : PL.E n × ℝ) := by
    have hp : (∑ w ∈ σ, μ w • (((w : PL.E n), (1 : ℝ)) : PL.E n × ℝ))
        = ((∑ w ∈ σ, μ w • w), (∑ w ∈ σ, μ w)) := by
      apply Prod.ext
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum]
    rw [hp, h2, h1]
  rw [← hprod, map_sum]
  rw [Finset.sum_congr rfl (fun w hw => by rw [map_smul, hL w hw, smul_eq_mul])]
  rw [Finset.sum_eq_single v]
  · simp
  · intro w hw hwv; simp [hwv]
  · intro hv'; exact absurd hv hv'

/-- **Uniqueness of the barycentric coordinates** of a point of an affinely independent simplex:
two weight functions on `σ` with total mass `1` and the same centre of mass `x` agree on `σ`. -/
theorem eq_of_sum_eq_sum_smul {σ : Finset (PL.E n)} (hσ : AffineIndependent ℝ ((↑) : σ → PL.E n))
    {x v : PL.E n} (hv : v ∈ σ) {μ ν : PL.E n → ℝ}
    (hμ1 : ∑ w ∈ σ, μ w = 1) (hμ2 : ∑ w ∈ σ, μ w • w = x)
    (hν1 : ∑ w ∈ σ, ν w = 1) (hν2 : ∑ w ∈ σ, ν w • w = x) : μ v = ν v :=
  hσ.eq_of_sum_eq_sum_subtype (by rw [hμ1, hν1]) (by rw [hμ2, hν2]) v hv

/-- **`rcoord` on the simplex is given by the functional `L`.**  This is the pointwise statement
which is the heart of the proof: on `PL.simp σ` the (arbitrarily chosen) weights of `x` always
give the value `L (x, 1)`. -/
theorem rcoord_eq_apply {σ : Finset (PL.E n)} {v : PL.E n} (hv : v ∈ σ)
    (L : (PL.E n × ℝ) →ₗ[ℝ] ℝ) (hL : ∀ w ∈ σ, L ((w, 1)) = if w = v then 1 else 0) :
    ∀ x ∈ PL.simp σ, rcoord σ x v = L (x, 1) := by
  intro x hx
  have hex : ∃ μ : PL.E n → ℝ, (∀ w ∈ σ, 0 ≤ μ w) ∧ (∑ w ∈ σ, μ w = 1) ∧
      (∑ w ∈ σ, μ w • w = x) := exists_weights_of_mem_simp hx
  have hstep : rcoord σ x v = hex.choose v := by
    rw [rcoord]
    simp only [dite_eq_left hx, dite_eq_left hv, dite_eq_left hex]
  rw [hstep]
  exact (dual_apply_eq hv L hL hex.choose hex.choose_spec.2.1 hex.choose_spec.2.2).symm

/-- **The barycentric coordinates of a face are continuous on the face.** -/
theorem continuousOn_rcoord {n : ℕ} {σ : Finset (PL.E n)}
    (hσ : AffineIndependent ℝ ((↑) : σ → PL.E n)) (v : PL.E n) :
    ContinuousOn (fun x : PL.E n => Work.Geo.DualStretch.rcoord σ x v) (PL.simp σ) := by
  classical
  by_cases hv : v ∈ σ
  · -- the coordinate is the restriction of the continuous function `x ↦ L (x, 1)`
    obtain ⟨L, hL⟩ : ∃ L : (PL.E n × ℝ) →ₗ[ℝ] ℝ,
        ∀ w ∈ σ, L ((w, 1)) = if w = v then 1 else 0 := by
      obtain ⟨L, hL⟩ := exists_dual_apply_eq (linearIndependent_prod_one hσ)
        (fun w : σ => if (w : PL.E n) = v then 1 else 0)
      exact ⟨L, fun w hw => hL ⟨w, hw⟩⟩
    have hcont : ContinuousOn (fun x : PL.E n => L (x, 1)) (PL.simp σ) :=
      ((LinearMap.continuous_of_finiteDimensional L).comp
        (continuous_id.prodMk continuous_const)).continuousOn
    exact hcont.congr fun x hx => rcoord_eq_apply hv L hL x hx
  · -- `v ∉ σ`: the coordinate vanishes on `PL.simp σ`
    have hz : (fun x : PL.E n => rcoord σ x v) = fun _ => 0 := by
      funext x
      simp [rcoord, hv]
    rw [hz]
    exact continuousOn_const

end Work.Geo.DualStretch
