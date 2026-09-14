import Submission.NBody.MarchalIsolatedOfLocalMin
import Submission.NBody.MarchalIsolatedCollision

/-!
# The existence of an isolated collision time (assembly)

For an `h`-minimiser `γ` on `[a,b]` with a collision time in `[c,d] ⊆ (a,b)`, and under the unique
analytic input that the centre-of-mass-relative energy of every cluster is bounded below on the
collision-free points of `[c,d]`, there is a collision time `t₁ ∈ [c,d]` which is *isolated*: `γ`
is collision free on a punctured neighbourhood of `t₁`.

The proof combines

* `exists_local_min_collision` — the existence of a collision time whose collision classes are
  locally constant (minimising the number of colliding pairs);
* `isolated_of_local_min` — the Rolle--Sperner step, which shows that such a collision time cannot
  be an accumulation point of collision times when the energy is bounded below.

Everything in this file is fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The existence of an isolated collision time.**  For an `h`-minimiser on `[a,b]` with a
collision in `[c,d] ⊆ (a,b)`, and if the relative energy of every cluster is bounded below on the
collision-free points of `[c,d]`, then some collision time of `[c,d]` is isolated. -/
theorem exists_isolated_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b c d C₁ : ℝ}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (hcd : Icc c d ⊆ Ioo a b)
    (hcoll : ∃ t ∈ Icc c d, ¬ WithoutCollisions (γ t))
    (hc1 : 0 ≤ C₁)
    (hE : ∀ (k : Finset (Fin N)) (t : ℝ), t ∈ Icc c d → 0 < clusterInertia m k (γ t) →
      -C₁ ≤ clusterRelEnergy m k (γ t) (deriv γ t)) :
    ∃ t₁ ∈ Icc c d, ¬ WithoutCollisions (γ t₁) ∧
      ∃ η > 0, η ≤ 1 ∧ ∀ t ∈ Icc c d, |t - t₁| < η → t ≠ t₁ → WithoutCollisions (γ t) := by
  classical
  have hcontab : ContinuousOn γ (Icc a b) := by
    have h := hac.continuousOn
    rwa [uIcc_of_le hab.le] at h
  have hcontcd : ContinuousOn γ (Icc c d) :=
    hcontab.mono (fun t ht => ⟨(hcd ht).1.le, (hcd ht).2.le⟩)
  obtain ⟨t₁, ht₁, i₁, hk2, ε, hεpos, hloc⟩ := exists_local_min_collision hcontcd hcoll
  have hcoll₁ : ¬ WithoutCollisions (γ t₁) := by
    obtain ⟨j, hj, hji⟩ : ∃ j ∈ collClass γ t₁ i₁, j ≠ i₁ := by
      have h1 : 1 < (collClass γ t₁ i₁).card := by omega
      obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
      by_cases hqi : q = i₁
      · exact ⟨p, hp, fun hpi => hpq (hpi.trans hqi.symm)⟩
      · exact ⟨q, hq, hqi⟩
    intro hnc'
    have heq : γ t₁ i₁ = γ t₁ j := (mem_collClass.mp hj).symm
    exact (hnc' i₁ j (fun h => hji h.symm))
      (by rw [r_eq_norm_sub, heq, sub_self, norm_zero])
  obtain ⟨η, hηpos, hη1, hiso⟩ := isolated_of_local_min (m := m) (h := h) (γ := γ) (a := a)
    (b := b) (c := c) (d := d) (t₁ := t₁) (C₁ := C₁) (i₁ := i₁) hm hh hab hac hmin hfin hcd
    ht₁ hk2 ⟨ε, hεpos, hloc⟩ hc1
    (fun t ht hFt => hE (collClass γ t₁ i₁) t ht hFt)
  exact ⟨t₁, ht₁, hcoll₁, η, hηpos, hη1, hiso⟩

end Submission.NBody
