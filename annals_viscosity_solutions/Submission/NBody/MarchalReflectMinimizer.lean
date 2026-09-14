import Submission.NBody.MarchalBumpTwoSided
import Submission.NBody.Identification
import Submission.NBody.MarchalKineticBoundAtCollision
import Submission.NBody.MarchalMultiEnergyBound
import Submission.NBody.MarchalCollClass

/-!
# Time reversal of an action minimiser

The Marchal chapter is developed for a curve defined on `(0, ε)`, i.e. on the *right* of a collision
time.  To obtain the same information on the *left* of a collision time one reflects the curve: if
`γ` is an `h`-minimiser on `[a,b]`, then `γ̄(u) = γ(t₀ - u)` is an `h`-minimiser on `[t₀-b, t₀-a]`,
because the Lagrangian is even in the velocity and the action potential is symmetric in its two
configuration arguments.

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

/-! ## 1. Reflection of the action -/

/-- **Reflection does not change the action**, on an arbitrary time interval. -/
theorem actionOn_reflectCurve {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b t₀ : ℝ}
    (hab : a ≤ b) :
    actionOn m h (reflectCurve γ t₀) (t₀ - b) (t₀ - a) = actionOn m h γ a b := by
  have e1 : (fun t : ℝ => reflectCurve γ t₀ (t + (t₀ - b)))
      = (fun t : ℝ => (fun s : ℝ => γ (a + s)) ((b - a) - t)) := by
    funext t
    show γ (t₀ - (t + (t₀ - b))) = γ (a + ((b - a) - t))
    rw [show t₀ - (t + (t₀ - b)) = a + ((b - a) - t) by ring]
  calc actionOn m h (reflectCurve γ t₀) (t₀ - b) (t₀ - a)
      = actionOn m h (fun t : ℝ => reflectCurve γ t₀ (t + (t₀ - b))) 0 ((t₀ - a) - (t₀ - b)) :=
        (actionOn_comp_add_const' (m := m) (h := h) (γ := reflectCurve γ t₀) (c := t₀ - b)).symm
    _ = actionOn m h (fun t : ℝ => (fun s : ℝ => γ (a + s)) ((b - a) - t)) 0 ((t₀ - a) - (t₀ - b)) := by
        rw [e1]
    _ = actionOn m h (fun t : ℝ => (fun s : ℝ => γ (a + s)) ((b - a) - t)) 0 (b - a) := by
        rw [show (t₀ - a) - (t₀ - b) = b - a by ring]
    _ = actionOn m h (fun s : ℝ => γ (a + s)) 0 (b - a) :=
        actionOn_comp_rev (m := m) (h := h) (γ := fun s : ℝ => γ (a + s)) (τ := b - a)
    _ = actionOn m h γ a b := by
        have h := (actionOn_comp_add_const' (m := m) (h := h) (γ := γ) (c := a) (d := b)).symm
        have hf : (fun s : ℝ => γ (a + s)) = (fun t : ℝ => γ (t + a)) := by
          funext t; rw [add_comm]
        rw [hf]
        exact h.symm

/-- **The time reversal of an `h`-minimiser is an `h`-minimiser.** -/
theorem isHMinimizer_reflectCurve {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b t₀ : ℝ}
    (hab : a ≤ b) (hmin : IsHMinimizer m h γ a b) :
    IsHMinimizer m h (reflectCurve γ t₀) (t₀ - b) (t₀ - a) := by
  unfold IsHMinimizer at hmin ⊢
  rw [actionOn_reflectCurve (m := m) (h := h) (γ := γ) (t₀ := t₀) hab, hmin]
  have h2 : reflectCurve γ t₀ (t₀ - b) = γ b := by simp [reflectCurve]
  have h3 : reflectCurve γ t₀ (t₀ - a) = γ a := by simp [reflectCurve]
  rw [h2, h3, actionPot_comm m h (γ b) (γ a)]

/-- The reflection of an absolutely continuous curve is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_reflectCurve {γ : ℝ → EN E N} {a b t₀ : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (reflectCurve γ t₀) (t₀ - b) (t₀ - a) := by
  have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
    (f := γ) (a := a) (b := b) (c := -1) (d := t₀) (by norm_num) hac
  have h2 : (fun t : ℝ => γ (-1 * t + t₀)) = reflectCurve γ t₀ := by
    funext t; simp [reflectCurve]; ring_nf
  rw [h2] at h
  have h3 : (a - t₀) / (-1 : ℝ) = t₀ - a := by ring
  have h4 : (b - t₀) / (-1 : ℝ) = t₀ - b := by ring
  rw [h3, h4] at h
  exact h.symm

/-! ## 2. The relative energy is even in the velocity -/

lemma clusterCM_neg {m : Fin N → ℝ} (k : Finset (Fin N)) (x : EN E N) :
    clusterCM m k (-x) = -clusterCM m k x := by
  have hsum : (∑ i ∈ k, m i • (-x) i) = -(∑ i ∈ k, m i • x i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [WithLp.ofLp_neg, Pi.neg_apply, smul_neg]
  unfold clusterCM
  rw [hsum, smul_neg]

/-- The centre-of-mass-relative configuration is odd. -/
lemma cmRel_neg {m : Fin N → ℝ} (k : Finset (Fin N)) (x : EN E N) :
    cmRel m k (-x) = -cmRel m k x := by
  have hcm := clusterCM_neg (m := m) k x
  refine PiLp.ext fun i => ?_
  by_cases hi : i ∈ k
  · have h1 : (cmRel m k (-x)) i = (-x) i - clusterCM m k (-x) := cmRel_apply_of_mem hi
    have h2 : (-cmRel m k x) i = -((cmRel m k x) i) := Pi.neg_apply (cmRel m k x) i
    have h3 : (cmRel m k x) i = x i - clusterCM m k x := cmRel_apply_of_mem hi
    rw [h1, h2, h3, hcm]
    simp [sub_eq_add_neg, add_comm]
  · have h1 : (cmRel m k (-x)) i = 0 := cmRel_apply_of_notMem hi
    have h2 : (-cmRel m k x) i = -((cmRel m k x) i) := Pi.neg_apply (cmRel m k x) i
    have h3 : (cmRel m k x) i = 0 := cmRel_apply_of_notMem hi
    rw [h1, h2, h3, neg_zero]

/-- The moment of inertia of a cluster is even. -/
lemma clusterInertia_neg {m : Fin N → ℝ} (k : Finset (Fin N)) (x : EN E N) :
    clusterInertia m k (-x) = clusterInertia m k x := by
  have hcm := clusterCM_neg (m := m) k x
  rw [clusterInertia, clusterInertia, hcm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (-x) i - -clusterCM m k x = -(x i - clusterCM m k x) := by
    simp only [WithLp.ofLp_neg, Pi.neg_apply]
    simp [sub_eq_add_neg, add_comm]
  rw [h, norm_neg]

lemma clusterRelKinetic_neg {m : Fin N → ℝ} (k : Finset (Fin N)) (v : EN E N) :
    clusterRelKinetic m k (-v) = clusterRelKinetic m k v := by
  have hcm : cmRel m k (-v) = -cmRel m k v := cmRel_neg (m := m) k v
  rw [clusterRelKinetic, clusterRelKinetic, hcm]
  simp only [clusterKineticSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [WithLp.ofLp_neg, Pi.neg_apply, norm_neg]

lemma clusterRelEnergy_neg {m : Fin N → ℝ} (k : Finset (Fin N)) (x v : EN E N) :
    clusterRelEnergy m k x (-v) = clusterRelEnergy m k x v := by
  rw [clusterRelEnergy, clusterRelEnergy, clusterRelKinetic_neg]

/-! ## 3. The kinetic bound on the two sides of a collision -/

/-! ## 4. The relative-energy bound on the two sides of a collision -/

/-- **The relative-energy bound of a colliding cluster**, with the kinetic hypothesis in the
eventual form at `0⁺` (Ferrario–Terracini, `lemma:bounded_energy`). -/
theorem exists_relEnergy_bound_of_kinetic {m : Fin N → ℝ} {k : Finset (Fin N)}
    {x : ℝ → EN E N} {ε ν Ck : ℝ} (hm : ∀ i, 0 < m i) (hk : k.Nonempty)
    (hε : 0 < ε) (hν : 0 < ν) (hCk : 0 < Ck)
    (hnc : ∀ t ∈ Ioo (0:ℝ) ε, WithoutCollisions (x t))
    (hx : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x t) t)
    (hd2 : ∀ t ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (deriv (deriv x) t) t)
    (hode : ∀ t ∈ Ioo (0:ℝ) ε, deriv (deriv x) t = ∇_[m] (U m) (x t))
    (hsepw : ∀ t ∈ Ioo (0:ℝ) ε, ClusterSeparatedWeak k (x t) ν)
    (hkin : ∀ᶠ t in 𝓝[>] (0:ℝ), kinetic m (deriv x t) ≤ Ck * t ^ (-((2:ℝ)/3))) :
    ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ t ∈ Ioo (0:ℝ) δ,
      |clusterRelEnergy m k (x t) (deriv x t)| ≤ C := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_forall_Ioo_of_eventually_nhdsGT hkin
  set δ' : ℝ := min (δ / 2) (ε / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min (by linarith) (by linarith)
  have hδ'le : δ' ≤ ε := le_trans (min_le_right _ _) (by linarith)
  have hδ'leδ : δ' ≤ δ := le_trans (min_le_left _ _) (by linarith)
  have hkin' : ∀ t ∈ Ioo (0:ℝ) δ', kinetic m (deriv x t) ≤ Ck * t ^ (-((2:ℝ)/3)) :=
    fun t ht => hδ t ⟨ht.1, lt_of_lt_of_le ht.2 hδ'leδ⟩
  obtain ⟨C, hC⟩ := exists_clusterRelEnergy_bound (m := m) (k := k) (x := x) (ε := δ') (ν := ν)
    (Ck := Ck) hm hk hδ'pos hν hCk
    (fun t ht => hnc t ⟨ht.1, lt_of_lt_of_le ht.2 hδ'le⟩)
    (fun t ht => hx t ⟨ht.1, lt_of_lt_of_le ht.2 hδ'le⟩)
    (fun t ht => hd2 t ⟨ht.1, lt_of_lt_of_le ht.2 hδ'le⟩)
    (fun t ht => hode t ⟨ht.1, lt_of_lt_of_le ht.2 hδ'le⟩)
    (fun t ht => hsepw t ⟨ht.1, lt_of_lt_of_le ht.2 hδ'le⟩)
    hkin'
  refine ⟨|C| + 1, by positivity, δ' / 2, by linarith, by linarith, fun t ht => ?_⟩
  exact le_trans (hC t ⟨ht.1, by linarith [ht.2]⟩)
    (le_trans (le_abs_self C) (by linarith [abs_nonneg C]))

/-! ## 5. The kinetic bound on the two sides of a collision -/

/-- **The kinetic bound on the right of a collision time.** -/
theorem exists_kinetic_bound_right_of_minimizer {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ ε : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hcoll : ¬ WithoutCollisions (γ t₀))
    (hε : 0 < ε) (hεb : t₀ + ε ≤ b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t)) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),
      kinetic m (deriv (fun s : ℝ => γ (t₀ + s)) t) ≤ Ck * t ^ (-((2:ℝ)/3)) :=
  exists_kinetic_bound_at_collision (m := m) (h := h) (γ := γ) (a := a) (b := b)
    (t₀ := t₀) (ε := ε) hm hh hab hac hmin hfin ht₀ hcoll hε hεb hnc

/-- **The kinetic bound on the left of a collision time.** -/
theorem exists_kinetic_bound_left_of_minimizer {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ ε : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hcoll : ¬ WithoutCollisions (γ t₀))
    (hε : 0 < ε) (hεa : a ≤ t₀ - ε)
    (hnc : ∀ t ∈ Ioo (t₀ - ε) t₀, WithoutCollisions (γ t)) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ᶠ t in 𝓝[>] (0:ℝ),
      kinetic m (deriv (fun s : ℝ => γ (t₀ - s)) t) ≤ Ck * t ^ (-((2:ℝ)/3)) := by
  -- the reflected curve is a minimiser on the reflected interval
  have hmin' : IsHMinimizer m h (reflectCurve γ t₀) (t₀ - b) (t₀ - a) :=
    isHMinimizer_reflectCurve hab.le hmin
  have hac' : AbsolutelyContinuousOnInterval (reflectCurve γ t₀) (t₀ - b) (t₀ - a) :=
    absolutelyContinuousOnInterval_reflectCurve hac
  have hlt : (0:ℝ) ∈ Ioo (t₀ - b) (t₀ - a) := ⟨by linarith [ht₀.2], by linarith [ht₀.1]⟩
  have hcoll' : ¬ WithoutCollisions (reflectCurve γ t₀ 0) := by
    simpa [reflectCurve] using hcoll
  have hnc' : ∀ t ∈ Ioo (0:ℝ) (0 + ε), WithoutCollisions (reflectCurve γ t₀ t) := by
    intro t ht
    have h1 : t₀ - t ∈ Ioo (t₀ - ε) t₀ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa [reflectCurve] using hnc (t₀ - t) h1
  have hεb' : (0:ℝ) + ε ≤ t₀ - a := by linarith
  obtain ⟨Ck, hCkpos, hCk⟩ := exists_kinetic_bound_right_of_minimizer (m := m) (h := h)
    (γ := reflectCurve γ t₀) (a := t₀ - b) (b := t₀ - a) (t₀ := 0) (ε := ε)
    hm hh (by linarith) hac' hmin' hfin hlt hcoll' hε hεb' hnc'
  refine ⟨Ck, hCkpos, ?_⟩
  filter_upwards [hCk] with t ht
  simpa only [zero_add, reflectCurve] using ht

end Submission.NBody
