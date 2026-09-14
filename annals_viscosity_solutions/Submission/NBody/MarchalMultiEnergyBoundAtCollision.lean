import Submission.NBody.MarchalEnergyBoundAtCollision
import Submission.NBody.MarchalMultiBound
import Submission.NBody.MarchalMultiOutsideKinetic

/-!
# The sum-level (multi-cluster) relative-energy bound at a collision

The multi-cluster counterpart of `MarchalEnergyBoundAtCollision.exists_relEnergy_bound_at_collision`:
for an `h`-minimiser with a collision time `t₀` and a family `ks` of clusters that is one-sidedly
separated from its complement on the collision-free side of `t₀`, the SUM of the relative energies
`Σ_{k∈ks} E^{rel}_k` is bounded.  This is Ferrario--Terracini's `nr:next`, obtained here from the a.e.
energy identity together with the boundedness of the "slow" quantities
(`multiOutsideKineticSq`, `multiCMKineticSq`, `multiRestPotential`).

Everything in this file is fully proved.
-/

open ViscositySolutions Filter Gradient
open Set Real Metric Finset InnerProductSpace MeasureTheory
open scoped BigOperators Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **The sum-level relative-energy bound** (Ferrario--Terracini `nr:next`). -/
theorem exists_multiRelEnergy_bound_at_collision {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {a b t₀ ε ν : ℝ} {ks : Finset (Finset (Fin N))}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hab : a < b)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hmin : IsHMinimizer m h γ a b) (hfin : ∀ x y : EN E N, actionPot m h x y < ⊤)
    (ht₀ : t₀ ∈ Ioo a b) (hε : 0 < ε) (hεb : t₀ + ε < b)
    (hnc : ∀ t ∈ Ioo t₀ (t₀ + ε), WithoutCollisions (γ t))
    (hν : 0 < ν) (hne : ∀ k ∈ ks, k.Nonempty)
    (hedj : ∀ k ∈ ks, ∀ k' ∈ ks, k ≠ k' → Disjoint k k')
    (hsep : ∀ t ∈ Ioo t₀ (t₀ + ε), ∀ k ∈ ks, ClusterSeparatedWeak k (γ t) ν)
    (hsepT : ∀ t ∈ Ioo t₀ (t₀ + ε), ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks,
      i ≠ j → ν ≤ r (γ t) i j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo t₀ (t₀ + ε / 4),
      |multiRelEnergy m ks (γ t) (deriv γ t)| ≤ C := by
  classical
  set x : ℝ → EN E N := fun u => γ (t₀ + u) with hxdef
  -- the strip
  have hsub : uIcc t₀ (t₀ + ε) ⊆ uIcc a b := by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le hab.le]
    exact Set.Icc_subset_Icc ht₀.1.le hεb.le
  have hac' : AbsolutelyContinuousOnInterval γ t₀ (t₀ + ε) := hac.mono hsub
  have hacx : AbsolutelyContinuousOnInterval x 0 ε := by
    have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
      (f := γ) (a := t₀) (b := t₀ + ε) (c := 1) (d := t₀) (by norm_num) hac'
    have h2 : (fun t : ℝ => γ (1 * t + t₀)) = x := by
      funext t; rw [hxdef]; ring_nf
    rw [h2] at h
    simpa using h
  have hminx : IsHMinimizer m h x 0 ε := by
    have hsub' : IsHMinimizer m h γ t₀ (t₀ + ε) :=
      IsHMinimizer.sub hac hmin (IsHMinimizer.actionOn_lt_top hmin (hfin (γ a) (γ b)))
        ht₀.1 (by linarith) hεb
    have h1 : actionOn m h x 0 ε = actionOn m h γ t₀ (t₀ + ε) := by
      have h := actionOn_comp_add_const' (m := m) (h := h) (γ := γ) (c := t₀) (d := t₀ + ε)
      have h2 : (fun t : ℝ => γ (t + t₀)) = x := by
        funext t; rw [hxdef]; ring_nf
      rw [← h2]
      simpa using h
    have hx0 : x 0 = γ t₀ := by rw [hxdef]; ring_nf
    have hxε : x ε = γ (t₀ + ε) := by rw [hxdef]
    show actionOn m h x 0 ε = actionPot m h (x 0) (x ε)
    rw [hx0, hxε, h1]
    exact hsub'
  have hfinx : actionPot m h (x 0) (x ε) < ⊤ := hfin (x 0) (x ε)
  have hsol := exists_solution_data_of_minimizer (m := m) (h := h) hm hh hab hac hmin hfin
    (S := Ioo t₀ (t₀ + ε)) (fun t ht => ⟨ht₀.1.trans ht.1, ht.2.trans hεb⟩) (fun t ht => hnc t ht)
  have hmem : ∀ u ∈ Ioo (0:ℝ) ε, t₀ + u ∈ Ioo t₀ (t₀ + ε) :=
    fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hxγ : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt γ (deriv γ (t₀ + u)) (t₀ + u) :=
    fun u hu => (hsol (t₀ + u) (hmem u hu)).1.self_of_nhds
  have hd2γ : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv γ) (iteratedDeriv 2 γ (t₀ + u)) (t₀ + u) :=
    fun u hu => (hsol (t₀ + u) (hmem u hu)).2.1
  have hodeγ : ∀ u ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 γ (t₀ + u) = ∇_[m] (U m) (γ (t₀ + u)) :=
    fun u hu => (hsol (t₀ + u) (hmem u hu)).2.2
  have hncx : ∀ u ∈ Ioo (0:ℝ) ε, WithoutCollisions (x u) := fun u hu => hnc (t₀ + u) (hmem u hu)
  have hx' : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt x (deriv x u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => γ (t₀ + s)) (deriv γ (t₀ + u)) u :=
      (hxγ u hu).comp_const_add t₀ u
    have h2 : deriv x u = deriv γ (t₀ + u) := deriv_shiftCurve_eq t₀ u
    rw [h2]
    exact h1
  have hd2' : ∀ u ∈ Ioo (0:ℝ) ε, HasDerivAt (deriv x) (iteratedDeriv 2 x u) u := fun u hu => by
    have h1 : HasDerivAt (fun s : ℝ => deriv γ (t₀ + s)) (iteratedDeriv 2 γ (t₀ + u)) u :=
      (hd2γ u hu).comp_const_add t₀ u
    have h2 : deriv x = fun s : ℝ => deriv γ (t₀ + s) := by
      funext s; exact deriv_shiftCurve_eq t₀ s
    rw [h2]
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    rw [h3]
    exact h1
  have hode' : ∀ u ∈ Ioo (0:ℝ) ε, iteratedDeriv 2 x u = ∇_[m] (U m) (x u) := fun u hu => by
    have h3 : iteratedDeriv 2 x u = iteratedDeriv 2 γ (t₀ + u) :=
      iteratedDeriv_two_shiftCurve_eq t₀ u
    rw [h3]
    exact hodeγ u hu
  have hEid : ∀ u ∈ Ioo (0:ℝ) ε, energy m x u = h :=
    energy_eq_level_of_minimizer hm hh hε hacx hminx hfinx hx' hd2' hode' hncx
  -- the separations
  have hsepx : ∀ u ∈ Ioo (0:ℝ) ε, ∀ k ∈ ks, ClusterSeparatedWeak k (x u) ν :=
    fun u hu => hsep (t₀ + u) (hmem u hu)
  have hsepTx : ∀ u ∈ Ioo (0:ℝ) ε, ∀ i ∉ multiUnion ks, ∀ j ∉ multiUnion ks,
      i ≠ j → ν ≤ r (x u) i j := fun u hu => hsepT (t₀ + u) (hmem u hu)
  -- the bounds
  obtain ⟨Cout, hCout0, hKout⟩ := exists_multiOutsideKineticSq_bound (m := m) (ks := ks) (x := x)
    (ε := ε / 4) (ν := ν) hm (by linarith) hν
    (fun u hu => clusterSeparated_multiUnion (hsepx u ⟨hu.1, by linarith [hu.2]⟩)
      (hsepTx u ⟨hu.1, by linarith [hu.2]⟩))
    (fun u hu => hncx u ⟨hu.1, by linarith [hu.2]⟩)
    (fun u hu => hode' u ⟨hu.1, by linarith [hu.2]⟩)
    (fun u hu => hd2' u ⟨hu.1, by linarith [hu.2]⟩)
  obtain ⟨Ccm, hCcm0, hKcm⟩ := exists_multiCMKineticSq_bound (m := m) (ks := ks) (x := x)
    (ε := ε) (ν := ν) hm hε hν hne (fun u hu => hsepx u hu) hncx hode' hd2'
  have hRest : ∀ u ∈ Ioo (0:ℝ) (ε / 4),
      multiRestPotential m ks (x u) ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν := fun u hu =>
    multiRestPotential_le (fun i => (hm i).le) hν hedj (hsepx u ⟨hu.1, by linarith [hu.2]⟩)
      (hsepTx u ⟨hu.1, by linarith [hu.2]⟩)
  refine ⟨|h| + Cout / 2 + Ccm / 2 + (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν, ?_, ?_⟩
  · have h1 : 0 ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν :=
      div_nonneg (Finset.sum_nonneg fun p _ => mul_nonneg (hm p.1).le (hm p.2).le) hν.le
    linarith [abs_nonneg h, hCout0, hCcm0]
  · intro t ht
    have htmem : t - t₀ ∈ Ioo (0:ℝ) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htmem4 : t - t₀ ∈ Ioo (0:ℝ) (ε / 4) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hEt : energy m x (t - t₀) = h := hEid (t - t₀) htmem
    have hxt : x (t - t₀) = γ t := by
      rw [hxdef]
      show γ (t₀ + (t - t₀)) = γ t
      rw [add_sub_cancel]
    have hderivt : deriv x (t - t₀) = deriv γ t := by
      rw [hxdef, deriv_shiftCurve_eq]
      congr 1
      ring
    -- the algebraic decomposition
    have hkey := multiRelEnergy_eq (m := m) (ks := ks) hm hne hedj x (t - t₀)
    -- rewrite everything in terms of `γ t`
    simp only [hxt, hderivt] at hkey
    have hOut : multiOutsideKineticSq m ks (deriv γ t) / 2 ≤ Cout / 2 := by
      have h1 : multiOutsideKineticSq m ks (deriv x (t - t₀)) ≤ Cout := hKout (t - t₀) htmem4
      rw [hderivt] at h1
      linarith
    have hCm : multiCMKineticSq m ks (deriv γ t) / 2 ≤ Ccm / 2 := by
      have h1 : multiCMKineticSq m ks (deriv x (t - t₀)) ≤ Ccm := hKcm (t - t₀) htmem4
      rw [hderivt] at h1
      linarith
    have hRe : multiRestPotential m ks (γ t) ≤ (∑ p ∈ pairFinset N, m p.1 * m p.2) / ν := by
      have h1 := hRest (t - t₀) htmem4
      rwa [hxt] at h1
    have hEn : energy m x (t - t₀) = energy m γ t := by
      show (1 / 2) * (∑ i, m i * ‖deriv x (t - t₀) i‖ ^ 2) - U m (x (t - t₀))
        = (1 / 2) * (∑ i, m i * ‖deriv γ t i‖ ^ 2) - U m (γ t)
      simp only [hderivt, hxt]
    rw [hkey, hEt]
    have h1 : 0 ≤ multiOutsideKineticSq m ks (deriv γ t) / 2 :=
      div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hm j).le (sq_nonneg _)) (by norm_num)
    have h2 : 0 ≤ multiCMKineticSq m ks (deriv γ t) / 2 :=
      div_nonneg (Finset.sum_nonneg fun k _ => mul_nonneg (clusterMass_nonneg (fun i => (hm i).le) k)
        (sq_nonneg _)) (by norm_num)
    have h3 : 0 ≤ multiRestPotential m ks (γ t) := by
      rw [multiRestPotential_eq (m := m) (ks := ks) hedj (γ t)]
      exact Finset.sum_nonneg fun p _ =>
        mul_nonneg (mul_nonneg (hm p.1).le (hm p.2).le) (inv_nonneg.mpr dist_nonneg)
    rw [abs_le]
    constructor <;>
      linarith [abs_nonneg h, neg_abs_le h, le_abs_self h, hOut, hCm, hRe, h1, h2, h3]

end Submission.NBody
