import Mathlib
import Submission.Work.Drive.N2.ChartSplit

namespace Work.Drive.N2

open scoped Manifold ContDiff RealInnerProductSpace

/-- The `i`-th coordinate of `A u`, viewed as a linear functional of `u`. -/
noncomputable def rowFun (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 5)) (i : Fin 5) :
    Module.Dual ℝ (EuclideanSpace ℝ (Fin 2)) :=
  (EuclideanSpace.projₗ (𝕜 := ℝ) i).comp A.toLinearMap

@[simp] lemma rowFun_apply (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 5))
    (i : Fin 5) (u : EuclideanSpace ℝ (Fin 2)) : rowFun A i u = (A u) i := rfl

/-- Combinatorial core: if a finite family of linear functionals on a `2`-dimensional space has
trivial common kernel, then two of them have disjoint kernels. Equivalently, a spanning family of
vectors in a `2`-dimensional space contains an independent pair. -/
lemma exists_disjoint_ker_pair (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hV : Module.finrank ℝ V = 2) (f : Fin 5 → Module.Dual ℝ V)
    (hker : ∀ u : V, (∀ i, f i u = 0) → u = 0) :
    ∃ i j : Fin 5, i ≠ j ∧ Disjoint (LinearMap.ker (f i)) (LinearMap.ker (f j)) := by
  -- some functional is nonzero
  have hne : ∃ i, f i ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    have hzero : ∀ x : V, x = 0 := fun x => hker x (fun i => by rw [hc i]; rfl)
    have h0 : Module.finrank ℝ V = 0 := finrank_zero_iff_forall_zero.mpr hzero
    omega
  obtain ⟨i, hi⟩ := hne
  -- hence its kernel is a hyperplane
  have hKi : Module.finrank ℝ (LinearMap.ker (f i)) = 1 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hi
    omega
  -- and some other functional does not vanish on it
  have hex : ∃ j, ¬ (LinearMap.ker (f i) ≤ LinearMap.ker (f j)) := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    have hbot : LinearMap.ker (f i) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact hker x (fun j => hc j hx)
    rw [hbot] at hKi
    simp at hKi
  obtain ⟨j, hj⟩ := hex
  have hij : i ≠ j := by
    intro h
    subst h
    exact hj le_rfl
  refine ⟨i, j, hij, ?_⟩
  rw [disjoint_iff]
  -- the intersection is a proper subspace of the `1`-dimensional kernel, hence zero
  have hlt : LinearMap.ker (f i) ⊓ LinearMap.ker (f j) < LinearMap.ker (f i) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    exact hj (heq ▸ inf_le_right)
  have := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hKi] at this
  have h0 : Module.finrank ℝ ↥(LinearMap.ker (f i) ⊓ LinearMap.ker (f j)) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp h0

open scoped Manifold ContDiff RealInnerProductSpace in
/-- If a linear map `A : ℝ² → ℝ⁵` is injective, then for some pair of distinct coordinate indices
`a ≠ b` the `(a,b)`-minor `depProj a b ∘ A` is bijective. -/
theorem exists_depProj_comp_bijective (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 5))
    (hA : Function.Injective A) :
    ∃ a b : Fin 5, a ≠ b ∧ Function.Bijective ((Work.Drive.N2.depProj a b).comp A) := by
  -- injectivity of `A` says that the coordinate functionals separate points
  have hker : ∀ u : EuclideanSpace ℝ (Fin 2), (∀ i, rowFun A i u = 0) → u = 0 := by
    intro u hu
    apply hA
    ext i
    simpa using hu i
  obtain ⟨a, b, hab, hdisj⟩ :=
    exists_disjoint_ker_pair (EuclideanSpace ℝ (Fin 2)) (finrank_euclideanSpace_fin (n := 2))
      (rowFun A) hker
  have hinj : Function.Injective ((depProj a b).comp A) := by
    intro u v huv
    have h0 : (depProj a b) (A (u - v)) = 0 := by
      have : ((depProj a b).comp A) (u - v) = 0 := by rw [map_sub, huv, sub_self]
      simpa using this
    have h1 : (A (u - v)) a = 0 := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h0
      simpa using this
    have h2 : (A (u - v)) b = 0 := by
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h0
      simpa using this
    have hmem : u - v ∈ LinearMap.ker (rowFun A a) ⊓ LinearMap.ker (rowFun A b) :=
      ⟨by simpa [rowFun_apply] using h1, by simpa [rowFun_apply] using h2⟩
    have hz : u - v = 0 := by simpa using hdisj.le_bot hmem
    exact sub_eq_zero.mp hz
  refine ⟨a, b, hab, hinj, ?_⟩
  have hinjLM : Function.Injective (((depProj a b).comp A).toLinearMap) :=
    fun _ _ h => hinj h
  have hsurjLM := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (rfl : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))).mp hinjLM
  intro y
  obtain ⟨x, hx⟩ := hsurjLM y
  exact ⟨x, hx⟩

end Work.Drive.N2
