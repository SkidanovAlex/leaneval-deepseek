import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

open scoped Topology

namespace Commons.Analysis.Calculus.FDeriv

/-- **Iterated derivatives commute with scaling the argument.**  If `f` is `C^i` at `b • x`, then
the `i`-th iterated derivative of `z ↦ f (b • z)` at `x` is `b^i` times the `i`-th iterated
derivative of `f` at `b • x`.

This is the `ContDiffAt` version of `iteratedFDeriv_comp_const_smul`, which Mathlib only provides
under a global `ContDiff` hypothesis. -/
theorem iteratedFDeriv_comp_const_smul_of_contDiffAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (b : ℝ) {i : ℕ} (hf : ContDiffAt ℝ i f (b • x)) :
    iteratedFDeriv ℝ i (fun z => f (b • z)) x
      = b ^ i • iteratedFDeriv ℝ i f (b • x) := by
  obtain ⟨U, hUo, hbU, hfU⟩ := hf.contDiffOn' le_rfl (by simp)
  rw [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hfU
  set L : E →L[ℝ] E := b • ContinuousLinearMap.id ℝ E with hL
  have hLx : L x = b • x := by simp [hL]
  have hcomp := L.iteratedFDerivWithin_comp_right (s := U) hfU hUo.uniqueDiffOn
      (hUo.preimage L.continuous).uniqueDiffOn hbU le_rfl
  rw [hLx] at hcomp
  rw [iteratedFDerivWithin_of_isOpen _ hUo hbU] at hcomp
  rw [iteratedFDerivWithin_of_isOpen _ (hUo.preimage L.continuous)
    (by simpa [hLx] using hbU)] at hcomp
  have h1 : (fun z => f (b • z)) = f ∘ L := by
    ext z; simp [hL]
  rw [h1, hcomp]
  clear h1 hcomp
  ext m
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have h2 : (fun i => L (m i)) = (fun i : Fin i => b • m i) := by
    ext j; simp [hL]
  rw [h2, ContinuousMultilinearMap.map_smul_univ, smul_apply]
  simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Second iterated derivative of an affine reparametrisation.**  For a `C²` function `u` at
`b • x + y`, the second iterated derivative of `z ↦ a * u (b • z + y)` at `x` equals
`a * b²` times the second iterated derivative of `u` at `b • x + y`. -/
theorem iteratedFDeriv_two_affine_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {y x : E} {a b : ℝ} (hu : ContDiffAt ℝ 2 u (b • x + y)) (m : Fin 2 → E) :
    (iteratedFDeriv ℝ 2 (fun z => a * u (b • z + y))) x m
      = a * b ^ 2 * (iteratedFDeriv ℝ 2 u (b • x + y)) m := by
  have hmap : ContDiffAt ℝ 2 (fun z : E => b • z + y) x := by
    have hlin : ContDiffAt ℝ 2 (fun z : E => b • z) x := by
      simpa using (contDiffAt_id (𝕜 := ℝ) (x := x) (n := 2)).const_smul b
    simpa using hlin.add (contDiffAt_const (x := x) (𝕜 := ℝ) (n := 2) (c := y))
  have hHcont : ContDiffAt ℝ 2 (fun z : E => u (b • z + y)) x :=
    hu.comp x hmap
  have hshift : ContDiffAt ℝ 2 (fun w : E => w + y) (b • x) := by
    simpa using (contDiffAt_id (𝕜 := ℝ) (x := (b • x)) (n := 2)).add
      (contDiffAt_const (x := (b • x)) (𝕜 := ℝ) (n := 2) (c := y))
  have hf1cont : ContDiffAt ℝ 2 (fun w : E => u (w + y)) (b • x) :=
    hu.comp (b • x) hshift
  have key1 : iteratedFDeriv ℝ 2 (fun z : E => u (b • z + y)) x
      = b ^ 2 • iteratedFDeriv ℝ 2 (fun w : E => u (w + y)) (b • x) :=
    iteratedFDeriv_comp_const_smul_of_contDiffAt (f := fun w : E => u (w + y))
      (x := x) (i := 2) b hf1cont
  have key2 : iteratedFDeriv ℝ 2 (fun w : E => u (w + y)) (b • x)
      = iteratedFDeriv ℝ 2 u (b • x + y) :=
    iteratedFDeriv_comp_add_right (f := u) 2 y (b • x)
  have keyH : iteratedFDeriv ℝ 2 (fun z : E => u (b • z + y)) x
      = b ^ 2 • iteratedFDeriv ℝ 2 u (b • x + y) := by
    rw [key1, key2]
  have hF : (fun z : E => a * u (b • z + y)) = a • (fun z : E => u (b • z + y)) := by
    ext z; simp [smul_eq_mul]
  rw [hF, iteratedFDeriv_const_smul_apply (a := a) hHcont, keyH]
  rw [smul_apply, smul_apply]
  simp only [smul_eq_mul]
  ring

end Commons.Analysis.Calculus.FDeriv