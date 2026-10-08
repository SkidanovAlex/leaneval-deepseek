import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff
import Submission.Work.L2F.Torus.ne_conj_negOne_mul

namespace Work.L2F.Torus

/-- Every element of `SL(2,F)` whose image in `PSL(2,F)` commutes with `π x` either commutes with
`x` or conjugates `x` to `-x`; and the latter is excluded when `π x` has prime order `r ≠ 2`
(`ne_conj_negOne_mul`).  Hence `C_{PSL}(π x) = π(C_{SL}(x))`. -/
theorem centralizer_pslMap_eq (F : Type*) [Field F] (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2) (hx : orderOf (Work.PSL2.pslMap F x) = r) : Subgroup.centralizer ({Work.PSL2.pslMap F x} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) = (cent F x).map (Work.PSL2.pslMap F) := by
  apply le_antisymm
  · intro g hg
    -- lift `g` to `y ∈ SL(2,F)`
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) g
    have hy' : Work.PSL2.pslMap F y = g := hy
    have hcomm' : Work.PSL2.pslMap F y * Work.PSL2.pslMap F x =
        Work.PSL2.pslMap F x * Work.PSL2.pslMap F y := by
      rw [hy']
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    -- the commutator `[y, x]` lies in the kernel `{±1}`
    have hcomm : Work.PSL2.pslMap F (y * x * y⁻¹ * x⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm']
      group
    rcases (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (y * x * y⁻¹ * x⁻¹)).mp hcomm with h1 | h1
    · -- `[y, x] = 1`: `y` commutes with `x`
      refine Subgroup.mem_map.mpr ⟨y, ?_, hy'⟩
      rw [cent_apply, Subgroup.mem_centralizer_singleton_iff]
      have hyx : y * x * y⁻¹ = x := mul_inv_eq_one.mp h1
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * y := by rw [hyx]
    · -- `[y, x] = -1`, i.e. `y x y⁻¹ = -x`: excluded by `ne_conj_negOne_mul`
      exfalso
      refine ne_conj_negOne_mul F h2 x y r hr hr2 hx ?_
      calc y * x * y⁻¹ = (y * x * y⁻¹ * x⁻¹) * x := by group
        _ = Work.L2F.negOne F * x := by rw [h1]
  · -- conversely, the image of an element commuting with `x` commutes with `π x`
    rintro g ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyx : y * x = x * y := by
      simpa [cent_apply] using (Subgroup.mem_centralizer_singleton_iff.mp hy)
    rw [← map_mul, ← map_mul, hyx]

end Work.L2F.Torus
