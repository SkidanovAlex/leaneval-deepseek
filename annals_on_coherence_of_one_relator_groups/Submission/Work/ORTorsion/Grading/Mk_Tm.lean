import Mathlib
import Submission.Work.ORTorsion.Defs

namespace Work.ORTorsion.Grading

open scoped TensorProduct

open Work.ORTorsion

open Work.ORTorsion.LaurentBase

/-- The shift rule in the form of an identity of `K`-linear maps: composing the degree-`i`
coordinate projection `Mk Lb i` with right multiplication `Tm Lb k` by a power of the Laurent
generator is the degree-`(i - k)` coordinate projection. -/
theorem Mk_Tm {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]
    (L : TorsionData K G U) {V : Type*} [AddCommGroup V] [Module K V]
    {H : Subgroup G} {φ : H →* Multiplicative ℤ} (Lb : LaurentBase K U G L.gen L.D H φ)
    (i k : ℤ) (z : V ⊗[K] ↥Lb.R) : Mk Lb i (Tm Lb k z) = Mk Lb (i - k) z := by
  have hcoord : (Lb.coord i).comp (Lb.rightMulU k) = Lb.coord (i - k) := by
    ext y
    simpa [LinearMap.comp_apply] using Lb.coord_shift i k y
  have hmap : (Mk Lb (V := V) i).comp (Tm Lb (V := V) k) = Mk Lb (V := V) (i - k) := by
    simp only [Mk, Tm]
    rw [← TensorProduct.map_comp, LinearMap.id_comp, hcoord]
  exact LinearMap.congr_fun hmap z

end Work.ORTorsion.Grading
