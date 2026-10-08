import Mathlib
import Submission.Work.ZASS.Defs

namespace Work.ZASS

/-- An involution `s` that moves `zero` to `inf` conjugates every element of a subgroup `U`
lying in the Borel `G_inf` into the stabilizer of `zero`.

Indeed `s⁻¹ = s`, so `s⁻¹ • zero = s • zero = inf` is fixed by `u ∈ U ≤ G_inf`, whence
`(s * u * s⁻¹) • zero = s • inf = s • (s • zero) = (s * s) • zero = zero`. -/
theorem conj_unipotent_le_stabilizer_zero {G X : Type} [Group G] [MulAction G X]
    {inf zero : X} {U : Subgroup G} (hUB : U ≤ Work.Zassenhaus.borel G inf) {s : G}
    (hs : s * s = 1) (hszero : s • zero = inf) :
    ∀ u ∈ U, s * u * s⁻¹ ∈ MulAction.stabilizer G zero := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  intro u hu
  rw [MulAction.mem_stabilizer_iff]
  have hu_inf : u • inf = inf := MulAction.mem_stabilizer_iff.mp (hUB hu)
  calc (s * u * s⁻¹) • zero = s • (u • (s⁻¹ • zero)) := by rw [mul_smul, mul_smul]
    _ = s • (u • (s • zero)) := by rw [hsinv]
    _ = s • (u • inf) := by rw [hszero]
    _ = s • inf := by rw [hu_inf]
    _ = s • (s • zero) := by rw [hszero]
    _ = (s * s) • zero := by rw [mul_smul]
    _ = zero := by rw [hs, one_smul]

end Work.ZASS
