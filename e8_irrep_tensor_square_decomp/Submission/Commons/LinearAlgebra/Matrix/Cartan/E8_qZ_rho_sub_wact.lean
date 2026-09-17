import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_ball4
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- **The squared length of a Weyl height is twice its height.**  For every word `L` of simple
reflections and `δ = ρ - wact L ρ` (a "Weyl height", i.e. the sum of the positive roots sent negative
by the element),

  `qZ δ = 2 * e8ht δ`.

Indeed `qZ (ρ - wρ) = qZ ρ + qZ (wρ) - 2⟪ρ, wρ⟫ = 1240 - 2 e8ht(wρ)` (using `qZ (wρ) = qZ ρ = 620`
and the symmetry of the form), while `e8ht (ρ - wρ) = 620 - e8ht (wρ)`.

This is the key estimate behind the replacement of the Weyl character formula sum by the certified
ball of radius `4`. -/
theorem E8_qZ_rho_sub_wact (L : List (Fin 8)) :
    Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ
        (Commons.LinearAlgebra.Matrix.Cartan.rhoZ -
          Commons.LinearAlgebra.Matrix.Cartan.wact L Commons.LinearAlgebra.Matrix.Cartan.rhoZ)
      = 2 * Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht
        (Commons.LinearAlgebra.Matrix.Cartan.rhoZ -
          Commons.LinearAlgebra.Matrix.Cartan.wact L Commons.LinearAlgebra.Matrix.Cartan.rhoZ) := by
  have hrr : bil rhoZ rhoZ = 620 := by rw [← e8ht_eq_bil, e8htZ_rhoZ]
  have hbil : bil rhoZ (wact L rhoZ) = e8htZ (wact L rhoZ) := (e8ht_eq_bil _).symm
  have hww : bil (wact L rhoZ) (wact L rhoZ) = 620 := by rw [bil_wact, hrr]
  have hch : bil (wact L rhoZ) rhoZ = bil rhoZ (wact L rhoZ) := bil_comm' _ _
  have hexp : bil (rhoZ - wact L rhoZ) (rhoZ - wact L rhoZ)
      = 1240 - 2 * e8htZ (wact L rhoZ) := by
    rw [bil_sub_left, bil_sub_right, bil_sub_right, hww, hbil, hch, hbil, hrr]
    ring
  rw [qZ_eq_bil, hexp, ← e8htZ_eq_e8ht, e8htZ_sub, e8htZ_rhoZ]
  ring

end Commons.LinearAlgebra.Matrix.Cartan
