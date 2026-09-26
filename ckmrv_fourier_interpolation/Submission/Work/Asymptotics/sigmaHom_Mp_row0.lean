import Mathlib
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.PropagateMpDefs
import Submission.Work.Asymptotics.exists_sigma_odd
import Submission.Work.Asymptotics.spanning_Mp_idealIOdd
import Submission.Work.Asymptotics.linearIndependent_Mp_idealIOdd
import Submission.Work.Residues.basis_quotient_IdealI
import Submission.Work.Residues.adjoin_R_S_R_T_eq_top
import Submission.Work.Modular.quotient_basis
import Submission.Work.Modular.quotient_linearIndependent
import Submission.Work.Modular.finrank_quotient_PSL

namespace Work.Asymptotics

open Work.Kernels
open scoped MatrixGroups

/-- **The six classes of `MpElem i` form a basis of `R ⧸ 𝓘_odd`** (`CKMRV` Proposition 3.2(1)
and 3.8(1), odd weight): they span (`Work.Asymptotics.spanning_Mp_idealIOdd`) and they are
linearly independent (`Work.Asymptotics.linearIndependent_Mp_idealIOdd`).

Equivalently, the canonical map `Φ : ℂ⁶ → R ⧸ 𝓘_odd`, `eᵢ ↦ [MpElem i]`, is a `ℂ`-linear
bijection. -/
theorem Phi_bijective : Function.Bijective Phi := by
  refine ⟨?_, Phi_surjective⟩
  intro v w hvw
  have hz : Phi (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hcoef : ∀ k : Fin 6, (v - w) k = 0 :=
    (Fintype.linearIndependent_iff.mp linearIndependent_Mp_idealIOdd) (v - w) hz
  have hvz : v - w = 0 := funext hcoef
  exact sub_eq_zero.mp hvz

/-- **The row-0 of `σ(Mp i)` in the basis `Mp` is the `i`-th standard basis vector.**
This is the odd-weight instance of the paper's observation that the first row of `σ` reads off
the coordinates in the `M'` (= `Mp`) basis (CKMRV, proof of Proposition 3.2(1)). -/
theorem sigmaHom_Mp_row0 (i : Fin 6) (j : Fin 6) :
    Work.Asymptotics.sigmaHom (Work.Asymptotics.Mp i) 0 j = (if j = i then 1 else 0 : ℂ) := by
  -- `Φ ∘ sHat γ = act γ ∘ Φ`, hence `sHat (Mp i) e₀` and `eᵢ` have the same image under `Φ`.
  have hsHat : ∀ (γ : SL(2,ℤ)) (v : Fin 6 → ℂ), Phi (sHat γ v) = act γ (Phi v) := by
    intro γ v
    simp only [sHat, LinearMap.add_apply, LinearMap.comp_apply]
    rw [map_add, Phi_sect_apply, Phi_Lam_apply, add_zero]
  have h0 : Phi (sHat (Mp i) (Pi.single 0 1)) = Phi (Pi.single i 1) := by
    rw [hsHat, Phi_single, Phi_single]
    have hone : MpElem (0 : Fin 6) * ofSL (Mp i) = ofSL (Mp i) := by
      rw [MpElem_zero, one_mul]
    rw [act_mkQ, hone]
    rfl
  have h1 : sHat (Mp i) (Pi.single 0 1) = Pi.single i 1 := Phi_bijective.1 h0
  have h2 : sigmaHom (Mp i) 0 j = (Pi.single i 1 : Fin 6 → ℂ) j := by
    show sigmaMat (Mp i) 0 j = _
    rw [sigmaMat_row]
    exact congrFun h1 j
  rw [h2]
  simp [Pi.single_apply]

end Work.Asymptotics
