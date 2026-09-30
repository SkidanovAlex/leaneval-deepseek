import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.GradedHilbDefs
import Submission.Work.BW.hilb_serre_poly
import Submission.Work.BW.HilbSerreDefs
import Submission.Work.BW.quotient_isGrading

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW


/-- The fibre of `Finset.univ ⊆ Fin (N+1) × Fin 2` over the first coordinate has cardinality `2`. -/
theorem card_univ_filter_fst (N : ℕ) (i : Fin (N + 1)) :
    (Finset.univ.filter (fun v : Fin (N + 1) × Fin 2 => v.1 = i)).card = 2 := by
  rw [← Fintype.card_subtype (fun v : Fin (N + 1) × Fin 2 => v.1 = i), ← Fintype.card_fin 2]
  exact Fintype.card_congr
    { toFun := fun v => v.1.2
      invFun := fun j => ⟨(i, j), rfl⟩
      left_inv := fun v => Subtype.ext (Prod.ext v.2.symm rfl)
      right_inv := fun j => rfl }

/-- Multigraded Hilbert–Serre for a quotient by a multihomogeneous ideal of the coordinate ring
`R = MR N = ℂ[X_{i,0}, X_{i,1}]` (graded so that both variables of the `i`-th factor have degree
`e_i`): there is a single polynomial `Q : MvPolynomial (Fin (N+1)) ℚ` whose binomial kernel `kFun`
with multiplicities `2` reproduces every graded piece dimension of `R/J`, and the same with
`J = ⊤`.
Intended proof: instantiate `hilb_serre_poly` with `M := (MR N) ⧸ J`, the grading given by the
images of `pieceZ N u`, and `V = univ` (so the multiplicity vector `fun i => (univ.filter
(·.1 = i)).card` is the constant `2`); the needed package (grading, `Module.Finite`, finite pieces,
and `finrank = hilbIdeal`) is stated in `Submission.Work.BW.quotient_isGrading` (in flight). -/
theorem hilb_serre_input (N : ℕ) :
    ∀ (J : Ideal (MR N)), MultiHom N J →
      ∃ Q : MvPolynomial (Fin (N + 1)) ℚ, ∀ u : Fin (N + 1) →₀ ℤ,
        (hilbIdeal N J u : ℚ) = kFun N (fun _ => 2) Q u := by
  intro J hJ
  obtain ⟨hgrad, hfin, hfd, hfr⟩ := quotient_isGrading N J hJ
  obtain ⟨P, hP⟩ := hilb_serre_poly N Finset.univ (MR N ⧸ J)
    (fun u => Submodule.map (Ideal.Quotient.mkₐ ℂ J).toLinearMap (pieceZ N u))
    hgrad hfin hfd (fun v hv => absurd (Finset.mem_univ v) hv)
  refine ⟨P, fun u => ?_⟩
  have hβ : (fun i : Fin (N + 1) =>
      (Finset.univ.filter (fun v : Fin (N + 1) × Fin 2 => v.1 = i)).card) = fun _ => 2 :=
    funext fun i => card_univ_filter_fst N i
  rw [hβ] at hP
  rw [← hfr u]
  exact hP u

end Work.BW
