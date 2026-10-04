import Mathlib
import Submission.Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-! **`L_{li} x_i = (ζ_i²)_{(l)} · x_l` for every pair of charts** (SESSION 15, (1)).

`R_i^* (R_i h) = ζ_i² · h` pointwise (`Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free`, PROVED, no
`[I.Boundaryless]` needed), and `R_l` is pointwise linear in the section
(`Work.Diff.STE.B3.R_fun_smul`).  Hence for every pair `(i,l)` and every section `f`

  `R_l (R_i^* (R_i f)) = R_l (ζ_i² • f) = (ζ_i² ∘ pt_l) · R_l f`,

i.e. in the notation of the SESSION 14 block, `L_{li} x_i = (ζ_i²)_{(l)} · x_l`: the transported
component `L_{li} x_i` is exactly the *localised* component of the other chart.  This holds for an
arbitrary atlas `ι₀` (this is what makes the two-chart pair computation of SESSION 14 legitimate
without any restriction on the number of charts).

The proof is the two-step composition just described; we inline the two steps (a `show`-rewriting
of `R` and `mat` for the pointwise scalar multiples) to avoid depending on `R_fun_smul` for the
statement. -/

lemma R_L_eq_zeta_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i l : ι₀) (f : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.R l (D.Rstar i (fun (c d : Fin (Module.finrank ℝ E))
        (y : Fin (Module.finrank ℝ E) → ℝ) => D.R i f c d y)) a b z
      = (D.ζ i (D.pt l z)) ^ 2 * D.R l f a b z := by
  -- Step 1: unfold `R l` and `mat l` so that the outer localisation is the prefactor
  -- `ψ l z · √(dens l z)` times the evaluation of the reconstructed section at the frame of chart `l`.
  rw [show D.R l (D.Rstar i (fun (c d : Fin (Module.finrank ℝ E))
        (y : Fin (Module.finrank ℝ E) → ℝ) => D.R i f c d y)) a b z
      = D.psi l z * Real.sqrt (D.dens l z) *
        (D.Rstar i (fun (c d : Fin (Module.finrank ℝ E))
          (y : Fin (Module.finrank ℝ E) → ℝ) => D.R i f c d y) (D.pt l z)
          (D.e l a (D.pt l z)) (D.e l b (D.pt l z))) from by
        rw [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]]
  -- Step 2: the pointwise reconstruction identity `R_i^* (R_i f) = ζ_i² · f`.
  rw [Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free D f i (D.pt l z)
        (D.e l a (D.pt l z)) (D.e l b (D.pt l z))]
  -- Step 3: unfold `R l f` on the right, so both sides are products of the same prefactor with the
  -- matrix entry of `f` at the frame of chart `l`.
  rw [show D.R l f a b z = D.psi l z * Real.sqrt (D.dens l z) *
        (f (D.pt l z) (D.e l a (D.pt l z)) (D.e l b (D.pt l z))) from by
        rw [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]]
  ring

end Work.Diff.STE.B3
