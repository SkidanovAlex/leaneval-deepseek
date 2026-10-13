import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllSol.VopAux.SliceTraceDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceIdents

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Clairaut for `∂_θ` and `D_z^j` on the open quadrant.**  For `f` which is `C^∞` on the open
quadrant, `D_z^j (∂_θ f)` is the `θ`-derivative of the `D_z^j`-slice.  This is the pointwise form
of the general open-set statement
`Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen`. -/
theorem DzIter_pth_eq_deriv_quad {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
      = deriv (fun θ' => Work.Spaces.DzIter j f z θ') θ :=
  (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
    (isOpen_Ioi.prod isOpen_Ioo) hf j
    (show (z, θ) ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) from ⟨hz, hθ⟩)).symm

/-- **The angular iterates of the `θ`-derivative of a slice.**  For `f` which is `C^∞` on the
open quadrant, the `i`-th iterate of `L = D_θ = sin(2θ)∂_θ` applied to the derived slice
`θ' ↦ ∂_θ(D_z^j f z ·)` is the mixed derivative `D_z^j D_θ^i (∂_θ f)`.  This is the open-quadrant
counterpart of `Work.FTS.EllipticEst.ThetaU.LopIter_deriv_DzIter_eq_mixed_open`, which is stated
in the half-strip class `SmoothOpenθ`. -/
theorem LopIter_deriv_DzIter_eq_mixed_quad {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.LopIter i
        (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ
      = Work.Spaces.mixed j i (Work.Spaces.pth f) z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  -- `pth f` is `C^∞` on the open quadrant as well
  have hf_pth : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth f))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.LocData.contDiffOn_pth hV (contDiffOn_infty.mpr hf)).of_le (by simp)
  -- the two slices agree on the open interval `(0,π/2)`, which contains `θ`
  have hEq : Set.EqOn (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ')
      (fun θ' => Work.Spaces.DzIter j (Work.Spaces.pth f) z θ')
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro θ' hθ'
    show deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ'
      = Work.Spaces.DzIter j (Work.Spaces.pth f) z θ'
    exact (Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen hV hf j
      (show (z, θ') ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) from ⟨hz, hθ'⟩))
  rw [Work.FTS.EllipticEst.ThetaU.LopIter_congr_of_isOpen isOpen_Ioo hEq i hθ]
  rw [congrFun (Work.FTS.EllipticEst.LopIter_slice i
    (Work.Spaces.DzIter j (Work.Spaces.pth f)) z) θ]
  exact Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open hf_pth j i hz hθ

/-
# The `j`-th slice group of the `ℋ^k`-integrand of `∂_θ f`, rewritten through a single slice

Same setting as `Work.FTS.EllSol.VopAux.sliceGroup_eq_sliceW`, with `f` replaced by its angular
derivative `Work.Spaces.pth f`:
claim: for `z > 0`, `θ ∈ (0,π/2)` and `f` of class `C^∞` on the open quadrant,

  `sliceGroup α k j (pth f) z θ
     = (w z)² · sliceW (k-j) α (fun θ' => deriv (fun θ'' => D_z^j f z θ'') θ') θ`,

where `sliceW K α u θ = (u θ)²·thEta θ + ∑_{1≤i≤K}(L^i u θ)²·thGam α θ` is the single-slice
functional of `Submission/Work/FTS/EllSol/VopAux/SliceTraceDefs.lean`.

ROUTE: as in `sliceGroup_eq_sliceW`, unfold `sliceGroup`, use
`Work.FTS.EllipticEst.w_div_sin_sq`/`Wt_sq` for the weights, and identify the mixed terms: for
`θ ∈ (0,π/2)` and `z > 0`,
`mixed j i (pth f) z θ = D_θ^i (D_z^j (pth f)) z θ` (open-quadrant commutation
`Work.FTS.EllipticEst.DthIter_DzIter_eq_mixed_open` in `SliceDecompDefs`), while
`D_z^j (pth f) = pth (D_z^j f)` pointwise on the open quadrant — that is
`pth_DzIter_eqOn_of_isOpen` from
`Submission/Work/FTS/EllipticEst/ThetaU/OpenSliceAux/pth_DzIter_eqOn_of_isOpen.lean` (Clairaut for
`∂_θ` and `D_z^j`, stated for an arbitrary open set with the raw `∀ n, ContDiffOn ℝ n`
hypothesis), so the mixed term is
`D_θ^i (pth (D_z^j f)) z θ = L^i (fun θ' => deriv (fun θ'' => D_z^j f z θ'') θ') θ`
by `Work.FTS.EllipticEst.LopIter_slice`. Note that `fun θ' => pth (D_z^j f) z θ'` is
*definitionally* `fun θ' => deriv (fun θ'' => D_z^j f z θ'') θ'`. The `j`-th radial summand
similarly uses `DzIter j (pth f) z θ = deriv (fun θ'' => DzIter j f z θ'') θ`
(`Work.FTS.EllipticEst.DzIter_pth_eq_deriv`-style, again from the open-quadrant Clairaut fact).
-/
theorem sliceGroup_pth_eq_sliceW (α : ℝ) (k j : ℕ) (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.sliceGroup α k j (Work.Spaces.pth f) z θ
        = (Work.Spaces.w z) ^ 2
            * Work.FTS.EllSol.VopAux.sliceW (k - j) α
                (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ := by
  intro θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- the `j`-th radial summand: `D_z^j (∂_θ f)` is `∂_θ` of the `D_z^j`-slice
  have hB : Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
      = deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ :=
    DzIter_pth_eq_deriv_quad hf j hz hθ
  -- the mixed summands: `D_z^j D_θ^i (∂_θ f)` is the `L^i`-iterate of the derived slice
  have hA : ∀ i : ℕ, Work.FTS.EllipticEst.LopIter i
        (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ
      = Work.Spaces.mixed j i (Work.Spaces.pth f) z θ :=
    fun i => LopIter_deriv_DzIter_eq_mixed_quad hf j i hz hθ
  -- the radial summand is `w(z)²` times the `η`-weighted square of the derived slice
  have hrad : (Work.Spaces.DzIter j (Work.Spaces.pth f) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.w z) ^ 2
          * ((deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := by
    rw [hB, mul_pow, Work.FTS.EllipticEst.w_div_sin_sq hθIθ z]
    ring
  -- and each mixed summand is `w(z)²` times the `γ`-weighted square of its `L`-iterate
  have hmix : ∀ i ∈ Finset.Icc 1 (k - j),
      (Work.Spaces.mixed j i (Work.Spaces.pth f) z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 *
            ((Work.FTS.EllipticEst.LopIter i
                (fun θ' => deriv (fun θ'' => Work.Spaces.DzIter j f z θ'') θ') θ) ^ 2
              * Work.FTS.EllipticEst.thGam α θ) := by
    intro i _
    rw [← hA i, mul_pow, Work.FTS.EllipticEst.Wt_sq hθIθ α z]
    ring
  rw [Work.FTS.EllipticEst.sliceGroup, Work.FTS.EllSol.VopAux.sliceW]
  rw [hrad]
  rw [Finset.sum_congr rfl hmix]
  rw [mul_add, Finset.mul_sum]

end Work.FTS.EllSol.VopAux
