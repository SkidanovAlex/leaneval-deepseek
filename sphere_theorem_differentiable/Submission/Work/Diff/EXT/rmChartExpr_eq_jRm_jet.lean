import Mathlib
import Submission.Work.Diff.EXT.ricJetDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.EXT.koszulPair_eq_sKz
import Submission.Work.Diff.EXT.dOp_koszulPair_eq_sKzD

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

/-!
# The coordinate curvature formula is the jet expression `jRm`

Fix a smooth metric `g`, a chart centre `x₀`, a point `p` in the source of the chart and the chart
coordinate `y = (extChartAt I x₀) p`.  Write `L = fderiv ℝ (chartMatFun g x₀) y` and
`B = fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y` for the first and second spatial jets of the chart
matrix of `g`, and `A = gmat g x₀ p` for the Gram matrix of the coordinate frame at `p`.

The main result is that the explicit Koszul/Christoffel coordinate expression
`Work.Diff.GE.rmChartExpr` for the curvature components `R_{abcd} = ⟪R(σ_a,σ_b)σ_d, σ_c⟫` in the
coordinate frame of the chart at `x₀`, specialised to the constant family `t ↦ g` at `t = 0`, is
the jet expression `Work.Diff.EXT.jRm A L B a b c d` of `ricJetDefs`.

The ingredients are all available:

* `Work.Diff.EXT.koszulPair_eq_sKz`: the Koszul pairing `Γ_{abc}` of the coordinate frame is
  `sKz (dJet1 g x₀ y) a b c`, i.e. `jKz L a b c`;
* `Work.Diff.EXT.dOp_koszulPair_eq_sKzD` (proved in `dOp_koszulPair_eq_sKzD`): its coordinate
  derivative `∂_m Γ_{abc}` is `sKzD (dJet2 g x₀ y) m a b c`, i.e. `jKzD B m a b c`;
* `jInv A = sInv (dJet0 g x₀ y)` is the inverse Gram matrix, which is definitionally the inverse of
  the chart matrix.

The only rounding off is the *symmetry of the metric*: the expression `jRm` is stated with the
Koszul pairings of `jKz` in the order `Γ_{dbc}, Γ_{dbr}, Γ_{dar}`, whereas the Koszul formula
`rmChartExpr` produces them in the order `Γ_{bdc}, Γ_{bdr}, Γ_{adr}`.  Both orderings agree because
the metric is symmetric, `g.inner q σᵢ σⱼ = g.inner q σⱼ σᵢ`; this gives the symmetry of `jKz` in
its first two slots (`jKz_swap_slot12`, from the symmetry of the first jet of the chart matrix) and
the symmetry of `jKzD` in its second and third slots (`jKzD_swap_slot23`, from the symmetry of the
second jet, which is reduced to the pointwise symmetry of the metric by `kz_second`).
-/

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
variable [I.Boundaryless] [T2Space M]

/-- **The Koszul pairing is symmetric in its first two slots.**  `Γ_{abc} = ½(∂_a g_{bc} + ∂_b g_{ac}
- ∂_c g_{ab})`, so the difference `Γ_{abc} - Γ_{bac} = ½(∂_c g_{ba} - ∂_c g_{ab})` vanishes by the
symmetry of the metric, read through the symmetry of the first jet of the chart matrix
(`Work.Diff.EXT.kz_chartMatFun_swap`). -/
lemma jKz_swap_slot12
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (a b c : Fin (Module.finrank ℝ E)) :
    jKz (fderiv ℝ (chartMatFun g x₀) y) a b c
      = jKz (fderiv ℝ (chartMatFun g x₀) y) b a c := by
  simp only [Work.Diff.EXT.jKz]
  rw [kz_chartMatFun_swap (I := I) g x₀ hy c a b]
  ring

/-- **The second jet matrices of the chart matrix are symmetric in their entries.**  For the metric
coefficient `g_{ij}`, the derivative of `q ↦ ∂_k g_{ij}(q)` is `(dJet2 g x₀ y m k) i j`; swapping
`i` and `j` does not change the function, by the pointwise symmetry `g.symm q` of the metric, so
(by `Work.Diff.EXT.kz_second`) it does not change the second derivative either. -/
lemma dJet2_entry_symm
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (m k i j : Fin (Module.finrank ℝ E)) :
    (dJet2 g x₀ y m k) i j = (dJet2 g x₀ y m k) j i := by
  have hfun : (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) i))
        (cvec (I := I) x₀ q' (bB (E := E) j)))
      = (fun q' : M => g.inner q' (cvec (I := I) x₀ q' (bB (E := E) j))
        (cvec (I := I) x₀ q' (bB (E := E) i))) := by
    funext q'; exact g.symm q' _ _
  rw [← kz_second (I := I) g x₀ hy i j k m, ← kz_second (I := I) g x₀ hy j i k m, hfun]

/-- **The derivative of the Koszul pairing is symmetric in its second and third slots**, which is
the symmetry `Γ_{abc} = Γ_{bac}` differentiated. -/
lemma sKzD_swap_slot23
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (m a b c : Fin (Module.finrank ℝ E)) :
    sKzD (dJet2 g x₀ y) m a b c = sKzD (dJet2 g x₀ y) m b a c := by
  have h := dJet2_entry_symm (I := I) g x₀ hy m c a b
  simp only [Work.Diff.EXT.sKzD]
  rw [h]
  ring

/-- The same symmetry for the jet expression `jKzD` (which is `sKzD` of the second jet,
definitionally). -/
lemma jKzD_swap_slot23
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (m a b c : Fin (Module.finrank ℝ E)) :
    jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) m a b c
      = jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) m b a c :=
  sKzD_swap_slot23 (I := I) g x₀ hy m a b c

/-- The scalar-jet Koszul pairing of the first coordinate jet is the jet expression `jKz`. -/
lemma sKz_eq_jKz (g : Submission.Diff.SMet I M) (x₀ : M) (y : E)
    (a b c : Fin (Module.finrank ℝ E)) :
    sKz (dJet1 g x₀ y) a b c = jKz (fderiv ℝ (chartMatFun g x₀) y) a b c := rfl

/-- The inverse Gram matrix of the coordinate frame is `jInv` of the Gram matrix `gmat`. -/
lemma GramInv_eq_jInv
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E) (m n : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 ((extChartAt I x₀).symm y) m n
      = jInv (gmat (I := I) g x₀ ((extChartAt I x₀).symm y)) m n := by
  have hG : Work.Diff.GE.GramM (I := I) (fun _ : ℝ => g) x₀ 0 ((extChartAt I x₀).symm y)
      = Matrix.of (gmat (I := I) g x₀ ((extChartAt I x₀).symm y)) := by
    unfold Work.Diff.GE.GramM Work.Diff.GE.mComp Work.Diff.EXT.gmat Work.Diff.EXT.fvec
    simp only [Work.Diff.GE.cFrame_apply]
    rfl
  unfold Work.Diff.GE.GramInv Work.Diff.EXT.jInv
  rw [hG]

/-- **`rmChartExpr` is `jRm`**, in the chart coordinates `y` of the base point. -/
private lemma rmChartExpr_eq_jRm_jet_aux
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (a b c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => g) x₀ a b c d 0 ((extChartAt I x₀).symm y)
      = jRm (gmat (I := I) g x₀ ((extChartAt I x₀).symm y))
          (fderiv ℝ (chartMatFun g x₀) y)
          (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) a b c d := by
  set p : M := (extChartAt I x₀).symm y with hpdef
  -- the three ingredients of `rmChartExpr`
  have hKz : ∀ m n o : Fin (Module.finrank ℝ E),
      Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ m n o 0 p
        = sKz (dJet1 g x₀ y) m n o :=
    fun m n o => koszulPair_eq_sKz (I := I) g x₀ hy m n o
  have hKzD1 : Work.Diff.GE.dOp (I := I) x₀ a
      (Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ b d c) 0 p
      = sKzD (dJet2 g x₀ y) a b d c :=
    dOp_koszulPair_eq_sKzD (I := I) g x₀ hy a b c d
  have hKzD2 : Work.Diff.GE.dOp (I := I) x₀ b
      (Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ a d c) 0 p
      = sKzD (dJet2 g x₀ y) b a d c :=
    dOp_koszulPair_eq_sKzD (I := I) g x₀ hy b a c d
  have hInv : ∀ m n : Fin (Module.finrank ℝ E),
      Work.Diff.GE.GramInv (I := I) (fun _ : ℝ => g) x₀ 0 p m n
        = jInv (gmat (I := I) g x₀ p) m n :=
    fun m n => GramInv_eq_jInv (I := I) g x₀ y m n
  -- the two `jKzD` terms of `jRm`, brought to the order used by `rmChartExpr`
  have hJ1 : jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) a d b c
      = sKzD (dJet2 g x₀ y) a b d c := by
    rw [jKzD_swap_slot23 (I := I) g x₀ hy a d b c]
    rfl
  have hJ2 : jKzD (fderiv ℝ (fderiv ℝ (chartMatFun g x₀)) y) b d a c
      = sKzD (dJet2 g x₀ y) b a d c := by
    rw [jKzD_swap_slot23 (I := I) g x₀ hy b d a c]
    rfl
  -- the two Koszul sums of `jRm`, likewise
  have hSum1 : (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        jInv (gmat (I := I) g x₀ p) m n * sKz (dJet1 g x₀ y) b d m
          * sKz (dJet1 g x₀ y) a c n)
      = (∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
        jInv (gmat (I := I) g x₀ p) r s * jKz (fderiv ℝ (chartMatFun g x₀) y) d b r
          * jKz (fderiv ℝ (chartMatFun g x₀) y) a c s) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [sKz_eq_jKz (I := I) g x₀ y b d m, sKz_eq_jKz (I := I) g x₀ y a c n,
      jKz_swap_slot12 (I := I) g x₀ hy b d m]
  have hSum2 : (∑ m : Fin (Module.finrank ℝ E), ∑ n : Fin (Module.finrank ℝ E),
        jInv (gmat (I := I) g x₀ p) m n * sKz (dJet1 g x₀ y) a d m
          * sKz (dJet1 g x₀ y) b c n)
      = (∑ r : Fin (Module.finrank ℝ E), ∑ s : Fin (Module.finrank ℝ E),
        jInv (gmat (I := I) g x₀ p) r s * jKz (fderiv ℝ (chartMatFun g x₀) y) d a r
          * jKz (fderiv ℝ (chartMatFun g x₀) y) b c s) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [sKz_eq_jKz (I := I) g x₀ y a d m, sKz_eq_jKz (I := I) g x₀ y b c n,
      jKz_swap_slot12 (I := I) g x₀ hy a d m]
  unfold Work.Diff.GE.rmChartExpr jRm
  rw [hKzD1, hKzD2]
  simp only [hKz, hInv]
  rw [hJ1, hJ2, hSum1, hSum2]
  ring

/-- **The jet form of the coordinate curvature formula.**  The explicit coordinate expression
`Work.Diff.GE.rmChartExpr` for the curvature components in the coordinate frame of the chart at
`x₀` (for the constant metric family `fun _ => g`) is the jet expression `Work.Diff.EXT.jRm` of
`ricJetDefs`.

Route.  Unfold `rmChartExpr`, `dOp`, `GramInv`, `GramM`: the `dOp` terms are `mvfderiv`'s along the
frame vector `frameVector x₀ p (bB a)` and the `GramInv`/`GramM` terms are `(Matrix.of (gmat g x₀ p))⁻¹`
and `Matrix.of (gmat g x₀ p)`.  Rewrite `koszulPair` to the jet expression `jKz` using the proved
`Work.Diff.EXT.koszulPair_eq_sKz`, convert the `mvfderiv`'s to `fderiv`'s of the chart-coordinate
representative with `Submission.ChartCurvCont.mvfderiv_frameVector_eq_fderiv` (and
`mvfderiv_congr_of_eventuallyEq` to pass from the manifold function to its chart representative on a
neighbourhood of `p`), and differentiate the resulting expression with the elementary identity
`(fderiv ℝ (fun y' => (fderiv ℝ V y') w) y) v = ((fderiv ℝ (fderiv ℝ V) y) v) w` (obtainable from
`ContinuousLinearMap.apply` and the chain rule for `HasFDerivAt`).  Finally use the symmetry of
`jKz`/`jKzD` in their first two slots, which follows from the symmetry `(g.symm p)` of the metric.
Do NOT use the sorried `Work.Diff.EXT.rmChartExpr_eq_sRm` or `Work.Diff.EXT.dOp_koszulPair_eq`; the
statement is provable directly. -/
theorem rmChartExpr_eq_jRm_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {p : M} (hp : p ∈ (chartAt H' x₀).source)
    (a b c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.rmChartExpr (I := I) (fun _ : ℝ => g) x₀ a b c d 0 p
      = Work.Diff.EXT.jRm (Work.Diff.EXT.gmat (I := I) g x₀ p)
          (fderiv ℝ (Work.Diff.EXT.chartMatFun g x₀) ((extChartAt I x₀) p))
          (fderiv ℝ (fderiv ℝ (Work.Diff.EXT.chartMatFun g x₀)) ((extChartAt I x₀) p))
          a b c d := by
  have hps : p ∈ (extChartAt I x₀).source := by rwa [extChartAt_source (I := I) x₀]
  have hy : (extChartAt I x₀) p ∈ (extChartAt I x₀).target := (extChartAt I x₀).map_source hps
  have hsymm : (extChartAt I x₀).symm ((extChartAt I x₀) p) = p := (extChartAt I x₀).left_inv hps
  have h := rmChartExpr_eq_jRm_jet_aux (I := I) g x₀ hy a b c d
  rw [hsymm] at h
  exact h

end Work.Diff.EXT
