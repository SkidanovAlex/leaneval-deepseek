/-
# The DeTurck field: the geometric layer of C1

This file starts the **geometric** layer of C1 (the DeTurck operator `P(g) = -2Ric(g) + L_{W(g)}g`).
The analytic content of C1 (the jet-level cancellation `pPhi = secOp + pN`) is in
`Submission/Work/Diff/STE/DeTurckJet.lean` and
`Submission/Work/Diff/STE/deTurck/pPhi_decomp.lean`; the numerical validation is in
`Scratch_room/deTurck_check.py` / `Scratch_room/deTurck_jet_check.py`.

## What is here

`connDiff g gbar x : T_xM →L[ℝ] T_xM →L[ℝ] T_xM` is the **difference of the two Levi-Civita
connections** `∇^{g} - ∇^{gbar}` at `x`, obtained from Mathlib's
`IsCovariantDerivativeOn.difference` (which bundles the tensoriality of the difference of two
covariant derivatives as a one-form with values in the endomorphism bundle).  Because both
connections are torsion free it is *symmetric*, and it is the tensor whose trace is the DeTurck
field:
`W(g) = tr_g (∇^g - ∇^{gbar}) = ∑_{ij} γ^{ij} (connDiff g gbar x) (f_i) (f_j)`
for any frame `{f_i}` of `T_xM` with inverse Gram matrix `γ`.  The trace is independent of the
frame; that linear-algebra statement (`traceVec_frame_indep` below) is what makes the field a
well-defined *global* vector field, and is the only really "new" ingredient of the geometric
layer.

## What is NOT here yet (the remaining obligations of C1)

* `traceVec`, the frame-free trace of a tensor `T_xM →L T_xM →L T_xM` with respect to the metric
  (via Mathlib's `LinearMap.trace` and the Riesz isomorphism `InnerProductSpace.toDual`), and
  `traceVec_eq_sum_invGram` identifying it with `∑_{ij} γ^{ij} S (f_i) (f_j)` in an arbitrary basis
  (from the already proved `Work.Diff.EXT.trace_eq_sum_inv_toMatrix`).
* `deTurckVec g gbar : Π x : M, TangentSpace I x`, `:= traceVec (connDiff g gbar x)`, and its
  smoothness in `x` and in the pair `(g, gbar)`.
* The **chart expression**: in the coordinate frame of the chart at `x₀`, the components of
  `deTurckVec g gbar` are `∑_{ij} γ^{ij}(Γ^k_{ij} - Γ̃^k_{ij})` with `Γ = chrCoord`/`koszulPair`
  (`Submission/Work/Diff/GE/norms_defs.lean`, `Submission/Work/Diff/GE/koszul.lean`).  This is
  `Work.Diff.STE.DeTurck.jWU` up to the dictionary `GramM ↔ chartMatFun`, `koszulPair ↔
  fderiv (chartMatFun)`; the Koszul identity `fPair_eq_koszul`/`cGram_chrB_eq_koszulPair` is
  already available.
* The chart expression of `L_{W}g` (the Lie derivative of the metric along the field), which is
  `Work.Diff.STE.DeTurck.jLW`; in the chart, `(L_Wg)(f_a,f_b) = ∂_a W_b + ∂_b W_a - 2∑_c Γ^c_{ab}W_c`
  with `W_b = ∑_c g_{bc}W^c`, i.e. `jnabW a b + jnabW b a`.
* The final bridge `chartMatrix (-2 Ric(g) + L_{W(g)}g) = pPhi (jets gbar) (jets g)`, combining the
  above with the *Ricci* part `chartRicMat = ricPhi (jets)` — the latter is the obligation of the
  EXT area (`Work.Diff.EXT.chartRicMat_eq_ricPhi`, still a `sorry` in
  `Submission/Work/Diff/EXT/chartRicMat_eq_ricPhi.lean`).

## Routes considered and rejected (so nobody repeats them)

* Using the trivialization frame `frameVector x₀ · (bB i)` **globally** to define the trace: that
  frame is a genuine frame only on `(chartAt H x₀).source` (`frameVector` is junk outside), so it
  gives a field only locally.  The trace must be defined frame-freely (via `LinearMap.trace`) or
  with a partition-of-unity combination of local frames, and the frame independence proved.
* Defining the DeTurck field *chartwise* (per chart centre) and gluing the local solutions: the
  local solutions then solve *different* gauge-modified equations and cannot be glued by
  uniqueness.  The field must be a single geometric object.
* Working with a general smooth family of fields `W(g)` instead of the DeTurck one: the pullback
  step would be fine, but the *parabolicity* of `∂ₜg = -2Ric(g) + L_{W(g)}g` fails unless the
  `∂Γ`-cancellation of the DeTurck trick holds, which pins `W(g)` to the metric trace of the
  connection difference.
-/

import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.T.lc_smooth
import Submission.Work.Diff.GE.norms_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

noncomputable section

/-- **The difference of the Levi-Civita connections of `g` and `gbar`**, at `x`, as a tensor
`T_xM →L[ℝ] T_xM →L[ℝ] T_xM`.  It is obtained from Mathlib's
`IsCovariantDerivativeOn.difference`, which supplies the tensoriality. -/
def connDiff (g gbar : SMet I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  IsCovariantDerivativeOn.difference (F := E)
    ((lcOf g).isCovariantDerivativeOn (s := Set.univ))
    ((lcOf gbar).isCovariantDerivativeOn (s := Set.univ)) x

/-- The defining property of `connDiff`: applied to any smooth section at `x` it is the difference
of the two covariant derivatives. -/
lemma connDiff_apply {g gbar : SMet I M} {x : M} {σ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    connDiff g gbar x (σ x) v = (lcOf g) σ x v - (lcOf gbar) σ x v := by
  rw [connDiff, IsCovariantDerivativeOn.difference_apply (hσ := hσ)]
  rfl

/-! ## The frame-free trace of a tensor `V →L V →L V` with respect to an inner product

This is what turns `connDiff` into the DeTurck *vector field*, and what makes that field canonical
(it must not depend on a choice of frame, since the local solutions of the gauge-modified equation
in different charts have to be glued). -/

section Trace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The Riesz representative of a continuous linear functional. -/
def rz (φ : V →L[ℝ] ℝ) : V := (InnerProductSpace.toDual ℝ V).symm φ

/-- Linearity of the Riesz representative. -/
lemma rz_add (φ ψ : V →L[ℝ] ℝ) : rz (φ + ψ) = rz φ + rz ψ := by
  simp only [rz, map_add]

lemma rz_smul (a : ℝ) (φ : V →L[ℝ] ℝ) : rz (a • φ) = a • rz φ := by
  simp only [rz, map_smul]

/-- The continuous linear functional `v ↦ ⟪v, ξ⟫`. -/
def innerFun (ξ : V) : V →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => inner ℝ v ξ
      map_add' := fun a b => by simp [inner_add_left]
      map_smul' := fun a b => by simp [inner_smul_left] }
    ‖ξ‖ fun v => by
      rw [Real.norm_eq_abs]
      calc |inner ℝ v ξ| = ‖inner ℝ v ξ‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖v‖ * ‖ξ‖ := norm_inner_le_norm v ξ
        _ = ‖ξ‖ * ‖v‖ := mul_comm _ _

@[simp] lemma innerFun_apply (ξ v : V) : innerFun ξ v = inner ℝ v ξ := rfl

@[simp] lemma innerFun_add (ξ ξ' : V) : innerFun (ξ + ξ') = innerFun ξ + innerFun ξ' := by
  ext v; simp [inner_add_right]

@[simp] lemma innerFun_smul (a : ℝ) (ξ : V) : innerFun (a • ξ) = a • innerFun ξ := by
  ext v; simp [inner_smul_right]

/-- `rzEnd S ξ` is the endomorphism `u ↦ ♯⁻¹(v ↦ ⟪S u v, ξ⟫)` attached to a bilinear map `S` and a
vector `ξ`; its trace is the `g`-trace of the bilinear form `(u,v) ↦ ⟪S u v, ξ⟫`. -/
def rzEnd (S : V →L[ℝ] V →L[ℝ] V) (ξ : V) : V →ₗ[ℝ] V where
  toFun u := rz ((innerFun ξ).comp (S u))
  map_add' u u' := by
    have h : (innerFun ξ).comp (S (u + u'))
        = (innerFun ξ).comp (S u) + (innerFun ξ).comp (S u') := by
      ext v
      simp [map_add]
    rw [h, rz_add]
  map_smul' a u := by
    have h : (innerFun ξ).comp (S (a • u)) = a • (innerFun ξ).comp (S u) := by
      ext v
      simp [map_smul]
    rw [h, rz_smul]
    simp

lemma rzEnd_add (S : V →L[ℝ] V →L[ℝ] V) (ξ ξ' : V) :
    rzEnd S (ξ + ξ') = rzEnd S ξ + rzEnd S ξ' := by
  ext u
  show rz ((innerFun (ξ + ξ')).comp (S u))
    = rz ((innerFun ξ).comp (S u)) + rz ((innerFun ξ').comp (S u))
  rw [innerFun_add, ContinuousLinearMap.add_comp, rz_add]

lemma rzEnd_smul (S : V →L[ℝ] V →L[ℝ] V) (a : ℝ) (ξ : V) :
    rzEnd S (a • ξ) = a • rzEnd S ξ := by
  ext u
  show rz ((innerFun (a • ξ)).comp (S u)) = a • rz ((innerFun ξ).comp (S u))
  rw [innerFun_smul, ContinuousLinearMap.smul_comp, rz_smul]

/-- **The trace of `S : V →L[ℝ] V →L[ℝ] V` with respect to the inner product**: the vector `w`
whose inner product with `ξ` is the trace of the endomorphism `rzEnd S ξ`, i.e.
`w = ∑_i S (e_i) (e_i)` for any orthonormal basis, or `∑_{ij} γ^{ij} S (f_i) (f_j)` for any frame
with inverse Gram matrix `γ`. -/
def traceVec [FiniteDimensional ℝ V] (S : V →L[ℝ] V →L[ℝ] V) : V :=
  rz (LinearMap.toContinuousLinearMap
    { toFun := fun ξ => LinearMap.trace ℝ V (rzEnd S ξ)
      map_add' := fun ξ ξ' => by simp [rzEnd_add]
      map_smul' := fun a ξ => by simp [rzEnd_smul] })

end Trace

section Field

/-- **The DeTurck field** `W(g) = tr_g (∇^g - ∇^{gbar})`, the trace of the difference of the two
Levi-Civita connections with respect to the metric `g`.  This is the vector field along which the
Lie derivative is taken in the DeTurck modification `P(g) = -2 Ric(g) + L_{W(g)} g`. -/
def deTurckVec (g gbar : SMet I M) (x : M) : TangentSpace I x :=
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  traceVec (V := TangentSpace I x) (connDiff g gbar x)

/-- The chart components of the DeTurck field in the coordinate frame of the chart at `x₀`, read
off from the Koszul pairings: this is `Work.Diff.STE.DeTurck.jWU` up to the dictionary between
`GramInv`/`chrCoord` and the chart matrix of `g` (see the module docstring). -/
def deTurckChartComp (g gbar : SMet I M) (x₀ p : M) (k : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ a, ∑ b, Work.Diff.GE.GramInv (fun _ : ℝ => g) (I := I) x₀ 0 p a b
    * (Work.Diff.GE.chrCoord (fun _ : ℝ => g) (I := I) x₀ k a b 0 p
        - Work.Diff.GE.chrCoord (fun _ : ℝ => gbar) (I := I) x₀ k a b 0 p)

end Field

end

end Work.Diff.STE.DeTurck
