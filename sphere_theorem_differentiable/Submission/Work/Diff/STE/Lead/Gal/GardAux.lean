import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.GardDef
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.deTurck.pPhi_decomp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The residual of the DeTurck transport in the B3 components (vocabulary)

This module fixes the objects of the route to `Work.Diff.STE.Lead.Gal.gardTransport_holds`.
It builds on the *proved* module `Submission.Work.Diff.STE.B3.TransportDefs`, which provides

* `Ff D j z a i` — the frame change: `e_j a = Σ_i Ff_{ai} ∂_i` (Θ),
* `Mf D h j z a b` — the chart matrix of `h` in the `g₀`-orthonormal frame of chart `j` (`D.mat`),
* `Gf D h j z i k` — the chart matrix of `h` in the *coordinate* frame,
* `wf D j z = ψ_j √dens_j` — the localised weight,
* and the identity `Mf = Ff · Gf · Ffᵀ` (`Mf_eq`), the dual `Gf = Finvf · Mf · Finvfᵀ`
  (`Gf_eq_dual`, `Finvf = Ff⁻¹`), and the invertibility of `Ff` on the `2σ`-ball
  (`det_Ff_ne_zero`).

Here we add the **residual data**: the coordinate chart matrix `G` and its first jet `∂G` as
explicit functions `gardGof`, `gardLof` of the *orthonormal*-frame chart matrix `u` and of its
first jet `du` (so that `G` may be eliminated from every expression in favour of `M` and `∂M`),
the background jets `gardAbar/gardLbar/gardBbar`, the frame-change correction `gardCorr`
(the eight terms of the two-fold Leibniz rule) and the two residual functions

* `gardRes z u du` — the part of `(P h)` in the orthonormal frame which is *not*
  `Σ_{cd}(G⁻¹)^{cd}∂_c∂_d M`; a smooth function of `(z, u, du)`;
* `gardResTot z η u du` — the same after pulling the localised weight `w` inside the two
  derivatives, i.e. the difference `w·(P h)_{ab} - Σγ^{cd}∂_c∂_d(w·M_{ab})`, cut off by `η`.

Flat-derivative convention: `∂_c∂_d F := pdR d (pdR c F)` (inner `c`, outer `d`).
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The first jet of the inverse frame matrix (a *fixed* smooth function of `z`):
`gardFinvfD c i a z = ∂_c (Finvf · i a) z`. -/
def gardFinvfD (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (c : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) :
    Work.Diff.EXT.MatE (E := E) :=
  fun i a => Work.Diff.STE.pdR c
    (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.B3.Finvf (I := I) (M := M) D j y i a) z

/-- **The coordinate chart matrix from the orthonormal-frame chart matrix**:
`G = Finvf · M · Finvfᵀ`, i.e. `gardGof z u i k = Σ_{ab} Finvf_{ia} u_{ab} Finvf_{kb}`. -/
def gardGof (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (u : Work.Diff.EXT.MatE (E := E)) :
    Work.Diff.EXT.MatE (E := E) :=
  fun i k => ∑ a, ∑ b,
    Work.Diff.STE.B3.Finvf (I := I) (M := M) D j z i a * u a b
      * Work.Diff.STE.B3.Finvf (I := I) (M := M) D j z k b

/-- **The first jet of the coordinate chart matrix as a function of `(u, du)`**: the product rule
applied to `G = Finvf · M · Finvfᵀ`. -/
def gardLof (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (u : Work.Diff.EXT.MatE (E := E))
    (du : Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E))
    (c : Fin (Module.finrank ℝ E)) : Work.Diff.EXT.MatE (E := E) :=
  fun i k => ∑ a, ∑ b,
    ( gardFinvfD (I := I) (M := M) D j c z i a * u a b
        * Work.Diff.STE.B3.Finvf (I := I) (M := M) D j z k b
      + Work.Diff.STE.B3.Finvf (I := I) (M := M) D j z i a * du c a b
        * Work.Diff.STE.B3.Finvf (I := I) (M := M) D j z k b
      + Work.Diff.STE.B3.Finvf (I := I) (M := M) D j z i a * u a b
        * gardFinvfD (I := I) (M := M) D j c z k b )

/-- The continuous linear map with prescribed values on the coordinate basis: the first-jet
argument of the jet-level operator `pN`. -/
def gardLclm (du : Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E)) :
    E →L[ℝ] Work.Diff.EXT.MatE (E := E) :=
  ((Work.Diff.EXT.bB (E := E)).constr ℝ du).toContinuousLinearMap

/-- The value `Ā` of the background chart matrix `g₀` at the flat coordinate `z`. -/
def gardAbar (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : Work.Diff.EXT.MatE (E := E) :=
  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
    (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z)).1

/-- The first jet `L̄` of the background chart matrix. -/
def gardLbar (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : E →L[ℝ] Work.Diff.EXT.MatE (E := E) :=
  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
    (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z)).2.1

/-- The second jet `B̄` of the background chart matrix. -/
def gardBbar (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E) :=
  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j)
    (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z)).2.2

/-- **The frame-change correction.**  With `M_{ab} = Σ_{ik} Ff_{ai}Ff_{bk}G_{ik}`, the two-fold
Leibniz rule gives
`Σ_{ik} Ff_{ai}(∂_c∂_d G_{ik}) Ff_{bk} = ∂_c∂_d M_{ab} - gardCorr`,
where `gardCorr` collects the eight terms in which `G_{ik}` is not twice differentiated; here
`G = gardGof z u` and `∂_e G = gardLof z u du e`. -/
def gardCorr (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (u : Work.Diff.EXT.MatE (E := E))
    (du : Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E))
    (c d a b : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ i, ∑ k,
    ( Work.Diff.STE.pdR d (Work.Diff.STE.pdR c
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
              * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k)) z
        * gardGof (I := I) (M := M) D j z u i k
      + Work.Diff.STE.pdR c
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
              * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
        * gardLof (I := I) (M := M) D j z u du d i k
      + Work.Diff.STE.pdR d
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
              * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
        * gardLof (I := I) (M := M) D j z u du c i k )

/-- **The DeTurck residual in the orthonormal frame** as a smooth function of `(z, u, du)`:
the lower-order part of the chart expression of `P` plus the frame-change correction. -/
def gardRes (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) (u : Work.Diff.EXT.MatE (E := E))
    (du : Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E)) :
    Work.Diff.EXT.MatE (E := E) :=
  fun a b =>
    ( ∑ i, ∑ k,
        Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k
          * Work.Diff.STE.DeTurck.pN (gardAbar (I := I) (M := M) D j z)
              (gardLbar (I := I) (M := M) D j z) (gardBbar (I := I) (M := M) D j z)
              (gardGof (I := I) (M := M) D j z u)
              (gardLclm (gardLof (I := I) (M := M) D j z u du)) i k )
      - ∑ c, ∑ d, Work.Diff.EXT.jInv (gardGof (I := I) (M := M) D j z u) c d
          * gardCorr (I := I) (M := M) D j z u du c d a b

/-- **The weighted residual**, cut off by `η`: with `w = wf D j` and `u = M(z)`, `du = ∂M(z)`, this
is `η(z)·( w(z)·gardRes(z,u,du)_{ab} - Σ_{cd}(γ)^{cd}(2∂_c w·du_{c,ab} + ∂_d∂_c w·u_{ab}) )`, i.e.
`w·(P h)_{ab} - Σ_{cd}γ^{cd}∂_c∂_d(w·M_{ab})` for an appropriate `A = γ`. -/
def gardResTot (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (z : Fin (Module.finrank ℝ E) → ℝ) (u : Work.Diff.EXT.MatE (E := E))
    (du : Fin (Module.finrank ℝ E) → Work.Diff.EXT.MatE (E := E)) :
    Work.Diff.EXT.MatE (E := E) :=
  fun a b => η z *
    ( Work.Diff.STE.B3.wf (I := I) (M := M) D j z
        * gardRes (I := I) (M := M) D j z u du a b
      - ∑ c, ∑ d, Work.Diff.EXT.jInv (gardGof (I := I) (M := M) D j z u) c d
        * ( 2 * Work.Diff.STE.pdR c (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z
              * du d a b
            + Work.Diff.STE.pdR d (Work.Diff.STE.pdR c
                (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z * u a b ) )

end

end Work.Diff.STE.Lead.Gal
