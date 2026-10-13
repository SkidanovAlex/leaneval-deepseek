import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS_RegExport.RXT.velPert

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

/-- **The right-hand side of the `ε`-scheme is `C^∞` on the open quadrant for `ClassC` data.**

Route for the prover (all ingredients are on disk):

* conjunct 1 (`L₁₂(F_*+w)`) and conjunct 2 (`FK(F_*+w)`): additivity over `F = F_* + w`
  (`StrongPersist.H6Rows.NZaux.L12AddFstar` for `L₁₂` and `GalFields.RHS.FK_add_of_slices` for
  `FK`, with the θ-slice integrability from `Stability.integrableOn_slice_Fstar` and
  `GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem`).  The `F_*`-moments are explicit:
  `GalFields.RHS.smoothOpen_L12_Fstar_rad`, `smoothOpen_FK_Fstar_rad` (and
  `Nonlinear.FstarPkg.FK_Fstar`, `Construction.L12_Fstar_eq`).
* **`FK w` needs no elliptic data at all**: `Construction.FK F z = 3 * Elliptic.Fstar F z`
  (`RXT.velPert_FK_eq`), so `ClassC.fsm` (`∀ m, ContDiffOn ℝ m (Elliptic.Fstar w) (Ioi 0)`)
  gives `SmoothOpen (fun z _ => FK w z)` through `NonlinRows.smoothOpen_radial` +
  `smoothOpen_const_mul`.  (This is the honed counterpart of the `SmoothQuad`-based
  `smoothOpen_FK_radial`; **do not** try to get `SmoothQuad w` from `ClassC α w` — it does not
  follow.)
* conjunct 3 (`LGammaT α w`): `GalFields.RHS.smoothOpen_LGammaT_of_L12` with
  `SmoothOpen (L12 w)` from `NonlinRows.smoothOpen_L12_radial` (needs only `SmoothOpen Φg` and
  `SmoothOpen (Vop (PhiTil α w Φg))`, both from `hell`), `hw.reg` for `SmoothOpen w`.
* conjunct 4 (`N0`): `StrongPersist.H6Pair6Aux.SmoothN0` with `SmoothOpen w`, conjunct 1.
* conjunct 5 (`N`): copy the proof of `GalFields.RHS.smoothOpen_N_Ftot_gal` verbatim, with the
  single `hFKg` step replaced by the `fsm`-route above and `hmem4` from `ClassC.mem`
  (`OpenPkg.HkMem_mono_open hw.reg 4 _ hw.mem`). -/
theorem SmoothOpenRHS {α Ce Cs : ℝ} {Φs w Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Ftot α w) z) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK (Work.Construction.Ftot α w) z) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α w) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α w)
      (fun z θ => Φs z θ + Φg z θ)) := by
  -- the `ℋ⁴`-honesty of the perturbation `w`, from the `ℋ⁷`-honesty of the class
  have hmem4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  -- `SmoothOpen (z ↦ L₁₂(w)(z))`: the perturbation half of the first moment
  have hL12w : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hell.smooth hell.V.1.1
  -- `SmoothOpen (z ↦ FK(w)(z))`: via `FK F = 3 F_*(F)`, so only `ClassC.fsm` is used
  have hFKw : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK w z) := by
    have hfs : Work.FTS.EllipticEst.SmoothOpen
        (fun z (_ : ℝ) => Work.Elliptic.Fstar w z) :=
      Work.FTS.NonlinRows.smoothOpen_radial (r := Work.Elliptic.Fstar w) hw.fsm
    refine (Work.FTS.NonlinRows.smoothOpen_const_mul 3 hfs).congr ?_
    intro z _ hz _ _
    exact (Work.FTS_RegExport.RXT.velPert_FK_eq w z).symm
  -- the two `F_*`-moments are explicit
  have hL12F : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_L12_Fstar_rad α hα hα1
  have hFKF : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα hα1
  -- the first moment `L₁₂(F_* + w)`
  have hL12tot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.L12 (Work.Construction.Ftot α w) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hL12F hL12w).congr (by
      intro z _ hz _ _
      exact (Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα hα1 hw.reg hmem4 z hz).symm)
  -- the second moment `FK(F_* + w)`
  have hFKadd : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α w) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z := by
    intro z hz
    exact Work.FTS.GalFields.RHS.FK_add_of_slices
      (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4 hz)
  have hFKtot : Work.FTS.EllipticEst.SmoothOpen
      (fun z (_ : ℝ) => Work.Construction.FK (Work.Construction.Ftot α w) z) :=
    (Work.FTS.NonlinRows.smoothOpen_add hFKF hFKw).congr (by
      intro z _ hz _ _
      exact (hFKadd z hz).symm)
  -- conjunct 3: the transport-modified linearised operator
  have hLG : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α w) :=
    Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12 hL12w hw.reg
  -- conjunct 4: the quadratic term of the modulation
  have hN0 : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
    Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hw.reg hL12w
  -- conjunct 5: the elliptic correction term `N` (a verbatim transcription of
  -- `GalFields.RHS.smoothOpen_N_Ftot_gal`, with the `FK w` slot fed by `hFKw`)
  have hN : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) := by
    have hΦ : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Φs z θ + Φg z θ) :=
      Work.FTS.NonlinRows.smoothOpen_add hstar.smooth hell.smooth
    have hTheta : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (1 / (4 * α)) * (Real.sin (2 * θ)
          * Work.Construction.L12 (Work.Construction.Ftot α w) z)) :=
      Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.GalFields.RHS.smoothOpen_sin_two) hL12tot)
    have hPsi_eq : Work.Construction.PhiTil α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)
        = fun z θ => (Φs z θ + Φg z θ)
          - (1 / (4 * α)) * (Real.sin (2 * θ)
            * Work.Construction.L12 (Work.Construction.Ftot α w) z) := by
      funext z θ
      simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
      ring
    have hPsi : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)) :=
      hPsi_eq ▸ (Work.FTS.NonlinRows.smoothOpen_sub hΦ hTheta)
    have hRop := Work.FTS.NonlinRows.smoothOpen_Rop (α := α) hPsi
    have hUop : Work.FTS.EllipticEst.SmoothOpen
        (Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ))) :=
      Work.FTS.EllipticEst.smoothOpen_Uop hPsi
    have hVop := Work.FTS.NonlinRows.smoothOpen_Vop hPsi
    have hF : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Ftot α w) :=
      Work.FTS.NonlinRows.smoothOpen_add
        (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hw.reg
    have hpthF := Work.FTS.EllipticEst.SmoothOpen.pth hF
    have hDzF := Work.FTS.EllipticEst.SmoothOpen.Dz hF
    have t1 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (2 * Work.Construction.Rop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
          * Work.Construction.Ftot α w z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hRop) hF
    have t2 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (2 * Work.Construction.Uop α (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul 2 hUop) hpthF
    have t3 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => ((2 * α) * Work.Construction.Vop (Work.Construction.PhiTil α
            (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ)
          * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_const_mul (2 * α) hVop) hDzF
    have t4 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (((1 / 2) * Real.sin (2 * θ)) * Work.Construction.FK
            (Work.Construction.Ftot α w) z)
          * Work.Spaces.pth (Work.Construction.Ftot α w) z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / 2)
            (Work.FTS.GalFields.RHS.smoothOpen_sin_two)) hFKtot) hpthF
    have t5 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z)
          * Work.Construction.Ftot α w z θ) :=
      Work.FTS.NonlinRows.smoothOpen_mul
        (Work.FTS.NonlinRows.smoothOpen_mul
          (Work.FTS.GalFields.RHS.smoothOpen_sin_sq) hFKtot) hF
    have hmain : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Construction.Ftot α w z θ
          - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
          - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
          - (1 / 2) * Real.sin (2 * θ) * Work.Construction.FK (Work.Construction.Ftot α w) z
            * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
          - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z
            * Work.Construction.Ftot α w z θ) :=
      Work.FTS.NonlinRows.smoothOpen_sub
        (Work.FTS.NonlinRows.smoothOpen_sub
          (Work.FTS.NonlinRows.smoothOpen_sub
            (Work.FTS.NonlinRows.smoothOpen_sub t1 t2) t3) t4) t5
    change Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => 2 * Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Construction.Ftot α w z θ
          - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
          - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α
              (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ)) z θ
            * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
          - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK
              (Work.Construction.Ftot α w) z
            * Work.Spaces.pth (Work.Construction.Ftot α w) z θ
          - Real.sin θ ^ 2 * Work.Construction.FK (Work.Construction.Ftot α w) z
            * Work.Construction.Ftot α w z θ)
    exact hmain
  exact ⟨hL12tot, hFKtot, hLG, hN0, hN⟩

end Work.FTS.StrongEps.ClassCRHS
