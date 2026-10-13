import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS_MuLipC.LinQuad
import Submission.Work.FTS_MuLipC.Poly0.n0_poly
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology

namespace Work.FTS_MuLipC.Poly1

open Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Locality of `∂_z`, `∂_θ` and of `ℛ`, `𝒰`, `𝒱` on the open quadrant

All the identities below hold on the open quadrant `Q0 = {z > 0, 0 < θ < π/2}`; the operators
`ℛ`, `𝒰`, `𝒱` are built from the *pointwise* data `Ψ(z,θ)`, `∂_zΨ(z,θ)`, `∂_θΨ(z,θ)`, so two
stream profiles that agree on the open quadrant (which is an open neighbourhood of every
interior point) produce the same value of the operator there.  This is what lets the split
`Φ̃_{F_*+u} = Φ̃_{F_*} + U_u` (which is only available at `z > 0`, where `L₁₂` is additive) be
transported through `ℛ`, `𝒰`, `𝒱`. -/

theorem pz_congr_Q0 {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Work.FTS.EllipticEst.Q0 :=
    (Continuous.prodMk_left θ).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) :=
    hnb.mono fun z' hz' => h z' θ hz'.1 hz'.2.1 hz'.2.2
  simpa only [Work.Spaces.pz] using hev.deriv_eq

theorem pth_congr_Q0 {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
    (Continuous.prodMk_right z).continuousAt.eventually
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hzθ)
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') :=
    hnb.mono fun θ' hθ' => h z θ' hθ'.1 hθ'.2.1 hθ'.2.2
  simpa only [Work.Spaces.pth] using hev.deriv_eq

/-- `ℛ` depends on `Ψ` only through the open quadrant. -/
theorem Rop_congr_Q0 {α : ℝ} {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Construction.Rop α f z θ = Work.Construction.Rop α g z θ := by
  have hpz := pz_congr_Q0 hz hθ h
  have hpth := pth_congr_Q0 hz hθ h
  simp only [Work.Construction.Rop, hpz, hpth, h z θ hz hθ.1 hθ.2]

/-- `𝒰` depends on `Ψ` only through the open quadrant. -/
theorem Uop_congr_Q0 {α : ℝ} {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Construction.Uop α f z θ = Work.Construction.Uop α g z θ := by
  have hpz := pz_congr_Q0 hz hθ h
  simp only [Work.Construction.Uop, hpz, h z θ hz hθ.1 hθ.2]

/-- `𝒱` depends on `Ψ` only through the open quadrant. -/
theorem Vop_congr_Q0 {f g : Fn} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.Construction.Vop f z θ = Work.Construction.Vop g z θ := by
  have hpth := pth_congr_Q0 hz hθ h
  simp only [Work.Construction.Vop, hpth, h z θ hz hθ.1 hθ.2]

/-! ## Smoothness of the perturbative stream function and additivity of `FK` -/

/-- `U_g = PhiTil α g (E g)`: the perturbative stream function is the elliptic residual of `g`. -/
theorem Ug_eq_PhiTil (α : ℝ) (E : Fn → Fn) (g : Fn) :
    Ug α E g = Work.Construction.PhiTil α g (E g) := rfl

/-- `U_g` is `C^∞` on the open quadrant, from the elliptic package of the pair `(g, E g)`. -/
theorem smoothOpen_Ug {α Ce : ℝ} (hα : 0 < α) {E : Fn → Fn} {g : Fn}
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g (E g)) :
    Work.FTS.EllipticEst.SmoothOpen (Ug α E g) :=
  Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hell

/-- **Additivity of the angular moment `FK` on two honest profiles.** -/
theorem FK_add_of_SmoothOpen_HkMem {α : ℝ} {a b : Fn}
    (ha : Work.FTS.EllipticEst.SmoothOpen a) (hb : Work.FTS.EllipticEst.SmoothOpen b)
    (hma : Work.Spaces.HkMem α 4 a) (hmb : Work.Spaces.HkMem α 4 b)
    {z : ℝ} (hz : 0 < z) :
    Work.Construction.FK (fun z θ => a z θ + b z θ) z
      = Work.Construction.FK a z + Work.Construction.FK b z :=
  Work.FTS.GalFields.RHS.FK_add_of_slices (ne_of_gt hz)
    (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem ha hma hz)
    (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hb hmb hz)

/-- **The `N` polynomial structure on the class `C`**: with `E` additive and `ℝ`-homogeneous
(a linear map in the application), the bilinear block satisfies
`Sn α Φs E g = C1 α Φs + Lin1 α Φs E g + Quad1 α E g` on the open quadrant, together with the
two polarization identities `Lin1 α Φs E (u+d) = Lin1 α Φs E u + Lin1 α Φs E d` and
`Quad1 α E (u+d) = Quad1 α E u + Bil1 α E u d + Bil1 α E d u + Quad1 α E d`.
The definitions are in `Submission/Work/FTS_MuLipC/LinQuad.lean`.  Ingredients: the profile-level
additivities `L₁₂(F_*+g) = L₁₂F_* + L₁₂g` (`Work.FTS.Nonlinear.Pieces.L12FK_add_ge0`, and for the
`u+d` conjuncts `Work.FTS.GalBasis.cc.L12_add_of_HkMem` / `Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0`)
and `FK(F_*+g) = FK F_* + FK g` (`Work.FTS_MuLamOK.Rows.Rl1Defs.FKaddOpen`,
`Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal.FK_add_of_slices`); the additivity of
`Rop`/`Uop`/`Vop` in their field argument (`Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0`,
`Uop_add_Q0`, `Vop_add_Q0`, available from `Work.FTS.OpenPkg.smoothOpen_PhiTil_star` and
`Work.FTS.GalFields.RHS.smoothOpen_N_Ftot.smoothOpen_PhiTil`); that of `pth`/`Dz` on the sum
(`Work.FTS.NonlinRows.Rl1.openSlice_pth_add`, `openSlice_pz_add`,
`Work.FTS.Nonlinear.Pieces.Dz_add_of_diff`); and `E (u+d) = Eu + Ed` for the linearity of
`U_g = E(·) − (1/(4α))·sin(2θ)·L₁₂(·)`. -/
theorem n_poly {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {u d : Work.FTS.Galerkin.Fn}
    (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d)
    (hEadd : ∀ a b : Work.FTS.Galerkin.Fn, E (a + b) = E a + E b)
    (hEsmul : ∀ (c : ℝ) (a : Work.FTS.Galerkin.Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f)) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Sn α Φs E u z θ
        = (Work.FTS_MuLipC.C1 α Φs + Work.FTS_MuLipC.Lin1 α Φs E u
            + Work.FTS_MuLipC.Quad1 α E u) z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Lin1 α Φs E (fun z' θ' => u z' θ' + d z' θ') z θ
        = (Work.FTS_MuLipC.Lin1 α Φs E u + Work.FTS_MuLipC.Lin1 α Φs E d) z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Quad1 α E (fun z' θ' => u z' θ' + d z' θ') z θ
        = (Work.FTS_MuLipC.Quad1 α E u + Work.FTS_MuLipC.Bil1 α E u d
            + Work.FTS_MuLipC.Bil1 α E d u + Work.FTS_MuLipC.Quad1 α E d) z θ) := by
  have huS : Work.FTS.EllipticEst.SmoothOpen u := hu.reg
  have hdS : Work.FTS.EllipticEst.SmoothOpen d := hd.reg
  have hu4 : Work.Spaces.HkMem α 4 u := Work.FTS.ClassC.classC_hkMem_four hu
  have hd4 : Work.Spaces.HkMem α 4 d := Work.FTS.ClassC.classC_hkMem_four hd
  have hFs : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  -- smoothness of the (constant and perturbative) stream functions
  have hZs : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil_star hα hα1 hstar
  have hUgu : Work.FTS.EllipticEst.SmoothOpen (Ug α E u) := smoothOpen_Ug hα (hell u hu)
  have hUgd : Work.FTS.EllipticEst.SmoothOpen (Ug α E d) := smoothOpen_Ug hα (hell d hd)
  -- `L₁₂` additivity on `F_* + u` resp. on `u + d`
  have hLu : ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (Work.Construction.Ftot α u) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z
          + Work.Construction.L12 u z :=
    fun z hz => (Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 huS hu4).1 z hz
  have hLud : ∀ z : ℝ, 0 ≤ z →
      Work.Construction.L12 (fun z θ => u z θ + d z θ) z
        = Work.Construction.L12 u z + Work.Construction.L12 d z :=
    Work.FTS_MuLipC.Poly0.L12_add_of_SmoothOpen_HkMem huS hdS hu4 hd4
  -- additivity of `E` in the eta-expanded form of the statement
  have hEadd' : ∀ a b : Fn, E (fun z θ => a z θ + b z θ) = E a + E b := by
    intro a b
    rw [show (fun z θ => a z θ + b z θ) = (a + b : Fn) from by funext z θ; rfl]
    exact hEadd a b
  refine ⟨?_, ?_, ?_⟩
  · -- ### the polynomial identity for `Sn`
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    -- the perturbative potential splits into the star part and `U_u`
    have hZgpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Construction.PhiTil α (Work.Construction.Ftot α u)
            (fun z θ => Φs z θ + E u z θ) z θ
          = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
            + Ug α E u z θ := by
      intro z θ hz h1 h2
      have hL := hLu z hz.le
      simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.FTS_MuLipC.Ug,
        Work.Construction.s2]
      rw [hL]
      ring
    have hRop := (Rop_congr_Q0 (α := α) (f := Work.Construction.PhiTil α (Work.Construction.Ftot α u)
          (fun z θ => Φs z θ + E u z θ))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Ug α E u z θ) hz hθ hZgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 (α := α)
        (f := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        (g := Ug α E u) hZs hUgu z θ hz hθ0 hθ1)
    have hUop := (Uop_congr_Q0 (α := α) (f := Work.Construction.PhiTil α (Work.Construction.Ftot α u)
          (fun z θ => Φs z θ + E u z θ))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Ug α E u z θ) hz hθ hZgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 (α := α)
        (f := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        (g := Ug α E u) hZs hUgu z θ hz hθ0 hθ1)
    have hVop := (Vop_congr_Q0 (f := Work.Construction.PhiTil α (Work.Construction.Ftot α u)
          (fun z θ => Φs z θ + E u z θ))
        (g := fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Ug α E u z θ) hz hθ hZgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0
        (f := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        (g := Ug α E u) hZs hUgu z θ hz hθ0 hθ1)
    have hpth : Work.Spaces.pth (Work.Construction.Ftot α u) z θ
        = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth u z θ :=
      Work.FTS.NonlinRows.Rl1.openSlice_pth_add hFs huS hz hθ
    have hDz : Work.Spaces.Dz (Work.Construction.Ftot α u) z θ
        = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz u z θ :=
      Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
        (Work.FTS.NonlinRows.Rl1.openSlice_pz_add hFs huS hz hθ)
    have hFK : Work.Construction.FK (Work.Construction.Ftot α u) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK u z :=
      Work.FTS_MuLamOK.Rows.FKaddOpen hα huS hu4 z hz
    have hF : Work.Construction.Ftot α u z θ
        = Work.Construction.Fstar α z θ + u z θ := rfl
    simp only [Work.FTS_MuLipC.Sn_apply, Work.Construction.N, Work.FTS_MuLipC.C1,
      Work.FTS_MuLipC.Lin1, Work.FTS_MuLipC.Quad1, Pi.add_apply]
    rw [hRop, hUop, hVop, hpth, hDz, hFK, hF]
    ring
  · -- ### `Lin1` is additive in the profile
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    have hUgpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Ug α E (fun z' θ' => u z' θ' + d z' θ') z θ
          = (fun z θ => Ug α E u z θ + Ug α E d z θ) z θ := by
      intro z θ hz h1 h2
      have hL := hLud z hz.le
      have hE := hEadd' u d
      simp only [Work.FTS_MuLipC.Ug, Work.Construction.s2]
      rw [hE, hL]
      simp only [Pi.add_apply]
      ring
    have hRop := (Rop_congr_Q0 (α := α) (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 (α := α) (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hUop := (Uop_congr_Q0 (α := α) (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 (α := α) (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hVop := (Vop_congr_Q0 (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hpth : Work.Spaces.pth (fun z' θ' => u z' θ' + d z' θ') z θ
        = Work.Spaces.pth u z θ + Work.Spaces.pth d z θ :=
      Work.FTS.NonlinRows.Rl1.openSlice_pth_add huS hdS hz hθ
    have hDz : Work.Spaces.Dz (fun z' θ' => u z' θ' + d z' θ') z θ
        = Work.Spaces.Dz u z θ + Work.Spaces.Dz d z θ :=
      Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
        (Work.FTS.NonlinRows.Rl1.openSlice_pz_add huS hdS hz hθ)
    have hFK : Work.Construction.FK (fun z' θ' => u z' θ' + d z' θ') z
        = Work.Construction.FK u z + Work.Construction.FK d z :=
      FK_add_of_SmoothOpen_HkMem huS hdS hu4 hd4 hz
    simp only [Work.FTS_MuLipC.Lin1, Pi.add_apply]
    rw [hRop, hUop, hVop, hpth, hDz, hFK]
    ring
  · -- ### the polarization identity of the quadratic block
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
    have hUgpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        Ug α E (fun z' θ' => u z' θ' + d z' θ') z θ
          = (fun z θ => Ug α E u z θ + Ug α E d z θ) z θ := by
      intro z θ hz h1 h2
      have hL := hLud z hz.le
      have hE := hEadd' u d
      simp only [Work.FTS_MuLipC.Ug, Work.Construction.s2]
      rw [hE, hL]
      simp only [Pi.add_apply]
      ring
    have hRop := (Rop_congr_Q0 (α := α) (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Rop_add_Q0 (α := α) (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hUop := (Uop_congr_Q0 (α := α) (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Uop_add_Q0 (α := α) (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hVop := (Vop_congr_Q0 (f := Ug α E (fun z' θ' => u z' θ' + d z' θ'))
        (g := fun z θ => Ug α E u z θ + Ug α E d z θ) hz hθ hUgpt).trans
      (Work.FTS.GalFields.RHS.Sharp.Vop_add_Q0 (f := Ug α E u) (g := Ug α E d)
        hUgu hUgd z θ hz hθ0 hθ1)
    have hpth : Work.Spaces.pth (fun z' θ' => u z' θ' + d z' θ') z θ
        = Work.Spaces.pth u z θ + Work.Spaces.pth d z θ :=
      Work.FTS.NonlinRows.Rl1.openSlice_pth_add huS hdS hz hθ
    have hDz : Work.Spaces.Dz (fun z' θ' => u z' θ' + d z' θ') z θ
        = Work.Spaces.Dz u z θ + Work.Spaces.Dz d z θ :=
      Work.FTS.Nonlinear.Pieces.Dz_add_of_diff
        (Work.FTS.NonlinRows.Rl1.openSlice_pz_add huS hdS hz hθ)
    have hFK : Work.Construction.FK (fun z' θ' => u z' θ' + d z' θ') z
        = Work.Construction.FK u z + Work.Construction.FK d z :=
      FK_add_of_SmoothOpen_HkMem huS hdS hu4 hd4 hz
    simp only [Work.FTS_MuLipC.Quad1, Work.FTS_MuLipC.Bil1, Pi.add_apply]
    rw [hRop, hUop, hVop, hpth, hDz, hFK]
    ring

end Work.FTS_MuLipC.Poly1
