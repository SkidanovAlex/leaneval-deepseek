/-
# `Submission/Work/FTS_MuLipC/RowN/SnPol.lean` — the polarization identity of the `N`-field

The field of the `N`-row is `Sn α Φs E g = N α (F_* + g) (Φ_s + E g)`
(`Work.FTS_MuLipC.Sn`).  `N` is a sum of products of two *affine* functions of the profile `g`
--- each of the twenty pieces of the split `Work.FTS.NonlinRows.Rl1.splitOpen` is a product
`c · X(g) · Y(g)` where `X`, `Y` are among the atoms `g`, `∂_θg`, `D_zg`, `FK g`,
`ℛ(Φ̃_g)`, `𝒰(Φ̃_g)`, `𝒱(Φ̃_g)` and the constants `F_*`, `∂_θF_*`, `D_zF_*`, `FK F_*`,
`ℛ(Φ̃_*)`, `𝒰(Φ̃_*)`, `𝒱(Φ̃_*)`.

Hence `g ↦ Sn α Φs E g` is a *polynomial of degree ≤ 2* in the profile,

  `Sn α Φs E g = C1 α Φs + Lin1 α Φs E g + Quad1 α E g`   (`C1`, `Lin1`, `Quad1` of
  `Submission/Work/FTS_MuLipC/LinQuad.lean`, proved in `Poly1.n_poly`),

with `Lin1` linear and `Quad1` homogeneous quadratic in `g`.  The present file records the
consequences of that structure that the difference row `DiffRow1` needs:

`Sn f − Sn f' = (1/(4t)) • (Sn (f+f'+t(f−f')) − Sn (f+f'−t(f−f')) + Sn (t(f−f')) − Sn (−(t(f−f'))))`

(the **polarization identity**), valid pointwise on the open quadrant `{z > 0, 0 < θ < π/2}`,
for every `t ≠ 0` and every pair of `ClassC` profiles.

## The route

Write `u := f + f'`, `d := f − f'`.  The four arguments on the right are
`(1±t)·f + (1∓t)·f'`, `t·f + (−t)·f'`, `(−t)·f + t·f'`, so it suffices to know the value of the
polynomial at a *general* linear combination `s • u + e • d` of two `ClassC` profiles:

  `Sn(s•u + e•d) = C1 + s·Lin1 u + e·Lin1 d + s²·Quad1 u + s·e·(Bil1 u d + Bil1 d u) + e²·Quad1 d`

(`Sn_comb` below), which follows from `Poly1.n_poly` (the three conjuncts: the polynomial
identity, the additivity of `Lin1` and the polarization of `Quad1`) together with the
homogeneity of `Lin1`, `Quad1` and `Bil1` in a *constant* (`Lin1_lin`, `Quad1_lin`), which in
turn rests on the homogeneity of the five primitive slots.  Those homogeneity lemmas are pure
pointwise algebra: every atom is an explicit expression in `g z θ`, `∂_zg`, `∂_θg`,
`(F_*,K) g` and `E g`, and `∂_z`, `∂_θ`, the angular moment `FK`, the integral operator `L₁₂`
and the three operators `ℛ`, `𝒰`, `𝒱` commute with a constant factor *unconditionally* (the
classical `deriv` of a constant multiple); see `pz_csmul`, `pth_csmul`, `Dz_csmul`, `FK_csmul`,
`Rop_csmul`, `Uop_csmul`, `Vop_csmul`, `Ug_csmul_fun`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_MuLipC.RowN.Defs
import Submission.Work.FTS_MuLipC.Poly1.n_poly
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.EllipticEst.ScaleAPI
import Submission.Work.FTS.GalLimit.GalWeak.bslOp_galPsi
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Homogeneity in a constant

The primitive slots (`∂_z`, `∂_θ`, the angular moment `FK`, and the three operators `ℛ`, `𝒰`,
`𝒱` built from them) commute with multiplication by a constant.  All of them are
unconditional: `deriv_const_mul_field` has no differentiability hypothesis, and the angular
moment is an integral. -/

/-- `∂_z` commutes with multiplication by a constant. -/
theorem pz_csmul (c : ℝ) (f : Fn) (z θ : ℝ) :
    Work.Spaces.pz (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.pz f z θ :=
  Work.FTS.GalLimit.GalWeak.pz_const_mul c f z θ

/-- `∂_θ` commutes with multiplication by a constant. -/
theorem pth_csmul (c : ℝ) (f : Fn) (z θ : ℝ) :
    Work.Spaces.pth (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.pth f z θ :=
  Work.FTS.GalLimit.GalWeak.pth_const_mul c f z θ

/-- `D_z = z ∂_z` commutes with multiplication by a constant. -/
theorem Dz_csmul (c : ℝ) (f : Fn) (z θ : ℝ) :
    Work.Spaces.Dz (fun z' θ' => c * f z' θ') z θ = c * Work.Spaces.Dz f z θ :=
  congrFun (congrFun (Work.FTS.EllipticEst.Dz_smul c f) z) θ

/-- The angular moment `FK` is homogeneous. -/
theorem FK_csmul (c : ℝ) (f : Fn) (z : ℝ) :
    Work.Construction.FK (fun z θ => c * f z θ) z = c * Work.Construction.FK f z := by
  simp only [Work.Construction.FK]
  rw [show (fun θ => (c * f z θ) * Work.Spaces.K θ)
      = (fun θ => c * (f z θ * Work.Spaces.K θ)) from by funext θ; ring]
  rw [MeasureTheory.integral_const_mul]

/-- `ℛ` is homogeneous. -/
theorem Rop_csmul (α c : ℝ) (Ψ : Fn) (z θ : ℝ) :
    Work.Construction.Rop α (fun z' θ' => c * Ψ z' θ') z θ
      = c * Work.Construction.Rop α Ψ z θ := by
  simp only [Work.Construction.Rop, pz_csmul, pth_csmul]
  ring

/-- `𝒰` is homogeneous. -/
theorem Uop_csmul (α c : ℝ) (Ψ : Fn) (z θ : ℝ) :
    Work.Construction.Uop α (fun z' θ' => c * Ψ z' θ') z θ
      = c * Work.Construction.Uop α Ψ z θ := by
  simp only [Work.Construction.Uop, pz_csmul]
  ring

/-- `𝒱` is homogeneous. -/
theorem Vop_csmul (c : ℝ) (Ψ : Fn) (z θ : ℝ) :
    Work.Construction.Vop (fun z' θ' => c * Ψ z' θ') z θ
      = c * Work.Construction.Vop Ψ z θ := by
  simp only [Work.Construction.Vop, pth_csmul]
  ring

/-- The perturbative stream function `U_g = E g − (1/(4α))·sin 2θ·L₁₂(g)` is homogeneous in the
profile (this is where the `ℝ`-homogeneity of `E` and the homogeneity of `L₁₂` enter). -/
theorem Ug_csmul_fun {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) :
    Ug α E (fun z' θ' => c * g z' θ') = fun z θ => c * Ug α E g z θ := by
  funext z θ
  have hE : E (fun z' θ' => c * g z' θ') z θ = c * E g z θ :=
    congrFun (congrFun (hEsmul c g) z) θ
  have hL := Work.FTS.GalBasis.L12_const_mul c g z
  simp only [Ug, hE, hL]
  ring

/-! ## Homogeneity of the graded pieces of `Sn` -/

/-- `Lin1` is homogeneous in the profile. -/
theorem Lin1_csmul {α : ℝ} (Φs : Fn) (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) (z θ : ℝ) :
    Lin1 α Φs E (fun z' θ' => c * g z' θ') z θ = c * Lin1 α Φs E g z θ := by
  have hUg := Ug_csmul_fun (α := α) E hEsmul c g
  have hR : Work.Construction.Rop α (Ug α E (fun z' θ' => c * g z' θ')) z θ
      = c * Work.Construction.Rop α (Ug α E g) z θ := by
    rw [hUg]; exact Rop_csmul α c (Ug α E g) z θ
  have hU : Work.Construction.Uop α (Ug α E (fun z' θ' => c * g z' θ')) z θ
      = c * Work.Construction.Uop α (Ug α E g) z θ := by
    rw [hUg]; exact Uop_csmul α c (Ug α E g) z θ
  have hV : Work.Construction.Vop (Ug α E (fun z' θ' => c * g z' θ')) z θ
      = c * Work.Construction.Vop (Ug α E g) z θ := by
    rw [hUg]; exact Vop_csmul c (Ug α E g) z θ
  have hfk := FK_csmul c g z
  have hpt := pth_csmul c g z θ
  have hDz := Dz_csmul c g z θ
  simp only [Lin1, hR, hU, hV, hfk, hpt, hDz]
  ring

/-- `Bil1` is homogeneous in its **first** argument. -/
theorem Bil1_csmul_left {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (u d : Fn) (z θ : ℝ) :
    Bil1 α E (fun z' θ' => c * u z' θ') d z θ = c * Bil1 α E u d z θ := by
  have hUg := Ug_csmul_fun (α := α) E hEsmul c u
  have hR : Work.Construction.Rop α (Ug α E (fun z' θ' => c * u z' θ')) z θ
      = c * Work.Construction.Rop α (Ug α E u) z θ := by
    rw [hUg]; exact Rop_csmul α c (Ug α E u) z θ
  have hU : Work.Construction.Uop α (Ug α E (fun z' θ' => c * u z' θ')) z θ
      = c * Work.Construction.Uop α (Ug α E u) z θ := by
    rw [hUg]; exact Uop_csmul α c (Ug α E u) z θ
  have hV : Work.Construction.Vop (Ug α E (fun z' θ' => c * u z' θ')) z θ
      = c * Work.Construction.Vop (Ug α E u) z θ := by
    rw [hUg]; exact Vop_csmul c (Ug α E u) z θ
  have hfk := FK_csmul c u z
  simp only [Bil1, hR, hU, hV, hfk]
  ring

/-- `Bil1` is homogeneous in its **second** argument (pure pointwise algebra: the second
argument occurs only through `d`, `∂_θd`, `D_zd`). -/
theorem Bil1_csmul_right {α : ℝ} (E : Fn → Fn) (u : Fn) (c : ℝ) (d : Fn) (z θ : ℝ) :
    Bil1 α E u (fun z' θ' => c * d z' θ') z θ = c * Bil1 α E u d z θ := by
  have hpt := pth_csmul c d z θ
  have hDz := Dz_csmul c d z θ
  simp only [Bil1, hpt, hDz]
  ring

/-- `Quad1` is homogeneous of degree two. -/
theorem Quad1_csmul {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) (z θ : ℝ) :
    Quad1 α E (fun z' θ' => c * g z' θ') z θ = c ^ 2 * Quad1 α E g z θ := by
  have hQ : Quad1 α E (fun z' θ' => c * g z' θ') z θ
      = Bil1 α E (fun z' θ' => c * g z' θ') (fun z' θ' => c * g z' θ') z θ := rfl
  have hQ' : Quad1 α E g z θ = Bil1 α E g g z θ := rfl
  rw [hQ, hQ', Bil1_csmul_left E hEsmul c g (fun z' θ' => c * g z' θ') z θ,
    Bil1_csmul_right E g c g z θ]
  ring

/-! ## Function-level forms -/

/-- Function-level homogeneity of `Lin1`. -/
theorem Lin1_smul {α : ℝ} (Φs : Fn) (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) :
    Lin1 α Φs E (c • g) = fun z θ => c * Lin1 α Φs E g z θ := by
  funext z θ; exact Lin1_csmul Φs E hEsmul c g z θ

/-- Function-level homogeneity of `Quad1`. -/
theorem Quad1_smul {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (g : Fn) :
    Quad1 α E (c • g) = fun z θ => c ^ 2 * Quad1 α E g z θ := by
  funext z θ; exact Quad1_csmul E hEsmul c g z θ

/-- Function-level homogeneity of `Bil1` in its first argument. -/
theorem Bil1_smul_left {α : ℝ} (E : Fn → Fn)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a) (c : ℝ) (u d : Fn) :
    Bil1 α E (c • u) d = fun z θ => c * Bil1 α E u d z θ := by
  funext z θ; exact Bil1_csmul_left E hEsmul c u d z θ

/-- Function-level homogeneity of `Bil1` in its second argument. -/
theorem Bil1_smul_right {α : ℝ} (E : Fn → Fn) (u : Fn) (c : ℝ) (d : Fn) :
    Bil1 α E u (c • d) = fun z θ => c * Bil1 α E u d z θ := by
  funext z θ; exact Bil1_csmul_right E u c d z θ

/-! ## The graded pieces at a general linear combination -/

/-- `Lin1` is linear: `Lin1 (s•u + e•d) = s·Lin1 u + e·Lin1 d` on the open quadrant. -/
theorem Lin1_lin {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Fn} {E : Fn → Fn}
    (hEadd : ∀ a b : Fn, E (a + b) = E a + E b)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {u d : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d)
    (s e : ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Lin1 α Φs E (s • u + e • d) z θ = s * Lin1 α Φs E u z θ + e * Lin1 α Φs E d z θ := by
  intro z θ hz hθ0 hθ1
  have hsu : Work.FTS.ClassC.ClassC α (s • u) := Work.FTS.ClassC.classC_smul s hu
  have hed : Work.FTS.ClassC.ClassC α (e • d) := Work.FTS.ClassC.classC_smul e hd
  have hnp := (Work.FTS_MuLipC.Poly1.n_poly hα hα1 hsu hed hEadd hEsmul hstar hell).2.1
    z θ hz hθ0 hθ1
  rw [Lin1_smul Φs E hEsmul s u, Lin1_smul Φs E hEsmul e d] at hnp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hnp
  exact hnp

/-- `Quad1` is a quadratic form: at the linear combination `s•u + e•d`,
`Quad1 = s²·Quad1 u + s·e·(Bil1 u d + Bil1 d u) + e²·Quad1 d` on the open quadrant. -/
theorem Quad1_lin {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Fn} {E : Fn → Fn}
    (hEadd : ∀ a b : Fn, E (a + b) = E a + E b)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {u d : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d)
    (s e : ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Quad1 α E (s • u + e • d) z θ
        = s ^ 2 * Quad1 α E u z θ + s * e * (Bil1 α E u d z θ + Bil1 α E d u z θ)
          + e ^ 2 * Quad1 α E d z θ := by
  intro z θ hz hθ0 hθ1
  have hsu : Work.FTS.ClassC.ClassC α (s • u) := Work.FTS.ClassC.classC_smul s hu
  have hed : Work.FTS.ClassC.ClassC α (e • d) := Work.FTS.ClassC.classC_smul e hd
  have hnp := (Work.FTS_MuLipC.Poly1.n_poly hα hα1 hsu hed hEadd hEsmul hstar hell).2.2
    z θ hz hθ0 hθ1
  rw [Quad1_smul E hEsmul s u, Quad1_smul E hEsmul e d,
    Bil1_smul_left E hEsmul s u (e • d), Bil1_smul_right E u e d,
    Bil1_smul_left E hEsmul e d (s • u), Bil1_smul_right E d s u] at hnp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hnp
  ring_nf at hnp ⊢
  exact hnp

/-! ## The value of the field at a linear combination -/

/-- **The `N`-field at a linear combination of two `ClassC` profiles.**  Combining the three
conjuncts of `Poly1.n_poly` with `Lin1_lin` and `Quad1_lin`. -/
theorem Sn_comb {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs : Fn} {E : Fn → Fn}
    (hEadd : ∀ a b : Fn, E (a + b) = E a + E b)
    (hEsmul : ∀ (c : ℝ) (a : Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {u d : Fn} (hu : Work.FTS.ClassC.ClassC α u) (hd : Work.FTS.ClassC.ClassC α d)
    (s e : ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Sn α Φs E (s • u + e • d) z θ
        = C1 α Φs z θ + s * Lin1 α Φs E u z θ + e * Lin1 α Φs E d z θ
          + s ^ 2 * Quad1 α E u z θ
          + s * e * (Bil1 α E u d z θ + Bil1 α E d u z θ)
          + e ^ 2 * Quad1 α E d z θ := by
  intro z θ hz hθ0 hθ1
  have hsd : Work.FTS.ClassC.ClassC α (s • u + e • d) :=
    Work.FTS.ClassC.classC_add (Work.FTS.ClassC.classC_smul s hu)
      (Work.FTS.ClassC.classC_smul e hd)
  have h1 := (Work.FTS_MuLipC.Poly1.n_poly hα hα1 hsd (Work.FTS.ClassC.classC_zero α)
    hEadd hEsmul hstar hell).1 z θ hz hθ0 hθ1
  have h2 := Lin1_lin hα hα1 hEadd hEsmul hstar hell hu hd s e z θ hz hθ0 hθ1
  have h3 := Quad1_lin hα hα1 hEadd hEsmul hstar hell hu hd s e z θ hz hθ0 hθ1
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2, h3]
  ring

/-! ## The polarization identity -/

theorem SnPol {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hEadd : ∀ a b : Work.FTS.Galerkin.Fn, E (a - b) = E a - E b)
    (hEsmul : ∀ (c : ℝ) (a : Work.FTS.Galerkin.Fn), E (c • a) = c • E a)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f →
      Work.FTS.VocabO.EllPkgGo α Ce f (E f))
    {f f' : Work.FTS.Galerkin.Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hf' : Work.FTS.ClassC.ClassC α f') {t : ℝ} (ht : t ≠ 0) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS_MuLipC.Sn α Φs E f z θ - Work.FTS_MuLipC.Sn α Φs E f' z θ
        = (1 / (4 * t)) * (Work.FTS_MuLipC.Sn α Φs E (f + f' + t • (f - f')) z θ
            - Work.FTS_MuLipC.Sn α Φs E (f + f' - t • (f - f')) z θ
            + Work.FTS_MuLipC.Sn α Φs E (t • (f - f')) z θ
            - Work.FTS_MuLipC.Sn α Φs E (-(t • (f - f'))) z θ) := by
  -- the *subtractive* form of the linearity of `E` gives the additive one
  have hE0 : E 0 = 0 := by
    have h := hEadd 0 0
    rw [sub_self] at h
    simpa using h
  have hEneg : ∀ b : Fn, E (-b) = - E b := by
    intro b
    have h := hEadd 0 b
    rw [zero_sub, hE0] at h
    simpa using h
  have hEadd' : ∀ a b : Fn, E (a + b) = E a + E b := by
    intro a b
    have h := hEadd a (-b)
    rw [sub_neg_eq_add, hEneg] at h
    simpa using h
  intro z θ hz hθ0 hθ1
  -- the six values of the field, read off from `Sn_comb`
  have hF : Sn α Φs E f z θ
      = C1 α Φs z θ + Lin1 α Φs E f z θ + Quad1 α E f z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (1 : ℝ) 0 z θ hz hθ0 hθ1
    rw [show (1 : ℝ) • f + (0 : ℝ) • f' = f from by funext z θ; simp] at h
    simpa using h
  have hF' : Sn α Φs E f' z θ
      = C1 α Φs z θ + Lin1 α Φs E f' z θ + Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (0 : ℝ) 1 z θ hz hθ0 hθ1
    rw [show (0 : ℝ) • f + (1 : ℝ) • f' = f' from by funext z θ; simp] at h
    simpa using h
  have hP1 : Sn α Φs E (f + f' + t • (f - f')) z θ
      = C1 α Φs z θ + (1 + t) * Lin1 α Φs E f z θ + (1 - t) * Lin1 α Φs E f' z θ
        + (1 + t) ^ 2 * Quad1 α E f z θ
        + (1 + t) * (1 - t) * (Bil1 α E f f' z θ + Bil1 α E f' f z θ)
        + (1 - t) ^ 2 * Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (1 + t) (1 - t) z θ hz hθ0 hθ1
    rwa [show (1 + t) • f + (1 - t) • f' = f + f' + t • (f - f') from by
      funext z θ; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring] at h
  have hP2 : Sn α Φs E (f + f' - t • (f - f')) z θ
      = C1 α Φs z θ + (1 - t) * Lin1 α Φs E f z θ + (1 + t) * Lin1 α Φs E f' z θ
        + (1 - t) ^ 2 * Quad1 α E f z θ
        + (1 - t) * (1 + t) * (Bil1 α E f f' z θ + Bil1 α E f' f z θ)
        + (1 + t) ^ 2 * Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (1 - t) (1 + t) z θ hz hθ0 hθ1
    rwa [show (1 - t) • f + (1 + t) • f' = f + f' - t • (f - f') from by
      funext z θ; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring] at h
  have hP3 : Sn α Φs E (t • (f - f')) z θ
      = C1 α Φs z θ + t * Lin1 α Φs E f z θ + (-t) * Lin1 α Φs E f' z θ
        + t ^ 2 * Quad1 α E f z θ
        + t * (-t) * (Bil1 α E f f' z θ + Bil1 α E f' f z θ)
        + (-t) ^ 2 * Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' t (-t) z θ hz hθ0 hθ1
    rwa [show t • f + (-t) • f' = t • (f - f') from by
      funext z θ; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring] at h
  have hP4 : Sn α Φs E (-(t • (f - f'))) z θ
      = C1 α Φs z θ + (-t) * Lin1 α Φs E f z θ + t * Lin1 α Φs E f' z θ
        + (-t) ^ 2 * Quad1 α E f z θ
        + (-t) * t * (Bil1 α E f f' z θ + Bil1 α E f' f z θ)
        + t ^ 2 * Quad1 α E f' z θ := by
    have h := Sn_comb hα hα1 hEadd' hEsmul hstar hell hf hf' (-t) t z θ hz hθ0 hθ1
    rwa [show (-t) • f + t • f' = -(t • (f - f')) from by
      funext z θ
      simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring] at h
  rw [hF, hF', hP1, hP2, hP3, hP4]
  field_simp
  ring

end Work.FTS_MuLipC.RowN
