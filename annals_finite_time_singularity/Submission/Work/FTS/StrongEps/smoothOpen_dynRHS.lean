import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/StrongEps/smoothOpen_dynRHS.lean`

**Target.** `Work.FTS.StrongEps.smoothOpen_dynRHS`: the nonlinear right-hand side
`dynRHS α (PsiCan Φs E (JfamP ρ ε g)) (JfamP ρ ε g) τ` of the fake-time equation is `C^n` on
the open quadrant `Quad` for every `n`, given the corresponding regularity of its *atoms*:

* `F = Ftau α (JfamP ρ ε g) τ` and `g̃ = slice (JfamP ρ ε g) τ` are `C^n` on the quadrant (`hF`,
  `hg`);
* the radial functions `z ↦ L₁₂(F)(z)`, `z ↦ L₁₂(g̃)(z)` and `z ↦ (F,K)(z) = FK F z` are `C^n`
  on `(0,∞)` (`hL12F`, `hL12g`, `hFK`);
* the three transported coefficients
  `ℛ(Φ̃)`, `𝒰(Φ̃)`, `𝒱(Φ̃)` at `Φ̃ = PhiTil α F (slice (PsiCan Φs E (JfamP ρ ε g)) τ)` are `C^n`
  on the quadrant (`hR`, `hU`, `hV`).

Note `dynRHS = Construction.gRHS` evaluated at the two modulation constants `muDyn`, `lamDyn`,
which are *numbers* (integrals of the nonlinear blocks at `z = 0`): smoothness of `gRHS` is
therefore insensitive to them, and the only other ingredient is the fixed smooth datum
`AK α = (Γ(θ)/c α)·2z²/(1+z)³`, whose angular factor `Γ` is smooth on the open quadrant
(`AK_smoothO`).  The hypotheses `hPhi` (regularity of `Φ` itself) and the smoothness of the
Fourier/profile data `Φs`, `E`, `ρ`, `ε` are not used: `Φ` enters `N` only through `PhiTil`, and
`JfamP` enters only through its slice.

The proof decomposes the right-hand side into the blocks `N₀` (`smoothOpen_N0_gen`), `N`
(`smoothOpen_N_gen`), `N_*` (`smoothOpen_Nstar_of`), the fixed `AK α` and the constant
`-μ̄·AK`, and assembles the four with the closure of `SmoothOpen` under finite sums, products and
constant multiples.
-/

namespace Work.FTS.StrongEps

open Work.FTS.EllipticEst (SmoothOpen)

set_option linter.unusedVariables false

/-! ## The quadratic block `N₀` -/

/-- `N₀ α F g` is `C^∞` on the open quadrant as soon as the profile `F`, the perturbation `g` and
the radial function `z ↦ L₁₂(g)(z)` are.  (The datum `F_*` and its moment `L₁₂(F_*)` are fixed
smooth functions, supplied by the library.) -/
theorem smoothOpen_N0_gen {α : ℝ} {F g : ℝ → ℝ → ℝ}
    (hF : SmoothOpen F) (hg : SmoothOpen g)
    (hLg : SmoothOpen (fun z _ => Work.Construction.L12 g z)) :
    SmoothOpen (Work.Construction.N0 α F g) := by
  have hFs : SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hLFs : SmoothOpen (fun z _ => Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α
  have hs2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_s2
  have hc2m : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m
  have t1 : SmoothOpen (fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hLFs) hFs.pth
  have t2 : SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hc2m hLFs) hFs.Dz
  have t3 : SmoothOpen (fun z θ => (1 / α) * Work.Construction.L12 g z * g z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / α) hLg) hg
  have t4 : SmoothOpen (fun z θ => (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 g z * Work.Spaces.pth F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (3 / (2 * α)) hs2) hLg) hF.pth
  have t5 : SmoothOpen (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 g z
      * Work.Spaces.Dz F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hc2m hLg) hF.Dz
  have t6 : SmoothOpen (fun z θ => Work.Construction.c2m θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz g z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hc2m hLFs) hg.Dz
  have key : SmoothOpen (fun z θ =>
      (3 / (2 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        + (1 / α) * Work.Construction.L12 g z * g z θ
        + (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z
          * Work.Spaces.pth F z θ
        - Work.Construction.c2m θ * Work.Construction.L12 g z
          * Work.Spaces.Dz F z θ
        - Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz g z θ) :=
    ((((t1.sub t2).add t3).add t4).sub t5).sub t6
  refine ContDiffOn.congr
    (f₁ := Function.uncurry (fun z θ => Work.Construction.N0 α F g z θ)) key ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N0]

/-! ## The elliptic-correction block `N` -/

/-- `N α F (Φ)` is `C^∞` on the open quadrant as soon as the profile `F`, the angular moment
`z ↦ FK F z` and the three transported coefficients `ℛ(Φ̃)`, `𝒰(Φ̃)`, `𝒱(Φ̃)` of the residual
`Φ̃ = PhiTil α F Φ` are. -/
theorem smoothOpen_N_gen {α : ℝ} {F Φ : ℝ → ℝ → ℝ}
    (hF : SmoothOpen F)
    (hFK : SmoothOpen (fun z _ => Work.Construction.FK F z))
    (hR : SmoothOpen (Work.Construction.Rop α (Work.Construction.PhiTil α F Φ)))
    (hU : SmoothOpen (Work.Construction.Uop α (Work.Construction.PhiTil α F Φ)))
    (hV : SmoothOpen (Work.Construction.Vop (Work.Construction.PhiTil α F Φ))) :
    SmoothOpen (Work.Construction.N α F Φ) := by
  have hs2 : SmoothOpen (fun _ (θ : ℝ) => Work.Construction.s2 θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_sin_two
  have hsin : SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) :=
    Work.FTS.GalFields.RHS.smoothOpen_sin_sq
  have t1 : SmoothOpen (fun z θ => 2 * Work.Construction.Rop α
      (Work.Construction.PhiTil α F Φ) z θ * F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul 2 hR) hF
  have t2 : SmoothOpen (fun z θ => 2 * Work.Construction.Uop α
      (Work.Construction.PhiTil α F Φ) z θ * Work.Spaces.pth F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul 2 hU) hF.pth
  have t3 : SmoothOpen (fun z θ => 2 * α * Work.Construction.Vop
      (Work.Construction.PhiTil α F Φ) z θ * Work.Spaces.Dz F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (2 * α) hV) hF.Dz
  have t4 : SmoothOpen (fun z θ => (1 / 2) * Work.Construction.s2 θ
      * Work.Construction.FK F z * Work.Spaces.pth F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul (1 / 2) hs2) hFK) hF.pth
  have t5 : SmoothOpen (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hsin hFK) hF
  have key : SmoothOpen (fun z θ =>
      2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φ) z θ * F z θ
        - 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φ) z θ
          * Work.Spaces.pth F z θ
        - 2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φ) z θ
          * Work.Spaces.Dz F z θ
        - (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
          * Work.Spaces.pth F z θ
        - Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ) :=
    (((t1.sub t2).sub t3).sub t4).sub t5
  refine ContDiffOn.congr
    (f₁ := Function.uncurry (fun z θ => Work.Construction.N α F Φ z θ)) key ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.N]

/-! ## The full right-hand side -/

/-- `gRHS α μ lam F Φ g` is `C^∞` on the open quadrant under the regularity of the atoms.  This
is the general form of the smoothness of `dynRHS`; the modulation constants `μ`, `lam` are free
(numbers). -/
theorem smoothOpen_gRHS_gen {α μ lam : ℝ} {F Φ gg : ℝ → ℝ → ℝ}
    (hF : SmoothOpen F) (hg : SmoothOpen gg)
    (hLg : SmoothOpen (fun z _ => Work.Construction.L12 gg z))
    (hFK : SmoothOpen (fun z _ => Work.Construction.FK F z))
    (hR : SmoothOpen (Work.Construction.Rop α (Work.Construction.PhiTil α F Φ)))
    (hU : SmoothOpen (Work.Construction.Uop α (Work.Construction.PhiTil α F Φ)))
    (hV : SmoothOpen (Work.Construction.Vop (Work.Construction.PhiTil α F Φ))) :
    SmoothOpen (Work.Construction.gRHS α μ lam F Φ gg) := by
  have hAK : SmoothOpen (Work.Construction.AK α) := Work.FTS.StrongPersist.AK_smoothO α
  have hN0 : SmoothOpen (Work.Construction.N0 α F gg) := smoothOpen_N0_gen hF hg hLg
  have hN : SmoothOpen (Work.Construction.N α F Φ) := smoothOpen_N_gen hF hFK hR hU hV
  have hNs : SmoothOpen (Work.Construction.Nstar μ lam gg) :=
    Work.FTS.GalFields.RHS.smoothOpen_Nstar_of hg
  have h1 : SmoothOpen (fun z θ => -Work.Construction.mubar (Work.Construction.N0 α F gg)
      (Work.Construction.N α F Φ) * Work.Construction.AK α z θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul
      (-Work.Construction.mubar (Work.Construction.N0 α F gg) (Work.Construction.N α F Φ)) hAK
  have key : SmoothOpen (fun z θ =>
      -Work.Construction.mubar (Work.Construction.N0 α F gg) (Work.Construction.N α F Φ)
          * Work.Construction.AK α z θ
        + Work.Construction.N0 α F gg z θ + Work.Construction.N α F Φ z θ
        + Work.Construction.Nstar μ lam gg z θ) :=
    ((h1.add hN0).add hN).add hNs
  refine ContDiffOn.congr
    (f₁ := Function.uncurry (fun z θ => Work.Construction.gRHS α μ lam F Φ gg z θ)) key ?_
  intro p hp
  simp only [Function.uncurry, Work.Construction.gRHS]

/-! ## The target -/

theorem smoothOpen_dynRHS {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {τ : ℝ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ))
      Work.FTS.StrongEps.Quad)
    (hPhi : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.Galerkin.slice
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g)) τ))
      Work.FTS.StrongEps.Quad)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ))
      Work.FTS.StrongEps.Quad)
    (hL12F : ∀ n : ℕ, ContDiffOn ℝ n (Work.Construction.L12
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)) (Set.Ioi 0))
    (hL12g : ∀ n : ℕ, ContDiffOn ℝ n (Work.Construction.L12
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) (Set.Ioi 0))
    (hFK : ∀ n : ℕ, ContDiffOn ℝ n (Work.Construction.FK
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)) (Set.Ioi 0))
    (hR : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Construction.Rop α
      (Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ ε g)) τ)))) Work.FTS.StrongEps.Quad)
    (hU : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Construction.Uop α
      (Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ ε g)) τ)))) Work.FTS.StrongEps.Quad)
    (hV : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Construction.Vop
      (Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ ε g)) τ)))) Work.FTS.StrongEps.Quad) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.FTS.Galerkin.dynRHS α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) τ)) Work.FTS.StrongEps.Quad := by
  -- the atoms, in the `SmoothOpen` normal form
  have hFs : SmoothOpen (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hF
  have hgs : SmoothOpen (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hg
  have hLFs : SmoothOpen (fun z _ => Work.Construction.L12
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ) z) :=
    Work.FTS.NonlinRows.smoothOpen_radial hL12F
  have hLgs : SmoothOpen (fun z _ => Work.Construction.L12
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) z) :=
    Work.FTS.NonlinRows.smoothOpen_radial hL12g
  have hFKs : SmoothOpen (fun z _ => Work.Construction.FK
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ) z) :=
    Work.FTS.NonlinRows.smoothOpen_radial hFK
  have hRs : SmoothOpen (Work.Construction.Rop α
      (Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ ε g)) τ))) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hR
  have hUs : SmoothOpen (Work.Construction.Uop α
      (Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ ε g)) τ))) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hU
  have hVs : SmoothOpen (Work.Construction.Vop
      (Work.Construction.PhiTil α (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
          (Work.FTS.StrongEps.JfamP ρ ε g)) τ))) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hV
  have hmain : SmoothOpen (Work.Construction.gRHS α
      (Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
        (Work.FTS.StrongEps.JfamP ρ ε g) τ)
      (Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
        (Work.FTS.StrongEps.JfamP ρ ε g) τ)
      (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E
        (Work.FTS.StrongEps.JfamP ρ ε g)) τ)
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) τ)) :=
    smoothOpen_gRHS_gen hFs hgs hLgs hFKs hRs hUs hVs
  intro n
  exact (show SmoothOpen (Work.FTS.Galerkin.dynRHS α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) τ) from hmain).forall n

end Work.FTS.StrongEps
