/-
# CORRECTION (session 21) — the refutation below is INVALID
Read `StrongEps/NOTES_session21.md` §2 first.  The claimed mechanism (`-2F_*/z → -4αΓ(θ)/c ≠ 0`)
is wrong on two counts: `UVR α F_* (Theta α F_*)` contains `-2F_*/(1+z)` (from
`Construction.UVR_sub` + `L12_Fstar_eq`), which cancels the `-2F_*` down to `O(αz²)`; and the
`Theta`-part of the `UVR` term is `O(αz)`, not `O(Csα²z)`.  The *machine-proved* computation is
`Work.FTS.StrongEps.EpsLocalPStar.MainLHS_zero_Fstar`
(`EpsLocalPStar/MainLHS_zero_Fstar.lean`): `MainLHS α 0 0 F_* = -8α²(Γ/c)c2m·z²/(1+z)⁴`, so the
model residual has NO `z`-linear part.  With `profRHS = -StatEqF` and `UVR_sub` one then gets
`profRHS α Φs E 0 z θ = -MainLHS α 0 0 F_* - 2αμ·AK - UVR α F_* Φt - ½s2·FK(F_*)·pthF_* -
sin²θ·FK(F_*)·F_*` (`Φt = PhiTil α F_* (Φs + E 0)`), in which every piece is flat at the axis
provided `SmoothOpen (PhiTil α F_* Φs)` and `PhiTil α F_* Φs (0,·) = 0` — the `StarCore.zeroOff`
data.  So at the zero profile `profRHS(0)/z → 0`, the `axis` clause is preserved, and `E2a`/`E4`
are NOT refuted by this mechanism; what remains open is the class-`C` invariance along the flow for
general class data (the `EpsEngine.profRHS_le_zsq_of_radial` route).  Do not cite this file as a
refutation.

# `StatResidual.lean` — the scheme's right-hand side is minus the stationary residual

**The identity** (`profRHS_eq_neg_dynLHS`):

  `profRHS α Φs E w z θ = -((1+μ)·F + (1+μ)(1+λ)·D_zF + UVR α F Φ)`,

where `F = Ftot α w = F_* + w`, `Φ = Φs + E w`, `μ = muDyn …`, `λ = lamDyn … = lamfun μ`.

Equivalently: `epsWP = dynLin + dynRHS = profRHS` is **minus the left-hand side of the
paper's stationary equation** `StatEqF α μ λ F Φ` (tex 1330).  The right-hand side of the
`ε`-scheme `∂_τ g = P₀ J_ε [𝓛+𝓡](P₀ J_ε g)` is therefore the *negative stationary residual*,
which is exactly what `Work.Construction.gEquationFinal` says (the `g`-equation `LGammaT g =
gRHS` is equivalent to `StatEqF`).

**Why it matters** (`Submission/Work/FTS/StrongEps/EpsLocalPStar/NOTES_EpsLocalPStar_FALSE.md`).
At `w = 0` the identity gives

  `profRHS α Φs E 0 z θ = -2·F_*(z,θ) + 2α(1-μ)·AK(z,θ) - UVR α F_* Φ(z,θ)`,

(stationarity of `F_*`: `F_* + D_zF_* = 2F_* - 2αAK`, `Fstar_sub_DzFstar`), and `-2F_*/z →
-4αΓ(θ)/c ≠ 0` while the other two terms are `O(α z²)` and `O(Csα²z)`.  Hence the flow of the
`ε`-scheme from *any* datum whose projected-mollified profile vanishes at `z = 0` immediately
leaves the class `C` (`axis` and `HkMem α 7` fail at `z = 0`), so `EpsRegP` — hence the target
`EpsLocalPStar` — is unachievable.  This is the formal core of that refutation.

The statement is stated with the side conditions that the (`rfl`-level) decompositions used by
`Work.Construction.MainLHS_explicit` / `Work.Stability.MainLHSSubN` supply: linearity of `D_z`,
`D_θ` and `L₁₂` (`hDz`, `hpth`, `hL`), the evaluation `L₁₂(F_*) = 2α/(1+z)` (`hLstar`), the
stationarity of `F_*` (`hstat`), the `Φ = Φ̃ + Θ` derivatives (`h2`, `h3`, `h5`, `h6`) and
`μ ≠ -1`.  All are available for `SmoothOpen` + `HkMem`-type profiles.  `hμ1` holds on the
class-`C` small ball by `MuLamOK`.

`#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.LinearCombination
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.Construction.Equation
import Submission.Work.Stability.MainLHSSubN
import Submission.Work.Construction.MufunS
import Submission.Work.Construction.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open Work.FTS.Galerkin (Fn Fam slice famOf)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The scheme's right-hand side is minus the stationary residual.**
`profRHS α Φs E w = -((1+μ)F + (1+μ)(1+lv)D_zF + UVR α F Φ)`, `F = F_* + w`,
`Φ = Φs + E w`, `μ = muDyn`, `lv = lamDyn = lamfun μ`. -/
theorem profRHS_eq_neg_dynLHS {α : ℝ} (hα : 0 < α) (Φs : Fn) (E : Fn → Fn) (w : Fn)
    (z θ : ℝ)
    (h1z : (1 : ℝ) + z ≠ 0) (hzm1 : -1 < z) (hcos : Real.cos θ ≠ 0)
    (hDz : Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz w z θ)
    (hpth : Work.Spaces.pth (Work.Construction.Ftot α w) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth w z θ)
    (hL : Work.Construction.L12 (Work.Construction.Ftot α w) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 w z)
    (hLstar : Work.Construction.L12 (Work.Construction.Fstar α) z = 2 * α / (1 + z))
    (hstat : Work.Construction.Fstar α z θ + Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      - 1 / α * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ = 0)
    (h2 : Work.Spaces.pz (fun z θ => Φs z θ + E w z θ) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
            (fun z θ => Φs z θ + E w z θ)) z θ
        + Work.Spaces.pz (Work.Construction.Theta α (Work.Construction.Ftot α w)) z θ)
    (h3 : Work.Spaces.pth (fun z θ => Φs z θ + E w z θ) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α w)
            (fun z θ => Φs z θ + E w z θ)) z θ
        + Work.Spaces.pth (Work.Construction.Theta α (Work.Construction.Ftot α w)) z θ)
    (h5 : z * Work.Spaces.pz (Work.Construction.Theta α (Work.Construction.Ftot α w)) z θ
      = -(1 / (4 * α)) * Work.Construction.s2 θ
        * Work.Construction.FK (Work.Construction.Ftot α w) z)
    (h6 : Work.Spaces.pth (Work.Construction.Theta α (Work.Construction.Ftot α w)) z θ
      = 1 / (2 * α) * Real.cos (2 * θ)
        * Work.Construction.L12 (Work.Construction.Ftot α w) z)
    (hμ1 : Work.FTS.Galerkin.muDyn α
        (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) (famOf (fun _ => w)) 0 ≠ -1) :
    profRHS α Φs E w z θ
      = -((1 + Work.FTS.Galerkin.muDyn α
              (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) (famOf (fun _ => w)) 0)
            * Work.Construction.Ftot α w z θ
          + (1 + Work.FTS.Galerkin.muDyn α
              (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) (famOf (fun _ => w)) 0)
            * (1 + Work.FTS.Galerkin.lamDyn α
              (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) (famOf (fun _ => w)) 0)
            * Work.Spaces.Dz (Work.Construction.Ftot α w) z θ
          + Work.Construction.UVR α (Work.Construction.Ftot α w)
              (fun z θ => Φs z θ + E w z θ) z θ) := by
  classical
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftot α w with hF
  set Φ : ℝ → ℝ → ℝ := fun z θ => Φs z θ + E w z θ with hΦ
  set μ : ℝ := Work.FTS.Galerkin.muDyn α
    (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) (famOf (fun _ => w)) 0 with hμ
  set lv : ℝ := Work.FTS.Galerkin.lamDyn α
    (Work.FTS.Nonlin.PsiCan Φs E (famOf (fun _ => w))) (famOf (fun _ => w)) 0 with hlv
  have hlveq : lv = Work.Construction.lamfun μ := by rw [hlv, hμ]; rfl
  have hμ1' : (1 : ℝ) + μ ≠ 0 := fun h => hμ1 (by rw [hμ]; linarith)
  have hlam1 : μ + lv + μ * lv = -μ := by
    rw [hlveq, Work.Construction.lamfun]
    field_simp
    ring
  -- the definitional shape of `profRHS`
  have hW : profRHS α Φs E w z θ
      = -(Work.Coercivity.LGammaT α w z θ)
        + Work.Construction.gRHS α μ lv F Φ w z θ := by
    simp only [profRHS, Work.FTS.StrongPersist.linPart, Work.FTS.StrongPersist.rhsOf,
      hF, hΦ, ← hμ, ← hlv]
  -- the two structural inputs
  have hT_eq := Work.Construction.LGammaT_eq α w z θ
  have hsplit : Φ z θ = Work.Construction.PhiTil α F Φ z θ
      + Work.Construction.Theta α F z θ := by
    simp only [Work.Construction.PhiTil]; ring
  have hsub := Work.Stability.MainLHSSubN (α := α) (μ := μ) (lam := lv) hα (F := F) (Φ := Φ) z θ
    hcos hsplit h2 h3 h5 h6
  have hexp := Work.Construction.MainLHS_explicit (α := α) (μ := μ) (lam := lv) hα
    (F := F) (g := w) z θ h1z rfl hDz hpth hL hLstar hstat
  have h2αμ := Work.Construction.two_mul_mufunS α (Work.Construction.N0 α F w)
    (Work.Construction.N α F Φ) w hα.ne'
  have hsubstar : Work.Construction.Fstar α z θ - Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = 2 * α * Work.Construction.AK α z θ := Work.Construction.Fstar_sub_DzFstar hα hzm1
  -- the assembly
  simp only [Work.Construction.gRHS, Work.Construction.Nstar] at hW
  rw [hT_eq] at hW
  -- all the pieces are now equations between the same scalars
  have hTp : 3 / (2 * α) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.pth w z θ
      = Work.Coercivity.Transport w z θ := by
    rw [Work.Construction.Transport_eq, hLstar]
    field_simp
  have key : Work.Coercivity.LGamma α w z θ - Work.Coercivity.Transport w z θ
      = Work.Construction.MainLHS α μ lv F z θ - μ * Work.Construction.Fstar α z θ
        - (μ + lv + μ * lv) * Work.Spaces.Dz (Work.Construction.Fstar α) z θ
        - μ * w z θ - (μ + lv + μ * lv) * Work.Spaces.Dz w z θ
        + Work.Construction.N0 α F w z θ := by linarith [hexp, hTp]
  rw [key] at hW
  have hN : Work.Construction.N α F Φ z θ
      = Work.Construction.MainLHS α μ lv F z θ
        - ((1 + μ) * F z θ + (1 + μ) * (1 + lv) * Work.Spaces.Dz F z θ
          + Work.Construction.UVR α F Φ z θ) := by linarith [hsub]
  rw [hN] at hW
  have harg : μ * (Work.Construction.Fstar α z θ - Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      = 2 * α * μ * Work.Construction.AK α z θ := by rw [hsubstar]; ring
  rw [hlam1] at hW
  have hμS : μ = Work.Construction.mufunS α (Work.Construction.N0 α F w)
      (Work.Construction.N α F Φ) w := by
    rw [hμ]; rfl
  have hsplit2 : Work.Construction.mubar (Work.Construction.N0 α F w) (Work.Construction.N α F Φ)
      = 2 * α * μ - Work.Construction.L12 (Work.Coercivity.Transport w) 0 := by
    rw [← hμS] at h2αμ
    linarith [h2αμ]
  rw [hsplit2] at hW
  rw [hW]
  ring_nf
  have harg3 : μ * Work.Construction.AK α z θ * α * 2
      = μ * (Work.Construction.Fstar α z θ - Work.Spaces.Dz (Work.Construction.Fstar α) z θ) := by
    linear_combination -harg
  rw [harg3]
  ring

end Work.FTS.StrongEps.EpsLocalPStar
