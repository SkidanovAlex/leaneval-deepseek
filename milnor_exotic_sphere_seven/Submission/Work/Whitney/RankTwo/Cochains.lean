import Mathlib
import Submission.Work.Whitney.RankTwo.Chain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-!
# The sign cochains

`posOf r` is `1` if `r > 0` and `0` otherwise.  On the singular simplicial set of
`X = tcmX Y 1 1` the two cochains `alpha0`, `beta0` are the signs of the first and second fibre
coordinates.  They are the lifts whose differentials represent the pulled-back rank-one model
classes, and they are the cochains on which both evaluations of `Work.Whitney.tcmProd_rankOne_one`
are computed.
-/

namespace Work.Whitney.RankTwo

open Work.Thom
open Work.Cohomology
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

set_option linter.unusedSectionVars false

noncomputable section

/-! ## Building cochains from their values on simplices -/

/-- **The cochain with prescribed values on the generators.** -/
noncomputable def cochainOf (Z : SSet) (n : ℕ) (g : Z _⦋n⦌ → ℤ) : Cochain ℤ Z n :=
  (Cofan.IsColimit.desc (Z.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ (g σ)))).hom

/-- The defining equation of `cochainOf` on generators. -/
theorem genEval_cochainOf (Z : SSet) (n : ℕ) (g : Z _⦋n⦌ → ℤ) (σ : Z _⦋n⦌) :
    genEval ℤ Z (cochainOf Z n g) σ = g σ := by
  have h := congrArg (fun (k : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) => k.hom (1 : ℤ))
    (Cofan.IsColimit.fac (Z.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
      (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ (g σ))) σ)
  simp only [cochainOf, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] at h
  exact h

/-! ## The sign function -/

/-- `posOf r` is `1` if `r > 0` and `0` otherwise. -/
def posOf (r : ℝ) : ℤ := if 0 < r then 1 else 0

theorem posOf_pos {r : ℝ} (h : 0 < r) : posOf r = 1 := if_pos h
theorem posOf_nonpos {r : ℝ} (h : ¬ 0 < r) : posOf r = 0 := if_neg h
theorem posOf_zero : posOf 0 = 0 := if_neg (lt_irrefl 0)

theorem posOf_eq_iff {r : ℝ} : posOf r = 1 ↔ 0 < r := by
  constructor
  · intro h
    by_contra hr
    rw [posOf_nonpos hr] at h
    exact one_ne_zero h.symm
  · exact posOf_pos

theorem posOf_ne_zero_iff {r : ℝ} : posOf r ≠ 0 ↔ 0 < r := by
  constructor
  · intro h
    by_contra hr
    exact h (posOf_nonpos hr)
  · intro h; rw [posOf_pos h]; exact one_ne_zero

/-! ## The two sign cochains on `X` -/

variable (Y : Type) [TopologicalSpace Y]

set_option linter.unusedSectionVars false in

/-- The first fibre coordinate of a point of `X`, in the coordinates of `tcmSumLin`. -/
def coordA (x : X Y) : ℝ := (tcmSumLin 1 1 x.2).ofLp 0

/-- The second fibre coordinate of a point of `X`, in the coordinates of `tcmSumLin`. -/
def coordB (x : X Y) : ℝ := (tcmSumLin 1 1 x.2).ofLp 1

theorem coordA_eq (x : X Y) : coordA Y x = (x.2.1).ofLp 0 :=
  tcmSumLin_apply_ofLp_zero x.2

theorem coordB_eq (x : X Y) : coordB Y x = (x.2.2).ofLp 0 :=
  tcmSumLin_apply_ofLp_one x.2

/-- The sign of the first fibre coordinate, as a `0`-cochain. -/
noncomputable def alpha0 : Cochain ℤ (ssX Y) 0 :=
  cochainOf (ssX Y) 0 (fun σ => posOf (coordA Y ((sEquiv Y 0) σ default)))

/-- The sign of the second fibre coordinate, as a `0`-cochain. -/
noncomputable def beta0 : Cochain ℤ (ssX Y) 0 :=
  cochainOf (ssX Y) 0 (fun σ => posOf (coordB Y ((sEquiv Y 0) σ default)))

@[simp] theorem genEval_alpha0 (σ : (ssX Y) _⦋0⦌) :
    genEval ℤ (ssX Y) (alpha0 Y) σ = posOf (coordA Y ((sEquiv Y 0) σ default)) :=
  genEval_cochainOf (ssX Y) 0 _ σ

@[simp] theorem genEval_beta0 (σ : (ssX Y) _⦋0⦌) :
    genEval ℤ (ssX Y) (beta0 Y) σ = posOf (coordB Y ((sEquiv Y 0) σ default)) :=
  genEval_cochainOf (ssX Y) 0 _ σ

/-- The differential of the sign cochain. -/
noncomputable def alpha : Cochain ℤ (ssX Y) 1 := cochainDiff ℤ (ssX Y) (alpha0 Y)

/-- The differential of the second sign cochain. -/
noncomputable def beta : Cochain ℤ (ssX Y) 1 := cochainDiff ℤ (ssX Y) (beta0 Y)

end

end Work.Whitney.RankTwo
