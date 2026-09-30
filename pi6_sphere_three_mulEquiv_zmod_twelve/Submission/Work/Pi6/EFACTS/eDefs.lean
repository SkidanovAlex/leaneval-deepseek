import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.EFACTS.FibreRing
import Submission.Work.Pi6.EFACTS.Coeff
import Submission.Work.Pi6.EFACTS.c3eq
import Submission.Work.Pi6.EFACTS.WangExact
import Submission.Work.Pi6.EFACTS.betaLow
import Submission.Work.Pi6.EFACTS.subH2
import Submission.Work.Pi6.EFACTS.h3zero
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Shared abbreviations and elementary lemmas for the cohomology of `E = S³⟨3⟩`

The Wang sequence of `proj g3 : E → SphModel 3` has fibre `F = fib g3`, a `K(ℤ,2)`-model through
degree `11`.  This file fixes the notation `Wθ` (the transgression `θ_n`), `Wθlow` (`θ_{-1}`),
`Wα` (the restriction `H^k(E) → H^k(F)`), `Wβ` (the connecting map `H^{n+1}(F) → H^{n+4}(E)`), the
powers `x2`, `y3`, `z4` of a degree-2 class `x`, and the elementary consequences of the exactness
spots and of the multiplicativity of `θ`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.EFACTS

noncomputable section

variable {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3))

/-- The Wang transgression `θ_n : H^{n+3}(F) → H^{n+1}(F)` of the cover. -/
abbrev Wθ (n : ℕ) : Coh ℤ (fib g3) (n + 3) →ₗ[ℤ] Coh ℤ (fib g3) (n + 1) :=
  Work.StemsB.wangTheta 3 (by norm_num) (proj g3) shellPt (hTG g3) (hTO g3) n

/-- The low Wang transgression `θ_{-1} : H²(F) → H⁰(F)`. -/
abbrev Wθlow : Coh ℤ (fib g3) 2 →ₗ[ℤ] Coh ℤ (fib g3) 0 :=
  wangThetaLow 3 (by norm_num) (Ecov g3) (proj g3) (isHurewiczFibration_proj g3) (hTO g3)
    shellPt (hTG g3)

/-- The restriction `α_k : H^k(E) → H^k(F)` of the Wang sequence. -/
abbrev Wα (k : ℕ) : Coh ℤ (Ecov g3) k ⟶ Coh ℤ (fib g3) k :=
  Work.StemsB.wangCohShiftαR ℤ (TopCat.of (Ecov g3)) (Work.StemsB.wangA 3 (proj g3))
    (Work.StemsB.wangCohFsp 3 (proj g3)) 3
    (Work.StemsB.wangGammaExplicit 3 (proj g3) (hTO g3)) k

/-- The connecting map `β_n : H^{n+1}(F) → H^{n+4}(E)` of the Wang sequence. -/
abbrev Wβ (n : ℕ) : Coh ℤ (fib g3) (n + 1) ⟶ Coh ℤ (Ecov g3) (n + 4) :=
  Work.StemsB.wangCohShiftβSR ℤ (TopCat.of (Ecov g3)) (Work.StemsB.wangA 3 (proj g3))
    (Work.StemsB.wangCohFsp 3 (proj g3)) 3
    (Work.StemsB.wangTauS 3 (by norm_num) (Ecov g3) (proj g3) (hTO g3) shellPt (hTG g3)) n

/-- The square `x ⌣ x` of a degree-2 class. -/
abbrev x2 (x : Coh ℤ (fib g3) 2) : Coh ℤ (fib g3) 4 := Work.StemsB.cupT (fib g3) 2 2 x x

/-- The cube `x ⌣ x ⌣ x` (right-nested) of a degree-2 class. -/
abbrev y3 (x : Coh ℤ (fib g3) 2) : Coh ℤ (fib g3) 6 :=
  Work.StemsB.cupT (fib g3) 2 4 x (x2 g3 x)

/-- The fourth power `x² ⌣ x²` of a degree-2 class. -/
abbrev z4 (x : Coh ℤ (fib g3) 2) : Coh ℤ (fib g3) 8 :=
  Work.StemsB.cupT (fib g3) 4 4 (x2 g3 x) (x2 g3 x)

/-- The generic-data transgression `τS_low` on the fibre's top degree. -/
abbrev wTauSLow : (Work.Cohomology.relComplex ℤ (TopCat.of (Ecov g3))
    (Work.StemsB.wangA 3 (proj g3))).homology ((3 - 1) + 1) ≅ Coh ℤ (fib g3) 0 :=
  Work.StemsB.wangTauSLow 3 (by norm_num) (Ecov g3) (proj g3) (hTO g3) shellPt (hTG g3)

/-! ## The low transgression -/

/-- The low Wang exactness: `im α₂ = ker θ_{-1}`. -/
theorem wExactLow :
    Function.Exact
      (⇑(Work.StemsB.wangCohAlphaLowR ℤ (TopCat.of (Ecov g3)) (Work.StemsB.wangA 3 (proj g3))
        (Work.StemsB.wangCohFsp 3 (proj g3)) 3
        (Work.StemsB.wangGammaExplicit 3 (proj g3) (hTO g3))))
      (⇑(Wθlow (g3 := g3))) :=
  wangExactLow 3 (by norm_num) (proj g3) (hTO g3) shellPt (hTG g3)

/-- **The low transgression of the cover is surjective**: `H³(E) = 0`. -/
theorem Wθlow_surj (hP3 : PostnikovData 3 12 g3 s3) :
    Function.Surjective (⇑(Wθlow (g3 := g3))) := by
  obtain ⟨β, hβ, -⟩ := betaLow 3 (by norm_num) (TopCat.of (Ecov g3))
    (Work.StemsB.wangA 3 (proj g3)) (Work.StemsB.wangCohFsp 3 (proj g3))
    (Work.StemsB.wangGammaExplicit 3 (proj g3) (hTO g3)) (wTauSLow g3)
  haveI : Subsingleton (Coh ℤ (Ecov g3) 3) := h3zero g3 hP3
  have hβ0 : β = 0 := by
    apply ModuleCat.hom_ext
    ext y
    exact Subsingleton.elim _ _
  have hθeq : ∀ a, (Work.StemsB.wangCohThetaLowR ℤ (TopCat.of (Ecov g3))
      (Work.StemsB.wangA 3 (proj g3)) (Work.StemsB.wangCohFsp 3 (proj g3)) 3
      (Work.StemsB.wangGammaExplicit 3 (proj g3) (hTO g3)) (wTauSLow g3)).hom a =
        Wθlow (g3 := g3) a :=
    fun a => Work.StemsB.wangTauSLow_value 3 (by norm_num) (Ecov g3) (proj g3) (hTO g3)
      shellPt (hTG g3) a
  intro y
  have hmem : y ∈ Set.range (fun a =>
      (Work.StemsB.wangCohThetaLowR ℤ (TopCat.of (Ecov g3)) (Work.StemsB.wangA 3 (proj g3))
        (Work.StemsB.wangCohFsp 3 (proj g3)) 3
        (Work.StemsB.wangGammaExplicit 3 (proj g3) (hTO g3)) (wTauSLow g3)).hom a) := by
    have h2 : β y = 0 := by rw [hβ0]; rfl
    exact (hβ y).mp h2
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, by rw [← hθeq a]; exact ha⟩

/-- **The low transgression of the cover is injective**: `H²(E) = 0`. -/
theorem Wθlow_inj (hP3 : PostnikovData 3 12 g3 s3) :
    Function.Injective (⇑(Wθlow (g3 := g3))) := by
  haveI : Subsingleton (Coh ℤ (Ecov g3) 2) := subH2 g3 hP3
  have hα0 : Work.StemsB.wangCohAlphaLowR ℤ (TopCat.of (Ecov g3))
      (Work.StemsB.wangA 3 (proj g3)) (Work.StemsB.wangCohFsp 3 (proj g3)) 3
      (Work.StemsB.wangGammaExplicit 3 (proj g3) (hTO g3)) = 0 := by
    apply ModuleCat.hom_ext
    ext y
    rw [show y = 0 from Subsingleton.elim y 0]
    exact map_zero _
  have hz : ∀ y : Coh ℤ (fib g3) 2, Wθlow (g3 := g3) y = 0 ↔ y = 0 := by
    intro y
    rw [wExactLow (g3 := g3) y, hα0]
    simp [eq_comm]
  intro a b hab
  refine sub_eq_zero.mp ((hz (a - b)).mp ?_)
  rw [map_sub, hab, sub_self]

/-! ## Elementary scalar lemmas -/

/-- The `ℕ`-multiple of a `ℤ`-multiple, in the `zsmul` normal form. -/
lemma nsmul_zsmul_assoc {M : Type} [AddCommGroup M] [Module ℤ M] (k : ℕ) (m : ℤ) (z : M) :
    (k:ℕ) • (m • z) = ((k:ℤ) * m) • z := by
  rw [show (k:ℕ) • (m • z) = (k:ℤ) • (m • z) from
    (Nat.cast_smul_eq_nsmul ℤ k (m • z)).symm.trans (Int.cast_smul_eq_zsmul ℤ k (m • z)),
    smul_smul]

/-- The right unit law of the cup product on the fibre, in the `cup` spelling. -/
lemma cup_one_rightL (n : ℕ) (y : Coh ℤ (fib g3) n) :
    (Work.Pi6.cup ℤ (fib g3) n 0 y) (one ℤ (fib g3)) = y :=
  Work.Cohomology.cupH'_one_right ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) n y

/-- The right unit law of the cup product on the fibre, in the `cupT` spelling. -/
lemma cupT_one_right (n : ℕ) (y : Coh ℤ (fib g3) n) :
    (Work.StemsB.cupT (fib g3) n 0 y) (one ℤ (fib g3)) = y :=
  Work.Cohomology.cupH'_one_right ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) n y

/-- `cupT x x` is `cpow x 2`. -/
lemma x2_eq (x : Coh ℤ (fib g3) 2) : cpow x 2 = x2 g3 x := cpow_two_eq_cupT g3 x

/-- The associativity of the cup product in the form `x³ = (x ⌣ x) ⌣ x`. -/
lemma cpow3_eq (x : Coh ℤ (fib g3) 2) :
    cpow x 3 = Work.StemsB.cupT (fib g3) 4 2 (x2 g3 x) x := by
  show (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) (2*2) 2 (cpow x 2)) x
    = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) 4 2 (x2 g3 x)) x
  rw [cpow_two_eq_cupT g3 x]

/-- The right-nested cube is the left-nested cube (`x ⌣ (x ⌣ x) = (x ⌣ x) ⌣ x`). -/
lemma y3_eq_cpow3 (x : Coh ℤ (fib g3) 2) : y3 g3 x = cpow x 3 :=
  ((Work.Cohomology.cupH'_assoc ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) 2 2 2 x x x).symm).trans
    (cpow3_eq g3 x).symm

/-- `(x ⌣ x) ⌣ x = x ⌣ (x ⌣ x)`. -/
lemma x2x_eq (x : Coh ℤ (fib g3) 2) : Work.StemsB.cupT (fib g3) 4 2 (x2 g3 x) x = y3 g3 x :=
  (cpow3_eq g3 x).symm.trans (y3_eq_cpow3 g3 x).symm

/-- `cpow x 4 = x² ⌣ x²` (associativity of the cup product). -/
lemma cpow4_eq (x : Coh ℤ (fib g3) 2) : cpow x 4 = z4 g3 x := by
  have h1 : cpow x 4 = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (fib g3)))
      (2*3) 2 (cpow x 3)) x := rfl
  rw [h1, cpow3_eq g3 x]
  show (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) (4+2) 2
      ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) 4 2 (x2 g3 x)) x)) x
    = (Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) 4 4 (x2 g3 x)
        ((Work.Cohomology.cupH' ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) 2 2) x x))
  exact (Work.Cohomology.cupH'_assoc ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) 4 2 2
    (x2 g3 x) x x)

end

end Work.Pi6.EFACTS
