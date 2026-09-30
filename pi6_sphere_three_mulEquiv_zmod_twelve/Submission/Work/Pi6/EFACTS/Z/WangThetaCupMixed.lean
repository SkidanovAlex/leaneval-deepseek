import Mathlib
import Submission.Work.Pi6.EFACTS.Z.CollarSigmaCupMixed
import Submission.Work.StemsB.wangTheta_cup
import Submission.Work.Pi6.EFACTS.Z.WangThetaLow
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The mixed-degree multiplicativity of the Wang transgression

*(Area STEMS.  See `Submission/Work/Stems/C2ODD_PLAN.md` §3 and §7.)*

The Wang transgression `θ = ρ ∘ Σ ∘ λ_G^*` of a fibration over the sphere model is a derivation; the
tree has the two extreme cases

* `Work.StemsB.wangTheta_cup` — both factors of degree `n + b`, `n ≥ 0`;
* `Work.StemsB.wangTheta_cup_low` — both factors of degree `b - 1`.

The `C2` odd step needs the **mixed** case, with one factor of degree `b - 1` (the fundamental class
of the fibre) and the other of degree `m + b`.  This file transports the collar computation
`Work.Pi6.EFACTS.CollarZ.collarSigma_cup_mixed` through `λ_G^* = collarLambdaGCoh` and `ρ = rhoCoh` exactly
as `WangThetaCupLow.lean` does for the low case:

  `θ_{m+b-1}(x ⌣ y) = (-1)^{b-1} x ⌣ θ_m(y) + (-1)^{(b-1)(m+b)+(m+b)} y ⌣ θ_{b-1}(x)`.

For the `C2` odd step the relevant instance is `x` the fundamental class of the fibre and `y = x ⌣ x`,
which gives `θ(x³) = 3 x² θ(x)` (`x` has even degree), and this together with `wangTheta_cup_low`
(`θ(x²) = 2 x θ(x)`) and `wangTheta_cup` (the high case) yields `θ(x^k) = k x^{k-1} θ(x)` for every
`k` — the multiplicativity input that makes the cover of `Sᵇ` rationally acyclic in *all* degrees.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.EFACTS.CollarZ

open Work.StemsB
open Work.Pi6.EFACTS.CollarZ

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- **The mixed-degree multiplicativity of the Wang transgression**:
`θ_{m+b-1}(x ⌣ y) = (-1)^{b-1} · x ⌣ θ_m(y) + (-1)^{(b-1)(m+b)+(m+b)} · y ⌣ θ_{b-1}(x)`
for `x` of degree `b - 1` and `y` of degree `m + b`. -/
theorem wangTheta_cup_mixed (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (m : ℕ) (x : Work.Thom.Coh ℤ (b - 1) ↥(p ⁻¹' {OnePoint.infty}))
    (y : Work.Thom.Coh ℤ (m + b) ↥(p ⁻¹' {OnePoint.infty})) :
    transT ↥(p ⁻¹' {OnePoint.infty}) (by omega : (m + b - 1) + 1 = (b - 1) + (m + 1))
        (wangTheta b hb p d_G hT_G hT_O (m + b - 1)
          (transT ↥(p ⁻¹' {OnePoint.infty})
            (by omega : (b - 1) + (m + b) = (m + b - 1) + b)
            (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (m + b) x y)))
      = ((-1 : ℤ) ^ (b - 1)) •
          cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (m + 1) x
            (wangTheta b hb p d_G hT_G hT_O m y)
        + ((-1 : ℤ) ^ ((b - 1) * (m + b) + (m + b))) •
            transT ↥(p ⁻¹' {OnePoint.infty})
              (by omega : (m + b) + 0 = (b - 1) + (m + 1))
              (cupT ↥(p ⁻¹' {OnePoint.infty}) (m + b) 0 y
                (wangThetaLow b hb E p d_G hT_G hT_O x)) := by
  have hb1 : 1 ≤ b := by omega
  have h1 : (m + b - 1) + 1 = (b - 1) + (m + 1) := by omega
  have h2 : (b - 1) + (m + b) = (m + b - 1) + b := by omega
  have h3 : (m + b) + 0 = (b - 1) + (m + 1) := by omega
  have hτ := wangSusT_thom b hb (wangFY b p d_G)
  have hs := wangSusS_trans b hb (wangFY b p d_G)
  have hssq := wangSusS_sq b hb (wangFY b p d_G)
  have hσ := wangSusS_sect b hb (wangFY b p d_G)
  -- the ring-map property of `λ_G^*`
  have hU : (Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O ((b - 1) + (m + b))).hom
        (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (m + b) x y)
      = cupT ↥(sphLoopCollarProd b (wangFY b p d_G)) (b - 1) (m + b)
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y) :=
    Work.StemsB.GCoh_cup b hb1 p d_G hT_G hT_O (b - 1) (m + b) x y
  -- the collar derivation, mixed degrees
  have hder := collarSigma_cup_mixed b hb (Y := wangFY b p d_G) (wangSusT b hb (wangFY b p d_G))
    hτ (wangSusS b hb (wangFY b p d_G)) hs hssq hσ m
    ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
    ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y)
  have hder' : transT (wangFY b p d_G) h1
        (collarSigma b (by omega) (Y := wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ
          (m + b - 1)
          (transT ↥(sphLoopCollarProd b (wangFY b p d_G)) h2
            (cupT ↥(sphLoopCollarProd b (wangFY b p d_G)) (b - 1) (m + b)
              ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
              ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y))))
      = ((-1 : ℤ) ^ (b - 1)) •
          cupT (wangFY b p d_G) (b - 1) (m + 1)
            ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℤ (b - 1)).hom
              ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))
            (collarSigma b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ m
              ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y))
        + ((-1 : ℤ) ^ ((b - 1) * (m + b) + (m + b))) •
            transT (wangFY b p d_G) h3
              (cupT (wangFY b p d_G) (m + b) 0
                ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℤ (m + b)).hom
                  ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y))
                (collarSigmaLow b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ
                  ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))) := hder
  -- the identification `ρ ∘ σ^* ∘ λ^* = id` on the two factors
  have hρσx : (rhoCoh b hb1 p d_G hT_G hT_O (b - 1)).hom
        ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℤ (b - 1)).hom
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)) = x := by
    rw [show (Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℤ (b - 1)).hom
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
        = (lamPtCoh b hb1 p d_G hT_G hT_O (b - 1)).hom x from
      GCoh_sec b hb1 p d_G hT_G hT_O (b - 1) x]
    exact rho_lam b hb1 p d_G hT_G hT_O (b - 1) x
  have hρσy : (rhoCoh b hb1 p d_G hT_G hT_O (m + b)).hom
        ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℤ (m + b)).hom
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y)) = y := by
    rw [show (Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℤ (m + b)).hom
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y)
        = (lamPtCoh b hb1 p d_G hT_G hT_O (m + b)).hom y from
      GCoh_sec b hb1 p d_G hT_G hT_O (m + b) y]
    exact rho_lam b hb1 p d_G hT_G hT_O (m + b) y
  -- the mixed-degree transgression of the product
  have hSig : collarSigma b (by omega) (Y := wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ
        (m + b - 1)
        (transT ↥(sphLoopCollarProd b (wangFY b p d_G)) h2
          (cupT ↥(sphLoopCollarProd b (wangFY b p d_G)) (b - 1) (m + b)
            ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
            ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y)))
      = transT (wangFY b p d_G) h1.symm
          ((((-1 : ℤ) ^ (b - 1)) •
              cupT (wangFY b p d_G) (b - 1) (m + 1)
                ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℤ (b - 1)).hom
                  ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))
                (collarSigma b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ m
                  ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y)))
            + ((-1 : ℤ) ^ ((b - 1) * (m + b) + (m + b))) •
                transT (wangFY b p d_G) h3
                  (cupT (wangFY b p d_G) (m + b) 0
                    ((Work.Thom.CohMap (collarSection (Y := wangFY b p d_G) b hb1) ℤ (m + b)).hom
                      ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y))
                    (collarSigmaLow b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ
                      ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)))) := by
    rw [transT_round h1 (collarSigma b (by omega) (Y := wangFY b p d_G)
      (wangSusT b hb (wangFY b p d_G)) hτ (m + b - 1)
      (transT ↥(sphLoopCollarProd b (wangFY b p d_G)) h2
        (cupT ↥(sphLoopCollarProd b (wangFY b p d_G)) (b - 1) (m + b)
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x)
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y))))]
    rw [hder']
  -- the two `λ`-transports
  have hlam : (Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O ((m + b - 1) + b)).hom
        (transT ↥(p ⁻¹' {OnePoint.infty}) h2
          (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (m + b) x y))
      = transT ↥(sphLoopCollarProd b (wangFY b p d_G)) h2
          ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O ((b - 1) + (m + b))).hom
            (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (m + b) x y)) :=
    GCoh_transT b hb1 p d_G hT_G hT_O h2 _
  have hmain : transT ↥(p ⁻¹' {OnePoint.infty}) h1
        (wangTheta b hb p d_G hT_G hT_O (m + b - 1)
          (transT ↥(p ⁻¹' {OnePoint.infty}) h2
            (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (m + b) x y)))
      = ((-1 : ℤ) ^ (b - 1)) •
          cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) (m + 1) x
            (wangTheta b hb p d_G hT_G hT_O m y)
        + ((-1 : ℤ) ^ ((b - 1) * (m + b) + (m + b))) •
            transT ↥(p ⁻¹' {OnePoint.infty}) h3
              (cupT ↥(p ⁻¹' {OnePoint.infty}) (m + b) 0 y
                (wangThetaLow b hb E p d_G hT_G hT_O x)) := by
    rw [wangTheta_apply]
    rw [hlam, hU]
    rw [hSig]
    rw [rho_transT]
    rw [map_add, map_zsmul, map_zsmul]
    rw [rho_transT]
    rw [rho_cup, rho_cup]
    rw [hρσx, hρσy]
    rw [show (rhoCoh b hb1 p d_G hT_G hT_O 0).hom
          (collarSigmaLow b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ
            ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (b - 1)).hom x))
        = wangThetaLow b hb E p d_G hT_G hT_O x from wangThetaLow_apply b hb E p d_G hT_G hT_O x]
    rw [show (rhoCoh b hb1 p d_G hT_G hT_O (m + 1)).hom
          (collarSigma b hb1 (wangFY b p d_G) (wangSusT b hb (wangFY b p d_G)) hτ m
            ((Work.StemsB.collarLambdaGCoh b p d_G hT_G hT_O (m + b)).hom y))
        = wangTheta b hb p d_G hT_G hT_O m y from wangTheta_apply b hb p d_G hT_G hT_O m _]
    -- the outer `transT` cancels the one introduced by `hSig`
    exact (transT_comp h1.symm h1 _).trans (transT_self _ _)
  exact hmain

/-! ## The powers of the fibre generator -/

/-- **The `k`-th power of a class of the fibre**, `x ↦ x^{k+1}` (so that `k = 0` gives `x`), living
in degree `(b-1) * (k+1)`.  Written by recursion on `k` so that no unit class of `H^*(F)` is
needed: the odd step only ever asks for powers `≥ 2`.  The degree is written with the *numeral* on
the right so that the recursion steps are definitional. -/
def wangPow (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b))
    (x : Work.Thom.Coh ℤ (b - 1) ↥(p ⁻¹' {OnePoint.infty})) :
    ∀ k : ℕ, Work.Thom.Coh ℤ ((b - 1) * (k + 1)) ↥(p ⁻¹' {OnePoint.infty})
  | 0 => transT ↥(p ⁻¹' {OnePoint.infty})
      (by rw [Nat.mul_one] : (b - 1) = (b - 1) * (0 + 1)) x
  | (k + 1) =>
      transT ↥(p ⁻¹' {OnePoint.infty})
        ((Nat.add_comm (b - 1) ((b - 1) * (k + 1))).trans
          (Nat.mul_succ (b - 1) (k + 1)).symm)
        (cupT ↥(p ⁻¹' {OnePoint.infty}) (b - 1) ((b - 1) * (k + 1)) x
          (wangPow b hb E p d_G hT_G hT_O x k))

end

end Work.Pi6.EFACTS.CollarZ
