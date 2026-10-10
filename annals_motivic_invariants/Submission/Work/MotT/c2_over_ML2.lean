import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotC2.aut_functionField

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

set_option linter.style.haveILetI false

/-- **T4, step 3: node C2 over the two-root Kummer field `L = K(ζ, w₁, w₂)`.**

`Work.MotC2.aut_functionField` (proved) applied to the base change `D.E.baseChange L`: every
`L`-algebra automorphism of `M = ML2 D h₁ h₂ hk = L(E)` is `τ_Q ∘ [-1]^ε` with `Q` an **`L`-point**
of `E` and `ε : Fin 2`.  Running node C2 over `L` (rather than over `K̄`) is what makes the point
`Q` — and hence the coordinates of the final `K`-point of the twisted Klein curve — rational over
`L`, hence over `K` by Galois descent along the finite Galois extension `L/K`
(`Work.MotT.isGalois_KummerField2`).

The two instance binders are not synthesizable globally and must therefore be explicit arguments:
`DecidableEq ↥(KummerField2 K h₁ h₂ hk)` (used by `transAlgEquiv`) and
`(D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic` (from `D.Good.elliptic`; there is no
`IsElliptic` base-change instance).  Callers supply them as `letI := Classical.decEq _` and
`haveI := hD.elliptic` + `inferInstance`.

Route: `j(D.E.baseChange L) ≠ 0, 1728` because `WeierstrassCurve.map_j` identifies the base-changed
`j` with the image of `D.E.j` and `D.Good` gives `j ≠ 0, 1728`; then apply
`Work.MotC2.aut_functionField ↥(KummerField2 K h₁ h₂ hk) (Classical.decEq _) (D.E.baseChange _) _ hj0 hj Θ`.

NOTE for the prover: the import chain `Work.MotC2.aut_functionField` currently fails to build
(`Submission/Work/MotC2/AffRingNormalCharTwo.lean` re-declares `Ax_le_affRing`, `xPhi_linCoef`,
`xPhi_cubCoef`, since added to `Submission/Work/MotC2/NeTwoSetup.lean`, plus four dependent failed
rewrites).  Repairing that clash (removing/renaming the duplicates in `AffRingNormalCharTwo.lean`)
is part of this lemma: nothing can be built against the `MotC2` chapter until it is fixed. -/
theorem c2_over_ML2 {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    (Θ : ML2 D h₁ h₂ hk ≃ₐ[↥(KummerField2 K h₁ h₂ hk)] ML2 D h₁ h₂ hk) :
    ∃ (Q : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point) (ε : Fin 2),
      Θ = Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) Q *
        (Work.MotC2.negAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk))) ^ (ε : ℕ) := by
  -- `hD.elliptic` as an instance, so that `j` of the *map* form `D.E.map (algebraMap K L)` (which is
  -- definitionally the base change) can be formed and `WeierstrassCurve.map_j` applied to it.
  haveI hE : D.E.IsElliptic := hD.elliptic
  -- `WeierstrassCurve.j` is defined through the elliptic instance (`Δ' = IsElliptic.isUnit.unit`),
  -- so `j` of the base change and `j` of the map form are only propositionally equal; since both
  -- instances are proofs of a `Prop`, they are definitionally equal and the `have` below is
  -- accepted by `exact`.
  have hj0 : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).j ≠ 0 := by
    have h : (D.E.map (algebraMap K ↥(KummerField2 K h₁ h₂ hk))).j ≠ 0 := by
      rw [WeierstrassCurve.map_j]
      exact fun h => hD.j_ne_zero
        ((algebraMap K ↥(KummerField2 K h₁ h₂ hk)).injective (by simpa using h))
    exact h
  have hj : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).j ≠ 1728 := by
    have h : (D.E.map (algebraMap K ↥(KummerField2 K h₁ h₂ hk))).j ≠ 1728 := by
      rw [WeierstrassCurve.map_j]
      intro h
      exact hD.j_ne
        ((algebraMap K ↥(KummerField2 K h₁ h₂ hk)).injective (by rw [h, map_ofNat]))
    exact h
  exact @Work.MotC2.aut_functionField ↥(KummerField2 K h₁ h₂ hk) _ instDec
    (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) instEll hj0 hj Θ

end Work.MotT
