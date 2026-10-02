import Mathlib
import Submission.Work.LerayHirsch.SplitLines
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.LerayHirsch.WhitneyParacompact
import Submission.Work.LerayHirsch.whitneySumFormula_one_one_of_topClassMul
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.ChernProduct
import Submission.Work.Whitney.chernClass_whitneySum_of_lt
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.Whitney.pontryagin1_whitneySum_line
import Submission.Work.Whitney.chernRelation_of_whitneyFormula
import Submission.Work.Whitney.chernClass_whitneySum_middle
import Submission.Work.LineBundles.Main
import Submission.Work.Gen.whitneySumFormulaPar_one_N_of_splitCrux
import Submission.Work.Gen.eSymDef
import Submission.Work.Whitney.cruxUniversality
import Submission.Work.Whitney.cruxDeltaExist

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The split case of the Whitney sum formula for `Work.Thom.chernClass`

**Target.** `Work.LerayHirsch.WhitneySumFormulaSplit`: for a complex line bundle `L` and an iterated
direct sum `lineSumCore n M` of `n` complex line bundles over a paracompact Hausdorff base,

  `c_k(L ⊕ (M 0 ⊕ … ⊕ M (n-1))) = Σ_{i+j=k} c_i(L) ⌣ c_j(lineSumCore n M)`   for all `k`.

**PROVED (this file).**  The proof goes through the "crux family"

  `hcrux(N)`:  `c_{N-1}(lineSumCore N M) = eSym N M (N-1)`   (`N` arbitrary, `M` a family of lines),

which `Work.Whitney.wsfSplit_of_crux` (below) turns into the target via
`Work.Gen.whitneySumFormulaPar_one_N_of_splitCrux`.  `hcrux` is obtained from the δ-form of the
ψ-analysis,

  `REL(N,B,M)`:  `∃ δ : H⁰(B;ℤ), c_{N-1}(lineSumCore N M) = deltaCup N M δ`
  (`Work.Whitney.CruxRel`, proved in `cruxDeltaExist.lean`),

by the **product argument** `Work.Whitney.hcrux_of_rel` (`cruxUniversality.lean`): over the product
`B₀ × B` of a compact model base `B₀ = ℂP^{N-1}` (model family `(ℓ,…,ℓ,ε)`, whose crux is the *top*
class formula, `Work.Whitney.cruxModelPins`) with `B`, the external tensor product
`pr₁^*M₀ᵢ ⊗ pr₂^*Mᵢ` has both a slice isomorphic to `M₀` — where the relation forces the coefficient
to be `1` (`Work.Whitney.cruxPin_of_familyIso` + `tensorSliceIso` + `cruxRel_comap`) — and a slice
isomorphic to `M`, which yields the crux.  The full account is in
`Submission/Work/Whitney/PLAN_universality_v3.md`.

The earlier reduction of the split case to the crux family, and the intermediate-degree material
(`Work.Whitney.chernClass_whitneySum_of_lt` for the degrees `k ≤ max(1,n) - 1`,
`Work.Whitney.chernClass_whitneySum_top` for the top degree `k = n+1`,
`Work.Gen.chernClass_whitneySum_of_diag` + padding for the rest), are unchanged.
-/

namespace Work.Whitney

/-- **The "core" family of the Whitney sum formula**: the cases `(k, k-1)` in degree `k`.  This is
equivalent to `Work.LerayHirsch.WhitneySumFormulaSplit` (see the module docstring). -/
def WhitneyCore : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin k)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (k - 1))) ι₂),
    Work.Thom.chernClass (k + (k - 1)) k (whitneySum Z₁ Z₂)
      = chernProductSum Z₁ Z₂ k

/-- **The middle degrees of the Whitney sum formula follow from the formula at smaller total rank**
(the "pairing argument"): for a pair of total rank `M`, all degrees `k ≤ M - 2` are reachable from
the descent over `P(Z₁)`, because the intermediate pair `(ℓ, Q₁ ⊕ π^*Z₂)` has total rank `M - 1`.
This is the part of the Whitney formula that does *not* need the core; it is stated here as a `Prop`
for use by the assembly. -/
def WhitneyMiddle : Prop :=
  ∀ {m₁ m₂ k : ℕ}, k + 2 ≤ m₁ + m₂ →
    (∀ {m₁' m₂' : ℕ}, m₁' + m₂' ≤ m₁ + m₂ - 1 →
      ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι₁' ι₂' : Type}
        [Fintype ι₁'] [Fintype ι₂']
        (W₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁')) ι₁')
        (W₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂')) ι₂') (j : ℕ),
        Work.Thom.chernClass (m₁' + m₂') j (whitneySum W₁ W₂) = chernProductSum W₁ W₂ j) →
    ∀ {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι₁ ι₂ : Type}
      [Fintype ι₁] [Fintype ι₂]
      (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
      (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂),
      Work.Thom.chernClass (m₁ + m₂) k (whitneySum Z₁ Z₂) = chernProductSum Z₁ Z₂ k

/-! ## The assembly: the target from the crux family

`Work.Gen.whitneySumFormulaPar_one_N_of_splitCrux` (proved, axiom-clean, see
`Submission/Work/Gen/whitneySumFormulaPar_one_N_of_splitCrux.lean`) turns the *crux family*

  `hcrux (n) : c_{n-1}(lineSumCore n M) = eSym n M (n-1)`   (`n` arbitrary, `M : Fin n → line`)

into the whole `(1,N)` family of the Whitney formula over paracompact Hausdorff bases, and the
split case is its instance `Z₂ = lineSumCore n M`.  So the target reduces to `hcrux`, which is
exactly the content of `Submission/Work/Whitney/PLAN_crux_v2.md`. -/

/-- **The split case from the `(1,N)` family** (the instance `Z₂ = lineSumCore n M`). -/
theorem wsfSplit_of_oneN
    (h : ∀ N : ℕ, Work.LerayHirsch.WhitneySumFormulaPar 1 N) :
    Work.LerayHirsch.WhitneySumFormulaSplit := by
  intro P _ _ _ ι ι' _ _ n L M k
  exact h n L (Work.LerayHirsch.lineSumCore n M) k

/-- **The target from the crux family** `c_{n-1}(lineSumCore n M) = eSym n M (n-1)`. -/
theorem wsfSplit_of_crux
    (hcrux : ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι]
      (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
        = Work.Gen.eSym n M (n - 1)) :
    Work.LerayHirsch.WhitneySumFormulaSplit :=
  wsfSplit_of_oneN (Work.Gen.whitneySumFormulaPar_one_N_of_splitCrux hcrux)

theorem whitneySumFormulaSplit : Work.LerayHirsch.WhitneySumFormulaSplit :=
  wsfSplit_of_crux (Work.Whitney.hcrux_of_rel (fun N => by
    rcases N with _ | N
    · exact cruxRel_zero
    · exact fun M => cruxDeltaExist (N + 1) (by omega) M))

end Work.Whitney
