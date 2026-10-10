import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.Data.Nat.Prime.Defs
import Submission.Work.SSGRoute.prop5.Nat
import Submission.Work.SSGRoute.prop5.Surj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: Proposition 5 of Schmidt–Wingberg for every τ = (i,j), 1 ≤ j ≤ i

Pure group theory. The whole shrinking chapter (`Submission/Work/CohomologicalShrinking/`) depends only on
this. Read its `NOTES.md` §3 and `Prop5.lean` (the structure `Prop5Data`); do not edit them.

**Goal.** Produce G-equivariant, surjective maps θ_d : (F(d)/F(d)²)^{⊗j} → E(d,(i,j)), natural in surjective
operator maps F(m) → F(n) (the field `θ_natural`), where F(d) = `Work.Shrinking.freeOperatorGroup G d`.
Take the paper's map x₁⊗…⊗x_j ↦ [x₁,[x₂,[…,x_j]]]^{p^{i−j}}. It is natural for *all* homs, so G-equivariance
and naturality are formal once it is well defined.

**Assets.**
- `refinedTerm`, `pSeries`, `centralSeries`, `tauSucc`, `E`, `squareQuotient`,
  `modsquare.squareQuotientToFun_bijective`;
- `commutator_refinedTerm_le`, `pow_refinedTerm_le`, `isFpGModule_E`;
- `gradedMapLin`, `quotMapLin` with `functorial.*`;
- the model case `nonempty_prop5Data_one_one`.

**Sketch.**
1. Lemma 4(i), collection. For x ∈ P_i and y ∈ P_j (p-central indices), (xy)^a ≡ x^a y^a [y,x]^{C(a,2)} and
   the two commutator-power formulas hold, modulo the stated P terms. Prove it in any group by induction on
   a, with the Hall–Petrescu formula x^a y^a = (xy)^a c_2^{C(a,2)} ⋯ c_a with c_k ∈ γ_k⟨x,y⟩, and
   γ_k(P_i-elements) ⊆ P_{ki}. Also show Lazard's P_i = ∏_{k≤i} γ_k^{p^{i−k}} (mod P_{i+1} suffices).
2. Well-definedness and multilinearity of θ follow from 1, by induction on the word length.
3. Lemma 4(ii), for free groups: P_i ∩ γ_j = ∏_{k≥j} γ_k^{p^{i−k}} · P_{i+1}. This needs γ_k/γ_{k+1}
   torsion-free (Witt). Use the Magnus map FreeGroup X → units of ℤ⟨X⟩ truncated at degree N, x ↦ 1+X.
   - The leading term of c ∈ γ_k is a nonzero Lie polynomial of degree k, and c ∈ γ_{k+1} iff it vanishes.
   - The leading term of c^{p^e} is p^e·(leading term), which is nonzero in ℤ⟨X⟩.
   - Delegate "Magnus: γ_k = dimension subgroup D_k over ℤ" as its own sub-lemma.
4. Surjectivity: generators of P_{(i,j)} mod P_{(i,j)+1} are the p^{i−j}-powers of left-normed j-fold
   commutators of basis elements. These are images of basis tensors.

**Imports.** `Mathlib`, `Submission.Work.CohomologicalShrinking.All`.

**Pitfalls.**
- The indices are the paper's: `pSeries p P i = pCentralSeries (i-1)` and
  `centralSeries P j = lowerCentralSeries (j-1)`.
- The group is the *discrete* free group. All statements happen in the finite quotients F/P_{i+1}.
-/

namespace Work.SSGRoute

open SSGRoute
theorem prop5Data_exists (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (hj : 1 ≤ j) (hji : j ≤ i) :
    Nonempty (Work.CohomologicalShrinking.Prop5Data p G i j) :=
  ⟨fun d => Work.SSGRoute.prop5.thetaLin p G i j d hj hji,
    fun d g x => Work.SSGRoute.prop5.thetaLin_smul p G i j d hj hji g x,
    fun d => Work.SSGRoute.prop5.thetaLin_surjective p G i j d hj hji,
    fun m n ψ hψ _ => Work.SSGRoute.prop5.thetaLin_natural p G i j hj hji ψ hψ⟩

end Work.SSGRoute
