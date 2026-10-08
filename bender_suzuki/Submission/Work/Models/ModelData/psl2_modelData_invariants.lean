import Mathlib
import Submission.Work.Models.ModelData.pSL2ModelData
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.Models.Abstract.modelFactsFor
import Submission.Work.Models.Port.BenderPairModels

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.ModelData

open LeanEval.GroupTheory.Defs

/-- **The invariants of the model data of `PSL(2, 2ⁿ)`.**  Every rank-one `(B,N)`-pair structure
with model data on `PSL(2,2ⁿ)` has unipotent radical `U` of order `2ⁿ` and `K₀ = J(T,w)` of order
`2ⁿ - 1`:

* the Borel `P.B` is a strongly embedded subgroup, hence a conjugate of the standard (point
  stabilizer) Borel (`Work.Models.Abstract.exists_conj_eq`), and the number of involutions of a
  subgroup is unchanged by conjugation;
* the standard Borel has exactly `2ⁿ - 1` involutions (`psl2NcardInvolutionsStab`), and
  `|K₀| = #Inv(B)` (`P.hK0card`);
* the Suzuki index axiom `[G : B] = |U| + 1` (`P.hindex`) together with the invariance of the
  index under conjugation pins down `|U| = 2ⁿ` from the standard value `|U₀| = 2ⁿ`. -/
theorem psl2_modelData_invariants {n : ℕ} (hn : 2 ≤ n)
    (P : Work.Models.ModelData (LeanEval.GroupTheory.Defs.PSL2Model n)) :
    Nat.card ↥P.K0 + 1 = 2 ^ n ∧ Nat.card ↥P.U = 2 ^ n := by
  have hn1 : 1 ≤ n := by omega
  -- `P.B` is a strongly embedded subgroup, hence a conjugate of the standard Borel.
  obtain ⟨g, hg⟩ := Work.Models.Abstract.exists_conj_eq
    (Submission.PSL2.pSL2BenderPair n hn) (H := P.B) P.hSemb
  -- The order of `K₀` is the involution count of the Borel.
  have hK0 : Nat.card ↥P.K0 = 2 ^ n - 1 := by
    rw [P.hK0card, hg, Work.Models.Abstract.ncard_involutions_conj]
    change (Submission.Blueprint.involutions
      ((MulAction.stabilizer (PSL2Model n) (Submission.PSL2.pt0 (GaloisField 2 n)) :
        Subgroup (PSL2Model n)) : Set (PSL2Model n))).ncard = 2 ^ n - 1
    exact psl2NcardInvolutionsStab n hn
  constructor
  · rw [hK0, Nat.sub_add_cancel Nat.one_le_two_pow]
  · -- `[G : B] = |U| + 1` and `[G : B]` is that of the standard Borel, namely `2ⁿ + 1`.
    have h1 := P.hindex
    rw [hg, Subgroup.index_map_of_bijective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).bijective] at h1
    have h2 := (Submission.PSL2.pSL2BenderPair n hn).hindex
    change (MulAction.stabilizer (PSL2Model n) (Submission.PSL2.pt0 (GaloisField 2 n))).index
      = Nat.card ↥P.U + 1 at h1
    change (MulAction.stabilizer (PSL2Model n) (Submission.PSL2.pt0 (GaloisField 2 n))).index
      = Nat.card ↥((Commons.GroupTheory.SL2.unipotentPSLHom (GaloisField 2 n)).range) + 1 at h2
    rw [h2, Submission.PSL2.card_unipotentPSLHom_range n hn1] at h1
    omega

end Work.Models.ModelData
