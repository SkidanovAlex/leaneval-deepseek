import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.CFTLib.Existence.exists_unramified_normClassSubgroup
import Submission.NK.CFTLib.Existence.localNormImage_of_forall_ne_of_arl
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

# Guidance: the existence theorem at prime index (Takagi; Milne CFT V.4 / Neukirch ANT VI.6 / Lang XI)
RULE: no licensed inputs; build what is missing; declare_false only with a counterexample.
Consumers: `NK.CFTLib.exists_pClassField_of_inputs` (its `hEx`) and `NK.CFTLib.pClassFieldArtin_of_inputs` — the
Hilbert p-class field needed by three LeanEval problems. Read `Submission/Work/CFTLib/{pClassField_exists,
pClassFieldArtin_of_fc}.lean` and `Submission/Work/CFTLib/Existence/` (partial work: Kummer index, `kummerE`, descent
lemmas — reuse).
Proof: (1) K ⊇ μ_p: choose a finite set S of places (∞, primes over p, generators of the class group) and
Δ = S-units; M = K(Δ^{1/p}) is abelian of exponent p with [M:K] = p^{|S|} (Kummer), and its norm group
N_{M/K}C_M is computed: it contains the image of ∏_{v∈S}K_v^{×p} × ∏_{v∉S}U_v (local norms from unramified/Kummer
local extensions) and the index count ([C_K : that subgroup] = p^{|S|} by the unit theorem / Kummer count) plus
[C_K : N C_M] = [M:K] (abelian: from hARL/hFC — reciprocity iso) forces equality. Every V ⊇ N C_M of index p is then
the norm group of the fixed field of the corresponding subgroup (Galois correspondence + reciprocity iso).
Choosing S so that V ⊇ that subgroup (V is open, contains the integral idèles) gives L. (2) General K: pass to
K' = K(μ_p) (degree prime to p), apply (1) to the preimage of V under N_{K'/K}, descend the field (the class field
over K' of the pulled-back group is Galois over K; its degree-p part descends).
Unramifiedness from V ⊇ integral idèles (local units are norms exactly when unramified; K_v^× at real v are norms
⇒ real places stay real). Delegate (1) and (2) and the unramifiedness step separately.
-/

namespace NK.CFTLib.Existence

theorem classField_exists_primeIndex (hARL : NK.CFTLib.ArtinReciprocityIdeal)
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement) :
    ∀ {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
      (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)), V.FiniteIndex →
      IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)) → V.index = p →
      (NK.GlobalCFT.Idele.integralIdeles K).map (NK.GlobalCFT.IdeleClassGroup.mk K) ≤ V →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
        IsGalois K L ∧ NK.GlobalCFT.Idele.normClassSubgroup K L = V ∧ Module.finrank K L = p ∧
        differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤ ∧
        IsUnramifiedAtInfinitePlaces K L := fun {K} _ _ p _ V hV hopen hidx hray =>
  exists_unramified_normClassSubgroup (K := K) hARL hFC
    (fun {K} [Field K] [NumberField K] {L} [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L)) {x v₀} hx =>
        NK.CFTLib.Existence.localNormImage_of_forall_ne_of_arl hARL hcyc hx)
    p V hV hopen hidx hray

end NK.CFTLib.Existence
