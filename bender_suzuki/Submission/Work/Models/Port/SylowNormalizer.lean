/-
**Strongly embedded subgroups are normalizers of Sylow `2`-subgroups.**

Let `G` be a finite group, `M ≤ G` strongly embedded, and suppose that the normalizer of every
Sylow `2`-subgroup of `G` is a maximal (proper) subgroup.  Then `M` itself is the normalizer of a
Sylow `2`-subgroup of `G`.

This is the first structural step of Bender's classification: a strongly embedded subgroup is a
`2`-local subgroup, namely the normalizer of a Sylow `2`-subgroup.  The mathematics now lives in
the commons (modules `Commons.GroupTheory.StronglyEmbedded.*`); the declarations below are thin
convenience wrappers under the `Submission` namespace.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.le_of_isPGroup_of_inf_ne_bot
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.exists_involution_mem
import Submission.Work.Models.Port.Commons.GroupTheory.OrderOfElement.odd_card_iff_forall_orderOf_ne_two
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.exists_sylow_normalizer_eq_of_isStronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff
import Submission.Work.Models.Port.Commons.GroupTheory.Bender.isBenderAction_coset
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.centralizer_le_conj
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.exists_conj_eq_of_isStronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.exists_conj_mem_of_orderOf_eq_two
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.existsUnique_conj_mem_of_orderOf_eq_two
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.exists_conj_centralizer_le_of_orderOf_eq_two
import Submission.Work.Models.Port.Commons.GroupTheory.MulAut.toMonoidHom_mulAut_conj_apply

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open LeanEval.GroupTheory.Defs

namespace Submission

theorem exists_sylow_normalizer_eq_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (hmax : ∀ T : Sylow 2 G,
      IsCoatom (Subgroup.normalizer (((T : Subgroup G) : Set G)))) :
    ∃ T : Sylow 2 G, M = Subgroup.normalizer (((T : Subgroup G) : Set G)) :=
  Commons.GroupTheory.StronglyEmbedded.exists_sylow_normalizer_eq_of_isStronglyEmbedded
    M hMne hMeven hModd hmax

/-! ## The normalizer of a conjugate subgroup -/

/-- Membership in a conjugate subgroup, in terms of conjugation by the inverse. -/
lemma mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (g : G) (y : G) :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H :=
  Commons.GroupTheory.Subgroup.mem_map_mulAut_conj_iff H g y

/-- `g y g⁻¹` lies in the conjugate `H^g` exactly when `y ∈ H`. -/
lemma mem_conj_iff {G : Type*} [Group G] (H : Subgroup G) (g : G) (y : G) :
    g * y * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom ↔ y ∈ H := by
  rw [mem_map_conj_iff]
  constructor
  · intro h; convert h using 1; group
  · intro h; convert h using 1; group

/-- **The normalizer of a conjugate subgroup is the conjugate of the normalizer.** -/
lemma normalizer_map_mulAut_conj {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom) : Set G) =
      (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom :=
  Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj H g

/-- **All strongly embedded subgroups are conjugate**, under the hypothesis that the normalizer of
every Sylow `2`-subgroup is a maximal subgroup: each strongly embedded subgroup is the normalizer
of a Sylow `2`-subgroup, and Sylow `2`-subgroups are conjugate. -/
theorem exists_conj_eq_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    (M M' : Subgroup G)
    (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (hM'ne : M' ≠ ⊤) (hM'even : Even (Nat.card M'))
    (hM'odd : ∀ g : G, g ∉ M' →
      Odd (Nat.card ((M' ⊓ M'.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    (hmax : ∀ T : Sylow 2 G,
      IsCoatom (Subgroup.normalizer (((T : Subgroup G) : Set G)))) :
    ∃ g : G, M' = M.map (MulAut.conj g).toMonoidHom :=
  Commons.GroupTheory.StronglyEmbedded.exists_conj_eq_of_isStronglyEmbedded M M'
    hMne hMeven hModd hM'ne hM'even hM'odd hmax

/-- **Every involution of `G` lies in a conjugate of a strongly embedded subgroup `M`.** -/
theorem exists_conj_mem_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t : G} (ht : orderOf t = 2) :
    ∃ g : G, t ∈ M.map (MulAut.conj g).toMonoidHom :=
  Commons.GroupTheory.StronglyEmbedded.exists_conj_mem_of_orderOf_eq_two M hMne hMeven hModd ht

/-- **Every involution of `G` lies in a *unique* conjugate of a strongly embedded subgroup `M`.** -/
theorem existsUnique_conj_mem_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t : G} (ht : orderOf t = 2) :
    ∃! H : Subgroup G, (∃ g : G, H = M.map (MulAut.conj g).toMonoidHom) ∧ t ∈ H :=
  Commons.GroupTheory.StronglyEmbedded.existsUnique_conj_mem_of_orderOf_eq_two
    M hMne hMeven hModd ht

/-- **Bender's fusion statement**: the centralizer of an involution `t` is contained in a conjugate
of a strongly embedded subgroup `M` — indeed in the unique conjugate of `M` containing `t`. -/
theorem exists_conj_centralizer_le_of_orderOf_eq_two {G : Type*} [Group G] [Finite G]
    (M : Subgroup G) (hMne : M ≠ ⊤) (hMeven : Even (Nat.card M))
    (hModd : ∀ g : G, g ∉ M →
      Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))))
    {t : G} (ht : orderOf t = 2) :
    ∃ g : G, Subgroup.centralizer ({t} : Set G) ≤ M.map (MulAut.conj g).toMonoidHom :=
  Commons.GroupTheory.StronglyEmbedded.exists_conj_centralizer_le_of_orderOf_eq_two
    M hMne hMeven hModd ht

end Submission
