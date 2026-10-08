import Mathlib
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs
import Submission.Work.ThmF.ChV3.Prove.S4_centD_not_stronglyReal
import Submission.Work.ThmF.ChV3.Prove.no_conj_le_T_101
import Submission.Work.ThmF.ChV3.Prove.exists_AT_inter_orb_101
import Submission.Work.ThmF.ChV3.Prove.AT_subset_orb_of_witness_101

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.orb_eq_AT_union_101`

Peterfalvi II Ch. V §3, step (12), case (10-1): the `N_G(R)`-orbit of `P` is `𝒜 ∪ {P}`, where
`𝒜 = AT R T P` is the set of subgroups `A ≤ R` of order `|P|` with `A ⊄ T` and `A ≠ P`
(`OrbitCountDefs.lean`).  This is the set-theoretic half of the orbit count of (12); the counting
half is `orbit_count_101`.

Here `P` is the prime-order subgroup `P ≤ centD H t` of the standing context `CtxF H Q t s r P`,
and `R = T ⊔ P` with `T ⊓ P = ⊥` is the step-(11) object (`Step11Out`), abelian, with `C_Q(P)`
regular on `𝒜` (`Step11Out.reg`).

## The two inclusions

* `orb P (NG R) ⊆ AT R T P ∪ {P}`.  For `g ∈ N_G(R)` the subgroup `cj g P` satisfies
  `cj g P ≤ cj g R = R` (so `cj g P ≤ R` as `P ≤ T ⊔ P = R`) and `Nat.card (cj g P) = Nat.card P`;
  and `cj g P ⊄ T` by `no_conj_le_T_101` (every element of `T` is inverted by the involution `s`,
  hence strongly real, whereas no non-trivial element of `V = centD H t ≥ P` is strongly real nor
  conjugate to one — Ch. V §2 Lemma 4).  So `cj g P` is either `P` itself or a member of `𝒜`.

* `AT R T P ⊆ orb P (NG R)`.  `exists_AT_inter_orb_101` (from `hRn`, `hNG`, `hNGne` and the
  previous bullet) supplies a witness `A₀ ∈ 𝒜` lying in the orbit, and
  `AT_subset_orb_of_witness_101` spreads it over all of `𝒜`: `C_Q(P)` is sharply transitive on `𝒜`
  (`h11.reg`) and `C_Q(P) ≤ C_G(P) ≤ N_G(R)` (`hRn`), so every `A ∈ 𝒜` is `cj (y * g₀) P` for some
  `y ∈ C_Q(P)`.  Finally `P = cj 1 P` lies in the orbit.

The only use of `hC4` is through `no_conj_le_T_101`, i.e. through Ch. V §2 Lemma 4.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

theorem orb_eq_AT_union_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P R T : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P)
    (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (hNG : Work.ThmF.ChV3.NG P = Work.ThmF.ChV3.CG P)
    (h11 : Work.ThmF.ChV3.Step11Out H Q t P R T)
    (hsT : ∀ x ∈ T, s * x * s⁻¹ = x⁻¹)
    (hNGne : Work.ThmF.ChV3.NG R ≠ Work.ThmF.ChV3.NG P) :
    Work.ThmF.ChV3.Prove.orb P (Work.ThmF.ChV3.NG R) =
      Work.ThmF.ChV3.Prove.AT R T P ∪ {P} := by
  classical
  -- `P ≤ R`, since `R = T ⊔ P` (step (11))
  have hPR : P ≤ R := by rw [← h11.TPR]; exact le_sup_right
  -- no conjugate of `P` lies in `T`
  have hno : ∀ g : G, ¬ cj g P ≤ T := no_conj_le_T_101 hC4 c hsT
  -- a witness `A₀ ∈ 𝒜` which already lies in the orbit
  obtain ⟨A0, hA0AT, hA0orb⟩ := exists_AT_inter_orb_101 hRn hNG hPR hno hNGne
  -- sharp transitivity of `C_Q(P) ≤ N_G(R)` on `𝒜` spreads the witness over all of `𝒜`
  have hATsub : AT R T P ⊆ orb P (NG R) := AT_subset_orb_of_witness_101 hRn h11 hA0AT hA0orb
  refine Set.Subset.antisymm ?_ ?_
  · -- the orbit lies in `𝒜 ∪ {P}`
    rintro A ⟨g, hgN, rfl⟩
    rw [Set.mem_union, Set.mem_singleton_iff]
    by_cases h : cj g P = P
    · exact Or.inr h
    · exact Or.inl ⟨by simpa [show cj g R = R from (cj_eq_self_iff g R).mpr hgN] using cj_mono hPR g,
        card_cj g P, hno g, h⟩
  · -- `𝒜 ∪ {P}` lies in the orbit (`P = cj 1 P`)
    intro A hA
    rw [Set.mem_union, Set.mem_singleton_iff] at hA
    rcases hA with hAAT | hAP
    · exact hATsub hAAT
    · rw [hAP]
      exact ⟨1, one_mem _, (cj_one P).symm⟩

end Work.ThmF.ChV3.Prove
