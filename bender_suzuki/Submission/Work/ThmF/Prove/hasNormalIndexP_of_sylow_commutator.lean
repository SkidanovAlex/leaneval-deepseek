import Mathlib
import Submission.Work.ThmF.Tools.External
import Submission.Work.ThmF.Prove.hasNormalIndexP_of_commutator_le
import Submission.Work.ThmF.Prove.normalizerSubgroupOfEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.hasNormalIndexP_of_sylow_commutator`

Peterfalvi II, Ch. V §3, step (9): the second Hall–Wielandt reduction (on the descent to `N`).

`G` is a finite group, `N ≤ G`, `S ≤ N` a `p`-subgroup whose index in `N` is prime to `p` (so `S`
is a Sylow `p`-subgroup of `N`), `Z ≤ S` normal in `N` with `[S,S] ≤ Z`, and `M ⊴ N_G(S)` of index
`p` containing `Z` — where `N_G(S) ≤ N`.  Then `N` has a normal subgroup of index `p`.

**Proof.**  All the hypotheses of `hasNormalIndexP_of_commutator_le` hold verbatim inside `N`:
`S` is a Sylow `p`-subgroup of `N`, `Z` (viewed in `N`) is normal in `N` and contains `[S,S]`, and
the normalizer `N_N(S)` coincides, element by element, with `N_G(S)` — precisely because
`N_G(S) ≤ N`; hence `M` can be pulled back to a normal subgroup of index `p` of `N_N(S)` containing
`Z`.  Apply the commutator lemma.
-/

set_option linter.unusedVariables false

namespace Work.ThmF.Prove

/-- Peterfalvi II, Ch. V §3, step (9), descent form: if `N ≤ G` contains `N_G(S)`, if `S ≤ N` is a
Sylow `p`-subgroup of `N`, `Z ≤ S` is normal in `N` with `[S,S] ≤ Z`, and `M ⊴ N_G(S)` has index `p`
and contains `Z`, then `N` itself has a normal subgroup of index `p`.

The normalizer `N_N(S)` is identified with `N_G(S)` (via
`Work.ThmF.Prove.normalizerSubgroupOfEquiv`, an identity on underlying elements), so `M` pulls back
to a normal subgroup of index `p` of `N_N(S)` containing `Z`; the second Hall–Wielandt reduction
`hasNormalIndexP_of_commutator_le` then applies inside `N`. -/
theorem hasNormalIndexP_of_sylow_commutator {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hHW : Work.ThmF.HallWielandtProp)
    {N S Z : Subgroup G} (hSN : S ≤ N) (hZleN : Z ≤ N)
    (hZN : (Z.subgroupOf N).Normal) (hZle : Z ≤ S)
    (hSp : IsPGroup p S) (hSidx : ¬ p ∣ S.relIndex N)
    (hNGSle : Subgroup.normalizer (S : Set G) ≤ N)
    (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (M : Subgroup ↥(Subgroup.normalizer (S : Set G)))
    (hMn : M.Normal) (hMidx : M.index = p)
    (hZleM : Z ≤ Subgroup.map (Subgroup.normalizer (S : Set G)).subtype M) :
    Work.ThmF.HasNormalIndexP p ↥N := by
  classical
  -- **(1)** `S` is a Sylow `p`-subgroup of `N`
  have hSpN : IsPGroup p (S.subgroupOf N) := hSp.comap_subtype
  have hSidxN : ¬ p ∣ (S.subgroupOf N).index := hSidx
  let S' : Sylow p ↥N := hSpN.toSylow hSidxN
  -- **(2)** the normalizers `N_N(S)` and `N_G(S)` are the same group
  obtain ⟨e, he, hes⟩ := normalizerSubgroupOfEquiv hSN hNGSle
  have esymm : ∀ y : ↥(Subgroup.normalizer (S : Set G)),
      (e : ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)) →*
        ↥(Subgroup.normalizer (S : Set G))) (e.symm y) = y :=
    fun y => MulEquiv.apply_symm_apply e y
  have hsurj : Function.Surjective
      (e : ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)) →*
        ↥(Subgroup.normalizer (S : Set G))) :=
    fun y => ⟨e.symm y, esymm y⟩
  -- **(3)** pull `M` back to `N_N(S) = N_G(S)`
  let M' : Subgroup ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)) :=
    M.comap (e : ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)) →*
      ↥(Subgroup.normalizer (S : Set G)))
  have hM'n : M'.Normal := Subgroup.Normal.comap hMn _
  have hM'idx : M'.index = p := by
    have h := Subgroup.index_comap_of_surjective M hsurj
    rw [hMidx] at h
    exact h
  -- **(4)** `Z`, `S` and `[S,S]` transport into `N`
  have hZle' : Z.subgroupOf N ≤ (S' : Subgroup ↥N) := Subgroup.subgroupOf_mono N hZle
  have hcomm' : ∀ a ∈ (S' : Subgroup ↥N), ∀ b ∈ (S' : Subgroup ↥N),
      a * b * a⁻¹ * b⁻¹ ∈ Z.subgroupOf N := by
    intro a ha b hb
    have haS : (a : G) ∈ S := Subgroup.mem_subgroupOf.mp ha
    have hbS : (b : G) ∈ S := Subgroup.mem_subgroupOf.mp hb
    have h := hcomm (a : G) haS (b : G) hbS
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using h
  -- **(5)** `Z` lifts into `M'`
  have hZleM' : Z.subgroupOf N ≤
      Subgroup.map (Subgroup.normalizer (S.subgroupOf N : Set ↥N)).subtype M' := by
    intro z hz
    have hzZ : (z : G) ∈ Z := Subgroup.mem_subgroupOf.mp hz
    obtain ⟨m, hmM, hmz⟩ := Subgroup.mem_map.mp (hZleM hzZ)
    refine Subgroup.mem_map.mpr ⟨e.symm m, ?_, ?_⟩
    · show e.symm m ∈ Subgroup.comap (e : ↥(Subgroup.normalizer (S.subgroupOf N : Set ↥N)) →*
        ↥(Subgroup.normalizer (S : Set G))) M
      rw [Subgroup.mem_comap]
      exact (esymm m).symm ▸ hmM
    · refine Subtype.ext ?_
      exact (hes m).trans hmz
  -- **(6)** the commutator lemma in `N`
  exact hasNormalIndexP_of_commutator_le (X := ↥N) hHW S' (Z.subgroupOf N) hZN hZle' hcomm'
    M' hM'n hM'idx hZleM'

end Work.ThmF.Prove
