import Mathlib
import Submission.Work.DoubleTransitivity.App1.Defs
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.exists_invariant_sylow
import Submission.Work.Coprime.invariant_sylow_conj
import Submission.Work.DoubleTransitivity.App1.isSylowSubgroupOf_map_subtype

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi, Appendix I (2): `t`-invariant Sylow subgroups

**Peterfalvi, Appendix I (2)**, in the internal form used downstream: `M` is a finite group, `d`
a prime, `t ∈ M` an element of order `d`, and `X ≤ M` a `d'`-subgroup normalised by `t`
(`t ∈ N_M(X)`). Then

* `X` has a `p`-Sylow normalised by `t`,
* two `p`-Sylows of `X` normalised by `t` are conjugate by an element of `V = C_X(t)`.

The paper's proof of the first point is an orbit count on `Syl_p(X)`, whose cardinality is prime
to `d`; the second uses Sylow inside `N_X(P)⟨t⟩`.  Formally we instead recognise this as the
*coprime action* theorem for the conjugation action of the cyclic group `A = ⟨t⟩` (of order `d`,
prime to `|X|`, and solvable) on the group `X`:

* `Work.Coprime.exists_invariant_sylow` (Glauberman's fixed point lemma on `Syl_p(X)`) gives a
  `t`-invariant `P : Sylow p ↥X`;
* `Work.Coprime.invariant_sylow_conj` — the `C_X(t)`-conjugacy of invariant Sylows, which uses
  the vanishing of `H¹(A, −)`.

The remaining work is the translation between the internal objects `P : Sylow p ↥X` and the
ambient subgroups of `G` used by the statement: `conjAut` (conjugation by an element of the
normalizer, restricted to `X`) and its naturality lemmas
(`conj_map_subtype`, `conjAut_subgroupOf`), and the two Sylow bridges.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Pointwise
open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity.App1

variable {G : Type} [Group G]

/-! ## Conjugation by an element of the normalizer -/

/-- Conjugation by an element `t` of `N_G(X)`, restricted to the subgroup `X`. -/
noncomputable def conjAut (X : Subgroup G) (t : G)
    (ht : t ∈ Subgroup.normalizer (X : Set G)) : MulAut ↥X where
  toFun x := ⟨t * (x : G) * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht (x : G)).mp x.2⟩
  invFun x := ⟨t⁻¹ * (x : G) * t, by
    have h : t⁻¹ * (x : G) * (t⁻¹)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) (x : G)).mp x.2
    simpa using h⟩
  left_inv x := Subtype.ext (by group)
  right_inv x := Subtype.ext (by group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[simp]
theorem conjAut_apply (X : Subgroup G) (t : G) (ht : t ∈ Subgroup.normalizer (X : Set G))
    (x : ↥X) : ((conjAut X t ht x : ↥X) : G) = t * (x : G) * t⁻¹ := rfl

/-- The pointwise action of an automorphism on subgroups is `Subgroup.map` by that automorphism. -/
theorem smul_eq_map {M : Type*} [Group M] (a : MulAut M) (S : Subgroup M) :
    a • S = S.map a.toMonoidHom := by
  rw [Subgroup.pointwise_smul_def, MulDistribMulAction.toMonoidEnd_apply]
  exact congrArg (Subgroup.map · S) (MonoidHom.ext fun z => by
    simp [MulDistribMulAction.toMonoidHom_apply])

/-- The pointwise action of the automorphism attached to `a` is the action of `a`. -/
theorem smul_eq_toMulAut_smul {A M : Type*} [Group A] [Group M] [MulDistribMulAction A M]
    (a : A) (S : Subgroup M) : MulDistribMulAction.toMulAut A M a • S = a • S := by
  rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def,
    MulDistribMulAction.toMonoidEnd_apply]
  exact congrArg (Subgroup.map · S) (MonoidHom.ext fun z => by
    simp [MulDistribMulAction.toMulEquiv_apply, MulDistribMulAction.toMonoidHom_apply])

/-- `gHg⁻¹` as a pointwise action (the challenge's `conj` is `Subgroup.map` by `MulAut.conj`). -/
theorem conj_eq_smul (t : G) (H : Subgroup G) :
    Submission.Blueprint.conj t H = MulAut.conj t • H := by
  rw [Subgroup.pointwise_smul_def]; rfl

theorem conjAut_smul_eq_map (X : Subgroup G) (t : G)
    (ht : t ∈ Subgroup.normalizer (X : Set G)) (S : Subgroup ↥X) :
    conjAut X t ht • S = S.map (conjAut X t ht).toMonoidHom :=
  smul_eq_map (conjAut X t ht) S

/-- **Naturality of conjugation.**  Conjugating a subgroup of `X` (inside `X`, by an element of
`N_G(X)`) and then pushing it into `G` agrees with conjugating its image in `G`. -/
theorem conj_map_subtype (X : Subgroup G) (t : G) (ht : t ∈ Subgroup.normalizer (X : Set G))
    (S : Subgroup ↥X) :
    Submission.Blueprint.conj t (S.map X.subtype)
      = (S.map (conjAut X t ht).toMonoidHom).map X.subtype := by
  rw [Submission.Blueprint.conj, Subgroup.map_map, Subgroup.map_map]
  exact congrArg (Subgroup.map · S) (MonoidHom.ext fun z => by
    simp [conjAut_apply, MulAut.conj_apply])

/-- The image of a subgroup of `X` under `X.subtype`, intersected back with `X`, is itself. -/
theorem subgroupOf_map_subtype_eq (X : Subgroup G) (H : Subgroup ↥X) :
    (H.map X.subtype).subgroupOf X = H := by
  rw [← Subgroup.comap_subtype]
  exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective H

/-- **Naturality of conjugation, `subgroupOf` form**: conjugating `Q ≤ X` in `G` and restricting
to `X` is the conjugation action on `Q` viewed inside `X`. -/
theorem conjAut_subgroupOf (X : Subgroup G) (t : G) (ht : t ∈ Subgroup.normalizer (X : Set G))
    (Q : Subgroup G) (hQ : Q ≤ X) :
    (Submission.Blueprint.conj t Q).subgroupOf X = conjAut X t ht • (Q.subgroupOf X) := by
  have h := conj_map_subtype X t ht (Q.subgroupOf X)
  rw [Subgroup.map_subgroupOf_eq_of_le hQ, ← conjAut_smul_eq_map] at h
  rw [h, subgroupOf_map_subtype_eq]

/-- The conjugation action of `A` on `X` (via `FT.Normalizes`) coincides with `conjAut`. -/
theorem conjAut_eq_toMulAut {X A : Subgroup G} [hA : FT.Normalizes A X] (a : A) :
    conjAut X (a : G) (hA.le_normalizer a.2) = MulDistribMulAction.toMulAut A ↥X a := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rw [conjAut_apply, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
  exact (FT.conj_smul_coe A X a x).symm

/-- Pushing a conjugation inside `X` down to `G`: conjugating by `x : ↥X` in `X` and then
mapping to `G` is conjugation by `(x : G)` in `G`. -/
theorem map_conj_eq (X : Subgroup G) (x : ↥X) (S : Subgroup ↥X) :
    (S.map (MulAut.conj x).toMonoidHom).map X.subtype
      = (S.map X.subtype).map (MulAut.conj (x : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  exact congrArg (Subgroup.map · S) (MonoidHom.ext fun z => by
    simp [MulAut.conj_apply])

/-! ## Transporting Sylow subgroups between `X` and `↥X` -/

/-- A `p`-subgroup of `X` whose index in `X` is prime to `p` is (the image of) a Sylow
`p`-subgroup of `↥X`. -/
theorem sylow_subgroupOf_of_isSylowSubgroupOf {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {p : ℕ} (hp : p.Prime) {Q : Subgroup G} (hQ : IsSylowSubgroupOf p Q X) :
    ∃ S : Sylow p ↥X, (S : Subgroup ↥X) = Q.subgroupOf X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p (Q.subgroupOf X) := hQ.2.1.comap_subtype (K := X)
  exact ⟨hpg.toSylow hQ.2.2, IsPGroup.toSylow_coe hpg hQ.2.2⟩

/-- The fixed points of the conjugation action of `A` on `X` are centralised by every element
of `A`; in particular `C_X(A) ≤ C_X(t)` for `t ∈ A`. -/
theorem fixedPoints_conjAction_le_centralizerIn {G : Type} [Group G] {X A : Subgroup G}
    [FT.Normalizes A X] {t : G} (ht : t ∈ A) :
    (FT.fixedPoints A X).map X.subtype ≤ centralizerIn X t := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
  rw [FT.mem_fixedPoints] at hc
  refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : (⟨t, ht⟩ : A) • c = c := hc ⟨t, ht⟩
  have h2 : (t : G) * (c : G) * (t : G)⁻¹ = (c : G) := by
    simpa using congrArg Subtype.val h1
  calc (c : G) * t = t * (c : G) * t⁻¹ * t := by rw [h2]
    _ = t * c := by group

/-! ## Peterfalvi, Appendix I (2) -/

theorem app1_2 {G : Type} [Group G] [Finite G] {X : Subgroup G} {t : G} {d : ℕ}
    (hp : d.Prime) (ht : orderOf t = d) (hcop : Nat.Coprime d (Nat.card ↥X))
    (hnorm : t ∈ Subgroup.normalizer (X : Set G)) {p : ℕ} (hpp : p.Prime) :
    ∃ P : Subgroup G, IsSylowSubgroupOf p P X ∧ t ∈ Subgroup.normalizer (P : Set G) ∧
      ∀ Q : Subgroup G, IsSylowSubgroupOf p Q X → t ∈ Subgroup.normalizer (Q : Set G) →
        ∃ v ∈ centralizerIn X t, Submission.Blueprint.conj v P = Q := by
  classical
  haveI : Fact p.Prime := ⟨hpp⟩
  -- the conjugation action of the cyclic group `A = ⟨t⟩` on `X`
  haveI hA : FT.Normalizes (Subgroup.zpowers t) X := ⟨Subgroup.zpowers_le.mpr hnorm⟩
  have hcopA : (Nat.card ↥(Subgroup.zpowers t)).Coprime (Nat.card ↥X) := by
    rw [Nat.card_zpowers, ht]; exact hcop
  -- Glauberman's fixed point lemma for the coprime action of `A` on `Syl_p(X)`
  obtain ⟨P, hPinv⟩ :=
    Work.Coprime.exists_invariant_sylow ↥(Subgroup.zpowers t) hcopA (Or.inl inferInstance) p
  -- `t` alone already normalises `P` (inside `X`)
  have hPsmul : conjAut X t hnorm • (P : Subgroup ↥X) = (P : Subgroup ↥X) := by
    have h2 : (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) • (P : Subgroup ↥X)
        = (P : Subgroup ↥X) := by
      have h3 := congrArg (fun S : Sylow p ↥X => (S : Subgroup ↥X))
        (hPinv ⟨t, Subgroup.mem_zpowers t⟩)
      rwa [Sylow.pointwise_smul_def] at h3
    rw [← smul_eq_toMulAut_smul,
      ← conjAut_eq_toMulAut (a := (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)))] at h2
    exact h2
  refine ⟨(P : Subgroup ↥X).map X.subtype, isSylowSubgroupOf_map_subtype hpp P, ?_, ?_⟩
  · -- `t` normalises the image of `P` in `G`
    have hfix : Submission.Blueprint.conj t ((P : Subgroup ↥X).map X.subtype)
        = (P : Subgroup ↥X).map X.subtype := by
      rw [conj_map_subtype (X := X) (t := t) (ht := hnorm) (S := (P : Subgroup ↥X)),
        ← conjAut_smul_eq_map, hPsmul]
    exact (conj_eq_self_iff_mem_normalizer t ((P : Subgroup ↥X).map X.subtype)).mp hfix
  · intro Q hQ hQt
    -- `Q` is the image of a `t`-invariant Sylow of `↥X`
    obtain ⟨Q', hQ'⟩ := sylow_subgroupOf_of_isSylowSubgroupOf hpp hQ
    have hQinv : ∀ a : ↥(Subgroup.zpowers t), a • Q' = Q' := by
      intro a
      apply Sylow.ext
      rw [Sylow.pointwise_smul_def, hQ']
      have ha : (a : G) ∈ Subgroup.normalizer (Q : Set G) :=
        Subgroup.zpowers_le.mpr hQt a.2
      have hconj : Submission.Blueprint.conj (a : G) Q = Q :=
        (conj_eq_self_iff_mem_normalizer (a : G) Q).mpr ha
      calc a • (Q.subgroupOf X)
          = MulDistribMulAction.toMulAut ↥(Subgroup.zpowers t) ↥X a • (Q.subgroupOf X) := by
            rw [smul_eq_toMulAut_smul]
        _ = conjAut X (a : G) (hA.le_normalizer a.2) • (Q.subgroupOf X) := by
            rw [conjAut_eq_toMulAut]
        _ = (Submission.Blueprint.conj (a : G) Q).subgroupOf X :=
            (conjAut_subgroupOf X (a : G) (hA.le_normalizer a.2) Q hQ.1).symm
        _ = Q.subgroupOf X := by rw [hconj]
    -- the two invariant Sylows are conjugate by `C_X(A) ≤ C_X(t)`
    obtain ⟨c, hc, hcQ⟩ :=
      Work.Coprime.invariant_sylow_conj ↥(Subgroup.zpowers t) hcopA (Or.inl inferInstance) p
        hPinv hQinv
    refine ⟨(c : G), fixedPoints_conjAction_le_centralizerIn (A := Subgroup.zpowers t) (t := t)
      (Subgroup.mem_zpowers t) (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩), ?_⟩
    -- transport the conjugacy `Q' = c P c⁻¹` back to `G`
    have h1 : (Q' : Subgroup ↥X) = MulAut.conj c • (P : Subgroup ↥X) := by
      rw [hcQ, Sylow.pointwise_smul_def]
    have h2 : Q.subgroupOf X = (P : Subgroup ↥X).map (MulAut.conj c).toMonoidHom := by
      rw [← hQ', h1, smul_eq_map]
    have h3 := congrArg (Subgroup.map X.subtype) h2
    rw [Subgroup.map_subgroupOf_eq_of_le hQ.1, map_conj_eq] at h3
    exact h3.symm

end Work.DoubleTransitivity.App1
