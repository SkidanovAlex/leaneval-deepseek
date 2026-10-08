import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.Coprime.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.ThreePoints.ThmC

/-!
# Peterfalvi, Appendix I, statement (2)

Let `d` be a prime, `t ∈ M` an element of order `d`, and `X ≤ M` a `d'`-subgroup normalised by
`t`.  For a prime `p`:

(a) every `t`-invariant `p`-subgroup of `X` lies in a `t`-invariant Sylow `p`-subgroup of `X`;
(b) two `t`-invariant Sylow `p`-subgroups of `X` are conjugate by an element of `C_X(t)`.

The mathematical input is the coprime-action Sylow theory of `Submission.Work.Coprime`
(`Work.Coprime.exists_invariant_sylow_ge`, `Work.Coprime.invariant_sylow_conj`), applied to the
cyclic (hence solvable) operator group `A = ⟨t⟩` acting on `↥X` by conjugation.  The lemmas below
translate that abstract formulation into the ambient language of `IsSylowOf` and
`Subgroup.normalizer` used in the statement.
-/

section Transfer

variable {M : Type} [Group M] [Finite M]

/-- If `t` maps `P` into itself then `t` lies in the normaliser of `P` (finiteness upgrades the
containment `t P t⁻¹ ≤ P` to an equality). -/
theorem mem_normalizer_of_mapsTo {t : M} {P : Subgroup M}
    (h : ∀ x ∈ P, t * x * t⁻¹ ∈ P) : t ∈ Subgroup.normalizer (P : Set M) := by
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]

/-- A Sylow `p`-subgroup of `↥X`, viewed inside `M`, is an `IsSylowOf` `p`-subgroup of `X`. -/
theorem sylowMap_isSylowOf {p : ℕ} [Fact p.Prime] {X : Subgroup M} (S : Sylow p ↥X) :
    IsSylowOf p (S.toSubgroup.map X.subtype) X := by
  refine ⟨Subgroup.map_subtype_le S.toSubgroup, IsPGroup.map S.isPGroup' X.subtype, ?_⟩
  intro Q hPQ hQX hQp
  have h1 : S.toSubgroup ≤ Q.subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hPQ (Subgroup.mem_map_of_mem X.subtype hx)
  have h2 : Q.subgroupOf X = S.toSubgroup := S.is_maximal' hQp.comap_subtype h1
  rw [← Subgroup.map_subgroupOf_eq_of_le hQX, h2]

/-- An `IsSylowOf` `p`-subgroup of `X` is a Sylow `p`-subgroup of the group `↥X`. -/
theorem isSylowOf_toSylow {p : ℕ} [Fact p.Prime] {X P : Subgroup M} (hP : IsSylowOf p P X) :
    ∃ S : Sylow p ↥X, (S : Subgroup ↥X) = P.subgroupOf X := by
  have hpP : IsPGroup p ↥(P.subgroupOf X) :=
    IsPGroup.of_equiv hP.2.1 (Subgroup.subgroupOfEquivOfLe hP.1).symm
  obtain ⟨S, hPS⟩ := hpP.exists_le_sylow
  have key : (S : Subgroup ↥X).map X.subtype = P := by
    refine hP.2.2 _ ?_ (Subgroup.map_subtype_le (S : Subgroup ↥X))
      (IsPGroup.map S.isPGroup' X.subtype)
    rw [← Subgroup.map_subgroupOf_eq_of_le hP.1]
    exact Subgroup.map_mono hPS
  refine ⟨S, le_antisymm ?_ hPS⟩
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have : (x : M) ∈ (S : Subgroup ↥X).map X.subtype := Subgroup.mem_map_of_mem X.subtype hx
  rwa [key] at this

/-- If every element of `A` normalises `P` (inside `M`), then `P.subgroupOf X` is `A`-invariant
for the conjugation action of `A` on `↥X`. -/
theorem isInvariant_subgroupOf {A P X : Subgroup M} [FT.Normalizes A X]
    (hA : ∀ a ∈ A, a ∈ Subgroup.normalizer (P : Set M)) :
    FT.IsInvariant A (P.subgroupOf X) := by
  refine ⟨fun a => Subgroup.ext (fun x => ?_)⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    FT.conj_smul_coe]
  simp only [Subgroup.coe_inv, inv_inv]
  exact (Subgroup.mem_normalizer_iff''.mp (hA (a : M) a.2) (x : M)).symm

/-- An `A`-invariant Sylow `p`-subgroup of `↥X` is normalised in `M` by every element of `A`. -/
theorem mapsTo_of_invariant_sylow {p : ℕ} [Fact p.Prime] {X A : Subgroup M} [FT.Normalizes A X]
    (S : Sylow p ↥X) (hS : ∀ a : A, a • S = S) (a : A) :
    ∀ x ∈ S.toSubgroup.map X.subtype, (a : M) * x * (a : M)⁻¹ ∈ S.toSubgroup.map X.subtype := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hcoe : (a • S.toSubgroup : Subgroup ↥X) = S.toSubgroup := by
    have h := congrArg (fun S' : Sylow p ↥X => (S' : Subgroup ↥X)) (hS a)
    simpa [Sylow.pointwise_smul_def] using h
  have hy' : a • y ∈ S.toSubgroup := by
    have h2 : a • y ∈ (a • S.toSubgroup : Subgroup ↥X) :=
      (Subgroup.mem_smul_pointwise_iff_exists _ a _).mpr ⟨y, hy, rfl⟩
    rwa [hcoe] at h2
  have hconj : (a : M) * (y : M) * (a : M)⁻¹ = ((a • y : ↥X) : M) :=
    (FT.conj_smul_coe A X a y).symm
  show (a : M) * (y : M) * (a : M)⁻¹ ∈ S.toSubgroup.map X.subtype
  rw [hconj]
  exact Subgroup.mem_map_of_mem X.subtype hy'

/-- Conjugation on `↥X` commutes with the inclusion `X ↪ M`. -/
theorem subtype_conj_apply (X : Subgroup M) (c x : ↥X) :
    X.subtype ((MulAut.conj c) x) = (MulAut.conj (c : M)) (X.subtype x) := by
  simp [MulAut.conj_apply]

/-- Conjugation of a Sylow `p`-subgroup of `↥X` by `c : ↥X`, transported to `M`. -/
theorem sylow_conj_transfer {p : ℕ} {X : Subgroup M} {P Q : Sylow p ↥X} {c : ↥X}
    (hc : Q = MulAut.conj c • P) :
    Q.toSubgroup.map X.subtype
      = (P.toSubgroup.map X.subtype).map (MulAut.conj (c : M)).toMonoidHom := by
  have hcoe : (Q : Subgroup ↥X) = (MulAut.conj c) • (P : Subgroup ↥X) := by
    have h := congrArg (fun S : Sylow p ↥X => (S : Subgroup ↥X)) hc
    simpa [Sylow.pointwise_smul_def] using h
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨q, hq, hqy⟩ := hy
    rw [hcoe] at hq
    obtain ⟨p, hp, hpq⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists q (MulAut.conj c) (P : Subgroup ↥X)).mp hq
    rw [Subgroup.mem_map]
    refine ⟨X.subtype p, Subgroup.mem_map_of_mem X.subtype hp, ?_⟩
    rw [← hqy, ← hpq]
    exact subtype_conj_apply X c p
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rw [Subgroup.mem_map] at hz
    obtain ⟨p, hp, hpz⟩ := hz
    refine ⟨(MulAut.conj c) p, ?_, ?_⟩
    · rw [hcoe]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ (MulAut.conj c) _).mpr ⟨p, hp, rfl⟩
    · rw [subtype_conj_apply, hpz]
      exact hzy

end Transfer

/-- **Peterfalvi I App. I (2).**  Let `d` be a prime, `t ∈ M` of order `d`, and `X` a subgroup of
the finite group `M` of order prime to `d` normalised by `t`.  Then (a) every `p`-subgroup `P₀ ≤ X`
normalised by `t` is contained in a `p`-Sylow `P` of `X` normalised by `t`, and (b) any two
`p`-Sylows `P`, `Q` of `X` normalised by `t` are conjugate by an element of `C_X(t)`.

(`Work.ThreePoints.ThmC.IsSylowOf p P X` means: `P ≤ X`, `P` is a `p`-group, and no strictly larger
`p`-subgroup of `X` contains `P`; see `Submission/Work/ThreePoints/ThmC/Defs.lean`.) -/
theorem app1_2 {M : Type} [Group M] [Finite M] {d : ℕ} (hd : d.Prime) {t : M}
    (ht : orderOf t = d) {X : Subgroup M} (hcop : Nat.Coprime (Nat.card X) d)
    (hnt : t ∈ Subgroup.normalizer (X : Set M)) {p : ℕ} (hp : p.Prime) :
    (∀ P₀ : Subgroup M, P₀ ≤ X → IsPGroup p P₀ → t ∈ Subgroup.normalizer (P₀ : Set M) →
        ∃ P : Subgroup M, P₀ ≤ P ∧ Work.ThreePoints.ThmC.IsSylowOf p P X ∧
          t ∈ Subgroup.normalizer (P : Set M)) ∧
      (∀ P Q : Subgroup M, Work.ThreePoints.ThmC.IsSylowOf p P X →
        Work.ThreePoints.ThmC.IsSylowOf p Q X →
        t ∈ Subgroup.normalizer (P : Set M) → t ∈ Subgroup.normalizer (Q : Set M) →
        ∃ v ∈ X ⊓ Subgroup.centralizer ({t} : Set M),
          Submission.Blueprint.conj v P = Q) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set A : Subgroup M := Subgroup.zpowers t with hAdef
  have htA : t ∈ A := by rw [hAdef]; exact Subgroup.mem_zpowers t
  have hAle : A ≤ Subgroup.normalizer (X : Set M) := by
    rw [hAdef]; exact Subgroup.zpowers_le.mpr hnt
  haveI hNAX : FT.Normalizes A X := ⟨hAle⟩
  have hcardA : Nat.card ↥A = d := by rw [hAdef, Nat.card_zpowers, ht]
  have hcopA : (Nat.card ↥A).Coprime (Nat.card ↥X) := by rw [hcardA]; exact hcop.symm
  have hsol : Group.IsSolvable ↥A ∨ Group.IsSolvable ↥X := by
    left
    refine Group.isSolvable_of_comm fun a b => ?_
    apply Subtype.ext
    show (a : M) * (b : M) = (b : M) * (a : M)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (show (a : M) ∈ Subgroup.zpowers t from by
      rw [← hAdef]; exact a.2)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (show (b : M) ∈ Subgroup.zpowers t from by
      rw [← hAdef]; exact b.2)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  refine ⟨?_, ?_⟩
  · -- (a) an invariant `p`-subgroup lies in an invariant Sylow
    intro P₀ hP₀X hP₀p hP₀n
    have hAnorm : ∀ a ∈ A, a ∈ Subgroup.normalizer (P₀ : Set M) := by
      have hle : A ≤ Subgroup.normalizer (P₀ : Set M) := by
        rw [hAdef]; exact Subgroup.zpowers_le.mpr hP₀n
      exact fun a ha => hle ha
    haveI hPI : FT.IsInvariant A (P₀.subgroupOf X) := isInvariant_subgroupOf hAnorm
    have hpP₀' : IsPGroup p ↥(P₀.subgroupOf X) :=
      IsPGroup.of_equiv hP₀p (Subgroup.subgroupOfEquivOfLe hP₀X).symm
    obtain ⟨S, hPS, hS⟩ :=
      Work.Coprime.exists_invariant_sylow_ge A (G := ↥X) hcopA hsol p (P₀.subgroupOf X) hpP₀'
    refine ⟨S.toSubgroup.map X.subtype, ?_, sylowMap_isSylowOf S, ?_⟩
    · rw [← Subgroup.map_subgroupOf_eq_of_le hP₀X]
      exact Subgroup.map_mono hPS
    · exact mem_normalizer_of_mapsTo (mapsTo_of_invariant_sylow S hS ⟨t, htA⟩)
  · -- (b) invariant Sylows are conjugate in `C_X(t)`
    intro P Q hP hQ hPn hQn
    have hPnA : ∀ a ∈ A, a ∈ Subgroup.normalizer (P : Set M) := by
      have hle : A ≤ Subgroup.normalizer (P : Set M) := by
        rw [hAdef]; exact Subgroup.zpowers_le.mpr hPn
      exact fun a ha => hle ha
    have hQnA : ∀ a ∈ A, a ∈ Subgroup.normalizer (Q : Set M) := by
      have hle : A ≤ Subgroup.normalizer (Q : Set M) := by
        rw [hAdef]; exact Subgroup.zpowers_le.mpr hQn
      exact fun a ha => hle ha
    haveI hPI : FT.IsInvariant A (P.subgroupOf X) := isInvariant_subgroupOf hPnA
    haveI hQI : FT.IsInvariant A (Q.subgroupOf X) := isInvariant_subgroupOf hQnA
    obtain ⟨Ps, hPseq⟩ := isSylowOf_toSylow hP
    obtain ⟨Qs, hQseq⟩ := isSylowOf_toSylow hQ
    have hPsinv : ∀ a : ↥A, a • Ps = Ps := by
      intro a
      apply Sylow.ext
      rw [Sylow.pointwise_smul_def, hPseq]
      exact hPI.smul_eq_self a
    have hQsinv : ∀ a : ↥A, a • Qs = Qs := by
      intro a
      apply Sylow.ext
      rw [Sylow.pointwise_smul_def, hQseq]
      exact hQI.smul_eq_self a
    obtain ⟨c, hc, hcQ⟩ :=
      Work.Coprime.invariant_sylow_conj A (G := ↥X) hcopA hsol p hPsinv hQsinv
    refine ⟨(c : M), Subgroup.mem_inf.mpr ⟨c.2, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (⟨t, htA⟩ : ↥A) • c = c := (FT.mem_fixedPoints.mp hc) ⟨t, htA⟩
      have h2 : t * (c : M) * t⁻¹ = (c : M) := by
        have := congrArg (Subtype.val) h1
        simpa [FT.conj_smul_coe] using this
      have h3 : t * (c : M) = (c : M) * t := by
        have := congrArg (· * t) h2
        simpa [mul_assoc] using this
      exact h3.symm
    · have hQmap : Qs.toSubgroup.map X.subtype = Q := by
        rw [hQseq, Subgroup.map_subgroupOf_eq_of_le hQ.1]
      have hPmap : Ps.toSubgroup.map X.subtype = P := by
        rw [hPseq, Subgroup.map_subgroupOf_eq_of_le hP.1]
      have htr := sylow_conj_transfer hcQ
      rw [hQmap, hPmap] at htr
      show P.map (MulAut.conj (c : M)).toMonoidHom = Q
      exact htr.symm

end Work.ThreePoints.ThmC
