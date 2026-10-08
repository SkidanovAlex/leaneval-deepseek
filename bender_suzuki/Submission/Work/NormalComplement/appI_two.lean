/-
# Appendix I, statement (2): Sylow theory for a prime-order operator

Peterfalvi, *Le théorème de Bender–Suzuki I*, Appendix I, statement (2).

Let `X` be a finite subgroup of `G`, `t ∈ G` an element of prime order `d` normalising `X`, with
`(d, |X|) = 1`.  Then:

* there exists a `t`-invariant Sylow `p`-subgroup of `X`;
* any two `t`-invariant Sylow `p`-subgroups of `X` are conjugate by an element of `C_X(t)`;
* every `t`-invariant `p`-subgroup of `X` lies in a `t`-invariant Sylow `p`-subgroup of `X`.

The coprime action of `A = ⟨t⟩` (a cyclic, hence solvable, group) on `↥X` is provided by
`Submission/Work/Coprime/`, where the corresponding Sylow statements are proved
(`Work.Coprime.exists_invariant_sylow`, `Work.Coprime.exists_invariant_sylow_ge`,
`Work.Coprime.invariant_sylow_conj`, via Glauberman's fixed point lemma).  The work here is the
translation between Mathlib's `Sylow p ↥X` and the ambient notion
`Work.NormalComplement.IsSylowIn p · X`, together with the identification of the conjugation
action on `↥X` with conjugation in `G`.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.Coprime.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-! ## Conjugation and normalizers -/

/-- For finite `G`, if `t` maps `X` into itself then it maps it onto itself; phrased as an
equality of subgroups. -/
lemma map_conj_eq_of_normalizedBy {t : G} {P : Subgroup G} (h : NormalizedBy t P) :
    Subgroup.map (MulAut.conj t).toMonoidHom P = P := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]

/-- `NormalizedBy t P` says that `t` lies in the normalizer of `P`. -/
lemma mem_normalizer_of_normalizedBy {t : G} {P : Subgroup G} (h : NormalizedBy t P) :
    t ∈ Subgroup.normalizer (P : Set G) := by
  have hmap := map_conj_eq_of_normalizedBy h
  rw [Subgroup.mem_normalizer_iff]
  refine fun n => ⟨fun hn => h n hn, fun hn => ?_⟩
  have hle : P ≤ Subgroup.map (MulAut.conj t).toMonoidHom P := hmap.ge
  have hy : t * n * t⁻¹ ∈ Subgroup.map (MulAut.conj t).toMonoidHom P := hle hn
  rw [Subgroup.mem_map] at hy
  obtain ⟨x, hx, hxeq⟩ := hy
  have hxeq' : t * x * t⁻¹ = t * n * t⁻¹ := by simpa [MulAut.conj_apply] using hxeq
  have hxn : x = n := mul_left_cancel (mul_right_cancel hxeq')
  rw [← hxn]
  exact hx

/-! ## Transfer between `Sylow p ↥X` and `IsSylowIn p · X` -/

/-- A Sylow `p`-subgroup of `↥X`, viewed as a subgroup of `G`, is a Sylow `p`-subgroup of `X` in
the ambient sense. -/
lemma sylow_toSubgroup_isSylowIn {p : ℕ} [Fact p.Prime] {X : Subgroup G} (S : Sylow p ↥X) :
    IsSylowIn p (S.toSubgroup.map X.subtype) X := by
  refine ⟨IsPGroup.map S.isPGroup' X.subtype, Subgroup.map_subtype_le S.toSubgroup, ?_⟩
  have h1 : (S.toSubgroup.map X.subtype).subgroupOf X = S.toSubgroup := by
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
  rw [h1]
  exact Sylow.not_dvd_index S

/-- An `A`-invariant Sylow subgroup of `↥X` (with `A` normalising `X`) is normalised in `G` by
every element of `A`. -/
lemma normalizedBy_map_subtype_of_invariant {p : ℕ} [Fact p.Prime] {X A : Subgroup G}
    [FT.Normalizes A X] (S : Sylow p ↥X) (hS : ∀ a : A, a • S = S) (a : A) :
    NormalizedBy (a : G) (S.toSubgroup.map X.subtype) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hcoe : (a • S.toSubgroup : Subgroup ↥X) = S.toSubgroup := by
    have h := congrArg (fun S' : Sylow p ↥X => (S' : Subgroup ↥X)) (hS a)
    simpa [Sylow.pointwise_smul_def] using h
  have hy' : a • y ∈ S.toSubgroup := by
    have h2 : a • y ∈ (a • S.toSubgroup : Subgroup ↥X) :=
      (Subgroup.mem_smul_pointwise_iff_exists _ a _).mpr ⟨y, hy, rfl⟩
    rwa [hcoe] at h2
  have hconj : (a : G) * (y : G) * (a : G)⁻¹ = ((a • y : ↥X) : G) :=
    (FT.conj_smul_coe A X a y).symm
  show (a : G) * (y : G) * (a : G)⁻¹ ∈ S.toSubgroup.map X.subtype
  rw [hconj]
  exact Subgroup.mem_map_of_mem X.subtype hy'

/-- If every element of `A` normalizes `P`, then `P.subgroupOf X` is `A`-invariant (for the
conjugation action of `A` on `↥X`). -/
lemma isInvariant_subgroupOf {A P X : Subgroup G} [FT.Normalizes A X]
    (hA : ∀ a ∈ A, a ∈ Subgroup.normalizer (P : Set G)) :
    FT.IsInvariant A (P.subgroupOf X) := by
  refine ⟨fun a => Subgroup.ext (fun x => ?_)⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    FT.conj_smul_coe]
  simp only [Subgroup.coe_inv, inv_inv]
  exact (Subgroup.mem_normalizer_iff''.mp (hA (a : G) a.2) (x : G)).symm

/-- Conjugation on `↥X` commutes with the inclusion `X ↪ G`. -/
lemma subtype_conj_apply (X : Subgroup G) (c p : ↥X) :
    X.subtype ((MulAut.conj c) p) = (MulAut.conj (c : G)) (X.subtype p) := by
  simp [MulAut.conj_apply]

/-- The map `S ↦ S.map X.subtype` sends conjugation of Sylow subgroups of `↥X` by `c : ↥X` to
conjugation of the corresponding subgroups of `G` by `c`. -/
lemma sylow_conj_transfer {p : ℕ} {X : Subgroup G} {P Q : Sylow p ↥X} {c : ↥X}
    (hc : Q = MulAut.conj c • P) :
    Q.toSubgroup.map X.subtype
      = (P.toSubgroup.map X.subtype).map (MulAut.conj (c : G)).toMonoidHom := by
  have hcoe : (Q : Subgroup ↥X) = (MulAut.conj c) • (P : Subgroup ↥X) := by
    have h := congrArg (fun S : Sylow p ↥X => (S : Subgroup ↥X)) hc
    simpa [Sylow.pointwise_smul_def] using h
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨q, hq, hqy⟩ := hy
    rw [hcoe] at hq
    obtain ⟨p, hp, hpq⟩ := (Subgroup.mem_smul_pointwise_iff_exists q (MulAut.conj c)
      (P : Subgroup ↥X)).mp hq
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
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨p, hp, rfl⟩
    · rw [subtype_conj_apply, hpz]
      exact hzy

/-- Sylow subgroups of `X` in the ambient sense are Sylow subgroups of `↥X`. -/
lemma toSylow_subgroupOf {p : ℕ} [Fact p.Prime] {X : Subgroup G} {P : Subgroup G}
    (hP : IsSylowIn p P X) :
    ((IsPGroup.toSylow (p := p) (P := P.subgroupOf X)
        (IsPGroup.of_equiv hP.1 (Subgroup.subgroupOfEquivOfLe hP.2.1).symm) hP.2.2 :
      Subgroup ↥X) = P.subgroupOf X) :=
  IsPGroup.toSylow_coe _ _

/-! ## Appendix I (2) -/

theorem appI_two {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : d.Prime) {t : G}
    (ht : orderOf t = d) {X : Subgroup G} (htX : Work.NormalComplement.NormalizedBy t X)
    (hdX : Nat.Coprime (Nat.card X) d) {p : ℕ} (hp : p.Prime) :
    (∃ P : Subgroup G, Work.NormalComplement.IsSylowIn p P X ∧
      Work.NormalComplement.NormalizedBy t P) ∧
    (∀ P Q : Subgroup G, Work.NormalComplement.IsSylowIn p P X →
      Work.NormalComplement.NormalizedBy t P → Work.NormalComplement.IsSylowIn p Q X →
      Work.NormalComplement.NormalizedBy t Q →
      ∃ v ∈ Subgroup.centralizer ({t} : Set G) ⊓ X, Q = P.map (MulAut.conj v).toMonoidHom) ∧
    (∀ P : Subgroup G, IsPGroup p P → P ≤ X → Work.NormalComplement.NormalizedBy t P →
      ∃ Q : Subgroup G, Work.NormalComplement.IsSylowIn p Q X ∧
        Work.NormalComplement.NormalizedBy t Q ∧ P ≤ Q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- The operator group `A = ⟨t⟩` is cyclic, and normalises `X`.
  have ht_mem : t ∈ Subgroup.normalizer (X : Set G) := mem_normalizer_of_normalizedBy htX
  have hAle : Subgroup.zpowers t ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr ht_mem
  haveI hN : FT.Normalizes (Subgroup.zpowers t) X := ⟨hAle⟩
  have hcardA : Nat.card ↥(Subgroup.zpowers t) = d := by rw [Nat.card_zpowers, ht]
  have hcop : (Nat.card ↥(Subgroup.zpowers t)).Coprime (Nat.card ↥X) := by
    rw [hcardA]; exact hdX.symm
  have hsol : Group.IsSolvable ↥(Subgroup.zpowers t) ∨ Group.IsSolvable ↥X := by
    left
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  -- Part (a): existence of an `A`-invariant Sylow.
  obtain ⟨S, hS⟩ := Work.Coprime.exists_invariant_sylow (Subgroup.zpowers t)
    (G := ↥X) hcop hsol p
  refine ⟨⟨S.toSubgroup.map X.subtype, sylow_toSubgroup_isSylowIn S,
      normalizedBy_map_subtype_of_invariant S hS ⟨t, Subgroup.mem_zpowers t⟩⟩, ?_, ?_⟩
  · -- Part (b): conjugacy.
    intro P Q hP hPn hQ hQn
    have hPn' : ∀ a ∈ Subgroup.zpowers t, a ∈ Subgroup.normalizer (P : Set G) :=
      fun a ha => Subgroup.zpowers_le.mpr (mem_normalizer_of_normalizedBy hPn) ha
    have hQn' : ∀ a ∈ Subgroup.zpowers t, a ∈ Subgroup.normalizer (Q : Set G) :=
      fun a ha => Subgroup.zpowers_le.mpr (mem_normalizer_of_normalizedBy hQn) ha
    haveI hPI : FT.IsInvariant (Subgroup.zpowers t) (P.subgroupOf X) := isInvariant_subgroupOf hPn'
    haveI hQI : FT.IsInvariant (Subgroup.zpowers t) (Q.subgroupOf X) := isInvariant_subgroupOf hQn'
    let Ps : Sylow p ↥X := IsPGroup.toSylow
      (IsPGroup.of_equiv hP.1 (Subgroup.subgroupOfEquivOfLe hP.2.1).symm) hP.2.2
    let Qs : Sylow p ↥X := IsPGroup.toSylow
      (IsPGroup.of_equiv hQ.1 (Subgroup.subgroupOfEquivOfLe hQ.2.1).symm) hQ.2.2
    have hPseq : (Ps : Subgroup ↥X) = P.subgroupOf X := IsPGroup.toSylow_coe _ _
    have hQseq : (Qs : Subgroup ↥X) = Q.subgroupOf X := IsPGroup.toSylow_coe _ _
    have hPsinv : ∀ a : ↥(Subgroup.zpowers t), a • Ps = Ps := by
      intro a
      apply Sylow.ext
      rw [Sylow.pointwise_smul_def, hPseq]
      exact hPI.smul_eq_self a
    have hQsinv : ∀ a : ↥(Subgroup.zpowers t), a • Qs = Qs := by
      intro a
      apply Sylow.ext
      rw [Sylow.pointwise_smul_def, hQseq]
      exact hQI.smul_eq_self a
    obtain ⟨c, hc, hcQ⟩ := Work.Coprime.invariant_sylow_conj (Subgroup.zpowers t)
      (G := ↥X) hcop hsol p hPsinv hQsinv
    have hQ' : Q = Qs.toSubgroup.map X.subtype := by
      rw [hQseq, Subgroup.map_subgroupOf_eq_of_le hQ.2.1]
    have hP' : P = Ps.toSubgroup.map X.subtype := by
      rw [hPseq, Subgroup.map_subgroupOf_eq_of_le hP.2.1]
    refine ⟨(c : G), ⟨?_, c.2⟩, ?_⟩
    · change (c : G) ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (⟨t, Subgroup.mem_zpowers t⟩ : ↥(Subgroup.zpowers t)) • c = c :=
        (FT.mem_fixedPoints.mp hc) ⟨t, Subgroup.mem_zpowers t⟩
      have h2 : t * (c : G) * t⁻¹ = (c : G) := by
        have := congrArg (Subtype.val) h1
        simpa [FT.conj_smul_coe] using this
      have h3 : t * (c : G) = (c : G) * t := by
        have := congrArg (· * t) h2
        simpa [mul_assoc] using this
      exact h3.symm
    · rw [hQ', hP', sylow_conj_transfer hcQ]
  · -- Part (c): every invariant `p`-subgroup lies in an invariant Sylow.
    intro P hpP hPX hPn
    have hPn' : ∀ a ∈ Subgroup.zpowers t, a ∈ Subgroup.normalizer (P : Set G) :=
      fun a ha => Subgroup.zpowers_le.mpr (mem_normalizer_of_normalizedBy hPn) ha
    haveI hPI : FT.IsInvariant (Subgroup.zpowers t) (P.subgroupOf X) := isInvariant_subgroupOf hPn'
    have hpP' : IsPGroup p ↥(P.subgroupOf X) :=
      IsPGroup.of_equiv hpP (Subgroup.subgroupOfEquivOfLe hPX).symm
    obtain ⟨S, hPS, hS⟩ := Work.Coprime.exists_invariant_sylow_ge (Subgroup.zpowers t)
      (G := ↥X) hcop hsol p (P.subgroupOf X) hpP'
    refine ⟨S.toSubgroup.map X.subtype, sylow_toSubgroup_isSylowIn S,
      normalizedBy_map_subtype_of_invariant S hS ⟨t, Subgroup.mem_zpowers t⟩, ?_⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hPX]
    exact Subgroup.map_mono hPS

end Work.NormalComplement
