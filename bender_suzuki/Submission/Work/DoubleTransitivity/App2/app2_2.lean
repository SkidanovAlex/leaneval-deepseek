import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi, Appendix II (2): exchange of the two fixed points

Formalisation of Peterfalvi, *Le théorème de Bender–Suzuki I*, Appendix II (2) (pp. 203–204):

> Suppose `{a, b}` is the set of fixed points of a `p`-subgroup of `X` and there is `x ∈ X`
> with `b = a^x`.  Then there is an element of `X` exchanging `a` and `b`.

The proof reproduces the source.  Let `H = X_a`, `D = X_a ⊓ X_b`, and let `Q` be a `p`-Sylow of
`D` containing the given `p`-subgroup `P`.  Since `Q ≥ P` and `Q ≤ D`, `E_Q = {a, b}`; and the
normalizer argument of Appendix II (1) shows `Q` is a `p`-Sylow of both `X_a` and `X_b`.  For
`x` with `x • a = b`, both `Q` and its conjugate `Q^x = x Q x⁻¹` are `p`-Sylows of `X_b`, so
Sylow's theorem gives `y ∈ X_b` with `y Q^x y⁻¹ = Q`; then `g = y * x` normalizes `Q` and sends
`a` to `b`, hence permutes `{a, b} = E_Q` and sends `b` to `a`.

The two group-theoretic ingredients (the "normalizer theorem" for `p`-Sylows of a subgroup and
Sylow conjugacy inside a subgroup) are proved here, so the file is self-contained.
-/

set_option linter.unusedVariables false

open scoped Pointwise

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.App2

/-! ## General facts about fixed points -/

/-- The stabiliser of `x • a` is the conjugate by `x` of the stabiliser of `a`. -/
lemma stabilizer_smul_eq_conj {X E : Type} [Group X] [MulAction X E] (x : X) (a : E) :
    MulAction.stabilizer X (x • a) = Submission.Blueprint.conj x (MulAction.stabilizer X a) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_conj, MulAction.mem_stabilizer_iff]
  show g • (x • a) = x • a ↔ (x⁻¹ * g * x) • a = a
  simp only [mul_smul]
  rw [inv_smul_eq_iff]

/-- An element of the normalizer of a subgroup `Q` maps fixed points of `Q` to fixed points of
`Q`. -/
lemma smul_mem_fixedBySub_of_mem_normalizer {X E : Type} [Group X] [MulAction X E]
    {Q : Subgroup X} {n : X} (hn : n ∈ Subgroup.normalizer (Q : Set X)) {c : E}
    (hc : c ∈ fixedBySub Q) : n • c ∈ fixedBySub Q := by
  intro q hq
  have h1 : n⁻¹ * q * n ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp hn) (n⁻¹ * q * n)
    rw [show n * (n⁻¹ * q * n) * n⁻¹ = q from by group] at this
    exact this.mpr hq
  calc q • (n • c) = (q * n) • c := by rw [mul_smul]
    _ = (n * (n⁻¹ * q * n)) • c := by rw [show q * n = n * (n⁻¹ * q * n) from by group]
    _ = n • ((n⁻¹ * q * n) • c) := by rw [mul_smul]
    _ = n • c := by rw [hc (n⁻¹ * q * n) h1]

/-! ## Two Sylow facts for subgroups of `X` -/

/-- If `R` is a `p`-subgroup of `X` containing `Q`, and the normalizer of `Q` inside `R` already
equals `Q`, then `R = Q`.  (This is the standard fact that a `p`-group satisfies the normalizer
condition.) -/
lemma app2_2_eq_of_normalizer_inf_eq {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q R : Subgroup X} (hR : IsPGroup p R) (hQR : Q ≤ R)
    (hN : Subgroup.normalizer (Q : Set X) ⊓ R ≤ Q) : R = Q := by
  haveI : Group.IsNilpotent ↥R := hR.isNilpotent
  have hnc : NormalizerCondition ↥R := Group.normalizerCondition_of_isNilpotent
  have hnorm : Subgroup.normalizer ((Q.subgroupOf R : Subgroup ↥R) : Set ↥R) ≤ Q.subgroupOf R := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx1 : x ∈ (Subgroup.normalizer (Q : Set X)).subgroupOf R := by
      rw [Subgroup.subgroupOf_normalizer_eq hQR]; exact hx
    rw [Subgroup.mem_subgroupOf] at hx1
    exact hN ⟨hx1, x.2⟩
  have heq : Subgroup.normalizer ((Q.subgroupOf R : Subgroup ↥R) : Set ↥R) = Q.subgroupOf R :=
    le_antisymm hnorm Subgroup.le_normalizer
  have htop : Q.subgroupOf R = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ heq
  refine le_antisymm ?_ hQR
  intro r hr
  have hmem : (⟨r, hr⟩ : ↥R) ∈ Q.subgroupOf R := by rw [htop]; trivial
  rwa [Subgroup.mem_subgroupOf] at hmem

/-- **Normalizer theorem.**  If `Q ≤ D ≤ K`, `Q` is maximal among the `p`-subgroups of `D`
containing it, and the normalizer of `Q` inside `K` lies in `D`, then `Q` is maximal among the
`p`-subgroups of `K` containing it. -/
lemma app2_2_sylow_max_norm {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q D K : Subgroup X}
    (hQD : Q ≤ D) (hDK : D ≤ K)
    (hmaxD : ∀ R : Subgroup X, IsPGroup p R → Q ≤ R → R ≤ D → R = Q)
    (hN : Subgroup.normalizer (Q : Set X) ⊓ K ≤ D) :
    ∀ R : Subgroup X, IsPGroup p R → Q ≤ R → R ≤ K → R = Q := by
  intro R hR hQR hRK
  refine app2_2_eq_of_normalizer_inf_eq hR hQR ?_
  have hle : Subgroup.normalizer (Q : Set X) ⊓ R ≤ D :=
    le_trans (le_inf inf_le_left (le_trans inf_le_right hRK)) hN
  exact le_of_eq (hmaxD (Subgroup.normalizer (Q : Set X) ⊓ R) (hR.to_le inf_le_right)
    (le_inf Subgroup.le_normalizer hQR) hle)

/-- **Sylow conjugacy inside a subgroup.**  Any two maximal `p`-subgroups `Q`, `R` of `K ≤ X` are
conjugate by an element of `K`. -/
lemma app2_2_sylow_max_conj {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {Q R K : Subgroup X}
    (hQ : IsPGroup p Q) (hQK : Q ≤ K)
    (hmaxQ : ∀ T : Subgroup X, IsPGroup p T → Q ≤ T → T ≤ K → T = Q)
    (hR : IsPGroup p R) (hRK : R ≤ K)
    (hmaxR : ∀ T : Subgroup X, IsPGroup p T → R ≤ T → T ≤ K → T = R) :
    ∃ k ∈ K, Subgroup.map (MulAut.conj k).toMonoidHom R = Q := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := by
    rw [← Subgroup.comap_subtype]; exact hQ.comap_subtype
  have hR' : IsPGroup p (R.subgroupOf K) := by
    rw [← Subgroup.comap_subtype]; exact hR.comap_subtype
  have hmaxQ'' : ∀ {T : Subgroup K}, IsPGroup p T → Q.subgroupOf K ≤ T → T = Q.subgroupOf K := by
    intro T hT hle
    have hle' : Q ≤ T.map K.subtype := by
      have h := Subgroup.map_mono (f := K.subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le hQK] at h
    have hTle : T.map K.subtype ≤ K := Subgroup.map_subtype_le T
    have hT' := hmaxQ (T.map K.subtype) (hT.map K.subtype) hle' hTle
    have : Subgroup.map K.subtype T = Subgroup.map K.subtype (Q.subgroupOf K) := by
      rw [hT', Subgroup.map_subgroupOf_eq_of_le hQK]
    exact Subgroup.map_injective K.subtype_injective this
  have hmaxR'' : ∀ {T : Subgroup K}, IsPGroup p T → R.subgroupOf K ≤ T → T = R.subgroupOf K := by
    intro T hT hle
    have hle' : R ≤ T.map K.subtype := by
      have h := Subgroup.map_mono (f := K.subtype) hle
      rwa [Subgroup.map_subgroupOf_eq_of_le hRK] at h
    have hTle : T.map K.subtype ≤ K := Subgroup.map_subtype_le T
    have hT' := hmaxR (T.map K.subtype) (hT.map K.subtype) hle' hTle
    have : Subgroup.map K.subtype T = Subgroup.map K.subtype (R.subgroupOf K) := by
      rw [hT', Subgroup.map_subgroupOf_eq_of_le hRK]
    exact Subgroup.map_injective K.subtype_injective this
  let Q' : Sylow p K := ⟨Q.subgroupOf K, hQ', hmaxQ''⟩
  let R' : Sylow p K := ⟨R.subgroupOf K, hR', hmaxR''⟩
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K R' Q'
  have hk' : MulAut.conj k • (R.subgroupOf K) = Q.subgroupOf K := by
    have h := congrArg (fun S : Sylow p K => (S : Subgroup K)) hk
    rw [Sylow.coe_subgroup_smul] at h
    exact h
  refine ⟨(k : X), k.2, ?_⟩
  have h1 : (MulAut.conj (k : X) • R).subgroupOf K = Q.subgroupOf K := by
    rw [← Subgroup.conj_smul_subgroupOf hRK k]; exact hk'
  have h2 := congrArg (Subgroup.map K.subtype) h1
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_subgroupOf_eq_of_le hQK,
      inf_eq_left.2 (Subgroup.conj_smul_le_of_le hRK k)] at h2
  show MulAut.conj (k : X) • R = Q
  exact h2

/-! ## Lifting the given `p`-subgroup to a `p`-Sylow with the same fixed points -/

/-- Given a `p`-subgroup `P` of `X` whose set of fixed points on `E` is exactly `{a, b}`, there
is a `p`-subgroup `Q` with `P ≤ Q`, the same fixed-point set `{a, b}`, and `Q` maximal among the
`p`-subgroups of both point stabilisers `X_a` and `X_b`.  (Appendix II (1), with the symmetric
statement for `X_b` added.) -/
lemma exists_sylow_fixed {X E : Type} [Group X] [MulAction X E] [Finite X]
    {p : ℕ} [Fact p.Prime] {a b : E} (hab : a ≠ b)
    {P : Subgroup X} (hP : IsPGroup p P) (hPfix : fixedBySub P = {a, b}) :
    ∃ Q : Subgroup X, P ≤ Q ∧ IsPGroup p Q ∧ fixedBySub Q = {a, b} ∧
      (∀ R : Subgroup X, IsPGroup p R → Q ≤ R → R ≤ MulAction.stabilizer X a → R = Q) ∧
      (∀ R : Subgroup X, IsPGroup p R → Q ≤ R → R ≤ MulAction.stabilizer X b → R = Q) := by
  have ha : a ∈ fixedBySub P := by rw [hPfix]; left; rfl
  have hb : b ∈ fixedBySub P := by rw [hPfix]; right; rfl
  have hPa : P ≤ MulAction.stabilizer X a := by
    intro m hm; rw [MulAction.mem_stabilizer_iff]; exact ha m hm
  have hPb : P ≤ MulAction.stabilizer X b := by
    intro m hm; rw [MulAction.mem_stabilizer_iff]; exact hb m hm
  set D : Subgroup X := MulAction.stabilizer X a ⊓ MulAction.stabilizer X b with hD
  have hDle_a : D ≤ MulAction.stabilizer X a := by rw [hD]; exact inf_le_left
  have hDle_b : D ≤ MulAction.stabilizer X b := by rw [hD]; exact inf_le_right
  have hPD : P ≤ D := by intro x hx; rw [hD]; exact ⟨hPa hx, hPb hx⟩
  have hPD' : IsPGroup p (P.subgroupOf D) := hP.comap_of_injective D.subtype D.subtype_injective
  obtain ⟨S, hPS⟩ := hPD'.exists_le_sylow
  have hPmap : (P.subgroupOf D).map D.subtype = P := by
    change (P.comap D.subtype).map D.subtype = P
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.mpr hPD
  have hQPD : (S : Subgroup ↥D).map D.subtype ≤ D := Subgroup.map_subtype_le (S : Subgroup ↥D)
  have hQa : (S : Subgroup ↥D).map D.subtype ≤ MulAction.stabilizer X a := le_trans hQPD hDle_a
  have hQb : (S : Subgroup ↥D).map D.subtype ≤ MulAction.stabilizer X b := le_trans hQPD hDle_b
  have hPQ : P ≤ (S : Subgroup ↥D).map D.subtype := by
    rw [← hPmap]; exact Subgroup.map_mono hPS
  have hQfix : fixedBySub ((S : Subgroup ↥D).map D.subtype) = {a, b} := by
    apply Set.Subset.antisymm
    · rw [← hPfix]; exact fixedBySub_antitone hPQ
    · intro c hc
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl
      · exact fun m hm => MulAction.mem_stabilizer_iff.mp (hQa hm)
      · exact fun m hm => MulAction.mem_stabilizer_iff.mp (hQb hm)
  have hmaxD : ∀ R : Subgroup X, IsPGroup p R →
      (S : Subgroup ↥D).map D.subtype ≤ R → R ≤ D → R = (S : Subgroup ↥D).map D.subtype := by
    intro R hR hQR hRD
    have hR' : IsPGroup p (R.subgroupOf D) := hR.comap_of_injective D.subtype D.subtype_injective
    have hSR : (S : Subgroup ↥D) ≤ R.subgroupOf D :=
      (Subgroup.map_le_iff_le_comap (f := D.subtype)).mp hQR
    have h1 : R.subgroupOf D = (S : Subgroup ↥D) := S.is_maximal' hR' hSR
    have hRmap : (R.subgroupOf D).map D.subtype = R := by
      change (R.comap D.subtype).map D.subtype = R
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.mpr hRD
    rw [← hRmap, h1]
  have hbQ : b ∈ fixedBySub ((S : Subgroup ↥D).map D.subtype) := by rw [hQfix]; right; rfl
  have hN_a : Subgroup.normalizer (((S : Subgroup ↥D).map D.subtype : Subgroup X) : Set X) ⊓
      MulAction.stabilizer X a ≤ D := by
    intro n hn
    have hn1 := hn.1
    have hn2 : n • a = a := MulAction.mem_stabilizer_iff.mp hn.2
    have hnb : n • b ∈ fixedBySub ((S : Subgroup ↥D).map D.subtype) :=
      smul_mem_fixedBySub_of_mem_normalizer hn1 hbQ
    rw [hQfix] at hnb
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hnb
    have hnb' : n • b = b := by
      rcases hnb with h | h
      · exact absurd (hab ((MulAction.injective n (h.trans hn2.symm)).symm)) (by simp)
      · exact h
    rw [hD]; exact ⟨hn.2, MulAction.mem_stabilizer_iff.mpr hnb'⟩
  have haQ : a ∈ fixedBySub ((S : Subgroup ↥D).map D.subtype) := by rw [hQfix]; left; rfl
  have hN_b : Subgroup.normalizer (((S : Subgroup ↥D).map D.subtype : Subgroup X) : Set X) ⊓
      MulAction.stabilizer X b ≤ D := by
    intro n hn
    have hn1 := hn.1
    have hn2 : n • b = b := MulAction.mem_stabilizer_iff.mp hn.2
    have hna : n • a ∈ fixedBySub ((S : Subgroup ↥D).map D.subtype) :=
      smul_mem_fixedBySub_of_mem_normalizer hn1 haQ
    rw [hQfix] at hna
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hna
    have hna' : n • a = a := by
      rcases hna with h | h
      · exact h
      · exact absurd (hab (MulAction.injective n (h.trans hn2.symm))) (by simp)
    rw [hD]; exact ⟨MulAction.mem_stabilizer_iff.mpr hna', hn.2⟩
  exact ⟨_, hPQ, S.isPGroup'.map D.subtype, hQfix,
    app2_2_sylow_max_norm hQPD hDle_a hmaxD hN_a,
    app2_2_sylow_max_norm hQPD hDle_b hmaxD hN_b⟩

/-! ## Appendix II (2) -/

theorem app2_2 {X E : Type} [Group X] [MulAction X E] [Finite X]
    {p : ℕ} [Fact p.Prime] {a b : E} (hab : a ≠ b)
    (h : ∃ P : Subgroup X, IsPGroup p P ∧ fixedBySub P = {a, b})
    (hx : ∃ x : X, x • a = b) :
    ∃ y : X, y • a = b ∧ y • b = a := by
  obtain ⟨P, hP, hPfix⟩ := h
  obtain ⟨x, hx⟩ := hx
  obtain ⟨Q, hPQ, hQgrp, hQfix, hmaxA, hmaxB⟩ := exists_sylow_fixed (X := X) hab hP hPfix
  have haQ : a ∈ fixedBySub Q := by rw [hQfix]; left; rfl
  have hbQ : b ∈ fixedBySub Q := by rw [hQfix]; right; rfl
  have hQa : Q ≤ MulAction.stabilizer X a := fun m hm => MulAction.mem_stabilizer_iff.mpr (haQ m hm)
  have hQb : Q ≤ MulAction.stabilizer X b := fun m hm => MulAction.mem_stabilizer_iff.mpr (hbQ m hm)
  have hXb : MulAction.stabilizer X b = Submission.Blueprint.conj x (MulAction.stabilizer X a) := by
    rw [← stabilizer_smul_eq_conj x a, hx]
  set R : Subgroup X := Submission.Blueprint.conj x Q with hR
  have hRgrp : IsPGroup p R := hQgrp.map (MulAut.conj x).toMonoidHom
  have hRle : R ≤ MulAction.stabilizer X b := by
    calc R = Submission.Blueprint.conj x Q := hR
      _ ≤ Submission.Blueprint.conj x (MulAction.stabilizer X a) := Subgroup.map_mono hQa
      _ = MulAction.stabilizer X b := hXb.symm
  have hmaxR : ∀ T : Subgroup X, IsPGroup p T → R ≤ T → T ≤ MulAction.stabilizer X b → T = R := by
    intro T hT hRT hTb
    have hxinv : Submission.Blueprint.conj x⁻¹ T ≤ MulAction.stabilizer X a := by
      calc Submission.Blueprint.conj x⁻¹ T
            ≤ Submission.Blueprint.conj x⁻¹ (MulAction.stabilizer X b) := Subgroup.map_mono hTb
        _ = Submission.Blueprint.conj x⁻¹
              (Submission.Blueprint.conj x (MulAction.stabilizer X a)) := by rw [hXb]
        _ = MulAction.stabilizer X a := conj_inv_conj x _
    have hQT : Q ≤ Submission.Blueprint.conj x⁻¹ T := by
      calc Q = Submission.Blueprint.conj x⁻¹ (Submission.Blueprint.conj x Q) :=
            (conj_inv_conj x Q).symm
        _ = Submission.Blueprint.conj x⁻¹ R := by rw [hR]
        _ ≤ Submission.Blueprint.conj x⁻¹ T := Subgroup.map_mono hRT
    have hQTgrp : IsPGroup p (Submission.Blueprint.conj x⁻¹ T) :=
      hT.map (MulAut.conj x⁻¹).toMonoidHom
    have h1 : Submission.Blueprint.conj x⁻¹ T = Q := hmaxA (Submission.Blueprint.conj x⁻¹ T) hQTgrp hQT hxinv
    calc T = Submission.Blueprint.conj x (Submission.Blueprint.conj x⁻¹ T) :=
          (conj_conj_inv x T).symm
      _ = Submission.Blueprint.conj x Q := by rw [h1]
      _ = R := hR.symm
  obtain ⟨y, hyb, hyconj⟩ := app2_2_sylow_max_conj (Q := Q) (R := R)
    (K := MulAction.stabilizer X b) hQgrp hQb hmaxB hRgrp hRle hmaxR
  have hyb' : y • b = b := MulAction.mem_stabilizer_iff.mp hyb
  have hga : (y * x) • a = b := by rw [mul_smul, hx, hyb']
  have hgconj : Submission.Blueprint.conj (y * x) Q = Q := by
    rw [conj_mul]
    rw [show Submission.Blueprint.conj x Q = R from rfl]
    exact hyconj
  have hgN : y * x ∈ Subgroup.normalizer (Q : Set X) :=
    (conj_eq_self_iff_mem_normalizer (y * x) Q).mp hgconj
  have hgE : (y * x) • b ∈ fixedBySub Q :=
    smul_mem_fixedBySub_of_mem_normalizer hgN hbQ
  rw [hQfix] at hgE
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hgE
  have hgb : (y * x) • b = a := by
    rcases hgE with hh | hh
    · exact hh
    · exfalso
      exact hab ((MulAction.injective (y * x) (hh.trans hga.symm)).symm)
  exact ⟨y * x, hga, hgb⟩

end Work.DoubleTransitivity.App2
