/-
# The `p`-control criterion (Peterfalvi I Ch. III §1 Lemma 2), product form

Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. III §1 Lemma 2 (p. 173): let `E ≤ W` be finite
with `p ∣ |E|` and let `P` be a `p`-Sylow of `E`.  If
1. `N_W(P) = O_{p'}(C_W(P))·N_E(P)`, and
2. `N_W(U) = O_{p'}(C_W(U))·N_E(U)` for every non-cyclic subgroup `U ≤ P`,
then `E` is a `p`-control group in `W` (in the product form of `Work.NormalComplement.IsPControl`).

The proof is the induction of `pcontrol_criterion.lean` (strong induction on `|P| - |A|`), with the
product structure `x = c·e` (`c ∈ C_W(A)`, `e ∈ E`) kept throughout.  The product decomposition of
an element of `N_W(A)` is obtained from hypotheses 1, 2 by Sylow conjugacy inside `E`, which is why
no "for all `U`" hypothesis is needed.

The auxiliary Sylow lemmas below are those of `Submission/Work/NormalComplement/pcontrol_criterion`
(whose final theorem is out of date), reproduced here so that this module is self-contained; and the
`O_{p'}`-preservation lemmas are those of `Submission/Work/NormalComplement/pcontrolProd`.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.isSylowIn_of_sylowIn_normalizer
import Submission.Work.NormalComplement.conj_sylow_of_isCyclic
import Submission.Work.NormalComplement.sylow_normalizer_transfer
import Submission.Work.NormalComplement.CC.mem_sup_prod
import Submission.Work.Fitting.piCore_isPiNat
import Submission.Work.Fitting.mem_piCore_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-! ## Elementary subgroup and counting lemmas -/

/-- `A.subgroupOf Y ⊓ B.subgroupOf Y = (A ⊓ B).subgroupOf Y`. -/
private lemma inf_subgroupOf_symm (A B Y : Subgroup G) :
    A.subgroupOf Y ⊓ B.subgroupOf Y = (A ⊓ B).subgroupOf Y := by
  ext x
  simp [Subgroup.mem_subgroupOf]

/-- `|H ⊔ K| · |H ⊓ K| = |H| · |K|` for `K` normal. -/
private lemma card_sup_mul_card_inf (A B : Subgroup G) [B.Normal] :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hcard : ∀ {H K : Subgroup G}, Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
    intro H K
    rw [← Subgroup.inf_subgroupOf_right H K]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := K) inf_le_right).toEquiv
  have h1 : Nat.card ↥(A ⊔ B) = B.relIndex A * Nat.card ↥B := by
    rw [← Subgroup.index_mul_card (B.subgroupOf (A ⊔ B)),
      show (B.subgroupOf (A ⊔ B)).index = B.relIndex A from
        Subgroup.relIndex_sup_right (H := A) (K := B),
      hcard (H := B) (K := A ⊔ B), inf_of_le_left le_sup_right]
  have h2 : Nat.card ↥A = B.relIndex A * Nat.card ↥(A ⊓ B) := by
    rw [← Subgroup.index_mul_card (B.subgroupOf A),
      show (B.subgroupOf A).index = B.relIndex A from rfl,
      hcard (H := B) (K := A), inf_comm]
  rw [h1, h2]; ring

/-- `|H ⊔ K| · |H ⊓ K| = |H| · |K|` when `K` is normalised by `H ⊔ K`. -/
private lemma card_sup_mul_card_inf_of_le_normalizer (A B : Subgroup G)
    (h : A ⊔ B ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hB : (B.subgroupOf (A ⊔ B)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  have key : Nat.card ↥(A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B)) *
      Nat.card ↥(A.subgroupOf (A ⊔ B) ⊓ B.subgroupOf (A ⊔ B)) =
      Nat.card ↥(A.subgroupOf (A ⊔ B)) * Nat.card ↥(B.subgroupOf (A ⊔ B)) :=
    card_sup_mul_card_inf (G := ↥(A ⊔ B)) (A.subgroupOf (A ⊔ B)) (B.subgroupOf (A ⊔ B))
  rw [← Subgroup.subgroupOf_sup (A := A) (A' := B) (B := A ⊔ B) le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.card_top, inf_subgroupOf_symm] at key
  have hA : Nat.card ↥(A.subgroupOf (A ⊔ B)) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hBB : Nat.card ↥(B.subgroupOf (A ⊔ B)) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hAB : Nat.card ↥((A ⊓ B).subgroupOf (A ⊔ B)) = Nat.card ↥(A ⊓ B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans le_sup_left)).toEquiv
  rw [hA, hBB, hAB] at key
  exact key

/-- `|H.subgroupOf Y| = |H|` for `H ≤ Y`. -/
private lemma card_subgroupOf_eq (H Y : Subgroup G) (h : H ≤ Y) :
    Nat.card ↥(H.subgroupOf Y) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

/-- Conjugation by an element of `X` fixes `X`. -/
private lemma map_conj_eq_self_of_mem {X : Subgroup G} {x : G} (hx : x ∈ X) :
    X.map (MulAut.conj x).toMonoidHom = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)

variable {p : ℕ} [Fact p.Prime]

/-- `S` a `p`-Sylow of `X` and `O` a `p'`-group normalised by `O ⊔ X` imply that `S` is a
`p`-Sylow of `O ⊔ X`. -/
private lemma isSylowIn_sup_of_le_normalizer_of_not_dvd_card {O X S : Subgroup G}
    (hOX : O ⊔ X ≤ Subgroup.normalizer (O : Set G)) (hO : ¬ p ∣ Nat.card O)
    (hS : IsSylowIn p S X) : IsSylowIn p S (O ⊔ X) := by
  refine ⟨hS.1, hS.2.1.trans le_sup_right, ?_⟩
  intro hdiv
  have hOX' : X ⊔ O ≤ Subgroup.normalizer (O : Set G) := by rw [sup_comm]; exact hOX
  have hY : Nat.card ↥(O ⊔ X) = (S.subgroupOf (O ⊔ X)).index * Nat.card ↥S := by
    rw [← Subgroup.index_mul_card (S.subgroupOf (O ⊔ X)),
      card_subgroupOf_eq S (O ⊔ X) (hS.2.1.trans le_sup_right)]
  have hX : Nat.card ↥X = (S.subgroupOf X).index * Nat.card ↥S := by
    rw [← Subgroup.index_mul_card (S.subgroupOf X), card_subgroupOf_eq S X hS.2.1]
  have hkey : Nat.card ↥(O ⊔ X) * Nat.card ↥(O ⊓ X) = Nat.card ↥O * Nat.card ↥X := by
    rw [sup_comm, inf_comm]
    exact (card_sup_mul_card_inf_of_le_normalizer X O hOX').trans (mul_comm _ _)
  rw [hY, hX] at hkey
  have hcancel : (S.subgroupOf (O ⊔ X)).index * Nat.card ↥(O ⊓ X) =
      Nat.card ↥O * (S.subgroupOf X).index := by
    refine Nat.mul_right_cancel (Nat.card_pos (α := ↥S)) ?_
    calc ((S.subgroupOf (O ⊔ X)).index * Nat.card ↥(O ⊓ X)) * Nat.card ↥S
        = (S.subgroupOf (O ⊔ X)).index * Nat.card ↥S * Nat.card ↥(O ⊓ X) := by ring
      _ = Nat.card ↥O * ((S.subgroupOf X).index * Nat.card ↥S) := hkey
      _ = (Nat.card ↥O * (S.subgroupOf X).index) * Nat.card ↥S := by ring
  have hdvd1 : p ∣ Nat.card ↥O * (S.subgroupOf X).index := by
    rw [← hcancel]
    exact dvd_mul_of_dvd_left hdiv _
  rcases (Fact.out : p.Prime).dvd_mul.mp hdvd1 with h | h
  · exact hO h
  · exact hS.2.2 h

/-- A proper subgroup of a `p`-group is properly contained in its normaliser. -/
private lemma lt_inf_normalizer_of_isPGroup {Q U : Subgroup G} (hUQ : U < Q) (hQ : IsPGroup p Q) :
    U < Q ⊓ Subgroup.normalizer (U : Set G) := by
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hNC : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent
  have hne : U.subgroupOf Q ≠ ⊤ := by
    intro h
    refine hUQ.2 ?_
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥Q) ∈ U.subgroupOf Q := by rw [h]; trivial
    simpa [Subgroup.mem_subgroupOf] using h1
  have hsub : U.subgroupOf Q ≠ Subgroup.normalizer (U.subgroupOf Q) := fun h =>
    hne ((normalizerCondition_iff_only_full_group_self_normalizing.mp hNC
      (U.subgroupOf Q) h.symm))
  have hle : U.subgroupOf Q ≤ Subgroup.normalizer (U.subgroupOf Q) := Subgroup.le_normalizer
  have hlt : U.subgroupOf Q < Subgroup.normalizer (U.subgroupOf Q) := lt_of_le_of_ne hle hsub
  have heq : Subgroup.normalizer (U.subgroupOf Q) = (Subgroup.normalizer (U : Set G)).subgroupOf Q :=
    (Subgroup.subgroupOf_normalizer_eq hUQ.1).symm
  rw [heq] at hlt
  refine lt_of_le_of_ne ?_ ?_
  · intro x hx
    exact ⟨hUQ.1 hx, Subgroup.le_normalizer hx⟩
  · intro h
    refine hlt.2 (le_of_eq ?_)
    rw [← Subgroup.inf_subgroupOf_left, ← h]

/-- A `p`-subgroup of `X` has order dividing the order of a `p`-Sylow of `X`. -/
private lemma card_dvd_card_of_isPGroup_of_isSylowIn {U P X : Subgroup G} (hUX : U ≤ X)
    (hU : IsPGroup p U) (hP : IsSylowIn p P X) : Nat.card U ∣ Nat.card P := by
  have h1 : Nat.card U ∣ Nat.card X := by
    rw [← card_subgroupOf_eq U X hUX]
    exact Subgroup.card_subgroup_dvd_card (U.subgroupOf X)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have h2 : Nat.card X = (P.subgroupOf X).index * Nat.card P := by
    rw [← Subgroup.index_mul_card (P.subgroupOf X), card_subgroupOf_eq P X hP.2.1]
  have h3 : p ^ k ∣ Nat.card P * (P.subgroupOf X).index := by
    rw [mul_comm (Nat.card P), ← h2, ← hk]
    exact h1
  have h4 : Nat.Coprime (p ^ k) (P.subgroupOf X).index :=
    Nat.Coprime.pow_left _ ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hP.2.2)
  rw [hk]
  exact h4.dvd_of_dvd_mul_right h3

/-- Every `p`-subgroup of `X` is contained in a `p`-Sylow of `X`. -/
private lemma exists_isSylowIn_ge {T X : Subgroup G} (hTX : T ≤ X) (hT : IsPGroup p T) :
    ∃ S : Subgroup G, T ≤ S ∧ IsSylowIn p S X := by
  have hT' : IsPGroup p (T.subgroupOf X) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  refine ⟨(S' : Subgroup ↥X).map X.subtype, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hTX hx⟩, hS' (by simpa [Subgroup.mem_subgroupOf] using hx),
      rfl⟩
  · exact S'.isPGroup'.map X.subtype
  · exact Subgroup.map_subtype_le (S' : Subgroup ↥X)
  · intro hdiv
    have hle : (S' : Subgroup ↥X) ≤ ((S' : Subgroup ↥X).map X.subtype).subgroupOf X := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact (Sylow.not_dvd_index S') (dvd_trans hdiv (Subgroup.index_dvd_of_le hle))

/-- Two `p`-Sylows of the same subgroup have the same order. -/
private lemma card_eq_of_isSylowIn_of_isSylowIn {A B X : Subgroup G} (hA : IsSylowIn p A X)
    (hB : IsSylowIn p B X) : Nat.card A = Nat.card B :=
  le_antisymm (Nat.le_of_dvd (Nat.card_pos)
      (card_dvd_card_of_isPGroup_of_isSylowIn hA.2.1 hA.1 hB))
    (Nat.le_of_dvd (Nat.card_pos)
      (card_dvd_card_of_isPGroup_of_isSylowIn hB.2.1 hB.1 hA))

/-- Two `p`-Sylows of the same subgroup are conjugate. -/
private lemma exists_conj_eq_of_isSylowIn_of_isSylowIn {A B X : Subgroup G} (hA : IsSylowIn p A X)
    (hB : IsSylowIn p B X) :
    ∃ g ∈ X, A.map (MulAut.conj g).toMonoidHom = B := by
  have hA' : IsPGroup p (A.subgroupOf X) :=
    hA.1.comap_of_injective X.subtype (fun a b h => Subtype.ext h)
  have hB' : IsPGroup p (B.subgroupOf X) :=
    hB.1.comap_of_injective X.subtype (fun a b h => Subtype.ext h)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥X)
    (IsPGroup.toSylow hA' hA.2.2) (IsPGroup.toSylow hB' hB.2.2)
  have hsmul : MulAut.conj g • (A.subgroupOf X) = B.subgroupOf X := by
    have hcoe : (↑(g • IsPGroup.toSylow hA' hA.2.2) : Subgroup ↥X) =
        ↑(IsPGroup.toSylow hB' hB.2.2) := congrArg _ hg
    simpa [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] using hcoe
  refine ⟨(g : G), g.2, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    have h1 : (⟨u, hA.2.1 hu⟩ : ↥X) ∈ A.subgroupOf X := by
      simpa [Subgroup.mem_subgroupOf] using hu
    have h2 : (MulAut.conj g) (⟨u, hA.2.1 hu⟩ : ↥X) ∈ B.subgroupOf X := by
      rw [← hsmul]
      exact ⟨_, h1, rfl⟩
    have h3 : ((MulAut.conj g) (⟨u, hA.2.1 hu⟩ : ↥X) : G) = (g : G) * u * (g : G)⁻¹ := by
      rw [MulAut.conj_apply]; simp
    rw [Subgroup.mem_subgroupOf] at h2
    rwa [h3] at h2
  · rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective,
      card_eq_of_isSylowIn_of_isSylowIn hA hB]

/-- A `p`-subgroup of `X` of the order of a `p`-Sylow of `X` is a `p`-Sylow of `X`. -/
private lemma isSylowIn_of_le_of_card_eq {U P X : Subgroup G} (hUX : U ≤ X) (hU : IsPGroup p U)
    (hP : IsSylowIn p P X) (hcard : Nat.card U = Nat.card P) : IsSylowIn p U X := by
  obtain ⟨Q, hUQ, hQsyl⟩ := exists_isSylowIn_ge hUX hU
  have hQcard : Nat.card Q = Nat.card U :=
    (card_eq_of_isSylowIn_of_isSylowIn hQsyl hP).trans hcard.symm
  have hQU : U = Q := Subgroup.eq_of_le_of_card_ge hUQ (le_of_eq hQcard)
  rwa [hQU]

/-- Conjugating a `p`-Sylow gives a `p`-Sylow of the conjugate. -/
private lemma isSylowIn_map_conj {A X : Subgroup G} (hA : IsSylowIn p A X) (g : G) :
    IsSylowIn p (A.map (MulAut.conj g).toMonoidHom)
      (X.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hA.1.map _, Subgroup.map_mono hA.2.1, ?_⟩
  have h : ((A.map (MulAut.conj g).toMonoidHom).subgroupOf (X.map (MulAut.conj g).toMonoidHom)).index
      = (A.subgroupOf X).index := by
    rw [← Subgroup.relIndex, ← Subgroup.relIndex]
    exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A X
      (MulAut.conj g).injective
  rw [h]
  exact hA.2.2

/-- The centralizer of a conjugate. -/
private lemma map_conj_centralizer_le (X : Subgroup G) (g : G) :
    (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ((X.map (MulAut.conj g).toMonoidHom) : Set G) := by
  have h := Subgroup.map_centralizer_le_centralizer_image (X : Set G)
    (MulAut.conj g).toMonoidHom
  have h2 : (MulAut.conj g).toMonoidHom '' (X : Set G) =
      ↑(X.map (MulAut.conj g).toMonoidHom) :=
    (Subgroup.coe_map (MulAut.conj g).toMonoidHom X).symm
  rwa [h2] at h

/-- Conjugation is compatible with composition. -/
private lemma map_conj_map_conj (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Conjugating by `a` and then by `a⁻¹` is the identity. -/
private lemma map_conj_inv (A : Subgroup G) (a : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = A := by
  rw [map_conj_map_conj, inv_mul_cancel]
  ext x
  simp [Subgroup.mem_map]

/-- Monotonicity of the order of a subgroup. -/
private lemma card_le_card_of_le {H K : Subgroup G} (h : H ≤ K) : Nat.card H ≤ Nat.card K :=
  Nat.le_of_dvd Nat.card_pos (by
    rw [← card_subgroupOf_eq H K h]
    exact Subgroup.card_subgroup_dvd_card (H.subgroupOf K))

/-- Cyclicity is preserved by conjugation. -/
private lemma isCyclic_map_conj_iff (A : Subgroup G) (g : G) :
    IsCyclic A ↔ IsCyclic (A.map (MulAut.conj g).toMonoidHom) :=
  MulEquiv.isCyclic (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective)

/-- `O_{p'}(X) ≤ Y` for `X ≤ Y`. -/
private lemma pPrimeCoreSub_le_of_le {X Y : Subgroup G} (h : X ≤ Y) : pPrimeCoreSub p X ≤ Y :=
  (Subgroup.map_subtype_le (pPrimeCore p ↥X)).trans h

/-! ## Transporting the two hypotheses to `E`-conjugates -/

/-- Hypothesis 1, transported to all `p`-Sylows of `E` (which are exactly the `E`-conjugates
of `P`). -/
private lemma normalizer_le_of_isSylowIn_of_h1 {E W P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hEW' : E ≤ W) (hPsyl : IsSylowIn p P E)
    (h1 : Subgroup.normalizer (P : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (P : Set G) ⊓ E))
    {A : Subgroup G} (hA : IsSylowIn p A E) :
    Subgroup.normalizer (A : Set G) ⊓ W ≤ Subgroup.centralizer (A : Set G) ⊔ E := by
  obtain ⟨f, hfE, hf⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hA hPsyl
  have hAeq : A = P.map (MulAut.conj f⁻¹).toMonoidHom := by
    have h := congrArg (fun S : Subgroup G => S.map (MulAut.conj f⁻¹).toMonoidHom) hf
    rw [map_conj_inv] at h
    exact h
  have hf'W : f⁻¹ ∈ W := hEW' (Subgroup.inv_mem E hfE)
  have hLHS : (Subgroup.normalizer (P : Set G) ⊓ W).map (MulAut.conj f⁻¹).toMonoidHom =
      Subgroup.normalizer (A : Set G) ⊓ W := by
    rw [Subgroup.map_inf _ _ (MulAut.conj f⁻¹).toMonoidHom (MulAut.conj f⁻¹).injective,
      Subgroup.map_equiv_normalizer_eq _ (MulAut.conj f⁻¹),
      map_conj_eq_self_of_mem (X := W) hf'W, ← hAeq]
  have hO : (pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W)).map
        (MulAut.conj f⁻¹).toMonoidHom ≤ Subgroup.centralizer (A : Set G) := by
    have h1' : (pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W)).map
          (MulAut.conj f⁻¹).toMonoidHom ≤
        Subgroup.centralizer ((P.map (MulAut.conj f⁻¹).toMonoidHom : Subgroup G) : Set G) :=
      (Subgroup.map_mono (le_trans (Subgroup.map_subtype_le _) inf_le_left)).trans
        (map_conj_centralizer_le P f⁻¹)
    rwa [← hAeq] at h1'
  have hE : (Subgroup.normalizer (P : Set G) ⊓ E).map (MulAut.conj f⁻¹).toMonoidHom ≤ E :=
    (Subgroup.map_mono inf_le_right).trans
      (le_of_eq (map_conj_eq_self_of_mem (X := E) (Subgroup.inv_mem E hfE)))
  calc Subgroup.normalizer (A : Set G) ⊓ W
      = (Subgroup.normalizer (P : Set G) ⊓ W).map (MulAut.conj f⁻¹).toMonoidHom := hLHS.symm
    _ = (pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W)).map
          (MulAut.conj f⁻¹).toMonoidHom ⊔
          ((Subgroup.normalizer (P : Set G) ⊓ E).map (MulAut.conj f⁻¹).toMonoidHom) := by
        rw [h1, Subgroup.map_sup]
    _ ≤ Subgroup.centralizer (A : Set G) ⊔ E :=
        sup_le (hO.trans le_sup_left) (hE.trans le_sup_right)

/-- Hypothesis 2, transported to all non-cyclic `p`-subgroups of `E`. -/
private lemma le_centralizer_sup_of_le_centralizer_sup_map_conj {A E W : Subgroup G}
    {g : G} (hgE : g ∈ E) (hW : g⁻¹ ∈ W)
    (h : Subgroup.normalizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊓ W ≤
      Subgroup.centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊔ E) :
    Subgroup.normalizer (A : Set G) ⊓ W ≤ Subgroup.centralizer (A : Set G) ⊔ E := by
  have hmap : (Subgroup.normalizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊓ W).map
      (MulAut.conj g⁻¹).toMonoidHom = Subgroup.normalizer (A : Set G) ⊓ W := by
    rw [Subgroup.map_inf (Subgroup.normalizer (A.map (MulAut.conj g).toMonoidHom : Set G)) W
        (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective,
      Subgroup.map_equiv_normalizer_eq _ (MulAut.conj g⁻¹),
      map_conj_eq_self_of_mem (X := W) hW, map_conj_inv]
  calc Subgroup.normalizer (A : Set G) ⊓ W
      = (Subgroup.normalizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊓ W).map
          (MulAut.conj g⁻¹).toMonoidHom := hmap.symm
    _ ≤ (Subgroup.centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊔ E).map
          (MulAut.conj g⁻¹).toMonoidHom := Subgroup.map_mono h
    _ ≤ Subgroup.centralizer (A : Set G) ⊔ E := by
        rw [Subgroup.map_sup, map_conj_eq_self_of_mem (X := E) (Subgroup.inv_mem E hgE)]
        refine sup_le ?_ le_sup_right
        refine (map_conj_centralizer_le (A.map (MulAut.conj g).toMonoidHom) g⁻¹).trans ?_
        rw [map_conj_inv]
        exact le_sup_left

/-- Hypothesis 2, transported to all non-cyclic `p`-subgroups of `E`. -/
private lemma normalizer_le_of_not_isCyclic_of_h2 {E W P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hEW : E ≤ W) (hPsyl : IsSylowIn p P E)
    (h2 : ∀ U : Subgroup G, U ≤ P → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ E))
    {A : Subgroup G} (hAE : A ≤ E) (hAp : IsPGroup p A) (hAnc : ¬ IsCyclic A) :
    Subgroup.normalizer (A : Set G) ⊓ W ≤ Subgroup.centralizer (A : Set G) ⊔ E := by
  obtain ⟨Q, hAQ, hQsyl⟩ := exists_isSylowIn_ge (p := p) (T := A) (X := E) hAE hAp
  obtain ⟨g, hgE, hg⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hQsyl hPsyl
  have hAp' : (A.map (MulAut.conj g).toMonoidHom) ≤ P :=
    (Subgroup.map_mono hAQ).trans (le_of_eq hg)
  have hAnc' : ¬ IsCyclic (A.map (MulAut.conj g).toMonoidHom) :=
    fun hc => hAnc ((isCyclic_map_conj_iff A g).mpr hc)
  have heq : Subgroup.normalizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊓ E) :=
    h2 (A.map (MulAut.conj g).toMonoidHom) hAp' hAnc'
  have h2A : Subgroup.normalizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊓ W ≤
      Subgroup.centralizer (A.map (MulAut.conj g).toMonoidHom : Set G) ⊔ E := by
    rw [heq]
    exact sup_le (pPrimeCoreSub_le_of_le (inf_le_left.trans le_sup_left))
      (inf_le_right.trans le_sup_right)
  exact le_centralizer_sup_of_le_centralizer_sup_map_conj hgE (hEW (Subgroup.inv_mem E hgE)) h2A


/-- `O_{p'}(X) = pPrimeCoreSub p X` written as the image of the `pPrimeCore` of `↥X`. -/
private lemma pPrimeCoreSub_eq_map (X : Subgroup G) :
    pPrimeCoreSub p X = (Work.Fitting.piCore (fun q => q ≠ p) ↥X).map X.subtype := by
  rw [pPrimeCoreSub, Work.GlaubermanZJ.pPrimeCore_eq_fitting p (Fact.out : p.Prime)]
  rfl

/-- `X` normalises `O_{p'}(X)`. -/
private lemma pPrimeCoreSub_le_normalizer (X : Subgroup G) :
    X ≤ Subgroup.normalizer (pPrimeCoreSub p X : Set G) := by
  have hpc := pPrimeCoreSub_eq_map (G := G) (p := p) X
  haveI hnrm : (Work.Fitting.piCore (fun q => q ≠ p) ↥X).Normal :=
    Work.Fitting.normal_sSup (fun N hN => hN.1)
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  rw [hpc] at hy ⊢
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹, hnrm.conj_mem k hk ⟨x, hx⟩, ?_⟩
  simp [MulAut.conj_apply]

/-- Conjugation by an element of `N_G(X)` sends `O_{p'}(X)` into itself: the conjugate
`O_{p'}(X)^b` is again a normal `p'`-subgroup of `X`. -/
private lemma map_conj_pPrimeCoreSub_le {X : Subgroup G} {b : G}
    (h : b ∈ Subgroup.normalizer (X : Set G)) :
    (pPrimeCoreSub p X).map (MulAut.conj b).toMonoidHom ≤ pPrimeCoreSub p X := by
  set A : Subgroup G := pPrimeCoreSub p X with hA
  set Ab : Subgroup G := A.map (MulAut.conj b).toMonoidHom with hAb
  have hpc := pPrimeCoreSub_eq_map (G := G) (p := p) X
  have hAX : A ≤ X := by rw [hA]; exact Subgroup.map_subtype_le _
  have hAnorm : X ≤ Subgroup.normalizer (A : Set G) := by
    rw [hA]; exact pPrimeCoreSub_le_normalizer X
  have hmapX : X.map (MulAut.conj b).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp h
  have hbinv : b⁻¹ ∈ Subgroup.normalizer (X : Set G) := Subgroup.inv_mem _ h
  have hconjX : ∀ g ∈ X, b⁻¹ * g * b ∈ X := fun g hg =>
    by simpa using (Subgroup.mem_normalizer_iff.mp hbinv g).mp hg
  -- `Ab` is a normal subgroup of `X`
  have hAbnorm : X ≤ Subgroup.normalizer (Ab : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg m hm
    rw [hAb, Subgroup.mem_map] at hm ⊢
    obtain ⟨a, ha, rfl⟩ := hm
    refine ⟨(b⁻¹ * g * b) * a * (b⁻¹ * g * b)⁻¹,
      (Subgroup.le_normalizer_iff.mp hAnorm (b⁻¹ * g * b) (hconjX g hg)) a ha, ?_⟩
    change (MulAut.conj b) ((b⁻¹ * g * b) * a * (b⁻¹ * g * b)⁻¹)
      = g * (MulAut.conj b) a * g⁻¹
    rw [MulAut.conj_apply, MulAut.conj_apply]; group
  have hAbX : Ab ≤ X := by
    rw [hAb]
    exact (Subgroup.map_mono hAX).trans (le_of_eq hmapX)
  -- `Ab` is a `p'`-group of the same order as `O_{p'}(X)`, so it is contained in `O_{p'}(X)`
  have hnormal : (Ab.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAbnorm
  have hispi : Work.Fitting.IsPiNat (fun q => q ≠ p) (Nat.card ↥(Ab.subgroupOf X)) := by
    rw [card_subgroupOf_eq Ab X hAbX, hAb, Subgroup.card_map_of_injective (MulAut.conj b).injective,
      hA, hpc, Subgroup.card_map_of_injective X.subtype_injective]
    exact Work.Fitting.piCore_isPiNat ↥X (fun q => q ≠ p)
  calc Ab = Ab ⊓ X := (inf_of_le_left hAbX).symm
    _ = (Ab.subgroupOf X).map X.subtype := (Subgroup.subgroupOf_map_subtype Ab X).symm
    _ ≤ (Work.Fitting.piCore (fun q => q ≠ p) ↥X).map X.subtype :=
        Subgroup.map_mono (Work.Fitting.le_piCore hnormal hispi)
    _ = pPrimeCoreSub p X := hpc.symm

/-- Conjugation by an element of `N_G(X)` preserves `O_{p'}(X)`. -/
private lemma map_conj_pPrimeCoreSub_eq {X : Subgroup G} {y : G}
    (h : y ∈ Subgroup.normalizer (X : Set G)) :
    (pPrimeCoreSub p X).map (MulAut.conj y).toMonoidHom = pPrimeCoreSub p X := by
  refine le_antisymm (map_conj_pPrimeCoreSub_le h) ?_
  have h2 := map_conj_pPrimeCoreSub_le (p := p) (X := X) (Subgroup.inv_mem _ h)
  calc pPrimeCoreSub p X
      = ((pPrimeCoreSub p X).map (MulAut.conj y⁻¹).toMonoidHom).map
          (MulAut.conj y).toMonoidHom := by
        rw [map_conj_map_conj, mul_inv_cancel]
        ext x
        simp
    _ ≤ (pPrimeCoreSub p X).map (MulAut.conj y).toMonoidHom := Subgroup.map_mono h2

/-- Conjugation by an element of `N_G(U)` preserves the centralizer `C_G(U)`. -/
private lemma map_conj_centralizer_eq {U : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (U : Set G)) :
    (Subgroup.centralizer (U : Set G)).map (MulAut.conj e).toMonoidHom
      = Subgroup.centralizer (U : Set G) := by
  have key : ∀ f ∈ Subgroup.normalizer (U : Set G),
      (Subgroup.centralizer (U : Set G)).map (MulAut.conj f).toMonoidHom
        ≤ Subgroup.centralizer (U : Set G) := by
    intro f hf x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro u hu
    have hmem : f⁻¹ * u * f ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hf (f⁻¹ * u * f)).mpr (by
        show f * (f⁻¹ * u * f) * f⁻¹ ∈ U
        rw [show f * (f⁻¹ * u * f) * f⁻¹ = u from by group]
        exact hu)
    calc u * (f * c * f⁻¹) = f * ((f⁻¹ * u * f) * c) * f⁻¹ := by group
      _ = f * (c * (f⁻¹ * u * f)) * f⁻¹ := by rw [hc (f⁻¹ * u * f) hmem]
      _ = (f * c * f⁻¹) * u := by group
  refine le_antisymm (key e he) ?_
  have h2 := key e⁻¹ (Subgroup.inv_mem _ he)
  calc Subgroup.centralizer (U : Set G)
      = ((Subgroup.centralizer (U : Set G)).map (MulAut.conj e⁻¹).toMonoidHom).map
          (MulAut.conj e).toMonoidHom := by
        rw [map_conj_map_conj, mul_inv_cancel]
        ext x
        simp
    _ ≤ (Subgroup.centralizer (U : Set G)).map (MulAut.conj e).toMonoidHom :=
        Subgroup.map_mono h2

/-- `N_G(U) ∩ W` normalises `C_G(U) ∩ W`. -/
private lemma normalizer_inf_le_normalizer_centralizer_inf {U W : Subgroup G} :
    Subgroup.normalizer (U : Set G) ⊓ W ≤
      Subgroup.normalizer ((Subgroup.centralizer (U : Set G) ⊓ W : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx c hc
  obtain ⟨hxN, hxW⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hcC, hcW⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨?_, W.mul_mem (W.mul_mem hxW hcW) (W.inv_mem hxW)⟩
  have hmem : x * c * x⁻¹ ∈ (Subgroup.centralizer (U : Set G)).map
      (MulAut.conj x).toMonoidHom := Subgroup.mem_map.mpr ⟨c, hcC, rfl⟩
  rwa [map_conj_centralizer_eq hxN] at hmem

/-- Extraction of the product form from the normaliser hypothesis
`N_W(U) = O_{p'}(C_W(U)) ⊔ N_E(U)`: `N_E(U)` normalises `O_{p'}(C_W(U))`, so the join is the
product. -/
private lemma exists_prod_of_mem_normalizer_eq {E U : Subgroup G} {x : G} (W : Subgroup G)
    (hEW : E ≤ W)
    (hx : x ∈ Subgroup.normalizer (U : Set G) ⊓ W)
    (heq : Subgroup.normalizer (U : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (U : Set G) ⊓ E)) :
    ∃ c : G, c ∈ Subgroup.centralizer (U : Set G) ∧ c ∈ W ∧
      ∃ e : G, e ∈ E ∧ e ∈ Subgroup.normalizer (U : Set G) ∧ x = c * e := by
  rw [heq] at hx
  have hnorm : Subgroup.normalizer (U : Set G) ⊓ E ≤
      Subgroup.normalizer
        (pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact map_conj_pPrimeCoreSub_eq (normalizer_inf_le_normalizer_centralizer_inf ⟨he.1, hEW he.2⟩)
  obtain ⟨c, hc, e, he, hce⟩ := Work.NormalComplement.CC.mem_sup_prod hnorm hx
  have hc' : c ∈ Subgroup.centralizer (U : Set G) ⊓ W := Subgroup.map_subtype_le _ hc
  exact ⟨c, hc'.1, hc'.2, e, he.2, he.1, hce.symm⟩

/-! ## Conjugation bookkeeping -/

/-- `A.map (conj 1) = A`. -/
private lemma map_conj_one_eq (A : Subgroup G) :
    A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x; simp [MulAut.conj_apply]
  rw [hone, Subgroup.map_id]

/-- `g w g⁻¹` normalises `A.map (conj g)` whenever `w` normalises `A`. -/
private lemma conj_mem_normalizer {A : Subgroup G} {g w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    g * w * g⁻¹ ∈ Subgroup.normalizer
      ((A.map (MulAut.conj g).toMonoidHom) : Subgroup G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hwA : A.map (MulAut.conj w).toMonoidHom = A :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  have hgwg : (g * w * g⁻¹) * g = g * w := by group
  calc (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (g * w * g⁻¹)).toMonoidHom
      = A.map (MulAut.conj ((g * w * g⁻¹) * g)).toMonoidHom := map_conj_map_conj A g (g * w * g⁻¹)
    _ = A.map (MulAut.conj (g * w)).toMonoidHom := by rw [hgwg]
    _ = (A.map (MulAut.conj w).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
        (map_conj_map_conj A w g).symm
    _ = A.map (MulAut.conj g).toMonoidHom := by rw [hwA]

/-! ## Product decomposition of `N_W(A)` from hypotheses 1 and 2 -/

/-- Hypothesis 1, transported along a Sylow conjugacy inside `E`: every element of `N_W(A)` for a
`p`-Sylow `A` of `E` is a product `c·e` with `c ∈ C_W(A)` and `e ∈ E ∩ N(A)`. -/
private lemma prod_of_mem_normalizer_eq_of_isSylowIn_of_h1 {E W P A : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hEW : E ≤ W) (hPsyl : IsSylowIn p P E)
    (h1 : Subgroup.normalizer (P : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (P : Set G) ⊓ E))
    (hA : IsSylowIn p A E) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G) ⊓ W) :
    ∃ c : G, c ∈ Subgroup.centralizer (A : Set G) ∧ c ∈ W ∧
      ∃ e : G, e ∈ E ∧ e ∈ Subgroup.normalizer (A : Set G) ∧ w = c * e := by
  obtain ⟨f, hfE, hf⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hA hPsyl
  have hfW : f ∈ W := hEW hfE
  have hzN : (MulAut.conj f) w ∈ Subgroup.normalizer (P : Set G) := by
    rw [← hf, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map.mpr ⟨w, hw.1, rfl⟩
  have hzW : (MulAut.conj f) w ∈ W := by
    have hval : (MulAut.conj f) w = f * w * f⁻¹ := MulAut.conj_apply f w
    rw [hval]; exact W.mul_mem (W.mul_mem hfW hw.2) (W.inv_mem hfW)
  obtain ⟨c, hcC, hcW, e, heE, heN, hce⟩ :=
    exists_prod_of_mem_normalizer_eq W hEW (Subgroup.mem_inf.mpr ⟨hzN, hzW⟩) h1
  have hce' : f * w * f⁻¹ = c * e := by simpa only [MulAut.conj_apply] using hce
  refine ⟨f⁻¹ * c * f, ?_, ?_, f⁻¹ * e * f, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff] at hcC ⊢
    intro a ha
    have haP : f * a * f⁻¹ ∈ P := by
      rw [← hf]
      exact Subgroup.mem_map.mpr ⟨a, ha,
        by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hc := hcC (f * a * f⁻¹) haP
    calc a * (f⁻¹ * c * f) = f⁻¹ * ((f * a * f⁻¹) * c) * f := by group
      _ = f⁻¹ * (c * (f * a * f⁻¹)) * f := by rw [hc]
      _ = (f⁻¹ * c * f) * a := by group
  · exact W.mul_mem (W.mul_mem (W.inv_mem hfW) hcW) hfW
  · exact E.mul_mem (E.mul_mem (E.inv_mem hfE) heE) hfE
  · have hAeq : P.map (MulAut.conj f⁻¹).toMonoidHom = A := by
      rw [← hf, map_conj_map_conj, inv_mul_cancel, map_conj_one_eq]
    have h := conj_mem_normalizer (A := P) (g := f⁻¹) heN
    rw [hAeq] at h
    simpa using h
  · calc w = f⁻¹ * (f * w * f⁻¹) * f := by group
      _ = f⁻¹ * (c * e) * f := by rw [hce']
      _ = (f⁻¹ * c * f) * (f⁻¹ * e * f) := by group

/-- Hypothesis 2, transported to all non-cyclic `p`-subgroups of `E`: every element of `N_W(A)` is a
product `c·e` with `c ∈ C_W(A)` and `e ∈ E ∩ N(A)`. -/
private lemma prod_of_mem_normalizer_eq_of_not_isCyclic_of_h2 {E W P A : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hEW : E ≤ W) (hPsyl : IsSylowIn p P E)
    (h2 : ∀ U : Subgroup G, U ≤ P → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ E))
    (hAE : A ≤ E) (hAp : IsPGroup p A) (hAnc : ¬ IsCyclic A) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G) ⊓ W) :
    ∃ c : G, c ∈ Subgroup.centralizer (A : Set G) ∧ c ∈ W ∧
      ∃ e : G, e ∈ E ∧ e ∈ Subgroup.normalizer (A : Set G) ∧ w = c * e := by
  obtain ⟨Q, hAQ, hQsyl⟩ := exists_isSylowIn_ge hAE hAp
  obtain ⟨g, hgE, hg⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hQsyl hPsyl
  have hgW : g ∈ W := hEW hgE
  have hB : A.map (MulAut.conj g).toMonoidHom ≤ P := by
    rw [← hg]; exact Subgroup.map_mono hAQ
  have hBnc : ¬ IsCyclic (A.map (MulAut.conj g).toMonoidHom) :=
    fun hc => hAnc ((isCyclic_map_conj_iff A g).mpr hc)
  have hzN : (MulAut.conj g) w ∈
      Subgroup.normalizer ((A.map (MulAut.conj g).toMonoidHom) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map.mpr ⟨w, hw.1, rfl⟩
  have hzW : (MulAut.conj g) w ∈ W := by
    have hval : (MulAut.conj g) w = g * w * g⁻¹ := MulAut.conj_apply g w
    rw [hval]; exact W.mul_mem (W.mul_mem hgW hw.2) (W.inv_mem hgW)
  obtain ⟨c, hcC, hcW, e, heE, heN, hce⟩ :=
    exists_prod_of_mem_normalizer_eq W hEW (Subgroup.mem_inf.mpr ⟨hzN, hzW⟩)
      (h2 _ hB hBnc)
  have hce' : g * w * g⁻¹ = c * e := by simpa only [MulAut.conj_apply] using hce
  have hAeq : (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
    rw [map_conj_map_conj, inv_mul_cancel, map_conj_one_eq]
  refine ⟨g⁻¹ * c * g, ?_, ?_, g⁻¹ * e * g, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff] at hcC ⊢
    intro a ha
    have haP : g * a * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, ha,
        by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hc := hcC (g * a * g⁻¹) haP
    calc a * (g⁻¹ * c * g) = g⁻¹ * ((g * a * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * a * g⁻¹)) * g := by rw [hc]
      _ = (g⁻¹ * c * g) * a := by group
  · exact W.mul_mem (W.mul_mem (W.inv_mem hgW) hcW) hgW
  · exact E.mul_mem (E.mul_mem (E.inv_mem hgE) heE) hgE
  · have h := conj_mem_normalizer (A := A.map (MulAut.conj g).toMonoidHom) (g := g⁻¹) heN
    rw [hAeq] at h
    simpa using h
  · calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
      _ = g⁻¹ * (c * e) * g := by rw [hce']
      _ = (g⁻¹ * c * g) * (g⁻¹ * e * g) := by group

/-! ## The criterion -/

/-- **Peterfalvi I Ch. III §1 Lemma 2, product form.**  Let `E ≤ W` be finite with `p ∣ |E|` and let
`P` be a `p`-Sylow of `E`.  If `N_W(P) = O_{p'}(C_W(P))·N_E(P)` and
`N_W(U) = O_{p'}(C_W(U))·N_E(U)` for every non-cyclic `U ≤ P`, then `E` is `p`-control in `W`. -/
theorem pcontrol_prod_v2 {E W : Subgroup G} (hEW : E ≤ W) (hpE : p ∣ Nat.card E)
    {P : Subgroup G} (hPsyl : IsSylowIn p P E)
    (h1 : Subgroup.normalizer (P : Set G) ⊓ W =
      pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (P : Set G) ⊓ E))
    (h2 : ∀ U : Subgroup G, U ≤ P → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ⊓ W =
        pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ E)) :
    IsPControl p E W := by
  have hP_W : IsSylowIn p P W := isSylowIn_of_sylowIn_normalizer hEW hPsyl h1
  refine ⟨hEW, ?_, ?_⟩
  · have hdiv : (E.subgroupOf W).index ∣ (P.subgroupOf W).index :=
      Subgroup.index_dvd_of_le (by
        intro x hx
        exact hPsyl.2.1 (by simpa [Subgroup.mem_subgroupOf] using hx))
    exact fun h => hP_W.2.2 (h.trans hdiv)
  · have key : ∀ A : Subgroup G, IsPGroup p A → A ≤ E → ∀ y : G, y ∈ W →
        A.map (MulAut.conj y⁻¹).toMonoidHom ≤ E →
        ∃ c : G, c ∈ Subgroup.centralizer (A : Set G) ∧ c ∈ W ∧
          ∃ e ∈ E, y = c * e := by
      suffices hmain : ∀ n : ℕ, ∀ A : Subgroup G, IsPGroup p A → A ≤ E →
          Nat.card P - Nat.card A = n → ∀ y : G, y ∈ W →
          A.map (MulAut.conj y⁻¹).toMonoidHom ≤ E →
          ∃ c : G, c ∈ Subgroup.centralizer (A : Set G) ∧ c ∈ W ∧
            ∃ e ∈ E, y = c * e by
        intro A hAp hAE y hyW hy
        exact hmain _ A hAp hAE rfl y hyW hy
      intro n
      refine Nat.strong_induction_on n ?_
      intro m ih A hAp hAE hmeasure y hyW hyconj
      set V : Subgroup G := A.map (MulAut.conj y⁻¹).toMonoidHom with hVdef
      have hVp : IsPGroup p V := hAp.map _
      by_cases hmax : Nat.card A = Nat.card P
      · -- base case: `A` is a `p`-Sylow of `E`
        have hAsyl : IsSylowIn p A E := isSylowIn_of_le_of_card_eq hAE hAp hPsyl hmax
        have hVsyl : IsSylowIn p V E := by
          refine isSylowIn_of_le_of_card_eq hyconj hVp hPsyl ?_
          rw [hVdef, Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective, hmax]
        obtain ⟨e, heE, he⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hVsyl hAsyl
        have hw : e * y⁻¹ ∈ Subgroup.normalizer (A : Set G) ⊓ W := by
          refine Subgroup.mem_inf.mpr ⟨?_, W.mul_mem (hEW heE) (W.inv_mem hyW)⟩
          rw [Subgroup.mem_normalizer_iff_map_conj_eq]
          have hstep : A.map (MulAut.conj (e * y⁻¹)).toMonoidHom = A := by
            rw [← map_conj_map_conj A y⁻¹ e, ← hVdef, he]
          exact hstep
        obtain ⟨c₁, hc₁C, hc₁W, e₁, he₁E, he₁N, heq₁⟩ :=
          prod_of_mem_normalizer_eq_of_isSylowIn_of_h1 hEW hPsyl h1 hAsyl hw
        have hc1 : e₁⁻¹ * c₁ * e₁ ∈ Subgroup.centralizer (A : Set G) := by
          rw [Subgroup.mem_centralizer_iff] at hc₁C ⊢
          intro a ha
          have ha' : e₁ * a * e₁⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp he₁N a).mp ha
          have hc := hc₁C (e₁ * a * e₁⁻¹) ha'
          calc a * (e₁⁻¹ * c₁ * e₁) = e₁⁻¹ * ((e₁ * a * e₁⁻¹) * c₁) * e₁ := by group
            _ = e₁⁻¹ * (c₁ * (e₁ * a * e₁⁻¹)) * e₁ := by rw [hc]
            _ = (e₁⁻¹ * c₁ * e₁) * a := by group
        refine ⟨e₁⁻¹ * c₁⁻¹ * e₁, ?_, ?_, e₁⁻¹ * e, ?_, ?_⟩
        · simpa [mul_inv_rev, mul_assoc]
            using Subgroup.inv_mem (Subgroup.centralizer (A : Set G)) hc1
        · exact W.mul_mem (W.mul_mem (W.inv_mem (hEW he₁E)) (W.inv_mem hc₁W)) (hEW he₁E)
        · exact E.mul_mem (E.inv_mem he₁E) heE
        · calc y = (e * y⁻¹)⁻¹ * e := by group
            _ = (c₁ * e₁)⁻¹ * e := by rw [heq₁]
            _ = e₁⁻¹ * c₁⁻¹ * e := by group
            _ = (e₁⁻¹ * c₁⁻¹ * e₁) * (e₁⁻¹ * e) := by group
      · -- recursion: `A` is not Sylow, enlarge it to a Sylow of `N_E(A)`
        have hAltAP : Nat.card A < Nat.card P :=
          lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos
            (card_dvd_card_of_isPGroup_of_isSylowIn hAE hAp hPsyl)) hmax
        obtain ⟨Q, hAQ, hQsyl⟩ := exists_isSylowIn_ge hAE hAp
        have hQcard : Nat.card Q = Nat.card P := card_eq_of_isSylowIn_of_isSylowIn hQsyl hPsyl
        have hAltQ : A < Q := lt_of_le_of_ne hAQ (fun h => hmax (by rw [h, hQcard]))
        have hleA : A ≤ Q ⊓ Subgroup.normalizer (A : Set G) := le_inf hAQ Subgroup.le_normalizer
        have hcardNQA : Nat.card A < Nat.card ↥(Q ⊓ Subgroup.normalizer (A : Set G)) := by
          have h1c : Nat.card A ∣ Nat.card ↥(Q ⊓ Subgroup.normalizer (A : Set G)) := by
            rw [← card_subgroupOf_eq A _ hleA]
            exact Subgroup.card_subgroup_dvd_card _
          refine lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos h1c) fun hc => ?_
          have heq : A = Q ⊓ Subgroup.normalizer (A : Set G) :=
            Subgroup.eq_of_le_of_card_ge hleA (le_of_eq hc.symm)
          exact (lt_inf_normalizer_of_isPGroup hAltQ hQsyl.1).2 (le_of_eq heq.symm)
        have hTle : Q ⊓ Subgroup.normalizer (A : Set G) ≤
            Subgroup.normalizer (A : Set G) ⊓ E :=
          le_inf inf_le_right (inf_le_left.trans hQsyl.2.1)
        obtain ⟨S, hNQS, hSsyl⟩ := exists_isSylowIn_ge hTle hQsyl.1.to_inf_left
        have hAS : A ≤ S := hleA.trans hNQS
        have hAltS : Nat.card A < Nat.card S :=
          lt_of_lt_of_le hcardNQA (card_le_card_of_le hNQS)
        have hlt' : Nat.card P - Nat.card S < m := by
          rw [← hmeasure]; omega
        have hS_NWA : IsSylowIn p S (Subgroup.normalizer (A : Set G) ⊓ W) :=
          sylow_normalizer_transfer hEW hPsyl h1 h2 hAE hAp hSsyl
        obtain ⟨S₁, -, hS₁syl⟩ := exists_isSylowIn_ge (T := ⊥)
          (X := Subgroup.normalizer (V : Set G) ⊓ E) bot_le (IsPGroup.of_bot (p := p))
        have hS₁_NWV : IsSylowIn p S₁ (Subgroup.normalizer (V : Set G) ⊓ W) :=
          sylow_normalizer_transfer hEW hPsyl h1 h2 hyconj hVp hS₁syl
        have hT2 : IsSylowIn p (S₁.map (MulAut.conj y).toMonoidHom)
            ((Subgroup.normalizer (V : Set G) ⊓ W).map (MulAut.conj y).toMonoidHom) :=
          isSylowIn_map_conj hS₁_NWV y
        have hVmap : V.map (MulAut.conj y).toMonoidHom = A := by
          rw [hVdef, map_conj_map_conj, mul_inv_cancel, map_conj_one_eq]
        have hmap2 : (Subgroup.normalizer (V : Set G) ⊓ W).map (MulAut.conj y).toMonoidHom =
            Subgroup.normalizer (A : Set G) ⊓ W := by
          rw [Subgroup.map_inf _ _ _ (MulAut.conj y).injective,
            Subgroup.map_equiv_normalizer_eq, hVmap, map_conj_eq_self_of_mem (X := W) hyW]
        have hT2' : IsSylowIn p (S₁.map (MulAut.conj y).toMonoidHom)
            (Subgroup.normalizer (A : Set G) ⊓ W) := by rw [← hmap2]; exact hT2
        have step : ∀ z : G, z ∈ W →
            S.map (MulAut.conj z).toMonoidHom = S₁.map (MulAut.conj y).toMonoidHom →
            ∃ c : G, c ∈ Subgroup.centralizer (S : Set G) ∧ c ∈ W ∧
              ∃ e ∈ E, z⁻¹ * y = c * e := by
          intro z hzW hzS
          have hwW : z⁻¹ * y ∈ W := W.mul_mem (W.inv_mem hzW) hyW
          have hwconj : S.map (MulAut.conj (z⁻¹ * y)⁻¹).toMonoidHom ≤ E := by
            have h1' : (z⁻¹ * y)⁻¹ = y⁻¹ * z := by group
            rw [h1', ← map_conj_map_conj S z y⁻¹, hzS, map_conj_inv]
            exact hS₁syl.2.1.trans inf_le_right
          exact ih (Nat.card P - Nat.card S) hlt' S hSsyl.1 (hSsyl.2.1.trans inf_le_right) rfl
            (z⁻¹ * y) hwW hwconj
        by_cases hcyc : IsCyclic A
        · -- `A` cyclic: the Sylow-conjugating element lies in `C_W(A)`
          obtain ⟨z, hz, hzS⟩ := conj_sylow_of_isCyclic (W := W) (U := A)
            (hAE.trans hEW) hcyc hS_NWA hT2'
          obtain ⟨c₂, hc₂C, hc₂W, e₂, he₂E, heq₂⟩ := step z hz.2 hzS
          refine ⟨z * c₂, ?_, mul_mem hz.2 hc₂W, e₂, he₂E, ?_⟩
          · exact Subgroup.mul_mem _ hz.1
              (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAS) hc₂C)
          · calc y = z * (z⁻¹ * y) := by group
              _ = z * (c₂ * e₂) := by rw [heq₂]
              _ = (z * c₂) * e₂ := by group
        · -- `A` non-cyclic: hypothesis 2 applies
          obtain ⟨z, hz, hzS⟩ := exists_conj_eq_of_isSylowIn_of_isSylowIn hS_NWA hT2'
          obtain ⟨c₁, hc₁C, hc₁W, e₁, he₁E, he₁N, hz_eq⟩ :=
            prod_of_mem_normalizer_eq_of_not_isCyclic_of_h2 hEW hPsyl h2 hAE hAp hcyc
              ⟨hz.1, hz.2⟩
          obtain ⟨c₂, hc₂C, hc₂W, e₂, he₂E, heq₂⟩ := step z hz.2 hzS
          have hc₂'A : c₂ ∈ Subgroup.centralizer (A : Set G) :=
            Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAS) hc₂C
          have he₁c₂ : e₁ * c₂ * e₁⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
            rw [Subgroup.mem_centralizer_iff] at hc₂'A ⊢
            intro u hu
            have hmem : e₁⁻¹ * u * e₁ ∈ A :=
              by simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ he₁N) u).mp hu
            have hc := hc₂'A (e₁⁻¹ * u * e₁) hmem
            calc u * (e₁ * c₂ * e₁⁻¹) = e₁ * ((e₁⁻¹ * u * e₁) * c₂) * e₁⁻¹ := by group
              _ = e₁ * (c₂ * (e₁⁻¹ * u * e₁)) * e₁⁻¹ := by rw [hc]
              _ = (e₁ * c₂ * e₁⁻¹) * u := by group
          refine ⟨c₁ * (e₁ * c₂ * e₁⁻¹), Subgroup.mul_mem _ hc₁C he₁c₂,
            mul_mem hc₁W (mul_mem (mul_mem (hEW he₁E) hc₂W) (inv_mem (hEW he₁E))),
            e₁ * e₂, E.mul_mem he₁E he₂E, ?_⟩
          calc y = z * (z⁻¹ * y) := by group
            _ = (c₁ * e₁) * (c₂ * e₂) := by rw [heq₂, hz_eq]
            _ = (c₁ * (e₁ * c₂ * e₁⁻¹)) * (e₁ * e₂) := by group
    intro U hUE hUp x hxW hconj
    by_cases hU : U = ⊥
    · subst hU
      refine ⟨x, ?_, 1, E.one_mem, by simp⟩
      rw [Subgroup.mem_inf]
      refine ⟨?_, hxW⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu1 : u = 1 := by simpa using hu
      subst hu1; simp
    · obtain ⟨c, hcC, hcW, e, heE, heq⟩ := key U hUp hUE x hxW hconj
      exact ⟨c, Subgroup.mem_inf.mpr ⟨hcC, hcW⟩, e, heE, heq⟩

end Work.NormalComplement
