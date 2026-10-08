/-
# The `p`-control criterion (Peterfalvi I, Ch. III §1, Lemma 2)

Peterfalvi, *Le théorème de Bender–Suzuki I*, Astérisque 142–143 (1986), Ch. III §1, Lemma 2
(p. 173) reads:

> Let `E ≤ W` be finite, let `p` be a prime dividing `|E|`, and let `P` be a `p`-Sylow of `E`.
> Suppose
> 1. `N_W(P) = O_{p'}(C_W(P))·N_E(P)`;
> 2. for every non-cyclic subgroup `U` of `P`, `N_W(U) = O_{p'}(C_W(U))·N_E(U)`.
> Then `E` is a `p`-control group in `W`.

This file proves the formal counterpart `pcontrol_criterion` in
`Submission.Work.NormalComplement.Defs`'s vocabulary.

Outline of the proof (the source's argument):

* Hypothesis 1 forces `P` to be a `p`-Sylow of `W` (the `O_{p'}`-factor is a normal `p'`-subgroup
  of `N_W(P)`, whence `|N_W(P)|` has the same `p`-part as `|N_E(P)| = |P|`, and a `p`-subgroup
  which is Sylow in its own normaliser is Sylow).
* One then proves by strong induction on `|P| - |U|` the statement

  `(∗)   U ≤ E a p-subgroup, x ∈ W, U^{x⁻¹} ≤ E ⇒ x ∈ C(U)·E`

  for every `p`-subgroup `U ≤ E`, and concludes (the formal statement of `IsPControl` asks the
  equivalent left-conjugation form).
* The inductive step replaces `U` by a strictly larger `p`-subgroup `S ≤ E` (a `p`-Sylow of
  `N_E(U)`) using a `p`-Sylow `S₁` of `N_E(U^{x⁻¹})` and the fact that `p`-Sylows of `N_E(V)` are
  `p`-Sylows of `N_W(V)` (the "transfer" step of the source).  If `U` is not cyclic, hypothesis 2
  transfers to all non-cyclic `p`-subgroups of `E` and gives the conclusion; if `U` is cyclic the
  conjugating element can be chosen in `C_W(U)` because `N/C` embeds in the abelian group `Aut(U)`.
* The base case `|U| = |P|` uses hypothesis 1, transported along an `E`-conjugation (which is what
  the Sylow conjugacy and the normaliser/centraliser bookkeeping below provide).
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.isSylowIn_of_sylowIn_normalizer
import Submission.Work.NormalComplement.conj_sylow_of_isCyclic
import Submission.Work.NormalComplement.sylow_normalizer_transfer
import Submission.Work.NormalComplement.pcontrol_prod_v2
-- `appI_five_d_corrected` exports `isSylowIn_map_conj`, which this file also states (privately, to
-- avoid a duplicate declaration when both are imported by `Main`).
import Submission.Work.NormalComplement.appI_five_d_corrected

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 4000000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type*} [Group G] [Finite G]

/-! ## Elementary subgroup and counting lemmas -/

/-- `A.subgroupOf Y ⊓ B.subgroupOf Y = (A ⊓ B).subgroupOf Y`. -/
lemma inf_subgroupOf_symm (A B Y : Subgroup G) :
    A.subgroupOf Y ⊓ B.subgroupOf Y = (A ⊓ B).subgroupOf Y := by
  ext x
  simp [Subgroup.mem_subgroupOf]

/-- `|H ⊔ K| · |H ⊓ K| = |H| · |K|` for `K` normal.  (Private: the module
`Work.NormalComplement.card_sup_mul_card_inf` exports a public lemma of the same name, and both are
reachable from `Main`.) -/
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
lemma card_sup_mul_card_inf_of_le_normalizer (A B : Subgroup G)
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
lemma card_subgroupOf_eq (H Y : Subgroup G) (h : H ≤ Y) :
    Nat.card ↥(H.subgroupOf Y) = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

/-- Conjugation by an element of `X` fixes `X`. -/
lemma map_conj_eq_self_of_mem {X : Subgroup G} {x : G} (hx : x ∈ X) :
    X.map (MulAut.conj x).toMonoidHom = X :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)

variable {p : ℕ} [Fact p.Prime]

/-- `S` a `p`-Sylow of `X` and `O` a `p'`-group normalised by `O ⊔ X` imply that `S` is a
`p`-Sylow of `O ⊔ X`. -/
lemma isSylowIn_sup_of_le_normalizer_of_not_dvd_card {O X S : Subgroup G}
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
lemma lt_inf_normalizer_of_isPGroup {Q U : Subgroup G} (hUQ : U < Q) (hQ : IsPGroup p Q) :
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
lemma card_dvd_card_of_isPGroup_of_isSylowIn {U P X : Subgroup G} (hUX : U ≤ X)
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
lemma exists_isSylowIn_ge {T X : Subgroup G} (hTX : T ≤ X) (hT : IsPGroup p T) :
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
lemma card_eq_of_isSylowIn_of_isSylowIn {A B X : Subgroup G} (hA : IsSylowIn p A X)
    (hB : IsSylowIn p B X) : Nat.card A = Nat.card B :=
  le_antisymm (Nat.le_of_dvd (Nat.card_pos)
      (card_dvd_card_of_isPGroup_of_isSylowIn hA.2.1 hA.1 hB))
    (Nat.le_of_dvd (Nat.card_pos)
      (card_dvd_card_of_isPGroup_of_isSylowIn hB.2.1 hB.1 hA))

/-- Two `p`-Sylows of the same subgroup are conjugate. -/
lemma exists_conj_eq_of_isSylowIn_of_isSylowIn {A B X : Subgroup G} (hA : IsSylowIn p A X)
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
lemma isSylowIn_of_le_of_card_eq {U P X : Subgroup G} (hUX : U ≤ X) (hU : IsPGroup p U)
    (hP : IsSylowIn p P X) (hcard : Nat.card U = Nat.card P) : IsSylowIn p U X := by
  obtain ⟨Q, hUQ, hQsyl⟩ := exists_isSylowIn_ge hUX hU
  have hQcard : Nat.card Q = Nat.card U :=
    (card_eq_of_isSylowIn_of_isSylowIn hQsyl hP).trans hcard.symm
  have hQU : U = Q := Subgroup.eq_of_le_of_card_ge hUQ (le_of_eq hQcard)
  rwa [hQU]

/-- Conjugating a `p`-Sylow gives a `p`-Sylow of the conjugate.  (Unused here: the public copy
from `appI_five_d_corrected` is imported below and serves the users of this module.) -/
private lemma isSylowIn_map_conj_aux {A X : Subgroup G} (hA : IsSylowIn p A X) (g : G) :
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
lemma map_conj_centralizer_le (X : Subgroup G) (g : G) :
    (Subgroup.centralizer (X : Set G)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ((X.map (MulAut.conj g).toMonoidHom) : Set G) := by
  have h := Subgroup.map_centralizer_le_centralizer_image (X : Set G)
    (MulAut.conj g).toMonoidHom
  have h2 : (MulAut.conj g).toMonoidHom '' (X : Set G) =
      ↑(X.map (MulAut.conj g).toMonoidHom) :=
    (Subgroup.coe_map (MulAut.conj g).toMonoidHom X).symm
  rwa [h2] at h

/-- Conjugation is compatible with composition. -/
lemma map_conj_map_conj (A : Subgroup G) (a b : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Conjugating by `a` and then by `a⁻¹` is the identity. -/
lemma map_conj_inv (A : Subgroup G) (a : G) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = A := by
  rw [map_conj_map_conj, inv_mul_cancel]
  ext x
  simp [Subgroup.mem_map]

/-- Monotonicity of the order of a subgroup. -/
lemma card_le_card_of_le {H K : Subgroup G} (h : H ≤ K) : Nat.card H ≤ Nat.card K :=
  Nat.le_of_dvd Nat.card_pos (by
    rw [← card_subgroupOf_eq H K h]
    exact Subgroup.card_subgroup_dvd_card (H.subgroupOf K))

/-- Cyclicity is preserved by conjugation. -/
lemma isCyclic_map_conj_iff (A : Subgroup G) (g : G) :
    IsCyclic A ↔ IsCyclic (A.map (MulAut.conj g).toMonoidHom) :=
  MulEquiv.isCyclic (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective)

/-- `O_{p'}(X) ≤ Y` for `X ≤ Y`. -/
lemma pPrimeCoreSub_le_of_le {X Y : Subgroup G} (h : X ≤ Y) : pPrimeCoreSub p X ≤ Y :=
  (Subgroup.map_subtype_le (pPrimeCore p ↥X)).trans h

/-! ## Transporting the two hypotheses to `E`-conjugates -/

/-- Hypothesis 1, transported to all `p`-Sylows of `E` (which are exactly the `E`-conjugates
of `P`). -/
lemma normalizer_le_of_isSylowIn_of_h1 {E W P : Subgroup G} {p : ℕ} [Fact p.Prime]
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
lemma le_centralizer_sup_of_le_centralizer_sup_map_conj {A E W : Subgroup G}
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
lemma normalizer_le_of_not_isCyclic_of_h2 {E W P : Subgroup G} {p : ℕ} [Fact p.Prime]
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

theorem pcontrol_criterion {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E W : Subgroup G} (hEW : E ≤ W) (hpE : p ∣ Nat.card E) {P : Subgroup G}
    (hPsyl : Work.NormalComplement.IsSylowIn p P E)
    (h1 : Subgroup.normalizer (P : Set G) ⊓ W =
      Work.NormalComplement.pPrimeCoreSub p (Subgroup.centralizer (P : Set G) ⊓ W) ⊔
        (Subgroup.normalizer (P : Set G) ⊓ E))
    (h2 : ∀ U : Subgroup G, U ≤ P → ¬ IsCyclic U →
      Subgroup.normalizer (U : Set G) ⊓ W =
        Work.NormalComplement.pPrimeCoreSub p (Subgroup.centralizer (U : Set G) ⊓ W) ⊔
          (Subgroup.normalizer (U : Set G) ⊓ E)) :
    Work.NormalComplement.IsPControl p E W := by
  exact pcontrol_prod_v2 hEW hpE hPsyl h1 h2
