/-
# Peterfalvi I Ch. III §5 Prop. 3, last step: `N_G(C) ≤ N_G(F(V))`

Let `F = F(V) = fitSub V` be the Fitting subgroup of `V`.  Suppose

* `F ≤ C` (`C = C_H(N)` in the application),
* some conjugate of `C` lies in `V` (`C ^ g ≤ V`),
* `F` is a Sylow `r`-subgroup of `V`.

Then every `x ∈ N_G(C)` normalises `F`.

The mathematical content: a Fitting subgroup which is an `r`-group is necessarily the (normal)
Sylow `r`-subgroup `O_r` of its group, so `F` is the unique Sylow `r`-subgroup of `V`; for
`W = V ^ g⁻¹ ⊇ C` the same holds for `F(W) = F ^ g⁻¹`, and since `F ≤ C ≤ W` has the order of a
Sylow `r`-subgroup of `W`, one gets `F = F ^ g⁻¹ = F(W)`, so `F` is normal in `W`, hence in `C`.
Then `F ⊴ C` is a Sylow `r`-subgroup of `C`; the conjugate `F ^ x ≤ C` (`x ∈ N_G(C)`) is an
`r`-subgroup of `W` of the order of `F`, hence is contained in `F`, so `F ^ x = F`.

The proof uses only the single counting fact that a `p`-subgroup of `X` has order dividing that of
a `p`-Sylow of `X` (no Sylow conjugacy/uniqueness machinery), plus transport of `IsSylowIn` and of
the Fitting subgroup along an automorphism of the ambient group.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.NormalComplement.Sec3Aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1000000

namespace Work.NormalComplement.Sec5Fix.NF

open Classical
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## Auxiliary general lemmas -/

/-- For `A ≤ B`, the order of `A` divides the order of `B`. -/
private theorem aux_card_dvd_card_of_le {A B : Subgroup G} (h : A ≤ B) :
    Nat.card ↥A ∣ Nat.card ↥B := by
  have h1 : Nat.card ↥A = Nat.card ↥(A.subgroupOf B) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv).symm
  rw [h1]
  exact Subgroup.card_subgroup_dvd_card (A.subgroupOf B)

/-- A `p`-subgroup of `X` has order dividing the order of a `p`-Sylow of `X`. -/
private theorem aux_card_dvd_card_of_isPGroup_of_isSylowIn [Finite G] {p : ℕ} [Fact p.Prime]
    {U P X : Subgroup G} (hUX : U ≤ X) (hU : IsPGroup p U)
    (hP : Work.NormalComplement.IsSylowIn p P X) : Nat.card ↥U ∣ Nat.card ↥P := by
  have h1 : Nat.card ↥U ∣ Nat.card ↥X := aux_card_dvd_card_of_le hUX
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
  have hc : Nat.card ↥(P.subgroupOf X) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.2.1).toEquiv
  have h2 : Nat.card ↥X = (P.subgroupOf X).index * Nat.card ↥P := by
    rw [← Subgroup.index_mul_card (P.subgroupOf X), hc]
  have h3 : p ^ k ∣ Nat.card ↥P * (P.subgroupOf X).index := by
    rw [mul_comm (Nat.card ↥P), ← h2, ← hk]
    exact h1
  have h4 : Nat.Coprime (p ^ k) (P.subgroupOf X).index :=
    Nat.Coprime.pow_left _ ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hP.2.2)
  rw [hk]
  exact h4.dvd_of_dvd_mul_right h3

/-- An automorphism of `G` maps a `p`-Sylow of a subgroup `X` to a `p`-Sylow of the image of `X`. -/
private theorem aux_isSylowIn_map_mulEquiv {p : ℕ} {A X : Subgroup G} (φ : G ≃* G)
    (hA : Work.NormalComplement.IsSylowIn p A X) :
    Work.NormalComplement.IsSylowIn p (A.map φ.toMonoidHom) (X.map φ.toMonoidHom) := by
  refine ⟨hA.1.map φ.toMonoidHom, Subgroup.map_mono hA.2.1, ?_⟩
  have h : ((A.map φ.toMonoidHom).subgroupOf (X.map φ.toMonoidHom)).index =
      (A.subgroupOf X).index := by
    rw [← Subgroup.relIndex, ← Subgroup.relIndex]
    exact Subgroup.relIndex_map_map_of_injective A X φ.injective
  rw [h]
  exact hA.2.2

/-- The Fitting subgroup of a subgroup commutes with an automorphism of the ambient group:
`F(X ^ e) = F(X) ^ e`. -/
private theorem aux_fitSub_map_mulEquiv [Finite G] (e : G ≃* G) (X : Subgroup G) :
    Work.NormalComplement.Design.fitSub (X.map e.toMonoidHom) =
      (Work.NormalComplement.Design.fitSub X).map e.toMonoidHom := by
  haveI : Finite ↥X := Subtype.finite
  have hcomp : (X.map e.toMonoidHom).subtype.comp
        (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective).toMonoidHom =
      e.toMonoidHom.comp X.subtype := by
    ext x
    rfl
  calc Work.NormalComplement.Design.fitSub (X.map e.toMonoidHom)
      = (Work.Fitting.fitting ↥(X.map e.toMonoidHom)).map
          (X.map e.toMonoidHom).subtype := rfl
    _ = ((Work.Fitting.fitting ↥X).map
          (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective).toMonoidHom).map
          (X.map e.toMonoidHom).subtype := by
        rw [Work.NormalComplement.fitting_map_mulEquiv
          (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective)]
    _ = (Work.Fitting.fitting ↥X).map ((X.map e.toMonoidHom).subtype.comp
          (Subgroup.equivMapOfInjective X e.toMonoidHom e.injective).toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = (Work.Fitting.fitting ↥X).map (e.toMonoidHom.comp X.subtype) := by rw [hcomp]
    _ = ((Work.Fitting.fitting ↥X).map X.subtype).map e.toMonoidHom := by
        rw [Subgroup.map_map]
    _ = (Work.NormalComplement.Design.fitSub X).map e.toMonoidHom := rfl

/-- If `A` is a `p`-Sylow subgroup of `X`, `B ≤ X` is a `p`-subgroup normalising `A` (so that
`A ⊔ B` is a `p`-subgroup of `X`) and `|A| = |B|`, then `A = B`. -/
private theorem aux_eq_of_isSylowIn_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {A B X : Subgroup G} (hA : Work.NormalComplement.IsSylowIn p A X) (hBX : B ≤ X)
    (hB : IsPGroup p B) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hcard : Nat.card ↥A = Nat.card ↥B) : A = B := by
  have hsup : IsPGroup p ↥(A ⊔ B) := IsPGroup.to_sup_of_normal_left' hA.1 hB hBA
  have hsub : A ⊔ B ≤ X := sup_le hA.2.1 hBX
  have hdvd : Nat.card ↥(A ⊔ B) ∣ Nat.card ↥A :=
    aux_card_dvd_card_of_isPGroup_of_isSylowIn hsub hsup hA
  have h1 : Nat.card ↥B ∣ Nat.card ↥(A ⊔ B) := aux_card_dvd_card_of_le le_sup_right
  have h2 : Nat.card ↥(A ⊔ B) = Nat.card ↥B := Nat.dvd_antisymm (hcard ▸ hdvd) h1
  have h3 : B = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (le_of_eq h2)
  exact Subgroup.eq_of_le_of_card_ge (h3.symm ▸ le_sup_left) (le_of_eq hcard.symm)

/-! ## The main lemma -/

/-- The main step, with the conjugating element replaced by an arbitrary automorphism of `G`:
for `C ^ σ ≤ V` and `F(V) ≤ C`, the normalizer of `C` normalises `F(V)`. -/
private theorem normalizer_fitSub_of_map_le [Finite G] {r : ℕ} [Fact r.Prime]
    {V C : Subgroup G} (hFC : Work.NormalComplement.Design.fitSub V ≤ C) (σ : G ≃* G)
    (hg : C.map σ.toMonoidHom ≤ V)
    (hsyl : Work.NormalComplement.IsSylowIn r (Work.NormalComplement.Design.fitSub V) V)
    {x : G} (hx : x ∈ Subgroup.normalizer (C : Set G)) :
    x ∈ Subgroup.normalizer
      ((Work.NormalComplement.Design.fitSub V : Subgroup G) : Set G) := by
  classical
  -- ## `C ≤ W`, where `W = V ^ σ⁻¹`
  have hCW : C ≤ V.map σ.symm.toMonoidHom := by
    have h2 : (C.map σ.toMonoidHom).map σ.symm.toMonoidHom ≤ V.map σ.symm.toMonoidHom :=
      Subgroup.map_mono (f := σ.symm.toMonoidHom) hg
    have h3 : (C.map σ.toMonoidHom).map σ.symm.toMonoidHom = C := by
      rw [Subgroup.map_map]
      have hid : σ.symm.toMonoidHom.comp σ.toMonoidHom = MonoidHom.id G := by
        ext y
        simp
      rw [hid, Subgroup.map_id]
    rwa [h3] at h2
  -- ## `F(W) = F(V) ^ σ⁻¹` is a Sylow `r`-subgroup of `W`, normal in `W`
  have hfitW : Work.NormalComplement.Design.fitSub (V.map σ.symm.toMonoidHom) =
      (Work.NormalComplement.Design.fitSub V).map σ.symm.toMonoidHom :=
    aux_fitSub_map_mulEquiv σ.symm V
  have hFsylW : Work.NormalComplement.IsSylowIn r
      (Work.NormalComplement.Design.fitSub (V.map σ.symm.toMonoidHom))
      (V.map σ.symm.toMonoidHom) := by
    rw [hfitW]
    exact aux_isSylowIn_map_mulEquiv σ.symm hsyl
  have hWnorm : V.map σ.symm.toMonoidHom ≤ Subgroup.normalizer
      (Work.NormalComplement.Design.fitSub (V.map σ.symm.toMonoidHom) : Set G) :=
    Work.NormalComplement.fitSub_le_normalizer _
  have hFWle : Work.NormalComplement.Design.fitSub V ≤ V.map σ.symm.toMonoidHom :=
    hFC.trans hCW
  have hcardW : Nat.card ↥(Work.NormalComplement.Design.fitSub (V.map σ.symm.toMonoidHom)) =
      Nat.card ↥(Work.NormalComplement.Design.fitSub V) := by
    rw [hfitW, Subgroup.card_map_of_injective σ.symm.injective]
  -- ## `F(V) = F(W)`, so `F(V)` is normal in `W`
  have hFeq : Work.NormalComplement.Design.fitSub V =
      Work.NormalComplement.Design.fitSub (V.map σ.symm.toMonoidHom) :=
    (aux_eq_of_isSylowIn_of_isPGroup hFsylW hFWle hsyl.1 (hFWle.trans hWnorm) hcardW).symm
  have hWleNF : V.map σ.symm.toMonoidHom ≤
      Subgroup.normalizer (Work.NormalComplement.Design.fitSub V : Set G) := by
    have h := hWnorm
    rwa [← hFeq] at h
  have hCleNF : C ≤ Subgroup.normalizer (Work.NormalComplement.Design.fitSub V : Set G) :=
    hCW.trans hWleNF
  -- ## `x` normalises `F(V)`
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  have hxF : C.map (MulAut.conj x).toMonoidHom = C := hx
  have hBleC : (Work.NormalComplement.Design.fitSub V).map
      (MulAut.conj x).toMonoidHom ≤ C := by
    have h := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hFC
    rwa [hxF] at h
  have hFsylV : Work.NormalComplement.IsSylowIn r (Work.NormalComplement.Design.fitSub V)
      (V.map σ.symm.toMonoidHom) := hFeq.symm ▸ hFsylW
  have hcardB : Nat.card ↥(Work.NormalComplement.Design.fitSub V) =
      Nat.card ↥((Work.NormalComplement.Design.fitSub V).map
        (MulAut.conj x).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).symm
  exact (aux_eq_of_isSylowIn_of_isPGroup hFsylV (hBleC.trans hCW)
    (hsyl.1.map (MulAut.conj x).toMonoidHom) (hBleC.trans hCleNF) hcardB).symm

theorem normalizer_fitSub_of_conj_le {G : Type} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {V C : Subgroup G}
    (hFC : Work.NormalComplement.Design.fitSub V ≤ C)
    (hg : ∃ g : G, C.map (MulAut.conj g).toMonoidHom ≤ V)
    (hsyl : Work.NormalComplement.IsSylowIn r (Work.NormalComplement.Design.fitSub V) V)
    {x : G} (hx : x ∈ Subgroup.normalizer (C : Set G)) :
    x ∈ Subgroup.normalizer
      ((Work.NormalComplement.Design.fitSub V : Subgroup G) : Set G) := by
  obtain ⟨g, hg⟩ := hg
  exact normalizer_fitSub_of_map_le hFC (MulAut.conj g) hg hsyl hx

end Work.NormalComplement.Sec5Fix.NF
