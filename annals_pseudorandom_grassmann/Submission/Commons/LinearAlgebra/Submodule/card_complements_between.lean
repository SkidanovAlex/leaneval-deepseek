import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_complements
import Submission.Commons.LinearAlgebra.Submodule.finrank_map_mkQ_of_le

namespace Commons.LinearAlgebra.Submodule

open Module

noncomputable section

/-- If the kernel of `f` is contained in both `p` and `q`, then `map f` commutes with `⊓`. -/
theorem map_inf_eq_map_inf_of_ker_le {K : Type*} [Field K] {M : Type*} [AddCommGroup M]
    [Module K M] {N : Type*} [AddCommGroup N] [Module K N] (f : M →ₗ[K] N)
    {p q : Submodule K M} (_hp : LinearMap.ker f ≤ p) (hq : LinearMap.ker f ≤ q) :
    Submodule.map f (p ⊓ q) = Submodule.map f p ⊓ Submodule.map f q := by
  rw [Submodule.map_inf_eq_map_inf_comap (f := f) (p := p) (p' := Submodule.map f q),
    Submodule.comap_map_eq f q, sup_eq_left.mpr hq]

/-- Submodules `U` of `M` with `S ≤ U ≤ T`, `U ⊓ A = S` and `U ⊔ A = T` correspond to
submodules `U'` of `↥T` with `S' ≤ U'`, `U' ⊓ A' = S'` and `U' ⊔ A' = ⊤`, where
`S' = S.comap T.subtype` and `A' = A.comap T.subtype`. -/
private noncomputable def betweenEquivIic {K : Type*} [Field K] {M : Type*} [AddCommGroup M]
    [Module K M] (S A T : Submodule K M) (hSA : S ≤ A) (hAT : A ≤ T) :
    {U : Submodule K M // S ≤ U ∧ U ≤ T ∧ U ⊓ A = S ∧ U ⊔ A = T} ≃
      {U' : Submodule K ↥T // S.comap T.subtype ≤ U' ∧
        U' ⊓ A.comap T.subtype = S.comap T.subtype ∧ U' ⊔ A.comap T.subtype = ⊤} where
  toFun U := ⟨Submodule.comap T.subtype U.1, by
    refine ⟨Submodule.comap_mono U.2.1, ?_, ?_⟩
    · rw [← Submodule.comap_inf U.1 A T.subtype, U.2.2.2.1]
    · rw [← Submodule.comap_sup_of_injective (f := T.subtype) T.subtype_injective
          (by simpa only [Submodule.range_subtype] using U.2.2.1)
          (by simpa only [Submodule.range_subtype] using hAT),
        U.2.2.2.2, Submodule.comap_subtype_self]⟩
  invFun U' := ⟨Submodule.map T.subtype U'.1, by
    refine ⟨?_, Submodule.map_subtype_le T U'.1, ?_, ?_⟩
    · have hS' : S = Submodule.map T.subtype (Submodule.comap T.subtype S) := by
        rw [Submodule.map_comap_subtype, inf_of_le_right (hSA.trans hAT)]
      exact (le_of_eq hS').trans (Submodule.map_mono U'.2.1)
    · have hA' : A = Submodule.map T.subtype (Submodule.comap T.subtype A) := by
        rw [Submodule.map_comap_subtype, inf_of_le_right hAT]
      have hS' : S = Submodule.map T.subtype (Submodule.comap T.subtype S) := by
        rw [Submodule.map_comap_subtype, inf_of_le_right (hSA.trans hAT)]
      calc Submodule.map T.subtype U'.1 ⊓ A
          = Submodule.map T.subtype U'.1 ⊓
              Submodule.map T.subtype (Submodule.comap T.subtype A) :=
              congrArg (fun X => Submodule.map T.subtype U'.1 ⊓ X) hA'
        _ = Submodule.map T.subtype (U'.1 ⊓ Submodule.comap T.subtype A) := by
              rw [Submodule.map_inf (f := T.subtype) T.subtype_injective]
        _ = Submodule.map T.subtype (Submodule.comap T.subtype S) := by rw [U'.2.2.1]
        _ = S := hS'.symm
    · have hA' : A = Submodule.map T.subtype (Submodule.comap T.subtype A) := by
        rw [Submodule.map_comap_subtype, inf_of_le_right hAT]
      calc Submodule.map T.subtype U'.1 ⊔ A
          = Submodule.map T.subtype U'.1 ⊔
              Submodule.map T.subtype (Submodule.comap T.subtype A) :=
              congrArg (fun X => Submodule.map T.subtype U'.1 ⊔ X) hA'
        _ = Submodule.map T.subtype (U'.1 ⊔ Submodule.comap T.subtype A) := by
              rw [Submodule.map_sup]
        _ = Submodule.map T.subtype ⊤ := by rw [U'.2.2.2]
        _ = T := Submodule.map_subtype_top T⟩
  left_inv U := Subtype.ext (by
    show Submodule.map T.subtype (Submodule.comap T.subtype ↑U) = ↑U
    rw [Submodule.map_comap_subtype, inf_of_le_right U.2.2.1])
  right_inv U' := Subtype.ext (by
    show Submodule.comap T.subtype (Submodule.map T.subtype ↑U') = ↑U'
    exact Submodule.comap_map_eq_of_injective T.subtype_injective ↑U')

/-- Complements of `A'/S'` inside `V ⧸ S'` correspond to submodules `U'` of `V` containing
`S'` with `U' ⊓ A' = S'` and `U' ⊔ A' = ⊤`. -/
private noncomputable def quotientComplementsEquiv {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] (S' A' : Submodule K V) (h : S' ≤ A') :
    {U' : Submodule K V // S' ≤ U' ∧ U' ⊓ A' = S' ∧ U' ⊔ A' = ⊤} ≃
      {W : Submodule K (V ⧸ S') // IsCompl W (Submodule.map S'.mkQ A')} where
  toFun U' := ⟨Submodule.map S'.mkQ U'.1, by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    refine ⟨?_, ?_⟩
    · rw [← map_inf_eq_map_inf_of_ker_le S'.mkQ
        (by rw [Submodule.ker_mkQ]; exact U'.2.1)
        (by rw [Submodule.ker_mkQ]; exact h),
        U'.2.2.1, Submodule.mkQ_map_self]
    · rw [← Submodule.map_sup (p := U'.1) (p' := A') (f := S'.mkQ), U'.2.2.2, Submodule.map_top,
        LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective S')]⟩
  invFun W := by
    refine ⟨Submodule.comap S'.mkQ W.1, Submodule.le_comap_mkQ S' W.1, ?_, ?_⟩
    · have hw : Submodule.map S'.mkQ (Submodule.comap S'.mkQ W.1) = W.1 :=
        Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective S') W.1
      have hinf : Submodule.map S'.mkQ (Submodule.comap S'.mkQ W.1 ⊓ A') = ⊥ := by
        rw [map_inf_eq_map_inf_of_ker_le S'.mkQ
          (by rw [Submodule.ker_mkQ]; exact Submodule.le_comap_mkQ S' W.1)
          (by rw [Submodule.ker_mkQ]; exact h), hw]
        exact disjoint_iff.mp (isCompl_iff.mp W.2).1
      have hker : Submodule.comap S'.mkQ W.1 ⊓ A' ≤ S'.mkQ.ker :=
        (LinearMap.le_ker_iff_map (f := S'.mkQ)
          (p := Submodule.comap S'.mkQ W.1 ⊓ A')).mpr hinf
      rw [Submodule.ker_mkQ S'] at hker
      exact le_antisymm hker (le_inf (Submodule.le_comap_mkQ S' W.1) h)
    · have hw : Submodule.map S'.mkQ (Submodule.comap S'.mkQ W.1) = W.1 :=
        Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective S') W.1
      have hsup : Submodule.map S'.mkQ (Submodule.comap S'.mkQ W.1 ⊔ A') = ⊤ := by
        rw [Submodule.map_sup (p := Submodule.comap S'.mkQ W.1) (p' := A') (f := S'.mkQ), hw]
        exact codisjoint_iff.mp (isCompl_iff.mp W.2).2
      have hmap := (Submodule.map_mkQ_eq_top S' (Submodule.comap S'.mkQ W.1 ⊔ A')).mp hsup
      rwa [sup_eq_right.mpr ((Submodule.le_comap_mkQ S' W.1).trans le_sup_left)] at hmap
  left_inv U' := Subtype.ext (by
    show Submodule.comap S'.mkQ (Submodule.map S'.mkQ ↑U') = ↑U'
    rw [Submodule.comap_map_eq, sup_eq_left.mpr (by rw [Submodule.ker_mkQ]; exact U'.2.1)])
  right_inv W := Subtype.ext (by
    show Submodule.map S'.mkQ (Submodule.comap S'.mkQ ↑W) = ↑W
    exact Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective S') ↑W)

/-- The number of subspaces `U` with `S ≤ U ≤ T`, `U ⊓ A = S` and `U ⊔ A = T`
(i.e. the number of complements of `A/S` inside `T/S`) is `#K ^ ((finrank T - finrank A) * (finrank A - finrank S))`
for `S ≤ A ≤ T`.  This is `card_complements` transported along the quotient `T/S`. -/
theorem card_complements_between {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (S A T : Submodule K M) (hSA : S ≤ A) (hAT : A ≤ T) :
    Nat.card {U : Submodule K M // S ≤ U ∧ U ≤ T ∧ U ⊓ A = S ∧ U ⊔ A = T} =
      Nat.card K ^ ((Module.finrank K ↥T - Module.finrank K ↥A) *
        (Module.finrank K ↥A - Module.finrank K ↥S)) := by
  classical
  set S' : Submodule K ↥T := S.comap T.subtype with hS'def
  set A' : Submodule K ↥T := A.comap T.subtype with hA'def
  have hS'A' : S' ≤ A' := Submodule.comap_mono hSA
  have hST : S ≤ T := hSA.trans hAT
  have hcard1 : Nat.card {U : Submodule K M // S ≤ U ∧ U ≤ T ∧ U ⊓ A = S ∧ U ⊔ A = T} =
      Nat.card {U' : Submodule K ↥T // S' ≤ U' ∧ U' ⊓ A' = S' ∧ U' ⊔ A' = ⊤} :=
    Nat.card_congr (betweenEquivIic S A T hSA hAT)
  have hcard2 : Nat.card {U' : Submodule K ↥T // S' ≤ U' ∧ U' ⊓ A' = S' ∧ U' ⊔ A' = ⊤} =
      Nat.card {W : Submodule K (↥T ⧸ S') // IsCompl W (Submodule.map S'.mkQ A')} :=
    Nat.card_congr (quotientComplementsEquiv S' A' hS'A')
  have hN : Module.finrank K (↥T ⧸ S') = Module.finrank K ↥T - Module.finrank K ↥S' :=
    Submodule.finrank_quotient (R := K) (S := K) (M := ↥T) S'
  have hP : Module.finrank K (Submodule.map S'.mkQ A') =
      Module.finrank K ↥A' - Module.finrank K ↥S' :=
    finrank_map_mkQ_of_le S' A' hS'A'
  have hs : Module.finrank K ↥S' = Module.finrank K ↥S :=
    (Submodule.comapSubtypeEquivOfLe hST).finrank_eq
  have ha : Module.finrank K ↥A' = Module.finrank K ↥A :=
    (Submodule.comapSubtypeEquivOfLe hAT).finrank_eq
  have hexp : (Module.finrank K (↥T ⧸ S') - Module.finrank K (Submodule.map S'.mkQ A')) *
        Module.finrank K (Submodule.map S'.mkQ A') =
      (Module.finrank K ↥T - Module.finrank K ↥A) *
        (Module.finrank K ↥A - Module.finrank K ↥S) := by
    have hle1 : Module.finrank K ↥S ≤ Module.finrank K ↥A := Submodule.finrank_mono hSA
    have hle2 : Module.finrank K ↥A ≤ Module.finrank K ↥T := Submodule.finrank_mono hAT
    rw [hN, hP, hs, ha]
    have hfac : (Module.finrank K ↥T - Module.finrank K ↥S) -
        (Module.finrank K ↥A - Module.finrank K ↥S) =
        Module.finrank K ↥T - Module.finrank K ↥A := by omega
    rw [hfac]
  calc Nat.card {U : Submodule K M // S ≤ U ∧ U ≤ T ∧ U ⊓ A = S ∧ U ⊔ A = T}
      = Nat.card {U' : Submodule K ↥T // S' ≤ U' ∧ U' ⊓ A' = S' ∧ U' ⊔ A' = ⊤} := hcard1
    _ = Nat.card {W : Submodule K (↥T ⧸ S') // IsCompl W (Submodule.map S'.mkQ A')} := hcard2
    _ = Nat.card K ^
          ((Module.finrank K (↥T ⧸ S') - Module.finrank K (Submodule.map S'.mkQ A')) *
            Module.finrank K (Submodule.map S'.mkQ A')) :=
          card_complements_aux (K := K) (N := ↥T ⧸ S') (Submodule.map S'.mkQ A')
    _ = Nat.card K ^ ((Module.finrank K ↥T - Module.finrank K ↥A) *
          (Module.finrank K ↥A - Module.finrank K ↥S)) := by rw [hexp]

end

end Commons.LinearAlgebra.Submodule
