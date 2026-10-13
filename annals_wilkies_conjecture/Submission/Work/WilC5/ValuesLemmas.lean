/-
  WilC5 — the basic API of the standard real valuation, as standalone lemmas (the form in which
  the extension lemmas 4.2–4.4 consume it).

  (`Work.WilC5.ValuesAPI` in `ValuesAPI.lean` bundles the same facts into one conjunction; this
  module exposes them one by one, under the names promised in `Values.lean`.)
-/
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValuesAPI

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG

section Lemmas

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The frozen `IsUnitVal` is exactly `Un(K)`: the elements of the same value as `1`. -/
theorem IsUnitVal_iff_SameArch (x : K) : IsUnitVal x ↔ SameArch x 1 :=
  (@ValuesAPI K _ _ _).1 x

/-- Same value is an equivalence relation on `K` (trivial at `0`: only `0` has the value of `0`). -/
theorem SameArch_equiv : Equivalence (fun x y : K => SameArch x y) := by
  obtain ⟨-, hrefl, hsymm, htrans, -, -, -⟩ := @ValuesAPI K _ _ _
  exact ⟨hrefl, fun h => hsymm _ _ h, fun h₁ h₂ => htrans _ _ _ h₁ h₂⟩

/-- The value-group order `VLe` is reflexive. -/
theorem VLe_refl (x : K) : VLe x x :=
  (@ValuesAPI K _ _ _).2.2.2.2.1 x

/-- The value-group order `VLe` is transitive. -/
theorem VLe_trans {x y z : K} (h₁ : VLe x y) (h₂ : VLe y z) : VLe x z := by
  obtain ⟨-, -, -, -, -, htrans, -⟩ := @ValuesAPI K _ _ _
  exact htrans x y z h₁ h₂

/-- `VLe` as a preorder on `K` (its strict part is `v x < v y`).  The value group itself — the
quotient by `SameArch`, made into an ordered abelian group by the multiplication of `K^×` — is the
next layer. -/
@[reducible] def VLePreorder : Preorder K where
  le := VLe
  lt := fun x y => VLe x y ∧ ¬ VLe y x
  le_refl := VLe_refl
  le_trans := fun _ _ _ => VLe_trans
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

/-- Same value is the equivalence relation associated with the preorder `VLe`. -/
theorem SameArch_iff_VLe (x y : K) : SameArch x y ↔ VLe x y ∧ VLe y x :=
  (@ValuesAPI K _ _ _).2.2.2.2.2.2 x y

end Lemmas

end Work.WilC5
