import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Stems.homotopyGroup_prod

-- The `haveI`s below are `Prop`-valued instance bindings (on `Subsingleton`, `Nonempty` and
-- `PathConnectedSpace`), so the instance-preference linter does not apply.
set_option linter.style.haveILetI false

namespace Work.Stems

/-- **The product of two Eilenberg–MacLane models is a model of the product group.**  For `m ≥ 1`,
if `X` is a model of `K(A,m)` (base point `pt`) and `Y` is a model of `K(B,m)` (base point `qt`),
then `X × Y` is a model of `K(A × B, m)` at `(pt, qt)`.

This is the dictionary step of the free part of `EMVan` (area STEMS' assignment): with
`A = B = ℤ` it gives `K(ℤ,k) × K(ℤ,k)` as a model of `K(ℤ²,k)`, and iterating it realises
`K(ℤ^r,k)` as the `r`-fold product of `K(ℤ,k)`, whose rational homology in the range is
`Work.Stems.fin_prod_ratH_vanishing` (and `Work.Stems.prod_acyclic_ratH_vanishing` for a rationally
acyclic factor, the finite/torsion part).

Ingredients: the product iso on homotopy groups `Work.Stems.homotopyGroup_prod`
(π_n(X × Y) ≃* π_n X × π_n Y) gives the iso on `π_m` (composed with the identity
`Multiplicative (A × B) ≃* Multiplicative A × Multiplicative B`) and, for `i ≠ m` with `i ≥ 1`, the
vanishing of `π_i`.  **The case `i = 0` needs separate work**: `homotopyGroup_prod` requires
`[Nonempty (Fin i)]`, which fails for `i = 0`, so `Subsingleton (π₀ (X × Y))` must be obtained from
the path connectedness of `X` and `Y` (e.g. through `HGProd.combine` in
`Submission/Work/Stems/homotopyGroup_prod.lean`, whose surjectivity at `Fin 0` is vacuous, or from
`HomotopyGroup.pi0EquivZerothHomotopy`).  `IsEMSpace A m hm X pt` is
`Nonempty (π_m(X,pt) ≃* Multiplicative A) ∧ ∀ i ≠ m, Subsingleton (π_i(X,pt))`. -/
theorem isEMSpace_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] {m : ℕ} (hm : 0 < m)
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (pt : X) (qt : Y)
    (hA : Work.Serre.IsEMSpace A m hm X pt) (hB : Work.Serre.IsEMSpace B m hm Y qt) :
    Work.Serre.IsEMSpace (A × B) m hm (X × Y) (pt, qt) := by
  -- `π_m` is nonempty, so the product formula for homotopy groups applies in degree `m`.
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  constructor
  · -- the isomorphism on `π_m`: `π_m(X × Y) ≃* π_m X × π_m Y ≃* Multiplicative A × Multiplicative B
    -- ≃* Multiplicative (A × B)`.
    obtain ⟨isoX⟩ := hA.1
    obtain ⟨isoY⟩ := hB.1
    obtain ⟨eprod⟩ := Work.Stems.homotopyGroup_prod (N := Fin m) pt qt
    exact ⟨eprod.trans ((isoX.prodCongr isoY).trans
      (MulEquiv.prodMultiplicative (G := A) (H := B)).symm)⟩
  · intro i hi
    by_cases h0 : i = 0
    · -- `π₀` is not a group and the product formula needs a nonempty index, so we work with the
      -- path components: `Subsingleton (π₀)` gives `Subsingleton (ZerothHomotopy)`, hence
      -- path connectedness of the two factors, hence of the product.
      subst h0
      haveI : Subsingleton (HomotopyGroup (Fin 0) X pt) := hA.2 0 (by omega)
      haveI : Subsingleton (HomotopyGroup (Fin 0) Y qt) := hB.2 0 (by omega)
      have hZx : Subsingleton (ZerothHomotopy X) :=
        Equiv.subsingleton (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := pt)).symm
      have hZy : Subsingleton (ZerothHomotopy Y) :=
        Equiv.subsingleton (HomotopyGroup.pi0EquivZerothHomotopy (X := Y) (x := qt)).symm
      haveI : PathConnectedSpace X :=
        pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk pt⟩, hZx⟩
      haveI : PathConnectedSpace Y :=
        pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk qt⟩, hZy⟩
      exact Equiv.subsingleton (HomotopyGroup.pi0EquivZerothHomotopy (X := X × Y) (x := (pt, qt)))
    · -- the remaining degrees `i ≥ 1`: the product formula for homotopy groups, where both
      -- factors vanish.
      haveI : Nonempty (Fin i) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
      obtain ⟨e⟩ := Work.Stems.homotopyGroup_prod (N := Fin i) pt qt
      haveI : Subsingleton (HomotopyGroup (Fin i) X pt) := hA.2 i hi
      haveI : Subsingleton (HomotopyGroup (Fin i) Y qt) := hB.2 i hi
      exact Equiv.subsingleton e.toEquiv

end Work.Stems
