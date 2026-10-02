import Mathlib
import Submission.Work.Stems.product_ratH_vanishing
import Submission.Work.Serre.Basic
import Submission.Work.Stems.homotopyGroup_prod
import Submission.Work.Stems.subsingleton_of_contractible
import Submission.Work.RatHurewicz.ConnectivityBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Stems

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

noncomputable section

/-! ## Auxiliary tools

The iteration of the product step `Work.Stems.product_ratH_vanishing` over the factors of
`Fin r → Z` needs three small tools, proved here:

* `homeoFinSucc` — the homeomorphism `(Fin (r+1) → Z) ≃ₜ (Fin r → Z) × Z` (split off the last
  coordinate);
* `conn_prod` — a product of `(k-1)`-connected spaces is `(k-1)`-connected (in the cube-based sense
  `Work.Serre.Conn`, `π₀` included);
* `conn_fin_prod` — consequence: `Fin r → Z` is `(k-1)`-connected when `Z` is (induction on `r`).
-/

/-- **Split off the last coordinate**: `(Fin (r+1) → Z) ≃ₜ (Fin r → Z) × Z`, by
`f ↦ (f ∘ castSucc, f (last r))` with inverse `Fin.snoc`. -/
def homeoFinSucc (Z : Type) [TopologicalSpace Z] (r : ℕ) :
    (Fin (r + 1) → Z) ≃ₜ ((Fin r → Z) × Z) where
  toFun f := (fun i => f i.castSucc, f (Fin.last r))
  invFun p := Fin.snoc (α := fun _ => Z) p.1 p.2
  left_inv f := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i; simp
    · simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_pi (fun i => continuous_apply i.castSucc)) ?_
    exact continuous_apply (Fin.last r)
  continuous_invFun := by
    apply continuous_pi
    intro i
    induction i using Fin.lastCases with
    | last => simpa using continuous_snd
    | cast j =>
        convert (continuous_apply j).comp continuous_fst using 1
        funext p
        simp

/-- **A product of `(k-1)`-connected spaces is `(k-1)`-connected** in the cube-based sense
(`Work.Serre.Conn`, so `π₀` included).

For `i ≥ 1` this is the multiplicativity of homotopy groups
(`Work.Stems.homotopyGroup_prod`); the `π₀` case is path connectedness of a product of path
connected factors (cube-based `π₀`-triviality implies `PathConnectedSpace`,
`Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero`). -/
theorem conn_prod {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (x : X) (y : Y)
    (k : ℕ) (hX : Work.Serre.Conn X x k) (hY : Work.Serre.Conn Y y k) :
    Work.Serre.Conn (X × Y) (x, y) k := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    haveI : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x (hX 0 hi)
    haveI : PathConnectedSpace Y :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y (hY 0 hi)
    haveI : PathConnectedSpace (X × Y) := inferInstance
    haveI : Subsingleton (ZerothHomotopy (X × Y)) := inferInstance
    refine ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := X × Y) (x := (x, y))).injective
      (Subsingleton.elim _ _)⟩
  · haveI : Nonempty (Fin i) := ⟨⟨0, hpos⟩⟩
    haveI hXs : Subsingleton (HomotopyGroup (Fin i) X x) := hX i hi
    haveI hYs : Subsingleton (HomotopyGroup (Fin i) Y y) := hY i hi
    obtain ⟨e⟩ := homotopyGroup_prod (N := Fin i) x y
    refine ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-- **`Fin r → Z` is `(k-1)`-connected when `Z` is**, by induction on `r` (the empty product
`Fin 0 → Z` being a one-point space). -/
theorem conn_fin_prod (k : ℕ) (r : ℕ) {Z : Type} [TopologicalSpace Z] (z₀ : Z)
    (hZc : Work.Serre.Conn Z z₀ k) :
    Work.Serre.Conn (Fin r → Z) (fun _ => z₀) k := by
  induction r with
  | zero =>
    intro i _
    haveI : Nonempty (Fin 0 → Z) := ⟨fun i => i.elim0⟩
    haveI : Subsingleton (Fin 0 → Z) := ⟨fun f g => funext fun i => i.elim0⟩
    exact subsingleton_of_contractible (fun _ => z₀)
  | succ r ih =>
    have h1 : Work.Serre.Conn ((Fin r → Z) × Z) ((fun _ => z₀), z₀) k :=
      conn_prod (fun _ => z₀) z₀ k ih hZc
    intro i hi
    exact subsingleton_homotopyGroup_fin_of_homeomorph (homeoFinSucc Z r) rfl i (h1 i hi)

/-- **The `ℤ^r` (free) case of `EMVan`**, by iterating the product step
`Work.Stems.product_ratH_vanishing`.

Let `k ≥ 2` and let `Z` be `(k-1)`-connected with vanishing rational homology in the range
`k < j ≤ 2k-1`.  Then the `r`-fold product `Fin r → Z` (the empty product for `r = 0`, i.e.
`PUnit`) has the same vanishing property.

With `Z = K(ℤ,k)` this is `H̃_j((K(ℤ,k))^r;ℚ) = 0` for `k < j ≤ 2k-1`, the free part of the
Eilenberg–MacLane input `EMVan(k)` (the finite part is `Work.Serre.RangeEMVanAll`, SERRE's).

Proof: induction on `r`, using the homeomorphism `(Fin (r+1) → Z) ≅ (Fin r → Z) × Z` (splitting off
the last coordinate, `Fin.snocEquiv`/`Fin.cons`), the fact that a product of `(k-1)`-connected
spaces is `(k-1)`-connected (joint induction, products of homotopy groups,
`Work.Stems.homotopyGroup_prod`), and the product step.  Everything is purely about spaces; no
`EMSpace` structure and no C2 statement enters here. -/
theorem fin_prod_ratH_vanishing (k : ℕ) (hk : 2 ≤ k) (r : ℕ) {Z : Type} [TopologicalSpace Z]
    (z₀ : Z) (hZc : Work.Serre.Conn Z z₀ k)
    (hZ : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Z) j))
    (hSerre : Work.Serre.SerreExactRangeCorrected) :
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Fin r → Z)) j) := by
  induction r with
  | zero =>
    intro j hj1 _
    haveI : Nonempty (Fin 0 → Z) := ⟨fun i => i.elim0⟩
    haveI : Subsingleton (Fin 0 → Z) := ⟨fun f g => funext fun i => i.elim0⟩
    exact (Work.Serre.ratAcyclic_of_contractible (Fin 0 → Z)).isZero_ratH (by omega)
  | succ r ih =>
    intro j hj1 hj2
    refine isZero_ratH_of_homeomorph (homeoFinSucc Z r) j ?_
    exact product_ratH_vanishing k hk (fun _ => z₀) z₀ (conn_fin_prod k r z₀ hZc) hZc
      ih hZ hSerre j hj1 hj2

end

end Work.Stems
