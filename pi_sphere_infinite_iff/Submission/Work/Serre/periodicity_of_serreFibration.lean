import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE2d
import Submission.Work.Stems.Engine.E2c
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.serreE0Range
import Submission.Work.Stems.Engine.Cohomology
import Submission.Work.StemsB.SerreExact
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.strictFibre_ratH_homotopyFibre
import Submission.Work.Serre.pathConnectedSpace_of_ratAcyclic
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Serre.ratSerrePairComparison

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Periodicity of a Serre fibration with rationally spherical fibre

`Work.Serre.periodicity_of_serreFibration`.

## The mathematics

Let `p : E → B` be a Serre fibration whose total space `E` is rationally acyclic and whose
(homotopy) fibre `F` is a rational homology sphere `S^r` (`r ≥ 1`), with `B` path-connected and
`(b-1)`-connected (`b ≥ 2`).  Then the rational homology of `B` is periodic with period `r + 1` in
the range where `B` is connected enough: `H_s(B;ℚ) ≅ H_{s+r+1}(B;ℚ)` for `1 ≤ s < b`, and
`H_0(B;ℚ) ≅ H_{r+1}(B;ℚ)`.

`Submission/Work/Serre/GYSIN_CUP_LOCAL_ISO_NOTES.md` records the analysis of this statement
(proved, no gaps, in `Submission/Work/Serre/gysinCupIsoReduction.lean`): because `H_s(B;ℚ) = 0`
for `0 < s < b` (Serre's `E0` in range form, `Work.Serre.serreE0Range`, see
`isZero_ratH_of_conn` below), and `H_0(B;ℚ) ≅ ℚ` for a path-connected `B`, the *whole* content of
the statement is the **additive** statement

> `(★)`  `H_{r+1}(B;ℚ) ≅ ℚ`  and  `H_k(B;ℚ) = 0`  for `r+1 < k ≤ b+r`,

and `(★)` is *equivalent* to the statement.

## What is proved in this file

`periodicity_of_ratPair` below is the **assembly**: it derives `(★)` — hence the statement — from

* the vanishing of `H_n(E;ℚ)` for `n > 0` (rational acyclicity of `E`);
* the rational homology of the strict fibre `F = p⁻¹{b₀}`: `H_r(F;ℚ) ≅ ℚ` and `H_n(F;ℚ) = 0` for
  `0 < n ≠ r`;
* the **rational pair comparison in the stable range** together with the vanishing of the relative
  homology of `(B,{b₀})` one degree beyond it:

  `H_i(E,F;ℚ) ≅ H_i(B,b₀;ℚ)` for `i < b+r`  and  `H_{b+r}(B,b₀;ℚ) = 0`;

* the connectivity vanishing `H_s(B;ℚ) = 0` for `0 < s < b`.

All the algebra is done here, with the long exact sequences of the pairs `(E,F)` and `(B,{b₀})`
over `ℚ` (`Work.StemsB.relChainsR ℚ`, `Work.StemsB.relChainsR_exact₁/₂/₃`).  Concretely:

* for `n ≥ 1` the pair sequence of `(E,F)` with `H_n(E) = H_{n+1}(E) = 0` gives
  `H_{n+1}(E,F;ℚ) ≅ H_n(F;ℚ)` (`isIso_relChainsRδ_of_isZero`);
* for `n ≥ 1` the pair sequence of `(B,{b₀})` with `H_n({b₀}) = H_{n+1}({b₀}) = 0` gives
  `H_{n+1}(B;ℚ) ≅ H_{n+1}(B,b₀;ℚ)` (`isIso_cokernelπH_of_isZero`, with
  `isZero_ratH_singleton` for the one-point space);
* combining, in degrees `k ≥ 2`, `H_k(B;ℚ) ≅ H_{b₀-rel}(B,b₀;ℚ) ≅ H_k(E,F;ℚ) ≅ H_{k-1}(F;ℚ)`,
  which vanishes unless `k = r+1`.

The **geometric input** (the pair comparison above) is *not* proved here: it is the rational
Serre exact sequence in the stable range, i.e. the `ℚ`-coefficient version of
`Work.Serre.SerreStableExact` / `Work.StemsB.SerreExactRange` (the cell-induction engine).  It is
supplied as the hypothesis `hpair`/`hstop` of `periodicity_of_ratPair`, and the final theorem
`periodicity_of_serreFibration` invokes it through

* `Work.Serre.ratSerrePairComparison` (`Submission/Work/Serre/ratSerrePairComparison.lean`) — the
  rational pair comparison itself;
* `Work.Serre.pathConnectedSpace_of_ratAcyclic` and
  `Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration` — the two connectivity inputs that make
  the fibre hypothesis of the pair comparison available (a rationally acyclic space is path
  connected, and a Serre fibration with path-connected total space and simply connected base has
  path-connected fibres).

`Submission/Work/Serre/_ps_assembly_check.lean` records the same assembly against local copies of
those three statements, so that it type-checks independently of them.
-/

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- **Rational homology vanishes below the connectivity radius.**  If `B` is `(b-1)`-connected
(`π_i(B,b₀) = 0` for `i < b`) with `b ≥ 1`, then `H_j(B;ℚ) = 0` for `0 < j < b`.  This is the
*proved* Serre `E0` in range form (`Work.Serre.serreE0Range`, the singular-cone construction). -/
theorem isZero_ratH_of_conn {B : Type} [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 1 ≤ b)
    (hconn : Conn B b₀ b) (j : ℕ) (hj : 0 < j) (hjb : j < b) :
    IsZero (ratH (TopCat.of B) j) := by
  have h := serreE0Range B b₀ (b - 1) (fun i hi => hconn i (by omega))
  rw [Nat.sub_add_cancel hb] at h
  exact h j hj hjb

/-! ## The rational relative homology of a pair -/

/-- `H_n(X,A;ℚ)`, the `n`-th rational homology of the pair `(X,A)`, as the homology of the
relative chain complex `C_*(X,A;ℚ) = coker(C_*(A;ℚ) → C_*(X;ℚ))`. -/
abbrev relHRat (X : TopCat) (A : Set X) (n : ℕ) : ModuleCat ℚ :=
  (Work.StemsB.relChainsR ℚ X A).homology n

/-- The connecting map `H_{n+1}(X,A;ℚ) ⟶ H_n(A;ℚ)` of the long exact sequence of the pair. -/
abbrev relHRatδ (X : TopCat) (A : Set X) (n : ℕ) :
    relHRat X A (n + 1) ⟶ ratH (TopCat.of ↥A) n :=
  Work.StemsB.relChainsRδ ℚ X A n

/-- Transport an isomorphism of modules along equalities of the two objects. -/
theorem nonempty_iso_of_eq {X Y X' Y' : ModuleCat ℚ} (hx : X = X') (hy : Y = Y')
    (e : Nonempty (X ≅ Y)) : Nonempty (X' ≅ Y') := by
  obtain ⟨e⟩ := e
  exact ⟨(eqToIso hx).symm ≪≫ e ≪≫ eqToIso hy⟩

/-! ## The one-point space -/

/-- The rational homology of a one-point space vanishes in positive degrees. -/
theorem isZero_ratH_singleton {B : Type} [TopologicalSpace B] (b₀ : B) {n : ℕ} (hn : 0 < n) :
    IsZero (ratH (TopCat.of ↥({b₀} : Set B)) n) := by
  haveI : Nonempty ↥({b₀} : Set B) := ⟨⟨b₀, rfl⟩⟩
  haveI : Subsingleton ↥({b₀} : Set B) :=
    ⟨fun x y => Subtype.ext (by rw [show (x : B) = b₀ from x.2, show (y : B) = b₀ from y.2])⟩
  exact RatAcyclic.isZero_ratH (ratAcyclic_of_contractible ↥({b₀} : Set B)) hn

/-- `H_0` of a one-point space is `ℚ`. -/
theorem nonempty_ratH_singleton_zero {B : Type} [TopologicalSpace B] (b₀ : B) :
    Nonempty (ratH (TopCat.of ↥({b₀} : Set B)) 0 ≅ ModuleCat.of ℚ ℚ) := by
  haveI : Nonempty ↥({b₀} : Set B) := ⟨⟨b₀, rfl⟩⟩
  haveI : Subsingleton ↥({b₀} : Set B) :=
    ⟨fun x y => Subtype.ext (by rw [show (x : B) = b₀ from x.2, show (y : B) = b₀ from y.2])⟩
  exact ratH_zero_of_pathConnected ↥({b₀} : Set B)

/-! ## Extracting isomorphisms from the pair long exact sequence -/

/-- **The connecting map out of a relative group is an isomorphism when the total space is
acyclic on both sides.**

If `H_n(X;ℚ) = H_{n+1}(X;ℚ) = 0`, then the exact sequence
`H_{n+1}(X) → H_{n+1}(X,A) --δ--> H_n(A) → H_n(X)` shows that `δ` is both mono and epi, hence an
isomorphism: `H_{n+1}(X,A;ℚ) ≅ H_n(A;ℚ)`. -/
theorem nonempty_iso_relChainsRδ_of_isZero (X : TopCat) (A : Set X) (n : ℕ)
    (h1 : IsZero (ratH X (n + 1))) (h2 : IsZero (ratH X n)) :
    Nonempty (relHRat X A (n + 1) ≅ ratH (TopCat.of ↥A) n) := by
  have hmono : Mono (Work.StemsB.relChainsRδ ℚ X A n) := by
    have hS := Work.StemsB.relChainsR_exact₃ ℚ X A n
    rw [hS.mono_g_iff]
    exact IsZero.eq_of_src h1 _ _
  have hepi : Epi (Work.StemsB.relChainsRδ ℚ X A n) := by
    have hS := Work.StemsB.relChainsR_exact₁ ℚ X A n
    rw [hS.epi_f_iff]
    exact IsZero.eq_of_tgt h2 _ _
  haveI : IsIso (Work.StemsB.relChainsRδ ℚ X A n) := isIso_of_mono_of_epi _
  exact ⟨asIso (Work.StemsB.relChainsRδ ℚ X A n)⟩

/-- **A pair with a homology-trivial subspace has `H_{n+1}(X;ℚ) ≅ H_{n+1}(X,A;ℚ)`.**

If `H_n(A;ℚ) = H_{n+1}(A;ℚ) = 0`, then in the exact sequence
`H_{n+1}(A) → H_{n+1}(X) → H_{n+1}(X,A) --δ--> H_n(A) → H_n(X)` the map
`H_{n+1}(X) → H_{n+1}(X,A)` is mono (from the vanishing of `H_{n+1}(A)`) and epi (from the
vanishing of `H_n(A)`), hence an isomorphism. -/
theorem nonempty_iso_cokernelπ_of_isZero (X : TopCat) (A : Set X) (n : ℕ)
    (h1 : IsZero (ratH (TopCat.of ↥A) (n + 1))) (h0 : IsZero (ratH (TopCat.of ↥A) n)) :
    Nonempty (ratH X (n + 1) ≅ relHRat X A (n + 1)) := by
  have hmono : Mono (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)) (n + 1)) := by
    have hS := Work.StemsB.relChainsR_exact₂ ℚ X A (n + 1)
    rw [hS.mono_g_iff]
    exact IsZero.eq_of_src h1 _ _
  have hepi : Epi (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)) (n + 1)) := by
    have hS := Work.StemsB.relChainsR_exact₃ ℚ X A n
    rw [hS.epi_f_iff]
    exact IsZero.eq_of_tgt h0 _ _
  haveI : IsIso (HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)) (n + 1)) := isIso_of_mono_of_epi _
  exact ⟨asIso (HomologicalComplex.homologyMap
    (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)) (n + 1))⟩

/-- A surjection whose source vanishes has vanishing target. -/
theorem isZero_of_isZero_of_surjective {X Y : ModuleCat ℚ} (hX : IsZero X) (f : X ⟶ Y)
    (hf : Function.Surjective f.hom) : IsZero Y := by
  have hzero : f = 0 := IsZero.eq_of_src hX f 0
  have hzero' : f.hom = 0 := by rw [hzero]; rfl
  haveI hsub : Subsingleton (↥Y) :=
    ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      rw [show f.hom x = 0 from by simp [hzero'],
        show f.hom y = 0 from by simp [hzero']]⟩
  exact ModuleCat.isZero_of_subsingleton Y

/-! ## The assembly -/

/-- **The rational periodicity of the base of a Serre fibration with rationally acyclic total
space and rationally spherical fibre**, modulo the geometric input.

This is the algebraic core of `Work.Serre.periodicity_of_serreFibration`: from the rational
homology of `E` and of the strict fibre `F = p⁻¹{b₀}`, the connectivity of `B`, and the **rational
pair comparison in the stable range** (`hpair`, `hstop`), it derives the periodicity. -/
theorem periodicity_of_ratPair {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b₀ : B) (hB : PathConnectedSpace B)
    (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r)
    (hBvan : ∀ j : ℕ, 0 < j → j < b → IsZero (ratH (TopCat.of B) j))
    (hEvan : ∀ n : ℕ, 0 < n → IsZero (ratH (TopCat.of E) n))
    (hFvan : ∀ n : ℕ, 0 < n → n ≠ r →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre p b₀)) n))
    (hFgen : Nonempty (ratH (TopCat.of (Work.StemsB.fibre p b₀)) r ≅ ModuleCat.of ℚ ℚ))
    (hpair : ∀ i : ℕ, i < b + r →
      Nonempty (relHRat (TopCat.of E) (p ⁻¹' {b₀}) i ≅
        relHRat (TopCat.of B) ({b₀} : Set B) i))
    (hstop : IsZero (relHRat (TopCat.of E) (p ⁻¹' {b₀}) (b + r)) →
      IsZero (relHRat (TopCat.of B) ({b₀} : Set B) (b + r))) :
    (∀ s : ℕ, 1 ≤ s → s < b →
      Nonempty (ratH (TopCat.of B) s ≅ ratH (TopCat.of B) (s + r + 1))) ∧
      Nonempty (ratH (TopCat.of B) 0 ≅ ratH (TopCat.of B) (r + 1)) := by
  -- the fibre, as a subset of `E`
  set F : Set E := p ⁻¹' {b₀} with hF
  -- (1) `H_{n+1}(E,F) ≅ H_n(F;ℚ)` for `n ≥ 1`
  have hiso1 : ∀ n : ℕ, 1 ≤ n →
      Nonempty (relHRat (TopCat.of E) F (n + 1) ≅
        ratH (TopCat.of (Work.StemsB.fibre p b₀)) n) := by
    intro n hn
    exact nonempty_iso_relChainsRδ_of_isZero (TopCat.of E) F n
      (hEvan (n + 1) (by omega)) (hEvan n hn)
  -- (2) `H_{k}(E,F) ≅ H_{k-1}(F;ℚ)` for `k ≥ 2`, in the `k`-indexed shape
  have hiso1' : ∀ k : ℕ, 2 ≤ k →
      Nonempty (relHRat (TopCat.of E) F k ≅
        ratH (TopCat.of (Work.StemsB.fibre p b₀)) (k - 1)) := by
    intro k hk
    exact nonempty_iso_of_eq
      (congrArg (relHRat (TopCat.of E) F) (Nat.sub_add_cancel (by omega : 1 ≤ k))) rfl
      (hiso1 (k - 1) (by omega))
  -- (3) `H_k(B;ℚ) ≅ H_k(B,{b₀};ℚ)` for `k ≥ 2`
  have hiso2 : ∀ k : ℕ, 2 ≤ k →
      Nonempty (ratH (TopCat.of B) k ≅ relHRat (TopCat.of B) ({b₀} : Set B) k) := by
    intro k hk
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
    exact nonempty_iso_of_eq (congrArg (ratH (TopCat.of B)) hk1)
      (congrArg (relHRat (TopCat.of B) ({b₀} : Set B)) hk1)
      (nonempty_iso_cokernelπ_of_isZero (TopCat.of B) ({b₀} : Set B) (k - 1)
        (isZero_ratH_singleton b₀ (by omega)) (isZero_ratH_singleton b₀ (by omega)))
  -- (4) `H_k(B;ℚ) = 0` for `r+2 ≤ k ≤ b+r`
  have hzero : ∀ k : ℕ, r + 2 ≤ k → k ≤ b + r → IsZero (ratH (TopCat.of B) k) := by
    intro k hk1 hk2
    obtain ⟨e1⟩ := hiso2 k (by omega)
    rcases lt_or_eq_of_le hk2 with hlt | heq
    · obtain ⟨e2⟩ := hpair k hlt
      obtain ⟨e3⟩ := hiso1' k (by omega)
      exact IsZero.of_iso (IsZero.of_iso
        (IsZero.of_iso (hFvan (k - 1) (by omega) (by omega)) e3) e2.symm) e1
    · subst heq
      have hR : IsZero (relHRat (TopCat.of E) F (b + r)) := by
        refine IsZero.of_iso (hFvan (b + r - 1) (by omega) (by omega)) ?_
        exact (hiso1' (b + r) (by omega)).some
      exact IsZero.of_iso (hstop hR) e1
  -- (5) `H_{r+1}(B;ℚ) ≅ ℚ`
  have hgenB : Nonempty (ratH (TopCat.of B) (r + 1) ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨e1⟩ := hiso2 (r + 1) (by omega)
    obtain ⟨e2⟩ := hpair (r + 1) (by omega)
    obtain ⟨e3⟩ := hiso1' (r + 1) (by omega)
    have htr : ratH (TopCat.of (Work.StemsB.fibre p b₀)) ((r + 1) - 1) =
        ratH (TopCat.of (Work.StemsB.fibre p b₀)) r :=
      congrArg (ratH (TopCat.of (Work.StemsB.fibre p b₀))) (by omega : (r + 1) - 1 = r)
    exact ⟨e1 ≪≫ e2.symm ≪≫ e3 ≪≫ eqToIso htr ≪≫ hFgen.some⟩
  haveI := hB
  refine ⟨fun s hs hsb => ?_, ?_⟩
  · exact ⟨(hBvan s hs hsb).iso (hzero (s + r + 1) (by omega) (by omega))⟩
  · obtain ⟨e0⟩ := ratH_zero_of_pathConnected B
    exact ⟨e0 ≪≫ hgenB.some.symm⟩

/-! ## The theorem, from the geometric input -/

/-- **The rational periodicity of the base** (Serre's Gysin/periodicity theorem for a fibration with
rationally acyclic total space and rationally `S^r` fibre).

The proof invokes the **rational pair comparison in the stable range** — the `ℚ`-coefficient Serre
exact sequence, `hpair`/`hstop` in `periodicity_of_ratPair` above — at the single place marked
`-- GEOMETRIC INPUT` below. -/
theorem periodicity_of_serreFibration {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (b₀ : B)
    (hB : PathConnectedSpace B) (hE : Work.Serre.RatAcyclic E)
    (hsc : Subsingleton (HomotopyGroup (Fin 1) B b₀))
    (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (hconn : Work.Serre.Conn B b₀ b)
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) r ≅
      ModuleCat.of ℚ ℚ)) :
    (∀ s : ℕ, 1 ≤ s → s < b → Nonempty (Work.Serre.ratH (TopCat.of B) s ≅ Work.Serre.ratH (TopCat.of B) (s + r + 1))) ∧
      Nonempty (Work.Serre.ratH (TopCat.of B) 0 ≅ Work.Serre.ratH (TopCat.of B) (r + 1)) := by
  -- the strict fibre over `b₀` has the same rational homology as the homotopy fibre over `e₀`
  have hbridge : ∀ j : ℕ, Nonempty (ratH (TopCat.of (Work.StemsB.fibre p b₀)) j ≅
      ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) j) :=
    fun j => strictFibre_ratH_homotopyFibre p hp e₀ b₀ hB j
  -- `E` is path connected (a rationally acyclic space has `H_0 = ℚ`, hence one path component)
  have hEpc : PathConnectedSpace E := pathConnectedSpace_of_ratAcyclic hE
  -- ... and then so is the fibre over `b₀`, because `π₁(B,b₀)` is trivial
  have hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀) :=
    pathConnectedSpace_fibre_of_isSerreFibration p hp b₀ hEpc hB hsc
  -- GEOMETRIC INPUT: the rational pair comparison in the stable range, i.e. the `ℚ`-coefficient
  -- Serre exact sequence in the stable range, together with its one-degree-beyond consequence.
  have hgeo := ratSerrePairComparison p hp b₀ b r hb hr hEpc hB
    (fun i hi => hconn i hi) hfib0
    (fun j hj hjr => IsZero.of_iso (hvan j hj (by omega)) (hbridge j).some)
  exact periodicity_of_ratPair p b₀ hB b r hb hr
    (fun j hj hjb => isZero_ratH_of_conn b₀ b (by omega) hconn j hj hjb)
    (fun n hn => hE.isZero_ratH hn)
    (fun n hn hnr => IsZero.of_iso (hvan n hn hnr) (hbridge n).some)
    ⟨(hbridge r).some ≪≫ hgen.some⟩
    hgeo.1 hgeo.2

end

end Work.Serre
