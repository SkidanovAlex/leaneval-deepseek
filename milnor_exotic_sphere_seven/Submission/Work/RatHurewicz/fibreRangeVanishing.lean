import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.ratSerrePairComparison
import Submission.Work.Serre.strictFibre_ratH_homotopyFibre
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.Stems.homotopyFibre_evalOne_equiv_loop
import Submission.Work.Stems.isEMSpace_loop
import Submission.Work.Stems.Engine.C2Range
import Submission.Work.Stems.Engine.DualVanishing
import Submission.Work.RatHurewicz.SimplyConnectedBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The **fibre-given-range** vanishing of a spherical fibration, from the pair comparison

## The mathematics

Let `p : E → B` be a Serre fibration with **rationally acyclic** total space `E`, path-connected
base `B` and strict fibre `F = p⁻¹{b₀}` which is a **rational `S^r` through degree `g`**:

  `H_n(F;ℚ) = 0` for `0 < n < g`, `n ≠ r`,  and `H_r(F;ℚ) ≅ ℚ`.

Let `b` be the connectivity parameter of `B` (`π_i(B,b₀) = 0` for `i < b`).  Then the long exact
sequences of the pairs `(E,F)` and `(B,{b₀})` combine with the **pair comparison in the stable
range** to give

  `H_k(B;ℚ) = 0` for `1 ≤ k ≤ min g (b+f-1)`, `k ≠ r+1`,  and  `H_{r+1}(B;ℚ) ≅ ℚ`,

where `f` is the fibre parameter of the pair comparison (the range of the comparison is `b+f`).

**The key point is that the *range is given by the fibre*** (`k ≤ g`), not by the base's
connectivity: for `k ≥ 2` the suspension isomorphism `H_k(E,F) ≅ H_{k-1}(F)` (valid because `E` is
acyclic) together with the pair comparison `H_k(E,F) ≅ H_k(B,{b₀})` identifies `H_k(B;ℚ)` with
`H_{k-1}(F;ℚ)`, which vanishes as soon as `k - 1 < g`.  This is the statement
`SERRE_BLUEPRINT.md` ADDENDUM 3 (B) asks for, in its *homological* form: no cohomology, no cup
product, no Euler class.

The pair comparison used here is `Work.Serre.ratSerrePairComparison`, whose fibre hypothesis is
*homological* (`H_j(F;ℚ) = 0` for `0 < j < f`) and whose conclusion is an isomorphism below `b+f`.
It is supplied here as the `Prop` `RatPairComparison`, so that consumers can invoke the results of
this file without inheriting the proof of the pair comparison.

## Consequence (`c2evenRange_of_ratPairComparison`)

Applied to the path–loop fibration `ΩL → PL → L` over a model `L` of `K(ℤ,2j)`, whose fibre `ΩL`
is a rational `S^{2j-1}` through `4j-2`, this gives the **even step of the `C2` layer**,
`Work.Stems.Engine.C2evenRange`, *without* the Euler-class/Gysin statement
`Work.Serre.SerreE3b` that the previous route to `C2evenRange`
(`Work.Stems.Engine.c2evenRange_of_oddSphereRange`) used: the required range `m ≤ 2j-2` of the
Gysin isomorphism is inside the range `m < b = 2j` that the base's connectivity alone gives.
-/

namespace Work.RatHurewicz

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Topology

/-! ## The relative rational homology of a pair -/

/-- `H_n(X,A;ℚ)`, the `n`-th rational homology of the pair `(X,A)`. -/
abbrev relHRat (X : TopCat) (A : Set X) (n : ℕ) : ModuleCat ℚ :=
  (Work.StemsB.relChainsR ℚ X A).homology n

/-- Transport an isomorphism of modules along equalities of the two objects. -/
theorem nonempty_iso_of_eq {X Y X' Y' : ModuleCat ℚ} (hx : X = X') (hy : Y = Y')
    (e : Nonempty (X ≅ Y)) : Nonempty (X' ≅ Y') := by
  obtain ⟨e⟩ := e
  exact ⟨(eqToIso hx).symm ≪≫ e ≪≫ eqToIso hy⟩

/-! ## The one-point space -/

/-- The rational homology of a one-point space vanishes in positive degrees. -/
theorem isZero_ratH_singleton {B : Type} [TopologicalSpace B] (b₀ : B) {n : ℕ} (hn : 0 < n) :
    IsZero (Work.Serre.ratH (TopCat.of ↥({b₀} : Set B)) n) := by
  haveI : Nonempty ↥({b₀} : Set B) := ⟨⟨b₀, rfl⟩⟩
  haveI : Subsingleton ↥({b₀} : Set B) :=
    ⟨fun x y => Subtype.ext (by rw [show (x : B) = b₀ from x.2, show (y : B) = b₀ from y.2])⟩
  exact Work.Serre.RatAcyclic.isZero_ratH (Work.Serre.ratAcyclic_of_contractible ↥({b₀} : Set B)) hn

/-- `H_0` of a one-point space is `ℚ`. -/
theorem nonempty_ratH_singleton_zero {B : Type} [TopologicalSpace B] (b₀ : B) :
    Nonempty (Work.Serre.ratH (TopCat.of ↥({b₀} : Set B)) 0 ≅ ModuleCat.of ℚ ℚ) := by
  haveI : Nonempty ↥({b₀} : Set B) := ⟨⟨b₀, rfl⟩⟩
  haveI : Subsingleton ↥({b₀} : Set B) :=
    ⟨fun x y => Subtype.ext (by rw [show (x : B) = b₀ from x.2, show (y : B) = b₀ from y.2])⟩
  exact Work.Serre.ratH_zero_of_pathConnected ↥({b₀} : Set B)

/-! ## Extracting isomorphisms from the pair long exact sequence -/

/-- **The connecting map out of a relative group is an isomorphism when the total space is acyclic
on both sides.**  `H_{n+1}(X,A;ℚ) ≅ H_n(A;ℚ)` when `H_n(X;ℚ) = H_{n+1}(X;ℚ) = 0`. -/
theorem nonempty_iso_relChainsRδ_of_isZero (X : TopCat) (A : Set X) (n : ℕ)
    (h1 : IsZero (Work.Serre.ratH X (n + 1))) (h2 : IsZero (Work.Serre.ratH X n)) :
    Nonempty (relHRat X A (n + 1) ≅ Work.Serre.ratH (TopCat.of ↥A) n) := by
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

/-- **A pair with a homology-trivial subspace has `H_{n+1}(X;ℚ) ≅ H_{n+1}(X,A;ℚ)`.** -/
theorem nonempty_iso_cokernelπ_of_isZero (X : TopCat) (A : Set X) (n : ℕ)
    (h1 : IsZero (Work.Serre.ratH (TopCat.of ↥A) (n + 1)))
    (h0 : IsZero (Work.Serre.ratH (TopCat.of ↥A) n)) :
    Nonempty (Work.Serre.ratH X (n + 1) ≅ relHRat X A (n + 1)) := by
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

/-! ## The pair comparison as a `Prop` -/

/-- **The rational pair comparison in the stable range**, with the *homological* fibre hypothesis
(verbatim restatement of `Work.Serre.ratSerrePairComparison`).

For a Serre fibration `p : E → B` over a path-connected base with path-connected, rationally
`f`-acyclic fibre (`H_j(F;ℚ) = 0` for `0 < j < f`), `B` `(b-1)`-connected (`b ≥ 2`) and `E` and `B`
path connected, the map of pairs `(E, F) → (B, {b₀})` is an isomorphism on rational homology in
degrees `< b + f` (and one degree beyond if the source vanishes).

This is the *homological*-fibre form, which is what makes the fibre-given range
(`fibreRangeVanishing` below) available.  It is stated as a `Prop` so that this file's results do
not inherit the proof of the pair comparison. -/
def RatPairComparison : Prop :=
  ∀ {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (b f : ℕ)
    (hb : 2 ≤ b) (hf : 1 ≤ f) (hE : PathConnectedSpace E) (hB : PathConnectedSpace B)
    (hconn : ∀ i < b, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hfib : ∀ j : ℕ, 0 < j → j < f →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j)),
    (∀ i : ℕ, i < b + f → Nonempty
      (relHRat (TopCat.of E) (p ⁻¹' {b₀}) i ≅ relHRat (TopCat.of B) ({b₀} : Set B) i)) ∧
      (IsZero (relHRat (TopCat.of E) (p ⁻¹' {b₀}) (b + f)) →
        IsZero (relHRat (TopCat.of B) ({b₀} : Set B) (b + f)))

/-- The proved `Work.Serre.ratSerrePairComparison` inhabits the `Prop`. -/
theorem ratPairComparison_proof : RatPairComparison :=
  Work.Serre.ratSerrePairComparison

/-! ## The fibre-given-range vanishing -/

/-- **The rational homology of the base vanishes in the range given by the fibre.**  See the module
docstring: `H_k(B;ℚ) = 0` for `1 ≤ k ≤ min g (b+f-1)`, `k ≠ r+1`, and `H_{r+1}(B;ℚ) ≅ ℚ`, where
the fibre is a rational `S^r` through degree `g` and the pair comparison is available below `b+f`. -/
theorem fibreRangeVanishing {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b₀ : B) (b r f g : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (hrbf : r + 1 < b + f)
    (hBvan : ∀ j : ℕ, 0 < j → j < b → IsZero (Work.Serre.ratH (TopCat.of B) j))
    (hEvan : ∀ n : ℕ, 0 < n → IsZero (Work.Serre.ratH (TopCat.of E) n))
    (hFvan : ∀ n : ℕ, 0 < n → n < g → n ≠ r →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) n))
    (hFgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) r ≅
      ModuleCat.of ℚ ℚ))
    (hpair : ∀ i : ℕ, i < b + f → Nonempty
      (relHRat (TopCat.of E) (p ⁻¹' {b₀}) i ≅ relHRat (TopCat.of B) ({b₀} : Set B) i)) :
    (∀ k : ℕ, 1 ≤ k → k ≤ min g (b + f - 1) → k ≠ r + 1 →
      IsZero (Work.Serre.ratH (TopCat.of B) k)) ∧
      Nonempty (Work.Serre.ratH (TopCat.of B) (r + 1) ≅ ModuleCat.of ℚ ℚ) := by
  -- (1) `H_{n+1}(E,F) ≅ H_n(F;ℚ)` for `n ≥ 1` (the total space is acyclic)
  have hiso1 : ∀ n : ℕ, 1 ≤ n → Nonempty
      (relHRat (TopCat.of E) (p ⁻¹' {b₀}) (n + 1) ≅
        Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) n) := by
    intro n hn
    exact nonempty_iso_relChainsRδ_of_isZero (TopCat.of E) (p ⁻¹' {b₀}) n
      (hEvan (n + 1) (by omega)) (hEvan n hn)
  -- (2) in the `k`-indexed shape, `k ≥ 2`
  have hiso1' : ∀ k : ℕ, 2 ≤ k → Nonempty
      (relHRat (TopCat.of E) (p ⁻¹' {b₀}) k ≅
        Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) (k - 1)) := by
    intro k hk
    exact nonempty_iso_of_eq
      (congrArg (relHRat (TopCat.of E) (p ⁻¹' {b₀})) (Nat.sub_add_cancel (by omega : 1 ≤ k))) rfl
      (hiso1 (k - 1) (by omega))
  -- (3) `H_k(B;ℚ) ≅ H_k(B,{b₀};ℚ)` for `k ≥ 2`
  have hiso2 : ∀ k : ℕ, 2 ≤ k → Nonempty
      (Work.Serre.ratH (TopCat.of B) k ≅ relHRat (TopCat.of B) ({b₀} : Set B) k) := by
    intro k hk
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
    exact nonempty_iso_of_eq (congrArg (Work.Serre.ratH (TopCat.of B)) hk1)
      (congrArg (relHRat (TopCat.of B) ({b₀} : Set B)) hk1)
      (nonempty_iso_cokernelπ_of_isZero (TopCat.of B) ({b₀} : Set B) (k - 1)
        (isZero_ratH_singleton b₀ (by omega)) (isZero_ratH_singleton b₀ (by omega)))
  refine ⟨?_, ?_⟩
  · intro k hk1 hkmin hkne
    rcases eq_or_lt_of_le hk1 with h1 | h2
    · -- `k = 1`: the connectivity of `B`
      subst h1
      exact hBvan 1 (by omega) (by omega)
    · -- `k ≥ 2`: the pair comparison plus the suspension isomorphism
      obtain ⟨e1⟩ := hiso2 k (by omega)
      obtain ⟨e2⟩ := hpair k (by omega)
      obtain ⟨e3⟩ := hiso1' k (by omega)
      exact IsZero.of_iso (IsZero.of_iso (IsZero.of_iso
        (hFvan (k - 1) (by omega) (by omega) (by omega)) e3) e2.symm) e1
  · -- the generator `H_{r+1}(B;ℚ) ≅ ℚ`
    obtain ⟨e1⟩ := hiso2 (r + 1) (by omega)
    obtain ⟨e2⟩ := hpair (r + 1) hrbf
    obtain ⟨e3⟩ := hiso1' (r + 1) (by omega)
    have htr : Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) ((r + 1) - 1) =
        Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) r :=
      congrArg (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀))) (by omega : (r + 1) - 1 = r)
    exact ⟨e1 ≪≫ e2.symm ≪≫ e3 ≪≫ eqToIso htr ≪≫ hFgen.some⟩

/-! ## The reach of a model of `K(ℤ,k)` whose loop space is a rational sphere -/

/-- **The reach of a model of `K(ℤ,k)` whose loop space is a rational `S^{k-1}`.**

Let `X` be a `(k-1)`-connected space (`k ≥ 2`) whose loop space `ΩX = Path x₀ x₀` is a rational
`S^{k-1}` through degree `N` (i.e. `H_n(ΩX;ℚ) = 0` for `0 < n ≤ N`, `n ≠ k-1`, and
`H_{k-1}(ΩX;ℚ) ≅ ℚ`).  Then

  `H_j(X;ℚ) = 0` for `1 ≤ j ≤ min (N+1) (2k-2)`, `j ≤ N+1`, and `H_k(X;ℚ) ≅ ℚ` (for `k ≤ N+1`).

Proof: `fibreRangeVanishing` applied to the path–loop fibration `ΩX → PX → X`, whose total space is
contractible (hence rationally acyclic), with base connectivity `b = k` (the `(k-1)`-connectivity of
`X`) and fibre parameter `f = k-1`: the pair comparison needs the fibre acyclic below `f`, and the
*homological* fibre hypothesis cannot be taken beyond the fibre's first nonzero homology degree
`k-1`.  Hence the pair comparison is available below `b + f = 2k - 1`, and the reach of
`fibreRangeVanishing` is `min (N+1) (b+f-1) = min (N+1) (2k-2)`.  The pair comparison in the
required range is `Work.Serre.ratSerrePairComparison`, which is **proved and axiom-clean** (the
*rational*, homological-fibre form of the Serre exact sequence in the stable range).

**The cap `2k-2`** is exactly the reason why going beyond it needs the *Euler class* / Gysin
statement (`Work.Serre.SerreE3b`) rather than the pair comparison: the pair comparison treats the
fibre as acyclic (below `f`), so its range is bounded by the base's connectivity plus the fibre's
*first nonvanishing* homology degree, not by the range in which the fibre is known to be a rational
sphere. -/
theorem model_vanishing_of_loop_sphere {X : Type} [TopologicalSpace X] (x₀ : X) (k N : ℕ)
    (hk : 2 ≤ k) (hkN : k ≤ N + 1)
    (hconn : ∀ i < k, Subsingleton (HomotopyGroup (Fin i) X x₀))
    (hLoopVan : ∀ n : ℕ, 0 < n → n < N + 1 → n ≠ k - 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Path x₀ x₀)) n))
    (hLoopGen : Nonempty (Work.Serre.ratH (TopCat.of (Path x₀ x₀)) (k - 1) ≅
      ModuleCat.of ℚ ℚ)) :
    (∀ j : ℕ, 1 ≤ j → j ≤ min (N + 1) (2 * k - 2) → j ≠ k →
        IsZero (Work.Serre.ratH (TopCat.of X) j)) ∧
      Nonempty (Work.Serre.ratH (TopCat.of X) k ≅ ModuleCat.of ℚ ℚ) := by
  have h0X : Subsingleton (HomotopyGroup (Fin 0) X x₀) := hconn 0 (by omega)
  have h1X : Subsingleton (HomotopyGroup (Fin 1) X x₀) := hconn 1 (by omega)
  haveI hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ h0X
  haveI hcontrP : ContractibleSpace (Work.StemsB.PathSpace X x₀) :=
    Work.StemsB.contractible_pathSpace X x₀
  haveI hpcP : PathConnectedSpace (Work.StemsB.PathSpace X x₀) := inferInstance
  -- the connectivity vanishing of `X`
  have hLow : ∀ d : ℕ, 0 < d → d < k → IsZero (Work.Serre.ratH (TopCat.of X) d) := by
    intro d hd hd'
    have h := Work.Serre.serreE0Range X x₀ (k - 1) (fun i hi => hconn i (by omega))
    exact h d hd (by omega)
  -- the strict fibre of `evalOne` has the rational homology of `ΩX`
  have hfibVanish : ∀ n : ℕ, 0 < n → n < N + 1 → n ≠ k - 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀)) n) := by
    intro n hn hng hnne
    obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop X x₀
    have h1 : IsZero (Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne X x₀)
          (Work.RatHurewicz.pathSpaceConst X x₀))) n) :=
      Work.Stems.isZero_ratH_of_homotopyEquiv heq n (hLoopVan n hn hng hnne)
    obtain ⟨estr⟩ := Work.Serre.strictFibre_ratH_homotopyFibre (Work.StemsB.evalOne X x₀)
      (Work.StemsB.isSerreFibration_evalOne X x₀) (Work.RatHurewicz.pathSpaceConst X x₀) x₀ hpcX n
    exact IsZero.of_iso h1 estr
  have hfibGen : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀)) (k - 1) ≅
      ModuleCat.of ℚ ℚ) := by
    obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop X x₀
    have h1 := Work.Stems.isoRat_of_homotopyEquiv heq (k - 1) hLoopGen
    obtain ⟨estr⟩ := Work.Serre.strictFibre_ratH_homotopyFibre (Work.StemsB.evalOne X x₀)
      (Work.StemsB.isSerreFibration_evalOne X x₀) (Work.RatHurewicz.pathSpaceConst X x₀) x₀ hpcX
      (k - 1)
    exact ⟨estr ≪≫ h1.some⟩
  have hfib0 : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (Work.StemsB.evalOne X x₀)
      (Work.StemsB.isSerreFibration_evalOne X x₀) x₀ hpcP hpcX h1X
  -- the pair comparison (`b = k`, `f = N+1`) supplied by the *proved* rational Serre exact sequence
  have hpairF : ∀ n : ℕ, 0 < n → n < k - 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne X x₀) x₀)) n) :=
    fun n hn hnf => hfibVanish n hn (by omega) (by omega)
  obtain ⟨hpair, -⟩ := ratPairComparison_proof (Work.StemsB.evalOne X x₀)
    (Work.StemsB.isSerreFibration_evalOne X x₀) x₀ k (k - 1) (by omega) (by omega) hpcP hpcX
    (fun i hi => hconn i hi) hfib0 hpairF
  have hpa : 2 ≤ k := by omega
  have hpb : 1 ≤ k - 1 := by omega
  have hpc : (k - 1) + 1 < k + (k - 1) := by omega
  have hmain := fibreRangeVanishing (Work.StemsB.evalOne X x₀) x₀ k (k - 1) (k - 1) (N + 1)
    hpa hpb hpc
    (fun j hj hjb => hLow j hj hjb)
    (fun n hn => Work.Serre.RatAcyclic.isZero_ratH
      (Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace X x₀)) hn)
    (fun n hn hng hnne => hfibVanish n hn hng hnne)
    hfibGen (fun i hi => hpair i hi)
  have hgen : Nonempty (Work.Serre.ratH (TopCat.of X) k ≅ ModuleCat.of ℚ ℚ) :=
    nonempty_iso_of_eq (congrArg (Work.Serre.ratH (TopCat.of X))
      (by omega : (k - 1) + 1 = k)) rfl hmain.2
  refine ⟨fun j hj1 hjmin hjk => hmain.1 j hj1 (le_min ?_ ?_) ?_, hgen⟩
  · exact le_trans hjmin (min_le_left _ _)
  · omega
  · intro h
    exact hjk (by omega)

/-! ## The even step of the `C2` layer, without the Euler-class statement -/

/-- **The loop space of a `K(A,m)`-model is a `K(A,m-1)`-model**, for `m ≥ 2` (the index shape used
below: `Work.Stems.isEMSpace_loop` is stated for `k + 1`). -/
theorem isEMSpace_loop_pred {A : Type} [AddCommGroup A] {m : ℕ} (hm : 2 ≤ m) {X : Type}
    [TopologicalSpace X] (pt : X) (h : Work.Serre.IsEMSpace A m (by omega) X pt) :
    Work.Serre.IsEMSpace A (m - 1) (by omega) (Path pt pt) (Path.refl pt) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, (Nat.sub_add_cancel (by omega : 1 ≤ m)).symm⟩
  exact Work.Stems.isEMSpace_loop (k := k) (by omega) pt h

/-- **The even step of the `C2` layer** (`Work.Stems.Engine.C2evenRange`): a model `L` of
`K(ℤ,2j)` has `H_{2jk}(L;ℚ) ≅ ℚ` for `2jk < 4j-1` and `H_d(L;ℚ) = 0` for `d < 4j-1`, `2j ∤ d`.

From the *fibre-given-range* vanishing (`fibreRangeVanishing`) applied to the path–loop fibration
`ΩL → PL → L`: the fibre `ΩL` is a rational `S^{2j-1}` through degree `2(2j-1) = 4j-2`
(`Work.Stems.Engine.OddSphereRange`, the odd side of `C2`), the base `L` is `(2j-1)`-connected and
the total space `PL` is contractible.  In particular this uses **no** Euler class: the range needed
is `d ≤ 4j-2 < b + f` with `b = 2j`, `f = 2j-1`. -/
theorem c2evenRange_of_ratPairComparison (hPC : RatPairComparison)
    (hOdd : Work.Stems.Engine.OddSphereRange (fun n => 2 * n)) :
    Work.Stems.Engine.C2evenRange := by
  intro j hj L _ l₀ hL
  have h0L : Subsingleton (HomotopyGroup (Fin 0) L l₀) := hL.2 0 (by omega)
  have h1L : Subsingleton (HomotopyGroup (Fin 1) L l₀) := hL.2 1 (by omega)
  haveI hpcL : PathConnectedSpace L :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero l₀ h0L
  haveI hcontrE : ContractibleSpace (Work.StemsB.PathSpace L l₀) :=
    Work.StemsB.contractible_pathSpace L l₀
  haveI hpcE : PathConnectedSpace (Work.StemsB.PathSpace L l₀) := inferInstance
  -- the connectivity vanishing of `L`
  have hLow : ∀ d : ℕ, 0 < d → d < 2 * j → IsZero (Work.Serre.ratH (TopCat.of L) d) := by
    intro d hd hd'
    have h := Work.Serre.serreE0Range L l₀ (2 * j - 1) (fun i hi => hL.2 i (by omega))
    exact h d hd (by omega)
  -- the fibre `ΩL` is a rational `S^{2j-1}` through `4j-2`
  have hFL : Work.Serre.IsEMSpace ℤ (2 * j - 1) (by omega) (Path l₀ l₀) (Path.refl l₀) :=
    isEMSpace_loop_pred (m := 2 * j) (by omega) l₀ hL
  have hsphere : Work.Stems.Engine.RatSphereBelow (Path l₀ l₀) (2 * j - 1) (2 * (2 * j - 1)) :=
    hOdd (2 * j - 1) (by omega) ⟨j - 1, by omega⟩ (Path l₀ l₀) (Path.refl l₀) hFL
  -- transfer the fibre data to the *strict* fibre of `evalOne`
  have hfibVanish : ∀ n : ℕ, 0 < n → n < 2 * (2 * j - 1) → n ≠ 2 * j - 1 →
      IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne L l₀) l₀)) n) := by
    intro n hn hng hnne
    obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop L l₀
    have h1 : IsZero (Work.Serre.ratH
        (TopCat.of (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne L l₀)
          (Work.RatHurewicz.pathSpaceConst L l₀))) n) :=
      Work.Stems.isZero_ratH_of_homotopyEquiv heq n (hsphere.2 n hn hng hnne)
    obtain ⟨estr⟩ := Work.Serre.strictFibre_ratH_homotopyFibre (Work.StemsB.evalOne L l₀)
      (Work.StemsB.isSerreFibration_evalOne L l₀) (Work.RatHurewicz.pathSpaceConst L l₀) l₀ hpcL n
    exact IsZero.of_iso h1 estr
  have hfibGen : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.StemsB.fibre (Work.StemsB.evalOne L l₀) l₀)) (2 * j - 1) ≅
      ModuleCat.of ℚ ℚ) := by
    obtain ⟨heq⟩ := Work.Stems.homotopyFibre_evalOne_equiv_loop L l₀
    have h1 := Work.Stems.isoRat_of_homotopyEquiv heq (2 * j - 1) hsphere.1
    obtain ⟨estr⟩ := Work.Serre.strictFibre_ratH_homotopyFibre (Work.StemsB.evalOne L l₀)
      (Work.StemsB.isSerreFibration_evalOne L l₀) (Work.RatHurewicz.pathSpaceConst L l₀) l₀ hpcL
      (2 * j - 1)
    exact ⟨estr ≪≫ h1.some⟩
  -- the pair comparison at `b = 2j`, `f = 2j-1`
  have hfib0 : PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.evalOne L l₀) l₀) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration (Work.StemsB.evalOne L l₀)
      (Work.StemsB.isSerreFibration_evalOne L l₀) l₀ hpcE hpcL h1L
  obtain ⟨hpair, -⟩ := hPC (Work.StemsB.evalOne L l₀) (Work.StemsB.isSerreFibration_evalOne L l₀)
    l₀ (2 * j) (2 * j - 1) (by omega) (by omega) hpcE hpcL
    (fun i hi => hL.2 i (by omega)) hfib0
    (fun n hn hnf => hfibVanish n hn (by omega) (by omega))
  -- the main vanishing
  have hmain := fibreRangeVanishing (Work.StemsB.evalOne L l₀) l₀ (2 * j) (2 * j - 1) (2 * j - 1)
    (2 * (2 * j - 1)) (by omega) (by omega) (by omega)
    (fun k hk hkb => hLow k hk hkb)
    (fun n hn => Work.Serre.RatAcyclic.isZero_ratH
      (Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace L l₀)) hn)
    (fun n hn hng hnne => hfibVanish n hn hng hnne)
    hfibGen (fun i hi => hpair i hi)
  refine ⟨?_, ?_⟩
  · intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa using Work.Serre.ratH_zero_of_pathConnected L
    · have hk1 : k = 1 := by
        by_contra hk1
        have h2 : 2 ≤ k := by omega
        have hle : 2 * j * 2 ≤ 2 * j * k := Nat.mul_le_mul_left (2 * j) h2
        omega
      subst hk1
      refine nonempty_iso_of_eq (congrArg (Work.Serre.ratH (TopCat.of L))
        (by omega : 2 * j - 1 + 1 = 2 * j * 1)) rfl hmain.2
  · intro d hd hne
    have hd0 : d ≠ 0 := fun h => hne 0 (by rw [h]; ring)
    have hdj : d ≠ 2 * j - 1 + 1 := fun h => hne 1 (by omega)
    rcases lt_or_ge d (2 * j) with hsmall | hbig
    · exact hLow d (Nat.pos_of_ne_zero hd0) hsmall
    · refine hmain.1 d (Nat.one_le_iff_ne_zero.mpr hd0) (le_min ?_ ?_) hdj
      · rw [Nat.mul_sub_left_distrib]; omega
      · omega
/-- **The even step of the `C2` layer, with the pair comparison discharged.**  Since
`Work.Serre.ratSerrePairComparison` is *proved* (and axiom-clean), the `Prop` `RatPairComparison` is
inhabited, and `c2evenRange_of_ratPairComparison` gives `Work.Stems.Engine.C2evenRange` from the
*odd* side of `C2` alone — in particular **without** the Euler-class/Gysin statement
`Work.Serre.SerreE3b`. -/
theorem c2evenRange_of_oddSphereRange (hOdd : Work.Stems.Engine.OddSphereRange (fun n => 2 * n)) :
    Work.Stems.Engine.C2evenRange :=
  c2evenRange_of_ratPairComparison ratPairComparison_proof hOdd

end

end Work.RatHurewicz
