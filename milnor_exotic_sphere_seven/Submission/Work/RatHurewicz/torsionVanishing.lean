import Submission.Work.RatHurewicz.serreAuxClone
import Submission.Work.Serre.subsingleton_pi0_homotopyFibre
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.serreRangeEMVanOne
import Submission.Work.Serre.RangeOne.colimModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The torsion-homotopy rational vanishing theorem, from the two Serre contracts

`Work.RatHurewicz.exists_killTower` is equivalent (given `Work.Serre.serreE0Range` and the first
conjunct) to Serre's mod-torsion Hurewicz theorem in the torsion case:

  `X` simply connected, `π_i(X)` a torsion group for `2 ≤ i ≤ M`  ⟹  `H_i(X;ℚ) = 0` for `1 ≤ i ≤ M`.

This file proves that statement from the two *contracts* of the SERRE chapter
(`Submission/Work/Drive/SERRE_BLUEPRINT.md`):

* `Work.Serre.SerreE3a` — the mapping theorem (blueprint `E3(a)`), and
* `Work.Serre.RangeEMVanAll` — the range form of the acyclicity of the truncated models of
  `K(A,·)` for torsion `A` (`C3` in range form; it is derived in
  `Submission/Work/Serre/serreRangeEMVanAll.lean` from `SerreE3a` and `RangeEMVanOne`).

## The argument (the mirror image of `serreS1OfRangeEMVan.lean`)

We prove, by induction on `M - s`, the statement

  `Y` `(s-1)`-connected, `π_i(Y)` torsion for `s ≤ i ≤ M`  ⟹  `H_i(Y;ℚ) = 0` for `s ≤ i ≤ M`.

Step: let `P` be the `s`-truncation of `Y` (`serrePostnikovTower`, `π_i(P) = π_i(Y)` for `i ≤ s`
and `π_i(P) = 0` for `s < i ≤ N'`), and let `Z := hofib(Y → P)` be the `s`-connected cover
(`serreConnectedCover`).  The *double* fibre `F := hofib(Z → Y)` — the homotopy fibre of the
projection `Fst : Z → Y` — has all its homotopy groups concentrated in degree `s-1`, where
`π_{s-1}(F) ≅ π_s(Y)` is torsion (long exact sequence of the pair, `Work.RatHurewicz.serreAux_relPi_torsion_of_torsion`).
Hence `RangeEMVanAll` makes `F` rationally acyclic in a range, and `E3a` makes the cover map
`Fst : Z → Y` a rational homology isomorphism up to `M+1`.  So

* `H_s(Y;ℚ) ≅ H_s(Z;ℚ) = 0` (`E0`, `Z` being `s`-connected),
* for `s+1 ≤ i ≤ M`, `H_i(Y;ℚ) ≅ H_i(Z;ℚ)`, and the induction hypothesis applies to `Z`
  (`s`-connected, with `π_i(Z) ≅ π_i(Y)` torsion for `i ≥ s+1`).

The base case of the induction is the case `s = M`, which the step handles directly because `Z`
is `s`-connected.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology

namespace Work.RatHurewicz

/-- **`RangeEMVanOne` from `SerreC3` alone.**  The comparison of a range model of `K(A,1)` with a
genuine one is `Work.Serre.RangeOne.colimModel` (proved: the colimit of the truncation tower of the
range model), so the only remaining input of the range form of C3 in degree one is the genuine
statement `Work.Serre.SerreC3`.  In particular the model-existence contract `SerreC0` is *not*
needed here. -/
theorem rangeEMVanOne_of_C3 (hC3 : Work.Serre.SerreC3) : Work.Serre.RangeEMVanOne :=
  Work.Serre.rangeEMVanOne_of_comparison hC3
    (fun N W _ w₀ h0 hcomm htors hvan =>
      Work.Serre.RangeOne.colimModel N W w₀ h0 hcomm htors hvan)

/-- **`RangeEMVanAll` from the two SERRE contracts `SerreE3a` and `SerreC3`.** -/
theorem rangeEMVanAll_of_C3 (hE3a : Work.Serre.SerreE3a) (hC3 : Work.Serre.SerreC3) :
    Work.Serre.RangeEMVanAll :=
  Work.Serre.serreRangeEMVanAll hE3a (rangeEMVanOne_of_C3 hC3)

noncomputable section

/-- Torsion statements about `π_a` are transported between equal indices. -/
theorem piTorsionRaw_of_index_eq {X : Type} [TopologicalSpace X] (x : X) {a b : ℕ} (h : a = b)
    [Nonempty (Fin a)] [Nonempty (Fin b)]
    (hm : ∀ α : HomotopyGroup (Fin a) X x, ∃ K : ℕ, 0 < K ∧ α ^ K = 1) :
    ∀ α : HomotopyGroup (Fin b) X x, ∃ K : ℕ, 0 < K ∧ α ^ K = 1 := by
  subst h
  exact hm

/-- **The cover step of the descent** (for `3 ≤ s`).  From `Y` `(s-1)`-connected with torsion
homotopy groups in degrees `s, …, M`, produce the `s`-connected cover `Z` of `Y` (through the
`s`-truncation), which has the same torsion homotopy groups in degrees `s+1, …, M`, whose rational
vanishing in those degrees transfers back to `Y`, and with `H_s(Y;ℚ) = 0`. -/
theorem ratVanishing_step (hE3a : Work.Serre.SerreE3a) (h : Work.Serre.RangeEMVanAll)
    {s M : ℕ} (hs : 3 ≤ s) (hsM : s ≤ M) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (hconn : ∀ i : ℕ, i < s → Subsingleton (HomotopyGroup (Fin i) Y y₀))
    (htors : ∀ m : ℕ, s ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Y y₀ m) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (z₀ : Z),
      (∀ i : ℕ, i ≤ s → Subsingleton (HomotopyGroup (Fin i) Z z₀)) ∧
      (∀ m : ℕ, s + 1 ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Z z₀ m) ∧
      (∀ i : ℕ, s + 1 ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of Z) i) →
          IsZero (Work.Serre.ratH (TopCat.of Y) i)) ∧
      IsZero (Work.Serre.ratH (TopCat.of Y) s) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 3 := ⟨s - 3, by omega⟩
  -- the truncation and the cover
  set N' : ℕ := M + 2 * (k + 3) + 4 with hN'def
  obtain ⟨P, tP, g, hg1, hg2⟩ := Work.Serre.serrePostnikovTower (k + 3) N' Y y₀ (by omega)
  letI := tP
  let Z : Type := Work.RatHurewicz.homotopyFibre g y₀
  let z₀ : Z := Work.RatHurewicz.homotopyFibreBasepoint g y₀
  let Fst : C(Z, Y) := Work.RatHurewicz.homotopyFibreFst g y₀
  obtain ⟨hcov1, hcov2⟩ :=
    Work.Serre.serreConnectedCover (k + 3) N' (by omega) (by omega) Y y₀ P g hg1 hg2
  let F : Type := Work.RatHurewicz.homotopyFibre Fst z₀
  let f₀ : F := Work.RatHurewicz.homotopyFibreBasepoint Fst z₀
  -- the homotopy groups of the double fibre
  have hF_low : ∀ j : ℕ, 1 ≤ j → j ≤ k + 1 → Subsingleton (HomotopyGroup (Fin j) F f₀) := by
    intro j hj1 hjk
    by_cases hj : j = 1
    · subst hj
      exact Work.RatHurewicz.serreAux_pi_one_homotopyFibre_subsingleton Fst z₀
        (hcov1 1 (by omega)) (hconn 2 (by omega))
    · have hZ : Subsingleton (HomotopyGroup (Fin ((j - 2) + 2)) Z z₀) :=
        Work.RatHurewicz.serreAux_subsingleton_homotopyGroup_of_index_eq (x := z₀) (a := j)
          (b := (j - 2) + 2) (by omega) (hcov1 j (by omega))
      have hY : Subsingleton (HomotopyGroup (Fin (((j - 2) + 2) + 1)) Y y₀) :=
        Work.RatHurewicz.serreAux_subsingleton_homotopyGroup_of_index_eq (x := y₀) (a := j + 1)
          (b := ((j - 2) + 2) + 1) (by omega) (hconn (j + 1) (by omega))
      have hres : Subsingleton (Work.RatHurewicz.RelHomotopyGroup Fst z₀ ((j - 2) + 2)) :=
        Work.RatHurewicz.serreAux_relPi_subsingleton_of_subsingleton Fst z₀ (j - 2) hZ hY
      exact Work.RatHurewicz.serreAux_subsingleton_homotopyGroup_of_index_eq (x := f₀) (a := (j - 2) + 2)
        (b := j) (by omega) hres
  have hF_high : ∀ j : ℕ, k + 3 ≤ j → j + 2 ≤ N' → Subsingleton (HomotopyGroup (Fin j) F f₀) := by
    intro j hj hjN
    have hinj : Function.Injective (Work.StemsB.πmap Fst ((j - 2) + 1) z₀) := by
      by_cases hj' : j = k + 3
      · have hZ := Work.RatHurewicz.serreAux_subsingleton_homotopyGroup_of_index_eq (x := z₀)
          (a := k + 3) (b := ((j - 2) + 1) + 1) (by omega) (hcov1 (k + 3) le_rfl)
        haveI := hZ
        exact fun a b _ => Subsingleton.elim a b
      · exact (by omega : j - 1 = (j - 2) + 1) ▸ (hcov2 j (by omega) (by omega)).1
    have hsurj : Function.Surjective (Work.StemsB.πmap Fst ((j - 2) + 2) z₀) :=
      (by omega : (j + 1) - 1 = (j - 2) + 2) ▸ (hcov2 (j + 1) (by omega) (by omega)).2
    have hres : Subsingleton (Work.RatHurewicz.RelHomotopyGroup Fst z₀ ((j - 2) + 2)) :=
      Work.RatHurewicz.serreAux_relPi_subsingleton_of_injective_surjective Fst z₀ (j - 2) (by omega) hinj hsurj
    exact Work.RatHurewicz.serreAux_subsingleton_homotopyGroup_of_index_eq (x := f₀) (a := (j - 2) + 2)
      (b := j) (by omega) hres
  have hF_tors : ∀ α : HomotopyGroup (Fin (k + 2)) F f₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1 :=
    Work.RatHurewicz.serreAux_relPi_torsion_of_torsion Fst z₀ k (hcov1 (k + 2) (by omega))
      (hcov1 (k + 3) le_rfl) (fun β => htors (k + 2) (by omega) (by omega) β)
  have hF_pi0 : Subsingleton (HomotopyGroup (Fin 0) F f₀) := by
    have hApath : ∀ a : Z, Joined z₀ a :=
      (Work.RatHurewicz.serreAux_pathConnected_of_subsingleton_pi_zero z₀ (hcov1 0 (by omega))).joined z₀
    have hfib : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.fibreOf Fst z₀)
        (Work.RatHurewicz.fibreOfPt Fst z₀)) :=
      Work.RatHurewicz.serreAux_subsingleton_pi_zero_fibreOf Fst z₀
        (Work.Serre.subsingleton_pi0_loopSpace_of_pi1 y₀ (hconn 1 (by omega)))
    exact Work.Serre.subsingleton_pi0_homotopyFibre Fst z₀ hApath hfib
  have hF_comm : ∀ a b : HomotopyGroup (Fin 1) F f₀, a * b = b * a :=
    Work.RatHurewicz.serreAux_pi_one_comm Fst z₀ (hcov1 1 (by omega))
  -- `RangeEMVanAll` makes the double fibre rationally acyclic in the range
  have hvan_van : ∀ i : ℕ, 1 ≤ i → i ≤ N' - 2 → i ≠ k + 1 + 1 →
      Subsingleton (HomotopyGroup (Fin i) F f₀) := by
    intro i hi1 hiN hine
    by_cases hlow : i ≤ k + 1
    · exact hF_low i hi1 hlow
    · exact hF_high i (by omega) (by omega)
  have hvanF' := h (k + 1) (N' - 2) F f₀ hF_pi0 hF_comm hvan_van hF_tors
  have hvanF : ∀ t : ℕ, 0 < t → t ≤ M + 2 → IsZero (Work.Serre.ratH (TopCat.of F) t) := by
    intro t ht0 htM
    refine hvanF' t ht0 ?_
    have hle : (N' - 2) - 1 - 2 * (k + 1) = M + 5 := by omega
    omega
  -- `E3a`: the cover map is a rational homology isomorphism up to `M+1`
  have hiso : ∀ i : ℕ, i < M + 2 → IsIso (Work.Serre.ratHomologyMap Fst i) := by
    refine hE3a Z Y Fst z₀ (M + 2)
      (Work.RatHurewicz.isSerreFibration_homotopyFibreFst g y₀)
      (Work.RatHurewicz.serreAux_pathConnected_of_subsingleton_pi_zero y₀ (hconn 0 (by omega)))
      ⟨hvanF, ?_⟩
    exact Work.RatHurewicz.serreAux_isIso_toPoint_zero_of_subsingleton_pi_zero F f₀ hF_pi0
  -- `Z` is `s`-connected, so `H_s(Z;ℚ) = 0` by `E0`
  have hZs : IsZero (Work.Serre.ratH (TopCat.of Z) (k + 3)) := by
    have h0 := Work.Serre.serreE0Range Z z₀ (k + 3) (fun i hi => hcov1 i hi)
    exact h0 (k + 3) (by omega) (by omega)
  have hYs : IsZero (Work.Serre.ratH (TopCat.of Y) (k + 3)) := by
    haveI : IsIso (Work.Serre.ratHomologyMap Fst (k + 3)) := hiso (k + 3) (by omega)
    exact IsZero.of_iso hZs (asIso (Work.Serre.ratHomologyMap Fst (k + 3))).symm
  -- the torsion of the cover's homotopy groups
  have hZtors : ∀ m : ℕ, k + 3 + 1 ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Z z₀ m := by
    intro m hm1 hm2
    have hbj : Function.Bijective (Work.StemsB.πmap Fst m z₀) :=
      (by omega : m + 1 - 1 = m) ▸ (hcov2 (m + 1) (by omega) (by omega))
    intro α
    have htors' : ∀ β : HomotopyGroup (Fin (m + 1)) Y (Fst z₀),
        ∃ K : ℕ, 0 < K ∧ β ^ K = 1 := fun β => htors m (by omega) hm2 β
    obtain ⟨K, hK, hK1⟩ := htors' (Work.StemsB.πmap Fst m z₀ α)
    exact ⟨K, hK, hbj.1 (by simpa only [map_pow, map_one] using hK1)⟩
  refine ⟨Z, inferInstance, z₀, hcov1, hZtors, ?_, hYs⟩
  intro i hi hiM hZi
  haveI : IsIso (Work.Serre.ratHomologyMap Fst i) := hiso i (by omega)
  exact IsZero.of_iso hZi (asIso (Work.Serre.ratHomologyMap Fst i)).symm

/-- **The cover step for `s = 2`.**  From `Y` `1`-connected with torsion homotopy groups in degrees
`2, …, M`, produce the `2`-connected cover `Z` of `Y`, which has the same torsion homotopy groups in
degrees `3, …, M`, whose rational vanishing there transfers back to `Y`, and with `H_2(Y;ℚ) = 0`.

The double fibre of the cover map has its homotopy concentrated in degree `1` (`≅ π_2(Y)`, torsion)
and vanishing above, so `RangeEMVanAll` with `a = 0` applies. -/
theorem ratVanishing_step_two (hE3a : Work.Serre.SerreE3a) (h : Work.Serre.RangeEMVanAll)
    {M : ℕ} (h2M : 2 ≤ M) (Y : Type) [TopologicalSpace Y] (y₀ : Y)
    (hconn : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) Y y₀))
    (htors : ∀ m : ℕ, 2 ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Y y₀ m) :
    ∃ (Z : Type) (_ : TopologicalSpace Z) (z₀ : Z),
      (∀ i : ℕ, i ≤ 2 → Subsingleton (HomotopyGroup (Fin i) Z z₀)) ∧
      (∀ m : ℕ, 3 ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Z z₀ m) ∧
      (∀ i : ℕ, 3 ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of Z) i) →
          IsZero (Work.Serre.ratH (TopCat.of Y) i)) ∧
      IsZero (Work.Serre.ratH (TopCat.of Y) 2) := by
  classical
  set N' : ℕ := M + 8 with hN'def
  obtain ⟨P, tP, g, hg1, hg2⟩ := Work.Serre.serrePostnikovTower 2 N' Y y₀ (by omega)
  letI := tP
  let Z : Type := Work.RatHurewicz.homotopyFibre g y₀
  let z₀ : Z := Work.RatHurewicz.homotopyFibreBasepoint g y₀
  let Fst : C(Z, Y) := Work.RatHurewicz.homotopyFibreFst g y₀
  obtain ⟨hcov1, hcov2⟩ :=
    Work.Serre.serreConnectedCover 2 N' (by omega) (by omega) Y y₀ P g hg1 hg2
  let F : Type := Work.RatHurewicz.homotopyFibre Fst z₀
  let f₀ : F := Work.RatHurewicz.homotopyFibreBasepoint Fst z₀
  have hF_high : ∀ j : ℕ, 3 ≤ j → j + 2 ≤ N' → Subsingleton (HomotopyGroup (Fin j) F f₀) := by
    intro j hj hjN
    have h1 : Function.Injective (Work.StemsB.πmap Fst (j - 1) z₀) :=
      (hcov2 j (by omega) (by omega)).1
    have hinj : Function.Injective (Work.StemsB.πmap Fst ((j - 2) + 1) z₀) := by
      rwa [show j - 1 = (j - 2) + 1 from by omega] at h1
    have h2 : Function.Surjective (Work.StemsB.πmap Fst ((j + 1) - 1) z₀) :=
      (hcov2 (j + 1) (by omega) (by omega)).2
    have hsurj : Function.Surjective (Work.StemsB.πmap Fst ((j - 2) + 2) z₀) := by
      rwa [show (j + 1) - 1 = (j - 2) + 2 from by omega] at h2
    have hres : Subsingleton (Work.RatHurewicz.RelHomotopyGroup Fst z₀ ((j - 2) + 2)) :=
      Work.RatHurewicz.serreAux_relPi_subsingleton_of_injective_surjective Fst z₀ (j - 2) (by omega) hinj hsurj
    exact Work.RatHurewicz.serreAux_subsingleton_homotopyGroup_of_index_eq (x := f₀) (a := (j - 2) + 2)
      (b := j) (by omega) hres
  -- `π₂` of the double fibre: in the long exact sequence of the pair `(Z, Y)` at `k = 1`,
  -- `d : π₃(Y) →* π₂(F)` sits between `πmap Fst 2 z₀ : π₃(Z) →* π₃(Y)` (onto, as `Z` is the
  -- `2`-connected cover) and `πmap (homotopyFibreFst Fst z₀) 1 _ : π₂(F) →* π₂(Z)` (whose target
  -- is trivial).  Hence `d = 0` and `π₂(F) = ker(π₂(F) → π₂(Z)) = im d = 0`.
  have hF_two : Subsingleton (HomotopyGroup (Fin 2) F f₀) := by
    obtain ⟨del, d, h1, h2, h3, h4⟩ := Work.RatHurewicz.pair_les Fst z₀ 1 le_rfl
    have hsurjFst : Function.Surjective (Work.StemsB.πmap Fst 2 z₀) :=
      (hcov2 3 (by omega) (by omega)).2
    have hZ2 : Subsingleton (HomotopyGroup (Fin 2) Z z₀) := hcov1 2 le_rfl
    -- `d` is the zero map
    have hd1 : ∀ y : HomotopyGroup (Fin 3) Y (Fst z₀), d y = 1 := by
      intro y
      obtain ⟨x, hx⟩ := hsurjFst y
      exact (h3 y).mpr ⟨x, hx⟩
    -- every element of `π₂(F)` is `1`
    have hx1 : ∀ x : HomotopyGroup (Fin 2) (Work.RatHurewicz.homotopyFibre Fst z₀)
        (Work.RatHurewicz.homotopyFibreBasepoint Fst z₀), x = 1 := by
      intro x
      have hx : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst Fst z₀) 1
          (Work.RatHurewicz.homotopyFibreBasepoint Fst z₀)) x = 1 :=
        hZ2.elim _ _
      obtain ⟨w, hw⟩ := (h4 x).mp hx
      rw [← hw, hd1 w]
    exact ⟨fun a b => by rw [hx1 a, hx1 b]⟩
  have hF_tors : ∀ α : HomotopyGroup (Fin 1) F f₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1 := by
    -- `π₁` of the honest fibre of the cover projection is `π₂(Y)` (`pairShiftHom`), torsion.
    have hY2 : ∀ β : HomotopyGroup (Fin 2) Y (Fst z₀), ∃ K : ℕ, 0 < K ∧ β ^ K = 1 :=
      fun β => htors 1 (by omega) (by omega) β
    have hfibT : ∀ γ : HomotopyGroup (Fin 1) (Work.RatHurewicz.fibreOf Fst z₀)
        (Work.RatHurewicz.fibreOfPt Fst z₀), ∃ K : ℕ, 0 < K ∧ γ ^ K = 1 :=
      Work.RatHurewicz.serreAux_piTorsion_of_surjective_hom
        (MulEquiv.ofBijective (Work.RatHurewicz.pairShiftHom Fst z₀ 0)
          (Work.RatHurewicz.pairShiftHom_bijective Fst z₀ 0)).toMonoidHom
        (MulEquiv.ofBijective (Work.RatHurewicz.pairShiftHom Fst z₀ 0)
          (Work.RatHurewicz.pairShiftHom_bijective Fst z₀ 0)).surjective hY2
    -- the inclusion of the honest fibre into the homotopy fibre is surjective on `π₁`
    have hsurjFib := Work.Serre.piMap_fibreIncl_surjective_pi1
      (Work.RatHurewicz.homotopyFibreFst Fst z₀)
      (Work.RatHurewicz.isSerreFibration_homotopyFibreFst Fst z₀) f₀
      (hcov1 1 (by omega))
    intro α
    exact Work.RatHurewicz.serreAux_piTorsion_of_surjective_hom _
      hsurjFib hfibT α
  have hF_pi0 : Subsingleton (HomotopyGroup (Fin 0) F f₀) := by
    have hApath : ∀ a : Z, Joined z₀ a :=
      (Work.RatHurewicz.serreAux_pathConnected_of_subsingleton_pi_zero z₀ (hcov1 0 (by omega))).joined z₀
    have hfib : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.fibreOf Fst z₀)
        (Work.RatHurewicz.fibreOfPt Fst z₀)) :=
      Work.RatHurewicz.serreAux_subsingleton_pi_zero_fibreOf Fst z₀
        (Work.Serre.subsingleton_pi0_loopSpace_of_pi1 y₀ (hconn 1 (by omega)))
    exact Work.Serre.subsingleton_pi0_homotopyFibre Fst z₀ hApath hfib
  have hF_comm : ∀ a b : HomotopyGroup (Fin 1) F f₀, a * b = b * a :=
    Work.RatHurewicz.serreAux_pi_one_comm Fst z₀ (hcov1 1 (by omega))
  have hvanF' := h 0 (N' - 2) F f₀ hF_pi0 hF_comm
    (fun i hi1 hiN hine => by
      by_cases hi2 : i = 2
      · subst hi2; exact hF_two
      · exact hF_high i (by omega) (by omega)) hF_tors
  have hvanF : ∀ t : ℕ, 0 < t → t ≤ M + 2 → IsZero (Work.Serre.ratH (TopCat.of F) t) := by
    intro t ht0 htM
    refine hvanF' t ht0 ?_
    have hle : (N' - 2) - 1 - 0 = M + 5 := by omega
    omega
  have hiso : ∀ i : ℕ, i < M + 2 → IsIso (Work.Serre.ratHomologyMap Fst i) := by
    refine hE3a Z Y Fst z₀ (M + 2)
      (Work.RatHurewicz.isSerreFibration_homotopyFibreFst g y₀)
      (Work.RatHurewicz.serreAux_pathConnected_of_subsingleton_pi_zero y₀ (hconn 0 (by omega)))
      ⟨hvanF, ?_⟩
    exact Work.RatHurewicz.serreAux_isIso_toPoint_zero_of_subsingleton_pi_zero F f₀ hF_pi0
  have hZs : IsZero (Work.Serre.ratH (TopCat.of Z) 2) := by
    have h0 := Work.Serre.serreE0Range Z z₀ 2 (fun i hi => hcov1 i hi)
    exact h0 2 (by omega) (by omega)
  have hYs : IsZero (Work.Serre.ratH (TopCat.of Y) 2) := by
    haveI : IsIso (Work.Serre.ratHomologyMap Fst 2) := hiso 2 (by omega)
    exact IsZero.of_iso hZs (asIso (Work.Serre.ratHomologyMap Fst 2)).symm
  have hZtors : ∀ m : ℕ, 3 ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Z z₀ m := by
    intro m hm1 hm2
    have hbj : Function.Bijective (Work.StemsB.πmap Fst m z₀) :=
      (by omega : m + 1 - 1 = m) ▸ (hcov2 (m + 1) (by omega) (by omega))
    intro α
    have htors' : ∀ β : HomotopyGroup (Fin (m + 1)) Y (Fst z₀),
        ∃ K : ℕ, 0 < K ∧ β ^ K = 1 := fun β => htors m (by omega) hm2 β
    obtain ⟨K, hK, hK1⟩ := htors' (Work.StemsB.πmap Fst m z₀ α)
    exact ⟨K, hK, hbj.1 (by simpa only [map_pow, map_one] using hK1)⟩
  refine ⟨Z, inferInstance, z₀, hcov1, hZtors, ?_, hYs⟩
  intro i hi hiM hZi
  haveI : IsIso (Work.Serre.ratHomologyMap Fst i) := hiso i (by omega)
  exact IsZero.of_iso hZi (asIso (Work.Serre.ratHomologyMap Fst i)).symm

/-- **The induction.**  For `Y` `(s-1)`-connected (`2 ≤ s`) with torsion homotopy groups in
degrees `s, …, M`, the rational homology of `Y` vanishes in those degrees. -/
theorem ratVanishing_of_torsion_aux (hE3a : Work.Serre.SerreE3a) (h : Work.Serre.RangeEMVanAll) :
    ∀ (d : ℕ), ∀ (s M : ℕ), M - s = d → 2 ≤ s → s ≤ M →
      ∀ (Y : Type) [TopologicalSpace Y] (y₀ : Y),
        (∀ i : ℕ, i < s → Subsingleton (HomotopyGroup (Fin i) Y y₀)) →
        (∀ m : ℕ, s ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Y y₀ m) →
        (∀ i : ℕ, s ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of Y) i)) := by
  intro d
  induction d with
  | zero =>
    intro s M hMs hs hsM Y _ y₀ hconn htors i hi hiM
    have his : i = s := by omega
    subst i
    by_cases hs2 : s = 2
    · subst hs2
      obtain ⟨Z, -, z₀, -, -, -, hYs⟩ := ratVanishing_step_two hE3a h hsM Y y₀ hconn htors
      exact hYs
    · obtain ⟨Z, -, z₀, -, -, -, hYs⟩ := ratVanishing_step hE3a h (by omega) hsM Y y₀ hconn htors
      exact hYs
  | succ d ih =>
    intro s M hMs hs hsM Y _ y₀ hconn htors i hi hiM
    have hlt : s < M := by omega
    by_cases hs2 : s = 2
    · subst hs2
      obtain ⟨Z, tZ, z₀, hZconn, hZtors, htr, hYs⟩ :=
        ratVanishing_step_two hE3a h hsM Y y₀ hconn htors
      letI : TopologicalSpace Z := tZ
      by_cases hi3 : i = 2
      · subst hi3; exact hYs
      · have hi3' : 3 ≤ i := by omega
        have hZvan := ih 3 M (by omega) (by omega) (by omega) Z z₀
          (fun j hj => hZconn j (by omega)) hZtors i hi3' hiM
        exact htr i hi3' hiM hZvan
    · obtain ⟨Z, tZ, z₀, hZconn, hZtors, htr, hYs⟩ :=
        ratVanishing_step hE3a h (by omega) hsM Y y₀ hconn htors
      letI : TopologicalSpace Z := tZ
      by_cases his : i = s
      · subst his; exact hYs
      · have his' : s + 1 ≤ i := by omega
        have hZvan := ih (s + 1) M (by omega) (by omega) (by omega) Z z₀
          (fun j hj => hZconn j (by omega)) hZtors i his' hiM
        exact htr i his' hiM hZvan

/-- **Serre's mod-torsion Hurewicz theorem in the torsion case, from `E3a` and `RangeEMVanAll`.**

`X` simply connected (π₀, π₁ trivial) with `π_{j+2}(X)` torsion for `j + 2 ≤ M` has
`H_i(X;ℚ) = 0` for `1 ≤ i ≤ M`. -/
theorem ratVanishingBelow_of_torsion (hE3a : Work.Serre.SerreE3a) (h : Work.Serre.RangeEMVanAll)
    (M : ℕ) (X : Type) [TopologicalSpace X] (x₀ : X)
    (h0 : Subsingleton (HomotopyGroup (Fin 0) X x₀))
    (h1 : Subsingleton (HomotopyGroup (Fin 1) X x₀))
    (htors : ∀ j : ℕ, j + 2 ≤ M →
      ∀ α : HomotopyGroup (Fin (j + 2)) X x₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1) :
    ∀ i : ℕ, 1 ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of X) i) := by
  have hlow : ∀ j : ℕ, j ≤ 1 → Subsingleton (HomotopyGroup (Fin j) X x₀) := by
    intro j hj
    interval_cases j
    · exact h0
    · exact h1
  by_cases hM : M < 2
  · intro i hi hiM
    have hi1 : i = 1 := by omega
    subst hi1
    exact (Work.Serre.serreE0Range X x₀ 1 (fun j hj => hlow j hj)) 1 (by omega) (by omega)
  · intro i hi hiM
    by_cases hi1 : i = 1
    · subst hi1
      exact (Work.Serre.serreE0Range X x₀ 1 (fun j hj => hlow j hj)) 1 (by omega) (by omega)
    · exact ratVanishing_of_torsion_aux hE3a h (M - 2) 2 M (by omega) (by omega) (by omega) X x₀
        (fun j hj => hlow j (by omega))
        (fun m hm1 hm2 => piTorsionRaw_of_index_eq x₀ (by omega : (m - 1) + 2 = m + 1)
          (fun α => htors (m - 1) (by omega) α)) i (by omega) hiM

end

end Work.RatHurewicz
