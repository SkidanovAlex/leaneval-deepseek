import Mathlib
import Submission.Work.Serre.RangeEMVanDefs
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreConnectedCover
import Submission.Work.Serre.Consumers
import Submission.Work.Serre.subsingleton_pi0_homotopyFibre
import Submission.Work.Serre.subsingleton_pi0_loopSpace_of_pi1
import Submission.Work.Serre.piMap_fibreIncl_surjective_pi1
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.RatHurewicz.Consumers
import Submission.Work.RatHurewicz.torsion_of_subsingleton_ratHomology
import Submission.Work.RatHurewicz.hurewiczKerTorsionFirstDegree
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.RatHurewicz.PairShiftBijective
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Serre.serreE0Range

/-!
# `SerreS1` from the range form of the acyclicity of Eilenberg–MacLane spaces

This file proves `Work.Serre.serreS1OfRangeEMVan`:

`SerreE3a → RangeEMVanAll → SerreS1`,

i.e. the assembly of the rational vanishing Hurewicz theorem (S1 of the blueprint
`Submission/Work/Drive/SERRE_BLUEPRINT.md` §3) from

* the mapping theorem `Work.Serre.SerreE3a` (`E3(a)`), and
* the range form of the acyclicity of the truncated models of `K(A,·)`,
  `Work.Serre.RangeEMVanAll`, for torsion `A`.

## The argument

Let `Y` be `(s-1)`-connected, `3 ≤ s ≤ M`, with `H_i(Y;ℚ) = 0` for `s ≤ i ≤ M`.  We show
`π_m(Y)` torsion for `s ≤ m+1 ≤ M` by induction on `M - s`:

* `π_s(Y)` is torsion by the Hurewicz theorem modulo torsion in the first non-vanishing degree
  (`Work.RatHurewicz.hurewiczKerTorsionFirstDegree` together with
  `Work.RatHurewicz.torsion_of_subsingleton_ratHomology`);
* passing to the `s`-truncation `g : Y → P` (`Work.Serre.serrePostnikovTower`) and its homotopy
  fibre `Z` (`Work.Serre.serreConnectedCover`), the *homotopy fibre* of the cover map `Z → Y` is
  the loop space `ΩP` up to homotopy, whose homotopy groups are `π_{i+1}(P)`: they vanish for
  `i ≥ s` and in degrees `2 ≤ i ≤ s-2`, and `π_{s-1}` is torsion (all by the long exact sequence of
  `Work.RatHurewicz.pair_les`).  Hence `RangeEMVanAll` makes that fibre rationally acyclic in a
  range, `E3a` makes `Z → Y` a rational homology isomorphism in that range, and the induction
  hypothesis applies to `Z` (which is `s`-connected with `π_i(Z) ≅ π_i(Y)` for `s < i < N'`).

The auxiliary lemmas `serreAux*` below isolate the two ingredients of the argument: the reindexing
of homotopy groups, and the four consequences of the long exact sequence of a pair that we need.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## Elementary transfers -/

/-- `Subsingleton` statements are transported between equal indices. -/
theorem serreAux_subsingleton_homotopyGroup_of_index_eq {X : Type} [TopologicalSpace X] {x : X}
    {a b : ℕ} (h : a = b) (hm : Subsingleton (HomotopyGroup (Fin a) X x)) :
    Subsingleton (HomotopyGroup (Fin b) X x) := h ▸ hm

/-- Torsion statements are transported between equal indices. -/
theorem serreAux_piTorsion_of_index_eq {X : Type} [TopologicalSpace X] (x : X) {a b : ℕ}
    (h : a = b) (hm : PiTorsion X x a) : PiTorsion X x b := h ▸ hm

/-- `Subsingleton` transfer along a multiplicative equivalence. -/
theorem serreAux_subsingleton_of_mulEquiv {G H : Type*} [Mul G] [Mul H] (e : G ≃* H)
    (h : Subsingleton H) : Subsingleton G :=
  ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩

/-- Torsion is preserved by a surjective homomorphism of groups. -/
theorem serreAux_piTorsion_of_surjective_hom {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) (h : ∀ g : G, ∃ N : ℕ, 0 < N ∧ g ^ N = 1) :
    ∀ h' : H, ∃ N : ℕ, 0 < N ∧ h' ^ N = 1 := by
  intro h'
  obtain ⟨g, rfl⟩ := hφ h'
  obtain ⟨N, hN, hg⟩ := h g
  exact ⟨N, hN, by rw [← map_pow, hg, map_one]⟩

/-- A space whose `π₀` is trivial is path connected. -/
theorem serreAux_pathConnected_of_subsingleton_pi_zero {X : Type} [TopologicalSpace X] (x₀ : X)
    (h : Subsingleton (HomotopyGroup (Fin 0) X x₀)) : PathConnectedSpace X := by
  have hZ : Subsingleton (ZerothHomotopy X) := by
    refine ⟨fun a b => ?_⟩
    have h1 := congrArg (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀))
      (Subsingleton.elim
        ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).symm a)
        ((HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x₀)).symm b))
    simpa using h1
  exact (pathConnectedSpace_iff_zerothHomotopy).mpr ⟨⟨ZerothHomotopy.mk x₀⟩, hZ⟩

/-- A path connected space has trivial `π₀`. -/
theorem serreAux_subsingleton_pi_zero_of_pathConnected {X : Type} [TopologicalSpace X] (x : X)
    (h : PathConnectedSpace X) : Subsingleton (HomotopyGroup (Fin 0) X x) := by
  have hZ : Subsingleton (ZerothHomotopy X) := (pathConnectedSpace_iff_zerothHomotopy).mp h |>.2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective
    (Subsingleton.elim _ _)⟩

/-- `π₀` of a one-point space is a point. -/
theorem serreAux_pi_zero_of_subsingleton (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (y : Y) :
    Subsingleton (HomotopyGroup (Fin 0) Y y) := by
  have h : Subsingleton (ZerothHomotopy Y) :=
    inferInstanceAs (Subsingleton (Quotient (pathSetoid Y)))
  exact ⟨fun a b =>
    (HomotopyGroup.pi0EquivZerothHomotopy (x := y)).injective (Subsingleton.elim _ _)⟩

/-- **`H₀(X;ℚ) ≅ ℚ` when `π₀(X)` is a point**, i.e. the degree-`0` case of K2
(`Work.Serre.hZeroOfPiZero`) in the form in which `RatAcyclicBelow` needs it. -/
theorem serreAux_isIso_toPoint_zero_of_subsingleton_pi_zero (X : Type) [TopologicalSpace X]
    (x₀ : X) (h : Subsingleton (HomotopyGroup (Fin 0) X x₀)) :
    IsIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint X) 0) := by
  haveI hpc : PathConnectedSpace X := serreAux_pathConnected_of_subsingleton_pi_zero x₀ h
  refine Work.Serre.hZeroOfPiZero (Work.Serre.toPoint X) (fun x => ?_)
  haveI hx : Subsingleton (HomotopyGroup (Fin 0) X x) :=
    serreAux_subsingleton_pi_zero_of_pathConnected x (inferInstance : PathConnectedSpace X)
  haveI hy : Subsingleton (HomotopyGroup (Fin 0) PUnit (Work.Serre.toPoint X x)) :=
    serreAux_pi_zero_of_subsingleton PUnit (Work.Serre.toPoint X x)
  exact ⟨fun a b _ => Subsingleton.elim a b,
    fun y => ⟨(HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm (ZerothHomotopy.mk x),
      Subsingleton.elim _ _⟩⟩

/-! ## The Hurewicz map and its behaviour on powers -/

/-- The Hurewicz map sends `1` to `0`. -/
theorem serreAux_hurewiczMapN_one (n : ℕ) {X : Type} [TopologicalSpace X] (x₀ : X) :
    Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀
      (1 : HomotopyGroup (Fin (n + 1)) X x₀) = 0 := by
  have h := Work.Stems.hurewiczMapN_mul n x₀ (1 : HomotopyGroup (Fin (n + 1)) X x₀) 1
  rw [one_mul] at h
  refine (add_left_cancel (show Work.Stems.hurewiczMapN (n + 1) _ x₀ 1 + 0
    = Work.Stems.hurewiczMapN (n + 1) _ x₀ 1
      + Work.Stems.hurewiczMapN (n + 1) _ x₀ 1 by rw [add_zero]; exact h)).symm

/-- The Hurewicz map is additive under powers: `h(a^N) = N • h(a)`. -/
theorem serreAux_hurewiczMapN_pow (n : ℕ) {X : Type} [TopologicalSpace X] {x₀ : X}
    (a : HomotopyGroup (Fin (n + 1)) X x₀) (N : ℕ) :
    Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ (a ^ N) =
      N • Work.Stems.hurewiczMapN (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) x₀ a := by
  induction N with
  | zero => rw [pow_zero, zero_nsmul, serreAux_hurewiczMapN_one]
  | succ N ih => rw [pow_succ, Work.Stems.hurewiczMapN_mul, ih, succ_nsmul]

/-! ## Hurewicz modulo torsion in the first non-vanishing degree -/

/-- **`π_{m+1}` of a space is torsion when it is the first non-vanishing degree and the rational
homology vanishes there.**  A class `a` whose Hurewicz image is torsion has a power killed by the
Hurewicz map, and `Work.RatHurewicz.hurewiczKerTorsionFirstDegree` makes that power torsion. -/
theorem serreAuxTorsionFirstDegree {m : ℕ} (hm : 1 ≤ m) {X : Type} [TopologicalSpace X]
    (x₀ : X) (hconn : ∀ i < m + 1, Subsingleton (HomotopyGroup (Fin i) X x₀))
    (h : Subsingleton ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology (m + 1))) :
    ∀ a : HomotopyGroup (Fin (m + 1)) X x₀, ∃ N : ℕ, 0 < N ∧ a ^ N = 1 := by
  intro a
  obtain ⟨N, hN, hNb⟩ := Work.RatHurewicz.torsion_of_subsingleton_ratHomology (m + 1) h
    (Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀ a)
  obtain ⟨K, hK, hK1⟩ := Work.RatHurewicz.hurewiczKerTorsionFirstDegree m hm X x₀ hconn (a ^ N)
    (by rw [serreAux_hurewiczMapN_pow, hNb])
  exact ⟨N * K, Nat.mul_pos hN hK, by rw [pow_mul]; exact hK1⟩

/-! ## Consequences of the long exact sequence of the pair `(X, A)` -/

section LES

variable {X A : Type} [TopologicalSpace X] [TopologicalSpace A]

/-- **The projection of the homotopy fibre is trivial on `π_{k+2}` when `π_{k+2}(A)` is trivial.**
(The statement is phrased at the base point `(homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)`,
which is definitionally `a₀`; the instance is ascribed explicitly so that type class synthesis does
not have to see through that identification.) -/
theorem serreAux_pair_e_eq_one (i : C(A, X)) (a₀ : A) (k : ℕ)
    (hA : Subsingleton (HomotopyGroup (Fin (k + 2)) A a₀))
    (x : Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2)) :
    (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) x = 1 := by
  haveI : Subsingleton (HomotopyGroup (Fin (k + 2)) A
      ((Work.RatHurewicz.homotopyFibreFst i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) := hA
  exact Subsingleton.elim _ _

/-- **Exactness at `π_{k+2}(A)` of the pair sequence**: the composite of the projection of the
homotopy fibre with `i_*` is trivial. -/
theorem serreAux_pair_comp_eq_one (i : C(A, X)) (a₀ : A) (k : ℕ) (hk : 1 ≤ k)
    (x : Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2)) :
    (Work.StemsB.πmap i (k + 1) a₀)
      ((Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) x) = 1 := by
  obtain ⟨_, _, _, h2, _, _⟩ := Work.RatHurewicz.pair_les i a₀ k hk
  exact (h2 _).mpr ⟨x, rfl⟩

/-- **`π_{k+2}` of the homotopy fibre vanishes when the two neighbouring groups do.** -/
theorem serreAux_relPi_subsingleton_of_subsingleton (i : C(A, X)) (a₀ : A) (k : ℕ)
    (hA : Subsingleton (HomotopyGroup (Fin (k + 2)) A a₀))
    (hX : Subsingleton (HomotopyGroup (Fin (k + 3)) X (i a₀))) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2)) := by
  obtain ⟨del, d, h1, h2, h3, h4⟩ := Work.RatHurewicz.pair_les i a₀ (k + 1) (by omega)
  haveI hX' : Subsingleton (HomotopyGroup (Fin ((k + 1) + 2)) X (i a₀)) := hX
  have key : ∀ x : Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2), x = 1 := by
    intro x
    have hex : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) x = 1 :=
      serreAux_pair_e_eq_one i a₀ k hA x
    obtain ⟨z, hz⟩ := (h4 x).mp hex
    rw [← hz]
    rw [show z = 1 from Subsingleton.elim z 1, map_one]
  exact ⟨fun x y => by rw [key x, key y]⟩

/-- **`π_{k+2}` of the homotopy fibre vanishes when `i_*` is injective in degree `k+2` and
surjective in degree `k+3`.** -/
theorem serreAux_relPi_subsingleton_of_injective_surjective (i : C(A, X)) (a₀ : A) (k : ℕ)
    (hk : 1 ≤ k)
    (hinj : Function.Injective (Work.StemsB.πmap i (k + 1) a₀))
    (hsurj : Function.Surjective (Work.StemsB.πmap i (k + 2) a₀)) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2)) := by
  obtain ⟨del, d, h1, h2, h3, h4⟩ := Work.RatHurewicz.pair_les i a₀ k hk
  obtain ⟨del', d', h1', h2', h3', h4'⟩ := Work.RatHurewicz.pair_les i a₀ (k + 1) (by omega)
  -- the connecting map `π_{k+3}(X) → π_{k+2}(F)` is zero
  have hd' : ∀ z, d' z = 1 := by
    intro z
    obtain ⟨w, hw⟩ := hsurj z
    exact (h3' z).mpr ⟨w, hw⟩
  have key : ∀ x : Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2), x = 1 := by
    intro x
    -- the image of the projection is contained in the kernel of the injective `i_*`
    have hmain : (Work.StemsB.πmap i (k + 1) a₀)
        ((Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) x) = 1 :=
      serreAux_pair_comp_eq_one i a₀ k hk x
    have hone : (Work.StemsB.πmap i (k + 1) a₀)
        (1 : HomotopyGroup (Fin (k + 2)) A a₀) = 1 := map_one _
    have hex : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) x = 1 :=
      hinj (hmain.trans hone.symm)
    obtain ⟨z, hz⟩ := (h4' x).mp hex
    rw [← hz]
    exact hd' z
  exact ⟨fun x y => by rw [key x, key y]⟩

/-- **Torsion of `π_{k+3}(X)` transfers to `π_{k+2}` of the homotopy fibre** when
`π_{k+2}(A) = π_{k+3}(A) = 0`: the connecting map `π_{k+3}(X) → π_{k+2}(F)` is then bijective. -/
theorem serreAux_relPi_torsion_of_torsion (i : C(A, X)) (a₀ : A) (k : ℕ)
    (hA2 : Subsingleton (HomotopyGroup (Fin (k + 2)) A a₀))
    (hA3 : Subsingleton (HomotopyGroup (Fin (k + 3)) A a₀))
    (hX : ∀ β : HomotopyGroup (Fin (k + 3)) X (i a₀), ∃ K : ℕ, 0 < K ∧ β ^ K = 1) :
    ∀ α : Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2), ∃ K : ℕ, 0 < K ∧ α ^ K = 1 := by
  obtain ⟨del, d, h1, h2, h3, h4⟩ := Work.RatHurewicz.pair_les i a₀ (k + 1) (by omega)
  haveI hA3' : Subsingleton (HomotopyGroup (Fin ((k + 1) + 2)) A a₀) := hA3
  have hinj : Function.Injective d := by
    intro x y hxy
    have hker : x * y⁻¹ = 1 := by
      have h1' : d (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
      have hmem : x * y⁻¹ ∈ Set.range (Work.StemsB.πmap i ((k + 1) + 1) a₀) :=
        (h3 (x * y⁻¹)).mp h1'
      obtain ⟨u, hu⟩ := hmem
      rw [← hu]
      rw [show u = 1 from Subsingleton.elim u 1, map_one]
    exact mul_inv_eq_one.mp hker
  have hsurj : Function.Surjective d := by
    intro y
    have hy : (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) y = 1 :=
      serreAux_pair_e_eq_one i a₀ k hA2 y
    exact (h4 y).mp hy
  exact serreAux_piTorsion_of_surjective_hom d hsurj hX

/-- **`π₁` of the homotopy fibre vanishes when `π₁` of the source and `π₂` of the target do.** -/
theorem serreAux_pi_one_homotopyFibre_subsingleton (i : C(A, X)) (a₀ : A)
    (hA : Subsingleton (HomotopyGroup (Fin 1) A a₀))
    (hX : Subsingleton (HomotopyGroup (Fin 2) X (i a₀))) :
    Subsingleton (HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
  haveI hA' : Subsingleton (HomotopyGroup (Fin 1) A
      ((Work.RatHurewicz.homotopyFibreFst i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) := hA
  have hfib : Subsingleton (HomotopyGroup (Fin 1) (Work.RatHurewicz.fibreOf i a₀)
      (Work.RatHurewicz.fibreOfPt i a₀)) :=
    serreAux_subsingleton_of_mulEquiv
      (MulEquiv.ofBijective (Work.RatHurewicz.pairShiftHom i a₀ 0)
        (Work.RatHurewicz.pairShiftHom_bijective i a₀ 0)).symm hX
  haveI hfib' : Subsingleton (HomotopyGroup (Fin 1)
      (Work.StemsB.fibre (Work.RatHurewicz.homotopyFibreFst i a₀)
        ((Work.RatHurewicz.homotopyFibreFst i a₀) (Work.RatHurewicz.homotopyFibreBasepoint i a₀)))
      (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) := hfib
  have hsurj := Work.Serre.piMap_fibreIncl_surjective_pi1
    (Work.RatHurewicz.homotopyFibreFst i a₀)
    (Work.RatHurewicz.isSerreFibration_homotopyFibreFst i a₀)
    (Work.RatHurewicz.homotopyFibreBasepoint i a₀) hA'
  exact ⟨fun x y => by
    obtain ⟨x', rfl⟩ := hsurj x
    obtain ⟨y', rfl⟩ := hsurj y
    rw [Subsingleton.elim x' y']⟩

/-- Commutativity transfers along a multiplicative equivalence. -/
theorem serreAux_mul_comm_of_mulEquiv {G H : Type*} [Mul G] [Mul H] (e : G ≃* H)
    (h : ∀ a b : H, a * b = b * a) : ∀ a b : G, a * b = b * a := by
  intro a b
  exact e.injective (by rw [map_mul, map_mul]; exact h (e a) (e b))

/-- **`π₁` of the homotopy fibre is abelian when `π₁` of the source is trivial.**  It is a quotient
of `π₁` of the honest fibre (`Work.Serre.piMap_fibreIncl_surjective_pi1`), which is `π₂(X)` by
`Work.RatHurewicz.pairShiftHom_bijective`, and `π₂` of a space is abelian (`Eckmann–Hilton`). -/
theorem serreAux_pi_one_comm (i : C(A, X)) (a₀ : A)
    (hA : Subsingleton (HomotopyGroup (Fin 1) A a₀)) :
    ∀ a b : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀), a * b = b * a := by
  -- `π₁` of the honest fibre is `π₂(X)`, hence abelian
  have hcomm_fib : ∀ a b : HomotopyGroup (Fin 1) (Work.RatHurewicz.fibreOf i a₀)
      (Work.RatHurewicz.fibreOfPt i a₀), a * b = b * a :=
    serreAux_mul_comm_of_mulEquiv
      (MulEquiv.ofBijective
        (M := HomotopyGroup (Fin 2) X (i a₀))
        (N := HomotopyGroup (Fin 1) (Work.RatHurewicz.fibreOf i a₀)
          (Work.RatHurewicz.fibreOfPt i a₀))
        (Work.RatHurewicz.pairShiftHom i a₀ 0)
        (Work.RatHurewicz.pairShiftHom_bijective i a₀ 0)).symm
      (fun a b => mul_comm a b)
  haveI hA' : Subsingleton (HomotopyGroup (Fin 1) A
      ((Work.RatHurewicz.homotopyFibreFst i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) := hA
  -- the projection of the honest fibre onto the total space, at the canonical base point
  let f : HomotopyGroup (Fin 1) (Work.RatHurewicz.fibreOf i a₀)
        (Work.RatHurewicz.fibreOfPt i a₀) →*
      HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀) :=
    Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
        ((Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) 0
      (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
  have hsurj : Function.Surjective f :=
    Work.Serre.piMap_fibreIncl_surjective_pi1
      (Work.RatHurewicz.homotopyFibreFst i a₀)
      (Work.RatHurewicz.isSerreFibration_homotopyFibreFst i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀) hA'
  intro a b
  obtain ⟨x, hx⟩ := hsurj a
  obtain ⟨y, hy⟩ := hsurj b
  calc a * b = f (x * y) := by rw [map_mul, hx, hy]
    _ = f (y * x) := congrArg f (hcomm_fib x y)
    _ = b * a := by rw [map_mul, hy, hx]

/-- **`π₀` of the honest fibre of the projection of the homotopy fibre** (the loop space `ΩX`) is
trivial when `π₁(X) = 0`. -/
theorem serreAux_subsingleton_pi_zero_fibreOf (i : C(A, X)) (a₀ : A)
    (h : Subsingleton (HomotopyGroup (Fin 0) (Path (i a₀) (i a₀)) (Path.refl (i a₀)))) :
    Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.fibreOf i a₀)
      (Work.RatHurewicz.fibreOfPt i a₀)) := by
  have hpc : PathConnectedSpace (Path (i a₀) (i a₀)) :=
    serreAux_pathConnected_of_subsingleton_pi_zero (Path.refl (i a₀)) h
  have hjoin : ∀ e : Work.RatHurewicz.fibreOf i a₀,
      Joined (Work.RatHurewicz.fibreOfPt i a₀) e := by
    intro e
    obtain ⟨γ⟩ := hpc.joined (Work.RatHurewicz.fibrePhi i a₀ e) (Path.refl (i a₀))
    have h2 : Joined (Work.RatHurewicz.fibrePsi i a₀ (Work.RatHurewicz.fibrePhi i a₀ e))
        (Work.RatHurewicz.fibrePsi i a₀ (Path.refl (i a₀))) :=
      ⟨γ.map (Work.RatHurewicz.fibrePsi i a₀).continuous⟩
    rw [Work.RatHurewicz.fibrePsi_fibrePhi] at h2
    rw [Work.RatHurewicz.fibrePsi_refl] at h2
    exact h2.symm
  exact serreAux_subsingleton_pi_zero_of_pathConnected (Work.RatHurewicz.fibreOfPt i a₀)
    ⟨⟨Work.RatHurewicz.fibreOfPt i a₀⟩, fun e₁ e₂ => (hjoin e₁).symm.trans (hjoin e₂)⟩

end LES

/-! ## The induction on the degrees -/

/-- **The rational vanishing Hurewicz theorem in a range, for a space `Y` which is
`(s-1)`-connected with `3 ≤ s`.**  If `H_i(Y;ℚ) = 0` for `s ≤ i ≤ M` then `π_{m+1}(Y)` is torsion
for `s ≤ m+1 ≤ M`.  The proof is the induction on `M - s` described in the module docstring. -/
private theorem serreAux_ind (hE3a : Work.Serre.SerreE3a) (h : Work.Serre.RangeEMVanAll) :
    ∀ (d : ℕ), ∀ (s M : ℕ), M - s = d → 2 ≤ s → s ≤ M → M ≤ 2 * s - 2 →
      ∀ (Y : Type) [TopologicalSpace Y] (y₀ : Y),
        (∀ i, i < s → Subsingleton (HomotopyGroup (Fin i) Y y₀)) →
        (∀ i, s ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of Y) i)) →
        (∀ m, s ≤ m + 1 → m + 1 ≤ M → Work.Serre.PiTorsion Y y₀ m) := by
  intro d
  induction d with
  | zero =>
    -- only one degree is left, and it is killed by the Hurewicz theorem modulo torsion
    intro s M hMs hs hsM h2s Y _ y₀ hconn hhom m hm1 hm2
    have hs' : s = m + 1 := by omega
    subst hs'
    have hM' : M = m + 1 := by omega
    subst hM'
    exact serreAuxTorsionFirstDegree (m := m) (by omega) y₀ (fun i hi => hconn i hi)
      (Work.Serre.subsingleton_of_isZero (hhom (m + 1) (by omega) (by omega)))
  | succ d ih =>
    intro s M hMs hs hsM h2s Y _ y₀ hconn hhom m hm1 hm2
    by_cases hs3 : 3 ≤ s
    swap
    · -- `s = 2` would force `M ≥ 3` and `M ≤ 2`
      exfalso
      omega
    -- name the connectivity class
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 3 := ⟨s - 3, by omega⟩
    -- (1) `π_{k+3}(Y)` is torsion
    have htors : ∀ β : HomotopyGroup (Fin (k + 3)) Y y₀, ∃ K : ℕ, 0 < K ∧ β ^ K = 1 :=
      serreAuxTorsionFirstDegree (m := k + 2) (by omega) y₀ (fun i hi => hconn i (by omega))
        (Work.Serre.subsingleton_of_isZero (hhom (k + 3) (by omega) (by omega)))
    -- (2) the truncation, the cover and the homotopy fibre of the cover map
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
    -- (3) the homotopy groups of the double fibre
    have hF_low : ∀ j, 1 ≤ j → j ≤ k + 1 → Subsingleton (HomotopyGroup (Fin j) F f₀) := by
      intro j hj1 hjk
      by_cases hj : j = 1
      · subst hj
        exact serreAux_pi_one_homotopyFibre_subsingleton Fst z₀
          (hcov1 1 (by omega)) (hconn 2 (by omega))
      · have hZ : Subsingleton (HomotopyGroup (Fin ((j - 2) + 2)) Z z₀) :=
          serreAux_subsingleton_homotopyGroup_of_index_eq (x := z₀) (a := j) (b := (j - 2) + 2)
            (by omega) (hcov1 j (by omega))
        have hY : Subsingleton (HomotopyGroup (Fin (((j - 2) + 2) + 1)) Y y₀) :=
          serreAux_subsingleton_homotopyGroup_of_index_eq (x := y₀) (a := j + 1)
            (b := ((j - 2) + 2) + 1) (by omega) (hconn (j + 1) (by omega))
        have hres : Subsingleton (Work.RatHurewicz.RelHomotopyGroup Fst z₀ ((j - 2) + 2)) :=
          serreAux_relPi_subsingleton_of_subsingleton Fst z₀ (j - 2) hZ hY
        exact serreAux_subsingleton_homotopyGroup_of_index_eq (x := f₀) (a := (j - 2) + 2)
          (b := j) (by omega) hres
    have hF_high : ∀ j, k + 3 ≤ j → j + 2 ≤ N' → Subsingleton (HomotopyGroup (Fin j) F f₀) := by
      intro j hj hjN
      have hinj : Function.Injective (Work.StemsB.πmap Fst ((j - 2) + 1) z₀) := by
        by_cases hj' : j = k + 3
        · -- the source `π_{k+3}(Z)` is trivial
          have hZ := serreAux_subsingleton_homotopyGroup_of_index_eq (x := z₀) (a := k + 3)
            (b := ((j - 2) + 1) + 1) (by omega) (hcov1 (k + 3) le_rfl)
          haveI := hZ
          exact fun a b _ => Subsingleton.elim a b
        · exact (by omega : j - 1 = (j - 2) + 1) ▸ (hcov2 j (by omega) (by omega)).1
      have hsurj : Function.Surjective (Work.StemsB.πmap Fst ((j - 2) + 2) z₀) :=
        (by omega : (j + 1) - 1 = (j - 2) + 2) ▸ (hcov2 (j + 1) (by omega) (by omega)).2
      have hres : Subsingleton (Work.RatHurewicz.RelHomotopyGroup Fst z₀ ((j - 2) + 2)) :=
        serreAux_relPi_subsingleton_of_injective_surjective Fst z₀ (j - 2) (by omega) hinj hsurj
      exact serreAux_subsingleton_homotopyGroup_of_index_eq (x := f₀) (a := (j - 2) + 2)
        (b := j) (by omega) hres
    have hF_tors : ∀ α : HomotopyGroup (Fin (k + 2)) F f₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1 :=
      serreAux_relPi_torsion_of_torsion Fst z₀ k (hcov1 (k + 2) (by omega))
        (hcov1 (k + 3) le_rfl) htors
    have hF_pi0 : Subsingleton (HomotopyGroup (Fin 0) F f₀) := by
      have hApath : ∀ a : Z, Joined z₀ a :=
        (serreAux_pathConnected_of_subsingleton_pi_zero z₀ (hcov1 0 (by omega))).joined z₀
      have hfib : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.fibreOf Fst z₀)
          (Work.RatHurewicz.fibreOfPt Fst z₀)) :=
        serreAux_subsingleton_pi_zero_fibreOf Fst z₀
          (Work.Serre.subsingleton_pi0_loopSpace_of_pi1 y₀ (hconn 1 (by omega)))
      exact Work.Serre.subsingleton_pi0_homotopyFibre Fst z₀ hApath hfib
    -- (4) `RangeEMVanAll` makes the double fibre rationally acyclic in the range
    have hvan_van : ∀ i : ℕ, 1 ≤ i → i ≤ N' - 2 → i ≠ k + 1 + 1 →
        Subsingleton (HomotopyGroup (Fin i) F f₀) := by
      intro i hi1 hiN hine
      by_cases hlow : i ≤ k + 1
      · exact hF_low i hi1 hlow
      · exact hF_high i (by omega) (by omega)
    have hvan_tors : ∀ α : HomotopyGroup (Fin ((k + 1) + 1)) F f₀,
        ∃ K : ℕ, 0 < K ∧ α ^ K = 1 := hF_tors
    have hF_comm : ∀ a b : HomotopyGroup (Fin 1) F f₀, a * b = b * a :=
      serreAux_pi_one_comm Fst z₀ (hcov1 1 (by omega))
    have hvanF' := h (k + 1) (N' - 2) F f₀ hF_pi0 hF_comm hvan_van hvan_tors
    have hvanF : ∀ t : ℕ, 0 < t → t ≤ M + 2 → IsZero (Work.Serre.ratH (TopCat.of F) t) := by
      intro t ht0 htM
      refine hvanF' t ht0 ?_
      have hle : (N' - 2) - 1 - 2 * (k + 1) = M + 5 := by omega
      omega
    -- (5) `E3a`: the cover map is a rational homology isomorphism up to `M+1`
    have hiso : ∀ i, i < M + 2 → IsIso (Work.Serre.ratHomologyMap Fst i) := by
      refine hE3a Z Y Fst z₀ (M + 2)
        (Work.RatHurewicz.isSerreFibration_homotopyFibreFst g y₀)
        (serreAux_pathConnected_of_subsingleton_pi_zero y₀ (hconn 0 (by omega)))
        ⟨hvanF, ?_⟩
      exact serreAux_isIso_toPoint_zero_of_subsingleton_pi_zero F f₀ hF_pi0
    -- (6) the induction hypothesis applies to the cover `Z`
    have hhomZ : ∀ i, k + 4 ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of Z) i) := by
      intro i hi1 hi2
      haveI : IsIso (Work.Serre.ratHomologyMap Fst i) := hiso i (by omega)
      exact IsZero.of_iso (hhom i (by omega) hi2) (asIso (Work.Serre.ratHomologyMap Fst i))
    have hIH := ih (k + 4) M (by omega) (by omega) (by omega) (by omega) Z z₀
      (fun i hi => hcov1 i (by omega)) hhomZ
    -- (7) conclude
    by_cases hm : m + 1 = k + 3
    · -- the degree `k+3` itself
      exact serreAux_piTorsion_of_index_eq y₀ (by omega : k + 2 = m) htors
    · -- higher degrees transfer from `Z` along the cover
      have hsurj : Function.Surjective (Work.StemsB.πmap Fst m z₀) :=
        (by omega : (m + 1) - 1 = m) ▸ (hcov2 (m + 1) (by omega) (by omega)).2
      exact serreAux_piTorsion_of_surjective_hom (Work.StemsB.πmap Fst m z₀) hsurj
        (hIH m (by omega) hm2)

/-- **S1 from `SerreE3a` and the range form of the acyclicity of the truncated Eilenberg–MacLane
spaces**: rational vanishing Hurewicz in the range `M ≤ 2k-2`. -/
theorem serreS1OfRangeEMVan (hE3a : Work.Serre.SerreE3a) (h : Work.Serre.RangeEMVanAll) :
    Work.Serre.SerreS1 := by
  intro k hk X _ x₀ hconn M hM hvan m hkm hmM
  have hhom : ∀ i, k ≤ i → i ≤ M → IsZero (Work.Serre.ratH (TopCat.of X) i) := by
    intro i hi1 hi2
    exact (by omega : i - 1 + 1 = i) ▸ hvan (i - 1) (by omega) (by omega)
  exact serreAux_ind hE3a h (M - k) k M rfl hk (by omega) hM X x₀ hconn hhom m hkm hmM

end

end Work.Serre
