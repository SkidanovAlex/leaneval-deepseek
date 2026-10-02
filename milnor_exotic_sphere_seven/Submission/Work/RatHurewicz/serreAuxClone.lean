import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Serre.RangeEMVanDefs
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Serre.piMap_fibreIncl_surjective_pi1
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.RatHurewicz.PairShiftBijective
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.RatHurewicz.homotopyFibreMap_exists

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A clash-free copy of the `serreAux_*` toolkit

`Submission/Work/Serre/serreS1OfRangeEMVan.lean` contains, besides its target, a toolkit of small
lemmas about the long exact sequence of the pair `(X, A)` expressed through
`Work.RatHurewicz.RelHomotopyGroup`.  `Submission/Work/RatHurewicz/torsionVanishing.lean` uses them,
but the *module* cannot be imported next to `Submission/Work/RatHurewicz/rangeEMVanOne_of_finite.lean`:
`serreS1OfRangeEMVan.lean` imports `Work.Serre.Consumers` / `Work.RatHurewicz.Consumers`, whose
closure contains `Submission/Work/RatHurewicz/PsiKillsAux.lean`, and that file together with
`Submission/Work/RatHurewicz/pushModelUniform.lean` (in the closure of `rangeEMVanOne_of_finite`)
declares `Work.RatHurewicz.piece` twice.  See `Submission/Work/RatHurewicz/CLASH_REPORT.md`.

The present module contains verbatim copies of the lemmas needed, with clash-free imports and in the
namespace `Work.RatHurewicz` (so that no name clashes with the originals either).  It is a stopgap
until the duplicate declaration is removed; the statements are the originals.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- `Subsingleton` statements are transported between equal indices. -/
theorem serreAux_subsingleton_homotopyGroup_of_index_eq {X : Type} [TopologicalSpace X] {x : X}
    {a b : ℕ} (h : a = b) (hm : Subsingleton (HomotopyGroup (Fin a) X x)) :
    Subsingleton (HomotopyGroup (Fin b) X x) := h ▸ hm

/-- Torsion statements are transported between equal indices. -/
theorem serreAux_piTorsion_of_index_eq {X : Type} [TopologicalSpace X] (x : X) {a b : ℕ}
    (h : a = b) (hm : Work.Serre.PiTorsion X x a) : Work.Serre.PiTorsion X x b := h ▸ hm

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

end

end Work.RatHurewicz
