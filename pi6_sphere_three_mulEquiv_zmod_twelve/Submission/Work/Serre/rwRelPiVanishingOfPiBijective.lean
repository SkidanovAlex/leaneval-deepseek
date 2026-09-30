import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre
import Submission.Work.Serre.piOneHomotopyFibreSubsingleton
import Submission.Work.Serre.attachIncl_pi0_bijective
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.RatHurewicz.PairLESCrux
import Submission.Work.RatHurewicz.PairShiftBijective
import Submission.Work.StemsB.LESExact
import Submission.Work.RatHurewicz.RelPiPathDefs

/-!
# Vanishing of the relative homotopy groups of `A ↪ W` when the inclusion is a `π`-isomorphism

The main result is `Work.Serre.rwRelPiVanishingOfPiBijective`: if the inclusion `A ↪ W` induces a
bijection on `π_q` at every base point for every `q ≤ N + 1`, then the relative homotopy groups
`RelHomotopyGroup (setIncl A) a k = π_k(fibre of A ↪ W at a)` vanish for `k ≤ N` at every base
point `a : ↥A`.

The proof is the long exact sequence of the pair (the homotopy fibre `F = homotopyFibre (setIncl A) a`
of the inclusion, `p : F → A` its projection, which is a Serre fibration):

* `k = 0`: since `π_0(A) → π_0(W)` is injective (the inclusion never identifies two points of `A`
  up to a path of `W`) and `π_1(A) → π_1(W)` is surjective, the fibre `F` is path connected, hence
  `π_0(F) = 0`.  The geometric form of `π_0`-injectivity is obtained from the injectivity of the
  induced map on `HomotopyGroup (Fin 0)`, via the identification with `ZerothHomotopy`.
* `k = 1`: `Work.Serre.piOneHomotopyFibreSubsingleton_of_surjective`: `π_1(i)` injective and `π_2(i)`
  surjective make `π_1(F) = 0`.
* `k ≥ 2`: in the long exact sequence of the fibration `F → A`, the composite
  `i ∘ p : F → W` is *null-homotopic* (the path attached to a point of the fibre provides a homotopy
  to the constant map at `i a`, relative to the base point), so `π_k(F) → π_k(A)` is the zero map;
  exactness of the pair sequence at `π_k(F)` turns `π_k(F)` into the image of the connecting map
  `π_{k+1}(W) → π_k(F)`, and that map is zero because `π_{k+1}(A) → π_{k+1}(W)` is onto and the
  two maps are adjacent in the sequence.

The two auxiliary results `πmap_comp_homotopyFibreFst_eq_one` and `injective_zmkMap_of_pi0` below
are the new ingredients; everything else is imported from the RATHUREWICZ and SERRE chapters.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The path attached to a point of the homotopy fibre, at the base point -/

/-- At the base point of the homotopy fibre the attached path is the constant path. -/
theorem fibreCM_basepoint {Y : Type} [TopologicalSpace Y] {A : Set Y} (a : ↥A) :
    Work.RatHurewicz.fibreCM (Work.RatHurewicz.homotopyFibreBasepoint
        (Work.RatHurewicz.setIncl A) a) =
      ContinuousMap.const I (Work.RatHurewicz.setIncl A a) := rfl

/-! ## `i ∘ p` is null-homotopic -/

/-- **The composite `(A ↪ W) ∘ (projection of the homotopy fibre)` is null-homotopic**: the path
attached to a point of the homotopy fibre is a homotopy, relative to the base point, from the
constant map at `i a₀` to `i ∘ p`.  Hence the induced map on every homotopy group is trivial. -/
theorem πmap_comp_homotopyFibreFst_eq_one {Y : Type} [TopologicalSpace Y] {A : Set Y}
    (a₀ : ↥A) (n : ℕ)
    (x : HomotopyGroup (Fin (n + 1))
      (Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl A) a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀)) :
    Work.StemsB.πmap ((Work.RatHurewicz.setIncl A).comp
        (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀)) n
      (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀) x = 1 := by
  induction x using Quotient.inductionOn with
  | h γ =>
    rw [Work.StemsB.πmap_apply_mk]
    refine (Quotient.sound ?_).trans HomotopyGroup.one_def.symm
    have H : ContinuousMap.HomotopyRel
        (GenLoop.const : Ω^ (Fin (n + 1)) Y ((Work.RatHurewicz.setIncl A).comp
          (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀))).1
        (Work.StemsB.genLoopMap ((Work.RatHurewicz.setIncl A).comp
          (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀)) (n + 1) γ).1
        (Cube.boundary (Fin (n + 1))) :=
      { toFun := fun q => Work.RatHurewicz.fibreCM (γ.1 q.2) q.1
        continuous_toFun := by
          exact Work.RatHurewicz.continuous_apply_comp
            ((Work.RatHurewicz.fibreCMFamily a₀).continuous.comp
              (γ.1.continuous.comp continuous_snd)) continuous_fst
        map_zero_left := fun u => by
          show Work.RatHurewicz.fibreCM (γ.1 u) 0
            = Work.RatHurewicz.setIncl A
              (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀
                (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀))
          rw [Work.RatHurewicz.fibreCM_zero]
          rfl
        map_one_left := fun u => by
          show Work.RatHurewicz.fibreCM (γ.1 u) 1
            = Work.RatHurewicz.setIncl A
              (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀ (γ.1 u))
          rw [Work.RatHurewicz.fibreCM_one]
          rfl
        prop' := fun t u hu => by
          show Work.RatHurewicz.fibreCM (γ.1 u) t
            = Work.RatHurewicz.setIncl A
              (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀
                (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀))
          rw [show γ.1 u = Work.RatHurewicz.homotopyFibreBasepoint
              (Work.RatHurewicz.setIncl A) a₀ from γ.2 u hu]
          show (ContinuousMap.const I (Work.RatHurewicz.setIncl A a₀)) t
            = Work.RatHurewicz.setIncl A
              (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀
                (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀))
          rfl }
    exact ⟨H.symm⟩

/-- **The projection of the homotopy fibre kills `π_{n+1}`** when the inclusion is injective on
`π_{n+1}`: the composite with the inclusion is null-homotopic. -/
theorem πmap_homotopyFibreFst_eq_one {Y : Type} [TopologicalSpace Y] {A : Set Y} (a₀ : ↥A)
    (n : ℕ) (hinj : Function.Injective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) n a₀))
    (x : HomotopyGroup (Fin (n + 1))
      (Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl A) a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀)) :
    Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀) n
      (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀) x = 1 := by
  have h0 := πmap_comp_homotopyFibreFst_eq_one (A := A) a₀ n x
  have h1 := Work.StemsB.πmap_comp_apply
    (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀)
    (Work.RatHurewicz.setIncl A) n
    (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀) x
  rw [h1] at h0
  exact hinj (h0.trans (map_one (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) n a₀)).symm)

/-! ## `π₀`-injectivity of the inclusion, in geometric form -/

/-- If the induced map on `π₀` at `x` is injective, then the induced map on path components is
injective.  (The naturality of `HomotopyGroup.pi0EquivZerothHomotopy` conjugates the two maps.) -/
theorem injective_zmkMap_of_pi0 {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X)
    (h : Function.Injective (HomotopyGroup.map (N := Fin 0) f (x := x))) :
    Function.Injective (zmkMap f) := by
  intro w₁ w₂ hw
  have nat : ∀ u : HomotopyGroup (Fin 0) X x,
      HomotopyGroup.pi0EquivZerothHomotopy (HomotopyGroup.map f u) =
        zmkMap f (HomotopyGroup.pi0EquivZerothHomotopy u) :=
    fun u => pi0EquivZerothHomotopy_map f x u
  have key : ∀ w : ZerothHomotopy X,
      HomotopyGroup.pi0EquivZerothHomotopy
        (HomotopyGroup.map f
          ((HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm w)) = zmkMap f w := by
    intro w
    rw [nat, Equiv.apply_symm_apply]
  have h2 : HomotopyGroup.pi0EquivZerothHomotopy (x := f x)
        (HomotopyGroup.map f
          ((HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm w₁))
      = HomotopyGroup.pi0EquivZerothHomotopy (x := f x)
        (HomotopyGroup.map f
          ((HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm w₂)) := by
    rw [key w₁, key w₂, hw]
  have h3 := (HomotopyGroup.pi0EquivZerothHomotopy (x := f x)).injective h2
  have h4 := h h3
  have h5 := congrArg (HomotopyGroup.pi0EquivZerothHomotopy (x := x)) h4
  simpa using h5

/-! ## The target theorem -/

/-- If the inclusion `A ↪ W` is a bijection on `π_q` at every base point for all `q ≤ N + 1`
(unshifted indexing: `q = 0` is `π₀`), and every point of `W` is joined by a path to `A`, then the
relative homotopy groups `RelHomotopyGroup (setIncl A) a k = π_k(fibre of A ↪ W at a)` are trivial
for `k ≤ N` at every base point `a : ↥A`. -/
theorem rwRelPiVanishingOfPiBijective {W : Type} [TopologicalSpace W] {A : Set W} (N : ℕ)
    (hconn0 : ∀ w : W, ∃ a : ↥A, Nonempty (Path w a))
    (hpi : ∀ (q : ℕ), q ≤ N + 1 → ∀ a : ↥A,
      Function.Bijective (Work.Serre.piMapN (Work.RatHurewicz.setIncl A) q a)) :
    ∀ a : ↥A, ∀ k : ℕ, k ≤ N →
      Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a k) := by
  intro a k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the fibre is path connected
    subst hk0
    have h0 : ∀ a' : ↥A, Nonempty (Path (Work.RatHurewicz.setIncl A a)
        (Work.RatHurewicz.setIncl A a')) → Nonempty (Path a a') := by
      intro a' h
      have hzm : Function.Injective (zmkMap (Work.RatHurewicz.setIncl A)) :=
        injective_zmkMap_of_pi0 (Work.RatHurewicz.setIncl A) a (hpi 0 (by omega) a).1
      obtain ⟨γ⟩ := h
      have hz : zmkMap (Work.RatHurewicz.setIncl A) (ZerothHomotopy.mk a)
          = zmkMap (Work.RatHurewicz.setIncl A) (ZerothHomotopy.mk a') := by
        rw [zmkMap_mk, zmkMap_mk]
        exact ZerothHomotopy.sound γ
      exact Quotient.exact (hzm hz)
    have hpc : PathConnectedSpace (Work.RatHurewicz.homotopyFibre
        (Work.RatHurewicz.setIncl A) a) :=
      Work.Serre.pathConnectedSpace_homotopyFibre (Work.RatHurewicz.setIncl A) a h0
        (hpi 1 (by omega) a).2
    have hZ : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre
        (Work.RatHurewicz.setIncl A) a)) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
    exact ⟨fun x y => (HomotopyGroup.pi0EquivZerothHomotopy
      (x := Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a)).injective
        (hZ.elim _ _)⟩
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_iff.mpr hkpos) with hk1 | hk2
    · -- `k = 1`
      exact hk1 ▸ Work.Serre.piOneHomotopyFibreSubsingleton_of_surjective
        (Work.RatHurewicz.setIncl A) a (hpi 1 (by omega) a).1 (hpi 2 (by omega) a).2
    · -- `k ≥ 2`: the pair sequence, and the null-homotopy of `i ∘ p`
      obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 + 1 := ⟨k - 2, by omega⟩
      obtain ⟨_, d, _, _, h3, h4⟩ :=
        Work.RatHurewicz.pair_les (Work.RatHurewicz.setIncl A) a (j + 1) (by omega)
      have hinj : Function.Injective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) (j + 1) a) :=
        (hpi (j + 2) (by omega) a).1
      have hsurj : Function.Surjective
          (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) (j + 1 + 1) a) :=
        (hpi (j + 3) (by omega) a).2
      have hg : ∀ y : Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a
          (j + 1 + 1),
          Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a)
            (j + 1)
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a) y = 1 :=
        fun y => πmap_homotopyFibreFst_eq_one (A := A) a (j + 1) hinj y
      have hd : ∀ y, d y = 1 := by
        intro y
        obtain ⟨x, hx⟩ := hsurj y
        exact (h3 y).mpr ⟨x, hx⟩
      refine ⟨fun y z => ?_⟩
      have hy : y = 1 := by
        obtain ⟨w, hw⟩ := (h4 y).mp (hg y)
        rw [← hw, hd w]
      have hz : z = 1 := by
        obtain ⟨w, hw⟩ := (h4 z).mp (hg z)
        rw [← hw, hd w]
      rw [hy, hz]

end

end Work.Serre
