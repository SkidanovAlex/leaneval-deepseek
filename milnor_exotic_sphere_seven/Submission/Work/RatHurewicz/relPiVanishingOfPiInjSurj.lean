import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Serre.rwRelPiVanishingOfPiBijective
import Submission.Work.Serre.piOneHomotopyFibreSubsingleton
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of the relative homotopy groups from injectivity in degree `J` and surjectivity in
degree `J + 1`

`RelHomotopyGroup (setIncl A) a J` is the `J`-th homotopy group of the homotopy fibre of the
inclusion `A ↪ W`, equivalently the classical relative homotopy group `π_{J+1}(W,A,a)`.

The statement proved here is the half of the (exactness part of the) long exact sequence of the
pair that does *not* need the hypotheses in all degrees: if the inclusion induces an **injection**
on `π_J` and a **surjection** on `π_{J+1}`, then `π_{J+1}(W,A,a) = 0`.  Indeed, in the exact
sequence

`π_{J+1}(A) → π_{J+1}(W) → π_J(F) → π_J(A) → π_J(W)`

(with `F` the homotopy fibre) every `x ∈ π_J(F)` has `p_* x` in the kernel of `π_J(A) → π_J(W)`,
because `i ∘ p` is null-homotopic; injectivity makes `p_* x = 1`, so `x` is in the image of the
connecting map `π_{J+1}(W) → π_J(F)`; surjectivity on `π_{J+1}` and exactness at `π_{J+1}(W)` make
that image trivial.

The low degrees are treated separately: `J = 0` is path connectedness of the homotopy fibre
(`Work.Serre.pathConnectedSpace_homotopyFibre`) and `J = 1` is
`Work.Serre.piOneHomotopyFibreSubsingleton_of_surjective`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.RatHurewicz

theorem relPiVanishingOfPiInjSurj {W : Type} [TopologicalSpace W] {A : Set W}
    (J : ℕ) (a : ↥A)
    (hinj : Function.Injective (Work.Serre.piMapN (Work.RatHurewicz.setIncl A) J a))
    (hsurj : Function.Surjective (Work.Serre.piMapN (Work.RatHurewicz.setIncl A) (J + 1) a)) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a J) := by
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · -- `J = 0`: the homotopy fibre is path connected.
    subst hJ0
    have hzm : Function.Injective (Work.Serre.zmkMap (Work.RatHurewicz.setIncl A)) :=
      Work.Serre.injective_zmkMap_of_pi0 (Work.RatHurewicz.setIncl A) a hinj
    have h0 : ∀ a' : ↥A, Nonempty (Path (Work.RatHurewicz.setIncl A a)
        (Work.RatHurewicz.setIncl A a')) → Nonempty (Path a a') := by
      intro a' h
      obtain ⟨γ⟩ := h
      have hz : Work.Serre.zmkMap (Work.RatHurewicz.setIncl A) (ZerothHomotopy.mk a)
          = Work.Serre.zmkMap (Work.RatHurewicz.setIncl A) (ZerothHomotopy.mk a') := by
        rw [Work.Serre.zmkMap_mk, Work.Serre.zmkMap_mk]
        exact ZerothHomotopy.sound γ
      exact Quotient.exact (hzm hz)
    have hpc : PathConnectedSpace (Work.RatHurewicz.homotopyFibre
        (Work.RatHurewicz.setIncl A) a) :=
      Work.Serre.pathConnectedSpace_homotopyFibre (Work.RatHurewicz.setIncl A) a h0 hsurj
    have hZ : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre
        (Work.RatHurewicz.setIncl A) a)) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
    exact ⟨fun x y => (HomotopyGroup.pi0EquivZerothHomotopy
      (x := Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a)).injective
        (hZ.elim _ _)⟩
  · rcases Nat.eq_or_lt_of_le (Nat.succ_le_iff.mpr hJpos) with hJ1 | hJ2
    · -- `J = 1`
      subst hJ1
      exact Work.Serre.piOneHomotopyFibreSubsingleton_of_surjective
        (Work.RatHurewicz.setIncl A) a hinj hsurj
    · -- `J ≥ 2`: the long exact sequence of the pair.
      obtain ⟨k, hk, hkJ⟩ : ∃ k : ℕ, 1 ≤ k ∧ J = k + 1 := ⟨J - 1, by omega, by omega⟩
      subst hkJ
      obtain ⟨del, d, h1, h2, h3, h4⟩ :=
        Work.RatHurewicz.pair_les (Work.RatHurewicz.setIncl A) a k hk
      -- `i ∘ p` is null-homotopic, so `p_*` lands in the kernel of `π_J(i)`.
      have hpx : ∀ x : Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a (k + 1),
          (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a) k
            (Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a)) x = 1 :=
        fun x => Work.Serre.πmap_homotopyFibreFst_eq_one (A := A) a k hinj x
      have hsurj' : Function.Surjective
          (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) (k + 1) a) := hsurj
      have key : ∀ x : Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a (k + 1),
          x = 1 := fun x => by
        -- `x` lies in the image of the connecting map `π_{k+2}(W) → π_{k+1}(F)`
        obtain ⟨y, hy⟩ := (h4 x).mp (hpx x)
        -- `y` lies in the image of `π_{k+2}(i)`, hence in the kernel of the connecting map
        obtain ⟨z, hz⟩ := hsurj' y
        have hz1 : d y = 1 := (h3 y).mpr ⟨z, hz⟩
        rw [← hy, hz1]
      exact ⟨fun x y => (key x).trans (key y).symm⟩

end Work.RatHurewicz
