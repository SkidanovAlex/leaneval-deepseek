import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.pair_les

/-!
# Consequences of the long exact sequence of a pair

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  Three exactness consequences of
`Work.RatHurewicz.pair_les`, the shape in which the long exact sequence of a pair is used in the
classical induction of the Hurewicz statements (compare connectivities, transport vanishing, produce
surjectivity of the inclusion on homotopy groups):

* `relPi_subsingleton_of_subsingleton` — `π_{k+3}(X) = π_{k+2}(A) = 0` ⟹ `π_{k+2}(X,A) = 0`;
* `pi_subsingleton_of_relPi_subsingleton` — `π_{k+2}(A) = π_{k+2}(X,A) = 0` ⟹ `π_{k+2}(X) = 0`;
* `piMap_surjective_of_relPi_subsingleton` — `π_{k+2}(X,A) = 0` ⟹ `π_{k+2}(A) → π_{k+2}(X)`
  surjective.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **An exactness consequence of the pair sequence.**  If `i : C(A,X)`, `k ≥ 1`, `π_{k+3}(X) = 0`
and `π_{k+2}(A) = 0`, then the relative group `π_{k+2}(X,A)` (`= RelHomotopyGroup i a₀ (k+2)`, the
homotopy group of the homotopy fibre of `i`) is trivial. -/
theorem relPi_subsingleton_of_subsingleton {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) (k : ℕ) (hk : 1 ≤ k)
    (hX : Subsingleton (HomotopyGroup (Fin (k + 3)) X (i a₀)))
    (hA : Subsingleton (HomotopyGroup (Fin (k + 2)) A a₀)) :
    Subsingleton (RelHomotopyGroup i a₀ (k + 2)) := by
  obtain ⟨del, d, h1, _h2, _h3, _h4⟩ := pair_les i a₀ k hk
  have key : ∀ x : RelHomotopyGroup i a₀ (k + 2), x = 1 := by
    intro x
    have hb : (Work.StemsB.πmap (homotopyFibreFst i a₀) (k + 1)
        (homotopyFibreBasepoint i a₀)) x = 1 :=
      hA.elim _ (1 : HomotopyGroup (Fin (k + 2)) A
        (homotopyFibreFst i a₀ (homotopyFibreBasepoint i a₀)))
    obtain ⟨u, hu⟩ := (h1 x).mp hb
    rw [← hu, hX.elim u (1 : HomotopyGroup (Fin (k + 3)) X (i a₀)), map_one]
  exact ⟨fun x y => by rw [key x, key y]⟩

/-- **An exactness consequence of the pair sequence.**  If `i : C(A,X)`, `k ≥ 1`, `π_{k+2}(A) = 0`
and the relative group `π_{k+2}(X,A) = RelHomotopyGroup i a₀ (k+1)` is trivial, then `π_{k+2}(X) = 0`.
-/
theorem pi_subsingleton_of_relPi_subsingleton {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) (k : ℕ) (hk : 1 ≤ k)
    (hA : Subsingleton (HomotopyGroup (Fin (k + 2)) A a₀))
    (hrel : Subsingleton (RelHomotopyGroup i a₀ (k + 1))) :
    Subsingleton (HomotopyGroup (Fin (k + 2)) X (i a₀)) := by
  obtain ⟨del, d, _h1, _h2, h3, _h4⟩ := pair_les i a₀ k hk
  have key : ∀ z : HomotopyGroup (Fin (k + 2)) X (i a₀), z = 1 := by
    intro z
    have hd : d z = 1 := hrel.elim _ (1 : RelHomotopyGroup i a₀ (k + 1))
    obtain ⟨a, ha⟩ := (h3 z).mp hd
    have ha1 : a = 1 := hA.elim _ (1 : HomotopyGroup (Fin (k + 2)) A a₀)
    rw [← ha, ha1, map_one]
  exact ⟨fun x y => by rw [key x, key y]⟩

/-- **An exactness consequence of the pair sequence.**  If `i : C(A,X)`, `k ≥ 1` and the relative
group `π_{k+2}(X,A) = RelHomotopyGroup i a₀ (k+1)` is trivial, then the map
`π_{k+2}(A) → π_{k+2}(X)` induced by `i` is surjective. -/
theorem piMap_surjective_of_relPi_subsingleton {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) (k : ℕ) (hk : 1 ≤ k)
    (hrel : Subsingleton (RelHomotopyGroup i a₀ (k + 1))) :
    Function.Surjective (Work.StemsB.πmap i (k + 1) a₀) := by
  obtain ⟨del, d, _h1, _h2, h3, _h4⟩ := pair_les i a₀ k hk
  intro x
  exact (h3 x).mp (hrel.elim _ _)

/-- **An exactness consequence of the pair sequence.**  If `i : C(A,X)`, `k ≥ 1` and the relative
group `π_{k+3}(X,A) = RelHomotopyGroup i a₀ (k+2)` is trivial, then the map
`π_{k+2}(A) → π_{k+2}(X)` induced by `i` is injective: an element of the kernel lies in the image of
the map out of the homotopy fibre, whose source is that trivial relative group.  (Note the shift
with respect to `piMap_surjective_of_relPi_subsingleton`, which needs the relative group one degree
lower: `πmap i (k+1)` is the map on `π_{k+2}`, its surjectivity comes from `π_{k+2}(X,A) = 0` and
its injectivity from `π_{k+3}(X,A) = 0`.) -/
theorem piMap_injective_of_relPi_subsingleton {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) (k : ℕ) (hk : 1 ≤ k)
    (hrel : Subsingleton (RelHomotopyGroup i a₀ (k + 2))) :
    Function.Injective (Work.StemsB.πmap i (k + 1) a₀) := by
  obtain ⟨del, d, _h1, h2, _h3, _h4⟩ := pair_les i a₀ k hk
  intro x y hxy
  have h : x * y⁻¹ = 1 := by
    have hker : Work.StemsB.πmap i (k + 1) a₀ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    obtain ⟨z, hz⟩ := (h2 (x * y⁻¹)).mp hker
    rw [← hz, hrel.elim z 1, map_one]
    rfl
  exact mul_inv_eq_one.mp h

end

end Work.RatHurewicz
