import Mathlib
import Submission.Work.MotTDG.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `pfaffStable_unlift`

`Work.MotTDG.PfaffStable.{0, 0, u} D L M` says that the matrix `M` preserves the Pfaffian net
*for every* commutative `L`-algebra `R` lying in the universe `Type u`.  The definition is
universe polymorphic in that test algebra, so a hypothesis at an arbitrary level `u` does not
elaborate as the same term as the statement at level `0`; this file removes the gap by
transporting the polynomial identity through `ULift`.

The mathematics is one line: `kleinP` is a polynomial in `(a, b, z)` with integer coefficients,
hence commutes with ring homomorphisms (`kleinP_map_ringHom`).  Given a test algebra `R` in
`Type 0`, we apply the hypothesis to `ULift R : Type u` and transport the resulting identity
back down along `ULift.up`/`ULift.down`; the coefficient matrix `N` is unchanged, being an
`L`-valued matrix.
-/

namespace Work.MotTDG

/-- `kleinP` is a polynomial with integer coefficients, so every ring homomorphism commutes
with it. -/
private lemma kleinP_map_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a b : R) (z : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP (f a) (f b) (fun i => f (z i)) k = f (Work.MotK.kleinP a b z k) := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, map_add, map_sub, map_mul,
      map_neg, map_pow]

/-- The `ULift.up` specialisation of `kleinP_map_ringHom`. -/
private lemma kleinP_up {R : Type*} [CommRing R] (a b : R) (z : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP (ULift.up a) (ULift.up b) (fun i => ULift.up (z i)) k =
      ULift.up (Work.MotK.kleinP a b z k) :=
  kleinP_map_ringHom (ULift.ringEquiv (R := R)).symm.toRingHom a b z k

/-- Sums of `ULift.up`s of `L`-algebra scalars and of an `L`-algebra element are
`ULift.up`s of the corresponding sums. -/
private lemma ulift_algebraMap_sum_mul {ι : Type*} [Fintype ι] {L : Type*} {R : Type*}
    [CommRing L] [CommRing R] [Algebra L R] (c : ι → L) (z : ι → R) :
    (∑ j, algebraMap L (ULift R) (c j) * ULift.up (z j)) =
      ULift.up (∑ j, algebraMap L R (c j) * z j) := by
  simp only [ULift.algebraMap_eq]
  exact (map_sum (ULift.ringEquiv (R := R)).symm (fun j => algebraMap L R (c j) * z j)
    Finset.univ) ▸ rfl

/-- Sums and products of `ULift.up`s are `ULift.up`s of sums and products. -/
private lemma ulift_sum_up_mul {ι : Type*} [Fintype ι] {R : Type*} [CommRing R] (c z : ι → R) :
    (∑ j, ULift.up (c j) * ULift.up (z j) : ULift R) = ULift.up (∑ j, c j * z j) :=
  (map_sum (ULift.ringEquiv (R := R)).symm (fun j => c j * z j) Finset.univ) ▸ rfl

/-- The `PfaffStable` identity of an `L`-algebra `R` in `Type 0` follows from the same identity
for the lifted algebra `ULift R`. -/
private lemma pfaff_eq_ulift {𝕜 : Type*} [CommRing 𝕜] {L : Type*} [CommRing L] {R : Type*}
    [CommRing R] [Algebra 𝕜 L] [Algebra L R]
    (a b : 𝕜) (M N : Matrix (Fin 5) (Fin 5) L) (z : Fin 5 → R) (k : Fin 5)
    (h : Work.MotK.kleinP (algebraMap L (ULift R) (algebraMap 𝕜 L a))
          (algebraMap L (ULift R) (algebraMap 𝕜 L b))
          (fun i => ∑ j, algebraMap L (ULift R) (M i j) * ULift.up (z j)) k =
        ∑ j, algebraMap L (ULift R) (N k j) *
          Work.MotK.kleinP (algebraMap L (ULift R) (algebraMap 𝕜 L a))
            (algebraMap L (ULift R) (algebraMap 𝕜 L b)) (fun i => ULift.up (z i)) j) :
    Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L a)) (algebraMap L R (algebraMap 𝕜 L b))
        (fun i => ∑ j, algebraMap L R (M i j) * z j) k =
      ∑ j, algebraMap L R (N k j) *
        Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L a))
          (algebraMap L R (algebraMap 𝕜 L b)) z j := by
  have hz : (fun i : Fin 5 => ∑ j, algebraMap L (ULift R) (M i j) * ULift.up (z j)) =
      fun i => ULift.up (∑ j, algebraMap L R (M i j) * z j) := by
    funext i
    exact ulift_algebraMap_sum_mul (fun j => M i j) z
  have h1 : Work.MotK.kleinP (algebraMap L (ULift R) (algebraMap 𝕜 L a))
        (algebraMap L (ULift R) (algebraMap 𝕜 L b))
        (fun i => ∑ j, algebraMap L (ULift R) (M i j) * ULift.up (z j)) k =
      ULift.up (Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L a))
        (algebraMap L R (algebraMap 𝕜 L b))
        (fun i => ∑ j, algebraMap L R (M i j) * z j) k) := by
    rw [ULift.algebraMap_eq, ULift.algebraMap_eq, hz]
    exact kleinP_up _ _ _ _
  have h2 : (∑ j, algebraMap L (ULift R) (N k j) *
          Work.MotK.kleinP (algebraMap L (ULift R) (algebraMap 𝕜 L a))
            (algebraMap L (ULift R) (algebraMap 𝕜 L b)) (fun i => ULift.up (z i)) j) =
      ULift.up (∑ j, algebraMap L R (N k j) *
        Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L a))
          (algebraMap L R (algebraMap 𝕜 L b)) z j) := by
    simp only [ULift.algebraMap_eq, kleinP_up]
    exact ulift_sum_up_mul (fun j => algebraMap L R (N k j))
      (fun j => Work.MotK.kleinP (algebraMap L R (algebraMap 𝕜 L a))
        (algebraMap L R (algebraMap 𝕜 L b)) z j)
  rw [h1, h2] at h
  exact ULift.up_injective h

/-- `PfaffStable` at test-algebra universe `u` implies `PfaffStable` at universe `0`. -/
private theorem pfaffStable_unlift_aux.{u} {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (L : Type) [Field L] [Algebra 𝕜 L] (M : Matrix (Fin 5) (Fin 5) L)
    (hM : Work.MotTDG.PfaffStable.{0, 0, u} D L M) :
    Work.MotTDG.PfaffStable.{0, 0, 0} D L M := by
  obtain ⟨N, hN⟩ := hM
  exact ⟨N, fun R _ _ z k => pfaff_eq_ulift D.a D.b M N z k
    (hN (ULift.{u, 0} R) (fun i => ULift.up (z i)) k)⟩

theorem pfaffStable_unlift {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (L : Type) [Field L] [Algebra 𝕜 L] (M : Matrix (Fin 5) (Fin 5) L)
    (hM : Work.MotTDG.PfaffStable D L M) : Work.MotTDG.PfaffStable.{0, 0, 0} D L M := by
  exact pfaffStable_unlift_aux D L M hM

end Work.MotTDG
