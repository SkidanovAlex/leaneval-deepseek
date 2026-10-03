import Mathlib
import Submission.Work.ORLyndon.LyndonIndependenceDefs
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.ORLyndon.LyndonConjDefs
import Submission.Work.ORLyndon.relatorVec_conj

/-!
# Conjugation invariance of the Cohen--Lyndon independence statement

Let `X` be a type, `K` a field and `r u c : F(X)`.  The Cohen--Lyndon independence statement
`Work.ORLyndon.LyndonIndependence K r u` (see `LyndonIndependenceDefs.lean`) is invariant under
conjugating both `r` and `u` by `c`:

`LyndonIndependence K r u → LyndonIndependence K (c r c⁻¹) (c u c⁻¹)`.

The two presentations `⟨X | r⟩` and `⟨X | c r c⁻¹⟩` are isomorphic along
`Work.ORLyndon.conjHom r c : ⟨X | r⟩ →* ⟨X | c r c⁻¹⟩` (induced by `w ↦ c w c⁻¹`, with inverse
`conjHomInv r c`), and the two ingredients that transport are

* the Fox derivative vector, `Work.ORLyndon.relatorVec_conj` (proved in `relatorVec_conj.lean`):
  the relation vector of the conjugate presentation is the image of `relatorVec K r` under
  `conjHom r c`, *twisted* on the right by the image of `c` itself:
  `relatorVec K (c r c⁻¹) x = Φ (relatorVec K r x) * of (ρ c)` with `Φ` the algebra map induced by
  `conjHom r c`;
* the transport of a linear combination along the inverse isomorphism `conjHomInv r c`, which is
  `Work.ORLyndon.conj_sum_eval`.

Because the twist by `of (ρ c)` is right multiplication by a unit, it can be cancelled, and the
statement follows formally.

## Main results

* `Work.ORLyndon.conj_sum_eval` -- the transport of a linear combination of the Fox vectors.
* `Work.ORLyndon.lyndonIndependence_conj` -- conjugation invariance of `LyndonIndependence`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- Right multiplication by the image in `K[Y]` of a group element `m` is injective (it is the
multiplication by a unit). -/
theorem mul_of_eq_zero {Y B : Type*} [Group Y] [Semiring B] (m : Y)
    {z : MonoidAlgebra B Y} (h : z * MonoidAlgebra.of B Y m = 0) : z = 0 := by
  have hm : MonoidAlgebra.of B Y m * MonoidAlgebra.of B Y m⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  calc z = z * 1 := (mul_one z).symm
    _ = z * (MonoidAlgebra.of B Y m * MonoidAlgebra.of B Y m⁻¹) := by rw [hm]
    _ = (z * MonoidAlgebra.of B Y m) * MonoidAlgebra.of B Y m⁻¹ := by rw [mul_assoc]
    _ = 0 := by rw [h, zero_mul]

/-- **Transport of a linear combination of Fox vectors along `conjHomInv`.**  A vanishing relation
between the vectors `of (g i) • relatorVec K (c r c⁻¹)` (in the conjugate presentation) implies the
same vanishing relation between the vectors `of (conjHomInv r c (g i)) • relatorVec K r` (in the
original presentation).

Indeed, by `Work.ORLyndon.relatorVec_conj` each vector of the conjugate presentation is
`Φ (relatorVec K r x) * of (ρ c)`, and the second factor is a unit, so it can be cancelled; applying
the algebra map `Ψ` induced by `conjHomInv r c` (using `Ψ ∘ Φ = id` and the compatibility of `Ψ`
with the algebra structures) then gives the claim. -/
theorem conj_sum_eval {X : Type*} [DecidableEq X] {K : Type*} [Field K] {ι : Type*} [Fintype ι]
    (r c : FreeGroup X) (g : ι → OneRelatorGroup (c * r * c⁻¹)) (cc : ι → K) (x : X)
    (h : (∑ i, cc i • ((MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (g i))
          • relatorVec K (c * r * c⁻¹))) x = 0) :
    (∑ i, cc i • ((MonoidAlgebra.of K (OneRelatorGroup r) (conjHomInv r c (g i)))
          • relatorVec K r)) x = 0 := by
  classical
  -- (1) evaluate the identity and substitute the Fox derivative of the conjugate
  have h1 : (∑ i, cc i • (MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (g i)
      * (MonoidAlgebra.mapDomainRingHom K (conjHom r c) (relatorVec K r x)
          * MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹))
              (presentRho (c * r * c⁻¹) c)))) = 0 := by
    simpa [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, relatorVec_conj r c x] using h
  -- (2) factor the right factor out of the sum
  have hsum_eq : (∑ i, cc i • (MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (g i)
        * MonoidAlgebra.mapDomainRingHom K (conjHom r c) (relatorVec K r x)))
          * MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹))
              (presentRho (c * r * c⁻¹) c)
      = ∑ i, cc i • (MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (g i)
        * (MonoidAlgebra.mapDomainRingHom K (conjHom r c) (relatorVec K r x)
            * MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹))
                (presentRho (c * r * c⁻¹) c))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, Algebra.smul_def]
    noncomm_ring
  have hX : (∑ i, cc i • (MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (g i)
        * MonoidAlgebra.mapDomainRingHom K (conjHom r c) (relatorVec K r x)))
          * MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹))
              (presentRho (c * r * c⁻¹) c) = 0 := by
    rw [hsum_eq]
    exact h1
  -- (3) cancel the right factor, which is a unit
  have h2 : (∑ i, cc i • (MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (g i)
        * MonoidAlgebra.mapDomainRingHom K (conjHom r c) (relatorVec K r x))) = 0 :=
    mul_of_eq_zero (presentRho (c * r * c⁻¹) c) hX
  -- (4) apply the inverse algebra map
  have hcancel : ∀ z : MonoidAlgebra K (OneRelatorGroup r),
      MonoidAlgebra.mapDomainRingHom K (conjHomInv r c)
        (MonoidAlgebra.mapDomainRingHom K (conjHom r c) z) = z := by
    intro z
    have hcomp : (MonoidAlgebra.mapDomainRingHom K (conjHomInv r c)).comp
        (MonoidAlgebra.mapDomainRingHom K (conjHom r c)) = RingHom.id _ := by
      have hc : (conjHomInv r c).comp (conjHom r c) = MonoidHom.id _ :=
        MonoidHom.ext (fun y => conjHomInv_conjHom r c y)
      rw [← MonoidAlgebra.mapDomainRingHom_comp, hc, MonoidAlgebra.mapDomainRingHom_id]
    exact DFunLike.congr_fun hcomp z
  have hof : ∀ y : OneRelatorGroup (c * r * c⁻¹),
      MonoidAlgebra.mapDomainRingHom K (conjHomInv r c)
        (MonoidAlgebra.of K _ y) = MonoidAlgebra.of K _ (conjHomInv r c y) := by
    intro y
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.of_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.of_apply]
  have halg : ∀ a : K, MonoidAlgebra.mapDomainRingHom K (conjHomInv r c)
      (algebraMap K (MonoidAlgebra K (OneRelatorGroup (c * r * c⁻¹))) a) =
      algebraMap K (MonoidAlgebra K (OneRelatorGroup r)) a :=
    fun a => DFunLike.congr_fun
      (MonoidAlgebra.mapDomainRingHom_comp_algebraMap (A := K) (conjHomInv r c)) a
  have hpt : ∀ i, MonoidAlgebra.mapDomainRingHom K (conjHomInv r c)
      (cc i • (MonoidAlgebra.of K (OneRelatorGroup (c * r * c⁻¹)) (g i)
        * MonoidAlgebra.mapDomainRingHom K (conjHom r c) (relatorVec K r x)))
      = cc i • (MonoidAlgebra.of K (OneRelatorGroup r) (conjHomInv r c (g i))
          * relatorVec K r x) := by
    intro i
    rw [Algebra.smul_def]
    simp only [map_mul]
    rw [halg, hof, hcancel (relatorVec K r x), ← Algebra.smul_def]
  have h4 : (∑ i, cc i • (MonoidAlgebra.of K (OneRelatorGroup r) (conjHomInv r c (g i))
      * relatorVec K r x)) = 0 := by
    have hh := congrArg (MonoidAlgebra.mapDomainRingHom K (conjHomInv r c)) h2
    rw [map_sum, map_zero] at hh
    rw [Finset.sum_congr rfl (fun i _ => hpt i)] at hh
    exact hh
  -- (5) put the goal into the shape of the hypothesis
  have hgoal : (∑ i, cc i • ((MonoidAlgebra.of K (OneRelatorGroup r) (conjHomInv r c (g i)))
        • relatorVec K r)) x
      = ∑ i, cc i • (MonoidAlgebra.of K (OneRelatorGroup r) (conjHomInv r c (g i))
          * relatorVec K r x) := by
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [hgoal, h4]

/-- **The Cohen--Lyndon independence is invariant under conjugation of the relator and the root.**
If the vectors `g • (∂r/∂x)_x` attached to the elements of `⟨X | r⟩` lying in pairwise distinct
`⟨presentRho r u⟩`-cosets are `K`-linearly independent, then the same holds for the conjugate
presentation `⟨X | c r c⁻¹⟩` with the conjugate root `c u c⁻¹`.

The two presentations are identified along `Work.ORLyndon.conjHom r c`, which carries
`presentRho r u` to `presentRho (c r c⁻¹) (c u c⁻¹)` and carries `relatorVec K r` to
`relatorVec K (c r c⁻¹)` up to a right factor that is a unit (`Work.ORLyndon.relatorVec_conj`);
`Work.ORLyndon.conj_sum_eval` transports a linear relation along the inverse identification, and
`Work.ORLyndon.conjHomInv_conjHom`/`conjHom_conjHomInv` preserve the coset condition. -/
theorem lyndonIndependence_conj {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r u c : FreeGroup X) :
    Work.ORLyndon.LyndonIndependence K r u →
    Work.ORLyndon.LyndonIndependence K (c * r * c⁻¹) (c * u * c⁻¹) := by
  intro hind
  intro ι inst g cc hcos hsum
  -- evaluate the relation at every generator and transport it back along `conjHomInv`
  have hpoint : ∀ x : X,
      (∑ i, cc i • ((MonoidAlgebra.of K (OneRelatorGroup r) (conjHomInv r c (g i)))
        • relatorVec K r)) x = 0 := by
    intro x
    exact conj_sum_eval r c g cc x
      (congrArg (fun v : X →₀ MonoidAlgebra K (OneRelatorGroup (c * r * c⁻¹)) => v x) hsum)
  have hsum' : (∑ i, cc i • ((MonoidAlgebra.of K (OneRelatorGroup r) (conjHomInv r c (g i)))
        • relatorVec K r)) = 0 := by
    apply Finsupp.ext
    intro x
    rw [Finsupp.zero_apply]
    exact hpoint x
  -- the coset condition is preserved because `conjHom` and `conjHomInv` are mutually inverse
  have hcos' : ∀ i j, i ≠ j → ∀ k : ℤ,
      conjHomInv r c (g i) ≠ conjHomInv r c (g j) * (presentRho r u) ^ k := by
    intro i j hij k hconj
    refine hcos i j hij k ?_
    have h2 := congrArg (conjHom r c) hconj
    rw [map_mul, map_zpow, conjHom_conjHomInv r c (g j), conjHom_mk r c u,
      conjHom_conjHomInv r c (g i)] at h2
    exact h2
  intro i
  exact hind ι (fun j => conjHomInv r c (g j)) cc hcos' hsum' i

end Work.ORLyndon
