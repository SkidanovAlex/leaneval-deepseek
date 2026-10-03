import Mathlib
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.ORLyndon.exists_levelHom_of_cohom_eq_one
import Submission.Work.ORLyndon.rootVec_letterPow_mul_letterPow

/-!
# `annAt` for the torus-family root `a ^ p * b ^ q` at the letter `a`

The concrete instance of the **leading-level transfer** for the two-letter root `u = a ^ p * b ^ q`
(`p, q ≥ 1`) of the torus family, at the letter `a`:

`Work.ORLyndon.annAt K (u ^ l) u {a}`  for every `l : ℕ`.

The weight is the character of the torus knot group, `c a = q`, `c b = -p`; it kills `u`, so it
descends to a homomorphism `φ : ⟨a, b | (a ^ p b ^ q) ^ l⟩ →* Multiplicative ℤ` (the general form
`Work.ORLyndon.exists_levelHom_of_cohom_eq_one` is applied with `w = u ^ l`).  The Fox vector of the
root is `∂u / ∂a = 1 + a + ⋯ + a ^ (p-1)` (`Work.ORLyndon.rootVec_letterPow_mul_letterPow`), whose
terms have `φ`-levels `0, q, 2q, …, (p-1)q`: since `q ≥ 1`, the level `(p-1)q` is attained only by
the single monomial `a ^ (p-1)`, a unit of `K[G]`.  Hence the Fox component is a right
non-zero-divisor, i.e. `annAt` holds at `{a}`.

The transfer used at the last step is `Work.ORLyndon.regular_of_sum_of_uniqueMax`, proved here
directly by the *leading coefficient* argument (no `levelPartOf` decomposition is needed): for a
level homomorphism `φ : G →* Multiplicative ℤ` and a finite family `g : ι → G` whose `φ`-levels have
a unique maximum at `i₀`, the sum `∑ of (g i)` is a right non-zero-divisor of `K[G]`.  Indeed, for
`b ≠ 0` let `g₀` be an element of the support of `b` of maximal level; then the coefficient of
`g₀ * g i₀` in `b * ∑ of (g i)` is `b.coeff g₀ ≠ 0`, since every other summand `i ≠ i₀` contributes
the coefficient of `b` at an element of strictly larger level, which vanishes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLyndon

open MonoidAlgebra

/-- **A finite sum of group elements with a unique top level is a right non-zero-divisor.**

Let `φ : G →* Multiplicative ℤ` be a level homomorphism and `g : ι → G` a finite family whose
`φ`-levels have a maximum at `i₀`, attained there only.  Then `∑ i ∈ s, of (g i)` is a right
non-zero-divisor of `K[G]`: `b * ∑ of (g i) = 0` forces `b = 0`.

Proof (leading coefficient): if `b ≠ 0`, pick `g₀` in the support of `b` of maximal `φ`-level and
look at the coefficient of `g₀ * g i₀` in `b * ∑ i ∈ s, of (g i)`.  That coefficient is
`∑ i ∈ s, b (g₀ * g i₀ * (g i)⁻¹)`; for `i ≠ i₀` the argument has level strictly larger than that of
`g₀`, so the coefficient of `b` there vanishes, while for `i = i₀` the argument is `g₀` with
coefficient `b g₀ ≠ 0`.  So `b * ∑ of (g i) ≠ 0`, as required. -/
theorem regular_of_sum_of_uniqueMax {G : Type*} [Group G] {K : Type*} [Field K]
    (φ : G →* Multiplicative ℤ) {ι : Type*} (s : Finset ι) (g : ι → G) (i₀ : ι)
    (hi₀ : i₀ ∈ s)
    (hle : ∀ i ∈ s, Multiplicative.toAdd (φ (g i)) ≤ Multiplicative.toAdd (φ (g i₀)))
    (huniq : ∀ i ∈ s, Multiplicative.toAdd (φ (g i)) = Multiplicative.toAdd (φ (g i₀)) → i = i₀) :
    ∀ b : MonoidAlgebra K G, b * (∑ i ∈ s, MonoidAlgebra.of K G (g i)) = 0 → b = 0 := by
  classical
  intro b hb
  by_contra hb0
  obtain ⟨g₀, hg₀mem, hg₀max⟩ : ∃ g₀ ∈ b.coeff.support,
      ∀ h ∈ b.coeff.support, Multiplicative.toAdd (φ h) ≤ Multiplicative.toAdd (φ g₀) := by
    obtain ⟨g₀, hg₀, hmax⟩ := Finset.exists_max_image b.coeff.support
      (fun h => Multiplicative.toAdd (φ h))
      (Finsupp.support_nonempty_iff.mpr (fun h => hb0 (MonoidAlgebra.coeff_eq_zero.mp h)))
    exact ⟨g₀, hg₀, fun h hh => hmax h hh⟩
  have hcoe : (b * (∑ i ∈ s, MonoidAlgebra.of K G (g i))).coeff (g₀ * g i₀) = b.coeff g₀ := by
    rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    have hsingle : (∑ i ∈ s, (b * MonoidAlgebra.of K G (g i)).coeff (g₀ * g i₀))
        = (b * MonoidAlgebra.of K G (g i₀)).coeff (g₀ * g i₀) := by
      refine Finset.sum_eq_single
        (s := s) (f := fun i => (b * MonoidAlgebra.of K G (g i)).coeff (g₀ * g i₀)) i₀ ?_ ?_
      · intro i hi hne
        rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply, mul_one]
        by_contra hne0
        have hmem : g₀ * g i₀ * (g i)⁻¹ ∈ b.coeff.support := Finsupp.mem_support_iff.mpr hne0
        have hmax' := hg₀max _ hmem
        have hlev : Multiplicative.toAdd (φ (g₀ * g i₀ * (g i)⁻¹)) =
            Multiplicative.toAdd (φ g₀) + Multiplicative.toAdd (φ (g i₀))
              - Multiplicative.toAdd (φ (g i)) := by
          rw [map_mul φ, map_mul φ, map_inv φ, toAdd_mul, toAdd_mul, toAdd_inv]
          ring
        have hlt : Multiplicative.toAdd (φ (g i)) < Multiplicative.toAdd (φ (g i₀)) := by
          have h1 := hle i hi
          have h2 : Multiplicative.toAdd (φ (g i)) ≠ Multiplicative.toAdd (φ (g i₀)) :=
            fun h => hne (huniq i hi h)
          omega
        rw [hlev] at hmax'
        omega
      · intro h
        exact absurd hi₀ h
    rw [hsingle, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply, mul_one,
      mul_inv_cancel_right]
  rw [hb] at hcoe
  exact (Finsupp.mem_support_iff.mp hg₀mem) (by simpa using hcoe.symm)

/-- **The torus weight kills the root.**  For `c a = q`, `c b = -p` (here `a = (0 : Fin 2)`,
`b = (1 : Fin 2)`) one has `cohom c (a ^ p * b ^ q) = 1`: the character `c` descends to every
quotient `⟨a, b | (a ^ p * b ^ q) ^ l⟩`. -/
theorem cohom_torusWeight_kills {p q : ℕ} (c : Fin 2 → ℤ) (hc0 : c 0 = (q : ℤ))
    (hc1 : c 1 = -((p : ℤ))) :
    Work.OROneRel.cohom c ((FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q) = 1 := by
  rw [map_mul, map_pow, map_pow, Work.OROneRel.cohom_of, Work.OROneRel.cohom_of, hc0, hc1]
  rw [← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add, nsmul_eq_mul, nsmul_eq_mul]
  ring_nf
  rfl

/-- **The levels of the powers of the letter `a`.**  Under the torus weight the class of `a ^ i`
has level `i * q`. -/
theorem cohom_torusWeight_letterPow {q : ℕ} (c : Fin 2 → ℤ) (hc0 : c 0 = (q : ℤ)) (i : ℕ) :
    Work.OROneRel.cohom c ((FreeGroup.of (0 : Fin 2)) ^ i) =
      Multiplicative.ofAdd ((i : ℤ) * (q : ℤ)) := by
  rw [map_pow, Work.OROneRel.cohom_of, hc0, ← ofAdd_nsmul, nsmul_eq_mul]

theorem annAt_letterPow_mul_letterPow {K : Type*} [Field K] {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (l : ℕ) :
    Work.ORLyndon.annAt K
      (((FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q) ^ l)
      ((FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q) {(0 : Fin 2)} := by
  classical
  set u : FreeGroup (Fin 2) := FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q with hu
  set ā : OneRelatorGroup (u ^ l) := presentRho (u ^ l) (FreeGroup.of (0 : Fin 2)) with hā
  set c : Fin 2 → ℤ := fun x => if x = 0 then (q : ℤ) else -((p : ℤ)) with hc
  have hc_0 : c 0 = (q : ℤ) := by simp [hc]
  have hc_1 : c 1 = -((p : ℤ)) := by
    simp only [hc]
    rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
  have hcu : Work.OROneRel.cohom c u = 1 := cohom_torusWeight_kills c hc_0 hc_1
  have hw : Work.OROneRel.cohom c (u ^ l) = 1 := by rw [map_pow, hcu, one_pow]
  obtain ⟨φ, hφ⟩ := exists_levelHom_of_cohom_eq_one c (u ^ l) hw
  change Work.ORLyndon.annAt K (u ^ l) u ({(0 : Fin 2)} : Set (Fin 2))
  intro b hb
  have hb0 : b * rootVec K (u ^ l) u (0 : Fin 2) = 0 := hb 0 (Set.mem_singleton 0)
  have hrv : rootVec K (u ^ l) u (0 : Fin 2)
      = ∑ i ∈ Finset.range p, (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) ā) ^ i :=
    rootVec_letterPow_mul_letterPow p q l
  rw [hrv] at hb0
  have hsum : (∑ i ∈ Finset.range p, (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) ā) ^ i)
      = ∑ i ∈ Finset.range p, MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (ā ^ i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  rw [hsum] at hb0
  have hφval : ∀ i : ℕ, Multiplicative.toAdd (φ (ā ^ i)) = (i : ℤ) * (q : ℤ) := by
    intro i
    have h1 : φ (ā ^ i) = Work.OROneRel.cohom c (FreeGroup.of (0 : Fin 2) ^ i) := by
      rw [hā, ← map_pow]
      exact hφ (FreeGroup.of (0 : Fin 2) ^ i)
    rw [h1, cohom_torusWeight_letterPow c hc_0 i, toAdd_ofAdd]
  refine regular_of_sum_of_uniqueMax (K := K) φ (Finset.range p) (fun i => ā ^ i) (p - 1)
    ?_ ?_ ?_ b hb0
  · exact Finset.mem_range.mpr (by omega)
  · intro i hi
    rw [hφval i, hφval (p - 1)]
    have hi' : i ≤ p - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hcast : (i : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hi'
    exact mul_le_mul_of_nonneg_right hcast (by positivity)
  · intro i hi h
    rw [hφval i, hφval (p - 1)] at h
    have hq0 : ((q : ℤ)) ≠ 0 := by
      have : q ≠ 0 := by omega
      exact_mod_cast this
    have h2 : (i : ℤ) = ((p - 1 : ℕ) : ℤ) := mul_right_cancel₀ hq0 h
    exact_mod_cast h2

end Work.ORLyndon
