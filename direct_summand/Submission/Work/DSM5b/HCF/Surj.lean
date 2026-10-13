import Submission.Work.DSM5b.HCF.Basic

/-!
# The "surjection complex" with coefficients `N`

For `S₀ : Finset (Fin n)` and an `R`-module `N`, this is the explicit cochain complex

  `C^q = ∏_{τ : Fin (q+1) → Fin n, tupRng τ = S₀} N`,
  `(dz) τ = ∑ i, if tupRng (tupDel i τ) = S₀ then (-1)^i • z (tupDel i τ) else 0`,

i.e. the differential drops the deletions which lose surjectivity onto `S₀`.  It is the honest
(double-indexed, "tuples with repetitions") Čech complex of the coefficient system supported on the
single subset `S₀`.

The cohomology of this complex, and the canonical isomorphism in degree `♯S₀ - 1` given by
evaluation at the increasing enumeration `incTupleE S₀`, is the crux of the honest-vs-sorted
comparison used in `Work.DSM5b.honestCohomologyFinite`.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe a

variable {R : Type a} [CommRing R]

section Surj

variable {n : ℕ} {S₀ : Finset (Fin n)} {N : Type a} [AddCommGroup N] [Module R N]

/-- The tuples of length `q+1` whose range is exactly `S₀`. -/
abbrev SurjIdx (S₀ : Finset (Fin n)) (q : ℕ) : Type := {τ : Fin (q + 1) → Fin n // tupRng τ = S₀}

/-- The `q`-th term of the surjection complex: functions on the surjective tuples. -/
abbrev SurjTerm (S₀ : Finset (Fin n)) (N : Type a) (q : ℕ) : Type a := SurjIdx S₀ q → N

/-- The differential of the surjection complex, dropping the deletions which lose surjectivity. -/
noncomputable def surjD (S₀ : Finset (Fin n)) (N : Type a) [AddCommGroup N] [Module R N]
    (q : ℕ) : SurjTerm S₀ N q →ₗ[R] SurjTerm S₀ N (q + 1) where
  toFun z := fun τ => ∑ i : Fin (q + 2), if h : tupRng (tupDel i τ.1) = S₀ then
      ((-1 : R) ^ (i : ℕ)) • z ⟨tupDel i τ.1, h⟩ else 0
  map_add' z z' := by
    funext τ
    rw [Pi.add_apply]
    trans ∑ i : Fin (q + 2), ((if h : tupRng (tupDel i τ.1) = S₀ then
          ((-1 : R) ^ (i : ℕ)) • z ⟨tupDel i τ.1, h⟩ else 0) +
        (if h : tupRng (tupDel i τ.1) = S₀ then
          ((-1 : R) ^ (i : ℕ)) • z' ⟨tupDel i τ.1, h⟩ else 0))
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : tupRng (tupDel i τ.1) = S₀
      · rw [dif_pos h, dif_pos h, dif_pos h]
        simp only [Pi.add_apply, smul_add]
      · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]
    · rw [Finset.sum_add_distrib]
  map_smul' r z := by
    funext τ
    rw [Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : tupRng (tupDel i τ.1) = S₀
    · rw [dif_pos h, dif_pos h]
      simp only [RingHom.id_apply]
      exact smul_comm _ _ _
    · rw [dif_neg h, dif_neg h]
      simp only [RingHom.id_apply, smul_zero]

/-- The increasing enumeration of `S₀`, as a tuple of length `q+1` whose range is `S₀`
(so `q = ♯S₀ - 1` is the top degree of the surjection complex). -/
noncomputable def incTupleE (S₀ : Finset (Fin n)) (q : ℕ) (hq : q + 1 = S₀.card) :
    SurjIdx S₀ q :=
  ⟨fun i => ((S₀.orderIsoOfFin hq.symm i : ↥S₀) : Fin n), by
    ext x
    simp only [tupRng, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (S₀.orderIsoOfFin hq.symm i).2
    · intro hx
      refine ⟨(S₀.orderIsoOfFin hq.symm).symm ⟨x, hx⟩, ?_⟩
      simp⟩

end Surj

end Work.DSM5b
