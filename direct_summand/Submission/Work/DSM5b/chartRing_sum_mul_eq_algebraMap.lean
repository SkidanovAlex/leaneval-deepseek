import Mathlib
import Submission.Work.DSM5b.CycleDefs

namespace Work.DSM5b

universe a

open scoped BigOperators

/-- **Coordinates multiply back to the denominator**: if `u l ∈ R[J/t_i]` is the coordinate
`t_l/t_i` of the point (i.e. `u l · t_i = t_l` in `R_{t_i}`), and `c = ∑_b d_b ∏_k t_{b k}` is an
element written in those coordinates, then `(∑_b d_b ∏_k u_{b k}) · t_i^n = c` in `R_{t_i}`. -/
theorem chartRing_sum_mul_eq_algebraMap {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (i : ι) (n : ℕ) (c : R) (B : Finset (Fin n → ι)) (d : (Fin n → ι) → R)
    (hcd : c = ∑ b ∈ B, d b * ∏ k, t (b k))
    (u : ι → ↥(DSMap.Mix2.chartRing t {i}))
    (hu : ∀ l : ι, (u l : Localization.Away (DSMap.Mix2.tS t {i}))
        * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t l)) :
    ((∑ b ∈ B, algebraMap R ↥(DSMap.Mix2.chartRing t {i}) (d b) * ∏ k, u (b k)
        : ↥(DSMap.Mix2.chartRing t {i})) : Localization.Away (DSMap.Mix2.tS t {i}))
      * (algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (DSMap.Mix2.tS t {i})) ^ n
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) c := by
  let A := ↥(DSMap.Mix2.chartRing t {i})
  let M := Localization.Away (DSMap.Mix2.tS t {i})
  -- `tS t {i} = t i`: the singleton chart has a single generator
  have htS : DSMap.Mix2.tS t {i} = t i := Finset.prod_singleton t i
  have hti : algebraMap R M (DSMap.Mix2.tS t {i}) = algebraMap R M (t i) := congrArg _ htS
  -- compatibility of the two `algebraMap`s
  have hcoeR : ∀ x : R, algebraMap A M (algebraMap R A x) = algebraMap R M x := fun x =>
    (IsScalarTower.algebraMap_apply R A M x).symm
  have hcoeU : ∀ l : ι, algebraMap A M (u l) = (u l : M) := fun l => rfl
  -- the `b`-th monomial: `∏_k u_{b k} · t_i^n = ∏_k t_{b k}`
  have key : ∀ b : Fin n → ι,
      algebraMap A M (algebraMap R A (d b) * ∏ k, u (b k))
        * (algebraMap R M (DSMap.Mix2.tS t {i})) ^ n
      = algebraMap R M (d b * ∏ k, t (b k)) := by
    intro b
    have hpow : (algebraMap R M (t i)) ^ n = ∏ _k : Fin n, algebraMap R M (t i) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [map_mul, map_prod, hcoeR]
    rw [Finset.prod_congr rfl (fun k _ => hcoeU (b k))]
    rw [hti, hpow, mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.prod_congr rfl (fun k _ => hu (b k)), ← map_prod, ← map_mul]
  change algebraMap A M (∑ b ∈ B, algebraMap R A (d b) * ∏ k, u (b k))
      * (algebraMap R M (DSMap.Mix2.tS t {i})) ^ n = algebraMap R M c
  rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun b _ => key b), ← map_sum, ← hcd]

end Work.DSM5b
