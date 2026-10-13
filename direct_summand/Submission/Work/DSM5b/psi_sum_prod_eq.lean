import Mathlib
import Submission.Work.DSM5b.CycleDefs

namespace Work.DSM5b

universe a

open DSMap DSMap.Mix DSMap.Mix2

set_option maxHeartbeats 800000

theorem psi_sum_prod_eq {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) {A K : Type a} [CommRing A] [Field K] [Algebra A K]
    (φ : R →+* A) (i j : ι)
    (u : ι → ↥(DSMap.Mix2.chartRing t {i}))
    (ψ : ↥(DSMap.Mix2.chartRing t {i}) →+* K)
    (hcompat : ψ.comp (algebraMap R ↥(DSMap.Mix2.chartRing t {i})) = (algebraMap A K).comp φ)
    (a : ι → A) (ha : ∀ l, ψ (u l) = algebraMap A K (a l) * ψ (u j))
    (n : ℕ) (B : Finset (Fin n → ι)) (d : (Fin n → ι) → R) :
    ψ (∑ b ∈ B, algebraMap R ↥(DSMap.Mix2.chartRing t {i}) (d b) * ∏ k, u (b k))
      = algebraMap A K (∑ b ∈ B, φ (d b) * ∏ k, a (b k)) * (ψ (u j)) ^ n := by
  -- `ψ` is compatible with the `R`-algebra structure via `φ`.
  have hψR : ∀ r : R, ψ (algebraMap R ↥(DSMap.Mix2.chartRing t {i}) r) = algebraMap A K (φ r) := by
    intro r
    have h := RingHom.congr_fun hcompat r
    simpa [RingHom.comp_apply] using h
  -- the value of `ψ` on a single summand.
  have hterm : ∀ b : Fin n → ι,
      ψ (algebraMap R ↥(DSMap.Mix2.chartRing t {i}) (d b) * ∏ k, u (b k))
        = algebraMap A K (φ (d b) * ∏ k, a (b k)) * (ψ (u j)) ^ n := by
    intro b
    rw [map_mul, map_prod, hψR]
    rw [show (∏ k : Fin n, ψ (u (b k))) = ∏ k : Fin n, (algebraMap A K (a (b k)) * ψ (u j)) from
      Finset.prod_congr rfl (fun k _ => ha (b k))]
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [map_mul]; ring
  -- distribute `ψ` over the outer sum, apply the per-summand computation, factor the constant.
  rw [map_sum]
  trans ∑ x ∈ B, algebraMap A K (φ (d x) * ∏ k, a (x k)) * (ψ (u j)) ^ n
  · apply Finset.sum_congr rfl; intro x _; exact hterm x
  · rw [← Finset.sum_mul, ← map_sum]

end Work.DSM5b
