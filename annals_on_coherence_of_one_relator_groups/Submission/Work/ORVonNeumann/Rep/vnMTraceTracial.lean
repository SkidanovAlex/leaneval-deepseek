import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.Rep.tau_tracial

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- The trace `τ` is additive over finite sums in the group von Neumann algebra `N(G)`. -/
theorem tau_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ↥(Work.ORVonNeumann.groupVonNeumann G)) :
    tau (∑ i ∈ s, f i) = ∑ i ∈ s, tau (f i) := by
  rw [← tauLin_apply, map_sum]
  simp

/-- The trace of a finite sum indexed by a fintype. -/
theorem tau_univ_sum (k : ℕ) (f : Fin k → ↥(Work.ORVonNeumann.groupVonNeumann G)) :
    tau (∑ i, f i) = ∑ i, tau (f i) :=
  tau_finset_sum Finset.univ f

/-- **Traciality of the amplified trace.**  For matrices `A : Mat_{m×n}(N(G))` and
`B : Mat_{n×m}(N(G))` over the group von Neumann algebra, the amplified trace of the
"square" products agrees: `tr_m(A B) = tr_n(B A)`.

This is the cyclic invariance of the trace, expanded entrywise and reduced to the traciality
`τ (a b) = τ (b a)` of `τ` on `N(G)` (`Work.Rep.tau_tracial`). -/
theorem vnMTraceTracial {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {m n : ℕ} (A : Matrix (Fin m) (Fin n) (↥(Work.ORVonNeumann.groupVonNeumann G))) (B : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) : Work.ORVonNeumann.Rep.mTrace (G := G) m (A * B) = Work.ORVonNeumann.Rep.mTrace (G := G) n (B * A) := by
  classical
  have h1 : mTrace (G := G) m (A * B)
      = ∑ i : Fin m, ∑ j : Fin n, tau (A i j * B j i) := by
    rw [mTrace_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [Matrix.mul_apply, tau_univ_sum])
  have h2 : mTrace (G := G) n (B * A)
      = ∑ j : Fin n, ∑ i : Fin m, tau (B j i * A i j) := by
    rw [mTrace_apply]
    exact Finset.sum_congr rfl (fun j _ => by rw [Matrix.mul_apply, tau_univ_sum])
  rw [h1, h2, Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ =>
    Work.Rep.tau_tracial (G := G) (A i j) (B j i)))

end Work.ORVonNeumann.Rep
