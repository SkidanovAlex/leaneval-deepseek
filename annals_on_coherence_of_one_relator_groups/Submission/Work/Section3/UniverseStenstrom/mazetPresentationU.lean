import Mathlib
import Submission.Work.ORHughesFree.Epic.BalancedTensor
import Submission.Work.Section3.UniverseStenstrom.matrixAssemblyU
import Submission.Work.Section3.UniverseStenstrom.mazetSyzygyU

set_option maxHeartbeats 1600000

universe u

namespace Work.Section3.UniverseStenstrom

open scoped TensorProduct

/-- In the `R`-balanced tensor product `S ⊗[R] S` the elementary tensor `a ⊗ 0` vanishes. -/
private lemma tmul_zero_right {R S : Type u} [Ring R] [Ring S] (f : R →+* S) (a : S) :
    Work.ORHughesFree.Epic.BalancedTensor.tmul f a 0 = 0 := by
  show Work.ORHughesFree.Epic.BalancedTensor.mk f (a ⊗ₜ[ℤ] (0 : S)) = 0
  rw [TensorProduct.tmul_zero, map_zero]

/-- **Mazet's presentation, universe-general form.**  If `f : R →+* S` satisfies the
Isbell–Silver–Mazet criterion `s ⊗ 1 = 1 ⊗ s` for all `s : S` (in the `R`-balanced tensor product
`S ⊗[R] S`), then every `d : S` is the `(0,0)` entry of a product `X · f(P) · Y` of matrices over
`S`, with `P` a matrix over `R` such that `X · f(P)` is a row over `f(R)` and `f(P) · Y` is a
column over `f(R)`.

This is the universe-general version of `Work.ORHughesFree.Section3.mazetPresentation`: the tensor
relation `d ⊗ 1 - 1 ⊗ d = 0` is turned into the Mazet syzygy data by `mazetSyzygyU` (the
universe-general form of `Mazet.syzygy`) and then assembled into matrices by `matrixAssemblyU`. -/
theorem mazetPresentationU {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (h : ∀ s : S, Work.ORHughesFree.Epic.BalancedTensor.tmul f s 1
        = Work.ORHughesFree.Epic.BalancedTensor.tmul f 1 s) (d : S) :
    ∃ (n : ℕ) (X : Matrix (Fin 1) (Fin n) S) (P : Matrix (Fin n) (Fin n) R)
      (Y : Matrix (Fin n) (Fin 1) S),
      (∃ P' : Matrix (Fin 1) (Fin n) R, X * P.map f = P'.map f) ∧
      (∃ Q' : Matrix (Fin n) (Fin 1) R, P.map f * Y = Q'.map f) ∧
      d = (X * P.map f * Y) 0 0 := by
  classical
  -- The tensor relation `d ⊗ 1 - 1 ⊗ d = 0`, i.e. `theta f (single d 1, -d) = 0`.
  have hrel : (Finsupp.single d (1 : S)).sum
        (fun s v => Work.ORHughesFree.Epic.BalancedTensor.tmul f s v)
      + Work.ORHughesFree.Epic.BalancedTensor.tmul f 1 (-d) = 0 := by
    rw [Finsupp.sum_single_index (tmul_zero_right f d)]
    have hneg : Work.ORHughesFree.Epic.BalancedTensor.tmul f 1 (-d)
        = - Work.ORHughesFree.Epic.BalancedTensor.tmul f 1 d := by
      have h0 : Work.ORHughesFree.Epic.BalancedTensor.tmul f 1 (-d + d) = 0 := by
        rw [neg_add_cancel]; exact tmul_zero_right f 1
      rw [Work.ORHughesFree.Epic.BalancedTensor.tmul_add_right] at h0
      exact eq_neg_of_add_eq_zero_left h0
    rw [hneg, h d, add_neg_cancel]
  -- Mazet's syzygy lemma produces the data underlying the matrix presentation.
  obtain ⟨m, a, astar, z, h1, h2, h3⟩ := mazetSyzygyU f hrel
  exact matrixAssemblyU f d m a astar z (Finsupp.single d (1 : S)) h1 h2 (by
    intro s
    rw [Finsupp.single_apply]
    by_cases hs : d = s
    · rw [if_pos hs]; exact ⟨1, map_one f⟩
    · rw [if_neg hs]; exact ⟨0, map_zero f⟩) (by rw [← h3, neg_neg])

end Work.Section3.UniverseStenstrom
