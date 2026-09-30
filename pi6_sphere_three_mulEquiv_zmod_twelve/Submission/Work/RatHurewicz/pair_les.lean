import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.RatHurewicz.PairShiftBijective
import Submission.Work.RatHurewicz.PairLESCrux
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.LoopShiftShifted
import Submission.Work.StemsB.PiMap

namespace Work.RatHurewicz

open Work.StemsB

noncomputable section

/-- **The long exact sequence of a pair.**  For `i : C(A,X)` and `a₀ : A`, put
`RelHomotopyGroup i a₀ n = πₙ(homotopyFibre i a₀)`, the `n`-th homotopy group of the homotopy
fibre of `i` (equivalently the classical relative homotopy group of the pair `(X,A,a₀)`, shifted by
one).  Then the sequence
`π_{k+3}(X) → π_{k+2}(X,A) → π_{k+2}(A) → π_{k+2}(X) → π_{k+1}(X,A) → π_{k+1}(A)`
is exact at `π_{k+2}(X,A)`, at `π_{k+2}(A)`, at `π_{k+2}(X)` and at `π_{k+1}(X,A)`, where

* `π_{k+2}(X,A) → π_{k+2}(A)` is the map of homotopy groups induced by the projection `homotopyFibreFst`,
* `π_{k+2}(A) → π_{k+2}(X)` is the map induced by `i`,
* `π_{k+1}(X,A) → π_{k+1}(A)` is again the map induced by the projection `homotopyFibreFst`,

and the two remaining maps are the connecting maps of the fibration `homotopyFibreFst i a₀`,
transported along the loop-space shift `π_{m+1}(X) ≃* π_m(ΩX)`. -/
theorem pair_les {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]
    (i : C(A, X)) (a₀ : A) (k : ℕ) (hk : 1 ≤ k) :
    ∃ (del : HomotopyGroup (Fin (k + 3)) X (i a₀) →*
          Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 2))
      (d : HomotopyGroup (Fin (k + 2)) X (i a₀) →*
          Work.RatHurewicz.RelHomotopyGroup i a₀ (k + 1)),
      Function.MulExact del
        (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) ∧
      Function.MulExact
        (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) (k + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
        (Work.StemsB.πmap i (k + 1) a₀) ∧
      Function.MulExact (Work.StemsB.πmap i (k + 1) a₀) d ∧
      Function.MulExact d
        (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst i a₀) k
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
  -- it suffices to treat the case `k = m + 1`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩
  subst hm
  refine ⟨(πmap (fibreIncl (homotopyFibreFst i a₀)
            ((homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))) ((m + 1) + 1)
            (fibrePoint (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))).comp
            (pairShiftHom i a₀ ((m + 1) + 1)),
          (πmap (fibreIncl (homotopyFibreFst i a₀)
            ((homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))) (m + 1)
            (fibrePoint (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))).comp
            (pairShiftHom i a₀ (m + 1)),
          ?_, ?_, ?_, ?_⟩
  · -- exactness at `π_{m+3}(X)`-image/... : the image of `del` is the image of the inclusion
    intro y
    have hE := les_exact_E (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)
      (fibreHrel i a₀) (m + 1)
    constructor
    · intro hy
      obtain ⟨w, hw⟩ := (hE y).mp hy
      obtain ⟨x, hx⟩ := (pairShiftHom_bijective i a₀ ((m + 1) + 1)).2 w
      refine ⟨x, ?_⟩
      show (πmap (fibreIncl (homotopyFibreFst i a₀)
        ((homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))) ((m + 1) + 1)
        (fibrePoint (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)))
        (pairShiftHom i a₀ ((m + 1) + 1) x) = y
      rw [hx]
      exact hw
    · rintro ⟨x, rfl⟩
      exact (hE ((πmap (fibreIncl (homotopyFibreFst i a₀)
        ((homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))) ((m + 1) + 1)
        (fibrePoint (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)))
        (pairShiftHom i a₀ ((m + 1) + 1) x))).mpr
        ⟨pairShiftHom i a₀ ((m + 1) + 1) x, rfl⟩
  · -- the connecting map is `i_*` after the loop space shift
    intro y
    have hE := les_exact_B (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)
      (fibreHrel i a₀) (m + 1)
    constructor
    · intro hy
      refine (hE y).mp ?_
      show (fibreDMap i a₀ (m + 1)) y = 1
      rw [fibreDMap_eq_pairShiftHom i a₀ (m + 1)]
      show (pairShiftHom i a₀ (m + 1)) ((πmap i ((m + 1) + 1) a₀) y) = 1
      rw [hy, map_one]
    · intro hy
      have h : (pairShiftHom i a₀ (m + 1)) ((πmap i ((m + 1) + 1) a₀) y) = 1 := by
        have h' : (fibreDMap i a₀ (m + 1)) y = 1 := (hE y).mpr hy
        have hcrux := congrArg (fun t => (⇑t) y) (fibreDMap_eq_pairShiftHom i a₀ (m + 1))
        rw [hcrux] at h'
        show ((pairShiftHom i a₀ (m + 1)).comp (πmap i ((m + 1) + 1) a₀)) y = 1
        exact h'
      have h3 : (pairShiftHom i a₀ (m + 1)) ((πmap i ((m + 1) + 1) a₀) y)
          = pairShiftHom i a₀ (m + 1) 1 := by
        rw [h, map_one]
      exact (pairShiftHom_bijective i a₀ (m + 1)).1 h3
  · -- the kernel of `d` is the image of `i_*`
    intro y
    have hF := les_exact_F (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)
      (fibreHrel i a₀) (m + 1)
    constructor
    · intro hy
      have hmem : pairShiftHom i a₀ (m + 1) y ∈ Set.range (fibreDMap i a₀ (m + 1)) :=
        (hF (pairShiftHom i a₀ (m + 1) y)).1 hy
      obtain ⟨x, hx⟩ := hmem
      refine ⟨x, ?_⟩
      apply (pairShiftHom_bijective i a₀ (m + 1)).1
      show (pairShiftHom i a₀ (m + 1)) ((πmap i ((m + 1) + 1) a₀) x)
        = pairShiftHom i a₀ (m + 1) y
      rw [← hx]
      show (pairShiftHom i a₀ (m + 1)) ((πmap i ((m + 1) + 1) a₀) x)
        = (fibreDMap i a₀ (m + 1)) x
      rw [fibreDMap_eq_pairShiftHom i a₀ (m + 1)]
      rfl
    · rintro ⟨x, rfl⟩
      refine (hF (pairShiftHom i a₀ (m + 1) ((πmap i ((m + 1) + 1) a₀) x))).2 ⟨x, ?_⟩
      show (fibreDMap i a₀ (m + 1)) x
        = (pairShiftHom i a₀ (m + 1)) ((πmap i ((m + 1) + 1) a₀) x)
      rw [fibreDMap_eq_pairShiftHom i a₀ (m + 1)]
      rfl
  · -- exactness at `π_{m+2}(F)`
    intro y
    have hE := les_exact_E (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)
      (fibreHrel i a₀) m
    constructor
    · intro hy
      obtain ⟨w, hw⟩ := (hE y).mp hy
      obtain ⟨x, hx⟩ := (pairShiftHom_bijective i a₀ (m + 1)).2 w
      refine ⟨x, ?_⟩
      show (πmap (fibreIncl (homotopyFibreFst i a₀)
        ((homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))) (m + 1)
        (fibrePoint (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)))
        (pairShiftHom i a₀ (m + 1) x) = y
      rw [hx]
      exact hw
    · rintro ⟨x, rfl⟩
      exact (hE ((πmap (fibreIncl (homotopyFibreFst i a₀)
        ((homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀))) (m + 1)
        (fibrePoint (homotopyFibreFst i a₀) (homotopyFibreBasepoint i a₀)))
        (pairShiftHom i a₀ (m + 1) x))).mpr
        ⟨pairShiftHom i a₀ (m + 1) x, rfl⟩

end

end Work.RatHurewicz
