import Mathlib
import Submission.CDTPlan.InterfacesC

/-!
# `Work.C17.pure_step`

Given a `ℚ(y)`-relation `Σ_i P_i • f_i = 0` among the seventeen functions of Theorem C whose
coefficients at the four `G`-derivatives (indices `5,6,7,8`) and at the six formal integrals
(indices `11,…,16`) vanish, every coefficient vanishes.

The sixteen `G`- and integral entries lie outside the image of

`e17 = ![0,1,2,3,4,9,10] : Fin 7 → Fin 17`,

which selects the pure entries `B₁,…,B₇`, so the relation collapses to a relation among
`pureB 0, …, pureB 6`, which the paper's Lemma `seven` (`hS`) kills.
-/

namespace Work.C17

open scoped BigOperators

/-- The position of the pure entry `pureB j` inside the list `seventeen`. -/
def e17 : Fin 7 → Fin 17 := ![(0 : Fin 17), 1, 2, 3, 4, 9, 10]

/-- `e17` selects exactly the pure entries: entry `j` of `seventeen` at `e17 j` is `pureB j`. -/
lemma e17_seventeen (m n : ℕ) (ra rb rab r0 : ℤ) (j : Fin 7) :
    Submission.CDTPlan.seventeen m n ra rb rab r0 (e17 j) = Submission.CDTPlan.pureB j := by
  fin_cases j <;>
    simp [e17, Submission.CDTPlan.seventeen, Submission.CDTPlan.pureB]

theorem pure_step (hS : Submission.CDTPlan.LemmaSeven) (m n : ℕ) (ra rb rab r0 : ℤ)
    (P : Fin 17 → Polynomial ℚ)
    (hsum : ∑ i : Fin 17,
      (P i : PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 i = 0)
    (h5 : P 5 = 0) (h6 : P 6 = 0) (h7 : P 7 = 0) (h8 : P 8 = 0)
    (h11 : P 11 = 0) (h12 : P 12 = 0) (h13 : P 13 = 0) (h14 : P 14 = 0)
    (h15 : P 15 = 0) (h16 : P 16 = 0) :
    ∀ i : Fin 17, P i = 0 := by
  classical
  set s : Finset (Fin 17) := {0, 1, 2, 3, 4, 9, 10} with hs
  have himage : Finset.image e17 Finset.univ = s := by rw [hs]; decide
  -- the indices outside `s` are exactly the ones whose coefficient vanishes
  have hzero : ∀ i : Fin 17, i ∉ s → P i = 0 := by
    intro i hi
    fin_cases i <;>
      first
      | exact absurd hi (by rw [hs]; decide)
      | exact h5 | exact h6 | exact h7 | exact h8 | exact h11 | exact h12 | exact h13
      | exact h14 | exact h15 | exact h16
  -- the relation collapses to a relation among the seven pure functions
  have hsplit : (∑ i : Fin 17,
        (P i : PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 i)
      = ∑ j : Fin 7, (P (e17 j) : PowerSeries ℚ) * Submission.CDTPlan.pureB j := by
    have key : ∑ j : Fin 7, (P (e17 j) : PowerSeries ℚ) * Submission.CDTPlan.pureB j
        = ∑ j : Fin 7,
            (P (e17 j) : PowerSeries ℚ)
              * Submission.CDTPlan.seventeen m n ra rb rab r0 (e17 j) :=
      Finset.sum_congr rfl fun j _ => by rw [e17_seventeen]
    have h1 : ∑ x ∈ Finset.image e17 Finset.univ,
            (P x : PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 x
        = ∑ j : Fin 7,
            (P (e17 j) : PowerSeries ℚ)
              * Submission.CDTPlan.seventeen m n ra rb rab r0 (e17 j) := by
      rw [Finset.sum_image (s := (Finset.univ : Finset (Fin 7))) (g := e17)
        (f := fun x : Fin 17 =>
          (P x : PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 x)
        (fun a _ b _ h => (by decide : Function.Injective e17) h)]
    have h2 : ∑ i : Fin 17,
            (P i : PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 i
        = ∑ x ∈ Finset.image e17 Finset.univ,
            (P x : PowerSeries ℚ) * Submission.CDTPlan.seventeen m n ra rb rab r0 x := by
      rw [himage]
      exact (Finset.sum_subset (s₁ := s) (s₂ := Finset.univ) (Finset.subset_univ _)
        (fun x _ hx => by simp [hzero x hx])).symm
    exact h2.trans (h1.trans key.symm)
  have hQ : ∑ j : Fin 7, (P (e17 j) : PowerSeries ℚ) * Submission.CDTPlan.pureB j = 0 := by
    rw [← hsplit]; exact hsum
  have hkey : ∀ j : Fin 7, P (e17 j) = 0 := hS (fun j => P (e17 j)) hQ
  intro i
  fin_cases i <;>
    first
    | exact h5 | exact h6 | exact h7 | exact h8 | exact h11 | exact h12 | exact h13
    | exact h14 | exact h15 | exact h16
    | simpa [e17] using hkey 0
    | simpa [e17] using hkey 1
    | simpa [e17] using hkey 2
    | simpa [e17] using hkey 3
    | simpa [e17] using hkey 4
    | simpa [e17] using hkey 5
    | simpa [e17] using hkey 6

end Work.C17
