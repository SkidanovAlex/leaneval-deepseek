import Mathlib
import Submission.Work.ORP311.P311Defs
import Submission.Work.ORP311.eq_zero_of_blk_eq_zero
import Submission.Work.ORP311.blk_comp_regBlk

namespace Work.ORP311

open Work.ORVonNeumann

/-- **The lowest-coset induction for the window kernel of the two-term operator.**

`P311.Ewin n N t m (twoTerm n t S C)` consists of the vectors `η` supported on the Følner window
`window N t m` whose block-`j` projection `P311.blk n N t j (twoTerm n t S C η)` vanishes for
every `j` with `-(m : ℤ) < j ≤ m`.

Writing `x_j := P311.blk n N t j η`, the assumptions `S` and `C` commute with every block
projection (`hSb`, `hCb`) together with `blk_comp_regBlk h n j`
(`blk j ∘L regBlk n t = regBlk n t ∘L blk (j - 1)`) give, for every `j`,

`blk j (twoTerm n t S C η) = S x_j + C (regBlk n t x_{j-1})`.

Hence the vanishing of `blk (-(m : ℤ)) η = x_{-(m : ℤ)}` (`h0`) and the injectivity of `S`
(`hS`) force `x_j = 0` for all `j ∈ [-(m : ℤ), m]` by upward induction on `j`: if `x_{j-1} = 0`
then `S x_j = 0`, so `x_j = 0`.  Since `η` is supported on the window, whose cosets are exactly
those with `j ∈ [-(m : ℤ), m]`, `eq_zero_of_blk_eq_zero` then gives `η = 0`. -/
theorem Ewin_bottom_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (h : Work.ORP311.P311.TwistData N t) (n m : ℕ) (S C : Work.ORVonNeumann.Rep.HSum (G := G) n →L[ℂ] Work.ORVonNeumann.Rep.HSum (G := G) n) (hSb : ∀ j, Work.ORP311.P311.blk n N t j ∘L S = S ∘L Work.ORP311.P311.blk n N t j) (hCb : ∀ j, Work.ORP311.P311.blk n N t j ∘L C = C ∘L Work.ORP311.P311.blk n N t j) (hS : Function.Injective S) {η : Work.ORVonNeumann.Rep.HSum (G := G) n} (hη : η ∈ Work.ORP311.P311.Ewin n N t m (Work.ORP311.twoTerm (G := G) n t S C)) (h0 : Work.ORP311.P311.blk n N t (-(m : ℤ)) η = 0) : η = 0 := by
  -- Unpack the membership in the window kernel.
  have hη' := hη
  simp only [Work.ORP311.P311.Ewin, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    at hη'
  obtain ⟨hwin, hker⟩ := hη'
  -- The block-level relation `blk j (twoTerm S C η) = S (blk j η) + C (regBlk t (blk (j-1) η))`.
  have hrel : ∀ j : ℤ, (Work.ORP311.P311.blk n N t j) (Work.ORP311.twoTerm (G := G) n t S C η)
      = S ((Work.ORP311.P311.blk n N t j) η)
        + C (Work.ORP311.regBlk (G := G) n t ((Work.ORP311.P311.blk n N t (j - 1)) η)) := by
    intro j
    rw [Work.ORP311.twoTerm]
    simp only [add_apply, map_add, ContinuousLinearMap.comp_apply]
    congr 1
    · simpa only [ContinuousLinearMap.comp_apply] using congrArg (fun f => f η) (hSb j)
    · rw [show (Work.ORP311.P311.blk n N t j) (C (Work.ORP311.regBlk (G := G) n t η))
            = C ((Work.ORP311.P311.blk n N t j) (Work.ORP311.regBlk (G := G) n t η)) from
        congrArg (fun f => f (Work.ORP311.regBlk (G := G) n t η)) (hCb j)]
      rw [show (Work.ORP311.P311.blk n N t j) (Work.ORP311.regBlk (G := G) n t η)
            = Work.ORP311.regBlk (G := G) n t ((Work.ORP311.P311.blk n N t (j - 1)) η) from
        congrArg (fun f => f η) (Work.ORP311.blk_comp_regBlk h n j)]
  -- Upward induction from the bottom coset `-(m : ℤ)`.
  have key : ∀ j : ℤ, -(m : ℤ) ≤ j → j ≤ (m : ℤ) → (Work.ORP311.P311.blk n N t j) η = 0 := by
    have hin : ∀ j : ℤ, -(m : ℤ) ≤ j →
        (j ≤ (m : ℤ) → (Work.ORP311.P311.blk n N t j) η = 0) := by
      refine Int.leInduction (m := -(m : ℤ))
        (motive := fun j _ => j ≤ (m : ℤ) → (Work.ORP311.P311.blk n N t j) η = 0) ?_ ?_
      · intro _; exact h0
      · intro k _hk ih hjle
        have hk1 : -(m : ℤ) < k + 1 := by omega
        have hkm : k ≤ (m : ℤ) := by omega
        have hkrel := hrel (k + 1)
        have hsub : (k + 1 : ℤ) - 1 = k := by ring
        rw [hsub] at hkrel
        have hkker : (Work.ORP311.P311.blk n N t (k + 1))
            (Work.ORP311.twoTerm (G := G) n t S C η) = 0 := by
          have hh := hker (k + 1) ⟨hk1, hjle⟩
          simpa using hh
        rw [hkrel] at hkker
        simp only [ih hkm, map_zero, add_zero] at hkker
        exact hS (by simpa using hkker)
    intro j hj1 hj2
    exact hin j hj1 hj2
  -- A window-supported vector all of whose blocks vanish is zero.
  exact Work.ORP311.eq_zero_of_blk_eq_zero n m hwin key

end Work.ORP311
