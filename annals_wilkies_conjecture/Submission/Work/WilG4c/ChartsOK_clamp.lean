import Mathlib
import Submission.Work.WilG4c.FLemAPI
import Submission.Work.WilG4c.Defs

namespace Work.WilG4c

/-- Generalized `ChartsOK` extension ("clamp" over a definable parameter set).  Given charts
`Φ` that are `ChartsOK` on `Λ ∩ Λ'`, and a modification `mod` that is the identity on `Λ'` and
the constant `c` outside `Λ'` (with `c` in the open cube), whose components still have
`Ω`-bounded graphs, the modified charts are `ChartsOK` on all of `Λ`; their number does not
increase.  This is `Work.WilG4c.PerLambda.ChartsOK_extends` with the validity hypothesis
weakened from `Λ'` to `Λ ∩ Λ'`. -/
theorem ChartsOK_clamp {S : WilkiesDesign.SOMin} {p n k a Dg r : ℕ}
    {Λ Λ' : Set (Fin p → ℝ)} {F : Work.WilkG4c.Family k p n}
    {Φ : Finset (Work.WilkG4c.ChartTuple p n)} {c : Fin n → ℝ}
    (hc : c ∈ WilkiesDesign.openCube n) (hval : Work.WilkG4c.ValuesIn01 Λ F)
    (mod : Work.WilkG4c.ChartTuple p n → Work.WilkG4c.ChartTuple p n)
    (hmod : ∀ φ j l, l ∈ Λ' → ∀ t : Fin n → ℝ, mod φ j l t = φ j l t)
    (hmodc : ∀ φ j l, l ∉ Λ' → ∀ t : Fin n → ℝ, mod φ j l t = c j)
    (hΩ : ∀ φ ∈ Φ, ∀ j : Fin n, WilkiesDesign.CG.famGraph ((mod φ) j) ∈ S.Ω a Dg (p + n + 1))
    (h : ∀ φ ∈ Φ, ∀ l, l ∈ Λ ∩ Λ' →
      (∀ t ∈ WilkiesDesign.openCube n, (fun j => φ j l t) ∈ WilkiesDesign.openCube n) ∧
      ∀ i, ContDiffOn ℝ r (fun t => F i l (fun j => φ j l t)) (WilkiesDesign.openCube n) ∧
        ∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube n,
          ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖ ≤ 1) :
    ∃ Φ' : Finset (Work.WilkG4c.ChartTuple p n),
      (∀ φ ∈ Φ, mod φ ∈ Φ') ∧ Φ'.card ≤ Φ.card ∧
      Work.WilkG4c.ChartsOK S a Dg r Λ F Φ' := by
  classical
  -- Take `Φ'` to be the image of `Φ` under `mod`; this preserves the cardinality bound and
  -- contains every modified chart.
  refine ⟨Φ.image mod, ?_, Finset.card_image_le, ?_⟩
  · intro φ hφ
    exact Finset.mem_image_of_mem mod hφ
  · rw [Work.WilkG4c.ChartsOK]
    intro φ' hφ'
    rw [Finset.mem_image] at hφ'
    obtain ⟨φ, hφ, rfl⟩ := hφ'
    refine ⟨fun j => hΩ φ hφ j, ?_⟩
    intro l hl
    by_cases hl' : l ∈ Λ'
    · -- On `Λ'` the modification is the identity, so the hypotheses for `φ` transfer verbatim.
      obtain ⟨hcube, hrest⟩ := h φ hφ l ⟨hl, hl'⟩
      have hpt : ∀ t : Fin n → ℝ, (fun j => mod φ j l t) = (fun j => φ j l t) :=
        fun t => funext (fun j => hmod φ j l hl' t)
      have hfun : ∀ i, (fun t : Fin n → ℝ => F i l (fun j => mod φ j l t))
          = (fun t : Fin n → ℝ => F i l (fun j => φ j l t)) :=
        fun i => funext (fun t => by congr 1; funext j; exact hmod φ j l hl' t)
      refine ⟨fun t ht => by rw [hpt t]; exact hcube t ht, ?_⟩
      intro i
      constructor
      · rw [hfun i]; exact (hrest i).1
      · intro m hm t ht
        rw [hfun i]; exact (hrest i).2 m hm t ht
    · -- Off `Λ'` the modified chart is the constant map `c`, whose composite with `F` is the
      -- constant function `F i l c`; constancy gives the `C^r` regularity and the norm bound.
      have hconst : ∀ t : Fin n → ℝ, (fun j => mod φ j l t) = c :=
        fun t => funext (fun j => hmodc φ j l hl' t)
      refine ⟨fun t ht => by rw [hconst t]; exact hc, ?_⟩
      intro i
      have hfun : (fun t : Fin n → ℝ => F i l (fun j => mod φ j l t))
          = (fun _ : Fin n → ℝ => F i l c) :=
        funext (fun t => by rw [hconst t])
      constructor
      · rw [hfun]; exact contDiffOn_const
      · intro m hm t ht
        rw [hfun]
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · rw [h0, norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hval i l hl c hc).1]
          exact le_of_lt (hval i l hl c hc).2
        · rw [iteratedFDeriv_const_of_ne (ne_of_gt hpos) (F i l c)]
          simp

end Work.WilG4c
