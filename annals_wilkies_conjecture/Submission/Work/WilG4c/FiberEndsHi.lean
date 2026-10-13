/-
  WilG4c — `Ω`-membership of the *upper* fibre-end set `A_hi` (BNZ §2.3).

  This is the exact mirror of `Work.WilG4c.FiberEndsA.A_lo_mem`: `A_hi` is
  `(NE1 ∩ UB1 ∩ LUB1) ∪ (NE1ᶜ ∩ yZero)` with

  * `NE1 = projLast (pull2 p Z)`                                (format `a1 + 1`, degree `D+2`),
  * `UB1 = (projLast (pull2 p Z ∩ midLtLast p))ᶜ`               (degree `(D+2) + 3`),
  * `LUB1 = (projLast ((projLast (pull3 p Z ∩ midLtLast3 p))ᶜ ∩ lastLtMid p))ᶜ`
                                                                (degree `((D+2)+3) + 3`),
  * `yZero`                                                     (degree `1`),

  so the total degree is `(D+2) + ((D+2)+3) + (((D+2)+3)+3) + ((D+2)+1) ≤ 100*D + 1000`, while
  the format is a function of `p` and `F0` alone (each of the finitely many `SOMin` operations
  bumps it by a fixed amount).  Every ingredient is one of `Work.WilG4c.Subst` (the substitution
  atom, degree `+2`), `Work.WilG1.Calc.lt_mem` (a coordinate comparison, degree `3`),
  `SOMin.proj`, `SOMin.compl`, `SOMin.hyp` and `Work.WilG0.Omega_inter2`/`Omega_union2` (which
  *add* degrees).
-/
import Mathlib
import Submission.Work.WilG4c.FiberEndsDefs
import Submission.Work.WilG4c.Subst
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Calc.lt_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-- `A_hi p Z` is `Ω`-definable, with a format depending on `p, F0` and a degree at most
`100*D + 1000`.  (Sibling of `Work.WilG4c.FiberEndsA.A_hi_mem`, proved here so that
`StepFiberEnds` has no unfinished dependency.) -/
theorem A_hi_mem_alt (S : WilkiesDesign.SOMin) (p F0 : ℕ) :
    ∃ a : ℕ, ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F0 D (p + 1) →
      A_hi p Z ∈ S.Ω a (100 * D + 1000) (p + 1) := by
  let a1 : ℕ := max (F0 + (p + 2)) ((p + 2) + (p + 1)) + 1 + (p + 1)
  let a3 : ℕ := max (F0 + (p + 3)) ((p + 3) + (p + 1)) + 1 + (p + 1)
  let FNE1 : ℕ := a1 + 1
  let FUBb : ℕ := (max a1 (p + 2 + 3) + 1) + 1
  let FUB1 : ℕ := FUBb + 1
  let G0 : ℕ := max a3 (p + 3 + 3) + 1
  let G2 : ℕ := (G0 + 1) + 1
  let G3 : ℕ := max G2 (p + 2 + 3) + 1
  let FLUBb : ℕ := G3 + 1
  let FLUB1 : ℕ := FLUBb + 1
  let F1 : ℕ := max (max FNE1 FUB1 + 1) FLUB1 + 1
  let F2 : ℕ := max (FNE1 + 1) (p + 1) + 1
  refine ⟨max F1 F2, ?_⟩
  intro D Z hZ
  -- the two pullbacks of `Z`
  have hpull2 : pull2 p Z ∈ S.Ω a1 (D + 2) (p + 2) :=
    Work.WilG4c.Subst S (iota1 p) hZ
  have hpull3 : pull3 p Z ∈ S.Ω a3 (D + 2) (p + 3) :=
    Work.WilG4c.Subst S (iota2 p) hZ
  -- `NE1`
  have hNE1 : NE1 p Z ∈ S.Ω FNE1 (D + 2) (p + 1) := S.proj hpull2
  -- the coordinate comparisons
  have hmid2 : midLtLast p ∈ S.Ω (p + 2 + 3) 3 (p + 2) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 2) D
      (Fin.castSucc (Fin.last p)) (Fin.last (p + 1))
    have h' : midLtLast p ∈ S.Ω (p + 2 + 3) ((Polynomial.C 3).eval D) (p + 2) := by
      simpa only [midLtLast] using h
    exact Work.WilG1.Omega.mono h' le_rfl (by rw [Polynomial.eval_C])
  have hlt2 : lastLtMid p ∈ S.Ω (p + 2 + 3) 3 (p + 2) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 2) D
      (Fin.last (p + 1)) (Fin.castSucc (Fin.last p))
    have h' : lastLtMid p ∈ S.Ω (p + 2 + 3) ((Polynomial.C 3).eval D) (p + 2) := by
      simpa only [lastLtMid] using h
    exact Work.WilG1.Omega.mono h' le_rfl (by rw [Polynomial.eval_C])
  have hmid3 : midLtLast3 p ∈ S.Ω (p + 3 + 3) 3 (p + 3) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 3) D
      (Fin.castSucc (Fin.last (p + 1))) (Fin.last (p + 2))
    have h' : midLtLast3 p ∈ S.Ω (p + 3 + 3) ((Polynomial.C 3).eval D) (p + 3) := by
      simpa only [midLtLast3] using h
    exact Work.WilG1.Omega.mono h' le_rfl (by rw [Polynomial.eval_C])
  -- `UB1 = (projLast (pull2 Z ∩ midLtLast))ᶜ`
  have hUBb : UBb p Z ∈ S.Ω FUBb ((D + 2) + 3) (p + 1) :=
    S.proj (Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hpull2)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hmid2))
  have hUB1 : UB1 p Z ∈ S.Ω FUB1 ((D + 2) + 3) (p + 1) := S.compl hUBb
  -- `LUB1 = (projLast ((projLast (pull3 Z ∩ midLtLast3))ᶜ ∩ lastLtMid))ᶜ`
  have hprojlt3 : WilkiesDesign.projLast (pull3 p Z ∩ midLtLast3 p) ∈
      S.Ω (G0 + 1) ((D + 2) + 3) (p + 2) :=
    S.proj (Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hpull3)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hmid3))
  have hG2 : (WilkiesDesign.projLast (pull3 p Z ∩ midLtLast3 p))ᶜ ∈
      S.Ω G2 ((D + 2) + 3) (p + 2) := S.compl hprojlt3
  have hLUBb : LUBb p Z ∈ S.Ω FLUBb (((D + 2) + 3) + 3) (p + 1) :=
    S.proj (Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hG2)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hlt2))
  have hLUB1 : LUB1 p Z ∈ S.Ω FLUB1 (((D + 2) + 3) + 3) (p + 1) := S.compl hLUBb
  -- the first disjunct `NE1 ∩ UB1 ∩ LUB1`
  have hpart1 : (NE1 p Z ∩ UB1 p Z ∩ LUB1 p Z) ∈
      S.Ω F1 ((D + 2) + ((D + 2) + 3) + (((D + 2) + 3) + 3)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _)
        (Work.WilG0.Omega_inter2 (S := S)
          (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hNE1)
          (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hUB1)))
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hLUB1)
  -- the second disjunct `NE1ᶜ ∩ yZero`
  have hyZero : yZero p ∈ S.Ω (p + 1) 1 (p + 1) := by
    have h := S.hyp (p + 1) (MvPolynomial.X (Fin.last p))
    simpa [yZero, MvPolynomial.totalDegree_X] using h
  have hpart2 : ((NE1 p Z)ᶜ ∩ yZero p) ∈ S.Ω F2 ((D + 2) + 1) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) (S.compl hNE1))
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hyZero)
  -- union
  have hun : ((NE1 p Z ∩ UB1 p Z ∩ LUB1 p Z) ∪ ((NE1 p Z)ᶜ ∩ yZero p)) ∈
      S.Ω (max F1 F2)
        (((D + 2) + ((D + 2) + 3) + (((D + 2) + 3) + 3)) + ((D + 2) + 1)) (p + 1) :=
    Work.WilG0.Omega_union2 (S := S)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_left _ _) hpart1)
      (Work.WilG0.Omega_mono_F (S := S) (le_max_right _ _) hpart2)
  have hdeg : ((D + 2) + ((D + 2) + 3) + (((D + 2) + 3) + 3)) + ((D + 2) + 1) ≤
      100 * D + 1000 := by omega
  exact Work.WilG0.Omega_mono_D (S := S) hdeg hun

/-! ## The upper fibre end: graph identity and exactness

The exact mirror of `graphOf_loOf_eq`/`loOf_props` (in `FiberEndsLo`) for the supremum: on a
nonempty fibre `hiOf p Z l = sSup (Z_l)`, which is an upper bound of the fibre and is sharp.
Proved here (rather than imported from the sibling module) so that `StepFiberEnds` rests only on
frozen modules. -/

/-- `A_hi p Z` is the graph of the pointwise supremum of the fibre, and that supremum is an
upper bound of the fibre which every smaller number fails to bound. -/
theorem hiOf_graph_props_alt (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ Set.Ioo (0 : ℝ) 1) :
    graphOf (hiOf p Z) = A_hi p Z ∧
      ∀ l : Fin p → ℝ, (∃ x : ℝ, Fin.snoc l x ∈ Z) →
        (∀ x : ℝ, Fin.snoc l x ∈ Z → x ≤ hiOf p Z l) ∧
        (∀ u : ℝ, u < hiOf p Z l → ∃ x : ℝ, Fin.snoc l x ∈ Z ∧ u < x) := by
  -- Every fibre value lies in `(0,1)`, by hypothesis.
  have hfib : ∀ l x, Fin.snoc l x ∈ Z → x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro l x hx
    have := hI (Fin.snoc l x) hx
    simpa [Fin.snoc_last] using this
  -- Hence every fibre is bounded above.
  have hbdd : ∀ l, BddAbove (fibre p Z l) := by
    intro l
    refine ⟨1, ?_⟩
    intro x hx
    exact le_of_lt (hfib l x hx).2
  -- The key characterisation: `Fin.snoc l y ∈ A_hi p Z ↔ y = hiOf p Z l`.
  have key : ∀ (l : Fin p → ℝ) (y : ℝ),
      Fin.snoc l y ∈ A_hi p Z ↔ y = hiOf p Z l := by
    intro l y
    rw [mem_A_hi_snoc]
    by_cases hne : (fibre p Z l).Nonempty
    · rw [hiOf, if_pos hne]
      constructor
      · rintro (⟨_, hub, hlub⟩ | ⟨hne', _⟩)
        · apply le_antisymm
          · exact hlub _ (fun t ht => le_csSup (hbdd l) ht)
          · exact csSup_le hne hub
        · exact absurd hne hne'
      · intro hy
        refine Or.inl ⟨hne, ?_, ?_⟩
        · intro t ht
          rw [hy]
          exact le_csSup (hbdd l) ht
        · intro u hu
          rw [hy]
          exact csSup_le hne hu
    · rw [hiOf, if_neg hne]
      constructor
      · rintro (⟨hne', _⟩ | ⟨_, hy⟩)
        · exact absurd hne' hne
        · exact hy
      · intro hy
        exact Or.inr ⟨hne, hy⟩
  refine ⟨?_, ?_⟩
  · ext z
    rw [graphOf]
    simp only [Set.mem_ofPred_eq]
    rw [← key (Fin.init z) (z (Fin.last p)), Fin.snoc_init_self]
  · intro l hne
    have hne' : (fibre p Z l).Nonempty := hne
    rw [hiOf, if_pos hne']
    refine ⟨?_, ?_⟩
    · intro x hx
      exact le_csSup (hbdd l) hx
    · intro u hu
      obtain ⟨x, hx, hux⟩ := exists_lt_of_lt_csSup hne hu
      exact ⟨x, hx, hux⟩

end Work.WilG4c
