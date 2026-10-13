import Mathlib
import Submission.Work.WilG4c.EngineDefs
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.GraphOfComp
import Submission.Work.WilG4c.FamGraphPad
import Submission.Work.WilG4c.FamGraphPolyComb
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- The unfolding of `flatFun` at a point. -/
theorem flatFun_apply' {p m : ℕ} (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) (x : Fin (p + m) → ℝ) :
    Work.WilkG4c.flatFun f x = f (fun i => x (Fin.castAdd m i)) (fun j => x (Fin.natAdd p j)) :=
  rfl

/-- **Padding by a dummy trailing coordinate.**  If `famGraph g ⊆ ℝ^{p+n+1}` is `Ω`-definable
at format `F` and degree `D`, then the graph of `(l, t) ↦ g l (Fin.init t)` (the same family on
`n+1` coordinates, ignoring the last one) is `Ω`-definable at format `F + a` and degree `D + c`
with `a, c` depending only on `p, n`. -/
theorem famGraph_pad_aux (S : SOMin) (p n : ℕ) : ∃ (a c : ℕ),
    ∀ (F D : ℕ) (g : (Fin p → ℝ) → (Fin n → ℝ) → ℝ),
      famGraph g ∈ S.Ω F D (p + n + 1) →
      famGraph (fun l (t : Fin (n + 1) → ℝ) => g l (Fin.init t)) ∈
        S.Ω (F + a) (D + c) (p + (n + 1) + 1) := by
  refine ⟨2 * ((p + (n + 1) + 1) + (p + n + 1)) + 1, 2, ?_⟩
  intro F D g hg
  have hmem : {x : Fin (p + (n + 1) + 1) → ℝ | x ∘ padSig p n ∈ famGraph g} ∈
      S.Ω (F + (2 * ((p + (n + 1) + 1) + (p + n + 1)) + 1)) (D + 2) (p + (n + 1) + 1) :=
    GraphComp.subst_mem S (padSig p n) hg
  rw [← famGraph_padSig_eq p n g] at hmem
  simpa using hmem

/-- The polynomial `(y₀, y₁, y₂) ↦ y₀ + (y₂ - 1/2)(2 y₁ - 1/2)`. -/
noncomputable def combP : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.X 0 + (MvPolynomial.X 2 - MvPolynomial.C (1 / 2 : ℝ)) *
    (MvPolynomial.C 2 * MvPolynomial.X 1 - MvPolynomial.C (1 / 2 : ℝ))

theorem combP_totalDegree : combP.totalDegree ≤ 2 := by
  have hA : (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 2 := by
    simp [MvPolynomial.totalDegree_X]
  have hB1 : (MvPolynomial.X (2 : Fin 3) - MvPolynomial.C (1 / 2 : ℝ) :
      MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  have hB2 : (MvPolynomial.C (2 : ℝ) * MvPolynomial.X (1 : Fin 3) -
      MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    constructor
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    · simp [MvPolynomial.totalDegree_C]
  rw [combP]
  refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
  rw [max_le_iff]
  exact ⟨hA, le_trans (MvPolynomial.totalDegree_mul _ _) (by omega)⟩

/-- **`Ω`-definability of the per-cell chart.**  If the `n` coordinates of the base
parametrisation `χ`, the midpoint `M`, the half-width `W` and the coordinates of the `n`-cube
chart `ψ` all have `Ω`-bounded graphs, then so does every coordinate of the chart
`(l, (t,ζ)) ↦ (χ (ψ l t), M (ψ l t) + (ζ - 1/2) (2 W (ψ l t) - 1/2))` of the `(n+1)`-cube, with
a format gain and a degree that are linear in the data. -/
theorem EngineChartMem (S : SOMin) (p n F0 : ℕ) : ∃ (A C : ℕ),
    ∀ (D : ℕ) (χ ψ : (Fin p → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
      (M W : (Fin p → ℝ) → (Fin n → ℝ) → ℝ),
      (∀ j : Fin n, famGraph (fun l u => χ l u j) ∈ S.Ω F0 D (p + n + 1)) →
      famGraph M ∈ S.Ω F0 D (p + n + 1) →
      famGraph W ∈ S.Ω F0 D (p + n + 1) →
      (∀ j : Fin n, famGraph (fun l u => ψ l u j) ∈ S.Ω F0 D (p + n + 1)) →
      ∀ j : Fin (n + 1),
        famGraph (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
          Work.WilG4c.cellChart χ M W ψ l z j) ∈ S.Ω (F0 + A) (C * D + C) (p + (n + 1) + 1) := by
  obtain ⟨aPad, cPad, hPad⟩ := famGraph_pad_aux S p n
  obtain ⟨aComp, cComp, hComp⟩ := Work.WilkG4c.famGraph_comp_single S p n
  obtain ⟨aPoly, cPoly, hPoly⟩ := FamGraphPolyComb S (p + (n + 1)) 3
  have hPdeg : combP.totalDegree ≤ 2 := combP_totalDegree
  set A : ℕ := 3 * F0 + 2 * aComp + 3 * aPad + aPoly + (p + (n + 1) + 1) + 2 * cComp + 2 * cPad + 10
    with hA
  set C : ℕ := cPoly * (2 * (p + n + 1)) + (cPoly * (2 * (cComp + cPad) + 3) + cPoly)
      + (cComp + cPad) + (p + n + 1) + 1 with hC
  refine ⟨A, C, ?_⟩
  intro D χ ψ M W hχ hM hW hψ j
  -- degree bound in the first case
  have hDA : (D + (p + n) * D + cComp) + cPad ≤ C * D + C := by
    have hp1 : p + n + 1 ≤ C := by rw [hC]; omega
    have hc1 : cComp + cPad ≤ C := by rw [hC]; omega
    have he : (D + (p + n) * D + cComp) + cPad = (p + n + 1) * D + (cComp + cPad) := by ring
    rw [he]
    exact add_le_add (Nat.mul_le_mul_right D hp1) hc1
  -- format bound in the first case
  have hFA : (F0 + F0 + aComp) + aPad ≤ F0 + A := by rw [hA]; omega
  by_cases hjn : (j : ℕ) = n
  · -- second case: j is the last coordinate
    have hjlast : j = Fin.last n := Fin.ext hjn
    rw [hjlast]
    have hfun : (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) =>
          cellChart χ M W ψ l z (Fin.last n))
        = fun l z => M l (ψ l (Fin.init z)) + (z (Fin.last n) - 1 / 2) *
            (2 * W l (ψ l (Fin.init z)) - 1 / 2) := by
      funext l z
      simp only [cellChart]
      rw [dif_pos (show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl)]
    -- composition with ψ
    have hcM := hComp F0 F0 D D M (fun i l u => ψ l u i) hM (fun i => hψ i)
    have hcW := hComp F0 F0 D D W (fun i l u => ψ l u i) hW (fun i => hψ i)
    -- padding
    have hpM := hPad (F0 + F0 + aComp) (D + (p + n) * D + cComp)
      (fun l u => M l (ψ l u)) hcM
    have hpW := hPad (F0 + F0 + aComp) (D + (p + n) * D + cComp)
      (fun l u => W l (ψ l u)) hcW
    -- the coordinate projection
    have hcoord : famGraph (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) => z (Fin.last n)) ∈
        S.Ω (p + (n + 1) + 1) 1 (p + (n + 1) + 1) := by
      rw [Work.WilkG4c.famGraph_eq_graphOf_flatFun]
      have h := Work.WilkG4c.graphOf_coord_mem S (Fin.natAdd p (Fin.last n))
      convert h using 2
      funext x
      simp [flatFun_apply']
    -- the data of the polynomial combination
    set Ffun : Fin 3 → ℕ := fun i => if (i : ℕ) = 2 then (p + (n + 1) + 1)
      else (F0 + F0 + aComp) + aPad with hFfun
    set Dfun : Fin 3 → ℕ := fun i => if (i : ℕ) = 2 then 1
      else (D + (p + n) * D + cComp) + cPad with hDfun
    set H : Fin 3 → (Fin (p + (n + 1)) → ℝ) → ℝ := fun i =>
      if (i : ℕ) = 0 then Work.WilkG4c.flatFun (fun l z => M l (ψ l (Fin.init z)))
      else if (i : ℕ) = 1 then Work.WilkG4c.flatFun (fun l z => W l (ψ l (Fin.init z)))
      else Work.WilkG4c.flatFun (fun l z => z (Fin.last n)) with hH
    have hHmem : ∀ i : Fin 3, graphOf (H i) ∈ S.Ω (Ffun i) (Dfun i) (p + (n + 1) + 1) := by
      intro i
      fin_cases i
      · exact hpM
      · exact hpW
      · exact hcoord
    have hpoly := hPoly Ffun Dfun H combP hHmem
    -- identify the function
    have hflat : (fun x : Fin (p + (n + 1)) → ℝ => MvPolynomial.eval (fun i => H i x) combP)
        = Work.WilkG4c.flatFun (fun l z => M l (ψ l (Fin.init z)) +
            (z (Fin.last n) - 1 / 2) * (2 * W l (ψ l (Fin.init z)) - 1 / 2)) := by
      funext x
      rw [hH]
      simp only [combP, MvPolynomial.eval_add, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_C]
      norm_num
      simp only [Work.WilkG4c.flatFun]
    -- format bound
    have hFB : (∑ i : Fin 3, Ffun i) + aPoly ≤ F0 + A := by
      have hs : (∑ i : Fin 3, Ffun i)
          = ((F0 + F0 + aComp) + aPad) + ((F0 + F0 + aComp) + aPad) + (p + (n + 1) + 1) := by
        rw [Fin.sum_univ_three]; simp [Ffun]
      rw [hs, hA]; omega
    -- degree bound
    have hDB : cPoly * ((∑ i : Fin 3, Dfun i) + combP.totalDegree) + cPoly ≤ C * D + C := by
      have hsum : (∑ i : Fin 3, Dfun i) = 2 * ((p + n + 1) * D + (cComp + cPad)) + 1 := by
        have h1 : Dfun 0 = (D + (p + n) * D + cComp) + cPad := by simp [Dfun]
        have h2 : Dfun 1 = (D + (p + n) * D + cComp) + cPad := by simp [Dfun]
        have h3 : Dfun 2 = 1 := by simp [Dfun]
        rw [Fin.sum_univ_three, h1, h2, h3]
        have he : (D + (p + n) * D + cComp) + cPad = (p + n + 1) * D + (cComp + cPad) := by ring
        rw [he]; ring
      have hDb : (∑ i : Fin 3, Dfun i) + combP.totalDegree
          ≤ 2 * (p + n + 1) * D + 2 * (cComp + cPad) + 3 := by
        rw [hsum]
        have : 2 * ((p + n + 1) * D + (cComp + cPad)) + 1 + combP.totalDegree
            ≤ 2 * ((p + n + 1) * D + (cComp + cPad)) + 1 + 2 := by omega
        calc 2 * ((p + n + 1) * D + (cComp + cPad)) + 1 + combP.totalDegree
            ≤ 2 * ((p + n + 1) * D + (cComp + cPad)) + 1 + 2 := this
          _ = 2 * (p + n + 1) * D + 2 * (cComp + cPad) + 3 := by ring
      have hcoef : cPoly * (2 * (p + n + 1)) ≤ C := by rw [hC]; omega
      have hconst : cPoly * (2 * (cComp + cPad) + 3) + cPoly ≤ C := by rw [hC]; omega
      have h2' : cPoly * ((∑ i : Fin 3, Dfun i) + combP.totalDegree) + cPoly
          ≤ cPoly * (2 * (p + n + 1) * D + 2 * (cComp + cPad) + 3) + cPoly :=
        add_le_add (Nat.mul_le_mul_left cPoly hDb) le_rfl
      have h3' : cPoly * (2 * (p + n + 1) * D + 2 * (cComp + cPad) + 3) + cPoly ≤ C * D + C := by
        have he : cPoly * (2 * (p + n + 1) * D + 2 * (cComp + cPad) + 3) + cPoly
            = cPoly * (2 * (p + n + 1)) * D + (cPoly * (2 * (cComp + cPad) + 3) + cPoly) := by
          ring
        rw [he]
        exact add_le_add (Nat.mul_le_mul_right D hcoef) hconst
      exact le_trans h2' h3'
    -- conclude
    have hmemB : famGraph (fun l z => M l (ψ l (Fin.init z)) +
        (z (Fin.last n) - 1 / 2) * (2 * W l (ψ l (Fin.init z)) - 1 / 2)) ∈
        S.Ω ((∑ i : Fin 3, Ffun i) + aPoly)
          (cPoly * ((∑ i : Fin 3, Dfun i) + combP.totalDegree) + cPoly) (p + (n + 1) + 1) := by
      rw [Work.WilkG4c.famGraph_eq_graphOf_flatFun, ← hflat]
      exact hpoly
    rw [hfun]
    exact Work.WilG1.Omega.mono hmemB hFB hDB
  · -- first case: j is not the last coordinate
    have hjlt : (j : ℕ) < n := by have := j.isLt; omega
    have hfun : (fun (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) => cellChart χ M W ψ l z j)
        = fun l z => χ l (ψ l (Fin.init z)) ⟨(j : ℕ), hjlt⟩ := by
      funext l z
      simp only [cellChart]
      rw [dif_neg hjn]
    have hχj : famGraph (fun l u => χ l u ⟨(j : ℕ), hjlt⟩) ∈ S.Ω F0 D (p + n + 1) :=
      hχ ⟨(j : ℕ), hjlt⟩
    have hc := hComp F0 F0 D D (fun l u => χ l u ⟨(j : ℕ), hjlt⟩)
      (fun i l u => ψ l u i) hχj (fun i => hψ i)
    have hp := hPad (F0 + F0 + aComp) (D + (p + n) * D + cComp)
      (fun l u => χ l (ψ l u) ⟨(j : ℕ), hjlt⟩) hc
    rw [hfun]
    exact Work.WilG1.Omega.mono hp hFA hDA

end Work.WilG4c
