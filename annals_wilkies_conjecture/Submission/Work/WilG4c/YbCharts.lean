/-
  WilG4c — `YbCharts`: charts for the family of `n+1` variables, in the *sliced* spelling.

  Given the induction hypothesis `ih : ∀ q, FLem S q n` (the F-lemma at cube dimension `n`, for
  every parameter dimension `q`), and a family `F` of `n+1` variables whose graphs are
  `Ω`-bounded, we produce a finite set of charts of the `n`-cube, parameterised by `(l, x)`
  (`Fin (p+1) → ℝ`) with `l ∈ Λ`, `x ∈ I`, which

  * have `Ω`-bounded graphs,
  * send the cube into the cube,
  * make the composites `t ↦ F i l (x, ψ(·)(l,x,t))` `C^r` on the cube with all jet norms `≤ 1`,
  * and cover, for each `(l,x,y)`, the value `F i l (x, y)` to within `ε/2`.

  This is nothing but the F-lemma at dimension `n` applied to the *pinned* (sliced) family
  `pinFam p n (F i) : (Fin (p+1) → ℝ) → (Fin n → ℝ) → ℝ`,
  `pinFam p n (F i) (l, x) y = F i l (Fin.cons x y)`
  (`Work.WilkG4c.pinFam`), whose graph is `Ω`-bounded because moving the distinguished cube
  coordinate into the parameter block is a pure relabelling of the ambient coordinates
  (`Work.WilkG4c.pinFam_famGraph_mem`): no format or degree is paid.
-/
import Mathlib
import Submission.Work.WilG4c.Hyps
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.pinFam_famGraph_mem

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

set_option autoImplicit false
noncomputable section
open Classical

theorem YbCharts (S : WilkiesDesign.SOMin) (n p : ℕ)
    (ih : ∀ q, WilkiesDesign.CG.FLem S q n) (F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Work.WilkG4c.Family k p (n + 1)),
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        Work.WilkG4c.ValuesIn01 Λ F →
        ∃ Ξ : Finset (Work.WilkG4c.ChartTuple (p + 1) n),
          (Ξ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c ∧
            (∀ ψ ∈ Ξ,
              (∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈
                S.Ω a (MvPolynomial.eval ![D, r] b) ((p + 1) + n + 1)) ∧
              (∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ t ∈ WilkiesDesign.openCube n,
                (fun j => ψ j (Fin.snoc l x) t) ∈ WilkiesDesign.openCube n) ∧
              (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I,
                ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
                  (WilkiesDesign.openCube n)) ∧
              (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube n,
                ‖iteratedFDeriv ℝ m
                    (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1)) ∧
            (∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n,
              ∃ ψ ∈ Ξ, ∃ t ∈ WilkiesDesign.openCube n,
                ∀ i, |F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) -
                  F i l (Fin.cons x y)| < ε / 2) := by
  obtain ⟨a₁, b₁, c₁, H⟩ := ih (p + 1) F0
  refine ⟨a₁, b₁, c₁, ?_⟩
  intro D r k ε hε hε1 Λ F hΩ hval
  -- The parameter set of the sliced family: `(l, x)` with `l ∈ Λ` and `x ∈ I`.
  set Λ' : Set (Fin (p + 1) → ℝ) :=
    {u | (fun i : Fin p => u (Fin.castSucc i)) ∈ Λ ∧ u (Fin.last p) ∈ Work.WilkG4c.I} with hΛ'
  -- `pinFam p n (F i)` at the parameter `Fin.snoc l x` is the slice `y ↦ F i l (Fin.cons x y)`.
  have hGsnoc : ∀ (i : Fin k) (l : Fin p → ℝ) (x : ℝ),
      Work.WilkG4c.pinFam p n (F i) (Fin.snoc l x) = fun y => F i l (Fin.cons x y) := by
    intro i l x
    funext y
    rw [Work.WilkG4c.pinFam_snoc]
    exact Work.WilkG4c.slice_apply (F i l) x y
  have hmemΛ' : ∀ (l : Fin p → ℝ) (x : ℝ), l ∈ Λ → x ∈ Work.WilkG4c.I →
      Fin.snoc l x ∈ Λ' := by
    intro l x hl hx
    rw [hΛ']
    refine ⟨?_, ?_⟩
    · simpa only [Fin.snoc_castSucc] using hl
    · simpa only [Fin.snoc_last] using hx
  have hΩG : ∀ i, WilkiesDesign.CG.famGraph (Work.WilkG4c.pinFam p n (F i)) ∈
      S.Ω F0 D ((p + 1) + n + 1) :=
    fun i => Work.WilkG4c.pinFam_famGraph_mem S p n F0 D (F i) (hΩ i)
  have hvalG : ∀ i, ∀ u ∈ Λ', ∀ y ∈ WilkiesDesign.openCube n,
      Work.WilkG4c.pinFam p n (F i) u y ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i u hu y hy
    rw [hΛ'] at hu
    obtain ⟨huΛ, huI⟩ := hu
    have hmem : Fin.cons (u (Fin.last p)) y ∈ WilkiesDesign.openCube (n + 1) := by
      intro j
      induction j using Fin.cases with
      | zero => simpa [Work.WilkG4c.I] using huI
      | succ j => simpa using hy j
    have h := hval i (fun i : Fin p => u (Fin.castSucc i)) huΛ
      (Fin.cons (u (Fin.last p)) y) hmem
    simpa only [Work.WilkG4c.pinFam_apply] using h
  obtain ⟨Ξ, hΞcard, hΞok, hΞcov⟩ :=
    H D r k (ε / 2) (by linarith) (by linarith) Λ'
      (fun i => Work.WilkG4c.pinFam p n (F i)) hΩG hvalG
  refine ⟨Ξ, hΞcard, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨hA, hB⟩ := hΞok ψ hψ
    refine ⟨hA, ?_, ?_, ?_⟩
    · intro l hl x hx t ht
      exact (hB (Fin.snoc l x) (hmemΛ' l x hl hx)).1 t ht
    · intro i l hl x hx
      have h := ((hB (Fin.snoc l x) (hmemΛ' l x hl hx)).2 i).1
      have hfun : (fun t : Fin n → ℝ => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          = (fun t : Fin n → ℝ => Work.WilkG4c.pinFam p n (F i) (Fin.snoc l x)
              (fun j => ψ j (Fin.snoc l x) t)) := by
        funext t; rw [hGsnoc i l x]
      rw [hfun]; exact h
    · intro i l hl x hx m hm t ht
      have h := (((hB (Fin.snoc l x) (hmemΛ' l x hl hx)).2 i).2 m hm) t ht
      have hfun : (fun t : Fin n → ℝ => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
          = (fun t : Fin n → ℝ => Work.WilkG4c.pinFam p n (F i) (Fin.snoc l x)
              (fun j => ψ j (Fin.snoc l x) t)) := by
        funext t; rw [hGsnoc i l x]
      rw [hfun]; exact h
  · intro l hl x hx y hy
    obtain ⟨φ, hφ, t, ht, hcov⟩ := hΞcov (Fin.snoc l x) (hmemΛ' l x hl hx) y hy
    refine ⟨φ, hφ, t, ht, ?_⟩
    intro i
    have h := hcov i
    simp only [hGsnoc i l x] at h
    exact h

end

end Work.WilG4c
