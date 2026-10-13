import Mathlib
import Submission.Work.WilkG4c.ExactCellDefs
import Submission.Work.WilG4c.graphOfLinComb_mem
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG1.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG0 Work.WilG1

/-- **`Ω`-bound for the graph of the per-cell chart.**  The chart `chartVal g α β` has
`Ω`-bounded graph, with a format depending only on `F0, F1, p` and a degree polynomial in
`D, D1`; the bookkeeping follows `graphOfLinComb_mem` and `graphOfCompGen` with the explicit
constants `aLC, cLC, cCG1, cCG2`. -/
theorem exactCell_graph (S : SOMin) (p : ℕ) (aLC cLC cCG1 cCG2 : ℕ)
    (hLC : ∀ (F₁ F₂ F₃ D₁ D₂ D₃ : ℕ) (A B T : (Fin (p + 1) → ℝ) → ℝ),
      graphOf A ∈ S.Ω F₁ D₁ (p + 1 + 1) → graphOf B ∈ S.Ω F₂ D₂ (p + 1 + 1) →
      graphOf T ∈ S.Ω F₃ D₃ (p + 1 + 1) →
      graphOf (fun x => A x + T x * (B x - A x)) ∈
        S.Ω (F₁ + F₂ + F₃ + aLC) (D₁ + D₂ + D₃ + cLC) (p + 1 + 1))
    (hCG : ∀ (F₁ F₂ D₁ D₂ : ℕ) (G : (Fin (p + 1) → ℝ) → ℝ)
        (Φ : (Fin (p + 1) → ℝ) → (Fin (p + 1) → ℝ)),
      graphOf G ∈ S.Ω F₁ D₁ (p + 1 + 1) →
      (∀ j : Fin (p + 1), graphOf (fun x => Φ x j) ∈ S.Ω F₂ D₂ (p + 1 + 1)) →
      graphOf (G ∘ Φ) ∈ S.Ω (F₁ + F₂ + cCG1) (D₁ + (p + 1) * D₂ + cCG2) (p + 1 + 1))
    (D D1 aE2 aE3 : ℕ) (bE2 b2' bE3 b3' : MvPolynomial (Fin 2) ℕ)
    (α β : (Fin p → ℝ) → ℝ) (g : (Fin (p + 1) → ℝ) → ℝ)
    (hα : graphOf α ∈ S.Ω aE2 (MvPolynomial.eval ![(D1 + 2) + (D + 2), 0] bE2) (p + 1))
    (hβ : graphOf β ∈ S.Ω aE2 (MvPolynomial.eval ![(D1 + 2) + (D + 2), 0] bE2) (p + 1))
    (hg : graphOf g ∈ S.Ω aE3 (MvPolynomial.eval ![(D1 + 2) + (D + 2), 0] bE3) (p + 1 + 1))
    (h2deg : MvPolynomial.eval ![(D1 + 2) + (D + 2), 0] bE2 ≤ MvPolynomial.eval ![D, D1] b2')
    (h3deg : MvPolynomial.eval ![(D1 + 2) + (D + 2), 0] bE3 ≤ MvPolynomial.eval ![D, D1] b3') :
    famGraph (chartVal g α β) ∈ S.Ω
      (aE3 + max ((aE2 + 2 * ((p + 2) + (p + 1)) + 1)
        + (aE2 + 2 * ((p + 2) + (p + 1)) + 1) + (p + 1 + 1) + aLC) (p + 1 + 1) + cCG1)
      (MvPolynomial.eval ![D, D1]
        (b3' + MvPolynomial.C (p + 1) * ((b2' + MvPolynomial.C 2) + (b2' + MvPolynomial.C 2)
          + MvPolynomial.C 1 + MvPolynomial.C cLC) + MvPolynomial.C cCG2)) (p + 1 + 1) := by
  let Afun : (Fin (p + 1) → ℝ) → ℝ :=
    fun x => α (Fin.init x) + x (Fin.last p) * (β (Fin.init x) - α (Fin.init x))
  let φmap : (Fin (p + 1) → ℝ) → (Fin (p + 1) → ℝ) :=
    fun x => Fin.snoc (Fin.init x) (Afun x)
  have hlα : graphOf (fun x : Fin (p + 1) → ℝ => α (Fin.init x)) ∈
      S.Ω (aE2 + 2 * ((p + 2) + (p + 1)) + 1)
        (MvPolynomial.eval ![D, D1] b2' + 2) (p + 1 + 1) := by
    refine Omega_mono_D ?_ (graphOf_lift_mem S hα)
    exact Nat.add_le_add_right h2deg 2
  have hlβ : graphOf (fun x : Fin (p + 1) → ℝ => β (Fin.init x)) ∈
      S.Ω (aE2 + 2 * ((p + 2) + (p + 1)) + 1)
        (MvPolynomial.eval ![D, D1] b2' + 2) (p + 1 + 1) := by
    refine Omega_mono_D ?_ (graphOf_lift_mem S hβ)
    exact Nat.add_le_add_right h2deg 2
  have hcoordf : graphOf (fun x : Fin (p + 1) → ℝ => x (Fin.last p)) ∈
      S.Ω (p + 1 + 1) 1 (p + 1 + 1) := Work.WilkG4c.graphOf_coord_mem S (Fin.last p)
  have hAfun : graphOf Afun ∈ S.Ω
      ((aE2 + 2 * ((p + 2) + (p + 1)) + 1) + (aE2 + 2 * ((p + 2) + (p + 1)) + 1)
        + (p + 1 + 1) + aLC)
      ((MvPolynomial.eval ![D, D1] b2' + 2) + (MvPolynomial.eval ![D, D1] b2' + 2)
        + 1 + cLC) (p + 1 + 1) := by
    have h := hLC (aE2 + 2 * ((p + 2) + (p + 1)) + 1) (aE2 + 2 * ((p + 2) + (p + 1)) + 1)
      (p + 1 + 1) (MvPolynomial.eval ![D, D1] b2' + 2)
      (MvPolynomial.eval ![D, D1] b2' + 2) 1
      (fun x : Fin (p + 1) → ℝ => α (Fin.init x))
      (fun x : Fin (p + 1) → ℝ => β (Fin.init x))
      (fun x : Fin (p + 1) → ℝ => x (Fin.last p)) hlα hlβ hcoordf
    simpa only [Afun] using h
  have hcoords : ∀ jj : Fin (p + 1),
      graphOf (fun x : Fin (p + 1) → ℝ => (Fin.snoc (Fin.init x) (Afun x)) jj) ∈
      S.Ω (max ((aE2 + 2 * ((p + 2) + (p + 1)) + 1)
          + (aE2 + 2 * ((p + 2) + (p + 1)) + 1) + (p + 1 + 1) + aLC) (p + 1 + 1))
        (max ((MvPolynomial.eval ![D, D1] b2' + 2) + (MvPolynomial.eval ![D, D1] b2' + 2)
          + 1 + cLC) 1) (p + 1 + 1) := by
    intro jj
    refine Fin.lastCases ?_ ?_ jj
    · have hh : (fun x : Fin (p + 1) → ℝ => (Fin.snoc (Fin.init x) (Afun x)) (Fin.last p))
          = Afun := by
        funext x
        exact Fin.snoc_last _ _
      rw [hh]
      exact Omega_mono_FD (le_max_left _ _) (le_max_left _ _) hAfun
    · intro i
      have hh : (fun x : Fin (p + 1) → ℝ =>
            (Fin.snoc (Fin.init x) (Afun x)) (Fin.castSucc i))
          = (fun x : Fin (p + 1) → ℝ => x (Fin.castSucc i)) := by
        funext x
        exact snoc_init_castSucc x (Afun x) i
      rw [hh]
      exact Omega_mono_FD (le_max_right _ _) (le_max_right _ _)
        (Work.WilkG4c.graphOf_coord_mem S (Fin.castSucc i))
  have hgg : graphOf g ∈ S.Ω aE3 (MvPolynomial.eval ![D, D1] b3') (p + 1 + 1) :=
    Omega_mono_D h3deg hg
  have hcomp := hCG aE3 (max ((aE2 + 2 * ((p + 2) + (p + 1)) + 1)
      + (aE2 + 2 * ((p + 2) + (p + 1)) + 1) + (p + 1 + 1) + aLC) (p + 1 + 1))
    (MvPolynomial.eval ![D, D1] b3')
    (max ((MvPolynomial.eval ![D, D1] b2' + 2) + (MvPolynomial.eval ![D, D1] b2' + 2)
      + 1 + cLC) 1)
    g φmap hgg hcoords
  have hfam : famGraph (chartVal g α β) = graphOf (g ∘ φmap) := by
    rw [famGraph_eq_graphOf_flatFam]
    rfl
  rw [hfam]
  refine Omega_mono_D ?_ hcomp
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  have hDpos : 1 ≤ (MvPolynomial.eval ![D, D1] b2' + 2) + (MvPolynomial.eval ![D, D1] b2' + 2)
      + 1 + cLC := by omega
  have hle : max ((MvPolynomial.eval ![D, D1] b2' + 2) + (MvPolynomial.eval ![D, D1] b2' + 2)
      + 1 + cLC) 1
      ≤ (MvPolynomial.eval ![D, D1] b2' + 2) + (MvPolynomial.eval ![D, D1] b2' + 2)
        + 1 + cLC := max_le le_rfl hDpos
  have hle2 := Nat.mul_le_mul_left (p + 1) hle
  omega

end Work.WilkG4c
