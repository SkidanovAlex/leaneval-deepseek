import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritAux
import Submission.Work.WilG4c.CritAux.hypoRaw_mem
import Submission.Work.WilG4c.CritAux.uv_mem
import Submission.Work.WilG4c.fibreLimitEqMem_pi

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The joint derivative graph along a cube word is `Ω`-definable

This is `SOMin.SharpDeriv` read in the coordinates of `AlSliceBase`: the set `dgSet` is
verbatim the set that `SharpDeriv` exhibits, so the two are the same constant and the
membership transfers without any bookkeeping. -/

theorem dgSet_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      ∀ (k : ℕ) (w : Fin k → Fin (n + 1)),
        dgSet p n f k w ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1) + 1) := by
  obtain ⟨a, b, hb⟩ := hder F0 (p + (n + 1))
  exact ⟨a, b, fun D f hf k w =>
    hb D (famFunHat f) (by simpa [famGraph_eq_graphOf_famFunHat] using hf) k
      (fun i => Fin.natAdd p (w i))⟩

/-! ## 2. `MvPolynomial` bookkeeping -/

/-- Substituting the second variable of a two-variable `ℕ`-polynomial into a univariate one. -/
theorem eval_eval₂ (bC : Polynomial ℕ) (P : MvPolynomial (Fin 2) ℕ) (D k : ℕ) :
    MvPolynomial.eval ![D, k] (bC.eval₂ MvPolynomial.C P)
      = bC.eval (MvPolynomial.eval ![D, k] P) := by
  induction bC using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [Polynomial.eval₂_add, map_add, hp, hq, Polynomial.eval_add]
  | monomial n a _ =>
      simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
        Polynomial.eval₂_pow, map_mul, map_pow, MvPolynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]

/-- Binary intersection of two `MvPolynomial ![D,k]`-bounded memberships: the format gains the
fixed `+1` of `SOMin.inter` and the degree polynomial is the sum. -/
theorem inter_mv {S : WilkiesDesign.SOMin} {M : ℕ} {a₁ a₂ : ℕ}
    {b₁ b₂ : MvPolynomial (Fin 2) ℕ} {D k : ℕ} {X Y : Set (Fin M → ℝ)}
    (hX : X ∈ S.Ω a₁ (MvPolynomial.eval ![D, k] b₁) M)
    (hY : Y ∈ S.Ω a₂ (MvPolynomial.eval ![D, k] b₂) M) :
    X ∩ Y ∈ S.Ω (max a₁ a₂ + 1) (MvPolynomial.eval ![D, k] (b₁ + b₂)) M := by
  have hX' : X ∈ S.Ω (max a₁ a₂) (MvPolynomial.eval ![D, k] b₁) M :=
    Work.WilG1.Omega.mono hX (le_max_left _ _) le_rfl
  have hY' : Y ∈ S.Ω (max a₁ a₂) (MvPolynomial.eval ![D, k] b₂) M :=
    Work.WilG1.Omega.mono hY (le_max_right _ _) le_rfl
  have h := S.inter (F := max a₁ a₂) (n := M) (k := 2)
    (fun i : Fin 2 => if i = 0 then MvPolynomial.eval ![D, k] b₁
      else MvPolynomial.eval ![D, k] b₂)
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by
      intro i
      fin_cases i
      · simpa using hX'
      · simpa using hY')
  have hsum : (∑ i : Fin 2, (if i = 0 then MvPolynomial.eval ![D, k] b₁
      else MvPolynomial.eval ![D, k] b₂)) = MvPolynomial.eval ![D, k] (b₁ + b₂) := by
    rw [Fin.sum_univ_two]
    simp [map_add]
  rw [hsum, Work.WilG1.Omega.iInter_fin_two] at h
  exact h

/-! ## 3. The target -/

theorem CritMem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.Crit p n f L ∈ S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) := by
  obtain ⟨aU, bU, hU⟩ := Work.WilG4c.CritAux.uv_mem S hder p n F0
  obtain ⟨aH, bH, hH⟩ := Work.WilG4c.CritAux.hypoRaw_mem S p n
  obtain ⟨aD, bD, hD⟩ := dgSet_mem S hder p n F0
  obtain ⟨aL, bL, hL⟩ := Work.WilG4c.fibreLimitEqMem_pi (S := S) (p := p) (n := n)
  refine ⟨max (aU + aH + 1) (aD + aL) + 1,
    bH.eval₂ MvPolynomial.C bU + bL.eval₂ MvPolynomial.C bD, ?_⟩
  intro D f L hf
  have hUV := hU D L.length f hf
  have hHyp := hH aU (MvPolynomial.eval ![D, L.length] bU) (UV p n f L.length) hUV
  have hLoc : {z : Fin (p + (n + 1) + 1) → ℝ | Fin.init z ∈ HypoRaw p n (UV p n f L.length)}
      ∈ S.Ω (aU + aH + 1) (MvPolynomial.eval ![D, L.length] (bH.eval₂ MvPolynomial.C bU))
          (p + (n + 1) + 1) := by
    simpa only [eval_eval₂] using S.prod_right hHyp
  have hdg := hD D f hf L.length (fun j => L.get j)
  have hLimeq : Work.WilG4c.LimeqP p n (dgSet p n f L.length (fun j => L.get j))
      ∈ S.Ω (aD + aL) (MvPolynomial.eval ![D, L.length] (bL.eval₂ MvPolynomial.C bD))
          (p + (n + 1) + 1) := by
    simpa only [eval_eval₂, Work.WilG4c.LimeqP] using
      hL (dgSet p n f L.length (fun j => L.get j)) hdg
  rw [crit_eq]
  exact inter_mv hLoc hLimeq

end Work.WilkG4c
