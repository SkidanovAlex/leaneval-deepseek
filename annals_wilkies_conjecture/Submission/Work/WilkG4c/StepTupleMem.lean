import Mathlib
import Submission.Work.WilG4c.ConsCompFamGraphMem
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.DominatingPoly
import Submission.Work.WilG5.Reindex

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The *identity* member `(l,u) ↦ u 0` of the §5.3 tuple: its graph is the coordinate
hyperplane `{z | z (Fin.last (p+1)) = z (Fin.last p)}` of `ℝ^{p+1+1}`, hence `Ω`-bounded with
format `p+1+1` and degree `1` (independently of `D`). -/
theorem famGraph_identity_mem (S : SOMin) (p : ℕ) :
    CG.famGraph (fun (_ : Fin p → ℝ) (u : Fin 1 → ℝ) => u 0) ∈
      S.Ω (p + 1 + 1) 1 (p + 1 + 1) :=
  Work.WilG4c.graphOf_projCoord_mem S (p + 1) (Fin.last p)

/-- **The `Ω`-bounds of the §5.3 tuple, with a uniform format and degree.**  Let `G` be a
family (`k` members, `p` parameters, cube dimension `n+1`, `Ω`-bounded with format `F0` and
degree `D`) and `γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)` a definable curve whose coordinate graphs
are `Ω`-bounded with format `Ag` and degree `MvPolynomial.eval ![D,0] Bg` (this is the shape in
which `CurveFam` supplies the near-maximising curve).  Then the three groups of members of the
§5.3 tuple — the *identity* `(l,u) ↦ u 0`, the *curve coordinates* `(l,u) ↦ γ l (u 0) j`, and the
*composites* `(l,u) ↦ G i l (Fin.cons (u 0) (γ l (u 0)))` — are all `Ω`-bounded as one-variable
families over `Fin p → ℝ`, with a **common** format `A` (independent of `D`) and a **common**
degree bound `MvPolynomial.eval ![D, MvPolynomial.eval ![D,0] Bg] B` (a polynomial in `D` and in
the curve's degree).

Ingredients: the identity is a coordinate hyperplane (`SOMin.hyp`); the curve coordinates are the
coordinate graphs of `γ` (transferred by `mono`, or by `Work.WilG5.reindex_mem`); the composites
are `Work.WilkG4c.ConsCompFamGraphMem`; the uniform bounds come from taking the maximum over the
finitely many members and using a dominating polynomial for the degrees
(`Work.WilkG4c.DominatingPoly`). -/
theorem StepTupleMem (S : WilkiesDesign.SOMin) (p n k : ℕ) :
    ∀ (F0 Ag : ℕ) (Bg : MvPolynomial (Fin 2) ℕ), ∃ (A : ℕ) (B : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (G : Work.WilkG4c.Family k p (n + 1))
        (γ : (Fin p → ℝ) → ℝ → (Fin n → ℝ)),
        (∀ i, WilkiesDesign.CG.famGraph (G i) ∈ S.Ω F0 D (p + (n + 1) + 1)) →
        (∀ j : Fin n, WilkiesDesign.graphOf (fun w : Fin (p + 1) → ℝ =>
            γ (Fin.init w) (w (Fin.last p)) j)
              ∈ S.Ω Ag (MvPolynomial.eval ![D, 0] Bg) (p + 1 + 1)) →
        (WilkiesDesign.CG.famGraph (fun (_ : Fin p → ℝ) (u : Fin 1 → ℝ) => u 0)
            ∈ S.Ω A (MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg] B) (p + 1 + 1)) ∧
        (∀ j : Fin n, WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (u : Fin 1 → ℝ) =>
            γ l (u 0) j)
              ∈ S.Ω A (MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg] B) (p + 1 + 1)) ∧
        (∀ i : Fin k, WilkiesDesign.CG.famGraph (fun (l : Fin p → ℝ) (u : Fin 1 → ℝ) =>
            G i l (Fin.cons (u 0) (γ l (u 0))))
              ∈ S.Ω A (MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg] B) (p + 1 + 1)) := by
  intro F0 Ag Bg
  -- the uniform format/degree increment for the restricted composition `(l,u) ↦ G i l (·, γ l (u 0))`
  obtain ⟨Ac, Cc, hCc⟩ := Work.WilG4c.ConsCompFamGraphMem S p n
  -- the common format is the maximum of the three group's formats; the common degree is the
  -- polynomial `D + (p + (n+1)) * (r + 1) + Cc` in `D` and the curve degree `r`
  refine ⟨max (p + 1 + 1) (max Ag (F0 + Ag + Ac)),
    MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
      + MvPolynomial.C Cc, ?_⟩
  intro D G γ hG hγ
  have hA1 : p + 1 + 1 ≤ max (p + 1 + 1) (max Ag (F0 + Ag + Ac)) := le_max_left _ _
  have hA2 : Ag ≤ max (p + 1 + 1) (max Ag (F0 + Ag + Ac)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hA3 : F0 + Ag + Ac ≤ max (p + 1 + 1) (max Ag (F0 + Ag + Ac)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hpn : 1 ≤ p + (n + 1) := by omega
  -- the common degree bound, evaluated at `(D, curve degree)`
  have hval : MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg]
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
        + MvPolynomial.C Cc) =
      D + (p + (n + 1)) * (MvPolynomial.eval ![D, 0] Bg + 1) + Cc := by
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul]
  have hmul : 1 * (MvPolynomial.eval ![D, 0] Bg + 1)
      ≤ (p + (n + 1)) * (MvPolynomial.eval ![D, 0] Bg + 1) :=
    Nat.mul_le_mul_right _ hpn
  have hle1 : (1 : ℕ) ≤ MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg]
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
        + MvPolynomial.C Cc) := by
    rw [hval]; omega
  have hle2 : MvPolynomial.eval ![D, 0] Bg ≤
      MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg]
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
        + MvPolynomial.C Cc) := by
    rw [hval]; omega
  have hle3 : D + (p + (n + 1)) * (MvPolynomial.eval ![D, 0] Bg + 1) + Cc ≤
      MvPolynomial.eval ![D, MvPolynomial.eval ![D, 0] Bg]
      (MvPolynomial.X 0 + MvPolynomial.C (p + (n + 1)) * (MvPolynomial.X 1 + MvPolynomial.C 1)
        + MvPolynomial.C Cc) := le_of_eq hval.symm
  refine ⟨?_, ?_, ?_⟩
  · -- the identity `(l,u) ↦ u 0`
    exact Omega_mono_le S hA1 hle1 (famGraph_identity_mem S p)
  · -- the curve coordinates `(l,u) ↦ γ l (u 0) j`: `famGraph` and `graphOf` agree definitionally
    intro j
    exact Omega_mono_le S hA2 hle2 (hγ j)
  · -- the composites `(l,u) ↦ G i l (Fin.cons (u 0) (γ l (u 0)))`
    intro i
    exact Omega_mono_le S hA3 hle3
      (hCc F0 D Ag (MvPolynomial.eval ![D, 0] Bg) (G i) γ (hG i) hγ)

end Work.WilkG4c
