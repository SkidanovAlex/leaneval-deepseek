import Mathlib
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.YbddAux
import Submission.Work.WilG4c.ParCompGraphMem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c.SectAux

open WilkiesDesign WilkiesDesign.CG

/-- `PullFamGraphPoly` with the number `k` of families moved *inside* the quantifiers, i.e.
with `C₁, C₂` uniform in `k`.  The particular constants produced by the
composition argument of `PullFamGraphPoly` do not depend on `k`, so the same proof applies. -/
theorem PullFamGraphPolyK (S : WilkiesDesign.SOMin) (p q m : ℕ) :
    ∃ (C₁ C₂ : ℕ),
      ∀ (k : ℕ) (Aθ : ℕ) (bθ : MvPolynomial (Fin 2) ℕ) (F0 : ℕ) (D r : ℕ)
        (F : Work.WilkG4c.Family k p m) (θ : (Fin q → ℝ) → (Fin p → ℝ)),
        (∀ i, WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 D (p + m + 1)) →
        (∀ j : Fin p, WilkiesDesign.graphOf (fun ν : Fin q → ℝ => θ ν j) ∈
          S.Ω Aθ (MvPolynomial.eval ![D, r] bθ) (q + 1)) →
        ∀ i, WilkiesDesign.CG.famGraph (fun (ν : Fin q → ℝ) (y : Fin m → ℝ) => F i (θ ν) y) ∈
          S.Ω (F0 + Aθ + C₁)
            (MvPolynomial.eval ![D, r]
              (MvPolynomial.X 0 + MvPolynomial.C (p + m + 1) * bθ + MvPolynomial.C C₂))
            (q + m + 1) := by
  obtain ⟨C₁g, C₂g, hcomp⟩ := Work.WilG4c.graphOfCompGen S (p + m) (q + m)
  refine ⟨2 * ((q + m + 1) + (q + 1)) + 1 + ((q + m) + 1) + C₁g, (p + m) * 2 + C₂g, ?_⟩
  intro k Aθ bθ F0 D r F θ hF hθ i
  have hcoord : ∀ j : Fin (p + m),
      WilkiesDesign.graphOf (fun z : Fin (q + m) → ℝ => Work.WilG4c.pcgm_parIdx θ z j) ∈
        S.Ω (max (Aθ + 2 * ((q + m + 1) + (q + 1)) + 1) ((q + m) + 1))
          (MvPolynomial.eval ![D, r] bθ + 2) (q + m + 1) := by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun l => ?_) j
    · have h : WilkiesDesign.graphOf
          (fun z : Fin (q + m) → ℝ => Work.WilG4c.pcgm_parIdx θ z (Fin.castAdd m j')) ∈
          S.Ω (Aθ + 2 * ((q + m + 1) + (q + 1)) + 1)
            (MvPolynomial.eval ![D, r] bθ + 2) (q + m + 1) := by
        rw [Work.WilG4c.pcgm_graphOf_parIdx_fst θ j']
        exact Work.WilG4c.GraphComp.subst_mem S (Work.WilG4c.pcgm_liftParIdx q m) (hθ j')
      exact Work.WilG1.Omega.mono h (le_max_left _ _) le_rfl
    · have hset : (fun z : Fin (q + m) → ℝ =>
            Work.WilG4c.pcgm_parIdx θ z (Fin.natAdd p l)) =
          (fun z : Fin (q + m) → ℝ => z (Fin.natAdd q l)) := by
        funext z; simp [Work.WilG4c.pcgm_parIdx, Fin.append_right]
      rw [hset]
      exact Work.WilG1.Omega.mono
        (Work.WilG4c.pcgm_graphOf_projCoord_mem S (q + m) (Fin.natAdd q l))
        (le_max_right _ _) (by omega)
  have hcomp' := hcomp F0 (max (Aθ + 2 * ((q + m + 1) + (q + 1)) + 1) ((q + m) + 1))
    D (MvPolynomial.eval ![D, r] bθ + 2) (Work.WilG4c.pcgm_compGFam (F i))
    (Work.WilG4c.pcgm_parIdx θ)
    (by rw [Work.WilG4c.pcgm_graphOf_compGFam]; exact hF i) hcoord
  rw [Work.WilG4c.pcgm_famGraph_parComp (F i) θ]
  refine Work.WilG1.Omega.mono hcomp' ?_ ?_
  · omega
  · have hR : MvPolynomial.eval ![D, r]
        (MvPolynomial.X 0 + MvPolynomial.C (p + m + 1) * bθ +
          MvPolynomial.C ((p + m) * 2 + C₂g))
        = D + (p + m + 1) * MvPolynomial.eval ![D, r] bθ + ((p + m) * 2 + C₂g) := by
      rw [MvPolynomial.eval_add, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_C]
      norm_num
    rw [hR]
    have h1 : (p + m) * (MvPolynomial.eval ![D, r] bθ + 2)
        = (p + m) * MvPolynomial.eval ![D, r] bθ + (p + m) * 2 := by ring
    have h2 : (p + m + 1) * MvPolynomial.eval ![D, r] bθ
        = (p + m) * MvPolynomial.eval ![D, r] bθ + MvPolynomial.eval ![D, r] bθ := by ring
    rw [h1, h2]
    omega

end Work.WilG4c.SectAux
