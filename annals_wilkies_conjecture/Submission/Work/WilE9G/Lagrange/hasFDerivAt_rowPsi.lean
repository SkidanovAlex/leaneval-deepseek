/-
  WilE9G / Lagrange — **the `l`-th Lagrange row of the differential of `degenPsi`.**

  `degenPsi S Phi p l` is the rearranged `l`-th Lagrange equation

    `ψ_l = ν₀ (Φ(z) c_l + ∂_l Φ(z)) - ∑_a ν_a ∂_l h_a(z)`

  (`z = degenZ p`, `(ν, ν₀) = degenNu p`, `c = degenC p`), and `rowPsi S Phi p l` is the row of
  the differential of the system `degenH` belonging to it.  This file computes that row: the
  function `p' ↦ degenPsi S Phi p' l` has `rowPsi S Phi p l` as its Fréchet derivative at `p`.

  The computation is purely the product rule.  Writing

  * `N p' = degenNu p' (Fin.last S.j)`      (derivative `degenNuProj (Fin.last S.j)`),
  * `A p' = eaEval S.X.c Phi (degenZ p')`   (derivative `eaDRow S Phi p`),
  * `C p' = degenC p' l`                    (derivative `degenCProj l`),
  * `B p' = eaEval S.X.c (∂_l Φ) (degenZ p')` (derivative `eaDRow S (∂_l Φ) p`),
  * `H_a p' = eaEval S.X.c (∂_l h_a) (degenZ p')` (derivative `eaDRow S (∂_l h_a) p`),

  we have `degenPsi S Phi p' l = N p' * (A p' * C p' + B p') - ∑_a N_a p' * H_a p'`, and the
  product rule for the `HasFDerivAt` combinators gives exactly `rowPsi S Phi p l`.  The only
  bookkeeping is the reordering of the two terms of each product and of the summands, and the
  identification of the coordinate projections `degenNuProj`/`degenCProj` with `degenNu`/`degenC`.
-/
import Mathlib
import Submission.Work.WilE9G.Lagrange.DegenDiff

namespace Work.WilE9G.Lagrange

open WilkiesDesign WilkiesDesign.E Work.WilE9G

variable {n m : ℕ}

/-! ## The coordinate projections as continuous linear maps -/

/-- The projection onto the `a`-th `(ν,ν₀)`-coordinate of the `(z,(ν,ν₀),c)`-space. -/
def degenNuProj {n m j : ℕ} (a : Fin (j + 1)) : (Fin (degenDim n m j) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
    (nuIdx (m := m) (j := j) a)

/-- The projection onto the `l`-th `c`-coordinate of the `(z,(ν,ν₀),c)`-space. -/
def degenCProj {n m j : ℕ} (l : Fin (1 + m)) : (Fin (degenDim n m j) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (degenDim n m j) => ℝ)
    (cIdx (m := m) (j := j) l)

@[simp] theorem degenNuProj_apply {n m j : ℕ} (a : Fin (j + 1))
    (p : Fin (degenDim n m j) → ℝ) : degenNuProj (m := m) a p = degenNu p a := rfl

@[simp] theorem degenCProj_apply {n m j : ℕ} (l : Fin (1 + m))
    (p : Fin (degenDim n m j) → ℝ) : degenCProj (m := m) (j := j) l p = degenC p l := rfl

theorem hasFDerivAt_degenNuComp {j : ℕ} (a : Fin (j + 1))
    (p : Fin (degenDim n m j) → ℝ) :
    HasFDerivAt (fun p' : Fin (degenDim n m j) → ℝ => degenNu p' a)
      (degenNuProj (m := m) (j := j) a) p := by
  simp only [degenNu_eq_apply]
  exact (degenNuProj (m := m) (j := j) a).hasFDerivAt

theorem hasFDerivAt_degenCComp {j : ℕ} (l : Fin (1 + m))
    (p : Fin (degenDim n m j) → ℝ) :
    HasFDerivAt (fun p' : Fin (degenDim n m j) → ℝ => degenC p' l)
      (degenCProj (m := m) (j := j) l) p := by
  simp only [degenC_eq_apply]
  exact (degenCProj (m := m) (j := j) l).hasFDerivAt

/-! ## The row of the `l`-th Lagrange equation -/

theorem hasFDerivAt_rowPsi {n m : ℕ} (S : Work.WilE9G.AmbStratum (n + (1 + m)))
    (Phi : WilkiesDesign.E.EAPoly (n + (1 + m)) S.X.r)
    (p : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ) (l : Fin (1 + m)) :
    HasFDerivAt (fun p' : Fin (Work.WilE9G.Lagrange.degenDim n m S.j) → ℝ =>
        Work.WilE9G.Lagrange.degenPsi S Phi p' l)
      (Work.WilE9G.Lagrange.rowPsi S Phi p l) p := by
  -- the `z`-part of `Φ` and of `∂_l Φ`
  have hA : HasFDerivAt (fun p' : Fin (degenDim n m S.j) → ℝ => eaEval S.X.c Phi (degenZ p'))
      (eaDRow S Phi p) p := hasFDerivAt_eaDRow S Phi p
  have hB : HasFDerivAt (fun p' : Fin (degenDim n m S.j) → ℝ =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) (degenZ p'))
      (eaDRow S (eaD S.X.c (Fin.natAdd n l) Phi) p) p := hasFDerivAt_eaDRow S _ p
  -- the coordinates `c_l` and `ν₀`
  have hC : HasFDerivAt (fun p' : Fin (degenDim n m S.j) → ℝ => degenC p' l)
      (degenCProj (m := m) (j := S.j) l) p := hasFDerivAt_degenCComp l p
  have hN : HasFDerivAt (fun p' : Fin (degenDim n m S.j) → ℝ => degenNu p' (Fin.last S.j))
      (degenNuProj (m := m) (Fin.last S.j)) p := hasFDerivAt_degenNuComp (Fin.last S.j) p
  -- the bracket `Φ(z) c_l + ∂_l Φ(z)`
  have h1 : HasFDerivAt (fun p' : Fin (degenDim n m S.j) → ℝ =>
        eaEval S.X.c Phi (degenZ p') * degenC p' l
          + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) (degenZ p'))
      (eaEval S.X.c Phi (degenZ p) • degenCProj (m := m) (j := S.j) l
        + degenC p l • eaDRow S Phi p
        + eaDRow S (eaD S.X.c (Fin.natAdd n l) Phi) p) p :=
    (hA.mul hC).add hB
  -- the subtracted sum `∑_a ν_a ∂_l h_a(z)`
  have hsum : HasFDerivAt
      (fun p' : Fin (degenDim n m S.j) → ℝ =>
        ∑ a : Fin S.j, degenNu p' (Fin.castAdd 1 a)
          * eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p'))
      (∑ a : Fin S.j,
        (degenNu p (Fin.castAdd 1 a) • eaDRow S (eaD S.X.c (Fin.natAdd n l) (S.h a)) p
          + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p)
              • degenNuProj (m := m) (Fin.castAdd 1 a))) p := by
    refine HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ => ?_)
    exact (hasFDerivAt_degenNuComp (Fin.castAdd 1 a) p).mul (hasFDerivAt_eaDRow S _ p)
  -- reordering the summands to the order used by `rowPsi`
  have hsum_eq : (∑ a : Fin S.j,
        (degenNu p (Fin.castAdd 1 a) • eaDRow S (eaD S.X.c (Fin.natAdd n l) (S.h a)) p
          + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p)
              • degenNuProj (m := m) (Fin.castAdd 1 a)))
      = (∑ a : Fin S.j,
        (eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p)
              • ContinuousLinearMap.proj (nuIdx (m := m) (Fin.castAdd 1 a))
          + degenNu p (Fin.castAdd 1 a) • eaDRow S (eaD S.X.c (Fin.natAdd n l) (S.h a)) p)) := by
    apply Finset.sum_congr rfl
    intro a _
    simp only [degenNuProj]
    exact add_comm _ _
  -- the differential produced by the product rule is exactly `rowPsi`
  have hD : (degenNu p (Fin.last S.j) •
          (eaEval S.X.c Phi (degenZ p) • degenCProj (m := m) (j := S.j) l
            + degenC p l • eaDRow S Phi p
            + eaDRow S (eaD S.X.c (Fin.natAdd n l) Phi) p)
        + (eaEval S.X.c Phi (degenZ p) * degenC p l
            + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) Phi) (degenZ p))
            • degenNuProj (m := m) (Fin.last S.j)
        - ∑ a : Fin S.j,
            (degenNu p (Fin.castAdd 1 a) • eaDRow S (eaD S.X.c (Fin.natAdd n l) (S.h a)) p
              + eaEval S.X.c (eaD S.X.c (Fin.natAdd n l) (S.h a)) (degenZ p)
                  • degenNuProj (m := m) (Fin.castAdd 1 a)))
      = rowPsi S Phi p l := by
    rw [rowPsi, hsum_eq]
    ext v
    simp only [degenNuProj, degenCProj, add_apply, sub_apply, smul_apply, sum_apply,
      smul_eq_mul, ContinuousLinearMap.proj_apply]
    ring
  exact ((hN.mul h1).sub hsum).congr_fderiv hD

end Work.WilE9G.Lagrange
