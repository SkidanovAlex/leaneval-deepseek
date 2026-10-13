/-
  WilG4a / CD / `fibreLimitMem` — the parametrised `Ω`-construction of the Cauchy locus of a
  fibre.

  For an `Ω F D (p+2)`-set `A` (the graph of the fibre-restrictions of a partial function) the
  set

    `Z = {z : ℝ^{p+1} | ∀ε>0 ∃δ>0, the `A`-values along `t ↦ (init z, t, ·)` over the punctured
      ball of radius `δ` around `c = z (last p)` differ by at most `ε`}`

  is `Ω (F + 4p + 36) (7D + 48) (p+1)`.

  ## Proof outline

  All the set theory lives in the vocabulary of `Work.WilG4a.CD.fibreLimitDefs`: the body
  `Gset p A ⊆ ℝ^{p+7}` is the conjunction of the seven atoms of the *(negated)* Cauchy
  condition in the coordinates `(z | ε | δ | t | t' | v | v')`, and `projChain` is the
  `Ω`-construction

    `(projLast ({ε>0} ∩ (projLast ({δ>0} ∩ (projLastIter (p+3) 4 (Gset p A))ᶜ))ᶜ))ᶜ`.

  Two sibling modules supply the two mathematical (non-`Ω`) facts:

  * `Work.WilG4a.CD.snocIt_mem_Gset` reads `Gset` in the coordinates of a point produced by
    the iterated projection, i.e. in terms of `z, ε, δ, t, t', v, v'`;
  * `Work.WilG4a.CD.fibreCauchySet_eq_projChain` uses that reading to identify `projChain`
    with the Cauchy locus `fibreCauchySet`.

  What is left — and what this file does — is the `Ω`-bookkeeping.  The seven atoms are put at
  the common format `F + 4p + 19` and the common degree `D + 6` (the two substitution atoms
  cost `F + 2((p+7)+(p+2)) + 1` and `D + 2` by `Work.WilG4a.subst_mem`; the `t ≠ c` atoms are
  complements of degree-`1` hypersurfaces; `δ² > (t-c)²` are positivity sets of degree-`2`
  polynomials and `ε < |v-v'|` is a union of two positivity sets of linear polynomials, all of
  format `p+9`).  Six binary intersections give `Gset` at format `F + 4p + 25` and degree
  `7(D+6)`; four projections give the `∃` over `t, t', v, v'` at format `F + 4p + 29`; then
  complement (`+1`), intersect with `{δ>0}` (`+1`), project (`+1`), complement (`+1`), intersect
  with `{ε>0}` (`+1`), project (`+1`) and complement (`+1`) give format `F + 4p + 36` and
  degree `7(D+6) + 6 = 7D + 48`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4a.liftNM_mem
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG0.API
import Submission.Work.WilG4a.CD.fibreLimitDefs
import Submission.Work.WilG4a.CD.snocIt_mem_Gset
import Submission.Work.WilG4a.CD.fibreCauchySet_eq_projChain

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4a.CD

open WilkiesDesign

/-! ## 1. Degree bookkeeping for the polynomial atoms -/

theorem flm_td_sub_le_one (n : ℕ) (a b : Fin n) :
    (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
  simp [MvPolynomial.totalDegree_X]

theorem flm_td_quad (n : ℕ) (a b c : Fin n) :
    ((MvPolynomial.X a : MvPolynomial (Fin n) ℝ) ^ 2 -
      (MvPolynomial.X b - MvPolynomial.X c) ^ 2).totalDegree ≤ 2 := by
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    simp [MvPolynomial.totalDegree_X]
  · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
    have h := flm_td_sub_le_one n b c
    omega

/-! ## 2. The seven atoms are `Ω`-sets at the common format `F + 4p + 19`, degree `D + 6` -/

/-- The first substitution atom `(init z, t, v) ∈ A`. -/
theorem flm_bA1_mem {S : WilkiesDesign.SOMin} {p F D : ℕ} {A : Set (Fin (p + 2) → ℝ)}
    (hA : A ∈ S.Ω F D (p + 2)) : bA1 p A ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := by
  have h := Work.WilG4a.subst_mem S (iota1_y p) hA
  exact Work.WilG0.Omega_mono_FD (by omega) (by omega) h

/-- The second substitution atom `(init z, t', v') ∈ A`. -/
theorem flm_bA2_mem {S : WilkiesDesign.SOMin} {p F D : ℕ} {A : Set (Fin (p + 2) → ℝ)}
    (hA : A ∈ S.Ω F D (p + 2)) : bA2 p A ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := by
  have h := Work.WilG4a.subst_mem S (iota2_y p) hA
  exact Work.WilG0.Omega_mono_FD (by omega) (by omega) h

/-- The atom `t ≠ c` as the complement of a hypersurface. -/
theorem flm_bTne_eq (p : ℕ) :
    bTne p = {w : Fin (p + 7) → ℝ | MvPolynomial.eval w
      (MvPolynomial.X (iT p) - MvPolynomial.X (iC p)) = 0}ᶜ := by
  ext w
  simp only [bTne, Set.mem_ofPred_eq, Set.mem_compl_iff, ne_eq, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, sub_eq_zero]

theorem flm_bTne_mem {S : WilkiesDesign.SOMin} {p F D : ℕ} :
    bTne p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := by
  have h0 : {w : Fin (p + 7) → ℝ | MvPolynomial.eval w
      (MvPolynomial.X (iT p) - MvPolynomial.X (iC p)) = 0} ∈ S.Ω (p + 7) 1 (p + 7) := by
    have h := S.hyp (p + 7)
      (MvPolynomial.X (iT p) - MvPolynomial.X (iC p) : MvPolynomial (Fin (p + 7)) ℝ)
    exact Work.WilG0.Omega_mono_FD le_rfl (flm_td_sub_le_one (p + 7) (iT p) (iC p)) h
  rw [flm_bTne_eq p]
  exact Work.WilG0.Omega_mono_FD (by omega) (by omega) (S.compl h0)

/-- The atom `t' ≠ c` as the complement of a hypersurface. -/
theorem flm_bTne'_eq (p : ℕ) :
    bTne' p = {w : Fin (p + 7) → ℝ | MvPolynomial.eval w
      (MvPolynomial.X (iT' p) - MvPolynomial.X (iC p)) = 0}ᶜ := by
  ext w
  simp only [bTne', Set.mem_ofPred_eq, Set.mem_compl_iff, ne_eq, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, sub_eq_zero]

theorem flm_bTne'_mem {S : WilkiesDesign.SOMin} {p F D : ℕ} :
    bTne' p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := by
  have h0 : {w : Fin (p + 7) → ℝ | MvPolynomial.eval w
      (MvPolynomial.X (iT' p) - MvPolynomial.X (iC p)) = 0} ∈ S.Ω (p + 7) 1 (p + 7) := by
    have h := S.hyp (p + 7)
      (MvPolynomial.X (iT' p) - MvPolynomial.X (iC p) : MvPolynomial (Fin (p + 7)) ℝ)
    exact Work.WilG0.Omega_mono_FD le_rfl (flm_td_sub_le_one (p + 7) (iT' p) (iC p)) h
  rw [flm_bTne'_eq p]
  exact Work.WilG0.Omega_mono_FD (by omega) (by omega) (S.compl h0)

/-- The atom `δ² > (t - c)²` as a positivity set. -/
theorem flm_bQ1_eq (p : ℕ) :
    bQ1 p = {w : Fin (p + 7) → ℝ | 0 < MvPolynomial.eval w
      ((MvPolynomial.X (iDel p) : MvPolynomial (Fin (p + 7)) ℝ) ^ 2 -
        (MvPolynomial.X (iT p) - MvPolynomial.X (iC p)) ^ 2)} := by
  ext w
  simp only [bQ1, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.eval_X]

theorem flm_bQ1_mem {S : WilkiesDesign.SOMin} {p F D : ℕ} :
    bQ1 p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := by
  rw [flm_bQ1_eq p]
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 7) D
    ((MvPolynomial.X (iDel p) : MvPolynomial (Fin (p + 7)) ℝ) ^ 2 -
      (MvPolynomial.X (iT p) - MvPolynomial.X (iC p)) ^ 2)
  refine Work.WilG0.Omega_mono_FD (by omega) ?_ h
  have htd := flm_td_quad (p + 7) (iDel p) (iT p) (iC p)
  simp only [Polynomial.eval_C]
  omega

/-- The atom `δ² > (t' - c)²` as a positivity set. -/
theorem flm_bQ2_eq (p : ℕ) :
    bQ2 p = {w : Fin (p + 7) → ℝ | 0 < MvPolynomial.eval w
      ((MvPolynomial.X (iDel p) : MvPolynomial (Fin (p + 7)) ℝ) ^ 2 -
        (MvPolynomial.X (iT' p) - MvPolynomial.X (iC p)) ^ 2)} := by
  ext w
  simp only [bQ2, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
    MvPolynomial.eval_X]

theorem flm_bQ2_mem {S : WilkiesDesign.SOMin} {p F D : ℕ} :
    bQ2 p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := by
  rw [flm_bQ2_eq p]
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 7) D
    ((MvPolynomial.X (iDel p) : MvPolynomial (Fin (p + 7)) ℝ) ^ 2 -
      (MvPolynomial.X (iT' p) - MvPolynomial.X (iC p)) ^ 2)
  refine Work.WilG0.Omega_mono_FD (by omega) ?_ h
  have htd := flm_td_quad (p + 7) (iDel p) (iT' p) (iC p)
  simp only [Polynomial.eval_C]
  omega

/-- The atom `ε < |v - v'|` as a union of two positivity sets. -/
theorem flm_bV_eq (p : ℕ) :
    bV p = {w : Fin (p + 7) → ℝ | 0 < MvPolynomial.eval w
        (MvPolynomial.X (iV p) - MvPolynomial.X (iV' p) - MvPolynomial.X (iEps p))} ∪
      {w : Fin (p + 7) → ℝ | 0 < MvPolynomial.eval w
        (MvPolynomial.X (iV' p) - MvPolynomial.X (iV p) - MvPolynomial.X (iEps p))} := by
  ext w
  simp only [bV, Set.mem_ofPred_eq, Set.mem_union, MvPolynomial.eval_sub, MvPolynomial.eval_X]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

theorem flm_bV_mem {S : WilkiesDesign.SOMin} {p F D : ℕ} :
    bV p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := by
  have hmk : ∀ (P : MvPolynomial (Fin (p + 7)) ℝ), P.totalDegree ≤ 1 →
      {w : Fin (p + 7) → ℝ | 0 < MvPolynomial.eval w P} ∈ S.Ω (p + 9) 3 (p + 7) := by
    intro P hP
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 7) D P
    refine Work.WilG0.Omega_mono_FD (by omega) ?_ h
    simp only [Polynomial.eval_C]
    omega
  have hL := hmk (MvPolynomial.X (iV p) - MvPolynomial.X (iV' p) - MvPolynomial.X (iEps p))
    (by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · exact flm_td_sub_le_one (p + 7) (iV p) (iV' p)
      · simp [MvPolynomial.totalDegree_X])
  have hR := hmk (MvPolynomial.X (iV' p) - MvPolynomial.X (iV p) - MvPolynomial.X (iEps p))
    (by
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · exact flm_td_sub_le_one (p + 7) (iV' p) (iV p)
      · simp [MvPolynomial.totalDegree_X])
  rw [flm_bV_eq p]
  refine Work.WilG0.Omega_mono_FD (by omega) (by omega)
    (Work.WilG0.Omega_union2 hL hR)

/-! ## 3. The positivity sets of the two quantifier blocks -/

theorem flm_posDel_mem {S : WilkiesDesign.SOMin} {p : ℕ} :
    posDelSet p ∈ S.Ω (p + 5) 3 (p + 3) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 3) 0
    (MvPolynomial.X (Fin.last (p + 2)) : MvPolynomial (Fin (p + 3)) ℝ)
  have hset : posDelSet p =
      {u : Fin (p + 3) → ℝ | 0 < MvPolynomial.eval u
        (MvPolynomial.X (Fin.last (p + 2)) : MvPolynomial (Fin (p + 3)) ℝ)} := by
    ext u
    simp [posDelSet, MvPolynomial.eval_X]
  rw [hset]
  refine Work.WilG0.Omega_mono_FD (by omega) ?_ h
  simp only [Polynomial.eval_C, MvPolynomial.totalDegree_X]
  omega

theorem flm_posEps_mem {S : WilkiesDesign.SOMin} {p : ℕ} :
    posEpsSet p ∈ S.Ω (p + 4) 3 (p + 2) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + 2) 0
    (MvPolynomial.X (Fin.last (p + 1)) : MvPolynomial (Fin (p + 2)) ℝ)
  have hset : posEpsSet p =
      {u : Fin (p + 2) → ℝ | 0 < MvPolynomial.eval u
        (MvPolynomial.X (Fin.last (p + 1)) : MvPolynomial (Fin (p + 2)) ℝ)} := by
    ext u
    simp [posEpsSet, MvPolynomial.eval_X]
  rw [hset]
  refine Work.WilG0.Omega_mono_FD (by omega) ?_ h
  simp only [Polynomial.eval_C, MvPolynomial.totalDegree_X]
  omega

/-! ## 4. The target -/

/-- Parametrised `Ω`-construction: for an `Ω`-set `A ⊆ ℝ^{p+2}` (playing the role of the
graph of the fibre-restrictions of a partial function `(l,x) ↦ value`), the set of `z` at which
the `A`-values along the fibre `t ↦ (Fin.init z, t, ·)` form a Cauchy family as `t` tends to
`z (Fin.last p)` (excluding `t = z (Fin.last p)`) is `Ω`-definable, with format exceeding the
atom's by a fixed amount and degree a fixed polynomial in the atom's degree. -/
theorem fibreLimitMem {p : ℕ} {S : WilkiesDesign.SOMin} :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ {F D : ℕ} (A : Set (Fin (p + 2) → ℝ)), A ∈ S.Ω F D (p + 2) →
        {z : Fin (p + 1) → ℝ | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ t t' : ℝ, t ≠ z (Fin.last p) → t' ≠ z (Fin.last p) →
            |t - z (Fin.last p)| < δ → |t' - z (Fin.last p)| < δ →
              ∀ v v' : ℝ, Fin.snoc (Fin.snoc (Fin.init z) t) v ∈ A →
                Fin.snoc (Fin.snoc (Fin.init z) t') v' ∈ A → |v - v'| ≤ ε} ∈
          S.Ω (F + a) (b.eval D) (p + 1) := by
  refine ⟨4 * p + 36, Polynomial.C 7 * Polynomial.X + Polynomial.C 48, ?_⟩
  intro F D A hA
  -- the seven atoms at the common format `F + 4p + 19` and common degree `D + 6`
  have h1 : bA1 p A ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := flm_bA1_mem hA
  have h2 : bA2 p A ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := flm_bA2_mem hA
  have h3 : bTne p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := flm_bTne_mem
  have h4 : bTne' p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := flm_bTne'_mem
  have h5 : bQ1 p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := flm_bQ1_mem
  have h6 : bQ2 p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := flm_bQ2_mem
  have h7 : bV p ∈ S.Ω (F + 4 * p + 19) (D + 6) (p + 7) := flm_bV_mem
  -- the six binary intersections, at formats `F + 4p + 20, …, F + 4p + 25`
  have i1 : bA1 p A ∩ bA2 p A ∈ S.Ω (F + 4 * p + 20) (2 * (D + 6)) (p + 7) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega) (Work.WilG0.Omega_inter2 h1 h2)
  have i2 : bA1 p A ∩ bA2 p A ∩ bTne p ∈ S.Ω (F + 4 * p + 21) (3 * (D + 6)) (p + 7) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega)
      (Work.WilG0.Omega_inter2 i1 (Work.WilG0.Omega_mono_F (by omega) h3))
  have i3 : bA1 p A ∩ bA2 p A ∩ bTne p ∩ bTne' p ∈
      S.Ω (F + 4 * p + 22) (4 * (D + 6)) (p + 7) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega)
      (Work.WilG0.Omega_inter2 i2 (Work.WilG0.Omega_mono_F (by omega) h4))
  have i4 : bA1 p A ∩ bA2 p A ∩ bTne p ∩ bTne' p ∩ bQ1 p ∈
      S.Ω (F + 4 * p + 23) (5 * (D + 6)) (p + 7) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega)
      (Work.WilG0.Omega_inter2 i3 (Work.WilG0.Omega_mono_F (by omega) h5))
  have i5 : bA1 p A ∩ bA2 p A ∩ bTne p ∩ bTne' p ∩ bQ1 p ∩ bQ2 p ∈
      S.Ω (F + 4 * p + 24) (6 * (D + 6)) (p + 7) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega)
      (Work.WilG0.Omega_inter2 i4 (Work.WilG0.Omega_mono_F (by omega) h6))
  have hG : Gset p A ∈ S.Ω (F + 4 * p + 25) (7 * (D + 6)) (p + 7) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega)
      (Work.WilG0.Omega_inter2 i5 (Work.WilG0.Omega_mono_F (by omega) h7))
  -- the four projections, the complement, the `δ > 0` block
  have hProj : Work.WilG0.projLastIter (p + 3) 4 (Gset p A) ∈
      S.Ω (F + 4 * p + 29) (7 * (D + 6)) (p + 3) :=
    Work.WilG0.Omega_mono_FD (by omega) le_rfl
      (Work.WilG4a.projLastIter_mem (S := S) (n := p + 3) (m := 4) hG)
  have hProjC : (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ ∈
      S.Ω (F + 4 * p + 30) (7 * (D + 6)) (p + 3) := S.compl hProj
  have hDel : posDelSet p ∈ S.Ω (F + 4 * p + 30) 3 (p + 3) :=
    Work.WilG0.Omega_mono_FD (by omega) le_rfl flm_posDel_mem
  have hInt1 : posDelSet p ∩ (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ ∈
      S.Ω (F + 4 * p + 31) (7 * (D + 6) + 3) (p + 3) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega)
      (Work.WilG0.Omega_inter2 hDel hProjC)
  have hE : projLast (posDelSet p ∩ (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ) ∈
      S.Ω (F + 4 * p + 32) (7 * (D + 6) + 3) (p + 2) :=
    Work.WilG0.Omega_mono_FD (by omega) le_rfl (S.proj hInt1)
  have hEc : (projLast
      (posDelSet p ∩ (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ))ᶜ ∈
      S.Ω (F + 4 * p + 33) (7 * (D + 6) + 3) (p + 2) := S.compl hE
  have hEps : posEpsSet p ∈ S.Ω (F + 4 * p + 33) 3 (p + 2) :=
    Work.WilG0.Omega_mono_FD (by omega) le_rfl flm_posEps_mem
  have hInt2 : posEpsSet p ∩
      (projLast (posDelSet p ∩ (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ))ᶜ ∈
      S.Ω (F + 4 * p + 34) (7 * (D + 6) + 3 + 3) (p + 2) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega)
      (Work.WilG0.Omega_inter2 hEps hEc)
  have hX : projLast (posEpsSet p ∩
      (projLast (posDelSet p ∩ (Work.WilG0.projLastIter (p + 3) 4 (Gset p A))ᶜ))ᶜ) ∈
      S.Ω (F + 4 * p + 35) (7 * (D + 6) + 3 + 3) (p + 1) :=
    Work.WilG0.Omega_mono_FD (by omega) le_rfl (S.proj hInt2)
  have hZ : projChain p A ∈ S.Ω (F + 4 * p + 36) (7 * D + 48) (p + 1) :=
    Work.WilG0.Omega_mono_FD (by omega) (by omega) (S.compl hX)
  -- transport the set identity and weaken the polynomial evaluation
  change fibreCauchySet p A ∈
    S.Ω (F + (4 * p + 36)) ((Polynomial.C 7 * Polynomial.X + Polynomial.C 48).eval D) (p + 1)
  rw [fibreCauchySet_eq_projChain p A
    (fun z ε δ w => snocIt_mem_Gset p A z ε δ w)]
  have hb : (Polynomial.C 7 * Polynomial.X + Polynomial.C 48 : Polynomial ℕ).eval D =
      7 * D + 48 := by
    simp [Polynomial.eval_add, Polynomial.eval_mul]
  refine Work.WilG0.Omega_mono_FD (by omega) ?_ hZ
  rw [hb]

end Work.WilG4a.CD
