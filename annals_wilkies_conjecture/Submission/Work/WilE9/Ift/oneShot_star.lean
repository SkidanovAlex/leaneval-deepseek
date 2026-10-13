import Mathlib
import Submission.Work.WilE9.Ift.OneShotDefs
import Submission.Work.WilE9.Ift.OneShot.oneShotSet_set
import Submission.Work.WilE9.Ift.OneShot.oneShotSet_deg_le
import Submission.Work.WilE9.Ift.OneShot.oneShotBasic_deg_le
import Submission.Work.WilE9.Ift.OneShot.exists_clean
import Submission.Work.WilE9.Ift.OneShot.poly_eval_le
import Submission.Work.WilE9.Ift.OneShot.mvpoly_eval_eval2
import Submission.Work.WilE8.StarOfSemipfLe.star_of_semipf_le

set_option maxHeartbeats 1000000
noncomputable section

namespace Work.WilE9.Ift
open WilkiesDesign WilkiesDesign.E

/-! ## Elementary index lemmas for the one-shot construction -/

/-- `Fin.init` on a non-dependent tuple. -/
theorem fin_init_apply {n : ℕ} (f : Fin (n + 1) → ℝ) (i : Fin n) :
    Fin.init f i = f (Fin.castSucc i) := by
  have h : Fin.init f = fun i => f (Fin.castSucc i) := Fin.init_def
  rw [h]

/-- `oneShotInj` on the base coordinates. -/
theorem oneShotInj_castAdd {n m : ℕ} (i : Fin n) :
    oneShotInj n m (Fin.castAdd (1 + m) i) = Fin.castAdd (1 + m) (Fin.castSucc i) :=
  Work.WilE8.Star.skipInj_castAdd_castSucc (n := n) (m := 1 + m) i

/-- The value of `insCoord` on the coordinates coming from the first `n` base coordinates. -/
theorem insCoord_castAdd_castSucc {n m : ℕ} (w : Fin (n + m) → ℝ) (t : ℝ) (i : Fin n) :
    Work.WilE8.Star.insCoord n m w t (Fin.castAdd m (Fin.castSucc i)) = w (Fin.castAdd m i) := by
  simp only [Work.WilE8.Star.insCoord]
  rw [Fin.append_left, Fin.snoc_castSucc]

/-! ## The point set of the one-shot construction -/

/-- **The projection identity of the one-shot construction.**  The projection of the
semi-Pfaffian set of the construction onto the first `n+1` coordinates is exactly the target
set of `oneShot_star`: a point `(x, z)` with `|z| ≤ 1` lies in the projection if and only if
there is a point `Z` of `Y` whose `n` base coordinates are `x` and which satisfies the new
equation `z * Q^(2|L|) = P_L`. -/
theorem projFirst_oneShotSet {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (Y : SemiPf (n + (1 + m))) :
    projFirst (n + 1) (1 + m) '' (oneShotSet c F L Y).set = oneShotTarget c F L Y := by
  rw [OneShot.oneShotSet_set c F L Y]
  ext z
  constructor
  · rintro ⟨p, ⟨hcube, hmem, heq⟩, rfl⟩
    refine ⟨?_, fun i => p (oneShotInj n m i), hmem, ?_, heq⟩
    · show |p (Fin.castAdd (1 + m) (Fin.last n))| ≤ 1
      exact hcube (oneShotNew n m)
    · intro i
      rw [fin_init_apply]
      show p (oneShotInj n m (Fin.castAdd (1 + m) i)) =
        p (Fin.castAdd (1 + m) (Fin.castSucc i))
      rw [oneShotInj_castAdd]
  · rintro ⟨hz, Z, hZ, hcoord, heq⟩
    have hZc : Z ∈ cubeC (n + (1 + m)) := Work.WilE8.SemiPf.set_subset_cube Y hZ
    have hins : (fun i => Work.WilE8.Star.insCoord n (1 + m) Z (z (Fin.last n))
        (oneShotInj n m i)) = Z := by
      funext i
      exact Work.WilE8.Star.insCoord_skipInj n (1 + m) Z (z (Fin.last n)) i
    refine ⟨Work.WilE8.Star.insCoord n (1 + m) Z (z (Fin.last n)), ⟨?_, ?_, ?_⟩, ?_⟩
    · exact Work.WilE8.Star.insCoord_cube n (1 + m) hZc hz
    · rw [hins]
      exact hZ
    · rw [Work.WilE8.Star.insCoord_new, hins]
      exact heq
    · funext i
      refine Fin.lastCases ?_ ?_ i
      · show Work.WilE8.Star.insCoord n (1 + m) Z (z (Fin.last n))
          (Fin.castAdd (1 + m) (Fin.last n)) = z (Fin.last n)
        rw [Work.WilE8.Star.insCoord_new]
      · intro i'
        show Work.WilE8.Star.insCoord n (1 + m) Z (z (Fin.last n))
          (Fin.castAdd (1 + m) (Fin.castSucc i')) = z (Fin.castSucc i')
        rw [insCoord_castAdd_castSucc, hcoord i', fin_init_apply]

/-! ## The degree polynomial -/

/-- Evaluation of the bounding polynomial `D + (D+1) * PolyB` of the one-shot construction. -/
theorem eval_bound_poly {D l : ℕ} (PolyB : MvPolynomial (Fin 2) ℕ) :
    MvPolynomial.eval ![D, l] (MvPolynomial.X 0 + (MvPolynomial.X 0 + 1) * PolyB)
      = D + (D + 1) * MvPolynomial.eval ![D, l] PolyB := by
  simp [map_add, map_mul, MvPolynomial.eval_X]

/-- **The one-shot construction of BNZ §3 (step 3).**  Fix the chain `c`, the system
`F : Fin (1+m) → EAPoly (n + (1+m)) r` (the equations of an effectively smooth piece: the first
`n` coordinates are the base, coordinate `n` is the graph coordinate `τ`, the last `m` are the
auxiliary `w`'s) and the derivative order `L`.  Then there are a constant format budget `a` and a
two-variable degree polynomial `b` such that for every semi-Pfaffian set `Y` of bounded format
(`Y.fmt ≤ F'`) whose degree dominates the degrees of the equations, the set of pairs `(x, z)`
with `|z| ≤ 1` for which there is a point `Z ∈ Y.set` whose first `n` coordinates are `x` and
which satisfies

  `z · (Q Z) ^ (2 |L|) = P_L Z`,

`Q = jq c F` and `P_L = iftP c F 0 L` the implicit-derivative polynomial of BNZ §3, is a `Star`
set of format `≤ a` and degree `≤ b (Y.deg, |L|)`.  This is the single new variable and the
single new equation that turn the equations of the piece into a description of the `L`-th
derivative of the piece function; because `b` is polynomial in both arguments, the format stays
fixed and the degree grows only polynomially in the order, which is the content of sharp
derivatives.

Construction: extend `Y` by the one fresh coordinate `z` inserted between the base and the fibre
block (`Work.WilE8.SemiPf.extend` with `Work.WilE8.skipInj`, `Work.WilE8.Extend.semipf_set_extend`
— note `SemiPf.set` always intersects with the cube, which is where the `|z| ≤ 1` conjunct and
the automatic `|xᵢ| ≤ 1` come from), add the single basic condition `z * Q^(2|L|) - P_L = 0`
(`Work.WilE5.semiPfAnd`, `semiPfAnd_set`, `semiPfAnd_deg`, `semiPfAnd_fmt`), and project the last
`1+m` coordinates away, packaging with `Work.WilE8.E2.star_of_semipf` (which is why
`E2_components` is the leading hypothesis, copied verbatim from the frozen area-E file, and why
`Y.fmt ≤ F'` is needed: it bounds the number of pieces through the component bound).  The degree
bound uses `Work.WilE9.Deg.iftP_totalDegree_le` for `deg P_L` and `Matrix.det` total-degree
bookkeeping for `deg Q ≤ (1+m)^2 · Y.deg`.  (Implementation note: if `Y` carries a basic of degree
`0`, that basic is empty and `Y.set = cubeC`; otherwise every basic has `deg ≥ 1`, so
`Y.basics.length ≤ Y.deg` bounds the additive degree.) -/
theorem oneShot_star {n m r F' : ℕ} (c : WilkiesDesign.E.EAChain (n + (1 + m)) r)
    (F : Fin (1 + m) → WilkiesDesign.E.EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (hE2 : ∀ F'' : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F'' →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (Y : WilkiesDesign.E.SemiPf (n + (1 + m))),
      Y.fmt ≤ F' → (∀ j, (F j).totalDegree ≤ Y.deg) →
      WilkiesDesign.E.Star a (MvPolynomial.eval ![(Y.deg : ℕ), L.length] b) (n + 1)
        {z : Fin (n + 1) → ℝ | |z (Fin.last n)| ≤ 1 ∧
          ∃ Z : Fin (n + (1 + m)) → ℝ,
            Z ∈ Y.set ∧
            (∀ i : Fin n, Z (Fin.castAdd (1 + m) i) = Fin.init z i) ∧
            z (Fin.last n) *
              (WilkiesDesign.E.eaEval c (Work.WilE9.jQ c F) Z) ^ (2 * L.length) =
              WilkiesDesign.E.eaEval c (Work.WilE9.iftP c F (0 : Fin (1 + m)) L) Z} := by
  classical
  obtain ⟨PolyB, hPolyB⟩ := OneShot.oneShotBasic_deg_le m
  refine ⟨(n + 1 + (1 + m)) + F' + r, Polynomial.eval₂ MvPolynomial.C
      (MvPolynomial.X 0 + (MvPolynomial.X 0 + 1) * PolyB)
      ((hE2 ((n + 1 + (1 + m)) + F' + r)).choose * Polynomial.X), ?_⟩
  intro Y hYfmt hYdeg
  obtain ⟨Y1, hY1set, hY1r, hY1deg, hY1len⟩ := OneShot.exists_clean (n + (1 + m)) Y
  have hYr : Y.r ≤ F' := by
    have h := hYfmt
    simp only [SemiPf.fmt] at h
    omega
  have hXfmt : (oneShotSet c F L Y1).fmt ≤ (n + 1 + (1 + m)) + F' + r := by
    rw [oneShotSet_fmt]
    omega
  have hstar := Work.WilE8.StarOfSemipfLe.star_of_semipf_le hE2 (n + 1) (1 + m)
    ((n + 1 + (1 + m)) + F' + r) (oneShotSet c F L Y1) hXfmt
  rw [projFirst_oneShotSet] at hstar
  have htarget : oneShotTarget c F L Y1 = oneShotTarget c F L Y := by
    unfold oneShotTarget
    rw [hY1set]
  rw [htarget] at hstar
  have hB : (oneShotBasic c F L).deg ≤ MvPolynomial.eval ![Y.deg, L.length] PolyB :=
    hPolyB c F L Y.deg hYdeg
  have hXd : (oneShotSet c F L Y1).deg ≤
      MvPolynomial.eval ![Y.deg, L.length]
        (MvPolynomial.X 0 + (MvPolynomial.X 0 + 1) * PolyB) := by
    have h1 := OneShot.oneShotSet_deg_le c F L Y1
    have h2 : Y1.deg + Y1.basics.length * (oneShotBasic c F L).deg ≤
        Y.deg + (Y.deg + 1) * (oneShotBasic c F L).deg :=
      Nat.add_le_add hY1deg (Nat.mul_le_mul hY1len le_rfl)
    have h3 : Y.deg + (Y.deg + 1) * (oneShotBasic c F L).deg ≤
        MvPolynomial.eval ![Y.deg, L.length]
          (MvPolynomial.X 0 + (MvPolynomial.X 0 + 1) * PolyB) := by
      rw [eval_bound_poly]
      exact Nat.add_le_add le_rfl (Nat.mul_le_mul le_rfl hB)
    omega
  have hmul : (hE2 ((n + 1 + (1 + m)) + F' + r)).choose.eval (oneShotSet c F L Y1).deg *
        (oneShotSet c F L Y1).deg ≤
      MvPolynomial.eval ![(Y.deg : ℕ), L.length]
        (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0 + (MvPolynomial.X 0 + 1) * PolyB)
          ((hE2 ((n + 1 + (1 + m)) + F' + r)).choose * Polynomial.X)) := by
    rw [OneShot.mvpoly_eval_eval2, Polynomial.eval_mul, Polynomial.eval_X]
    exact Nat.mul_le_mul (OneShot.poly_eval_le hXd) hXd
  exact Work.WilE8.Star.mono hstar le_rfl hmul

end Work.WilE9.Ift
