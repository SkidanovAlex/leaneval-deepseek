import Mathlib
import Submission.Work.Drive.qwDefs
import Submission.Work.Drive.rank_triplet_Xa

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-!
# Smoothness of the level-`m` augmented map `qPsiM`

The map `qPsiM r m` sends `p = (c, τ) : Coeff × QP` to the pair consisting of the triplet
`(qU × qV, qU × qS, qV × qS)` of pairwise collinearity conditions and the function sending a
`m`-tuple of rows and a `m`-tuple of columns to the corresponding `m`-minor of the partial matrix
`i ↦ qPartial r p i`.

Every ingredient is smooth:

* the triplet is `C^∞` (`Work.Drive.contDiff_triplet`, from `rank_triplet_Xa.lean`);
* each entry of the partial matrix is `(eTgt (qPartial r p i)).ofLp j`, and `qPartial` is built out
  of the jointly smooth maps `(c,t) ↦ pertV r c t`, `(c,t) ↦ pertVelV r c t`
  (`contDiff_pertV_joint`, `contDiff_pertVelV_joint`) via `cross3`
  (`Work.Drive.contDiff_cross3_pair`);
* a determinant is a polynomial (via `Matrix.det_apply'`) in its entries.

The `m = 0` case (empty determinant) is the constant `1` and is covered by the same argument
(the empty product is `1` and the empty permutation sum is a single term).
-/

/-- **Each partial is smooth.**  The `i`-th partial of the four-point collinearity map, as a
function of the coefficient and the window, is `C^∞`. -/
lemma contDiff_qPartial_apply {r : ℝ → Space} (hr : IsSmoothKnot r) (i : Fin 4) :
    ContDiff ℝ ⊤ (fun p : Coeff × QP => qPartial r p i) := by
  have hc3 : ∀ {f g : Coeff × QP → Space}, ContDiff ℝ ⊤ f → ContDiff ℝ ⊤ g →
      ContDiff ℝ ⊤ (fun p : Coeff × QP => cross3 (f p) (g p)) :=
    fun hf hg => contDiff_cross3_pair.comp (hf.prodMk hg)
  have hA : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qA p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp (contDiff_fst.prodMk (contDiff_qA.comp contDiff_snd))
  have hZ : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qZ p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp (contDiff_fst.prodMk (contDiff_qZ.comp contDiff_snd))
  have hW : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qW p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp (contDiff_fst.prodMk (contDiff_qW.comp contDiff_snd))
  have hB : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qB p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp (contDiff_fst.prodMk (contDiff_qB.comp contDiff_snd))
  have vA : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertVelV r p.1 (qA p.2)) :=
    (contDiff_pertVelV_joint hr.smooth).comp (contDiff_fst.prodMk (contDiff_qA.comp contDiff_snd))
  have vZ : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertVelV r p.1 (qZ p.2)) :=
    (contDiff_pertVelV_joint hr.smooth).comp (contDiff_fst.prodMk (contDiff_qZ.comp contDiff_snd))
  have vW : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertVelV r p.1 (qW p.2)) :=
    (contDiff_pertVelV_joint hr.smooth).comp (contDiff_fst.prodMk (contDiff_qW.comp contDiff_snd))
  have vB : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertVelV r p.1 (qB p.2)) :=
    (contDiff_pertVelV_joint hr.smooth).comp (contDiff_fst.prodMk (contDiff_qB.comp contDiff_snd))
  obtain ⟨k, hk⟩ := i
  interval_cases k <;>
    simp only [qPartial, quadPartial.eq_1, quadPartial.eq_2, quadPartial.eq_3, quadPartial.eq_4,
      velocity, deriv_pertV_eq hr]
  · exact ContDiff.prodMk
      (ContDiff.add (hc3 vA.neg (hW.sub hA)) (hc3 (hZ.sub hA) vA.neg))
      (ContDiff.add (hc3 vA.neg (hB.sub hA)) (hc3 (hZ.sub hA) vA.neg))
  · exact ContDiff.prodMk (hc3 vZ (hW.sub hA)) (hc3 vZ (hB.sub hA))
  · exact ContDiff.prodMk (hc3 (hZ.sub hA) vW) contDiff_const
  · exact ContDiff.prodMk contDiff_const (hc3 (hZ.sub hA) vB)

/-- **Each entry of the partial matrix is smooth.**  The map sending `p` to the `j`-th coordinate
of the `i`-th partial (after the linear identification `eTgt` with `ℝ⁶`) is `C^∞`. -/
lemma contDiff_minorEntry {r : ℝ → Space} (hr : IsSmoothKnot r) (i : Fin 4) (j : Fin 6) :
    ContDiff ℝ ⊤ (fun p : Coeff × QP => (eTgt (qPartial r p i)).ofLp j) := by
  have hpar : ContDiff ℝ ⊤ (fun p : Coeff × QP => qPartial r p i) := contDiff_qPartial_apply hr i
  have h1 : ContDiff ℝ ⊤ (fun p : Coeff × QP => eTgt (qPartial r p i)) := eTgt.contDiff.comp hpar
  have h2 : ContDiff ℝ ⊤ (fun x : Tgt => x.ofLp j) := by fun_prop
  exact h2.comp h1

/-- **The determinant is smooth in the entries.**  If every entry of a square matrix depends
smoothly on a parameter, so does the determinant (a polynomial in the entries). -/
lemma contDiff_det_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    {f : E → Fin m → Fin m → ℝ} (hf : ∀ i j, ContDiff ℝ ⊤ (fun p => f p i j)) :
    ContDiff ℝ ⊤ (fun p => (Matrix.of (f p)).det) := by
  have hsum : (fun p : E => (Matrix.of (f p)).det) =
      (fun p => ∑ σ : Equiv.Perm (Fin m), ↑↑(Equiv.Perm.sign σ) * ∏ i, f p (σ i) i) := by
    funext p
    rw [Matrix.det_apply']
    simp [Matrix.of_apply]
  rw [hsum]
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  exact hf (σ i) i

/-- **Each minor depends smoothly on the parameter.** -/
lemma contDiff_qMinor {r : ℝ → Space} (hr : IsSmoothKnot r) (m : ℕ)
    (a : Fin m → Fin 4) (b : Fin m → Fin 6) :
    ContDiff ℝ ⊤ (fun p : Coeff × QP => qMinor r p m (a, b)) := by
  have h : ContDiff ℝ ⊤ (fun p : Coeff × QP =>
      (Matrix.of (fun i j : Fin m => (eTgt (qPartial r p (a i))).ofLp (b j))).det) :=
    contDiff_det_of_entries (fun i j => contDiff_minorEntry hr (a i) (b j))
  simpa only [qMinor] using h

open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **Smoothness of the level-`m` augmented map.**

For a smooth knot `r` and every `m : ℕ`, the map
`p ↦ (triplet r p, all m-minors of the partial matrix)` is `C¹` on `Coeff × QP`.

The ingredients are all smooth: the joint smoothness of `(c, t) ↦ pertV r c t` and of
`(c, t) ↦ pertVelV r c t` (`Work.Drive.contDiff_pertV_joint`, `Work.Drive.contDiff_pertVelV_joint`),
the smoothness of `cross3` on `Space`, the smooth coordinates `qA … qB` of the window
(`Work.Drive.contDiff_qA` etc.), and the fact that `quadPartial (pertV r c) a z w b` is a fixed
polynomial expression in the four values and four velocities — so the entries of the partial matrix
are smooth, and each `m`-minor is a polynomial (a determinant) in those entries.  The special case
`m = 0` (empty determinant) is the constant `1`. -/
theorem contDiff_qPsiM {r : ℝ → Space} (hr : IsSmoothKnot r) (m : ℕ) :
    ContDiff ℝ 1 (qPsiM r m) := by
  have hmin : ContDiff ℝ ⊤ (fun p : Coeff × QP =>
      fun (a : Fin m → Fin 4) (b : Fin m → Fin 6) => qMinor r p m (a, b)) := by
    apply contDiff_pi.2
    intro a
    apply contDiff_pi.2
    intro b
    exact contDiff_qMinor hr m a b
  have hall : ContDiff ℝ ⊤ (qPsiM r m) := by
    change ContDiff ℝ ⊤ (fun p : Coeff × QP =>
      (triplet r p, fun (a : Fin m → Fin 4) (b : Fin m → Fin 6) => qMinor r p m (a, b)))
    exact (contDiff_triplet hr).prodMk hmin
  exact ContDiff.of_le hall le_top

end

end Work.Drive
