import Mathlib
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.TopLayer
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.CuspChartAux
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **The recovered layer point of the *unslabbed* collar source is the layer point of its own
coordinates.**  For a point `q = (x,s)` of `cuspSourceTop v c δ` (the box of side `2δ` with height in
`(s₁, sTop)`, on or above the ceiling `s ≥ β(x)`) the first component of `cuspInvOuter v q` is
`t • bndOfU (outerU v (xOf q))` with

  `t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`,

and `t > 0`, so its sup norm `‖·‖∞ = |t|` is `t` itself.  Hence the first component is
`‖(cuspInvOuter v q).1‖∞ • bndOfU (outerU v (xOf q))` — the point that the layer chart
`layerPtI (cuspAnchor v c)` reconstructs from the `(u,t)`-coordinates of `cuspTopF`.

This is the unslabbed analogue of `cuspInvOuter_fst_eq_smul`, whose positivity proof uses the
slabbed window `s < s_J` together with `β(x) ≤ s`; here only `s < sTop` is available, and positivity
follows from `β(x) ≤ β_max` and `β_max · sTop < s_J²` (`Work.Cusp.betaMax_mul_sTop_lt_sJ_sq`). -/
lemma cuspInvOuter_fst_eq_smulTop (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) :
    (cuspInvOuter v q).1 = nrm (cuspInvOuter v q).1 • bndOfU (outerU v (xOf q)) := by
  obtain ⟨hbox, -⟩ := hq
  obtain ⟨-, hs1, hlt⟩ := hbox
  have hq3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hb_lt_sJ : beta (xOf q) < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  set t : ℝ := 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
      (2 * (Real.log (beta (xOf q)) - Real.log sJ)) with ht
  have ht_pos : 0 < t := by
    rw [ht]
    have hDpos : 0 < Real.log sJ - Real.log (beta (xOf q)) := by
      have h := Real.log_lt_log hbpos hb_lt_sJ; linarith
    have hprod : q 3 * beta (xOf q) < sJ ^ 2 := by
      have h1 : q 3 * beta (xOf q) < sTop * beta (xOf q) :=
        mul_lt_mul_of_pos_right hlt hbpos
      have h2 : sTop * beta (xOf q) ≤ sTop * betaMax :=
        mul_le_mul_of_nonneg_left (beta_le_max _) (le_of_lt sTop_pos)
      have h3 : sTop * betaMax < sJ ^ 2 := by rw [mul_comm]; exact betaMax_mul_sTop_lt_sJ_sq
      linarith
    have hAJ : Real.log (q 3) - Real.log (beta (xOf q))
        < 2 * (Real.log sJ - Real.log (beta (xOf q))) := by
      have h := Real.log_lt_log (mul_pos hq3pos hbpos) hprod
      rw [Real.log_mul (ne_of_gt hq3pos) (ne_of_gt hbpos), Real.log_pow] at h
      push_cast at h
      linarith
    have hden : 2 * (Real.log (beta (xOf q)) - Real.log sJ)
        = -(2 * (Real.log sJ - Real.log (beta (xOf q)))) := by ring
    rw [hden, div_neg]
    have hlt' : (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log sJ - Real.log (beta (xOf q)))) < 1 := by
      rw [div_lt_one (by linarith : (0:ℝ) < 2 * (Real.log sJ - Real.log (beta (xOf q))))]
      exact hAJ
    linarith
  have hpe : (cuspInvOuter v q).1 = t • bndOfU (outerU v (xOf q)) := by rw [ht]; rfl
  rw [hpe, nrm_smul, nrm_bndOfU, mul_one, abs_of_pos ht_pos]

/-- **The upper branch of the collar chart of `M̂` is the point of the filling piece recovered by the
outer chart.**  The collar coordinate `cuspTopF v c δ hδ` sends a point `q` of the collar source to
`(u,t,y) = (outerU v (xOf q), ‖(cuspInvOuter v q).1‖∞, outerY v (xOf q))`; applying the layer chart
`layerPtI (cuspAnchor v c)` to `(u,t)` and the `mod`-reduction of `y` to the torus gives exactly the
filling-piece point `(cuspInvOuter v q).1, (cuspInvOuter v q).2` of the gluing data `D`:

* the square coordinate is the recovered point `(cuspInvOuter v q).1`, which the layer chart
  reconstructs from its own `(u,t)`-coordinates by `cuspInvOuter_fst_eq_smulTop`;
* the torus coordinate `outerY v (xOf q)` is the second component of `cuspInvOuter v q`. -/
theorem cuspTopUp_eq (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) (q : {q : E4 // q ∈ cuspSourceTop v c δ}) :
    cuspTopUp a v D c δ hδ q =
      ((⟨(cuspInvOuter v q.1).1,
          cuspInvOuter_mem_SqTop v c δ q.1 ⟨q.2.1, q.2.2⟩⟩ : Work.Space.SquarePt),
       D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ)))) := by
  unfold cuspTopUp
  simp only [cuspTopF]
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    exact (cuspInvOuter_fst_eq_smulTop v c δ q.1 q.2).symm
  · rfl

end Work.Cusp
