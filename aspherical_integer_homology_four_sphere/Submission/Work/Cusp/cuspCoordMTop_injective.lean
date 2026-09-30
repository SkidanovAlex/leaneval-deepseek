import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.cuspInvOuter_heightTop
import Submission.Work.Cusp.ThetaOuter_add_int
import Submission.Work.Cusp.TopWindow
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU
import Submission.Work.Cusp.beta_add_int
import Submission.Work.Cusp.cuspX_outerU_outerY

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Injectivity of the *unslabbed* collar coordinate `cuspCoordMTop` on `M̂`

`cuspCoordM` is injective on the slabbed box `cuspChartBox v c δ`
(`Work.Cusp.cuspCoordM_injective`).  Here we do the same for the *unslabbed* collar box
`cuspBoxTop v c δ` (no condition on the meridian coordinate `outerU v x`, heights in
`(s₁, sTop)`), which is the box that covers the corner directions of the filling square.

The structure of the proof is the one of the slabbed family, with two differences.

* The upper branch recovers the layer point
  `(cuspInvOuter v q).1 = t • bndOfU (outerU v (xOf q))` with the *sign* of `t` determined: on the
  collar source `cuspSourceTop v c δ` the comparison `β(x) · s < s_J²`
  (`Work.Cusp.beta_mul_sTop_lt_sJ_sq`, through `s < sTop`, `β ≤ β_max`) forces `t > 0`
  (`cuspInvOuter_scalar_pos`).  Consequently `bndOfU` is determined by the layer point and
  `uPerim_bndOfU` gives `Int.fract (outerU v x') = Int.fract (outerU v x)`: the meridian
  coordinates differ by an **integer** `k` (in the slabbed case they were equal, because the slab
  `0 ≤ outerU v x < 1` pins the fractional part).
* Apart from that the argument is the same: the difference of the two cusp coordinates is the
  lattice vector `k σ_v + m₀λ₂ + m₁λ₃`, whose coordinates are integers, while the box has side
  `2δ ≤ 1`; hence the difference vanishes, the pair `(outerU, outerY)` is equal, `t = t'` (from the
  equality of the sup norms) and the two heights agree by the height round trip
  `cuspInvOuter_heightTop`.  As in the slabbed case, a point below the ceiling and a point on or
  above it can only agree when the upper point lies *on* the ceiling
  (`cuspInvOuter_nrm_eq_one_ceilingTop`).
-/

noncomputable section

open Set Topology Function

namespace Work.Cusp

/-! ### Two elementary computations on the cusp lattice -/

/-- `ofInt3` is additive. -/
private lemma ofInt3_add (A B : Fin 3 → ℤ) : ofInt3 A + ofInt3 B = ofInt3 (A + B) := by
  ext j
  fin_cases j <;> simp [ofInt3, PiLp.add_apply]

/-- The coordinates of the slope `σ_v` are the integers
`(κ_{v,1})_i + b_v (κ_{v,2})_i + c_v (κ_{v,3})_i` (`slopeB`, `slopeC` are `ℤ`-valued). -/
private lemma slope_apply (v : Fin 5) (i : Fin 3) :
    slope v i = ((kappa v 0 i + slopeB v * kappa v 1 i + slopeC v * kappa v 2 i : ℤ) : ℝ) := by
  fin_cases i <;>
    simp [Work.Cusp.slope, kv, ofInt3, PiLp.add_apply, PiLp.smul_apply] <;>
    push_cast <;> ring

/-- **An integer shift of the meridian parameter** translates the cusp coordinate by the integer
vector `k σ_v`. -/
private lemma cuspX_add_int_slope (v : Fin 5) (u : ℝ) (y : E2) (k : ℤ) :
    cuspX v (u + (k : ℝ)) y = cuspX v u y +
      ofInt3 (fun j => k * (kappa v 0 j + slopeB v * kappa v 1 j + slopeC v * kappa v 2 j)) := by
  have h : (k : ℝ) • slope v =
      ofInt3 (fun j => k * (kappa v 0 j + slopeB v * kappa v 1 j + slopeC v * kappa v 2 j)) := by
    ext j
    fin_cases j <;>
      simp [Work.Cusp.slope, kv, ofInt3, PiLp.add_apply, PiLp.smul_apply] <;>
      push_cast <;> ring
  simp only [cuspX, cuspY, add_smul]
  rw [h]
  abel

/-! ### The positivity of the recovered layer parameter -/

/-- **The scalar recovered by `cuspInvOuter` on the unslabbed collar source is positive.**
Writing `B = β(x)`, `A = log s − log B` and `J = log s_J − log B`,
`1 + A/(2(log B − log s_J)) = 1 − A/(2J) > 0` is `A < 2J`, i.e. `s · B < s_J²`, which follows from
`s < sTop`, `B ≤ β_max` and `β_max · sTop < s_J²`. -/
private lemma cuspInvOuter_scalar_pos (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) :
    0 < 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ)) := by
  obtain ⟨hbox, -⟩ := hq
  obtain ⟨-, hs1, hlt⟩ := hbox
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hs3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have hprod : q 3 * beta (xOf q) < sJ ^ 2 := by
    have h1 : q 3 * beta (xOf q) < sTop * beta (xOf q) := mul_lt_mul_of_pos_right hlt hbpos
    have h2 : sTop * beta (xOf q) ≤ sTop * betaMax :=
      mul_le_mul_of_nonneg_left (beta_le_max _) (le_of_lt sTop_pos)
    have h3 : sTop * betaMax < sJ ^ 2 := by rw [mul_comm]; exact betaMax_mul_sTop_lt_sJ_sq
    linarith
  have hlog : Real.log (q 3) + Real.log (beta (xOf q)) < 2 * Real.log sJ := by
    have h := Real.log_lt_log (mul_pos hs3pos hbpos) hprod
    rw [Real.log_mul (ne_of_gt hs3pos) (ne_of_gt hbpos), Real.log_pow] at h
    push_cast at h
    linarith
  have hJ : 0 < 2 * (Real.log sJ - Real.log (beta (xOf q))) := by
    have h := Real.log_lt_log hbpos (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)
    linarith
  have hA : Real.log (q 3) - Real.log (beta (xOf q))
      < 2 * (Real.log sJ - Real.log (beta (xOf q))) := by linarith
  have hkey : 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ))
      = 1 - (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log sJ - Real.log (beta (xOf q)))) := by
    have hden : 2 * (Real.log (beta (xOf q)) - Real.log sJ)
        = -(2 * (Real.log sJ - Real.log (beta (xOf q)))) := by ring
    rw [hden, div_neg]
    ring
  rw [hkey, sub_pos, div_lt_one hJ]
  exact hA

/-- **The sup norm of the recovered layer point on the collar source is the recovered scalar**
(no absolute value: the scalar is positive). -/
private lemma cuspInvOuter_nrm_eq_scalar (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) :
    nrm (cuspInvOuter v q).1
      = 1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log (beta (xOf q)) - Real.log sJ)) := by
  rw [cuspInvOuter_nrm_fst, abs_of_pos (cuspInvOuter_scalar_pos v c δ q hq)]

/-- **A point of the unslabbed collar source whose recovered layer parameter has sup norm `1` lies
on the ceiling.**  `nrm = 1` is `1 − A/(2J) = 1`, i.e. `log s = log β(x)`, and both are positive. -/
private lemma cuspInvOuter_nrm_eq_one_ceilingTop (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hq : q ∈ cuspSourceTop v c δ) (h1 : nrm (cuspInvOuter v q).1 = 1) :
    q 3 = beta (xOf q) := by
  obtain ⟨hbox, hbeta_le⟩ := hq
  have hs1 : s1 < q 3 := hbox.2.1
  have hbpos : 0 < beta (xOf q) := beta_pos _
  have hs3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have hne : 2 * (Real.log (beta (xOf q)) - Real.log sJ) ≠ 0 := by
    have h := Real.log_lt_log hbpos (lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ)
    intro hc; linarith
  have hsc := cuspInvOuter_nrm_eq_scalar v c δ q ⟨hbox, hbeta_le⟩
  rw [h1] at hsc
  have hA : Real.log (q 3) - Real.log (beta (xOf q)) = 0 := by
    have h : (Real.log (q 3) - Real.log (beta (xOf q))) /
        (2 * (Real.log (beta (xOf q)) - Real.log sJ)) = 0 := by linarith
    rcases div_eq_zero_iff.mp h with h' | h'
    · exact h'
    · exact absurd h' hne
  have hlog : Real.log (q 3) = Real.log (beta (xOf q)) := by linarith
  calc q 3 = Real.exp (Real.log (q 3)) := (Real.exp_log hs3pos).symm
    _ = Real.exp (Real.log (beta (xOf q))) := by rw [hlog]
    _ = beta (xOf q) := Real.exp_log hbpos

/-! ### The two branches of the unslabbed collar coordinate -/

/-- The upper branch of the unslabbed collar coordinate, as a map into `M̂` on the whole collar
source. -/
private def cuspCoordMTopUp (a : Work.Space.Assembly) (v : Work.Space.Cusp) (D : CuspGlueData a v)
    (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspSourceTop v c δ}) : a.Mhat :=
  a.incW v
    ((⟨(cuspInvOuter v q.1).1, by
        simpa only [Work.Space.Sq, Sq] using cuspInvOuter_mem_SqTop v c δ q.1 q.2⟩ :
        Work.Space.SquarePt),
      D.tor.symm (fun i => (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1 : ℝ))))

/-- **The two branches of `cuspCoordMTop` agree at the ceiling** of the unslabbed box. -/
private lemma incMbar_mbarLowTop_eq (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (q : E4)
    (hbox : q ∈ cuspBoxTop v c δ) (hceil : q 3 = beta (xOf q)) :
    a.incMbar (D.mbarLow q) =
      a.incW v
        ((⟨(cuspInvOuter v q).1, by
            simpa only [Work.Space.Sq, Sq] using
              cuspInvOuter_mem_SqTop v c δ q ⟨hbox, le_of_eq hceil.symm⟩⟩ :
            Work.Space.SquarePt),
          D.tor.symm (fun i => (((cuspInvOuter v q).2 i : ℝ) : AddCircle (1 : ℝ)))) := by
  have hqc : q = ceilingPt (xOf q) := by
    ext i
    fin_cases i <;> simp [ceilingPt, xOf, hceil]
  have hL : D.mbarLow q = D.mbarPt (xOf q) := by
    conv_lhs => rw [hqc]
    rw [← D.mbarPt_eq]
  rw [hL, incMbar_mbarPt_eq a v D (xOf q)]
  have hci : cuspInvOuter v q = (bndOfU (outerU v (xOf q)), outerY v (xOf q)) := by
    simp [cuspInvOuter, xOf, hceil]
  refine incW_pair_congr a v ?_ ?_
  · exact congrArg (fun z : E2 × E2 => z.1) hci.symm
  · exact congrArg (fun z : E2 => D.tor.symm (fun i => ((z i : ℝ) : AddCircle (1 : ℝ))))
      (congrArg (fun z : E2 × E2 => z.2) hci.symm)

/-- **The lower branch computes `cuspCoordMTop` below the ceiling.** -/
private lemma cuspCoordMTop_eq_le (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspBoxTop v c δ})
    (hq : q.1 3 ≤ beta (xOf q.1)) :
    cuspCoordMTop a v D c δ q = a.incMbar (D.mbarLow q.1) := by
  by_cases hlt : q.1 3 < beta (xOf q.1)
  · unfold cuspCoordMTop
    rw [dif_pos hlt]
  · have heq : q.1 3 = beta (xOf q.1) := le_antisymm hq (not_lt.mp hlt)
    unfold cuspCoordMTop
    rw [dif_neg hlt]
    rw [incMbar_mbarLowTop_eq a v D c δ q.1 q.2 heq]

/-- **The upper branch computes `cuspCoordMTop` above the ceiling.** -/
private lemma cuspCoordMTop_eq_ge (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (q : {q : E4 // q ∈ cuspBoxTop v c δ})
    (hq : beta (xOf q.1) ≤ q.1 3) :
    cuspCoordMTop a v D c δ q = cuspCoordMTopUp a v D c δ ⟨q.1, ⟨q.2, hq⟩⟩ := by
  unfold cuspCoordMTop cuspCoordMTopUp
  rw [dif_neg (not_lt.mpr hq)]

/-! ### The two halves of the injectivity -/

/-- **The mixed case**: one point strictly below the ceiling, the other on or above it.  Equality of
the images forces the upper point onto the ceiling, so that both lie in the region where `mbarLow`
is injective. -/
private lemma cuspCoordMTop_mixed (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q q' : {q : E4 // q ∈ cuspBoxTop v c δ})
    (hlt : q.1 3 < beta (xOf q.1)) (hge' : beta (xOf q'.1) ≤ q'.1 3)
    (h : cuspCoordMTop a v D c δ q = cuspCoordMTop a v D c δ q') : q = q' := by
  have hlow := cuspCoordMTop_eq_le a v D c δ q (le_of_lt hlt)
  have hhigh := cuspCoordMTop_eq_ge a v D c δ q' hge'
  have hmix : a.incMbar (D.mbarLow q.1) =
      cuspCoordMTopUp a v D c δ ⟨q'.1, ⟨q'.2, hge'⟩⟩ := hlow.symm.trans (h.trans hhigh)
  simp only [cuspCoordMTopUp] at hmix
  obtain ⟨hx, hglue⟩ := incMbar_eq_incW_imp a v hmix
  have hnrm1 : nrm (cuspInvOuter v q'.1).1 = 1 := by
    have hbdry := (a.glue ⟨D.mbarLow q.1, hx⟩).2
    rw [hglue] at hbdry
    simpa only [Work.Space.Assembly.boundarySet, Work.Space.FillingBdry, Set.mem_ofPred_eq,
      Work.Space.sqNorm, Work.Space.nrm, nrm] using hbdry
  have hceil' : q'.1 3 = beta (xOf q'.1) :=
    cuspInvOuter_nrm_eq_one_ceilingTop v c δ q'.1 ⟨q'.2, hge'⟩ hnrm1
  have h' : a.incMbar (D.mbarLow q.1) = a.incMbar (D.mbarLow q'.1) := by
    rw [cuspCoordMTop_eq_le a v D c δ q (le_of_lt hlt),
        cuspCoordMTop_eq_le a v D c δ q' (le_of_eq hceil')] at h
    exact h
  exact Subtype.ext (D.mbarLow_injTop c δ hδ ⟨q.2, le_of_lt hlt⟩ ⟨q'.2, le_of_eq hceil'⟩
    (a.incMbar_injective h'))

/-- **Both points on or above the ceiling.**  The recovered layer points agree, hence the meridian
coordinates differ by an integer `k` and the torus coordinates by an integer pair `m`; the
difference of the cusp coordinates is therefore the lattice vector `k σ_v + m₀λ₂ + m₁λ₃`, an integer
vector, while the box has side `2δ ≤ 1`.  Hence the cusp coordinates agree, so `t = t'`
(`nrm` of the layer points), the two recovered points of `E2 × E2` agree and the heights agree by
`cuspInvOuter_heightTop`. -/
private lemma cuspCoordMTop_high (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q q' : {q : E4 // q ∈ cuspBoxTop v c δ})
    (hge : beta (xOf q.1) ≤ q.1 3) (hge' : beta (xOf q'.1) ≤ q'.1 3)
    (h : cuspCoordMTop a v D c δ q = cuspCoordMTop a v D c δ q') : q = q' := by
  have hboxq : ∀ i, |xOf q.1 i - c i| < δ := q.2.1
  have hboxq' : ∀ i, |xOf q'.1 i - c i| < δ := q'.2.1
  have hsrcq : q.1 ∈ cuspSourceTop v c δ := ⟨q.2, hge⟩
  have hsrcq' : q'.1 ∈ cuspSourceTop v c δ := ⟨q'.2, hge'⟩
  have hup : cuspCoordMTopUp a v D c δ ⟨q.1, hsrcq⟩
      = cuspCoordMTopUp a v D c δ ⟨q'.1, hsrcq'⟩ := by
    rw [← cuspCoordMTop_eq_ge a v D c δ q hge, ← cuspCoordMTop_eq_ge a v D c δ q' hge']
    exact h
  simp only [cuspCoordMTopUp] at hup
  have hpair := a.incW_injective v hup
  -- the recovered layer points agree
  have hfst : (cuspInvOuter v q.1).1 = (cuspInvOuter v q'.1).1 := by
    have h1 := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : E2)) hpair
    simpa using h1
  -- the torus coordinates agree modulo the period of the torus
  have hsnd : ∀ i : Fin 2, (((cuspInvOuter v q.1).2 i : ℝ) : AddCircle (1:ℝ)) =
      (((cuspInvOuter v q'.1).2 i : ℝ) : AddCircle (1:ℝ)) := by
    have h2 := congrArg (fun z : Work.Space.SquarePt × a.Torus v => z.2) hpair
    have h2' := (Homeomorph.injective D.tor.symm) h2
    intro i
    exact congrFun h2' i
  have hm : ∀ i : Fin 2, ∃ m : ℤ,
      (cuspInvOuter v q'.1).2 i = (cuspInvOuter v q.1).2 i + (m : ℝ) :=
    fun i => (addCircle_one_coe_eq_iff _ _).mp (hsnd i).symm
  choose m hm using hm
  have hy : (cuspInvOuter v q'.1).2 = (cuspInvOuter v q.1).2 + ofInt2 m := by
    ext i
    fin_cases i
    · simpa [ofInt2, PiLp.add_apply] using hm 0
    · simpa [ofInt2, PiLp.add_apply] using hm 1
  have hy' : outerY v (xOf q'.1) = outerY v (xOf q.1) + ofInt2 m := hy
  -- the recovered scalars
  set t : ℝ := 1 + (Real.log (q.1 3) - Real.log (beta (xOf q.1))) /
      (2 * (Real.log (beta (xOf q.1)) - Real.log sJ)) with ht
  set t' : ℝ := 1 + (Real.log (q'.1 3) - Real.log (beta (xOf q'.1))) /
      (2 * (Real.log (beta (xOf q'.1)) - Real.log sJ)) with ht'
  have htpos : 0 < t := cuspInvOuter_scalar_pos v c δ q.1 hsrcq
  have hnrmq : nrm (cuspInvOuter v q.1).1 = t := by
    rw [cuspInvOuter_nrm_eq_scalar v c δ q.1 hsrcq, ht]
  have hnrmq' : nrm (cuspInvOuter v q'.1).1 = t' := by
    rw [cuspInvOuter_nrm_eq_scalar v c δ q'.1 hsrcq', ht']
  have hnrm : t = t' := by
    rw [← hnrmq, ← hnrmq']
    exact congrArg nrm hfst
  have hunf : (cuspInvOuter v q.1).1 = t • bndOfU (outerU v (xOf q.1)) := by
    rw [ht]; rfl
  have hunf' : (cuspInvOuter v q'.1).1 = t' • bndOfU (outerU v (xOf q'.1)) := by
    rw [ht']; rfl
  have hbnd : bndOfU (outerU v (xOf q.1)) = bndOfU (outerU v (xOf q'.1)) := by
    have hh := hfst
    rw [hunf, hunf', ← hnrm] at hh
    have hh2 := congrArg (fun z : E2 => t⁻¹ • z) hh
    simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt htpos)] using hh2
  have hfract : Int.fract (outerU v (xOf q.1)) = Int.fract (outerU v (xOf q'.1)) := by
    have h := congrArg uPerim hbnd
    rwa [uPerim_bndOfU, uPerim_bndOfU] at h
  obtain ⟨k, hk⟩ : ∃ k : ℤ, outerU v (xOf q'.1) - outerU v (xOf q.1) = (k : ℝ) :=
    Int.fract_eq_fract.mp hfract.symm
  have hku : outerU v (xOf q'.1) = outerU v (xOf q.1) + (k : ℝ) := by linarith
  -- the cusp coordinates differ by the integer vector `k σ_v + m₀λ₂ + m₁λ₃`
  have hxq : xOf q'.1
      = cuspX v (outerU v (xOf q.1) + (k : ℝ)) (outerY v (xOf q.1) + ofInt2 m) := by
    rw [← cuspX_outerU_outerY v (xOf q'.1), hku, hy']
  have hmid : cuspX v (outerU v (xOf q.1) + (k : ℝ)) (outerY v (xOf q.1) + ofInt2 m)
      = xOf q.1
        + (ofInt3 (fun i => k * (kappa v 0 i + slopeB v * kappa v 1 i
              + slopeC v * kappa v 2 i))
          + ofInt3 (fun i => m 0 * kappa v 1 i + m 1 * kappa v 2 i)) := by
    rw [cuspX_add_int_ofInt3, cuspX_add_int_slope, cuspX_outerU_outerY, add_assoc]
  have hE : xOf q'.1 - xOf q.1
      = ofInt3 (fun i => k * (kappa v 0 i + slopeB v * kappa v 1 i + slopeC v * kappa v 2 i))
        + ofInt3 (fun i => m 0 * kappa v 1 i + m 1 * kappa v 2 i) := by
    rw [hxq, hmid]
    abel
  have hint : ∀ i : Fin 3, ∃ n : ℤ, xOf q'.1 i - xOf q.1 i = (n : ℝ) := by
    intro i
    refine ⟨k * (kappa v 0 i + slopeB v * kappa v 1 i + slopeC v * kappa v 2 i)
      + (m 0 * kappa v 1 i + m 1 * kappa v 2 i), ?_⟩
    have hd := congrArg (fun z : E3 => z i) hE
    simp only [PiLp.add_apply, PiLp.sub_apply, ofInt3_apply] at hd
    rw [hd]
    push_cast
    ring
  have hxeq : xOf q'.1 = xOf q.1 := by
    ext i
    obtain ⟨n, hn⟩ := hint i
    have hbnd2 : |xOf q'.1 i - xOf q.1 i| < 1 := by
      calc |xOf q'.1 i - xOf q.1 i| = |(xOf q'.1 i - c i) - (xOf q.1 i - c i)| := by
            congr 1; ring
        _ ≤ |xOf q'.1 i - c i| + |xOf q.1 i - c i| := abs_sub _ _
        _ < δ + δ := by linarith [hboxq' i, hboxq i]
        _ ≤ 1 := by linarith
    have h2 : |(n : ℝ)| < 1 := by rw [← hn]; exact hbnd2
    have hn0 : n = 0 := by
      have h3 : n < 1 := by exact_mod_cast (abs_lt.mp h2).2
      have h4 : -1 < n := by exact_mod_cast (abs_lt.mp h2).1
      omega
    have hzero : xOf q'.1 i - xOf q.1 i = 0 := by rw [hn, hn0]; norm_num
    linarith
  -- hence the recovered data and the heights agree
  have huu : outerU v (xOf q'.1) = outerU v (xOf q.1) := congrArg (outerU v) hxeq
  have hye : (cuspInvOuter v q'.1).2 = (cuspInvOuter v q.1).2 :=
    congrArg (fun x => outerY v x) hxeq
  have hci : cuspInvOuter v q'.1 = cuspInvOuter v q.1 := by
    refine Prod.ext ?_ ?_
    · rw [hunf', hunf, ← hnrm, huu]
    · exact hye
  have hh3 : q'.1 3 = q.1 3 := by
    rw [← cuspInvOuter_heightTop v c δ q'.1 hsrcq',
      ← cuspInvOuter_heightTop v c δ q.1 hsrcq, hci]
  refine Subtype.ext ?_
  ext i
  fin_cases i
  · simpa [xOf] using (congrArg (fun z : E3 => z 0) hxeq).symm
  · simpa [xOf] using (congrArg (fun z : E3 => z 1) hxeq).symm
  · simpa [xOf] using (congrArg (fun z : E3 => z 2) hxeq).symm
  · exact hh3.symm

/-! ### The theorem -/

theorem cuspCoordMTop_injective (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    Function.Injective (cuspCoordMTop a v D c δ) := by
  intro q q' h
  by_cases hlt : q.1 3 < beta (xOf q.1)
  · by_cases hlt' : q'.1 3 < beta (xOf q'.1)
    · have h' : a.incMbar (D.mbarLow q.1) = a.incMbar (D.mbarLow q'.1) := by
        rw [cuspCoordMTop_eq_le a v D c δ q (le_of_lt hlt),
            cuspCoordMTop_eq_le a v D c δ q' (le_of_lt hlt')] at h
        exact h
      exact Subtype.ext (D.mbarLow_injTop c δ hδ ⟨q.2, le_of_lt hlt⟩ ⟨q'.2, le_of_lt hlt'⟩
        (a.incMbar_injective h'))
    · exact cuspCoordMTop_mixed a v D c δ hδ q q' hlt (not_lt.mp hlt') h
  · by_cases hlt' : q'.1 3 < beta (xOf q'.1)
    · exact (cuspCoordMTop_mixed a v D c δ hδ q' q hlt' (not_lt.mp hlt) h.symm).symm
    · exact cuspCoordMTop_high a v D c δ hδ q q' (not_lt.mp hlt) (not_lt.mp hlt') h

end Work.Cusp
