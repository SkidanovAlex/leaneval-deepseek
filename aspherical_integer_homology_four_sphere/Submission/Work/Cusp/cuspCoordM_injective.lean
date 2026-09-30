import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.cuspX_outerU_outerY
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.outerY_cuspX
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.bndOfU_u
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.beta_le_max
import Submission.Work.Cusp.betaMax_lt_sJ
import Submission.Work.Cusp.cuspCoordM_continuous
import Submission.Work.Cusp.ThetaOuter_cuspInvOuter
import Submission.Work.Cusp.ThetaOuter_injOn
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.Cusp

/-!
# Injectivity of the collar coordinate `cuspCoordM` on the assembled space `M̂`

`cuspCoordM a v D c δ` sends a point `q = (x,s)` of the *open* chart box `cuspChartBox v c δ` to
`M̂`: below the ceiling `s < β x` to the point of the hyperbolic piece with UHS coordinates `q`
(the branch `incMbar ∘ mbarLow`), at or above it to the filling boundary point recovered by the
outer chart (the branch `incW ∘ cuspInvOuter`).  The two branches agree on the ceiling
(`incMbar_mbarLow_eq`), where the gluing `CuspGlueData.glue_eq` identifies the truncation torus with
the boundary of the filling piece.

This file shows that the two branches do not meet anywhere else, and that each is injective, so
that the whole map is injective on the open box.

* **Both points below the ceiling.**  Both are taken by the lower branch and `incMbar` is
  injective, so `mbarLow q = mbarLow q'`; the chart datum `CuspGlueData.mbarLow_inj` then gives
  `q = q'`.

* **Both points on or above the ceiling.**  Both are taken by the upper branch and `incW` is
  injective, so the recovered layer points `(t_i • bndOfU u_i, y_i)` agree up to the period of the
  torus: `nrm (cuspInvOuter v q).1 = nrm (cuspInvOuter v q').1` and
  `(cuspInvOuter v q).2 ≡ (cuspInvOuter v q').2` modulo `ℤ²`.  Writing `y' = y + m` with `m ∈ ℤ²`
  and using the round trip `ThetaOuter_cuspInvOuter`, the difference of the cusp coordinates
  `xOf q' - xOf q` is the lattice vector `m₀ λ₂ + m₁ λ₃`, whose three coordinates are **integers**;
  but the two points lie in the box of side `2δ ≤ 1`, so every coordinate difference has absolute
  value `< 1`.  Hence the difference is `0`, and `cuspX_injOn` gives `y' = y`, i.e. `q = q'`.

* **One point below and one on or above the ceiling.**  If `incMbar x = incW v p` then `x` lies on
  the truncation torus and `p` on the boundary of the filling piece (`incMbar_eq_incW_imp`); the
  upper point is therefore recovered with layer parameter `1`, i.e. it lies *on* the ceiling
  (`cuspInvOuter_nrm_eq_one_ceiling`), and the previous case applies to both points.
-/

/-! ### Auxiliary computations -/

/-- **A point of `AddCircle 1` determines its lift up to an integer**: `(A : AddCircle 1)` and
`(B : AddCircle 1)` agree iff `A = B + m` for some `m : ℤ`. -/
theorem addCircle_one_coe_eq_iff (A B : ℝ) :
    ((A : AddCircle (1:ℝ)) = (B : AddCircle (1:ℝ))) ↔ ∃ m : ℤ, A = B + (m : ℝ) := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub (1:ℝ), AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hm' : (m:ℝ) = A - B := by simpa using hm
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hm' : A - B = (m:ℝ) := by linarith
    simpa using hm'.symm

/-- **A point of the hyperbolic piece equals a point of a filling piece only through the
gluing.**  If `incMbar x = incW v p` then `x` lies on the truncation torus `Tset` and `p` is its
image under the gluing homeomorphism. -/
theorem incMbar_eq_incW_imp (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    {x : a.Mbar} {p : Work.Space.SquarePt × a.Torus v}
    (h : a.incMbar x = a.incW v p) :
    ∃ (hx : x ∈ a.Tset),
      ((a.glue ⟨x, hx⟩ : {q : a.Y // q ∈ a.boundarySet}) : a.Y) = ⟨v, p⟩ := by
  have hrel : a.glueData.Rel (Sum.inl x) (Sum.inr ⟨v, p⟩) := Quotient.exact h
  rcases (Work.QuotientT2.GlueData.rel_iff a.glueData _ _).mp hrel with
    ⟨x', h1, h2⟩ | ⟨y', h1, h2⟩ | h3
  · obtain rfl : x = x' := Sum.inl.inj h1
    have h2' : (⟨v, p⟩ : a.Y) = ((a.glue x' : {q : a.Y // q ∈ a.boundarySet}) : a.Y) :=
      Sum.inr.inj h2
    exact ⟨x'.2, h2'.symm⟩
  · exact absurd h1 (by simp)
  · exact absurd h3 (by simp)

/-- The second cusp lattice vector `λ₂ = κ_{v,2}` has integer coordinates. -/
theorem lam2_apply (v : Fin 5) (i : Fin 3) : lam2 v i = ((kappa v 1 i : ℤ) : ℝ) := by
  fin_cases i <;> simp [lam2, kv]

/-- The third cusp lattice vector `λ₃ = κ_{v,3}` has integer coordinates. -/
theorem lam3_apply (v : Fin 5) (i : Fin 3) : lam3 v i = ((kappa v 2 i : ℤ) : ℝ) := by
  fin_cases i <;> simp [lam3, kv]

/-- The horizontal part of `ThetaOuter v p y` is the cusp coordinate `cuspX v (u p) y`. -/
theorem xOf_ThetaOuter (v : Fin 5) (p y : E2) : xOf (ThetaOuter v p y) = cuspX v (u p) y := by
  ext i
  rw [show xOf (ThetaOuter v p y) i = (ThetaOuter v p y) (Fin.castSucc i) from by
    fin_cases i <;> simp [xOf]]
  exact ThetaOuter_apply_cuspX v p y i

/-- The sup norm of the recovered layer point of `cuspInvOuter v q` is the absolute value of the
recovered layer parameter `t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`. -/
theorem cuspInvOuter_nrm_fst (v : Fin 5) (q : E4) :
    nrm (cuspInvOuter v q).1
      = |1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log (beta (xOf q)) - Real.log sJ))| := by
  have hpe : (cuspInvOuter v q).1
      = (1 + (Real.log (q 3) - Real.log (beta (xOf q))) /
          (2 * (Real.log (beta (xOf q)) - Real.log sJ))) • bndOfU (outerU v (xOf q)) := rfl
  rw [hpe, nrm_smul, nrm_bndOfU, mul_one]

/-- **A point of the cusp box whose recovered layer parameter has sup norm `1` lies on the
ceiling.**  The recovered parameter is
`t = 1 + (log s − log β(x)) / (2 (log β(x) − log s_J))`; `|t| = 1` together with the box conditions
`s < s_J`, `0 < β(x) < s_J` forces `s = β(x)`. -/
theorem cuspInvOuter_nrm_eq_one_ceiling (v : Fin 5) (c : E3) (δ : ℝ) (q : E4)
    (hbox : q ∈ cuspBox v c δ)
    (h1 : nrm (cuspInvOuter v q).1 = 1) : q 3 = beta (xOf q) := by
  obtain ⟨-, hs1, hsJ, -, -⟩ := hbox
  set b : ℝ := beta (xOf q) with hb
  set e : ℝ := 1 + (Real.log (q 3) - Real.log b) / (2 * (Real.log b - Real.log sJ)) with he
  have hbpos : 0 < b := by rw [hb]; exact beta_pos _
  have hblt : b < sJ := lt_of_le_of_lt (beta_le_max _) betaMax_lt_sJ
  have hq3pos : 0 < q 3 := lt_trans (by norm_num [s1]) hs1
  have habs : |e| = 1 := by
    have hh := cuspInvOuter_nrm_fst v q
    rw [h1, ← hb, ← he] at hh
    exact hh.symm
  have hloglt : Real.log (q 3) < Real.log sJ := Real.log_lt_log hq3pos hsJ
  have hlogb : Real.log b < Real.log sJ := Real.log_lt_log hbpos hblt
  have hden : (2 * (Real.log b - Real.log sJ)) ≠ 0 := by
    intro hc; linarith
  have key : Real.log (q 3) = Real.log b := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp habs with h | h
    · have hr : (Real.log (q 3) - Real.log b) / (2 * (Real.log b - Real.log sJ)) = 0 := by
        rw [he] at h; linarith
      rw [div_eq_iff hden] at hr
      linarith
    · have hr : (Real.log (q 3) - Real.log b) / (2 * (Real.log b - Real.log sJ)) = -2 := by
        rw [he] at h; linarith
      rw [div_eq_iff hden] at hr
      linarith
  calc q 3 = Real.exp (Real.log (q 3)) := (Real.exp_log hq3pos).symm
    _ = Real.exp (Real.log b) := by rw [key]
    _ = b := Real.exp_log hbpos
    _ = beta (xOf q) := hb.symm

/-! ### The two halves of the injectivity -/

/-- **The mixed case.**  If `q` lies strictly below the ceiling and `q'` on or above it, and the two
have the same image in `M̂`, then `q = q'` (in fact equality forces `q'` to lie *on* the ceiling, so
that both lie in the region where `mbarLow` is injective). -/
theorem cuspCoordM_mixed (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q q' : {q : E4 // q ∈ cuspChartBox v c δ})
    (hlt : q.1 3 < beta (xOf q.1)) (hge' : beta (xOf q'.1) ≤ q'.1 3)
    (h : cuspCoordM a v D c δ q = cuspCoordM a v D c δ q') : q = q' := by
  have hlow := cuspCoordM_eq_le a v D c δ q (le_of_lt hlt)
  have hhigh := cuspCoordM_eq_ge a v D c δ q' hge'
  have hmix : a.incMbar (D.mbarLow q.1) =
      cuspCoordMUp a v D c δ ⟨q'.1, ⟨cuspChartBox_subset_cuspBox v c δ q'.2, hge'⟩⟩ :=
    hlow.symm.trans (h.trans hhigh)
  simp only [cuspCoordMUp] at hmix
  obtain ⟨hx, hglue⟩ := incMbar_eq_incW_imp a v hmix
  have hnrm1 : nrm (cuspInvOuter v q'.1).1 = 1 := by
    have hbdry := (a.glue ⟨D.mbarLow q.1, hx⟩).2
    rw [hglue] at hbdry
    simpa only [Work.Space.Assembly.boundarySet, Work.Space.FillingBdry, Set.mem_ofPred_eq,
      Work.Space.sqNorm, Work.Space.nrm, nrm] using hbdry
  have hceil' : q'.1 3 = beta (xOf q'.1) :=
    cuspInvOuter_nrm_eq_one_ceiling v c δ q'.1 (cuspChartBox_subset_cuspBox v c δ q'.2) hnrm1
  have h' : a.incMbar (D.mbarLow q.1) = a.incMbar (D.mbarLow q'.1) := by
    rw [cuspCoordM_eq_le a v D c δ q (le_of_lt hlt),
        cuspCoordM_eq_le a v D c δ q' (le_of_eq hceil')] at h
    exact h
  exact Subtype.ext (D.mbarLow_inj c δ hδ ⟨q.2, le_of_lt hlt⟩ ⟨q'.2, le_of_eq hceil'⟩
    (a.incMbar_injective h'))

/-- **Both points on or above the ceiling.**  The recovered layer points agree, hence the cusp
coordinates differ by a lattice vector with integer coordinates; the box has side `2δ ≤ 1`, so the
difference vanishes and `q = q'`. -/
theorem cuspCoordM_high (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (q q' : {q : E4 // q ∈ cuspChartBox v c δ})
    (hge : beta (xOf q.1) ≤ q.1 3) (hge' : beta (xOf q'.1) ≤ q'.1 3)
    (h : cuspCoordM a v D c δ q = cuspCoordM a v D c δ q') : q = q' := by
  have hboxq : ∀ i, |xOf q.1 i - c i| < δ := q.2.1
  have hboxq' : ∀ i, |xOf q'.1 i - c i| < δ := q'.2.1
  have hhigh := cuspCoordM_eq_ge a v D c δ q hge
  have hhigh' := cuspCoordM_eq_ge a v D c δ q' hge'
  have hup : cuspCoordMUp a v D c δ ⟨q.1, ⟨cuspChartBox_subset_cuspBox v c δ q.2, hge⟩⟩ =
      cuspCoordMUp a v D c δ ⟨q'.1, ⟨cuspChartBox_subset_cuspBox v c δ q'.2, hge'⟩⟩ :=
    hhigh.symm.trans (h.trans hhigh')
  simp only [cuspCoordMUp] at hup
  have hpair := a.incW_injective v hup
  -- the recovered layer points agree up to the period of the torus
  have hfst : (cuspInvOuter v q.1).1 = (cuspInvOuter v q'.1).1 := by
    have := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : E2)) hpair
    simpa using this
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
  -- write both points as points of the outer chart
  have hsrcq : q.1 ∈ cuspSource v c δ := ⟨cuspChartBox_subset_cuspBox v c δ q.2, hge⟩
  have hsrcq' : q'.1 ∈ cuspSource v c δ := ⟨cuspChartBox_subset_cuspBox v c δ q'.2, hge'⟩
  have hqT : q.1 = ThetaOuter v (cuspInvOuter v q.1).1 (cuspInvOuter v q.1).2 :=
    (ThetaOuter_cuspInvOuter v c δ q.1 hsrcq).symm
  have hqT' : q'.1 = ThetaOuter v (cuspInvOuter v q'.1).1 (cuspInvOuter v q'.1).2 :=
    (ThetaOuter_cuspInvOuter v c δ q'.1 hsrcq').symm
  have hX1 : xOf q.1 = cuspX v (u (cuspInvOuter v q.1).1) (cuspInvOuter v q.1).2 :=
    (congrArg xOf hqT).trans (xOf_ThetaOuter v _ _)
  have hX2 : xOf q'.1 = cuspX v (u (cuspInvOuter v q'.1).1) (cuspInvOuter v q'.1).2 :=
    (congrArg xOf hqT').trans (xOf_ThetaOuter v _ _)
  -- the cusp coordinates differ by an integer vector, but are close
  have hxi : ∀ i : Fin 3, xOf q'.1 i = xOf q.1 i := by
    intro i
    have hdiff : xOf q'.1 i - xOf q.1 i
        = (m 0 : ℝ) * lam2 v i + (m 1 : ℝ) * lam3 v i := by
      have g1 := congrArg (fun z : E3 => z i) hX1
      have g2 := congrArg (fun z : E3 => z i) hX2
      rw [g2, g1, hfst]
      simp only [cuspX, cuspY, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [hm 0, hm 1]
      ring
    have hzi : xOf q'.1 i - xOf q.1 i
        = ((m 0 * kappa v 1 i + m 1 * kappa v 2 i : ℤ) : ℝ) := by
      rw [hdiff, lam2_apply, lam3_apply]
      push_cast
      ring
    have hbnd : |xOf q'.1 i - xOf q.1 i| < 1 := by
      have h1 := hboxq' i
      have h2 := hboxq i
      calc |xOf q'.1 i - xOf q.1 i|
          = |(xOf q'.1 i - c i) - (xOf q.1 i - c i)| := by congr 1; ring
        _ ≤ |xOf q'.1 i - c i| + |xOf q.1 i - c i| := abs_sub _ _
        _ < δ + δ := by linarith
        _ ≤ 1 := by linarith
    have hz : (m 0 * kappa v 1 i + m 1 * kappa v 2 i : ℤ) = 0 := by
      have hh := hbnd
      rw [hzi] at hh
      have hlt1 : ((m 0 * kappa v 1 i + m 1 * kappa v 2 i : ℤ) : ℝ) < 1 := (abs_lt.mp hh).2
      have hgt1 : (-1:ℝ) < ((m 0 * kappa v 1 i + m 1 * kappa v 2 i : ℤ) : ℝ) := (abs_lt.mp hh).1
      have ha : (m 0 * kappa v 1 i + m 1 * kappa v 2 i : ℤ) < 1 := by exact_mod_cast hlt1
      have hb : (-1:ℤ) < (m 0 * kappa v 1 i + m 1 * kappa v 2 i : ℤ) := by exact_mod_cast hgt1
      omega
    have hzz : xOf q'.1 i - xOf q.1 i = 0 := by rw [hzi, hz]; norm_num
    linarith
  have hxeq : xOf q'.1 = xOf q.1 := by ext i; exact hxi i
  -- so the torus coordinates agree and the points coincide
  have hg : (cuspInvOuter v q'.1).2 = (cuspInvOuter v q.1).2 := by
    have hX : cuspX v (u (cuspInvOuter v q.1).1) (cuspInvOuter v q'.1).2
        = cuspX v (u (cuspInvOuter v q.1).1) (cuspInvOuter v q.1).2 := by
      calc cuspX v (u (cuspInvOuter v q.1).1) (cuspInvOuter v q'.1).2
          = cuspX v (u (cuspInvOuter v q'.1).1) (cuspInvOuter v q'.1).2 := by rw [hfst]
        _ = xOf q'.1 := hX2.symm
        _ = xOf q.1 := hxeq
        _ = cuspX v (u (cuspInvOuter v q.1).1) (cuspInvOuter v q.1).2 := hX1
    have hXp : (u (cuspInvOuter v q.1).1, (cuspInvOuter v q'.1).2)
        = (u (cuspInvOuter v q.1).1, (cuspInvOuter v q.1).2) := by
      apply cuspX_injOn v (Set.mem_univ _) (Set.mem_univ _)
      exact hX
    exact congrArg (fun z : ℝ × E2 => z.2) hXp
  refine Subtype.ext ?_
  calc q.1 = ThetaOuter v (cuspInvOuter v q.1).1 (cuspInvOuter v q.1).2 := hqT
    _ = ThetaOuter v (cuspInvOuter v q'.1).1 (cuspInvOuter v q'.1).2 := by rw [hg, hfst]
    _ = q'.1 := hqT'.symm

/-! ### The theorem -/

theorem cuspCoordM_injective (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : CuspGlueData a v) (c : E3) (δ : ℝ) (hδ : δ ≤ 1/2) :
    Function.Injective (cuspCoordM a v D c δ) := by
  intro q q' h
  by_cases hlt : q.1 3 < beta (xOf q.1)
  · by_cases hlt' : q'.1 3 < beta (xOf q'.1)
    · have h' : a.incMbar (D.mbarLow q.1) = a.incMbar (D.mbarLow q'.1) := by
        rw [cuspCoordM_eq_le a v D c δ q (le_of_lt hlt),
            cuspCoordM_eq_le a v D c δ q' (le_of_lt hlt')] at h
        exact h
      exact Subtype.ext (D.mbarLow_inj c δ hδ ⟨q.2, le_of_lt hlt⟩ ⟨q'.2, le_of_lt hlt'⟩
        (a.incMbar_injective h'))
    · exact cuspCoordM_mixed a v D c δ hδ q q' hlt (not_lt.mp hlt') h
  · by_cases hlt' : q'.1 3 < beta (xOf q'.1)
    · exact (cuspCoordM_mixed a v D c δ hδ q' q hlt' (not_lt.mp hlt) h.symm).symm
    · exact cuspCoordM_high a v D c δ hδ q q' (not_lt.mp hlt) (not_lt.mp hlt') h

end Work.Cusp
