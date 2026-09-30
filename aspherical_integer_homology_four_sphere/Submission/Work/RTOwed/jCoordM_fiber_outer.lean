import Mathlib
import Submission.Work.RTOwed.jLat
import Submission.Work.RTOwed.jCoordM_isOpenMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped Real RealInnerProductSpace

namespace Work.RTOWed

/-! ## The collar branch of the inner inverse `cuspInvInner`

On the collar branch `r_J < q 0` the inverse of the polar chart recovers the layer parameter
`t = 1 + (R₀ − q 0 − log β(x))/(2 (log β(x) − log s_J))`, the boundary direction
`bndOfU (uqOf v q)` and the torus coordinates `invY v (q 2, q 3)`.  We record this branch and the
positivity of its layer parameter, which is what makes the two sides of the fibre computation
cancel. -/

/-- The ceiling `β (cuspX v (uqOf v q) (invY v (q 2, q 3)))` of the cusp coordinate in which the
collar branch of `cuspInvInner` lands. -/
def jCeil (v : Work.Space.Cusp) (q : Work.Cusp.E4) : ℝ :=
  Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.uqOf v q) (Work.Cusp.invY v !₂[q 2, q 3]))

/-- The layer parameter recovered by the collar branch of `cuspInvInner`. -/
def jInT (v : Work.Space.Cusp) (q : Work.Cusp.E4) : ℝ :=
  1 + (Work.Cusp.R0 - q 0 - Real.log (jCeil v q))
    / (2 * (Real.log (jCeil v q) - Real.log Work.Cusp.sJ))

/-- **The collar branch of `cuspInvInner`.**  For `r_J < q 0` the inverse of the polar chart is the
layer parameter `jInT v q` times the boundary direction `bndOfU (uqOf v q)`, together with the
recovered torus coordinates `invY v (q 2, q 3)`. -/
theorem cuspInvInner_collar (v : Work.Space.Cusp) (q : Work.Cusp.E4)
    (h : Work.Cusp.rJ < q 0) :
    Work.Cusp.cuspInvInner v q
      = (jInT v q • Work.Cusp.bndOfU (Work.Cusp.uqOf v q),
         Work.Cusp.invY v !₂[q 2, q 3]) := by
  simp only [Work.Cusp.cuspInvInner, jInT, jCeil]
  rw [ite_eq_right (not_le.mpr h)]
  simp only [Work.Cusp.uqOf, mul_div_assoc]

/-- **The collar layer parameter is positive**: `jInT v q > 1/2` for `r_J < q 0`. -/
theorem jInT_pos (v : Work.Space.Cusp) (q : Work.Cusp.E4) (h : Work.Cusp.rJ < q 0) :
    0 < jInT v q := by
  have hlog : Real.log (jCeil v q) < Real.log Work.Cusp.sJ :=
    Real.log_lt_log (by rw [jCeil]; exact Work.Cusp.beta_pos _)
      (by rw [jCeil]; exact Work.Cusp.beta_lt_sJ _)
  have h2 := Work.Cusp.cuspInvRate_gt_half hlog h
  rw [jInT]
  linarith

/-- The angle coordinate in terms of `uqOf` (inverting the definition of `uqOf`). -/
theorem uqOf_angleR (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    q 1 = 2 * π * Work.Cusp.uqOf v q
      + 2 * π * inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3]))
          (Work.Cusp.slope v) / ‖Work.Cusp.slope v‖ ^ 2 := by
  rw [Work.Cusp.uqOf]
  have h : (2 * (π : ℝ)) ≠ 0 := by positivity
  field_simp
  ring

/-! ## The lattice step

The two cusp coordinates `cuspX v (uqOf v q) (invY v (q 2, q 3))` of two polar coordinates whose
recovered torus coordinates differ by an *integer* vector (`jLreal k`) and whose recovered perimeter
coordinates differ by an integer `n` differ by a vector of the cusp lattice `Λ_v`: the displacement
is `n • σ_v + k 0 • λ₂ + k 1 • λ₃` and `Λ_v = ⟨σ_v, λ₂, λ₃⟩`. -/

theorem slope_mem_lattice (v : Work.Space.Cusp) :
    Work.Cusp.slope v ∈ Work.Cusp.lattice v := by
  rw [Work.Cusp.slope_eq_kv v]
  exact add_mem
    (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (0 : Fin 3))) 1)
    (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (1 : Fin 3)))
      (Work.Cusp.slopeB v))

theorem cuspX_diff_mem_lattice (v : Work.Space.Cusp) {q r : Work.Cusp.E4} (n : ℤ)
    (k : Fin 2 → ℤ)
    (hu : Work.Cusp.uqOf v r - Work.Cusp.uqOf v q = (n : ℝ))
    (hy : Work.Cusp.invY v !₂[r 2, r 3] - Work.Cusp.invY v !₂[q 2, q 3]
      = Work.RTOwed.jLreal k) :
    Work.Cusp.cuspX v (Work.Cusp.uqOf v r) (Work.Cusp.invY v !₂[r 2, r 3])
      - Work.Cusp.cuspX v (Work.Cusp.uqOf v q) (Work.Cusp.invY v !₂[q 2, q 3])
      ∈ Work.Cusp.lattice v := by
  have hslope := slope_mem_lattice v
  have hlam2 : Work.Cusp.lam2 v ∈ Work.Cusp.lattice v :=
    AddSubgroup.subset_closure (Set.mem_range_self (1 : Fin 3))
  have hlam3 : Work.Cusp.lam3 v ∈ Work.Cusp.lattice v :=
    AddSubgroup.subset_closure (Set.mem_range_self (2 : Fin 3))
  have hdiff : Work.Cusp.cuspX v (Work.Cusp.uqOf v r) (Work.Cusp.invY v !₂[r 2, r 3])
      - Work.Cusp.cuspX v (Work.Cusp.uqOf v q) (Work.Cusp.invY v !₂[q 2, q 3])
      = (n : ℝ) • Work.Cusp.slope v + (k 0 : ℝ) • Work.Cusp.lam2 v
        + (k 1 : ℝ) • Work.Cusp.lam3 v := by
    have hc : Work.Cusp.cuspX v (Work.Cusp.uqOf v r) (Work.Cusp.invY v !₂[r 2, r 3])
        - Work.Cusp.cuspX v (Work.Cusp.uqOf v q) (Work.Cusp.invY v !₂[q 2, q 3])
        = (Work.Cusp.uqOf v r - Work.Cusp.uqOf v q) • Work.Cusp.slope v
          + (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[r 2, r 3])
             - Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3])) := by
      rw [Work.Cusp.cuspX, Work.Cusp.cuspX]; module
    rw [hc, hu, ← Work.RTOwed.cuspY_sub v, hy, Work.Cusp.cuspY,
      Work.RTOwed.jLreal_apply, Work.RTOwed.jLreal_apply]
    abel
  rw [hdiff, Int.cast_smul_eq_zsmul ℝ, Int.cast_smul_eq_zsmul ℝ,
    Int.cast_smul_eq_zsmul ℝ]
  exact add_mem
    (add_mem (AddSubgroup.zsmul_mem _ hslope n) (AddSubgroup.zsmul_mem _ hlam2 (k 0)))
    (AddSubgroup.zsmul_mem _ hlam3 (k 1))

/-! ## The fibre of the junction coordinate inclusion on the collar

Both points have `r_J < q 0 < jTop`, so the junction coordinate inclusion is the pinning-independent
polar inclusion `incW v ∘ fillProj ∘ cuspInvInner` (`jCoordM_eq_jPolarInc`).  The fibre computation
is then a computation with the explicit collar branch of `cuspInvInner`. -/

theorem jCoordM_fiber_outer (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P Q : Work.RTOwed.JPin a v) {q r : Work.Cusp.E4}
    (hq : q ∈ Work.RTOwed.jBox v P.cU P.k P.W P.kx P.δ)
    (hr : r ∈ Work.RTOwed.jBox v Q.cU Q.k Q.W Q.kx Q.δ)
    (hq0 : Work.Cusp.rJ < q 0) (hr0 : Work.Cusp.rJ < r 0)
    (hqT : q 0 < Work.RTOWed.jTop) (hrT : r 0 < Work.RTOWed.jTop)
    (h : Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq⟩
      = Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨r, hr⟩) :
    ∃ (n : ℤ) (m : Fin 2 → ℤ), r = q + Work.RTOwed.jlVec v n m := by
  classical
  -- ### Step 1: below the top of the collar window `jCoordM` is the polar inclusion
  have h1 := Work.RTOWed.jCoordM_eq_jPolarInc a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq⟩ hqT
  have h2 := Work.RTOWed.jCoordM_eq_jPolarInc a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨r, hr⟩ hrT
  have hkey : Work.RTOWed.jPolarInc a v (D v) P.cU P.k P.W
        ⟨q, ⟨Work.RTOWed.jBox_subset_jTarget v P.cU P.k P.W P.kx P.δ hq, hqT⟩⟩
      = Work.RTOWed.jPolarInc a v (D v) Q.cU Q.k Q.W
        ⟨r, ⟨Work.RTOWed.jBox_subset_jTarget v Q.cU Q.k Q.W Q.kx Q.δ hr, hrT⟩⟩ := by
    rw [← h1, ← h2]
    exact h
  -- the two recovered points of the filling cover agree
  have hpl := a.incW_injective v hkey
  have hfst : (Work.Cusp.cuspInvInner v q).1 = (Work.Cusp.cuspInvInner v r).1 := by
    have hc := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : Work.Cusp.E2)) hpl
    simpa only [Work.RTOWed.jPolarInc, Work.Cusp.fillProj, Work.Cusp.sqPtOf] using hc
  have hsnd : (fun i => (((Work.Cusp.cuspInvInner v q).2 i : ℝ) : AddCircle (1 : ℝ)))
      = (fun i => (((Work.Cusp.cuspInvInner v r).2 i : ℝ) : AddCircle (1 : ℝ))) := by
    have hc := congrArg (fun z : Work.Space.SquarePt × a.Torus v => z.2) hpl
    simp only [Work.Cusp.fillProj] at hc
    exact (D v).tor.symm.injective hc
  -- ### Step 2: the collar branch of the inner inverse
  have hqI := cuspInvInner_collar v q hq0
  have hrI := cuspInvInner_collar v r hr0
  have hTq : 0 < jInT v q := jInT_pos v q hq0
  have hTr : 0 < jInT v r := jInT_pos v r hr0
  have hA : jInT v q • Work.Cusp.bndOfU (Work.Cusp.uqOf v q)
      = jInT v r • Work.Cusp.bndOfU (Work.Cusp.uqOf v r) := by
    rw [hqI, hrI] at hfst
    exact hfst
  -- the sup norms agree, so the layer parameters agree
  have hT : jInT v q = jInT v r := by
    have hh := congrArg Work.Cusp.nrm hA
    rw [Work.Cusp.nrm_smul, Work.Cusp.nrm_smul, Work.Cusp.nrm_bndOfU,
      Work.Cusp.nrm_bndOfU, mul_one, mul_one, abs_of_pos hTq, abs_of_pos hTr] at hh
    exact hh
  -- ... hence so do the boundary directions
  have hbnd : Work.Cusp.bndOfU (Work.Cusp.uqOf v q) = Work.Cusp.bndOfU (Work.Cusp.uqOf v r) := by
    have hh := hA
    rw [← hT] at hh
    have h2 := congrArg (fun z : Work.Cusp.E2 => (jInT v q)⁻¹ • z) hh
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hTq), one_smul] at h2
    exact h2
  -- ... and the recovered perimeter coordinates differ by an integer
  have hfr : Int.fract (Work.Cusp.uqOf v q) = Int.fract (Work.Cusp.uqOf v r) := by
    have hh := congrArg Work.Cusp.u hbnd
    rwa [Work.Cusp.u_bndOfU, Work.Cusp.u_bndOfU] at hh
  have hnu : Work.Cusp.uqOf v r - Work.Cusp.uqOf v q
      = ((⌊Work.Cusp.uqOf v r⌋ - ⌊Work.Cusp.uqOf v q⌋ : ℤ) : ℝ) := by
    have h1 : (⌊Work.Cusp.uqOf v r⌋ : ℝ) + Int.fract (Work.Cusp.uqOf v r)
        = Work.Cusp.uqOf v r := Int.floor_add_fract _
    have h2 : (⌊Work.Cusp.uqOf v q⌋ : ℝ) + Int.fract (Work.Cusp.uqOf v q)
        = Work.Cusp.uqOf v q := Int.floor_add_fract _
    rw [← hfr] at h1
    push_cast
    linarith
  -- the recovered torus coordinates differ by an integer vector
  rw [hqI, hrI] at hsnd
  have hm : ∀ i : Fin 2, ∃ kk : ℤ,
      (Work.Cusp.invY v !₂[r 2, r 3]) i - (Work.Cusp.invY v !₂[q 2, q 3]) i = (kk : ℝ) := by
    intro i
    have hthis := (Work.RTOwed.addCircle_coe_eq_iff _ _).mp (congrFun hsnd i).symm
    exact hthis
  choose k hk using hm
  refine ⟨⌊Work.Cusp.uqOf v r⌋ - ⌊Work.Cusp.uqOf v q⌋, k, ?_⟩
  set n : ℤ := ⌊Work.Cusp.uqOf v r⌋ - ⌊Work.Cusp.uqOf v q⌋ with hn
  have hnu' : Work.Cusp.uqOf v r - Work.Cusp.uqOf v q = (n : ℝ) := by
    rw [hn]; exact hnu
  have hyk : Work.Cusp.invY v !₂[r 2, r 3] - Work.Cusp.invY v !₂[q 2, q 3]
      = Work.RTOwed.jLreal k := by
    ext i
    simpa only [PiLp.sub_apply, Work.RTOwed.jLreal_apply] using hk i
  -- ### Step 3: the ceilings agree, hence so do the radial coordinates
  have hxr : jCeil v r = jCeil v q := by
    simp only [jCeil]
    have hmem := cuspX_diff_mem_lattice (q := q) (r := r) v n k hnu' hyk
    have hb := Work.Cusp.beta_lattice_periodic v
      (Work.Cusp.cuspX v (Work.Cusp.uqOf v q) (Work.Cusp.invY v !₂[q 2, q 3]))
      (Work.Cusp.cuspX v (Work.Cusp.uqOf v r) (Work.Cusp.invY v !₂[r 2, r 3])
        - Work.Cusp.cuspX v (Work.Cusp.uqOf v q) (Work.Cusp.invY v !₂[q 2, q 3])) hmem
    have hadd : Work.Cusp.cuspX v (Work.Cusp.uqOf v q) (Work.Cusp.invY v !₂[q 2, q 3])
        + (Work.Cusp.cuspX v (Work.Cusp.uqOf v r) (Work.Cusp.invY v !₂[r 2, r 3])
          - Work.Cusp.cuspX v (Work.Cusp.uqOf v q) (Work.Cusp.invY v !₂[q 2, q 3]))
        = Work.Cusp.cuspX v (Work.Cusp.uqOf v r) (Work.Cusp.invY v !₂[r 2, r 3]) := by abel
    rw [hadd] at hb
    exact hb
  have hqr : q 0 = r 0 := by
    have hh := hT
    simp only [jInT] at hh
    rw [hxr] at hh
    have hd : (2 : ℝ) * (Real.log (jCeil v q) - Real.log Work.Cusp.sJ) ≠ 0 := by
      have hlog : Real.log (jCeil v q) < Real.log Work.Cusp.sJ :=
        Real.log_lt_log (by rw [jCeil]; exact Work.Cusp.beta_pos _)
          (by rw [jCeil]; exact Work.Cusp.beta_lt_sJ _)
      linarith
    have h3 : (Work.Cusp.R0 - q 0 - Real.log (jCeil v q))
        = (Work.Cusp.R0 - r 0 - Real.log (jCeil v q)) := by
      have h2 : (Work.Cusp.R0 - q 0 - Real.log (jCeil v q))
            / (2 * (Real.log (jCeil v q) - Real.log Work.Cusp.sJ))
          = (Work.Cusp.R0 - r 0 - Real.log (jCeil v q))
            / (2 * (Real.log (jCeil v q) - Real.log Work.Cusp.sJ)) := by linarith
      have h4 := congrArg
        (fun t : ℝ => t * (2 * (Real.log (jCeil v q) - Real.log Work.Cusp.sJ))) h2
      rwa [div_mul_cancel₀ _ hd, div_mul_cancel₀ _ hd] at h4
    linarith
  -- ### Step 4: the four coordinates
  have hinner : inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[r 2, r 3]))
        (Work.Cusp.slope v)
      - inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3])) (Work.Cusp.slope v)
      = inner ℝ (Work.Cusp.cuspY v (Work.RTOwed.jLreal k)) (Work.Cusp.slope v) := by
    rw [← hyk, Work.RTOwed.cuspY_sub, inner_sub_left]
  have hwsub : Work.Cusp.wOf v (Work.RTOwed.jLreal k)
      = Work.Cusp.wOf v (Work.Cusp.invY v !₂[r 2, r 3])
        - Work.Cusp.wOf v (Work.Cusp.invY v !₂[q 2, q 3]) := by
    rw [← hyk, Work.RTOwed.wOf_sub]
  have hq2 : q 2 = Work.Cusp.wOf v (Work.Cusp.invY v !₂[q 2, q 3]) 0 := by
    rw [Work.Cusp.wOf_invY]; simp
  have hr2 : r 2 = Work.Cusp.wOf v (Work.Cusp.invY v !₂[r 2, r 3]) 0 := by
    rw [Work.Cusp.wOf_invY]; simp
  have hq3 : q 3 = Work.Cusp.wOf v (Work.Cusp.invY v !₂[q 2, q 3]) 1 := by
    rw [Work.Cusp.wOf_invY]; simp
  have hr3 : r 3 = Work.Cusp.wOf v (Work.Cusp.invY v !₂[r 2, r 3]) 1 := by
    rw [Work.Cusp.wOf_invY]; simp
  have h0 : r 0 = (q + Work.RTOwed.jlVec v n k) 0 := by
    rw [PiLp.add_apply, Work.RTOwed.jlVec_apply_zero, add_zero]
    exact hqr.symm
  have h1 : r 1 = (q + Work.RTOwed.jlVec v n k) 1 := by
    rw [PiLp.add_apply, Work.RTOwed.jlVec_apply_one, uqOf_angleR v q, uqOf_angleR v r]
    have hnu'' : Work.Cusp.uqOf v r = Work.Cusp.uqOf v q + (n : ℝ) := by linarith [hnu']
    rw [hnu'']
    have hinner' : inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[r 2, r 3]))
          (Work.Cusp.slope v)
        = inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3])) (Work.Cusp.slope v)
          + inner ℝ (Work.Cusp.cuspY v (Work.RTOwed.jLreal k)) (Work.Cusp.slope v) := by
      linarith [hinner]
    rw [hinner']
    ring
  have h2 : r 2 = (q + Work.RTOwed.jlVec v n k) 2 := by
    rw [PiLp.add_apply, Work.RTOwed.jlVec_apply_two, hq2, hr2, hwsub]
    simp only [PiLp.sub_apply]
    ring
  have h3 : r 3 = (q + Work.RTOwed.jlVec v n k) 3 := by
    rw [PiLp.add_apply, Work.RTOwed.jlVec_apply_three, hq3, hr3, hwsub]
    simp only [PiLp.sub_apply]
    ring
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

end Work.RTOWed
