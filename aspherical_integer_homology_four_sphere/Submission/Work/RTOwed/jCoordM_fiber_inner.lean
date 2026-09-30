import Mathlib
import Submission.Work.RTOwed.jLat

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOWed

open scoped Real RealInnerProductSpace

/-! ## Small helpers -/

/-- The second component of `cuspInvInner` is the recovered torus coordinate `invY`. -/
private theorem cuspInvInner_snd (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    (Work.Cusp.cuspInvInner v q).2 = Work.Cusp.invY v !₂[q 2, q 3] := rfl

/-- Linearity of `cuspY`. -/
private theorem cuspY_sub' (v : Work.Space.Cusp) (y y' : Work.Cusp.E2) :
    Work.Cusp.cuspY v (y - y') = Work.Cusp.cuspY v y - Work.Cusp.cuspY v y' := by
  ext i
  fin_cases i <;>
    simp only [Work.Cusp.cuspY, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    ring

/-- `uqOf` inverts the angle coordinate. -/
private theorem two_pi_mul_uqOf (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    2 * π * Work.Cusp.uqOf v q = q 1 - 2 * π * inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3])) (Work.Cusp.slope v) / ‖Work.Cusp.slope v‖ ^ 2 := by
  rw [Work.Cusp.uqOf]
  exact mul_div_cancel₀ _ (by positivity : (2 * π : ℝ) ≠ 0)

/-- The angle coordinate in terms of `uqOf`. -/
private theorem uqOf_angle (v : Work.Space.Cusp) (q : Work.Cusp.E4) :
    q 1 = 2 * π * Work.Cusp.uqOf v q + 2 * π * inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3])) (Work.Cusp.slope v) / ‖Work.Cusp.slope v‖ ^ 2 := by
  have h := two_pi_mul_uqOf v q
  linarith

/-! ## The inner fiber lemma -/

theorem jCoordM_fiber_inner (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P Q : Work.RTOwed.JPin a v) {q r : Work.Cusp.E4}
    (hq : q ∈ Work.RTOwed.jBox v P.cU P.k P.W P.kx P.δ)
    (hr : r ∈ Work.RTOwed.jBox v Q.cU Q.k Q.W Q.kx Q.δ)
    (hq0 : q 0 ≤ Work.Cusp.rJ) (hr0 : r 0 ≤ Work.Cusp.rJ)
    (h : Work.RTOwed.jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq⟩
      = Work.RTOwed.jCoordM a v (D v) Q.cU Q.k Q.W Q.kx Q.δ ⟨r, hr⟩) :
    ∃ (n : ℤ) (m : Fin 2 → ℤ), r = q + Work.RTOwed.jlVec v n m := by
  -- both points lie on the inner branch: unfold the coordinate inclusion there
  unfold Work.RTOwed.jCoordM at h
  rw [dite_eq_left hq0, dite_eq_left hr0] at h
  have hpair := a.incW_injective v h
  -- the filling points agree
  have hP : (Work.Cusp.cuspInvInner v q).1 = (Work.Cusp.cuspInvInner v r).1 := by
    have hc := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : Work.Cusp.E2)) hpair
    simpa using hc
  -- ... and so do the torus classes
  have hyc : (fun i => (((Work.Cusp.cuspInvInner v q).2 i : ℝ) : AddCircle (1 : ℝ)))
      = (fun i => (((Work.Cusp.cuspInvInner v r).2 i : ℝ) : AddCircle (1 : ℝ))) := by
    have hc := congrArg (fun z : Work.Space.SquarePt × a.Torus v => z.2) hpair
    exact Homeomorph.injective (D v).tor.symm hc
  have hqpos : 0 < q 0 := by have := hq.1; linarith
  have hrpos : 0 < r 0 := by have := hr.1; linarith
  have hrJpos : (0 : ℝ) < 2 * Work.Cusp.rJ := by norm_num [Work.Cusp.rJ]
  have hcIq : (Work.Cusp.cuspInvInner v q).1
      = (q 0 / (2 * Work.Cusp.rJ)) • Work.Cusp.bndOfU (Work.Cusp.uqOf v q) := by
    simpa using congrArg Prod.fst (Work.RTOwed.cuspInvInner_le v hq0)
  have hcIr : (Work.Cusp.cuspInvInner v r).1
      = (r 0 / (2 * Work.Cusp.rJ)) • Work.Cusp.bndOfU (Work.Cusp.uqOf v r) := by
    simpa using congrArg Prod.fst (Work.RTOwed.cuspInvInner_le v hr0)
  -- the layer parameters agree, hence `q 0 = r 0`
  have hscal : q 0 / (2 * Work.Cusp.rJ) = r 0 / (2 * Work.Cusp.rJ) := by
    have h2 := congrArg Work.Cusp.nrm hP
    rw [hcIq, hcIr] at h2
    simp only [Work.Cusp.nrm_smul, Work.Cusp.nrm_bndOfU, mul_one,
      abs_of_pos (div_pos hqpos hrJpos), abs_of_pos (div_pos hrpos hrJpos)] at h2
    exact h2
  have hqr : q 0 = r 0 := (div_left_inj' (ne_of_gt hrJpos)).mp hscal
  -- the perimeter coordinates agree modulo `ℤ`
  have hsq : (0 : ℝ) < q 0 / (2 * Work.Cusp.rJ) := div_pos hqpos hrJpos
  have hbnd : Work.Cusp.bndOfU (Work.Cusp.uqOf v q)
      = Work.Cusp.bndOfU (Work.Cusp.uqOf v r) := by
    have h2 : (q 0 / (2 * Work.Cusp.rJ)) • Work.Cusp.bndOfU (Work.Cusp.uqOf v q)
        = (q 0 / (2 * Work.Cusp.rJ)) • Work.Cusp.bndOfU (Work.Cusp.uqOf v r) := by
      rw [← hcIq, hP, hcIr, ← hscal]
    have h3 := congrArg (fun p : Work.Cusp.E2 => (q 0 / (2 * Work.Cusp.rJ))⁻¹ • p) h2
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hsq), one_smul] using h3
  have hfr : Int.fract (Work.Cusp.uqOf v q) = Int.fract (Work.Cusp.uqOf v r) := by
    have h2 := congrArg Work.Cusp.u hbnd
    rwa [Work.Cusp.u_bndOfU, Work.Cusp.u_bndOfU] at h2
  have hnu : Work.Cusp.uqOf v r - Work.Cusp.uqOf v q
      = ((⌊Work.Cusp.uqOf v r⌋ - ⌊Work.Cusp.uqOf v q⌋ : ℤ) : ℝ) := by
    have h1 : (⌊Work.Cusp.uqOf v r⌋ : ℝ) + Int.fract (Work.Cusp.uqOf v r)
        = Work.Cusp.uqOf v r := Int.floor_add_fract _
    have h2 : (⌊Work.Cusp.uqOf v q⌋ : ℝ) + Int.fract (Work.Cusp.uqOf v q)
        = Work.Cusp.uqOf v q := Int.floor_add_fract _
    rw [← hfr] at h1
    push_cast
    linarith
  -- the torus coordinates differ by an integer vector
  have hm : ∀ i : Fin 2, ∃ kk : ℤ,
      (Work.Cusp.invY v !₂[r 2, r 3]) i - (Work.Cusp.invY v !₂[q 2, q 3]) i = (kk : ℝ) := by
    intro i
    have hthis := (Work.RTOwed.addCircle_coe_eq_iff _ _).mp (congrFun hyc i).symm
    rwa [cuspInvInner_snd, cuspInvInner_snd] at hthis
  choose k hk using hm
  refine ⟨⌊Work.Cusp.uqOf v r⌋ - ⌊Work.Cusp.uqOf v q⌋, k, ?_⟩
  set n : ℤ := ⌊Work.Cusp.uqOf v r⌋ - ⌊Work.Cusp.uqOf v q⌋ with hn
  have hnu' : Work.Cusp.uqOf v r - Work.Cusp.uqOf v q = (n : ℝ) := by
    rw [hn]; exact hnu
  have hnu'' : Work.Cusp.uqOf v r = Work.Cusp.uqOf v q + (n : ℝ) := by linarith
  have hyrk : Work.Cusp.invY v !₂[r 2, r 3] - Work.Cusp.invY v !₂[q 2, q 3]
      = Work.RTOwed.jLreal k := by
    ext i
    fin_cases i
    · simp only [PiLp.sub_apply, Work.RTOwed.jLreal_apply]
      have hk' := hk 0
      push_cast at hk' ⊢
      linarith
    · simp only [PiLp.sub_apply, Work.RTOwed.jLreal_apply]
      have hk' := hk 1
      push_cast at hk' ⊢
      linarith
  have hq1 : q 1 = 2 * π * Work.Cusp.uqOf v q + 2 * π * inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3])) (Work.Cusp.slope v) / ‖Work.Cusp.slope v‖ ^ 2 := uqOf_angle v q
  have hr1 : r 1 = 2 * π * Work.Cusp.uqOf v r + 2 * π * inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[r 2, r 3])) (Work.Cusp.slope v) / ‖Work.Cusp.slope v‖ ^ 2 := uqOf_angle v r
  have hinner : inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[r 2, r 3])) (Work.Cusp.slope v) - inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3])) (Work.Cusp.slope v) = inner ℝ (Work.Cusp.cuspY v (Work.RTOwed.jLreal k)) (Work.Cusp.slope v) := by
    rw [← hyrk, cuspY_sub', inner_sub_left]
  have hinner' : inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[r 2, r 3])) (Work.Cusp.slope v) = inner ℝ (Work.Cusp.cuspY v (Work.Cusp.invY v !₂[q 2, q 3])) (Work.Cusp.slope v) + inner ℝ (Work.Cusp.cuspY v (Work.RTOwed.jLreal k)) (Work.Cusp.slope v) := by
    linarith [hinner]
  have hq2 : q 2 = Work.Cusp.wOf v (Work.Cusp.invY v !₂[q 2, q 3]) 0 := by
    rw [Work.Cusp.wOf_invY]; simp
  have hr2 : r 2 = Work.Cusp.wOf v (Work.Cusp.invY v !₂[r 2, r 3]) 0 := by
    rw [Work.Cusp.wOf_invY]; simp
  have hq3 : q 3 = Work.Cusp.wOf v (Work.Cusp.invY v !₂[q 2, q 3]) 1 := by
    rw [Work.Cusp.wOf_invY]; simp
  have hr3 : r 3 = Work.Cusp.wOf v (Work.Cusp.invY v !₂[r 2, r 3]) 1 := by
    rw [Work.Cusp.wOf_invY]; simp
  have hwsub : Work.Cusp.wOf v (Work.RTOwed.jLreal k)
      = Work.Cusp.wOf v (Work.Cusp.invY v !₂[r 2, r 3])
        - Work.Cusp.wOf v (Work.Cusp.invY v !₂[q 2, q 3]) := by
    rw [← hyrk, Work.RTOwed.wOf_sub]
  have h0 : r 0 = (q + Work.RTOwed.jlVec v n k) 0 := by
    rw [PiLp.add_apply, Work.RTOwed.jlVec_apply_zero, add_zero]
    exact hqr.symm
  have h1 : r 1 = (q + Work.RTOwed.jlVec v n k) 1 := by
    rw [PiLp.add_apply, Work.RTOwed.jlVec_apply_one, hq1, hr1]
    rw [hnu'', hinner']
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
