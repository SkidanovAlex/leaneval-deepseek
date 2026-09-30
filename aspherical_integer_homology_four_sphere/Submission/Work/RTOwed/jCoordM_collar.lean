import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.cuspInvOuter_ThetaOuter_half
import Submission.Work.Cusp.polarToUHS_ThetaPolar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Function

/-- **The collar height never drops below the ceiling.**  For a layer parameter `t ≤ 1` and a
ceiling value `b` with `0 < b < s_J` one has `b ≤ collarHeight t b = β^{2t-1} s_J^{2-2t}`.  Writing
`E = (2t-1) log b + (2-2t) log s_J` for the exponent, the difference
`E - log b = (2-2t)(log s_J - log b)` is nonnegative because `2 - 2t ≥ 0` and `log b < log s_J`.
This is the comparison that decides that the collar branch of a junction chart lies *on or above*
the ceiling `β`, i.e. in the collar of the filling piece rather than in the chimney of `M̄`. -/
theorem collarHeight_ge_self {t b : ℝ} (ht : t ≤ 1) (hb : 0 < b) (hbs : b < Work.Cusp.sJ) :
    b ≤ Work.Cusp.collarHeight t b := by
  rw [Work.Cusp.collarHeight]
  have hlog : Real.log b ≤ (2 * t - 1) * Real.log b + (2 - 2 * t) * Real.log Work.Cusp.sJ := by
    have h2 : 0 ≤ 2 - 2 * t := by linarith
    have h3 : Real.log b ≤ Real.log Work.Cusp.sJ := le_of_lt (Real.log_lt_log hb hbs)
    have h4 : (2 - 2 * t) * Real.log b ≤ (2 - 2 * t) * Real.log Work.Cusp.sJ :=
      mul_le_mul_of_nonneg_left h3 h2
    nlinarith
  rw [← Real.log_le_iff_le_exp hb]
  exact hlog

theorem jCoordM_collar (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (p : Work.Space.SquarePt) (y : a.Torus v) (w : Work.Cusp.E2)
    (hw : ∀ i, ((w i : ℝ) : AddCircle (1 : ℝ)) = D.tor y i)
    (hp : (p : Work.Cusp.E2) ∈ Work.Cusp.Sq) (h1 : 1 / 2 ≤ Work.Cusp.nrm (p : Work.Cusp.E2))
    (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2) (kx : Work.Cusp.E3) (δ : ℝ)
    (z : {q : Work.Cusp.E4 // q ∈ Work.RTOwed.jBox v cU k W kx δ})
    (hz : z.1 = Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w)
    (hlt : Work.Cusp.rJ < z.1 0) :
    Work.RTOwed.jCoordM a v D cU k W kx δ z = a.incW v (p, y) := by
  have hnrm : Work.Cusp.nrm (p : Work.Cusp.E2) ≤ 1 := max_le hp.1 hp.2
  -- The UHS point `polarToUHS v z.1 = Θ_v(p,w)` lies **on or above** the ceiling `β`, so the
  -- collar branch of `cuspCoordMTop` (and not its chimney branch) produces the value of `jCoordM`.
  have hge : Work.Cusp.beta
        (Work.Cusp.xOf (Work.Cusp.polarToUHS v (Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w)))
      ≤ (Work.Cusp.polarToUHS v (Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w)) 3 := by
    rw [Work.Cusp.polarToUHS_ThetaPolar v (p : Work.Cusp.E2) w h1 hnrm]
    rw [show Work.Cusp.beta (Work.Cusp.xOf (Work.Cusp.ThetaOuter v (p : Work.Cusp.E2) w))
          = Work.Cusp.beta (Work.Cusp.cuspX v (Work.Cusp.u (p : Work.Cusp.E2)) w) from by
        congr 1
        ext i
        fin_cases i <;> simp [Work.Cusp.ThetaOuter, Work.Cusp.xOf]]
    rw [show (Work.Cusp.ThetaOuter v (p : Work.Cusp.E2) w) 3
          = Work.Cusp.collarS v (p : Work.Cusp.E2) w from by simp [Work.Cusp.ThetaOuter]]
    exact collarHeight_ge_self hnrm (Work.Cusp.beta_pos _)
      (lt_of_le_of_lt (Work.Cusp.beta_le_max _) Work.Cusp.betaMax_lt_sJ)
  -- Destructure the box point so that `z.1 = Θ_v(p,w)` can be substituted throughout.
  cases z with
  | mk v1 v2 =>
    subst hz
    unfold Work.RTOwed.jCoordM
    rw [dite_eq_right (not_le.mpr hlt)]
    unfold Work.Cusp.cuspCoordMTop
    rw [dite_eq_right (not_lt.mpr hge)]
    -- On the collar the outer chart inverts to `(p,w)`.
    have hcy : Work.Cusp.cuspInvOuter v
          (Work.Cusp.polarToUHS v (Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w))
        = ((p : Work.Cusp.E2), w) := by
      rw [Work.Cusp.polarToUHS_ThetaPolar v (p : Work.Cusp.E2) w h1 hnrm]
      exact Work.Cusp.cuspInvOuter_ThetaOuter_half v (p : Work.Cusp.E2) w hp h1 hnrm
    have hX1 : (Work.Cusp.cuspInvOuter v
          (Work.Cusp.polarToUHS v (Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w))).1
        = (p : Work.Cusp.E2) := by rw [hcy]
    have hX2 : (Work.Cusp.cuspInvOuter v
          (Work.Cusp.polarToUHS v (Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w))).2
        = w := by rw [hcy]
    refine congrArg (a.incW v) ?_
    refine Prod.ext ?_ ?_
    · exact Subtype.ext hX1
    · rw [hX2]
      rw [show (fun i => ((w i : ℝ) : AddCircle (1 : ℝ))) = D.tor y from funext hw]
      exact D.tor.symm_apply_apply y

end Work.RTOwed
