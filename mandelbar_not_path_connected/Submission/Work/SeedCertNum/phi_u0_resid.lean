/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# `‖Φ u₀‖ ≤ residBound`

Item **A1** of the `SeedCertNum` contract (`NOTES_LEAD_mandelbar_noncusp.md` §2.2): the residual
bound `etaBound = β · residBound` of the Krawczyk certificate is only useful if `residBound` really
bounds the residual `‖Φ u₀‖`, where `u₀ = (Re z₀, Im z₀, Im c₀)` is the centre of the box and `Φ`
is the map of `Submission/Work/SeedCertNum/A1Defs.lean`.

`residBound D` is computed from `residBox D`, the interval evaluation of `Φ` on the *degenerate*
boxes
`Xzp = [ux,ux] × [uy,uy]` (`z = z₀`) and `Xtp = [ut,ut]` (`Im c = t₀`).  On degenerate boxes every
interval operation of the box layer is exact, so each component of `Phi x₀ u₀` lies in the
corresponding interval of `residBox D`; `residBound D` is the maximum of the `maxAbs`es of the six
endpoints, hence an upper bound for the sup norm of the three components.

The interval soundness is `mem_boxV` (`Submission/Work/SeedCertNum/Jet1.lean`) for `Z₅`,
`mem_boxPi` (`Submission/Work/SeedCertNum/A1Defs.lean`) for `Π`, together with the interval
operations `CBox.mem_sub`, `IV.mem_sub` of `Submission/Work/SeedCertNum/Box.lean`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Cert
import Submission.Work.SeedCertNum.d1Chart_sound_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- The first component bound: `residBox D`.1 bounds `(Θ u₀).re`. -/
theorem residBound_fst_le (D : KrawData) :
    (Dya.maxAbs (KrawData.residBox D).1.lo (KrawData.residBox D).1.hi).toReal ≤
      (KrawData.residBound D).toReal := by
  simp only [KrawData.residBound, Dya.toReal_max]
  exact le_trans (le_max_left _ _) (le_max_left _ _)

/-- The second component bound: `residBox D`.2.1 bounds `(Θ u₀).im`. -/
theorem residBound_snd_le (D : KrawData) :
    (Dya.maxAbs (KrawData.residBox D).2.1.lo (KrawData.residBox D).2.1.hi).toReal ≤
      (KrawData.residBound D).toReal := by
  simp only [KrawData.residBound, Dya.toReal_max]
  exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- The third component bound: `residBox D`.2.2 bounds `Π u₀ - 1`. -/
theorem residBound_trd_le (D : KrawData) :
    (Dya.maxAbs (KrawData.residBox D).2.2.lo (KrawData.residBox D).2.2.hi).toReal ≤
      (KrawData.residBound D).toReal := by
  simp only [KrawData.residBound, Dya.toReal_max]
  exact le_max_right _ _

/-- The centre as a point of the degenerate box: the sup-norm bound on `Φ u₀` reduces to the
componentwise bounds `(Θ u₀).re ∈ residBox.1`, `(Θ u₀).im ∈ residBox.2.1`,
`Π u₀ - 1 ∈ residBox.2.2`. -/
theorem phi_u0_resid (D : Work.SeedCert.KrawData) :
    ‖Work.SeedCert.Phi (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D)‖ ≤ (Work.SeedCert.KrawData.residBound D).toReal := by
  have huz : Work.SeedCert.KrawData.u₀ D =
      Work.SeedCert.mkE ((D.ux.toReal : ℂ) + (D.uy.toReal : ℂ) * Complex.I) (D.ut.toReal) := by
    simp [Work.SeedCert.KrawData.u₀, Work.SeedCert.mkE]
  have hz : ((D.ux.toReal : ℂ) + (D.uy.toReal : ℂ) * Complex.I) ∈
      (Work.SeedCert.KrawData.Xzp D).toSet := by
    rw [Work.SeedCert.KrawData.Xzp, Work.SeedCert.CBox.mem_toSet]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have ht : D.ut.toReal ∈ (Work.SeedCert.KrawData.Xtp D).toSet := by
    rw [Work.SeedCert.KrawData.Xtp, Work.SeedCert.IV.mem_toSet]
    exact ⟨le_rfl, le_rfl⟩
  have hV := Work.SeedCert.mem_boxV D.x₀ (Work.SeedCert.KrawData.Xtp D)
    (Work.SeedCert.KrawData.Xzp D) 5 hz ht
  have hPi := Work.SeedCert.mem_boxPi D.x₀ (Work.SeedCert.KrawData.Xtp D)
    (Work.SeedCert.KrawData.Xzp D) hz ht
  have hsub : Work.SeedCert.Z (D.x₀).toReal 5
        (Work.SeedCert.mkE ((D.ux.toReal : ℂ) + (D.uy.toReal : ℂ) * Complex.I) (D.ut.toReal))
      - ((D.ux.toReal : ℂ) + (D.uy.toReal : ℂ) * Complex.I) ∈
      ((Work.SeedCert.boxV (Work.SeedCert.pbox D.x₀ (Work.SeedCert.KrawData.Xtp D))
        (Work.SeedCert.KrawData.Xzp D) 5).sub (Work.SeedCert.KrawData.Xzp D)).toSet :=
    Work.SeedCert.CBox.mem_sub hV hz
  have h1 : (Work.SeedCert.Theta (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D)).re ∈
      (Work.SeedCert.KrawData.residBox D).1.toSet := by
    rw [huz]
    simp only [Work.SeedCert.KrawData.residBox, Work.SeedCert.Theta, Work.SeedCert.zOf_mkE,
      Work.SeedCert.CBox.re, Work.SeedCert.IV.mem_toSet]
    exact ⟨hsub.1, hsub.2.1⟩
  have h2 : (Work.SeedCert.Theta (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D)).im ∈
      (Work.SeedCert.KrawData.residBox D).2.1.toSet := by
    rw [huz]
    simp only [Work.SeedCert.KrawData.residBox, Work.SeedCert.Theta, Work.SeedCert.zOf_mkE,
      Work.SeedCert.CBox.im, Work.SeedCert.IV.mem_toSet]
    exact ⟨hsub.2.2.1, hsub.2.2.2⟩
  have h3 : Work.SeedCert.Pi (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D) - 1 ∈
      (Work.SeedCert.KrawData.residBox D).2.2.toSet := by
    rw [huz]
    have h1mem : (1 : ℝ) ∈ ({ lo := Dya.one, hi := Dya.one } : Work.SeedCert.IV).toSet := by
      rw [Work.SeedCert.IV.mem_toSet]
      exact ⟨le_of_eq Dya.toReal_one, le_of_eq Dya.toReal_one.symm⟩
    have := Work.SeedCert.IV.mem_sub hPi h1mem
    simpa only [Work.SeedCert.KrawData.residBox, Work.SeedCert.KrawData.Ctypp] using this
  have hn : ‖Work.SeedCert.Phi (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D)‖ =
      max |(Work.SeedCert.Theta (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D)).re|
        (max |(Work.SeedCert.Theta (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D)).im|
          |Work.SeedCert.Pi (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D) - 1|) := by
    rw [show Work.SeedCert.Phi (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D) =
        ((Work.SeedCert.Theta (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D)).re,
         (Work.SeedCert.Theta (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D)).im,
         Work.SeedCert.Pi (D.x₀).toReal (Work.SeedCert.KrawData.u₀ D) - 1) from rfl]
    simp [Prod.norm_def]
  rw [hn]
  refine max_le ?_ (max_le ?_ ?_)
  · exact le_trans (abs_le_maxAbs h1.1 h1.2) (residBound_fst_le D)
  · exact le_trans (abs_le_maxAbs h2.1 h2.2) (residBound_snd_le D)
  · exact le_trans (abs_le_maxAbs h3.1 h3.2) (residBound_trd_le D)

end Work.SeedCertNum
