/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The Jacobian enclosure bound `‖fderiv Φ u - matLin Ac‖ ≤ Σ|Δ|` on the Krawczyk ball

Item **A1** of the `SeedCertNum` contract: the fifth numeric hypothesis `hJac` of
`Work.SeedCertNum.krawczyk_numeric` (the enclosure of the Jacobian of `Φ` on the ball by the
matrix `Ac` with error `Δ`).

Three ingredients are put together:

* `Work.SeedCertNum.jentry_mem_Jint` — every entry `(i,j)` of the Jacobian `matOf (LPhi x₀ u)`
  lies in the interval `Jint Ctyp Xz i j` (the interval enclosure of the corresponding partial
  derivative over the box `Xz × Xt`);
* `Work.SeedCert.KrawData.allJint`, one of the conjuncts of the Boolean certificate `ok`, which
  states exactly `Jint Ctyp Xz i j ⊆ [Ac i j - Δ i j, Ac i j + Δ i j]` for all `(i,j)` — turned
  here into the real inequality `|x - Ac i j| ≤ Δ i j` for `x ∈ Jint (i,j)`
  (`allJint_entry_abs_sub_le`);
* the row-sum estimate `Work.SeedCertNum.norm_matLin_sub_le`, which bounds the operator norm of
  the difference of two `matLin`s by the sum of the (absolute values of the) entrywise data.

The bridge between the analytic ball `closedBall u₀ rad` and the box `Xz × Xt` is
`Work.SeedCertNum.mem_closedBall_iff`; the derivative is identified by
`Work.SeedCertNum.hasFDerivAt_Phi` (hence `fderiv Φ u = LPhi x₀ u`) and the matrix of a linear
map is recovered with `Work.SeedCertNum.matLin_matOf`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Cert
import Submission.Work.SeedCertNum.jentry_mem_Jint
import Submission.Work.SeedCertNum.norm_matLin_sub_le
import Submission.Work.SeedCertNum.hasFDerivAt_Phi
import Submission.Work.SeedCertNum.matLin_matOf
import Submission.Work.SeedCertNum.mem_closedBall_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- Every point of `E3` is recovered from its complex coordinate `zOf u` and its last
coordinate `u.2.2`: `mkE (zOf u) u.2.2 = u`. -/
theorem mkE_zOf_self (u : Work.SeedCert.E3) :
    Work.SeedCert.mkE (Work.SeedCert.zOf u) u.2.2 = u := by
  obtain ⟨a, b, c⟩ := u
  simp [Work.SeedCert.mkE, Work.SeedCert.zOf]

/-- **The entrywise content of `allJint`**: if the Boolean `D.allJint` is `true`, then every
`x` in the interval `Jint D.Ctyp D.Xz i j` satisfies `|x - (D.Ac i j).toReal| ≤ (D.Δ i j).toReal`.

`D.allJint` is the `Bool` `∀ i j, (Ac i j - Δ i j ≤ (Jint i j).lo) && ((Jint i j).hi ≤ Ac i j + Δ i j)`;
each of the two conjuncts is converted with `Dya.toReal_le_of_le` (`Dya.le` is the exact,
kernel-checkable dyadic comparison `toReal`-reflected by `Dya.toReal_le_iff`), which yields
`Ac i j - Δ i j ≤ x ≤ Ac i j + Δ i j` for `x ∈ Jint i j`, i.e. `|x - Ac i j| ≤ Δ i j`. -/
theorem allJint_entry_abs_sub_le (D : Work.SeedCert.KrawData) (hJ : D.allJint = true)
    (i j : Fin 3) {x : ℝ} (hx : x ∈ (Work.SeedCert.Jint D.Ctyp D.Xz i j).toSet) :
    |x - (D.Ac i j).toReal| ≤ (D.Δ i j).toReal := by
  simp only [Work.SeedCert.KrawData.allJint] at hJ
  have hi := (List.all_eq_true.mp hJ) i (List.mem_finRange i)
  have hij := (List.all_eq_true.mp hi) j (List.mem_finRange j)
  simp only [Bool.and_eq_true] at hij
  obtain ⟨hlo, hhi⟩ := hij
  have hlo' : (D.Ac i j).toReal - (D.Δ i j).toReal ≤
      (Work.SeedCert.Jint D.Ctyp D.Xz i j).lo.toReal := by
    have := Work.SeedCert.Dya.toReal_le_of_le hlo
    rwa [Work.SeedCert.Dya.toReal_sub] at this
  have hhi' : (Work.SeedCert.Jint D.Ctyp D.Xz i j).hi.toReal ≤
      (D.Ac i j).toReal + (D.Δ i j).toReal := by
    have := Work.SeedCert.Dya.toReal_le_of_le hhi
    rwa [Work.SeedCert.Dya.toReal_add] at this
  rw [Work.SeedCert.IV.mem_toSet] at hx
  obtain ⟨hxl, hxh⟩ := hx
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The dyadic sum `D.eps = Σ_{ij} |Δ_{ij}|` computes the real number `Σ_{ij} |Δr_{ij}|`:
`toReal` turns the nested dyadic sum into a sum of reals and `Dya.abs` into `|·|`.  This is the
form in which the fifth numeric hypothesis `hJac` of `krawczyk_numeric` is phrased (with `eps`),
matching `matSum (matAbs (Δr D))` on the nose. -/
theorem kraw_eps_toReal_eq_matSum (D : Work.SeedCert.KrawData) :
    (Work.SeedCert.KrawData.eps D).toReal
      = Work.SeedCert.matSum (Work.SeedCert.matAbs (Work.SeedCert.KrawData.Δr D)) := by
  simp only [Work.SeedCert.KrawData.eps, Work.SeedCert.KrawData.Δr, Work.SeedCert.matSum,
    Work.SeedCert.matAbs, Work.SeedCert.matSumDya, Work.SeedCert.matAbsDya,
    Work.SeedCert.Dya.toReal_add, Work.SeedCert.Dya.toReal_abs]
  norm_num [Fin.sum_univ_three]
  ring

theorem fderiv_Phi_bound (D : Work.SeedCert.KrawData) (h : Work.SeedCert.KrawData.ok D = true) :
    ∀ u ∈ Metric.closedBall (Work.SeedCert.KrawData.u₀ D) (Work.SeedCert.KrawData.rad D),
      ‖fderiv ℝ (Work.SeedCert.Phi (D.x₀).toReal) u - Work.SeedCert.matLin (Work.SeedCert.KrawData.Acr D)‖
        ≤ Work.SeedCert.matSum (Work.SeedCert.matAbs (Work.SeedCert.KrawData.Δr D)) := by
  have hJ : D.allJint = true := by
    simp only [Work.SeedCert.KrawData.ok, Bool.and_eq_true] at h
    exact h.1.1.2
  intro u hu
  -- move `u` into the normal form `mkE (zOf u) u.2.2` so that the box lemmas apply
  have hu' : Work.SeedCert.mkE (Work.SeedCert.zOf u) u.2.2 ∈
      Metric.closedBall (Work.SeedCert.KrawData.u₀ D) (Work.SeedCert.KrawData.rad D) := by
    rw [mkE_zOf_self]
    exact hu
  obtain ⟨hz, ht⟩ := (Work.SeedCertNum.mem_closedBall_iff D).mp hu'
  -- every entry of the Jacobian is within `Δ` of the corresponding entry of `Ac`
  have hentry : ∀ i j,
      |Work.SeedCert.matOf (Work.SeedCert.LPhi (D.x₀).toReal u) i j - (D.Ac i j).toReal|
        ≤ (D.Δ i j).toReal := by
    intro i j
    refine allJint_entry_abs_sub_le D hJ i j ?_
    have hj := jentry_mem_Jint (x₀ := D.x₀) (Xt := D.Xt) (Xz := D.Xz)
      (z := Work.SeedCert.zOf u) (t := u.2.2) hz ht i j
    rwa [mkE_zOf_self] at hj
  -- row-sum estimate for the difference of the two `matLin`s
  have hmain := norm_matLin_sub_le (X := Work.SeedCert.matOf (Work.SeedCert.LPhi (D.x₀).toReal u))
    (Y := Work.SeedCert.KrawData.Acr D) (Δ := Work.SeedCert.matAbs (Work.SeedCert.KrawData.Δr D))
    (fun i j => by
      have h2 : ((Work.SeedCert.KrawData.Δr D) i j) ≤ |((Work.SeedCert.KrawData.Δr D) i j)| :=
        le_abs_self _
      exact le_trans (hentry i j) h2)
  -- identify `fderiv Φ u` with `LPhi x₀ u` and `LPhi x₀ u` with `matLin (matOf (LPhi x₀ u))`
  have hfd : fderiv ℝ (Work.SeedCert.Phi (D.x₀).toReal) u
      = Work.SeedCert.LPhi (D.x₀).toReal u :=
    (hasFDerivAt_Phi (D.x₀).toReal u).fderiv
  rw [hfd, ← matLin_matOf (Work.SeedCert.LPhi (D.x₀).toReal u)]
  exact hmain

/-- The same enclosure in the form used by `krawczyk_numeric`: the error bound is
`(KrawData.eps D).toReal`. -/
theorem fderiv_Phi_bound_eps (D : Work.SeedCert.KrawData)
    (h : Work.SeedCert.KrawData.ok D = true) :
    ∀ u ∈ Metric.closedBall (Work.SeedCert.KrawData.u₀ D) (Work.SeedCert.KrawData.rad D),
      ‖fderiv ℝ (Work.SeedCert.Phi (D.x₀).toReal) u
          - Work.SeedCert.matLin (Work.SeedCert.KrawData.Acr D)‖
        ≤ (Work.SeedCert.KrawData.eps D).toReal := by
  rw [kraw_eps_toReal_eq_matSum]
  exact fderiv_Phi_bound D h

end Work.SeedCertNum
