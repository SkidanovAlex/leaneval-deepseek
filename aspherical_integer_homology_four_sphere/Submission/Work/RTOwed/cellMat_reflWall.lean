import Mathlib
import Submission.Work.RTOwed.mobius_reflWall_high
import Submission.Work.RTOwed.wallLo_slack_sign
import Submission.Work.RTOwed.cuspWallTableCerts
import Submission.Work.RTOwed.mbarLow_foldLocal_helpers

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The wall reflection of the cusp charts, in the coordinates of the Möbius chart `cellMat`

`Work.RTOwed.cellMat v i r b k` is the Möbius matrix of the fold chart of the fold piece `(i,r)` in
the cusp coordinates of the cell `(b,k)`:

`mobius (cellMat v i r b k) q = foldTheta i r (chartKlein b (mkE4 (uhsXj q - lamV v k) (q 3)))`
(`foldTheta_chartKlein_eq_mobius`).

The target lemma `cellMat_reflWall` computes what happens to this Möbius map under the reflection of
the cusp coordinate `m` in the *wall* of the cube `b` which is the `t`-th wall of the fold piece:

  `foldWalls i r t = wallLo b m`   ⟹
  `mobius (cellMat v i r b k) (reflWall4 m (cubeCorner b m + lamV v k m - 1/2) z)
     = reflCoords {t} (mobius (cellMat v i r b k) z)`   for `0 < z 3`.

The reflection centre `cubeCorner b m + lamV v k m - 1/2` is exactly the cusp coordinate of the
hyperplane `{x m = cubeCorner b m}` in the cube coordinates `x = uhsXj q - lamV v k`; the height
`1/2` is the translation `cuspH` between the cusp and cube upper half space coordinates.

## Method

The proof is an application of `Work.RTOwed.mobius_reflWall_high`: the (apparently weak) hypothesis
"the wall is mapped into the coordinate hyperplane `{y t = 0}` at heights `≥ 11/10`" is verified
with the coordinate formula of the fold chart,

  `fold_theta_coord`:  `√(1-‖y‖²) (foldTheta i r y) t = ± sideSlack (foldWalls i r t) y · (. 3)`,

together with `sideSlack_wallLo_chartKlein_eq_zero`: the lower-wall slack of the cube `b` vanishes at
the chart point exactly when the cube coordinate `m` equals `cubeCorner b m`.  On the wall
`u m = cubeCorner b m` the `t`-th fold coordinate therefore vanishes; since the fold chart of the
cusp chart is the Möbius map `cellMat`, the `t`-th row of `cellMat` annihilates the lift of every
point of the wall, which is the row relation needed by `mobius_reflWall_high`.

The remaining bookkeeping is the identification of the fold index `t : Fin (foldCodim i)` with a
horizontal coordinate `f3of (foldCodim i) (foldCodim_le i) t : Fin 3` (`foldCodim i ≤ 3`), and the
corresponding identification of `reflCoords {t}` with `reflCoord` of that coordinate.
-/

noncomputable section

open Set Topology Function Matrix
open scoped Matrix

namespace Work.RTOwed

open Work.FoldInst

/-! ### The inclusion of the fold indices into the horizontal coordinates -/

/-- **The canonical inclusion of the fold indices into the horizontal coordinates.**  Since
`foldCodim i ≤ 3` (`foldCodim_le`), the `t`-th fold coordinate is one of the first three coordinates
of the upper half space model. -/
def f3of (c : ℕ) (hc : c ≤ 3) (t : Fin c) : Fin 3 := ⟨t.val, by omega⟩

@[simp] theorem f3of_val (c : ℕ) (hc : c ≤ 3) (t : Fin c) : (f3of c hc t : ℕ) = t.val := rfl

/-- **The singleton fold reflection is the coordinate reflection.**  The reflection of the single
fold coordinate `t` (as an element of `Finset (Fin (foldCodim i))`) is the reflection of the
horizontal coordinate `f3of (foldCodim i) (foldCodim_le i) t`. -/
theorem reflCoords_singleton_eq_reflCoord {c : ℕ} (hc : c ≤ 3) (t : Fin c) :
    reflCoords ({t} : Finset (Fin c)) = Work.RTOwed.reflCoord (f3of c hc t) := by
  funext z
  refine Work.Fold.e4_ext fun i => ?_
  rw [reflCoords_apply, Work.RTOwed.reflCoord_apply]
  by_cases hi : (i : ℕ) < c
  · have hi3 : (i : ℕ) < 3 := by omega
    rw [dite_eq_left hi, dite_eq_left hi3]
    have e1 : ((⟨i, hi⟩ : Fin c) ∈ ({t} : Finset (Fin c))) ↔ (i : ℕ) = t.val := by
      simp [Finset.mem_singleton, Fin.ext_iff]
    have e2 : ((⟨i, hi3⟩ : Fin 3) = f3of c hc t) ↔ (i : ℕ) = t.val := by
      simp [f3of, Fin.ext_iff]
    by_cases hiv : (i : ℕ) = t.val
    · rw [ite_eq_left (e1.mpr hiv), ite_eq_left (e2.mpr hiv)]
    · rw [ite_eq_right (fun h => hiv (e1.mp h)), ite_eq_right (fun h => hiv (e2.mp h))]
  · rw [dite_eq_right hi]
    by_cases hi3 : (i : ℕ) < 3
    · rw [dite_eq_left hi3]
      have hne : ¬ ((⟨i, hi3⟩ : Fin 3) = f3of c hc t) := by
        intro hcon
        have hval := congrArg Fin.val hcon
        rw [Fin.val_mk, f3of_val] at hval
        omega
      rw [ite_eq_right hne, one_mul]
    · rw [dite_eq_right hi3]

/-! ### The lower-wall slack of the cube chart -/

/-- **The lower-wall slack vanishes exactly on the wall.**  For a cube `a : Fin 48`, a wall
coordinate `i : Fin 3`, any point `u` of the cube coordinates and any height `s ≥ 11/10`, the slack
of the side `wallLo a i` at the chart point `chartKlein a (mkE4 u s)` vanishes exactly when the
`i`-th coordinate of `u` is the corner `cubeCorner a i`.

This is `Work.RTOwed.wallLo_slack_sign` with the (unused) box hypothesis dropped: the identity
`sideSlack (wallLo a i) (chartKlein a (mkE4 u s)) = L · (u i - cubeCorner a i) / chartVec a u s 4`
with `L > 0` and `chartVec a u s 4 > 0` holds for *every* `u` and every `s ≥ 11/10`. -/
theorem sideSlack_wallLo_chartKlein_eq_zero (a : Fin 48) (i : Fin 3) (u : CuspE3) {s : ℝ}
    (hs : 11 / 10 ≤ s) :
    Work.FoldInst.sideSlack (wallLo a i) (chartKlein a (mkE4 u s)) = 0
      ↔ u i = (Work.Cusp.cubeCorner a i : ℝ) := by
  have hs0 : s ≠ 0 := by linarith
  have hVpos : 0 < chartKleinMem.chartVec a u s 4 := chartVec4_pos_all a u hs
  have hPpos : 0 < (chartKleinMem.Ls a (wallLo a i) i : ℝ) := by
    exact_mod_cast wallLo_Ls_pos_all a i
  have hkey : Work.FoldInst.sideSlack (wallLo a i) (chartKlein a (mkE4 u s))
      = ((chartKleinMem.Ls a (wallLo a i) i : ℝ) / chartKleinMem.chartVec a u s 4)
          * (u i - (Work.Cusp.cubeCorner a i : ℝ)) := by
    rw [chartKleinMem.sideSlack_eq a (wallLo a i) u s hs0 hVpos.ne',
      wallLo_Nside]
    ring
  rw [hkey, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (div_ne_zero (ne_of_gt hPpos) (ne_of_gt hVpos))
    · exact sub_eq_zero.mp h
  · intro h; exact Or.inr (by rw [h, sub_self])

/-- **The cube chart of a point of positive height lies in the Klein ball.** -/
theorem chartKlein_mem_ball_chart (a : Fin 48) {q : CuspE4} (hq : 0 < q 3) :
    chartKlein a q ∈ Work.HypModel.ball := by
  rw [chartKlein_eq]
  refine Work.HypModel.kleinOfHyp_mem_ball (Work.HypModel.isLorentzMat_mem_upperSheet
    (chartK_isLorentz a) ?_)
  exact hypOfUHS_mem_upperSheet hq

/-! ### The `t`-th fold coordinate vanishes on the wall -/

/-- **The `t`-th fold coordinate vanishes on the lower wall `wallLo a m`.**  If the `t`-th wall of
the fold piece `(i,r)` is the lower wall `wallLo a m` of the cube `a` (`ht`), and the cube
coordinate `u` lies on that wall (`hum`), then the `t`-th coordinate of the fold chart of the chart
point is zero.  Here `s : Fin 3` is the horizontal coordinate corresponding to `t`
(`hs : (s:ℕ) = t.val`).

The proof is the coordinate formula `fold_theta_coord` of the fold chart: the `s`-th chart
coordinate is `± sideSlack (foldWalls i r t) y` times a nonzero factor, and the slack vanishes by
`sideSlack_wallLo_chartKlein_eq_zero`. -/
theorem foldTheta_coord_zero_of_wall (i : Fin 98) (r : Fin (foldCodim i) → Bool) (a : Fin 48)
    (m : Fin 3) (t : Fin (foldCodim i)) (s : Fin 3) (hs : (s : ℕ) = t.val)
    (u : CuspE3) {h : ℝ} (hh : 11 / 10 ≤ h) (hum : u m = (Work.Cusp.cubeCorner a m : ℝ))
    (ht : foldWalls i r t = wallLo a m) :
    (foldTheta i r (chartKlein a (mkE4 u h))) (f3to4 s) = 0 := by
  have hs' : (s : ℕ) < foldCodim i := by rw [hs]; exact t.isLt
  have hball : chartKlein a (mkE4 u h) ∈ Work.HypModel.ball :=
    chartKlein_mem_ball_chart a (by simp [mkE4]; linarith)
  have hslack : Work.FoldInst.sideSlack (wallLo a m) (chartKlein a (mkE4 u h)) = 0 :=
    (sideSlack_wallLo_chartKlein_eq_zero a m u hh).mpr hum
  have hg : (foldNr i).mulVec (Work.HypModel.ray (act (toG (foldKr i r))
      (chartKlein a (mkE4 u h)))) (f3to5 (foldWallPos i s)) = 0 := by
    rw [foldNr_mulVec_ray_row,
      sideSlack_act (toG (foldKr i r)) (foldTriple i (foldWallPos i s)) (chartKlein a (mkE4 u h))]
    have hfin : (⟨s.val, hs'⟩ : Fin (foldCodim i)) = t := Fin.ext hs
    rw [← foldWalls_eq i r s hs', hfin, ht]
    exact hslack
  rw [foldTheta_coord_apply i r _ hball s hs', hg]
  ring

/-! ### The target -/

theorem cellMat_reflWall (v : Fin 5) (i : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (b : Fin 48) (k' : Fin 3 → ℤ) (m : Fin 3) (t : Fin (Work.FoldInst.foldCodim i))
    (ht : Work.FoldInst.foldWalls i r t = wallLo b m) :
    ∀ z : Work.RTOwed.CuspE4, 0 < z 3 →
      Work.HypModel.mobius (Work.RTOwed.cellMat v i r b k')
          (Work.RTOwed.reflWall4 m ((Work.Cusp.cubeCorner b m : ℝ) + (Work.RTOwed.cuspCert.lamV v k') m - 1 / 2) z)
        = Work.FoldInst.reflCoords ({t} : Finset (Fin (Work.FoldInst.foldCodim i)))
            (Work.HypModel.mobius (Work.RTOwed.cellMat v i r b k') z) := by
  intro z hz
  set t₀ : Fin 3 := f3of (foldCodim i) (foldCodim_le i) t with ht₀
  set c : ℝ := (Work.Cusp.cubeCorner b m : ℝ) + (cuspCert.lamV v k') m - 1 / 2 with hc
  have hL : Work.HypModel.IsLorentzMat (cellMat v i r b k') := cellMat_isLorentz v i r b k'
  -- The wall hypothesis of `mobius_reflWall_high`: the `t`-th row of `cellMat` annihilates the
  -- lift of every point of positive height on the wall `{z m = c}`.
  have hW : ∀ w : Work.HypModel.E4, 11 / 10 ≤ w 3 → w (f3to4 m) = c →
      (cellMat v i r b k' *ᵥ Work.HypModel.hypOfUHS w) (f3to5 t₀) = 0 := by
    intro w hw hwm
    have hwpos : 0 < w 3 := by linarith
    -- the cube coordinate of the wall point is the corner of the cube
    have hum : (uhsXj w - cuspCert.lamV v k') m = (Work.Cusp.cubeCorner b m : ℝ) := by
      rw [PiLp.sub_apply]
      have hx : uhsXj w m = w (f3to4 m) + 1 / 2 := by
        fin_cases m <;> simp [uhsXj, xOf4, cuspH]
      have hl : cuspCert.lamV v k' m = (cuspCert.lamK v k' m : ℝ) := rfl
      rw [hx, hwm, hc, hl]
      ring
    -- the `t`-th fold coordinate vanishes there
    have hcoord : (foldTheta i r (chartKlein b (mkE4 (uhsXj w - cuspCert.lamV v k') (w 3))))
        (f3to4 t₀) = 0 :=
      foldTheta_coord_zero_of_wall i r b m t t₀ rfl (uhsXj w - cuspCert.lamV v k') hw hum ht
    have hmob : Work.HypModel.mobius (cellMat v i r b k') w
        = foldTheta i r (chartKlein b (mkE4 (uhsXj w - cuspCert.lamV v k') (w 3))) :=
      (foldTheta_chartKlein_eq_mobius v i r b k' w hwpos).symm
    have hmzero : (Work.HypModel.mobius (cellMat v i r b k') w) (f3to4 t₀) = 0 := by
      rw [hmob]; exact hcoord
    -- translate back to the lift of `w`
    have hPup : (cellMat v i r b k' *ᵥ Work.HypModel.hypOfUHS w) ∈ Work.HypModel.upperSheet :=
      Work.HypModel.isLorentzMat_mem_upperSheet hL (hypOfUHS_mem_upperSheet hwpos)
    have hδ : (cellMat v i r b k' *ᵥ Work.HypModel.hypOfUHS w) 4
        - (cellMat v i r b k' *ᵥ Work.HypModel.hypOfUHS w) 3 ≠ 0 :=
      ne_of_gt (Work.HypModel.upperSheet_four_sub_three_pos hPup)
    rw [Work.HypModel.mobius, uhsOfHyp_coord_f3to5] at hmzero
    exact (mul_eq_zero.mp hmzero).resolve_right (inv_ne_zero hδ)
  have hmain := mobius_reflWall_high hL m t₀ c hW z hz
  rw [hmain, ht₀]
  rw [← reflCoords_singleton_eq_reflCoord (foldCodim_le i) t]

end Work.RTOwed
