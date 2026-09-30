import Mathlib
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.exists_section_box
import Submission.Work.Cusp.exists_polarChartM
import Submission.Work.Cusp.uqOf_ThetaPolarS
import Submission.Work.Cusp.cuspInvInner_ThetaPolarS
import Submission.Work.Cusp.radial_eq_inner
import Submission.Work.Cusp.cuspInvInner_mem_polarStratum
import Submission.Work.Cusp.ThetaPolarS_cuspInvInner

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Real InnerProductSpace

namespace Work.Cusp

/-- **The polar chart does not move the layer point it is built from.**

If `p` is a point of the square with `0 < ‖p‖∞ ≤ 1/2` and `y` is any pair of real cusp
coordinates, then the inner-chart inverse `cuspInvInner` inverts the `(c,k)`-shifted polar chart
`ThetaPolarS v (u p - 1/8)` *exactly* at the point `(p,y)`:

`q := ThetaPolarS v (u p - 1/8) p y = (2 r_J ‖p‖∞, θ, wOf v y)` satisfies

* its radial coordinate is `2 r_J ‖p‖∞ ≤ r_J`, so the layer parameter recovered by `cuspInvInner`
  is `t = q 0/(2 r_J) = ‖p‖∞`;
* its `w`-coordinates are `wOf v y`, and `invY v` inverts `wOf v` (`invY_wOf`), so the recovered
  cusp coordinate is `y`;
* its recovered perimeter coordinate is `uqOf v q = uS c p = c + fract (u p - c)`, which for the
  shift `c = u p - 1/8` is `u p - 1/8 + 1/8 = u p`.

Hence `cuspInvInner v q = (‖p‖∞ • bndOfU (u p), y) = (p, y)`, the last step being
`bndOfU_u` (`bndOfU (u p) = bnd p`) and `‖p‖∞ • bnd p = p`. -/
private theorem cuspInvInner_ThetaPolarS_self (v : Fin 5) (p y : E2) (hp : p ∈ Sq)
    (hp0 : 0 < nrm p) (hple : nrm p ≤ 1/2) :
    cuspInvInner v (ThetaPolarS v (u p - 1/8) p y) = (p, y) := by
  set q : E4 := ThetaPolarS v (u p - 1/8) p y with hqdef
  have hq0 : q 0 = 6 * nrm p := by
    rw [hqdef,
      show (ThetaPolarS v (u p - 1/8) p y) 0 = radial v p y from by simp [ThetaPolarS],
      radial_eq_inner v p y hple]
    rw [rJ]; ring
  have hqle : q 0 ≤ rJ := by rw [hq0, rJ]; linarith
  have hq23 : (!₂[q 2, q 3] : E2) = wOf v y := by
    rw [hqdef]; ext i; fin_cases i <;> simp [ThetaPolarS]
  have huu : (q 1 - 2 * π * (⟪cuspY v (invY v !₂[q 2, q 3]), slope v⟫_ℝ / ‖slope v‖ ^ 2))
      / (2 * π) = u p := by
    rw [cuspInvInner_uu, hqdef, uqOf_ThetaPolarS, uS]
    have h1 : u p - (u p - 1/8) = (1/8 : ℝ) := by ring
    rw [h1, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    ring
  have hfirst : (cuspInvInner v q).1 = p := by
    have hb : (cuspInvInner v q).1 = (q 0 / (2 * rJ)) •
        bndOfU ((q 1 - 2 * π * (⟪cuspY v (invY v !₂[q 2, q 3]), slope v⟫_ℝ / ‖slope v‖ ^ 2))
          / (2 * π)) := by
      simp only [cuspInvInner, ite_eq_left hqle]
    rw [hb, huu, hq0]
    have htriv : 6 * nrm p / (2 * rJ) = nrm p := by rw [rJ]; ring
    rw [htriv, bndOfU_u hp (by intro h; rw [h] at hp0; simp [nrm] at hp0)]
    rw [bnd, smul_smul, mul_inv_cancel₀ (ne_of_gt hp0), one_smul]
  have hsecond : (cuspInvInner v q).2 = y := by
    simp only [cuspInvInner]
    rw [hq23, invY_wOf]
  rw [Prod.ext_iff]
  exact ⟨hfirst, hsecond⟩

theorem polarLayer_subset_range_polarCoordM (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (tor : a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ))) (y : a.Torus v)
    (p : Work.Space.SquarePt) (hp : 1/24 < nrm (p : E2)) (hp2 : nrm (p : E2) < 1/2) :
    ∃ (c : ℝ) (k : Fin 4) (W : Set E2), IsOpen W ∧
      (∀ y' y'' : E2, wOf v y' ∈ W → wOf v y'' ∈ W →
        (∀ i, ((y' i : ℝ) : AddCircle (1 : ℝ)) = ((y'' i : ℝ) : AddCircle (1 : ℝ))) → y' = y'') ∧
      a.incW v (p, y) ∈ Set.range (polarCoordM a v tor c k W) := by
  -- `p` is a nonzero point of the square
  have hpSq : (p : E2) ∈ Sq := by simpa only [Work.Space.Sq, Sq] using p.2
  have hp0 : 0 < nrm (p : E2) := by linarith
  have hple : nrm (p : E2) ≤ 1/2 := le_of_lt hp2
  -- lift the abstract torus coordinate `y` to a real pair `y0`
  obtain ⟨y0, hy0⟩ : ∃ y0 : E2, ∀ i, ((y0 i : ℝ) : AddCircle (1 : ℝ)) = tor y i :=
    ⟨!₂[(AddCircle.equivIco (1:ℝ) (0:ℝ) (tor y 0) : ℝ),
        (AddCircle.equivIco (1:ℝ) (0:ℝ) (tor y 1) : ℝ)], by
      intro i; fin_cases i <;> simp [AddCircle.coe_equivIco]⟩
  -- the local section of `wOf v` around `wOf v y0`
  obtain ⟨W, hWopen, _hWy, hWsec⟩ := exists_section_box v y0
  -- the chart shift, the wedge index and the chart target
  set c : ℝ := u (p : E2) - 1/8 with hc
  refine ⟨c, 0, W, hWopen, hWsec, ?_⟩
  set q : E4 := ThetaPolarS v c (p : E2) y0 with hqdef
  have hc' : c = u (p : E2) - 1/8 := hc
  have hq0 : q 0 = 6 * nrm (p : E2) := by
    rw [hqdef, hc',
      show (ThetaPolarS v (u (p : E2) - 1/8) (p : E2) y0) 0 = radial v (p : E2) y0 from by
        simp [ThetaPolarS],
      radial_eq_inner v (p : E2) y0 hple]
    rw [rJ]; ring
  have hq23 : (!₂[q 2, q 3] : E2) = wOf v y0 := by
    rw [hqdef]; ext i; fin_cases i <;> simp [ThetaPolarS]
  have huq : uqOf v q = uS c (p : E2) := by
    rw [hqdef]; exact uqOf_ThetaPolarS v c (p : E2) y0
  have hfrac : uqOf v q - c = 1/8 := by
    rw [huq, uS, hc']
    have h1 : u (p : E2) - (u (p : E2) - 1/8) = (1/8 : ℝ) := by ring
    rw [h1, Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩]
    ring
  -- `q` lies in the chart box
  have hqmem : q ∈ polarBoxSect v c 0 W := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [polarBox]; constructor
      · rw [hq0]; linarith
      · rw [hq0, rJ]; linarith
    · rw [hq23]; exact _hWy
    · rw [hq0, rJ]; linarith
    · rw [hfrac]; norm_num
    · rw [hfrac]; exact ⟨by norm_num, by norm_num⟩
  refine ⟨⟨q, hqmem⟩, ?_⟩
  -- the chart inverts to `(p, y0)`, and `y0` is a lift of `tor y`
  have hci : cuspInvInner v q = ((p : E2), y0) := by
    rw [hqdef, hc']
    exact cuspInvInner_ThetaPolarS_self v (p : E2) y0 hpSq hp0 hple
  have h1 : (cuspInvInner v q).1 = (p : E2) := congrArg Prod.fst hci
  have h2 : (cuspInvInner v q).2 = y0 := congrArg Prod.snd hci
  simp only [polarCoordM]
  refine congrArg (a.incW v) ?_
  rw [Prod.mk.injEq]
  refine ⟨Subtype.ext h1, ?_⟩
  have hfun : (fun i : Fin 2 => (((cuspInvInner v q).2 i : ℝ) : AddCircle (1 : ℝ))) = tor y := by
    rw [h2]; funext i; exact hy0 i
  rw [hfun, Homeomorph.symm_apply_apply]

end Work.Cusp
