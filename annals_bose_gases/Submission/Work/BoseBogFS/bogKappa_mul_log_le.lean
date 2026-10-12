import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.BogFSCompare
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open scoped Real Topology BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary arithmetic of the parameter block

The target `Work.BoseBogFS.bogKappa_mul_log_le` compares the FS cutoff combination
`bogKappa = (1-ε_T)c₁ + ε_T c₂` (up to the logarithm) with FS's error `lhyEps`.
At FS's parameter block `paramsAt μ (a v) = fsParams (μ(a v)³)` every quantity is a
monomial in the diluteness `D = μ(a v)³`:

* `s = D^{1/323}`, `d = D^{6/323}`, `Kl = D^{-3/646}`, `ε_T = D^{23/1292}`;
* hence `(Kl s)⁻¹ = D^{1/646}` (`sKl_inv`), `ε_T (Kl d s)⁻¹ = D^{1/1292}`
  (`eT_dsKl_inv`) and `Kl d s / (μa³)^{1/2} = D^{-156/323}`;
* and `c₁ = ½(K_ℓs)⁻¹√(μ/ρ)`, `c₂ = ½(K_ℓds)⁻¹√(μ/ρ)`.

Since `(Kl s)⁻¹ = (ε_T(K_ℓds)⁻¹)²`, the second cutoff dominates the first, and the
*`ε_T`-weighted fourth summand* of `lhyEps` pays the whole logarithm.  The three lemmas
below isolate the parameter arithmetic; independently proved twins of them were also
banked by colleagues (`Work.BoseBogFS.logSqrtBound`,
`Work.BoseBogFS.lhyEps_ge_eT_dsKl_inv`, `Work.BoseBogFS.bogLogQ_eq`). -/

/-- **The logarithmic form of `Kl d s / (μa³)^{1/2}`**: at FS's parameters the ratio is
`D^{-156/323}`, so its logarithm is `(156/323)log(1/D)`. -/
lemma bogLogQ_aux {v : E3 → ℝ} {μ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) :
    Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2))
      = ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ) := by
  have ha : 0 < _root_.BoseGases.a v := hav
  have hD : 0 < Work.BoseFixR.dil v μ := Work.BoseBogFS.dil_pos v hμ hav
  have harg : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2)
      = (Work.BoseFixR.dil v μ) ^ (-(156 / 323 : ℝ)) := by
    rw [Work.BoseBogFS.paramsAt_Kl, Work.BoseBogFS.paramsAt_d, Work.BoseBogFS.paramsAt_s]
    rw [show μ * (_root_.BoseGases.a v) ^ 3 = Work.BoseFixR.dil v μ from rfl]
    rw [← Real.rpow_add hD, ← Real.rpow_add hD, ← Real.rpow_sub hD]
    congr 1
    norm_num
  rw [harg, Real.log_rpow hD, one_div, Real.log_inv]
  ring

/-- **The logarithm of `√(ρa)·a` against `log(1/D)`**: from FS's lower bound
`ρ ≥ 9μ/10` one gets `1 - log(√(ρa)·a) ≤ 1 + 1/18 + ½log(1/D)` (the constant `1/18`
is sharp for the `9/10`). -/
lemma logSqrtBound_aux {v : E3 → ℝ} {ρ μ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) (hρlo : 9 / 10 * μ ≤ ρ) :
    1 - Real.log (Real.sqrt (ρ * _root_.BoseGases.a v) * _root_.BoseGases.a v)
      ≤ 1 + 1 / 18 + (1 / 2) * Real.log (1 / Work.BoseFixR.dil v μ) := by
  have ha : 0 < _root_.BoseGases.a v := hav
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hρlo
  have hD : 0 < Work.BoseFixR.dil v μ := Work.BoseBogFS.dil_pos v hμ hav
  have hsq : Real.sqrt (ρ * _root_.BoseGases.a v) * _root_.BoseGases.a v
      = Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3) := by
    have h := Real.sqrt_mul (x := ρ * _root_.BoseGases.a v) (by positivity)
      ((_root_.BoseGases.a v) ^ 2)
    rw [Real.sqrt_sq ha.le] at h
    rw [← h]
    congr 1
    ring
  have harg : (9 / 10) * Work.BoseFixR.dil v μ ≤ ρ * (_root_.BoseGases.a v) ^ 3 := by
    rw [Work.BoseFixR.dil]
    have h := mul_le_mul_of_nonneg_right hρlo (by positivity : (0 : ℝ) ≤ (_root_.BoseGases.a v) ^ 3)
    linarith
  have hpos : 0 < (9 / 10) * Work.BoseFixR.dil v μ := by positivity
  have hmono : Real.log (Real.sqrt ((9 / 10) * Work.BoseFixR.dil v μ))
      ≤ Real.log (Real.sqrt (ρ * (_root_.BoseGases.a v) ^ 3)) :=
    Real.log_le_log (Real.sqrt_pos.mpr hpos) (Real.sqrt_le_sqrt harg)
  rw [← hsq] at hmono
  have hlog1 : Real.log (Real.sqrt ((9 / 10) * Work.BoseFixR.dil v μ))
      = (1 / 2) * (Real.log (9 / 10) + Real.log (Work.BoseFixR.dil v μ)) := by
    rw [Real.log_sqrt hpos.le, Real.log_mul (by norm_num) (ne_of_gt hD)]
    ring
  rw [hlog1] at hmono
  have h109 : Real.log (9 / 10) = -Real.log (10 / 9) := by
    rw [← Real.log_inv]
    norm_num
  rw [h109] at hmono
  have hlog109 : Real.log (10 / 9) ≤ 1 / 9 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 9 by norm_num)
    linarith
  have hL : Real.log (1 / Work.BoseFixR.dil v μ) = -Real.log (Work.BoseFixR.dil v μ) := by
    rw [one_div, Real.log_inv]
  rw [hL]
  linarith

/-- **FS's error dominates its own `ε_T`-weighted fourth summand**: the `ε_T(K_ℓds)⁻¹`
term of `lhyEps` (with the logarithm) is bounded by the whole sum. -/
lemma lhyEps_ge_aux (a R eT Kl s d mu : ℝ)
    (ha : 0 < a) (hmu : 0 < mu) (_hR : 0 ≤ R) (hKl : 0 < Kl) (hs : 0 < s) (hd : 0 < d)
    (hd1 : d ≤ 1) (he0 : 0 ≤ eT)
    (hlog1 : 1 ≤ Kl * d * s / (mu * a ^ 3) ^ ((1 : ℝ) / 2)) :
    eT * (Kl * d * s)⁻¹ * (1 + Real.log (Kl * d * s / (mu * a ^ 3) ^ ((1 : ℝ) / 2)))
      ≤ Work.BoseB6.lhyEps a R eT Kl s d mu := by
  rw [Work.BoseB6.lhyEps]
  have hQ0 : 0 ≤ Real.log (Kl * d * s / (mu * a ^ 3) ^ ((1 : ℝ) / 2)) := Real.log_nonneg hlog1
  have hlogd : 0 ≤ Real.log d⁻¹ := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hd.le hd1)
  have hKls : 0 ≤ (Kl * s)⁻¹ := inv_nonneg.mpr (mul_pos hKl hs).le
  have hKlds : 0 ≤ (Kl * d * s)⁻¹ := inv_nonneg.mpr ((mul_pos (mul_pos hKl hd) hs)).le
  have h1 : 0 ≤ (mu * a) ^ ((1 : ℝ) / 4) * Real.sqrt R :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt (mul_pos hmu ha)) _) (Real.sqrt_nonneg R)
  have h3 : 0 ≤ (Kl * s)⁻¹ * (1 + Real.log d⁻¹
      + Real.log (Kl * d * s / (mu * a ^ 3) ^ ((1 : ℝ) / 2))) :=
    mul_nonneg hKls (by linarith)
  nlinarith [h1, h3, hQ0, he0, hKlds]

/-- `d ≤ 1` (with `d = D^{6/323}`) forces `D ≤ 1`. -/
lemma dil_le_one_of_d_le_one (v : E3 → ℝ) {μ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ)
    (hd1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1) :
    Work.BoseFixR.dil v μ ≤ 1 := by
  have hD : 0 < Work.BoseFixR.dil v μ := Work.BoseBogFS.dil_pos v hμ hav
  have h := hd1
  rw [Work.BoseBogFS.paramsAt_d] at h
  calc Work.BoseFixR.dil v μ = (Work.BoseFixR.dil v μ ^ ((6 : ℝ) / 323)) ^ ((323 : ℝ) / 6) := by
        rw [← Real.rpow_mul hD.le]
        norm_num
    _ ≤ (1 : ℝ) ^ ((323 : ℝ) / 6) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hD.le _) h (by norm_num)
    _ = 1 := Real.one_rpow _

theorem bogKappa_mul_log_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ρ μ : ℝ}
    (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v) (hρ : 0 < ρ)
    (hreg : Work.BoseB6Est.FsI1Regime (Work.BoseBogFS.bogKernel v R ρ μ)
      (_root_.BoseGases.a v) R ρ μ
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      (Work.BoseBogFS.bogC1 v ρ μ) (Work.BoseBogFS.bogC2 v ρ μ)
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) :
    Work.BoseBogFS.bogKappa v ρ μ
        * (1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v)
            * Work.BoseBogFS.bogT v R μ * _root_.BoseGases.a v)))
      ≤ 10 ^ 8 * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  set Kl := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl with hKl_eq
  set ss := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hs_eq
  set dd := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hd_eq
  set eT := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with heT_eq
  have hD : 0 < Work.BoseFixR.dil v μ := Work.BoseBogFS.dil_pos v hreg.hμ hav
  have hD1 : Work.BoseFixR.dil v μ ≤ 1 := dil_le_one_of_d_le_one v hav hreg.hμ hreg.hd1
  -- the momentum cutoff is at least `1`
  have hTge1 : 1 ≤ bogT v R μ := by
    have h := hreg.hT1
    rw [bogKernel_T] at h
    by_cases hc : bogT v R μ ≤ 0
    · rw [max_eq_left hc] at h
      linarith
    · rwa [max_eq_right (le_of_lt (not_le.mp hc))] at h
  have hTpos : 0 < bogT v R μ := lt_of_lt_of_le one_pos hTge1
  have hTn : 0 ≤ Real.log (bogT v R μ) := Real.log_nonneg hTge1
  -- the two cutoff monomials
  have hS : (Kl * ss)⁻¹ = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) := by
    rw [mul_comm Kl ss]
    exact Work.BoseBogFS.sKl_inv v μ hD
  have hTp : eT * (Kl * dd * ss)⁻¹ = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) := by
    rw [show Kl * dd * ss = dd * ss * Kl from by ring]
    exact Work.BoseBogFS.eT_dsKl_inv v μ hD
  have hkey : (Kl * ss)⁻¹ ≤ eT * (Kl * dd * ss)⁻¹ := by
    rw [hS, hTp]
    exact Real.rpow_le_rpow_of_exponent_ge hD hD1 (by norm_num)
  -- the two cutoffs
  have hV : Real.sqrt (μ / ρ) ≤ 2 := hreg.sqrt_mu_div_rhoz_le_two
  have hc1le : bogC1 v ρ μ ≤ (Kl * ss)⁻¹ := by
    rw [hreg.hc1val]
    have h0 : 0 ≤ (Kl * ss)⁻¹ := inv_nonneg.mpr (mul_pos hreg.hKl hreg.hs).le
    nlinarith [hV, h0, Real.sqrt_nonneg (μ / ρ)]
  have hc2le : bogC2 v ρ μ ≤ (Kl * dd * ss)⁻¹ := by
    rw [hreg.hc2val]
    have h0 : 0 ≤ (Kl * dd * ss)⁻¹ :=
      inv_nonneg.mpr ((mul_pos (mul_pos hreg.hKl hreg.hd) hreg.hs)).le
    nlinarith [hV, h0, Real.sqrt_nonneg (μ / ρ)]
  have hκeq : bogKappa v ρ μ = (1 - eT) * bogC1 v ρ μ + eT * bogC2 v ρ μ := by
    rw [bogKappa]
  have hκnn : 0 ≤ bogKappa v ρ μ := by
    rw [hκeq]
    have h2 : 0 ≤ bogC2 v ρ μ := le_trans hreg.hc1 hreg.hc12
    nlinarith [hreg.hc1, h2, hreg.hε0, hreg.hε1]
  have hκ2 : bogKappa v ρ μ ≤ 2 * (eT * (Kl * dd * ss)⁻¹) := by
    rw [hκeq]
    nlinarith [hc1le, hc2le, hkey, hreg.hc1, hreg.hε0, hreg.hε1, hreg.hc12]
  -- the error dominates the weighted fourth summand
  have hEge : eT * (Kl * dd * ss)⁻¹
        * (1 + Real.log (Kl * dd * ss / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2)))
      ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R eT Kl ss dd μ :=
    lhyEps_ge_aux (_root_.BoseGases.a v) R eT Kl ss dd μ hav hreg.hμ hR.le
      hreg.hKl hreg.hs hreg.hd hreg.hd1 hreg.hε0 hreg.hlog1
  have hEnn : 0 ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R eT Kl ss dd μ :=
    le_trans (by
      have h0 : 0 ≤ eT * (Kl * dd * ss)⁻¹ :=
        mul_nonneg hreg.hε0 (inv_nonneg.mpr ((mul_pos (mul_pos hreg.hKl hreg.hd) hreg.hs)).le)
      have h1 : 0 ≤ 1 + Real.log (Kl * dd * ss / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2)) :=
        by linarith [Real.log_nonneg hreg.hlog1]
      exact mul_nonneg h0 h1) hEge
  have hQnn : 0 ≤ Real.log (Kl * dd * ss / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2)) :=
    Real.log_nonneg hreg.hlog1
  have hTpnn : 0 ≤ eT * (Kl * dd * ss)⁻¹ :=
    mul_nonneg hreg.hε0 (inv_nonneg.mpr ((mul_pos (mul_pos hreg.hKl hreg.hd) hreg.hs)).le)
  have hLnn : 0 ≤ Real.log (1 / Work.BoseFixR.dil v μ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv₀ hD).mpr hD1)
  have hlogQrel : Real.log (1 / Work.BoseFixR.dil v μ)
      = ((323 : ℝ) / 156) * Real.log (Kl * dd * ss / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2)) := by
    have h := bogLogQ_aux (v := v) (μ := μ) hav hreg.hμ
    linarith
  have hsqrtb := logSqrtBound_aux (v := v) (ρ := ρ) (μ := μ) hav hreg.hμ hreg.hclose1
  -- the log of the argument of the target
  have hstep : 1 + Real.log (1 / (Real.sqrt (ρ * _root_.BoseGases.a v)
        * bogT v R μ * _root_.BoseGases.a v))
      = 1 - Real.log (Real.sqrt (ρ * _root_.BoseGases.a v) * _root_.BoseGases.a v)
        - Real.log (bogT v R μ) := by
    have hprod : Real.sqrt (ρ * _root_.BoseGases.a v) * bogT v R μ * _root_.BoseGases.a v
        = (Real.sqrt (ρ * _root_.BoseGases.a v) * _root_.BoseGases.a v) * bogT v R μ := by ring
    rw [hprod, one_div, Real.log_inv, Real.log_mul (by positivity) (ne_of_gt hTpos)]
    ring
  rw [hstep]
  calc bogKappa v ρ μ
        * (1 - Real.log (Real.sqrt (ρ * _root_.BoseGases.a v) * _root_.BoseGases.a v)
          - Real.log (bogT v R μ))
      ≤ bogKappa v ρ μ
        * (1 - Real.log (Real.sqrt (ρ * _root_.BoseGases.a v) * _root_.BoseGases.a v)) := by
        apply mul_le_mul_of_nonneg_left _ hκnn
        linarith [hTn]
    _ ≤ bogKappa v ρ μ * (1 + 1 / 18 + (1 / 2) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
        mul_le_mul_of_nonneg_left hsqrtb hκnn
    _ ≤ (2 * (eT * (Kl * dd * ss)⁻¹))
          * (1 + 1 / 18 + (1 / 2) * Real.log (1 / Work.BoseFixR.dil v μ)) :=
        mul_le_mul_of_nonneg_right hκ2 (by linarith [hLnn])
    _ = (2 * (eT * (Kl * dd * ss)⁻¹))
          * (1 + 1 / 18 + (1 / 2) * (((323 : ℝ) / 156)
              * Real.log (Kl * dd * ss / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2)))) := by
        rw [hlogQrel]
    _ ≤ ((19 : ℝ) / 9) * (eT * (Kl * dd * ss)⁻¹)
          * (1 + Real.log (Kl * dd * ss / (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2))) := by
        nlinarith [hTpnn, hQnn]
    _ ≤ ((19 : ℝ) / 9) * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R eT Kl ss dd μ := by
        nlinarith [hEge]
    _ ≤ 10 ^ 8 * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R eT Kl ss dd μ := by
        nlinarith [hEnn]

end Work.BoseBogFS
