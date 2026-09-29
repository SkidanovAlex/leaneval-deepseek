import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.Cert.All
import Submission.Work.CNum.LgUpSpec
import Submission.Work.CNum.LogUpMSpec
import Submission.Work.CNum.LgInfra

/-!
# `Work.CNum.TabCert` — the tabulated numeric certificate

The certificate of `Fx` (`Gv`, `gv`, `certOK`) evaluates the `44`-term series `serUp`/`serDn` at
every grid point; that kernel evaluation is expensive.  Here we replace it by the tabulated values
of `Cert.All` (`svUpTab`, `svDnTab`, `svUpCA`, …), obtaining the same bounds `GvT k = Gv k` and
`gvT k = gv k` (provable by rewriting with the tabulation) whose arithmetic is cheap for the kernel.

The final numeric facts are

* `pairSumT * 10 ≤ 102 * 1024 * 1024 * SC` (the rearrangement sum),
* `GvT k ≤ LOG7E5DN` for all `k < 1024`,  where `LOG7E5DN = lgDn 7SC + 5 lgDn 10SC ≤ log 700000`,
* `LOG1E13LB ≤ gvT k` for all `k < 1024`, where `LOG1E13LB = -13 lgDn 10SC ≤ log 10⁻¹³`.
-/

namespace Work.CNum

open Work.ANum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! ## The tabulated `Gv`, `gv` -/

/-- `Fx`'s `Gv` with the series values replaced by the tabulation. -/
def GvT (k : ℕ) : ℤ :=
  if k ≤ 243 then
    max (svUpTab k) (svUpTab (k + 1)) + chord1 (dWup (ptOf k) (ptOf (k + 1)))
  else if k = 244 then
    max (max (svUpTab 244) svUpCA) (max (svUpTab 245) svUpCA)
      + max (chord1 (dWup (ptOf 244) ptCuspA)) (chord2 (dVup (ptOf 245) ptCuspA))
  else if k ≤ 778 then
    max (svUpTab k) (svUpTab (k + 1)) + chord2 (dVup (ptOf k) (ptOf (k + 1)))
  else if k = 779 then
    max (max (svUpTab 779) svUpCB) (max (svUpTab 780) svUpCB)
      + max (chord2 (dVup (ptOf 779) ptCuspB)) (chord1 (dWup (ptOf 780) ptCuspB))
  else
    max (svUpTab k) (svUpTab (k + 1)) + chord1 (dWup (ptOf k) (ptOf (k + 1)))

/-- `Fx`'s `gv` with the series values replaced by the tabulation. -/
def gvT (k : ℕ) : ℤ :=
  if k ≤ 243 then
    min (svDnTab k) (svDnTab (k + 1)) - chord1 (dWup (ptOf k) (ptOf (k + 1)))
  else if k = 244 then
    min (min (svDnTab 244) svDnCA) (min (svDnTab 245) svDnCA)
      - max (chord1 (dWup (ptOf 244) ptCuspA)) (chord2 (dVup (ptOf 245) ptCuspA))
  else if k ≤ 778 then
    min (svDnTab k) (svDnTab (k + 1)) - chord2 (dVup (ptOf k) (ptOf (k + 1)))
  else if k = 779 then
    min (min (svDnTab 779) svDnCB) (min (svDnTab 780) svDnCB)
      - max (chord2 (dVup (ptOf 779) ptCuspB)) (chord1 (dWup (ptOf 780) ptCuspB))
  else
    min (svDnTab k) (svDnTab (k + 1)) - chord1 (dWup (ptOf k) (ptOf (k + 1)))

theorem Gv_eq_T (k : ℕ) (hk : k < 1024) : Gv k = GvT k := by
  have h1 : svUp (ptOf k) = svUpTab k := svUpTab_spec k (by omega)
  have h2 : svUp (ptOf (k + 1)) = svUpTab (k + 1) := svUpTab_spec (k + 1) (by omega)
  have h3 : svUp (ptOf 244) = svUpTab 244 := svUpTab_spec 244 (by norm_num)
  have h4 : svUp (ptOf 245) = svUpTab 245 := svUpTab_spec 245 (by norm_num)
  have h5 : svUp (ptOf 779) = svUpTab 779 := svUpTab_spec 779 (by norm_num)
  have h6 : svUp (ptOf 780) = svUpTab 780 := svUpTab_spec 780 (by norm_num)
  simp only [Gv, GvT, h1, h2, h3, h4, h5, h6, svUpCA_spec, svUpCB_spec]

theorem gv_eq_T (k : ℕ) (hk : k < 1024) : gv k = gvT k := by
  have h1 : svDn (ptOf k) = svDnTab k := svDnTab_spec k (by omega)
  have h2 : svDn (ptOf (k + 1)) = svDnTab (k + 1) := svDnTab_spec (k + 1) (by omega)
  have h3 : svDn (ptOf 244) = svDnTab 244 := svDnTab_spec 244 (by norm_num)
  have h4 : svDn (ptOf 245) = svDnTab 245 := svDnTab_spec 245 (by norm_num)
  have h5 : svDn (ptOf 779) = svDnTab 779 := svDnTab_spec 779 (by norm_num)
  have h6 : svDn (ptOf 780) = svDnTab 780 := svDnTab_spec 780 (by norm_num)
  simp only [gv, gvT, h1, h2, h3, h4, h5, h6, svDnCA_spec, svDnCB_spec]

/-! ## The numeric certificates -/

/-- `log 700000` from below. -/
def LOG7E5DN : ℤ := lgDn (7 * SC) + 5 * lgDn (10 * SC)

/-- `log 10⁻¹³` from below. -/
def LOG1E13LB : ℤ := -(13 * lgDn (10 * SC))

/-- The list of tabulated arc bounds. -/
def gvTabL : List ℤ := (List.range 1024).map GvT

/-- `Σ_{k,k'} max (GvT k) (GvT k')` (mantissas). -/
def pairSumT : ℤ :=
  let l := gvTabL
  l.foldl (fun acc x => l.foldl (fun a y => a + max x y) acc) 0

theorem all_range_iff {N : ℕ} {p : ℕ → Prop} [DecidablePred p] :
    (List.range N).all (fun k => decide (p k)) = true ↔ ∀ k < N, p k := by
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    exact of_decide_eq_true (h k (List.mem_range.mpr hk))
  · intro h k hk
    exact decide_eq_true (h k (List.mem_range.mp hk))

theorem m2r_LOG7E5DN : m2r LOG7E5DN ≤ Real.log 700000 := by
  have h1 : m2r (lgDn (7 * SC)) ≤ Real.log (m2r (7 * SC)) :=
    lgDn_spec (by norm_num [SC]) (by norm_num [SC])
  have h2 : m2r (lgDn (10 * SC)) ≤ Real.log (m2r (10 * SC)) :=
    lgDn_spec (by norm_num [SC]) (by norm_num [SC])
  have h7 : m2r (7 * SC) = 7 := by rw [m2r_mul_SC']; norm_num
  have h10 : m2r (10 * SC) = 10 := by rw [m2r_mul_SC']; norm_num
  have h1' : m2r (lgDn (7 * SC)) ≤ Real.log 7 := h7 ▸ h1
  have h2' : m2r (lgDn (10 * SC)) ≤ Real.log 10 := h10 ▸ h2
  have hlog : Real.log 700000 = Real.log 7 + 5 * Real.log 10 := by
    rw [show (700000:ℝ) = 7 * 10 ^ 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have hsplit : m2r (lgDn (7 * SC) + 5 * lgDn (10 * SC))
      = m2r (lgDn (7 * SC)) + 5 * m2r (lgDn (10 * SC)) := by
    rw [m2r_add]
    have : m2r (5 * lgDn (10 * SC)) = 5 * m2r (lgDn (10 * SC)) := by
      simp only [m2r]; push_cast; ring
    rw [this]
  rw [LOG7E5DN, hsplit, hlog]
  linarith

theorem m2r_LOG1E13LB : Real.log (1 / 10 ^ 13) ≤ m2r LOG1E13LB := by
  have h2 : m2r (lgDn (10 * SC)) ≤ Real.log (m2r (10 * SC)) :=
    lgDn_spec (by norm_num [SC]) (by norm_num [SC])
  have h10 : m2r (10 * SC) = 10 := by rw [m2r_mul_SC']; norm_num
  have h2' : m2r (lgDn (10 * SC)) ≤ Real.log 10 := h10 ▸ h2
  have hlog : Real.log (1 / 10 ^ 13) = -(13 * Real.log 10) := by
    rw [one_div, Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hsplit : m2r (-(13 * lgDn (10 * SC))) = -(13 * m2r (lgDn (10 * SC))) := by
    rw [m2r_neg]
    have : m2r (13 * lgDn (10 * SC)) = 13 * m2r (lgDn (10 * SC)) := by
      simp only [m2r]; push_cast; ring
    rw [this]
  rw [LOG1E13LB, hsplit, hlog]
  linarith

end Work.CNum
