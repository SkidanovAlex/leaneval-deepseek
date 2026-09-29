import Mathlib
import Submission.Work.Cert.ACBall.Basic
import Submission.Work.APsi.lune_cont_diff

/-! # Named pieces of `Work.Cert.luneStage` (v2)

The checker `luneStage` is one large `let`-expression; this file mirrors it as named definitions
(`lZ`, `lopz`, `lo2`, `lR`, `ls`, `lv`, `lRp`, `linvs`, `lvp`, the `M2`/radius data), proves the
bridge `luneStage_eq`, and records the *ball semantics* of the chain: each ball contains the
mathematical value it approximates (`lR` contains `luneR (36/5) (-c)`, `ls` contains its square
root, `lv` contains `lune (36/5) (-c)`, `lvp` contains the derivative `lune' (-c)`).

All statements are sorry-free; the only external inputs are the ball-operation soundness lemmas
`bmul_sound`/`binv_sound`/`bsqrt_sound` (see `Work.Cert.ball_ops`). -/

namespace Work.Cert.ACBall
open Work.Cert Complex Submission.CDTPlan

/-! ## Named pieces -/

/-- the ball for `−c` (`radius 0`). -/
def lZ (st : St) : Bl := ⟨-st.cr, -st.ci, 0⟩
/-- the ball for `1 − c`. -/
def lopz (st : St) : Bl := badd (bK S) (lZ st)
/-- the ball for `(1 − c)²`. -/
def lo2 (st : St) : Bl := bmul (lopz st) (lopz st)
/-- the ball for `luneR (36/5) (−c) = (1+c²)²(1−c)² − 16c²(−c)`. -/
def lR (st : St) : Bl := bsub (bmul (bK LB2) (lo2 st)) (bmul (bK K16) (lZ st))
/-- the ball `1/LD = 1/(2(c²−1))`, radius 1 ulp. -/
def lINVLD : Bl := ⟨fdiv (S * S) LD, 0, 1⟩
/-- the ball for `√(luneR (36/5) (−c))`. -/
def ls (st : St) (w : LuneW) : Bl := bsqrt (lR st) w.sr w.si
/-- the ball for `lune (36/5) (−c)`. -/
def lv (st : St) (w : LuneW) : Bl :=
  bmul (badd (bsub (bmul (bK LB) (lZ st)) (bK LB)) (ls st w)) lINVLD
/-- the ball for `R'(−c) = 2(1+c²)²(1−c) − 16c²`. -/
def lRp (st : St) : Bl := bsub (bmul (bK (2 * LB2)) (lopz st)) (bK K16)
/-- the ball for `1/√(luneR (36/5) (−c))`, from the witness `w.Ls`. -/
def linvs (st : St) (w : LuneW) : Bl := binv (ls st w) w.Ls
/-- the ball for `deriv (lune (36/5)) (−c)`. -/
def lvp (st : St) (w : LuneW) : Bl :=
  bmul (badd (bK LB) (bmul (bmul (lRp st) (linvs st w)) (bK (fdiv S 2)))) lINVLD
/-- the `okB` flag. -/
def lokB (st : St) (w : LuneW) : Bool := bsqrtOK (lR st) w.sr && binvOK (ls st w) w.Ls
/-- the `okM` flag. -/
def lokM (st : St) (w : LuneW) : Bool :=
  decide (0 ≤ w.D) && decide ((lvp st w).x * (lvp st w).x + (lvp st w).y * (lvp st w).y ≤ w.D * w.D) &&
    decide (0 ≤ w.zU) && decide (st.cr * st.cr + st.ci * st.ci ≤ w.zU * w.zU) &&
    decide (0 ≤ w.RU) && decide ((lR st).x * (lR st).x + (lR st).y * (lR st).y ≤ w.RU * w.RU) &&
    decide (0 ≤ w.RL) && decide (w.RL * w.RL ≤ (lR st).x * (lR st).x + (lR st).y * (lR st).y) &&
    decide (0 ≤ w.rpU) &&
      decide ((lRp st).x * (lRp st).x + (lRp st).y * (lRp st).y ≤ w.rpU * w.rpU)
/-- the mantissa of `|R''| = 2(1+c²)²`. -/
def lRpp : Int := 2 * LB2
/-- the upper mantissa of `sup |R'|` on the input disc. -/
def lRpD (st : St) (w : LuneW) : Int := w.rpU + (lRp st).r + mu st.rho lRpp + 1
/-- the upper mantissa of `sup |R|` on the input disc. -/
def lRhi (st : St) (w : LuneW) : Int := w.RU + (lR st).r + mu st.rho (lRpD st w) + 1
/-- the lower mantissa of `inf |R|` on the input disc. -/
def lRlo (st : St) (w : LuneW) : Int := w.RL - (lR st).r - mu st.rho (lRpD st w) - 1
/-- whether the explicit (`M2e`) branch is used. -/
def luseE (st : St) (w : LuneW) : Bool := decide (0 < lRlo st w)
/-- the `okW` flag. -/
def lokW (st : St) (w : LuneW) : Bool :=
  !(luseE st w) || (decide (0 < w.sL) && decide (w.sL * w.sL ≤ lRlo st w * S))
/-- numerator of the explicit second-derivative bound. -/
def lnum (st : St) (w : LuneW) : Int := mu (2 * lRhi st w) lRpp + mu (lRpD st w) (lRpD st w)
/-- denominator of the explicit second-derivative bound. -/
def ldd (st : St) (w : LuneW) : Int := md (md L8 (lRlo st w)) w.sL
/-- the explicit second-derivative mantissa. -/
def lM2e (st : St) (w : LuneW) : Int :=
  if luseE st w && decide (0 < ldd st w) then dvu (lnum st w) (ldd st w) else INF
/-- the mantissa `S − zU − ρ − 1`. -/
def ld (st : St) (w : LuneW) : Int := S - w.zU - st.rho - 1
/-- `⌊d²/S⌋`. -/
def ldsq (st : St) (w : LuneW) : Int := md (ld st w) (ld st w)
/-- the Cauchy second-derivative mantissa. -/
def lM2c (st : St) (w : LuneW) : Int :=
  if decide (0 < ld st w) && decide (0 < ldsq st w) then dvu (2 * S) (ldsq st w) else INF
/-- the second-derivative mantissa `M2 = min M2e M2c`. -/
def lM2 (st : St) (w : LuneW) : Int := imin (lM2e st w) (lM2c st w)
/-- the output radius mantissa `⌈ρ(D + vp.r)⌉ + ⌈⌈ρ²⌉M2/2⌉ + v.r + 1`. -/
def lrho2 (st : St) (w : LuneW) : Int :=
  mu st.rho (w.D + (lvp st w).r) + chalf (mu (mu st.rho st.rho) (lM2 st w)) + (lv st w).r + 1

set_option maxHeartbeats 1000000 in
/-- The bridge: `luneStage` is the ball chain above. -/
theorem luneStage_eq (st : St) (w : LuneW) :
    luneStage st w =
      ⟨st.ok && lokB st w && lokM st w && lokW st w && decide (w.zU + st.rho + 1 < S) &&
          decide (lM2 st w < INF) && decide (0 ≤ st.rho) && decide (0 ≤ lrho2 st w),
        (lv st w).x, (lv st w).y, lrho2 st w⟩ := rfl

theorem luneStage_cr (st : St) (w : LuneW) : (luneStage st w).cr = (lv st w).x := by
  rw [luneStage_eq]
theorem luneStage_ci (st : St) (w : LuneW) : (luneStage st w).ci = (lv st w).y := by
  rw [luneStage_eq]
theorem luneStage_rho (st : St) (w : LuneW) : (luneStage st w).rho = lrho2 st w := by
  rw [luneStage_eq]

/-- The `ok` flag of `luneStage`, split into its eight conjuncts. -/
theorem luneStage_ok_spec (st : St) (w : LuneW) (h : (luneStage st w).ok = true) :
    st.ok = true ∧ lokB st w = true ∧ lokM st w = true ∧ lokW st w = true ∧
      (w.zU + st.rho + 1 < S) ∧ lM2 st w < INF ∧ 0 ≤ st.rho ∧ 0 ≤ lrho2 st w := by
  rw [luneStage_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2,
    h.1.2, h.2⟩

/-! ## `cx` arithmetic helpers -/

lemma cx_neg (x y : ℤ) : cx (-x) (-y) = -cx x y := by
  simp only [cx]; push_cast; ring

end Work.Cert.ACBall
