import Mathlib
import Submission.Work.Cert.ACBall.Basic

/-!
# Named pieces of `Work.Cert.slitStage` (v3)

The checker `Work.Cert.slitStage` is one large `let`-expression; this file mirrors it as named
definitions with the *uniform* parameter list `(A B2 E C1 G8 A2 ror roi : Int) (st : St)
(w : SlitW)` (unused parameters are simply ignored), proves the bridge `slitStage_eq`, and exposes
the `ok` flag as eight conjuncts.

The mathematical meaning of the chain (proved in the sibling module `ACSlit.Chain`) is
`su ∋ rot t · slit r c` and `sfp ∋ rot t · deriv (slit r) c` for the centre `c = cIn st`.
-/

namespace Work.Cert.ACSlit
open Work.Cert Complex Submission.CDTPlan
open Work.Cert.ACBall

/-- the input centre `c = (cr + ci i)/S`. -/
noncomputable def cIn (st : St) : ℂ := cx st.cr st.ci

/-! ## Named pieces -/

/-- the ball for `c`, radius 0. -/
def sC (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl := ⟨st.cr, st.ci, 0⟩
/-- the ball for `c²`. -/
def sc2 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl := bmul (sC A B2 E C1 G8 A2 ror roi st w) (sC A B2 E C1 G8 A2 ror roi st w)
/-- the ball for `Q(c) = (1+r)² − 2(1−6r+r²)c + (1+r)²c²`. -/
def sQ (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  badd (bsub (bmul (bK A) (sc2 A B2 E C1 G8 A2 ror roi st w))
      (bmul (bK B2) (sC A B2 E C1 G8 A2 ror roi st w))) (bK A)
/-- the ball for `√(Q(c))`. -/
def ss (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  bsqrt (sQ A B2 E C1 G8 A2 ror roi st w) w.sr w.si
/-- the ball for `c − 1`. -/
def scm1 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl := ⟨st.cr - S, st.ci, 0⟩
/-- the ball for the numerator `N(c) = (1+r)² − 2(r−1)²c + (1+r)²c² + (1+r)(c−1)√(Q(c))`. -/
def sN (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  badd (badd (bsub (bK A) (bmul (bK E) (sC A B2 E C1 G8 A2 ror roi st w)))
      (bmul (bK A) (sc2 A B2 E C1 G8 A2 ror roi st w)))
    (bmul (bK C1) (bmul (scm1 A B2 E C1 G8 A2 ror roi st w) (ss A B2 E C1 G8 A2 ror roi st w)))
/-- the ball for `8 r c`. -/
def sden (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl := bmul (bK G8) (sC A B2 E C1 G8 A2 ror roi st w)
/-- the ball for `1/(8 r c)`, from the witness `w.L1`. -/
def sinv1 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl := binv (sden A B2 E C1 G8 A2 ror roi st w) w.L1
/-- the ball for `slit r c = N(c)/(8 r c)`. -/
def sv (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  bmul (sN A B2 E C1 G8 A2 ror roi st w) (sinv1 A B2 E C1 G8 A2 ror roi st w)
/-- the ball for the rotation constant `rot t` (radius 2 ulp). -/
def sRO (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl := ⟨ror, roi, 2⟩
/-- the ball for `rot t · slit r c`. -/
def su (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  bmul (sRO A B2 E C1 G8 A2 ror roi st w) (sv A B2 E C1 G8 A2 ror roi st w)
/-- the ball for `Q'(c) = 2(1+r)²c − 2(1−6r+r²)`. -/
def sQp (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  bsub (bmul (bK A2) (sC A B2 E C1 G8 A2 ror roi st w)) (bK B2)
/-- the ball for `1/√(Q(c))`, from the witness `w.Ls`. -/
def sinvs (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  binv (ss A B2 E C1 G8 A2 ror roi st w) w.Ls
/-- the ball for `Q'(c)/(2√(Q(c)))`. -/
def sqos (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  bmul (bmul (sQp A B2 E C1 G8 A2 ror roi st w) (sinvs A B2 E C1 G8 A2 ror roi st w)) (bK (fdiv S 2))
/-- the ball for `N'(c) = −2(r−1)² + 2(1+r)²c + (1+r)√(Q(c)) + (1+r)(c−1)Q'(c)/(2√(Q(c)))`. -/
def sNp (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  badd (badd (bsub (bmul (bK A2) (sC A B2 E C1 G8 A2 ror roi st w)) (bK E))
      (bmul (bK C1) (ss A B2 E C1 G8 A2 ror roi st w)))
    (bmul (bK C1) (bmul (scm1 A B2 E C1 G8 A2 ror roi st w) (sqos A B2 E C1 G8 A2 ror roi st w)))
/-- the ball for `N'(c)·c − N(c)`. -/
def sdn (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  bsub (bmul (sNp A B2 E C1 G8 A2 ror roi st w) (sC A B2 E C1 G8 A2 ror roi st w))
    (sN A B2 E C1 G8 A2 ror roi st w)
/-- the ball for `1/c`, from the witness `w.cL`. -/
def sinvc (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl := binv (sC A B2 E C1 G8 A2 ror roi st w) w.cL
/-- the ball for `rot t · (N'(c)c − N(c))/(8 r c²)`. -/
def sfp (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bl :=
  bmul (sRO A B2 E C1 G8 A2 ror roi st w)
    (bmul (bmul (sdn A B2 E C1 G8 A2 ror roi st w) (sinv1 A B2 E C1 G8 A2 ror roi st w)) (sinvc A B2 E C1 G8 A2 ror roi st w))

/-! ## The flags and the radius data -/

/-- the `okB` flag. -/
def sokB (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bool :=
  bsqrtOK (sQ A B2 E C1 G8 A2 ror roi st w) w.sr && binvOK (sden A B2 E C1 G8 A2 ror roi st w) w.L1 &&
    binvOK (ss A B2 E C1 G8 A2 ror roi st w) w.Ls && binvOK (sC A B2 E C1 G8 A2 ror roi st w) w.cL

/-- the `okM` flag. -/
def sokM (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bool :=
  decide (0 ≤ w.D) &&
    decide ((sfp A B2 E C1 G8 A2 ror roi st w).x * (sfp A B2 E C1 G8 A2 ror roi st w).x
        + (sfp A B2 E C1 G8 A2 ror roi st w).y * (sfp A B2 E C1 G8 A2 ror roi st w).y ≤ w.D * w.D) &&
    decide (0 ≤ w.cU) && decide (st.cr * st.cr + st.ci * st.ci ≤ w.cU * w.cU) &&
    decide (0 ≤ w.qU) &&
      decide ((sQ A B2 E C1 G8 A2 ror roi st w).x * (sQ A B2 E C1 G8 A2 ror roi st w).x
        + (sQ A B2 E C1 G8 A2 ror roi st w).y * (sQ A B2 E C1 G8 A2 ror roi st w).y ≤ w.qU * w.qU) &&
    decide (0 ≤ w.qL) &&
      decide (w.qL * w.qL ≤ (sQ A B2 E C1 G8 A2 ror roi st w).x * (sQ A B2 E C1 G8 A2 ror roi st w).x
        + (sQ A B2 E C1 G8 A2 ror roi st w).y * (sQ A B2 E C1 G8 A2 ror roi st w).y) &&
    decide (0 ≤ w.qpU) &&
      decide ((sQp A B2 E C1 G8 A2 ror roi st w).x * (sQp A B2 E C1 G8 A2 ror roi st w).x
        + (sQp A B2 E C1 G8 A2 ror roi st w).y * (sQp A B2 E C1 G8 A2 ror roi st w).y
        ≤ w.qpU * w.qpU) &&
    decide (0 ≤ w.m1U) &&
      decide ((st.cr - S) * (st.cr - S) + st.ci * st.ci ≤ w.m1U * w.m1U)

/-- upper mantissa of `S·|w|` on the input disc. -/
def swhi (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int := w.cU + st.rho + 1
/-- lower mantissa of `S·|w|` on the input disc. -/
def swlo (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int := w.cL - st.rho - 1
/-- upper mantissa of `S·sup|Q'|` on the input disc. -/
def sQpD (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  w.qpU + (sQp A B2 E C1 G8 A2 ror roi st w).r + mu st.rho A2 + 1
/-- upper mantissa of `S·sup|Q|` on the input disc. -/
def sQhi (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  w.qU + (sQ A B2 E C1 G8 A2 ror roi st w).r + mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) + 1
/-- lower mantissa of `S·inf|Q|` on the input disc. -/
def sQlo (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  w.qL - (sQ A B2 E C1 G8 A2 ror roi st w).r - mu st.rho (sQpD A B2 E C1 G8 A2 ror roi st w) - 1
/-- whether the explicit (`M2e`) branch may be used. -/
def suseE (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bool :=
  decide (0 < sQlo A B2 E C1 G8 A2 ror roi st w) && decide (0 < swlo A B2 E C1 G8 A2 ror roi st w)
/-- the `okW` flag. -/
def sokW (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Bool :=
  !(suseE A B2 E C1 G8 A2 ror roi st w) ||
    (decide (0 < w.sL) && decide (w.sL * w.sL ≤ sQlo A B2 E C1 G8 A2 ror roi st w * S) &&
      decide (0 ≤ w.sH) && decide (sQhi A B2 E C1 G8 A2 ror roi st w * S ≤ w.sH * w.sH))
/-- upper mantissa of `S·|w−1|` on the input disc. -/
def swm1 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int := w.m1U + st.rho + 1
/-- numerator of the explicit second-derivative bound: bound for `S·|N|`. -/
def sN0 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  A + mu E (swhi A B2 E C1 G8 A2 ror roi st w) +
    mu A (mu (swhi A B2 E C1 G8 A2 ror roi st w) (swhi A B2 E C1 G8 A2 ror roi st w)) +
    mu (mu C1 (swm1 A B2 E C1 G8 A2 ror roi st w)) w.sH
/-- bound for `S·|N'|`. -/
def sN1 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  E + mu A2 (swhi A B2 E C1 G8 A2 ror roi st w) + mu C1 w.sH +
    dvu (mu (mu C1 (swm1 A B2 E C1 G8 A2 ror roi st w))
      (sQpD A B2 E C1 G8 A2 ror roi st w)) (2 * w.sL)
/-- the intermediate product of the `1/Slo³` term. -/
def sx (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  mu (mu (2 * sQhi A B2 E C1 G8 A2 ror roi st w) A2 +
      mu (sQpD A B2 E C1 G8 A2 ror roi st w) (sQpD A B2 E C1 G8 A2 ror roi st w))
    (mu C1 (swm1 A B2 E C1 G8 A2 ror roi st w))
/-- bound for `S·|N''|`. -/
def sN2 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  A2 + dvu (mu C1 (sQpD A B2 E C1 G8 A2 ror roi st w)) w.sL +
    dvu (dvu (dvu (sx A B2 E C1 G8 A2 ror roi st w) w.sL) w.sL) (4 * w.sL)
/-- numerator of the explicit second-derivative bound. -/
def snum (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  mu (sN2 A B2 E C1 G8 A2 ror roi st w)
      (mu (swhi A B2 E C1 G8 A2 ror roi st w) (swhi A B2 E C1 G8 A2 ror roi st w)) +
    2 * mu (sN1 A B2 E C1 G8 A2 ror roi st w) (swhi A B2 E C1 G8 A2 ror roi st w) +
    2 * sN0 A B2 E C1 G8 A2 ror roi st w
/-- denominator of the explicit second-derivative bound: bound for `S³·8r|w|³`. -/
def sdd (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  md G8 (md (md (swlo A B2 E C1 G8 A2 ror roi st w) (swlo A B2 E C1 G8 A2 ror roi st w))
    (swlo A B2 E C1 G8 A2 ror roi st w))
/-- the explicit second-derivative mantissa. -/
def sM2e (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  if suseE A B2 E C1 G8 A2 ror roi st w && decide (0 < sdd A B2 E C1 G8 A2 ror roi st w) then
    dvu (snum A B2 E C1 G8 A2 ror roi st w) (sdd A B2 E C1 G8 A2 ror roi st w)
  else INF
/-- the mantissa `S − cU − ρ − 1`. -/
def sd (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int := S - w.cU - st.rho - 1
/-- `⌊d²/S⌋`. -/
def sdsq (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  md (sd A B2 E C1 G8 A2 ror roi st w) (sd A B2 E C1 G8 A2 ror roi st w)
/-- the Cauchy second-derivative mantissa. -/
def sM2c (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  if decide (0 < sd A B2 E C1 G8 A2 ror roi st w) &&
      decide (0 < sdsq A B2 E C1 G8 A2 ror roi st w) then
    dvu (2 * S) (sdsq A B2 E C1 G8 A2 ror roi st w)
  else INF
/-- the second-derivative mantissa `M2 = min M2e M2c`. -/
def sM2 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  imin (sM2e A B2 E C1 G8 A2 ror roi st w) (sM2c A B2 E C1 G8 A2 ror roi st w)
/-- the output radius mantissa `⌈ρ(D + fp.r)⌉ + ⌈⌈ρ²⌉M2/2⌉ + u.r + 1`. -/
def srho2 (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) : Int :=
  mu st.rho (w.D + (sfp A B2 E C1 G8 A2 ror roi st w).r) +
    chalf (mu (mu st.rho st.rho) (sM2 A B2 E C1 G8 A2 ror roi st w)) +
    (su A B2 E C1 G8 A2 ror roi st w).r + 1

/-- The bridge: `slitStage` is the ball chain above. -/
theorem slitStage_eq (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) :
    slitStage A B2 E C1 G8 A2 ror roi st w =
      ⟨st.ok && sokB A B2 E C1 G8 A2 ror roi st w && sokM A B2 E C1 G8 A2 ror roi st w &&
        sokW A B2 E C1 G8 A2 ror roi st w && decide (swhi A B2 E C1 G8 A2 ror roi st w < S) &&
        decide (sM2 A B2 E C1 G8 A2 ror roi st w < INF) && decide (0 ≤ st.rho) &&
        decide (0 ≤ srho2 A B2 E C1 G8 A2 ror roi st w),
        (su A B2 E C1 G8 A2 ror roi st w).x,
        (su A B2 E C1 G8 A2 ror roi st w).y,
        srho2 A B2 E C1 G8 A2 ror roi st w⟩ := rfl

theorem slitStage_cr (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) :
    (slitStage A B2 E C1 G8 A2 ror roi st w).cr = (su A B2 E C1 G8 A2 ror roi st w).x := by
  rw [slitStage_eq]

theorem slitStage_ci (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) :
    (slitStage A B2 E C1 G8 A2 ror roi st w).ci = (su A B2 E C1 G8 A2 ror roi st w).y := by
  rw [slitStage_eq]

theorem slitStage_rho (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW) :
    (slitStage A B2 E C1 G8 A2 ror roi st w).rho = srho2 A B2 E C1 G8 A2 ror roi st w := by
  rw [slitStage_eq]

/-- The `ok` flag of `slitStage`, split into its eight conjuncts. -/
theorem slitStage_ok_spec (A B2 E C1 G8 A2 ror roi : Int) (st : St) (w : SlitW)
    (h : (slitStage A B2 E C1 G8 A2 ror roi st w).ok = true) :
    st.ok = true ∧ sokB A B2 E C1 G8 A2 ror roi st w = true ∧
      sokM A B2 E C1 G8 A2 ror roi st w = true ∧ sokW A B2 E C1 G8 A2 ror roi st w = true ∧
      swhi A B2 E C1 G8 A2 ror roi st w < S ∧ sM2 A B2 E C1 G8 A2 ror roi st w < INF ∧
      0 ≤ st.rho ∧ 0 ≤ srho2 A B2 E C1 G8 A2 ror roi st w := by
  rw [slitStage_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto

end Work.Cert.ACSlit
