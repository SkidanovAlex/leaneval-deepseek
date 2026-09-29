import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Cert.LeafAux

/-! # Named pieces of the winding leaf check `gDisc`

`Work.Cert.gDisc` (in `Submission/Work/Cert/WindDefs.lean`) computes, for a leaf `L` and a witness
`bU`, a disc `(gr, gi, rg)` of mantissas at scale `S` that contains

  `g(q) = h(q) + 1/72 = -256·q·(A(q)/B(q))^8 + 1/72`,   `q = ψ_A(z)`,

for `z` in the leaf disc; `windLeafOK lab L bU = true` then asserts `rg < Re(cx gr gi · conj(I^lab))`.

This file names, *as functions of the parameters* `(qr, qi, rq, mU, aU, bL, bU)` rather than of `L`,
each intermediate quantity of `gDisc`: the ratio mantissas `gxr, gxi`, their radius `grx`, the disc
`gy` of `X^8`, the mantissas `gpr, gpi` of `q·X^8`, the centre `(ggr, ggi)` of `g` and its radius
`grg`.  The `rfl` lemmas `gDisc_gr/gi/rg` identify them with the components of `gDisc`.

The θ-side quantities `Acell`, `Bcell`, `tailAZ`, `tailBZ` (and the stage chain `stage0 … stage5`,
`qrZ`, `qiZ`, `rqZ`) come from `Submission/Work/Cert/LeafAux.lean`.
-/
set_option maxRecDepth 100000
namespace Work.Cert
namespace WL

open Complex

/-! ## The parameterized quantities -/

/-- `⌊|B_centre|²/S⌋`, the denominator of the ratio `a/b`. -/
def gb2 (qr qi rq mU : ℤ) : ℤ :=
  fdiv ((Bcell qr qi rq (mU + rq + 1)).Br * (Bcell qr qi rq (mU + rq + 1)).Br +
      (Bcell qr qi rq (mU + rq + 1)).Bi * (Bcell qr qi rq (mU + rq + 1)).Bi) S

/-- The real part of the ratio `a/b`, a mantissa at scale `S`. -/
def gxr (qr qi rq mU : ℤ) : ℤ :=
  fdiv ((Acell qr qi rq (mU + rq + 1)).Ar * (Bcell qr qi rq (mU + rq + 1)).Br +
      (Acell qr qi rq (mU + rq + 1)).Ai * (Bcell qr qi rq (mU + rq + 1)).Bi) (gb2 qr qi rq mU)

/-- The imaginary part of the ratio `a/b`, a mantissa at scale `S`. -/
def gxi (qr qi rq mU : ℤ) : ℤ :=
  fdiv ((Acell qr qi rq (mU + rq + 1)).Ai * (Bcell qr qi rq (mU + rq + 1)).Br -
      (Acell qr qi rq (mU + rq + 1)).Ar * (Bcell qr qi rq (mU + rq + 1)).Bi) (gb2 qr qi rq mU)

/-- The radius mantissa `eA` of the disc of `A(q)`. -/
def gAup (qr qi rq mU : ℤ) : ℤ := (Acell qr qi rq (mU + rq + 1)).dA + tailAZ qr qi rq (mU + rq + 1)

/-- The radius mantissa `eB` of the disc of `B(q)`. -/
def gBup (qr qi rq mU : ℤ) : ℤ := (Bcell qr qi rq (mU + rq + 1)).dB + tailBZ qr qi rq (mU + rq + 1)

/-- The lower bound `bL - eB` for `|B(q)|`. -/
def gBlo (qr qi rq mU bL : ℤ) : ℤ := bL - gBup qr qi rq mU

/-- The radius mantissa of the disc of the ratio `X = A(q)/B(q)`. -/
def grx (qr qi rq mU aU bL bU : ℤ) : ℤ :=
  dvu (mu (gAup qr qi rq mU) bU + mu aU (gBup qr qi rq mU)) (md bL (gBlo qr qi rq mU bL)) +
    2 * fdiv (iabs (gxr qr qi rq mU) + iabs (gxi qr qi rq mU) + 2) (gb2 qr qi rq mU) + 4 + ETOL

/-- The disc (mantissa centre and radius) of `X^8 = (A(q)/B(q))^8`. -/
def gy (qr qi rq mU aU bL bU : ℤ) : ℤ × ℤ × ℤ :=
  sqD (sqD (sqD (gxr qr qi rq mU, gxi qr qi rq mU, grx qr qi rq mU aU bL bU)))

/-- The real part of the centre `q·X^8`. -/
def gpr (qr qi rq mU aU bL bU : ℤ) : ℤ :=
  cmr qr qi (gy qr qi rq mU aU bL bU).1 (gy qr qi rq mU aU bL bU).2.1

/-- The imaginary part of the centre `q·X^8`. -/
def gpi (qr qi rq mU aU bL bU : ℤ) : ℤ :=
  cmi qr qi (gy qr qi rq mU aU bL bU).1 (gy qr qi rq mU aU bL bU).2.1

/-- The real part of the centre of `g = h + 1/72 = -256·q·X^8 + 1/72`. -/
def ggr (qr qi rq mU aU bL bU : ℤ) : ℤ := -256 * gpr qr qi rq mU aU bL bU + fdiv S 72

/-- The imaginary part of the centre of `g`. -/
def ggi (qr qi rq mU aU bL bU : ℤ) : ℤ := -256 * gpi qr qi rq mU aU bL bU

/-- The radius mantissa of the disc of `g`. -/
def grg (qr qi rq mU aU bL bU : ℤ) : ℤ :=
  256 * (mu (iabs qr + iabs qi) (gy qr qi rq mU aU bL bU).2.2 +
      mu (iabs (gy qr qi rq mU aU bL bU).1 + iabs (gy qr qi rq mU aU bL bU).2.1) rq +
      mu rq (gy qr qi rq mU aU bL bU).2.2) + ETOL + ETOL

/-! ## The identification with `gDisc` -/

/-- The real part of the centre of `g` in `gDisc`. -/
theorem gDisc_gr (L : Leaf) (bU : ℤ) :
    (gDisc L bU).2.1 = ggr (qChain L).cr (qChain L).ci (qChain L).rho L.mU L.aU L.bL bU := rfl

/-- The imaginary part of the centre of `g` in `gDisc`. -/
theorem gDisc_gi (L : Leaf) (bU : ℤ) :
    (gDisc L bU).2.2.1 = ggi (qChain L).cr (qChain L).ci (qChain L).rho L.mU L.aU L.bL bU := rfl

/-- The radius of the disc of `g` in `gDisc`. -/
theorem gDisc_rg (L : Leaf) (bU : ℤ) :
    (gDisc L bU).2.2.2 = grg (qChain L).cr (qChain L).ci (qChain L).rho L.mU L.aU L.bL bU := rfl

/-! ## Rounding facts -/

/-- One ulp of `md`. -/
theorem md_err (x c : ℤ) :
    |((md x c : ℤ) : ℝ) - (x : ℝ) * (c : ℝ) / (S : ℝ)| < 1 := by
  have h1 := md_le x c
  have h2 := md_gt x c
  rw [abs_lt]
  constructor <;> linarith

/-- The naive complex product rounds each of the four integer products. -/
theorem cx_mul_le' (a b c d : ℤ) :
    ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 4 / (S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := S_posR
  have h1 := md_err a c
  have h2 := md_err b d
  have h3 := md_err a d
  have h4 := md_err b c
  have hre : |(cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d).re| ≤ 2 / (S : ℝ) := by
    simp only [Complex.sub_re, Complex.mul_re, cx_re, cx_im, cmr]
    push_cast
    have e : (((md a c : ℤ) : ℝ) - ((md b d : ℤ) : ℝ)) / (S : ℝ) -
        (((a : ℝ) / (S : ℝ)) * ((c : ℝ) / (S : ℝ)) - ((b : ℝ) / (S : ℝ)) * ((d : ℝ) / (S : ℝ))) =
        ((((md a c : ℤ) : ℝ) - (a : ℝ) * (c : ℝ) / (S : ℝ)) -
          (((md b d : ℤ) : ℝ) - (b : ℝ) * (d : ℝ) / (S : ℝ))) / (S : ℝ) := by
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hS]
    apply div_le_div_of_nonneg_right _ (le_of_lt hS)
    rw [abs_sub_le_iff]
    constructor
    · have p1 := (abs_lt.mp h1).2
      have p2 := (abs_lt.mp h2).1
      linarith
    · have p1 := (abs_lt.mp h1).1
      have p2 := (abs_lt.mp h2).2
      linarith
  have him : |(cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d).im| ≤ 2 / (S : ℝ) := by
    simp only [Complex.sub_im, Complex.mul_im, cx_re, cx_im, cmi]
    push_cast
    have e : (((md a d : ℤ) : ℝ) + ((md b c : ℤ) : ℝ)) / (S : ℝ) -
        (((a : ℝ) / (S : ℝ)) * ((d : ℝ) / (S : ℝ)) + ((b : ℝ) / (S : ℝ)) * ((c : ℝ) / (S : ℝ))) =
        ((((md a d : ℤ) : ℝ) - (a : ℝ) * (d : ℝ) / (S : ℝ)) +
          (((md b c : ℤ) : ℝ) - (b : ℝ) * (c : ℝ) / (S : ℝ))) / (S : ℝ) := by
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hS]
    apply div_le_div_of_nonneg_right _ (le_of_lt hS)
    rw [abs_le]
    have p1 := (abs_lt.mp h3).1
    have p2 := (abs_lt.mp h3).2
    have p3 := (abs_lt.mp h4).1
    have p4 := (abs_lt.mp h4).2
    constructor
    · linarith
    · linarith
  calc ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖
      ≤ |(cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d).re| +
        |(cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 / (S : ℝ) + 2 / (S : ℝ) := add_le_add hre him
    _ = 4 / (S : ℝ) := by ring

/-- Squaring a disc: `sqD` is sound. -/
theorem sqD_sound (c : ℤ × ℤ × ℤ) (w : ℂ)
    (hw : ‖w - cx c.1 c.2.1‖ ≤ ((c.2.2 : ℤ) : ℝ) / (S : ℝ)) :
    ‖w ^ 2 - cx (sqD c).1 (sqD c).2.1‖ ≤ (((sqD c).2.2 : ℤ) : ℝ) / (S : ℝ) := by
  have hS : (0 : ℝ) < (S : ℝ) := S_posR
  have hsq : (sqD c).2.2 = 2 * mu (iabs c.1 + iabs c.2.1) c.2.2 + mu c.2.2 c.2.2 + ETOL := rfl
  have hsd1 : (sqD c).1 = cmr c.1 c.2.1 c.1 c.2.1 := rfl
  have hsd2 : (sqD c).2.1 = cmi c.1 c.2.1 c.1 c.2.1 := rfl
  by_cases hc : 0 ≤ c.2.2
  · have hcR : (0 : ℝ) ≤ (c.2.2 : ℝ) := by exact_mod_cast hc
    set r : ℝ := ((c.2.2 : ℤ) : ℝ) / (S : ℝ) with hrdef
    have hr0 : 0 ≤ r := div_nonneg hcR (le_of_lt hS)
    set a : ℂ := cx c.1 c.2.1 with hadef
    have hwa : ‖w - a‖ ≤ r := hw
    -- the second order part
    have h1 : ‖w ^ 2 - a ^ 2‖ ≤ 2 * ‖a‖ * r + r ^ 2 := by
      have hsum : ‖w + a‖ ≤ r + 2 * ‖a‖ := by
        have e : w + a = (w - a) + 2 * a := by ring
        calc ‖w + a‖ = ‖(w - a) + 2 * a‖ := by rw [e]
          _ ≤ ‖w - a‖ + ‖2 * a‖ := norm_add_le _ _
          _ = ‖w - a‖ + 2 * ‖a‖ := by rw [norm_mul]; norm_num
          _ ≤ r + 2 * ‖a‖ := by linarith
      have e2 : w ^ 2 - a ^ 2 = (w - a) * (w + a) := by ring
      calc ‖w ^ 2 - a ^ 2‖ = ‖(w - a) * (w + a)‖ := by rw [e2]
        _ = ‖w - a‖ * ‖w + a‖ := norm_mul _ _
        _ ≤ r * (r + 2 * ‖a‖) := mul_le_mul hwa hsum (norm_nonneg _) hr0
        _ = 2 * ‖a‖ * r + r ^ 2 := by ring
    -- the rounding part
    have h2 : ‖a ^ 2 - cx (sqD c).1 (sqD c).2.1‖ ≤ 4 / (S : ℝ) := by
      rw [hsd1, hsd2, hadef, pow_two, norm_sub_rev]
      exact cx_mul_le' c.1 c.2.1 c.1 c.2.1
    -- the radius accounting
    have hna : ‖cx c.1 c.2.1‖ ≤ (((iabs c.1 + iabs c.2.1 : ℤ)) : ℝ) / (S : ℝ) := by
      calc ‖cx c.1 c.2.1‖ ≤ (|(c.1 : ℝ)| + |(c.2.1 : ℝ)|) / (S : ℝ) := norm_cx_le_abs _ _
        _ = (((iabs c.1 + iabs c.2.1 : ℤ)) : ℝ) / (S : ℝ) := by
            push_cast
            simp only [iabs_abs]
    have hA : (0 : ℝ) ≤ ((iabs c.1 + iabs c.2.1 : ℤ) : ℝ) := by
      have h : (0 : ℤ) ≤ iabs c.1 + iabs c.2.1 := by
        have h1 := iabs_nonneg c.1
        have h2 := iabs_nonneg c.2.1
        omega
      exact_mod_cast h
    have hterm1 : 2 * ‖a‖ * r ≤ (2 * ((mu (iabs c.1 + iabs c.2.1) c.2.2 : ℤ) : ℝ)) / (S : ℝ) := by
      rw [hrdef, hadef]
      calc 2 * ‖cx c.1 c.2.1‖ * (((c.2.2 : ℤ) : ℝ) / (S : ℝ))
          ≤ 2 * (((iabs c.1 + iabs c.2.1 : ℤ) : ℝ) / (S : ℝ)) * (((c.2.2 : ℤ) : ℝ) / (S : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (div_nonneg hcR (le_of_lt hS))
            exact mul_le_mul_of_nonneg_left hna (by norm_num)
        _ = 2 * ((((iabs c.1 + iabs c.2.1 : ℤ) : ℝ) * ((c.2.2 : ℤ) : ℝ) / (S : ℝ)) / (S : ℝ)) := by ring
        _ ≤ 2 * ((mu (iabs c.1 + iabs c.2.1) c.2.2 : ℤ) : ℝ) / (S : ℝ) := by
            have hm := mu_ge (iabs c.1 + iabs c.2.1) c.2.2
            have h2m : 2 * (((iabs c.1 + iabs c.2.1 : ℤ) : ℝ) * ((c.2.2 : ℤ) : ℝ) / (S : ℝ)) ≤
                2 * ((mu (iabs c.1 + iabs c.2.1) c.2.2 : ℤ) : ℝ) := by linarith
            calc 2 * ((((iabs c.1 + iabs c.2.1 : ℤ) : ℝ) * ((c.2.2 : ℤ) : ℝ) / (S : ℝ)) / (S : ℝ))
                = (2 * (((iabs c.1 + iabs c.2.1 : ℤ) : ℝ) * ((c.2.2 : ℤ) : ℝ) / (S : ℝ))) / (S : ℝ) := by ring
              _ ≤ (2 * ((mu (iabs c.1 + iabs c.2.1) c.2.2 : ℤ) : ℝ)) / (S : ℝ) :=
                  div_le_div_of_nonneg_right h2m (le_of_lt hS)
    have hterm2 : r ^ 2 ≤ ((mu c.2.2 c.2.2 : ℤ) : ℝ) / (S : ℝ) := by
      rw [hrdef]
      calc (((c.2.2 : ℤ) : ℝ) / (S : ℝ)) ^ 2
          = ((((c.2.2 : ℤ) : ℝ) * ((c.2.2 : ℤ) : ℝ) / (S : ℝ)) / (S : ℝ)) := by ring
        _ ≤ ((mu c.2.2 c.2.2 : ℤ) : ℝ) / (S : ℝ) :=
            div_le_div_of_nonneg_right (mu_ge c.2.2 c.2.2) (le_of_lt hS)
    have hterm3 : 4 / (S : ℝ) ≤ (ETOL : ℝ) / (S : ℝ) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hS)
      norm_num [ETOL]
    have hrw : (((sqD c).2.2 : ℤ) : ℝ) / (S : ℝ) =
        (2 * ((mu (iabs c.1 + iabs c.2.1) c.2.2 : ℤ) : ℝ)) / (S : ℝ) +
        ((mu c.2.2 c.2.2 : ℤ) : ℝ) / (S : ℝ) + (ETOL : ℝ) / (S : ℝ) := by
      rw [hsq]; push_cast; ring
    have htri : w ^ 2 - cx (sqD c).1 (sqD c).2.1 =
        (w ^ 2 - a ^ 2) + (a ^ 2 - cx (sqD c).1 (sqD c).2.1) := by ring
    calc ‖w ^ 2 - cx (sqD c).1 (sqD c).2.1‖
        = ‖(w ^ 2 - a ^ 2) + (a ^ 2 - cx (sqD c).1 (sqD c).2.1)‖ := by rw [htri]
      _ ≤ ‖w ^ 2 - a ^ 2‖ + ‖a ^ 2 - cx (sqD c).1 (sqD c).2.1‖ := norm_add_le _ _
      _ ≤ (2 * ‖a‖ * r + r ^ 2) + 4 / (S : ℝ) := add_le_add h1 h2
      _ ≤ (((sqD c).2.2 : ℤ) : ℝ) / (S : ℝ) := by
          rw [hrw]; linarith [hterm1, hterm2, hterm3]
  · have hneg : c.2.2 < 0 := not_le.mp hc
    have hrneg : ((c.2.2 : ℤ) : ℝ) / (S : ℝ) < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast hneg) hS
    exact absurd (le_trans (norm_nonneg _) hw) (not_le.mpr hrneg)

end WL
end Work.Cert

namespace Work.Cert.WL

/-- `⌊|b|²/S⌋` for a mantissa pair `(Br, Bi)`. -/
def gb20 (Br Bi : ℤ) : ℤ := fdiv (Br * Br + Bi * Bi) S

/-- Real part of the ratio `a/b` as a mantissa. -/
def gxr0 (Ar Ai Br Bi : ℤ) : ℤ := fdiv (Ar * Br + Ai * Bi) (gb20 Br Bi)

/-- Imaginary part of the ratio `a/b` as a mantissa. -/
def gxi0 (Ar Ai Br Bi : ℤ) : ℤ := fdiv (Ai * Br - Ar * Bi) (gb20 Br Bi)

end Work.Cert.WL
