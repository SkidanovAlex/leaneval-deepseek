/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# `norm_sq_le_jet3box`: a bound for `‖F'''‖²` over the certificate box

Item **E-E** of the `SeedCertNum` contract (`NOTES_LEAD_mandelbar_noncusp.md` §2.5) needs an upper
bound of the third derivative of the iterate `F c = (Tsq c)^[5]` on the box `Xz2 = Xz ⊕ [-ρ,ρ]²`.
The third-order Taylor remainder of `F` is controlled by `sup ‖F'''‖`, and the sharp constant
`Kee` of `Submission/Work/SeedCertNum/EE.lean` is obtained from the *rounded third-order jet*
`jet3IterR 400 (pbox x₀ Xt) Xz2 5` of `Submission/Work/SeedCertNum/Jet3.lean` by the
`decide`-checked comparison `ee_d3_check`.

## Main results

* `Work.SeedCertNum.Nsjb.iteratedDeriv_three_Tsq` — `(Tsq c)''' = 24·id`;
* `Work.SeedCertNum.Nsjb.contDiff_three_Tsq`, `…_iter` — `Tsq c` and its iterates are `C³`;
* `Work.SeedCertNum.Nsjb.jet3IterR_sound` — **soundness of `jet3IterR`**: for `c` in the parameter
  box and `z` in `Xz`, the value and the first three derivatives of `(Tsq c)^[n]` at `z` lie in the
  four boxes of `jet3IterR K Ctyp Xz n`;
* `Work.SeedCertNum.norm_sq_le_jet3box` — **the requested lemma**.

The soundness proof of `jet3IterR_sound` is the order-three analogue of
`Submission/Work/SeedCertNum/mem_jet2R.lean`: the chain rule `deriv_comp` in order one, the
Faà-di-Bruno formulas `iteratedDeriv_comp_two` / `iteratedDeriv_comp_three` in orders two and
three, and the box arithmetic of `Work.SeedCert.CBox` (`CBox_mem_mul`, `CBox.mem_sq`,
`CBox.mem_add`, `CBox.mem_conj`, `CBox.mem_mulScalar`, `CBox.mem_roundOut`).  The helpers live in
the namespace `Work.SeedCertNum.Nsjb` so as not to collide with the (independently written)
third-order soundness development of `Submission/Work/SeedCertNum/mem_jet3R.lean`.
-/
import Mathlib
import Submission.Work.SeedCertNum.Jet3
import Submission.Work.SeedCertNum.NormSq
import Submission.Work.SeedCertNum.mem_jet2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

noncomputable section

namespace Nsjb

/-! ## The derivatives of `Tsq c` -/

/-- `iteratedDeriv 2 f = deriv (deriv f)`, for `f : ℂ → ℂ`. -/
theorem iteratedDeriv_two_eq (f : ℂ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- The third derivative of `Tsq c = fun z => (z^2 + star c)^2 + c`: `(Tsq c)''' w = 24 w`. -/
theorem iteratedDeriv_three_Tsq (c w : ℂ) :
    iteratedDeriv 3 (Work.Landing.Tsq c) w = 24 * w := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_two_eq]
  rw [show deriv (deriv (Work.Landing.Tsq c)) = fun v : ℂ => 12 * v ^ 2 + 4 * star c from
    funext (fun v => deriv_deriv_Tsq_apply c v)]
  have h : HasDerivAt (fun v : ℂ => 12 * v ^ 2 + 4 * star c) (24 * w) w := by
    have h1 : HasDerivAt (fun v : ℂ => v ^ 2) (2 * w) w := by
      simpa using hasDerivAt_pow 2 w
    have h2 : HasDerivAt (fun v : ℂ => 12 * v ^ 2 + 4 * star c) (12 * (2 * w)) w :=
      (h1.const_mul (12 : ℂ)).add_const (4 * star c)
    convert h2 using 1
    ring
  exact h.deriv

/-! ## Smoothness -/

/-- `Tsq c` is `C³` (it is a polynomial). -/
theorem contDiff_three_Tsq (c : ℂ) : ContDiff ℂ 3 (Work.Landing.Tsq c) := by
  show ContDiff ℂ 3 (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
  exact (((contDiff_id.pow 2).add contDiff_const).pow 2).add contDiff_const

/-- Every iterate of `Tsq c` is `C³`. -/
theorem contDiff_three_Tsq_iter (c : ℂ) (n : ℕ) : ContDiff ℂ 3 ((Work.Landing.Tsq c)^[n]) := by
  induction n with
  | zero => simpa using contDiff_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (contDiff_three_Tsq c).comp ih

/-! ## The base case: the identity -/

theorem iteratedDeriv_two_id (x : ℂ) : iteratedDeriv 2 (id : ℂ → ℂ) x = 0 := by
  rw [iteratedDeriv_two_eq, show deriv (id : ℂ → ℂ) = fun _ => (1 : ℂ) from funext deriv_id]
  exact deriv_const x 1

theorem iteratedDeriv_three_id (x : ℂ) : iteratedDeriv 3 (id : ℂ → ℂ) x = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
    show iteratedDeriv 2 (id : ℂ → ℂ) = fun _ => (0 : ℂ) from funext iteratedDeriv_two_id]
  exact deriv_const x 0

/-! ## Soundness of the rounded third-order jet recursion -/

/-- **Soundness of `jet3IterR`.**  For `c` in the parameter box `Ctyp` and `z` in `Xz`, the `n`-th
iterate of `Tsq c` at `z`, together with its first three derivatives, lies in the corresponding
rounded boxes of `jet3IterR K Ctyp Xz n`. -/
theorem jet3IterR_sound {c : ℂ} {Ctyp Xz : CBox} (hc : c ∈ Ctyp.toSet) (K n : ℕ) {z : ℂ}
    (hz : z ∈ Xz.toSet) :
    ((Work.Landing.Tsq c)^[n] z ∈ (jet3IterR K Ctyp Xz n).v.toSet) ∧
      (deriv ((Work.Landing.Tsq c)^[n]) z ∈ (jet3IterR K Ctyp Xz n).d1.toSet) ∧
      (iteratedDeriv 2 ((Work.Landing.Tsq c)^[n]) z ∈ (jet3IterR K Ctyp Xz n).d2.toSet) ∧
      (iteratedDeriv 3 ((Work.Landing.Tsq c)^[n]) z ∈ (jet3IterR K Ctyp Xz n).d3.toSet) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_zero_apply]
      exact CBox.mem_roundOut hz
    · rw [Function.iterate_zero, deriv_id]
      refine CBox.mem_roundOut ?_
      simp [oneBox, Dya.toReal_one, Dya.toReal_zero]
    · rw [Function.iterate_zero, iteratedDeriv_two_id]
      refine CBox.mem_roundOut ?_
      simp [zeroB, Dya.toReal_zero]
    · rw [Function.iterate_zero, iteratedDeriv_three_id]
      refine CBox.mem_roundOut ?_
      simp [zeroB, Dya.toReal_zero]
  | succ n ih =>
    obtain ⟨hv, hd1, hd2, hd3⟩ := ih
    -- `conj c` lies in the conjugated parameter box
    have hsc : star c ∈ Ctyp.conj.toSet := CBox.mem_conj hc
    -- `w^2 + conj c` lies in the intermediate box `v.sq + conj Ctyp`
    have hu : ((Work.Landing.Tsq c)^[n] z) ^ 2 + star c
        ∈ (((jet3IterR K Ctyp Xz n).v.sq).add Ctyp.conj).toSet :=
      CBox.mem_add (CBox.mem_sq hv) hsc
    -- `4 w` lies in `v.mulScalar 4`
    have h4 : (4 : ℂ) * ((Work.Landing.Tsq c)^[n] z)
        ∈ ((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).toSet := by
      have h := CBox.mem_mulScalar (B := (jet3IterR K Ctyp Xz n).v) hv (a := Dya.ofInt 4)
      simpa using h
    -- `G'(w) = 4 w (w^2 + conj c)` lies in `G1`
    have hdG : deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z)
        ∈ (((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).mul
           (((jet3IterR K Ctyp Xz n).v.sq).add Ctyp.conj)).toSet := by
      rw [deriv_Tsq_apply]
      exact CBox_mem_mul h4 hu
    -- `12 w^2` and `4 conj c` lie in `G2`
    have h12 : (12 : ℂ) * ((Work.Landing.Tsq c)^[n] z) ^ 2
        ∈ ((jet3IterR K Ctyp Xz n).v.sq.mulScalar (Dya.ofInt 12)).toSet := by
      have h := CBox.mem_mulScalar (B := (jet3IterR K Ctyp Xz n).v.sq) (CBox.mem_sq hv)
        (a := Dya.ofInt 12)
      simpa using h
    have h4c : (4 : ℂ) * star c ∈ (Ctyp.conj.mulScalar (Dya.ofInt 4)).toSet := by
      have h := CBox.mem_mulScalar (B := Ctyp.conj) hsc (a := Dya.ofInt 4)
      simpa using h
    -- `G''(w) = 12 w^2 + 4 conj c` lies in `G2`
    have hd2G : iteratedDeriv 2 (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z)
        ∈ (((jet3IterR K Ctyp Xz n).v.sq.mulScalar (Dya.ofInt 12)).add
           (Ctyp.conj.mulScalar (Dya.ofInt 4))).toSet := by
      rw [iteratedDeriv_two_eq, deriv_deriv_Tsq_apply]
      exact CBox.mem_add h12 h4c
    -- `G'''(w) = 24 w` lies in `G3`
    have h24 : (24 : ℂ) * ((Work.Landing.Tsq c)^[n] z)
        ∈ ((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 24)).toSet := by
      have h := CBox.mem_mulScalar (B := (jet3IterR K Ctyp Xz n).v) hv (a := Dya.ofInt 24)
      simpa using h
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- value: `G w = (w^2 + conj c)^2 + c`
      rw [Function.iterate_succ', Function.comp_apply]
      show (((Work.Landing.Tsq c)^[n] z) ^ 2 + star c) ^ 2 + c ∈
        ((jet3IterR K Ctyp Xz (n + 1)).v).toSet
      simp only [jet3IterR, DJet3.roundOut, jet3Step]
      exact CBox.mem_roundOut (CBox.mem_add (CBox.mem_sq hu) hc)
    · -- first derivative: chain rule
      have hdiffG : DifferentiableAt ℂ (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z) :=
        ((contDiff_Tsq c).contDiffAt).differentiableAt (by norm_num)
      have hdiffH : DifferentiableAt ℂ ((Work.Landing.Tsq c)^[n]) z :=
        ((contDiff_Tsq_iter c n).contDiffAt).differentiableAt (by norm_num)
      rw [Function.iterate_succ', deriv_comp z hdiffG hdiffH]
      have hprod := CBox_mem_mul hdG hd1
      simpa only [jet3IterR, DJet3.roundOut, jet3Step] using CBox.mem_roundOut hprod
    · -- second derivative: order-two Faà di Bruno
      have hcomp2 := iteratedDeriv_comp_two (𝕜 := ℂ) (g := Work.Landing.Tsq c)
        (f := (Work.Landing.Tsq c)^[n]) (x := z)
        ((contDiff_Tsq c).contDiffAt) ((contDiff_Tsq_iter c n).contDiffAt)
      rw [Function.iterate_succ', hcomp2]
      have hA := CBox_mem_mul hd2G (CBox.mem_sq hd1)
      have hB := CBox_mem_mul hdG hd2
      have hsum := CBox.mem_add hA hB
      simpa only [jet3IterR, DJet3.roundOut, jet3Step] using CBox.mem_roundOut hsum
    · -- third derivative: order-three Faà di Bruno
      have hcomp3 := iteratedDeriv_comp_three (𝕜 := ℂ) (g := Work.Landing.Tsq c)
        (f := (Work.Landing.Tsq c)^[n]) (x := z)
        ((contDiff_three_Tsq c).contDiffAt) ((contDiff_three_Tsq_iter c n).contDiffAt)
      rw [Function.iterate_succ', hcomp3]
      -- first term: `G'''(w) · (H')³`
      have ht1 : iteratedDeriv 3 (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z)
            * deriv ((Work.Landing.Tsq c)^[n]) z ^ 3
          ∈ (((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 24)).mul
             ((jet3IterR K Ctyp Xz n).d1.sq.mul (jet3IterR K Ctyp Xz n).d1)).toSet := by
        have h := CBox_mem_mul h24 (CBox_mem_mul (CBox.mem_sq hd1) hd1)
        rw [iteratedDeriv_three_Tsq c ((Work.Landing.Tsq c)^[n] z),
          show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
        exact h
      -- second term: `3 · G''(w) · H'' · H'`
      have ht2 : 3 * iteratedDeriv 2 (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z)
            * iteratedDeriv 2 ((Work.Landing.Tsq c)^[n]) z * deriv ((Work.Landing.Tsq c)^[n]) z
          ∈ (CBox.mulScalar (Dya.ofInt 3)
              (CBox.mul
                (CBox.add (CBox.mulScalar (Dya.ofInt 12) ((jet3IterR K Ctyp Xz n).v.sq))
                  (CBox.mulScalar (Dya.ofInt 4) Ctyp.conj))
                (CBox.mul (jet3IterR K Ctyp Xz n).d1 (jet3IterR K Ctyp Xz n).d2))).toSet := by
        have h := CBox_mem_mul hd2G (CBox_mem_mul hd1 hd2)
        have hs := CBox.mem_mulScalar (B := (((jet3IterR K Ctyp Xz n).v.sq.mulScalar
          (Dya.ofInt 12)).add (Ctyp.conj.mulScalar (Dya.ofInt 4))).mul
            ((jet3IterR K Ctyp Xz n).d1.mul (jet3IterR K Ctyp Xz n).d2)) h (a := Dya.ofInt 3)
        rw [Dya.toReal_ofInt] at hs
        convert hs using 1
        push_cast
        ring
      -- third term: `G'(w) · H'''`
      have ht3 : deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z)
            * iteratedDeriv 3 ((Work.Landing.Tsq c)^[n]) z
          ∈ ((((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).mul
             (((jet3IterR K Ctyp Xz n).v.sq).add Ctyp.conj)).mul
             (jet3IterR K Ctyp Xz n).d3).toSet :=
        CBox_mem_mul hdG hd3
      have hsum := CBox.mem_add (CBox.mem_add ht1 ht2) ht3
      simpa only [jet3IterR, DJet3.roundOut, jet3Step] using CBox.mem_roundOut hsum

end Nsjb

/-! ## The requested lemma -/

theorem norm_sq_le_jet3box {x₀ : Work.SeedCert.Dya} {Xt : Work.SeedCert.IV}
    {Xz2 : Work.SeedCert.CBox} {ρ : ℝ} {z : ℂ} {t : ℝ}
    (hz2 : ∀ u : ℂ, ‖u‖ ≤ ρ → z + u ∈ Xz2.toSet) (ht : t ∈ Xt.toSet) :
    ∀ w : ℂ, ‖w‖ ≤ ρ →
      ‖iteratedDeriv 3 ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[5]) (z + w)‖ ^ 2
        ≤ ((Work.SeedCert.jet3IterR 400 (Work.SeedCert.pbox x₀ Xt) Xz2 5).d3.normSq).hi.toReal := by
  intro w hw
  have hc : (x₀.toReal + t * Complex.I) ∈ (pbox x₀ Xt).toSet := mem_pbox ht
  have hzw : z + w ∈ Xz2.toSet := hz2 w hw
  have hmem := (Nsjb.jet3IterR_sound hc 400 5 hzw).2.2.2
  exact (CBox.mem_normSq hmem).2

end

end Work.SeedCertNum
