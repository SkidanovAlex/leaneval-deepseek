/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Soundness of the *rounded* third-order jet recursion `jet3IterR`

`Work.SeedCert.jet3IterR K Ctyp Xz n` is the interval-arithmetic enclosure, over the parameter box
`Ctyp` and the `z`-box `Xz`, of the third-order jet `(value, first, second, third derivative)` of the
iterate `(Tsq c)^[n]`, with an outward rounding to the grid `2^-K` after every step
(`Work.SeedCert.DJet3.roundOut`, `Work.SeedCert.CBox.mem_roundOut` in
`Submission/Work/SeedCertNum/Round.lean`).

This file proves the soundness `mem_jet3R`:  for `c ∈ Ctyp`, `z ∈ Xz` and every `n`,

* `(Tsq c)^[n] z` lies in the `v`-box,
* `deriv ((Tsq c)^[n]) z` lies in the `d1`-box,
* `deriv (deriv ((Tsq c)^[n])) z` lies in the `d2`-box,
* `deriv (deriv (deriv ((Tsq c)^[n]))) z` lies in the `d3`-box

of the rounded recursion: equivalently (`iteratedDeriv` form, which is the statement requested),
the first, second and third *iterated* derivative of `(Tsq c)^[n]` at `z` lie in `d1`, `d2`, `d3`.

The proof is the induction of `Submission/Work/SeedCertNum/mem_jet2.lean` (`jet2_step`) at order
three; the induction step is the third-order Faà di Bruno formula

  `(G∘H)''' = (G'''∘H)·(H')³ + 3·(G''∘H)·H'·H'' + (G'∘H)·H'''`

(`iteratedDeriv_comp_three` of Mathlib, `Mathlib/Analysis/Calculus/IteratedDeriv/FaaDiBruno.lean`,
rewritten here in `deriv`-form as `deriv_deriv_deriv_comp_three`), and the explicit derivatives of
`G = Tsq c` (`G' = 4w(w²+c̄)`, `G'' = 12w²+4c̄`, `G''' = 24w`).  The `roundOut K` inserted after each
step is handled by `Work.SeedCert.CBox.mem_roundOut`, exactly as in `mem_jet2R`.
-/
import Mathlib
import Submission.Work.SeedCertNum.Jet3
import Submission.Work.SeedCertNum.Round

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

noncomputable section

/-! ## Iterated derivatives in terms of ordinary ones -/

/-- `iteratedDeriv 2 f = deriv (deriv f)`. -/
theorem iteratedDeriv_two_eq (f : ℂ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- `iteratedDeriv 3 f = deriv (deriv (deriv f))`. -/
theorem iteratedDeriv_three_eq (f : ℂ → ℂ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_eq]

/-! ## The derivatives of `Tsq c` and its smoothness -/

/-- `Tsq c = fun z => (z^2 + conj c)^2 + c` is `C³` (it is a polynomial). -/
theorem contDiff_Tsq3 (c : ℂ) : ContDiff ℂ 3 (Work.Landing.Tsq c) := by
  show ContDiff ℂ 3 (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
  exact (((contDiff_id.pow 2).add contDiff_const).pow 2).add contDiff_const

/-- Every iterate of `Tsq c` is `C³`. -/
theorem contDiff_Tsq_iter3 (c : ℂ) (n : ℕ) : ContDiff ℂ 3 ((Work.Landing.Tsq c)^[n]) := by
  induction n with
  | zero => simpa using contDiff_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (contDiff_Tsq3 c).comp ih

/-- The first derivative of `Tsq c = fun z => (z^2 + conj c)^2 + c`:
`deriv (Tsq c) w = 4 w (w^2 + conj c)`. -/
theorem deriv_Tsq_apply' (c w : ℂ) :
    deriv (Work.Landing.Tsq c) w = 4 * w * (w ^ 2 + star c) := by
  have h1 : HasDerivAt (fun z : ℂ => z ^ 2 + star c) (2 * w) w := by
    have := (hasDerivAt_pow 2 w).add_const (star c)
    simpa using this
  have h2 : HasDerivAt (fun z : ℂ => (z ^ 2 + star c) ^ 2) (4 * w * (w ^ 2 + star c)) w := by
    have := h1.pow 2
    convert this using 1
    ring
  have h3 : HasDerivAt (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c) (4 * w * (w ^ 2 + star c)) w :=
    h2.add_const c
  exact h3.deriv

/-- The second derivative of `Tsq c`: `deriv (deriv (Tsq c)) w = 12 w^2 + 4 conj c`. -/
theorem deriv_deriv_Tsq_apply' (c w : ℂ) :
    deriv (deriv (Work.Landing.Tsq c)) w = 12 * w ^ 2 + 4 * star c := by
  have hd : deriv (Work.Landing.Tsq c) = fun v => 4 * v * (v ^ 2 + star c) :=
    funext (fun v => deriv_Tsq_apply' c v)
  rw [hd]
  have h : HasDerivAt (fun v : ℂ => 4 * v * (v ^ 2 + star c)) (12 * w ^ 2 + 4 * star c) w := by
    have hA : HasDerivAt (fun v : ℂ => 4 * v) 4 w := by
      have := (hasDerivAt_id w).const_mul (4 : ℂ)
      simpa using this
    have hB : HasDerivAt (fun v : ℂ => v ^ 2 + star c) (2 * w) w := by
      have := (hasDerivAt_pow 2 w).add_const (star c)
      simpa using this
    have hm := hA.mul hB
    convert hm using 1
    ring
  exact h.deriv

/-- The third derivative of `Tsq c`: `deriv (deriv (deriv (Tsq c))) w = 24 w`. -/
theorem deriv_deriv_deriv_Tsq_apply (c w : ℂ) :
    deriv (deriv (deriv (Work.Landing.Tsq c))) w = 24 * w := by
  have hd : deriv (deriv (Work.Landing.Tsq c)) = fun v => 12 * v ^ 2 + 4 * star c :=
    funext (fun v => deriv_deriv_Tsq_apply' c v)
  rw [hd]
  have h : HasDerivAt (fun v : ℂ => 12 * v ^ 2 + 4 * star c) (24 * w) w := by
    have h1 : HasDerivAt (fun v : ℂ => 12 * v ^ 2) (12 * (2 * w)) w := by
      simpa using (hasDerivAt_pow 2 w).const_mul (12 : ℂ)
    have h2 : HasDerivAt (fun _ : ℂ => 4 * star c) 0 w := hasDerivAt_const w _
    have hm := h1.add h2
    rw [show (12 : ℂ) * (2 * w) + 0 = 24 * w from by ring] at hm
    exact hm
  rw [h.deriv]

/-! ## Faà di Bruno in orders two and three, in `deriv` form -/

/-- The second derivative of a composition of holomorphic functions:
`(G ∘ H)'' = (G'' ∘ H)·(H')² + (G' ∘ H)·H''`.  This is `iteratedDeriv_comp_two` rewritten with
`iteratedDeriv 2 = deriv ∘ deriv`. -/
theorem deriv_deriv_comp_two' {G H : ℂ → ℂ} {z : ℂ}
    (hG : ContDiffAt ℂ 2 G (H z)) (hH : ContDiffAt ℂ 2 H z) :
    deriv (deriv (G ∘ H)) z =
      deriv (deriv G) (H z) * (deriv H z) ^ 2 + deriv G (H z) * deriv (deriv H) z := by
  have key := iteratedDeriv_comp_two (𝕜 := ℂ) (g := G) (f := H) hG hH
  rw [iteratedDeriv_two_eq, iteratedDeriv_two_eq, iteratedDeriv_two_eq] at key
  exact key

/-- The third derivative of a composition of holomorphic functions:
`(G ∘ H)''' = (G''' ∘ H)·(H')³ + 3·(G'' ∘ H)·H''·H' + (G' ∘ H)·H'''`.  This is
`iteratedDeriv_comp_three` rewritten with `iteratedDeriv 2 = deriv ∘ deriv` and
`iteratedDeriv 3 = deriv ∘ deriv ∘ deriv`. -/
theorem deriv_deriv_deriv_comp_three {G H : ℂ → ℂ} {z : ℂ}
    (hG : ContDiffAt ℂ 3 G (H z)) (hH : ContDiffAt ℂ 3 H z) :
    deriv (deriv (deriv (G ∘ H))) z =
      deriv (deriv (deriv G)) (H z) * (deriv H z) ^ 3 +
      3 * deriv (deriv G) (H z) * deriv (deriv H) z * deriv H z +
      deriv G (H z) * deriv (deriv (deriv H)) z := by
  have key := iteratedDeriv_comp_three (𝕜 := ℂ) (g := G) (f := H) hG hH
  rw [iteratedDeriv_three_eq, iteratedDeriv_three_eq, iteratedDeriv_three_eq,
    iteratedDeriv_two_eq, iteratedDeriv_two_eq] at key
  exact key

/-! ## The induction step of the rounded recursion -/

/-- One step of the rounded third-order jet recursion: the four box inclusions for `n + 1` follow
from those for `n`.  Mirror of `Work.SeedCertNum.jet2_stepR`, with the third-order Faà di Bruno
formula supplying the `d3`-box and `Work.SeedCert.CBox.mem_roundOut` the rounding. -/
theorem jet3_stepR {c : ℂ} {Ctyp Xz : CBox} (hc : c ∈ Ctyp.toSet) (K n : ℕ) {z : ℂ}
    (ih : ((Work.Landing.Tsq c)^[n] z ∈ (jet3IterR K Ctyp Xz n).v.toSet) ∧
          (deriv ((Work.Landing.Tsq c)^[n]) z ∈ (jet3IterR K Ctyp Xz n).d1.toSet) ∧
          (deriv (deriv ((Work.Landing.Tsq c)^[n])) z ∈ (jet3IterR K Ctyp Xz n).d2.toSet) ∧
          (deriv (deriv (deriv ((Work.Landing.Tsq c)^[n]))) z
            ∈ (jet3IterR K Ctyp Xz n).d3.toSet)) :
    ((Work.Landing.Tsq c)^[n+1] z ∈ (jet3IterR K Ctyp Xz (n+1)).v.toSet) ∧
    (deriv ((Work.Landing.Tsq c)^[n+1]) z ∈ (jet3IterR K Ctyp Xz (n+1)).d1.toSet) ∧
    (deriv (deriv ((Work.Landing.Tsq c)^[n+1])) z ∈ (jet3IterR K Ctyp Xz (n+1)).d2.toSet) ∧
    (deriv (deriv (deriv ((Work.Landing.Tsq c)^[n+1]))) z
      ∈ (jet3IterR K Ctyp Xz (n+1)).d3.toSet) := by
  obtain ⟨hv, hd1, hd2, hd3⟩ := ih
  -- `conj c` lies in the conjugated parameter box
  have hsc : star c ∈ Ctyp.conj.toSet := CBox.mem_conj hc
  -- `4 w` lies in `v.mulScalar 4`
  have h4 : (4 : ℂ) * ((Work.Landing.Tsq c)^[n] z)
      ∈ ((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).toSet := by
    have := CBox.mem_mulScalar (B := (jet3IterR K Ctyp Xz n).v) hv (a := Dya.ofInt 4)
    simpa using this
  -- `w^2 + conj c` lies in the intermediate box `v.sq + conj Ctyp`
  have hu : ((Work.Landing.Tsq c)^[n] z) ^ 2 + star c
      ∈ (((jet3IterR K Ctyp Xz n).v.sq).add Ctyp.conj).toSet :=
    CBox.mem_add (CBox.mem_sq hv) hsc
  -- `G'(w) = 4 w (w^2 + conj c)` lies in `G1`
  have hdG : deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z)
      ∈ (((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).mul
         (((jet3IterR K Ctyp Xz n).v.sq).add Ctyp.conj)).toSet := by
    rw [deriv_Tsq_apply']
    exact CBox_mem_mul h4 hu
  -- `12 w^2` and `4 conj c` lie in the boxes of `G2`
  have h12 : (12 : ℂ) * ((Work.Landing.Tsq c)^[n] z) ^ 2
      ∈ ((jet3IterR K Ctyp Xz n).v.sq.mulScalar (Dya.ofInt 12)).toSet := by
    have := CBox.mem_mulScalar (B := (jet3IterR K Ctyp Xz n).v.sq)
      (CBox.mem_sq hv) (a := Dya.ofInt 12)
    simpa using this
  have h4c : (4 : ℂ) * star c ∈ (Ctyp.conj.mulScalar (Dya.ofInt 4)).toSet := by
    have := CBox.mem_mulScalar (B := Ctyp.conj) hsc (a := Dya.ofInt 4)
    simpa using this
  -- `G''(w) = 12 w^2 + 4 conj c` lies in `G2`
  have hd2G : deriv (deriv (Work.Landing.Tsq c)) ((Work.Landing.Tsq c)^[n] z)
      ∈ (((jet3IterR K Ctyp Xz n).v.sq.mulScalar (Dya.ofInt 12)).add
         (Ctyp.conj.mulScalar (Dya.ofInt 4))).toSet := by
    rw [deriv_deriv_Tsq_apply']
    exact CBox.mem_add h12 h4c
  -- `G'''(w) = 24 w` lies in `G3`
  have hd3G : deriv (deriv (deriv (Work.Landing.Tsq c))) ((Work.Landing.Tsq c)^[n] z)
      ∈ ((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 24)).toSet := by
    rw [deriv_deriv_deriv_Tsq_apply]
    have := CBox.mem_mulScalar (B := (jet3IterR K Ctyp Xz n).v) hv (a := Dya.ofInt 24)
    simpa using this
  -- differentiability, for the chain rules
  have hdiffG : DifferentiableAt ℂ (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z) :=
    ((contDiff_Tsq3 c).contDiffAt).differentiableAt (by norm_num)
  have hdiffH : DifferentiableAt ℂ ((Work.Landing.Tsq c)^[n]) z :=
    ((contDiff_Tsq_iter3 c n).contDiffAt).differentiableAt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- value: `G w = (w^2 + conj c)^2 + c`
    rw [Function.iterate_succ_apply']
    simp only [jet3IterR, DJet3.roundOut, jet3Step]
    exact CBox.mem_roundOut
      (CBox.mem_add (CBox.mem_sq (CBox.mem_add (CBox.mem_sq hv) hsc)) hc)
  · -- first derivative: chain rule
    have hcomp := deriv_comp z hdiffG hdiffH
    rw [Function.iterate_succ', hcomp]
    have hprod := CBox_mem_mul hdG hd1
    simpa only [jet3IterR, DJet3.roundOut, jet3Step] using CBox.mem_roundOut hprod
  · -- second derivative: order-two Faà di Bruno
    have hG2 : ContDiffAt ℂ 2 (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z) :=
      ((contDiff_Tsq3 c).contDiffAt).of_le (by norm_num)
    have hH2 : ContDiffAt ℂ 2 ((Work.Landing.Tsq c)^[n]) z :=
      ((contDiff_Tsq_iter3 c n).contDiffAt).of_le (by norm_num)
    have hcomp2 := deriv_deriv_comp_two' (G := Work.Landing.Tsq c)
      (H := (Work.Landing.Tsq c)^[n]) (z := z) hG2 hH2
    rw [Function.iterate_succ', hcomp2]
    have hA := CBox_mem_mul hd2G (CBox.mem_sq hd1)
    have hB := CBox_mem_mul hdG hd2
    have hsum := CBox.mem_add hA hB
    simpa only [jet3IterR, DJet3.roundOut, jet3Step] using CBox.mem_roundOut hsum
  · -- third derivative: order-three Faà di Bruno
    have hcomp3 := deriv_deriv_deriv_comp_three (G := Work.Landing.Tsq c)
      (H := (Work.Landing.Tsq c)^[n]) (z := z)
      ((contDiff_Tsq3 c).contDiffAt) ((contDiff_Tsq_iter3 c n).contDiffAt)
    rw [Function.iterate_succ', hcomp3]
    -- `G'''·(H')³`
    have hA : deriv (deriv (deriv (Work.Landing.Tsq c))) ((Work.Landing.Tsq c)^[n] z) * deriv ((Work.Landing.Tsq c)^[n]) z ^ 3 ∈ (((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 24)).mul (((jet3IterR K Ctyp Xz n).d1.sq).mul (jet3IterR K Ctyp Xz n).d1)).toSet := by
      have h0 := CBox_mem_mul hd3G (CBox_mem_mul (CBox.mem_sq hd1) hd1)
      convert h0 using 1
      ring
    -- `3·G''·H''·H'`
    have hB : 3 * deriv (deriv (Work.Landing.Tsq c)) ((Work.Landing.Tsq c)^[n] z) * deriv (deriv ((Work.Landing.Tsq c)^[n])) z * deriv ((Work.Landing.Tsq c)^[n]) z ∈ (((((((jet3IterR K Ctyp Xz n).v.sq).mulScalar (Dya.ofInt 12)).add (Ctyp.conj.mulScalar (Dya.ofInt 4))).mul ((jet3IterR K Ctyp Xz n).d1.mul (jet3IterR K Ctyp Xz n).d2))).mulScalar (Dya.ofInt 3)).toSet
        := by
      have h0 := CBox_mem_mul hd2G (CBox_mem_mul hd1 hd2)
      have h1 := CBox.mem_mulScalar h0 (a := Dya.ofInt 3)
      convert h1 using 1
      ring_nf
      norm_num [Dya.toReal_ofInt]
    -- `G'·H'''`
    have hC : deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z) * deriv (deriv (deriv ((Work.Landing.Tsq c)^[n]))) z ∈ ((((jet3IterR K Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).mul (((jet3IterR K Ctyp Xz n).v.sq).add Ctyp.conj)).mul (jet3IterR K Ctyp Xz n).d3).toSet :=
      CBox_mem_mul hdG hd3
    have hsum := CBox.mem_add (CBox.mem_add hA hB) hC
    simpa only [jet3IterR, DJet3.roundOut, jet3Step] using CBox.mem_roundOut hsum

/-! ## Soundness of the rounded recursion -/

/-- **Soundness of `jet3IterR`** (derivative form).  For `c` in the parameter box `Ctyp` and `z` in
`Xz`, the `n`-th iterate of `Tsq c` at `z`, together with its first three ordinary derivatives, lies
in the corresponding rounded boxes of the recursion. -/
theorem mem_jet3R_of_mem {c : ℂ} {Ctyp Xz : CBox} (hc : c ∈ Ctyp.toSet)
    (K n : ℕ) {z : ℂ} (hz : z ∈ Xz.toSet) :
    ((Work.Landing.Tsq c)^[n] z ∈ (jet3IterR K Ctyp Xz n).v.toSet) ∧
      (deriv ((Work.Landing.Tsq c)^[n]) z ∈ (jet3IterR K Ctyp Xz n).d1.toSet) ∧
      (deriv (deriv ((Work.Landing.Tsq c)^[n])) z ∈ (jet3IterR K Ctyp Xz n).d2.toSet) ∧
      (deriv (deriv (deriv ((Work.Landing.Tsq c)^[n]))) z
        ∈ (jet3IterR K Ctyp Xz n).d3.toSet) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_zero_apply]
      simp only [jet3IterR]
      exact CBox.mem_roundOut hz
    · have hd : deriv ((Work.Landing.Tsq c)^[0]) z = 1 := by
        rw [Function.iterate_zero]
        exact deriv_id z
      rw [hd]
      simp only [jet3IterR]
      refine CBox.mem_roundOut ?_
      simp [oneBox, Dya.toReal_one, Dya.toReal_zero]
    · have hd : deriv (deriv ((Work.Landing.Tsq c)^[0])) z = 0 := by
        rw [Function.iterate_zero]
        rw [show deriv (id : ℂ → ℂ) = fun _ => 1 from funext (fun x => deriv_id x)]
        exact deriv_const z 1
      rw [hd]
      simp only [jet3IterR]
      refine CBox.mem_roundOut ?_
      simp [zeroB]
    · have hd : deriv (deriv (deriv ((Work.Landing.Tsq c)^[0]))) z = 0 := by
        rw [Function.iterate_zero]
        have h1 : deriv (id : ℂ → ℂ) = fun _ => 1 := funext (fun x => deriv_id x)
        have h2 : deriv (deriv (id : ℂ → ℂ)) = fun _ => (0 : ℂ) := by
          rw [h1]
          exact funext (fun x => deriv_const x 1)
        rw [h2]
        exact deriv_const z (0 : ℂ)
      rw [hd]
      simp only [jet3IterR]
      refine CBox.mem_roundOut ?_
      simp [zeroB]
  | succ n ih => exact jet3_stepR hc K n ih

/-! ## The requested lemma -/

theorem mem_jet3R {x₀ : Work.SeedCert.Dya} {Xt : Work.SeedCert.IV} {Xz : Work.SeedCert.CBox}
    (K n : ℕ) {z : ℂ} {t : ℝ} (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n] z
        ∈ (Work.SeedCert.jet3IterR K (Work.SeedCert.pbox x₀ Xt) Xz n).v.toSet) ∧
      (iteratedDeriv 1 ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n]) z
        ∈ (Work.SeedCert.jet3IterR K (Work.SeedCert.pbox x₀ Xt) Xz n).d1.toSet) ∧
      (iteratedDeriv 2 ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n]) z
        ∈ (Work.SeedCert.jet3IterR K (Work.SeedCert.pbox x₀ Xt) Xz n).d2.toSet) ∧
      (iteratedDeriv 3 ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n]) z
        ∈ (Work.SeedCert.jet3IterR K (Work.SeedCert.pbox x₀ Xt) Xz n).d3.toSet) := by
  have hc : (x₀.toReal + t * Complex.I) ∈ (Work.SeedCert.pbox x₀ Xt).toSet :=
    Work.SeedCert.mem_pbox ht
  obtain ⟨h1, h2, h3, h4⟩ :=
    mem_jet3R_of_mem (Ctyp := Work.SeedCert.pbox x₀ Xt) hc K n hz
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [iteratedDeriv_one]
    exact h2
  · rw [iteratedDeriv_two_eq]
    exact h3
  · rw [iteratedDeriv_three_eq]
    exact h4

end

end Work.SeedCertNum
