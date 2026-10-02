/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Soundness of the second-order jet recursion `jet2Iter` (item A3)

`Work.SeedCert.jet2Iter Ctyp Xz n` is the interval-arithmetic enclosure of the second-order jet
`(value, first derivative, second derivative)` of the iterate `(Tsq c)^[n]` at `z`, where
`c ∈ Ctyp` and `z ∈ Xz` and `Tsq c = fun z => (z^2 + conj c)^2 + c` is the holomorphic polynomial
whose fifth iterate is the map `F` of item A3 of the `SeedCertNum` contract.

The present file proves the *soundness* of that recursion, `mem_jet2`: for every `c ∈ Ctyp`,
every `z ∈ Xz` and every `n`,

* `(Tsq c)^[n] z` lies in the `v`-box,
* `deriv ((Tsq c)^[n]) z` lies in the `d1`-box,
* `deriv (deriv ((Tsq c)^[n])) z` lies in the `d2`-box.

The proof is an induction on `n`; the induction step composes `Tsq c` with `(Tsq c)^[n]` and uses

* `deriv_comp` for the first derivative;
* the order-two Faà di Bruno formula `iteratedDeriv_comp_two` (Mathlib,
  `Mathlib/Analysis/Calculus/IteratedDeriv/FaaDiBruno.lean`) for the second derivative, packaged here
  as `deriv_deriv_comp_two`;
* the closed forms `deriv_Tsq_apply`, `deriv_deriv_Tsq_apply` of the first two derivatives of
  `Tsq c`, computed directly from `HasDerivAt` combinators (no Faà di Bruno).

Everything is proved inside the box arithmetic of `Work.SeedCert.CBox` (`CBox_mem_mul`,
`CBox.mem_sq`, `CBox.mem_add`, `CBox.mem_conj`, `CBox.mem_mulScalar`).
-/
import Mathlib
import Submission.Work.SeedCertNum.Jet2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

noncomputable section

/-! ## The derivatives of `Tsq c` -/

/-- The first derivative of the holomorphic polynomial `Tsq c = fun z => (z^2 + conj c)^2 + c`:
`deriv (Tsq c) w = 4 w (w^2 + conj c)`. -/
theorem deriv_Tsq_apply (c w : ℂ) :
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
theorem deriv_deriv_Tsq_apply (c w : ℂ) :
    deriv (deriv (Work.Landing.Tsq c)) w = 12 * w ^ 2 + 4 * star c := by
  have hd : deriv (Work.Landing.Tsq c) = fun v => 4 * v * (v ^ 2 + star c) :=
    funext (fun v => deriv_Tsq_apply c v)
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

/-! ## Faà di Bruno in order two -/

/-- The second derivative of a composition, on `ℂ`:
`(G ∘ H)'' = (G'' ∘ H)·(H')² + (G' ∘ H)·H''`.  This is `iteratedDeriv_comp_two` rewritten with
`iteratedDeriv 2 f = deriv (deriv f)`. -/
theorem deriv_deriv_comp_two {G H : ℂ → ℂ} {z : ℂ}
    (hG : ContDiffAt ℂ 2 G (H z)) (hH : ContDiffAt ℂ 2 H z) :
    deriv (deriv (G ∘ H)) z =
      deriv (deriv G) (H z) * (deriv H z) ^ 2 + deriv G (H z) * deriv (deriv H) z := by
  have key := iteratedDeriv_comp_two (𝕜 := ℂ) (g := G) (f := H) hG hH
  have e1 : iteratedDeriv 2 (G ∘ H) = deriv (deriv (G ∘ H)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have e2 : iteratedDeriv 2 G = deriv (deriv G) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have e3 : iteratedDeriv 2 H = deriv (deriv H) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [e1, e2, e3] at key
  exact key

/-! ## Smoothness of the iterates -/

/-- `Tsq c` is `C²` (it is a polynomial). -/
theorem contDiff_Tsq (c : ℂ) : ContDiff ℂ 2 (Work.Landing.Tsq c) := by
  show ContDiff ℂ 2 (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c)
  exact (((contDiff_id.pow 2).add contDiff_const).pow 2).add contDiff_const

/-- Every iterate of `Tsq c` is `C²`. -/
theorem contDiff_Tsq_iter (c : ℂ) (n : ℕ) : ContDiff ℂ 2 ((Work.Landing.Tsq c)^[n]) := by
  induction n with
  | zero => simpa using contDiff_id
  | succ n ih =>
    rw [Function.iterate_succ']
    exact (contDiff_Tsq c).comp ih

/-! ## The induction step -/

/-- One step of the jet recursion: the three box inclusions for `n + 1` follow from those for `n`. -/
theorem jet2_step {c : ℂ} {Ctyp Xz : CBox} (hc : c ∈ Ctyp.toSet) (n : ℕ) {z : ℂ}
    (ih : ((Work.Landing.Tsq c)^[n] z ∈ (jet2Iter Ctyp Xz n).v.toSet) ∧
          (deriv ((Work.Landing.Tsq c)^[n]) z ∈ (jet2Iter Ctyp Xz n).d1.toSet) ∧
          (deriv (deriv ((Work.Landing.Tsq c)^[n])) z ∈ (jet2Iter Ctyp Xz n).d2.toSet)) :
    ((Work.Landing.Tsq c)^[n+1] z ∈ (jet2Iter Ctyp Xz (n+1)).v.toSet) ∧
    (deriv ((Work.Landing.Tsq c)^[n+1]) z ∈ (jet2Iter Ctyp Xz (n+1)).d1.toSet) ∧
    (deriv (deriv ((Work.Landing.Tsq c)^[n+1])) z ∈ (jet2Iter Ctyp Xz (n+1)).d2.toSet) := by
  obtain ⟨hv, hd1, hd2⟩ := ih
  -- `conj c` lies in the conjugated parameter box
  have hsc : star c ∈ Ctyp.conj.toSet := CBox.mem_conj hc
  -- `4 w` lies in `v.mulScalar 4`
  have h4 : (4 : ℂ) * ((Work.Landing.Tsq c)^[n] z)
      ∈ ((jet2Iter Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).toSet := by
    have := CBox.mem_mulScalar (B := (jet2Iter Ctyp Xz n).v) hv (a := Dya.ofInt 4)
    simpa using this
  -- `w^2 + conj c` lies in the intermediate box `v.sq + conj Ctyp`
  have hu : ((Work.Landing.Tsq c)^[n] z) ^ 2 + star c
      ∈ (((jet2Iter Ctyp Xz n).v.sq).add Ctyp.conj).toSet :=
    CBox.mem_add (CBox.mem_sq hv) hsc
  -- `G'(w) = 4 w (w^2 + conj c)` lies in `dG`
  have hdG : deriv (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z)
      ∈ (((jet2Iter Ctyp Xz n).v.mulScalar (Dya.ofInt 4)).mul
         (((jet2Iter Ctyp Xz n).v.sq).add Ctyp.conj)).toSet := by
    rw [deriv_Tsq_apply]
    exact CBox_mem_mul h4 hu
  refine ⟨?_, ?_, ?_⟩
  · -- value: `G w = (w^2 + conj c)^2 + c`
    rw [Function.iterate_succ_apply']
    show ((Work.Landing.Tsq c)^[n] z ^ 2 + star c) ^ 2 + c ∈
      (Work.SeedCert.jet2Step Ctyp (jet2Iter Ctyp Xz n)).v.toSet
    simp only [Work.SeedCert.jet2Step]
    exact CBox.mem_add (CBox.mem_sq (CBox.mem_add (CBox.mem_sq hv) hsc)) hc
  · -- first derivative: chain rule
    have hdiffG : DifferentiableAt ℂ (Work.Landing.Tsq c) ((Work.Landing.Tsq c)^[n] z) :=
      ((contDiff_Tsq c).contDiffAt).differentiableAt (by norm_num)
    have hdiffH : DifferentiableAt ℂ ((Work.Landing.Tsq c)^[n]) z :=
      ((contDiff_Tsq_iter c n).contDiffAt).differentiableAt (by norm_num)
    have hcomp := deriv_comp z hdiffG hdiffH
    rw [Function.iterate_succ', hcomp]
    have hprod := CBox_mem_mul hdG hd1
    simpa only [Work.SeedCert.jet2Iter, Work.SeedCert.jet2Step] using hprod
  · -- second derivative: order-two Faà di Bruno
    have hcomp2 := deriv_deriv_comp_two (G := Work.Landing.Tsq c)
      (H := (Work.Landing.Tsq c)^[n]) (z := z)
      ((contDiff_Tsq c).contDiffAt) ((contDiff_Tsq_iter c n).contDiffAt)
    rw [Function.iterate_succ', hcomp2]
    have h12 : (12 : ℂ) * ((Work.Landing.Tsq c)^[n] z) ^ 2
        ∈ ((jet2Iter Ctyp Xz n).v.sq.mulScalar (Dya.ofInt 12)).toSet := by
      have := CBox.mem_mulScalar (B := (jet2Iter Ctyp Xz n).v.sq)
        (CBox.mem_sq hv) (a := Dya.ofInt 12)
      simpa using this
    have h4c : (4 : ℂ) * star c ∈ (Ctyp.conj.mulScalar (Dya.ofInt 4)).toSet := by
      have := CBox.mem_mulScalar (B := Ctyp.conj) hsc (a := Dya.ofInt 4)
      simpa using this
    have hd2G : deriv (deriv (Work.Landing.Tsq c)) ((Work.Landing.Tsq c)^[n] z)
        ∈ (((jet2Iter Ctyp Xz n).v.sq.mulScalar (Dya.ofInt 12)).add
           (Ctyp.conj.mulScalar (Dya.ofInt 4))).toSet := by
      rw [deriv_deriv_Tsq_apply]
      exact CBox.mem_add h12 h4c
    have hA := CBox_mem_mul hd2G (CBox.mem_sq hd1)
    have hB := CBox_mem_mul hdG hd2
    have hsum := CBox.mem_add hA hB
    simpa only [Work.SeedCert.jet2Iter, Work.SeedCert.jet2Step] using hsum

/-! ## Soundness of the recursion -/

/-- **Soundness of `jet2Iter`.**  For `c` in the parameter box `Ctyp` and `z` in `Xz`, the `n`-th
iterate of `Tsq c` at `z`, together with its first two derivatives, lies in the corresponding
boxes of the recursion. -/
theorem mem_jet2_of_mem {c : ℂ} {Ctyp Xz : CBox} (hc : c ∈ Ctyp.toSet)
    (n : ℕ) {z : ℂ} (hz : z ∈ Xz.toSet) :
    ((Work.Landing.Tsq c)^[n] z ∈ (jet2Iter Ctyp Xz n).v.toSet) ∧
      (deriv ((Work.Landing.Tsq c)^[n]) z ∈ (jet2Iter Ctyp Xz n).d1.toSet) ∧
      (deriv (deriv ((Work.Landing.Tsq c)^[n])) z ∈ (jet2Iter Ctyp Xz n).d2.toSet) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simpa [Function.iterate_zero_apply, Work.SeedCert.jet2Iter] using hz
    · have hd : deriv ((Work.Landing.Tsq c)^[0]) z = 1 := by
        rw [Function.iterate_zero]
        exact deriv_id z
      rw [hd]
      simp [Work.SeedCert.jet2Iter, Work.SeedCert.oneBox, Work.SeedCert.Dya.toReal_one,
        Work.SeedCert.Dya.toReal_zero]
    · have hd : deriv (deriv ((Work.Landing.Tsq c)^[0])) z = 0 := by
        rw [Function.iterate_zero]
        rw [show deriv (id : ℂ → ℂ) = fun _ => 1 from funext (fun x => deriv_id x)]
        exact deriv_const z 1
      rw [hd]
      simp [Work.SeedCert.jet2Iter, Work.SeedCert.Dya.toReal_zero]
  | succ n ih => exact jet2_step hc n ih

/-! ## The requested lemma -/

theorem mem_jet2 {x₀ : Work.SeedCert.Dya} {Xt : Work.SeedCert.IV} {Xz : Work.SeedCert.CBox}
    (n : ℕ) {z : ℂ} {t : ℝ} (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n] z
        ∈ (Work.SeedCert.jet2Iter (Work.SeedCert.pbox x₀ Xt) Xz n).v.toSet) ∧
      (deriv ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n]) z
        ∈ (Work.SeedCert.jet2Iter (Work.SeedCert.pbox x₀ Xt) Xz n).d1.toSet) ∧
      (deriv (deriv ((Work.Landing.Tsq (x₀.toReal + t * Complex.I))^[n])) z
        ∈ (Work.SeedCert.jet2Iter (Work.SeedCert.pbox x₀ Xt) Xz n).d2.toSet) :=
  mem_jet2_of_mem (Ctyp := Work.SeedCert.pbox x₀ Xt) (Work.SeedCert.mem_pbox ht) n hz

end

end Work.SeedCertNum
