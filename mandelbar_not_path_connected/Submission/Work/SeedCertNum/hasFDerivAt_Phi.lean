/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Fréchet differentiability of the `(P₁,P₂,P₃)`-map `Φ` (item A1)

`Work.SeedCert.Phi x₀ : E3 → E3` is the map
`u ↦ (Re Θ(u), Im Θ(u), Π(u) - 1)` with `Θ = Z_5 - z` and `Π = ∏_{k<5} (2‖Z_k‖)²`
(`Submission/Work/SeedCertNum/A1Defs.lean`), and `Work.SeedCert.LPhi x₀ u` is its claimed
derivative.  This file proves `HasFDerivAt (Phi x₀) (LPhi x₀ u) u` (item S3 of the
`SeedCertNum` statement list), self-contained: the supporting statements S1
(`HasFDerivAt (Z x₀ n) (LZ x₀ n u) u`) and S2 (`HasFDerivAt (Pi x₀) (dPi x₀ u) u`) are
re-proved here in the auxiliary namespace so that this module depends only on the definitions.

The proof follows the structure of the definitions:

* the iterate `Z_{n+1} = star(Z_n)² + c` has derivative
  `δ ↦ 2 star(Z_n) star(LZ_n δ) + i δ_t`, which is *exactly* the recursion defining
  `p, q, s` (and hence `LZ_{n+1}`) — auxiliary lemma `LZ_succ_eq_aux`;
* `Nk = 4‖Z_k‖²` has derivative `dNk` (`HasFDerivAt.norm_sq` + the inner-product identity
  `⟪w, v⟫_ℝ = w.re v.re + w.im v.im` on `ℂ`);
* `Pi`, a nested product of five `Nk`'s, has derivative `dPi` (the nested product rule);
* `Φ` is assembled from the `Re`/`Im` components of `Θ` and from `Pi - 1`.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

noncomputable section

/-! ## Auxiliary derivative lemmas -/

/-- The real-linear chart `zOf : E3 → ℂ` is its own derivative. -/
private lemma hasFDerivAt_zOf_aux (u : E3) : HasFDerivAt zOf Lz u := by
  have h : (fun u : E3 => Lz u) = zOf := by funext δ; simp [zOf]
  rw [← h]; exact Lz.hasFDerivAt

/-- The parameter chart `cOf x₀ : E3 → ℂ` has derivative `Lt`. -/
private lemma hasFDerivAt_cOf_aux (x₀ : ℝ) (u : E3) : HasFDerivAt (cOf x₀) Lt u := by
  have h : HasFDerivAt (fun u : E3 => (x₀ : ℂ) + Lt u) Lt u :=
    (Lt.hasFDerivAt (x := u)).const_add (x₀ : ℂ)
  convert h using 1
  ext δ; simp [cOf]

/-- The determinant of the step `w ↦ star w ^ 2`: its derivative is
`(star w • conjCLM + star w • conjCLM) ∘SL ·`. -/
private lemma hasFDerivAt_starSq_aux (f : E3 → ℂ) (f' : E3 →L[ℝ] ℂ) (u : E3)
    (hf : HasFDerivAt f f' u) :
    HasFDerivAt (fun u => star (f u) ^ 2)
      ((star (f u) • conjCLM + star (f u) • conjCLM).comp f') u := by
  have hg : HasFDerivAt (fun z : ℂ => conjCLM z * conjCLM z)
      (conjCLM (f u) • conjCLM + conjCLM (f u) • conjCLM) (f u) :=
    (conjCLM.hasFDerivAt (x := f u)).mul (conjCLM.hasFDerivAt (x := f u))
  simpa [Function.comp_def, pow_two, conjCLM_apply] using hg.comp u hf

/-- The recursion of `LZ`: the derivative of `star (Z_n)² + c` is `LZ_{n+1}`. -/
private lemma LZ_succ_eq_aux (x₀ : ℝ) (n : ℕ) (u : E3) :
    (star (Z x₀ n u) • conjCLM + star (Z x₀ n u) • conjCLM).comp (LZ x₀ n u) + Lt
      = LZ x₀ (n + 1) u := by
  apply ContinuousLinearMap.ext
  intro δ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, conjCLM_apply, Lt_apply]
  rw [LZ_apply, LZ_apply, p_succ, q_succ, ss_succ]
  simp only [star_add, star_mul, star_zOf, star_conjZ]
  simp
  ring

/-- **S1**: `LZ x₀ n u` is the derivative of the iterate `Z x₀ n` at `u`. -/
private lemma hasFDerivAt_Z_aux (x₀ : ℝ) (n : ℕ) (u : E3) :
    HasFDerivAt (Z x₀ n) (LZ x₀ n u) u := by
  induction n with
  | zero =>
    have h := hasFDerivAt_zOf_aux u
    simpa [LZ_zero] using h
  | succ n ih =>
    have h1 := hasFDerivAt_starSq_aux _ _ _ ih
    have h2 := hasFDerivAt_cOf_aux x₀ u
    have h := h1.add h2
    rw [LZ_succ_eq_aux] at h
    change HasFDerivAt (Z x₀ (n + 1)) (LZ x₀ (n + 1) u) u at h
    exact h

/-- `dNk x₀ k u` is the derivative of `Nk x₀ k = 4‖Z_k‖²` at `u`. -/
private lemma hasFDerivAt_Nk_aux (x₀ : ℝ) (k : ℕ) (u : E3) :
    HasFDerivAt (Nk x₀ k) (dNk x₀ k u) u := by
  have hsq := (hasFDerivAt_Z_aux x₀ k u).norm_sq
  have h4raw := hsq.const_smul (4 : ℝ)
  convert h4raw using 1
  · ext x
    simp only [Nk, Pi.smul_apply, smul_eq_mul]
  · apply ContinuousLinearMap.ext
    intro δ
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
      dNk, ContinuousLinearMap.add_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    rw [innerSL_apply_apply, Complex.inner]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

/-- Product rule for real-valued functions on `E3`, in the order used by the nested product
`Pi`. -/
private lemma hasFDerivAt_mul_aux {c d : E3 → ℝ} {c' d' : E3 →L[ℝ] ℝ} {x : E3}
    (hc : HasFDerivAt c c' x) (hd : HasFDerivAt d d' x) :
    HasFDerivAt (c * d) (d x • c' + c x • d') x := by
  simpa only [add_comm] using hc.mul hd

/-- **S2**: `dPi x₀ u` is the derivative of the nested product `Pi x₀` at `u`. -/
private lemma hasFDerivAt_Pi_aux (x₀ : ℝ) (u : E3) :
    HasFDerivAt (Pi x₀) (dPi x₀ u) u := by
  have h0 := hasFDerivAt_Nk_aux x₀ 0 u
  have h1 := hasFDerivAt_Nk_aux x₀ 1 u
  have h2 := hasFDerivAt_Nk_aux x₀ 2 u
  have h3 := hasFDerivAt_Nk_aux x₀ 3 u
  have h4 := hasFDerivAt_Nk_aux x₀ 4 u
  have h34 := hasFDerivAt_mul_aux h3 h4
  have h234 := hasFDerivAt_mul_aux h2 h34
  have h1234 := hasFDerivAt_mul_aux h1 h234
  have h := hasFDerivAt_mul_aux h0 h1234
  convert h using 1
  · ext x; simp [Pi]
  · apply ContinuousLinearMap.ext
    intro δ
    simp only [dPi, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Pi.mul_apply]

/-! ## The main statement -/

/-- **S3**: `LPhi x₀ u` is the derivative of `Φ x₀ = (Re Θ, Im Θ, Π - 1)` at `u`. -/
theorem hasFDerivAt_Phi (x₀ : ℝ) (u : Work.SeedCert.E3) :
    HasFDerivAt (Work.SeedCert.Phi x₀) (Work.SeedCert.LPhi x₀ u) u := by
  have hZ := hasFDerivAt_Z_aux x₀ 5 u
  have hzOf := hasFDerivAt_zOf_aux u
  have hTheta : HasFDerivAt (Theta x₀) (LTheta x₀ u) u := by
    have h := hZ.sub hzOf
    change HasFDerivAt (Theta x₀) (LTheta x₀ u) u at h
    exact h
  have hPi := hasFDerivAt_Pi_aux x₀ u
  have h1 : HasFDerivAt (fun u => (Theta x₀ u).re) (Complex.reCLM.comp (LTheta x₀ u)) u :=
    (Complex.reCLM.hasFDerivAt (x := Theta x₀ u)).comp u hTheta
  have h2 : HasFDerivAt (fun u => (Theta x₀ u).im) (Complex.imCLM.comp (LTheta x₀ u)) u :=
    (Complex.imCLM.hasFDerivAt (x := Theta x₀ u)).comp u hTheta
  have h3 : HasFDerivAt (fun u => Pi x₀ u - 1) (dPi x₀ u) u := hPi.sub_const 1
  have h := h1.prodMk (h2.prodMk h3)
  change HasFDerivAt (Phi x₀) (LPhi x₀ u) u at h
  exact h

end

end Work.SeedCertNum
