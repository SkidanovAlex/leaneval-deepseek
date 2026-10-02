/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# The `(P₁,P₂,P₃)` system of item A1: definitions

Item **A1** of the `SeedCertNum` contract (`NOTES_LEAD_mandelbar_noncusp.md` §2.2) certifies the
unique zero `(z₁, c_b)` of

  `P₁ = Re (g z - z)`,  `P₂ = Im (g z - z)`,  `P₃ = ∏_{k<5} (2‖T_c^k z‖)² - 1`,
  `g = (T_c)^[5]`,  `c = x₀ + it`  (`x₀ : ℚ` fixed),

by Krawczyk's criterion.  This file fixes the objects: the iterate `Z` and its jets come from
`Submission/Work/SeedCertNum/Jet1.lean`; here we add

* `Nk`, `Pi` — the product `∏_{k<5} 4‖Z_k‖²` (so `P₃ = Pi - 1`) and its derivative `dPi`;
  both are written as *nested* products so that the interval mirror `nest` of the box layer
  matches them factor by factor;
* `boxNf`, `boxPi` and the ingredients `boxA`, `boxB`, `boxC` of the partial derivatives of `Pi`
  (`∂_x N_k = 8 Re (conj Z_k (p_k+q_k))`, `∂_y N_k = -8 Im (conj Z_k (p_k-q_k))`,
  `∂_t N_k = 8 Re (conj Z_k s_k)`), together with `derPiX`, `derPiY`, `derPiT`;
* `Theta`, `Phi` — the map `ℝ³ → ℝ³`, and `LTheta`, `LPhi` — its derivative;
* `Jint` — the `3×3` interval matrix enclosing the Jacobian of `Phi` over a box.

The soundness statements are `mem_Pi`, `mem_derPiX`, `mem_derPiY`, `mem_derPiT`,
`hasFDerivAt_Pi`, `hasFDerivAt_Phi` and the entrywise enclosure `fderiv_Phi_mem_Jint`.
-/
import Mathlib
import Submission.Work.SeedCertNum.Jet1
import Submission.Work.SeedCertNum.IV_mem_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## The product `Π = ∏_{k<5} (2‖Z_k‖)²` and its derivative -/

/-- `N_k(u) = 4‖Z_k(u)‖² = (2‖Z_k(u)‖)²`. -/
def Nk (x₀ : ℝ) (k : ℕ) (u : E3) : ℝ := 4 * ‖Z x₀ k u‖ ^ 2

/-- `Π(u) = ∏_{k<5} (2‖Z_k(u)‖)²`, in the nested form the box layer mirrors. -/
def Pi (x₀ : ℝ) (u : E3) : ℝ :=
  Nk x₀ 0 u * (Nk x₀ 1 u * (Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u)))

/-- The derivative of `N_k`: `δ ↦ 8 (Re Z_k · (LZ_k δ).re + Im Z_k · (LZ_k δ).im)`. -/
def dNk (x₀ : ℝ) (k : ℕ) (u : E3) : E3 →L[ℝ] ℝ :=
  (8 * (Z x₀ k u).re) • (Complex.reCLM.comp (LZ x₀ k u))
    + (8 * (Z x₀ k u).im) • (Complex.imCLM.comp (LZ x₀ k u))

/-- The derivative of `Π`, in the nested form matching `Pi`. -/
def dPi (x₀ : ℝ) (u : E3) : E3 →L[ℝ] ℝ :=
  (Nk x₀ 1 u * (Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u))) • dNk x₀ 0 u
    + Nk x₀ 0 u •
        ((Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u)) • dNk x₀ 1 u
          + Nk x₀ 1 u •
              ((Nk x₀ 3 u * Nk x₀ 4 u) • dNk x₀ 2 u
                + Nk x₀ 2 u • (Nk x₀ 4 u • dNk x₀ 3 u + Nk x₀ 3 u • dNk x₀ 4 u)))

/-- The `x`-partial of `N_k`. -/
theorem dNk_eX (x₀ : ℝ) (k : ℕ) (u : E3) :
    dNk x₀ k u eX = 8 * (star (Z x₀ k u) * (p x₀ k u + q x₀ k u)).re := by
  simp only [dNk, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, LZ_eX, smul_eq_mul]
  simp [Complex.mul_re]
  ring

/-- The `y`-partial of `N_k`. -/
theorem dNk_eY (x₀ : ℝ) (k : ℕ) (u : E3) :
    dNk x₀ k u eY = -8 * (star (Z x₀ k u) * (p x₀ k u - q x₀ k u)).im := by
  simp only [dNk, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, LZ_eY, smul_eq_mul]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The `t`-partial of `N_k`. -/
theorem dNk_eT (x₀ : ℝ) (k : ℕ) (u : E3) :
    dNk x₀ k u eT = 8 * (star (Z x₀ k u) * ss x₀ k u).re := by
  simp only [dNk, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, LZ_eT, smul_eq_mul]
  simp [Complex.mul_re]
  ring

/-! ## The box layer for `Π` and its derivatives -/

/-- A box containing `1`, as a complex box (for the `-1` of `P₃` and `p+q-1`). -/
def oneBox : CBox := ⟨Dya.one, Dya.one, Dya.zero, Dya.zero⟩

/-- The interval enclosure of `N_k = 4‖Z_k‖²` over `Xz × Xt`. -/
def boxNf (Ctyp Xz : CBox) (k : ℕ) : IV :=
  IV.mulScalar (Dya.ofInt 4) ((boxV Ctyp Xz k).normSq)

/-- The interval enclosure of `Π` (nested form). -/
def boxPi (Ctyp Xz : CBox) : IV :=
  IV.mul (boxNf Ctyp Xz 0)
    (IV.mul (boxNf Ctyp Xz 1)
      (IV.mul (boxNf Ctyp Xz 2) (IV.mul (boxNf Ctyp Xz 3) (boxNf Ctyp Xz 4))))

/-- The box enclosure of `conj(Z_k)·(p_k + q_k)`, whose real part is `∂_x N_k / 8`. -/
def boxA (Ctyp Xz : CBox) (k : ℕ) : CBox :=
  ((boxV Ctyp Xz k).conj).mul (((boxPQ Ctyp Xz k).1).add ((boxPQ Ctyp Xz k).2))

/-- The box enclosure of `conj(Z_k)·(p_k - q_k)`, whose imaginary part is `-∂_y N_k / 8`. -/
def boxB (Ctyp Xz : CBox) (k : ℕ) : CBox :=
  ((boxV Ctyp Xz k).conj).mul (((boxPQ Ctyp Xz k).1).sub ((boxPQ Ctyp Xz k).2))

/-- The box enclosure of `conj(Z_k)·s_k`, whose real part is `∂_t N_k / 8`. -/
def boxC (Ctyp Xz : CBox) (k : ℕ) : CBox :=
  ((boxV Ctyp Xz k).conj).mul (boxS Ctyp Xz k)

/-- The interval `8·(boxA_k).re`, enclosing `∂_x N_k`. -/
def dXv (Ctyp Xz : CBox) (k : ℕ) : IV := IV.mulScalar (Dya.ofInt 8) ((boxA Ctyp Xz k).re)

/-- The interval `-8·(boxB_k).im`, enclosing `∂_y N_k`. -/
def dYv (Ctyp Xz : CBox) (k : ℕ) : IV := IV.neg (IV.mulScalar (Dya.ofInt 8) ((boxB Ctyp Xz k).im))

/-- The interval `8·(boxC_k).re`, enclosing `∂_t N_k`. -/
def dTv (Ctyp Xz : CBox) (k : ℕ) : IV := IV.mulScalar (Dya.ofInt 8) ((boxC Ctyp Xz k).re)

/-- The nested product-rule combination
`d₀·N₁N₂N₃N₄ + N₀·(d₁·N₂N₃N₄ + N₁·(d₂·N₃N₄ + N₂·(d₃N₄ + N₃d₄)))`. -/
def nest (d n : ℕ → IV) : IV :=
  IV.add (IV.mul (d 0) (IV.mul (n 1) (IV.mul (n 2) (IV.mul (n 3) (n 4)))))
    (IV.mul (n 0)
      (IV.add (IV.mul (d 1) (IV.mul (n 2) (IV.mul (n 3) (n 4))))
        (IV.mul (n 1)
          (IV.add (IV.mul (d 2) (IV.mul (n 3) (n 4)))
            (IV.mul (n 2) (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4))))))))

/-- The interval enclosure of `∂_x Π` over `Xz × Xt`. -/
def derPiX (Ctyp Xz : CBox) : IV := nest (dXv Ctyp Xz) (boxNf Ctyp Xz)

/-- The interval enclosure of `∂_y Π` over `Xz × Xt`. -/
def derPiY (Ctyp Xz : CBox) : IV := nest (dYv Ctyp Xz) (boxNf Ctyp Xz)

/-- The interval enclosure of `∂_t Π` over `Xz × Xt`. -/
def derPiT (Ctyp Xz : CBox) : IV := nest (dTv Ctyp Xz) (boxNf Ctyp Xz)

/-! ### Soundness of the `Π`-layer (elementary, proved here) -/

theorem mem_boxNf (x₀ : Dya) (Xt : IV) (Xz : CBox) (k : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    Nk x₀.toReal k (mkE z t) ∈ (boxNf (pbox x₀ Xt) Xz k).toSet := by
  have hV := mem_boxV x₀ Xt Xz k hz ht
  have h := IV.mem_mulScalar (I := (boxV (pbox x₀ Xt) Xz k).normSq) (CBox.mem_normSq hV)
    (a := Dya.ofInt 4)
  simpa [boxNf, Nk, Dya.toReal_ofInt] using h

theorem mem_boxPi (x₀ : Dya) (Xt : IV) (Xz : CBox) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    Pi x₀.toReal (mkE z t) ∈ (boxPi (pbox x₀ Xt) Xz).toSet := by
  have h0 := mem_boxNf x₀ Xt Xz 0 hz ht
  have h1 := mem_boxNf x₀ Xt Xz 1 hz ht
  have h2 := mem_boxNf x₀ Xt Xz 2 hz ht
  have h3 := mem_boxNf x₀ Xt Xz 3 hz ht
  have h4 := mem_boxNf x₀ Xt Xz 4 hz ht
  have h34 := Work.SeedCertNum.IV_mem_mul h3 h4
  have h234 := Work.SeedCertNum.IV_mem_mul h2 h34
  have h1234 := Work.SeedCertNum.IV_mem_mul h1 h234
  have h := Work.SeedCertNum.IV_mem_mul h0 h1234
  simpa [boxPi, Pi] using h

theorem mem_boxA (x₀ : Dya) (Xt : IV) (Xz : CBox) (k : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    star (Z x₀.toReal k (mkE z t)) *
        (p x₀.toReal k (mkE z t) + q x₀.toReal k (mkE z t))
      ∈ (boxA (pbox x₀ Xt) Xz k).toSet :=
  Work.SeedCertNum.CBox_mem_mul (CBox.mem_conj (mem_boxV x₀ Xt Xz k hz ht))
    (CBox.mem_add (mem_boxP x₀ Xt Xz k hz ht) (mem_boxQ x₀ Xt Xz k hz ht))

theorem mem_boxB (x₀ : Dya) (Xt : IV) (Xz : CBox) (k : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    star (Z x₀.toReal k (mkE z t)) *
        (p x₀.toReal k (mkE z t) - q x₀.toReal k (mkE z t))
      ∈ (boxB (pbox x₀ Xt) Xz k).toSet :=
  Work.SeedCertNum.CBox_mem_mul (CBox.mem_conj (mem_boxV x₀ Xt Xz k hz ht))
    (CBox.mem_sub (mem_boxP x₀ Xt Xz k hz ht) (mem_boxQ x₀ Xt Xz k hz ht))

theorem mem_boxC (x₀ : Dya) (Xt : IV) (Xz : CBox) (k : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    star (Z x₀.toReal k (mkE z t)) * ss x₀.toReal k (mkE z t)
      ∈ (boxC (pbox x₀ Xt) Xz k).toSet :=
  Work.SeedCertNum.CBox_mem_mul (CBox.mem_conj (mem_boxV x₀ Xt Xz k hz ht))
    (mem_boxS x₀ Xt Xz k hz ht)

/-! ## The map `Φ` and its derivative -/

/-- `Θ(u) = Z_5(u) - z(u)`, the complex form of `(P₁,P₂)`. -/
def Theta (x₀ : ℝ) (u : E3) : ℂ := Z x₀ 5 u - zOf u

/-- The derivative of `Θ`: `LΘ = LZ_5 - Lz`. -/
def LTheta (x₀ : ℝ) (u : E3) : E3 →L[ℝ] ℂ := LZ x₀ 5 u - Lz

/-- `Φ(u) = (Re Θ, Im Θ, Π - 1) : ℝ³ → ℝ³`. -/
def Phi (x₀ : ℝ) (u : E3) : E3 :=
  ((Theta x₀ u).re, (Theta x₀ u).im, Pi x₀ u - 1)

/-- The derivative of `Φ`. -/
def LPhi (x₀ : ℝ) (u : E3) : E3 →L[ℝ] E3 :=
  (Complex.reCLM.comp (LTheta x₀ u)).prod
    ((Complex.imCLM.comp (LTheta x₀ u)).prod (dPi x₀ u))

/-- The `3×3` interval matrix enclosing the Jacobian of `Φ` over `Xz × Xt`. -/
def Jint (Ctyp Xz : CBox) (i j : Fin 3) : IV :=
  let PQ0 := ((boxPQ Ctyp Xz 5).1).sub (boxPQ Ctyp Xz 5).2
  let PQ1 := ((boxPQ Ctyp Xz 5).1).add (boxPQ Ctyp Xz 5).2
  if i = 0 ∧ j = 0 then (PQ1.sub oneBox).re
  else if i = 0 ∧ j = 1 then IV.neg ((PQ0.sub oneBox).im)
  else if i = 0 ∧ j = 2 then (boxS Ctyp Xz 5).re
  else if i = 1 ∧ j = 0 then (PQ1.sub oneBox).im
  else if i = 1 ∧ j = 1 then (PQ0.sub oneBox).re
  else if i = 1 ∧ j = 2 then (boxS Ctyp Xz 5).im
  else if i = 2 ∧ j = 0 then derPiX Ctyp Xz
  else if i = 2 ∧ j = 1 then derPiY Ctyp Xz
  else derPiT Ctyp Xz

end

end Work.SeedCert
