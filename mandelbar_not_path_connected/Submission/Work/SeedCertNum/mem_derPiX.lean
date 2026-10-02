/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Soundness of `Work.SeedCert.derPiX` (the `x`-partial of `Π`)

Item **A1** of the `SeedCertNum` contract certifies the zero of the `ℝ³`-system `(P₁,P₂,P₃)` by
Krawczyk's criterion, which needs an interval enclosure of every entry of the Jacobian of
`Work.SeedCert.Phi` over the box `Xz × Xt`.  The `(2,0)`-entry is the `x`-partial of
`Π = ∏_{k<5} (2‖Z_k‖)²`, enclosed by `Work.SeedCert.derPiX`.

`Work.SeedCert.dPi` is the derivative of `Π` written in *nested* form (so that it mirrors
`Work.SeedCert.boxPi` factor by factor), and `Work.SeedCert.derPiX = nest dXv boxNf` is the
matching nested product-rule combination of the interval enclosures `dXv k` of `∂_x N_k` and
`boxNf k` of `N_k`.  The content of this file is that the evaluation `dPi x₀ u eX` at the
`x`-direction lies in `derPiX`.

* `mem_nest` — the general product-rule soundness lemma for the nested combination `nest`:
  if `D k ∈ d k` and `N k ∈ n k` for `k < 5` then the nested sum of products of the `D k`, `N k`
  lies in `nest d n`;
* `dPi_apply_eX` — unfolding of `dPi _ _ eX` into exactly that nested sum;
* `mem_derPiX` — the two together.
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

/-- **Soundness of the nested product-rule combination** `Work.SeedCert.nest`.

If `d k`, `n k` are intervals with `D k ∈ d k`, `N k ∈ n k` (`k < 5`) then

`D 0·(N 1·(N 2·(N 3·N 4))) + N 0·(D 1·(N 2·(N 3·N 4)) + N 1·(D 2·(N 3·N 4) + N 2·(D 3·N 4 + N 3·D 4)))`

lies in `nest d n`.  The products are grouped exactly as in the definition of
`Work.SeedCert.nest`, so that the proof is `IV.mem_add`/`IV_mem_mul` applied along the nesting
(with no use of commutativity of `IV.mul`). -/
private theorem mem_nest {d n : ℕ → IV} {D N : ℕ → ℝ}
    (hD : ∀ k, D k ∈ (d k).toSet) (hN : ∀ k, N k ∈ (n k).toSet) :
    D 0 * (N 1 * (N 2 * (N 3 * N 4)))
      + N 0 * (D 1 * (N 2 * (N 3 * N 4))
        + N 1 * (D 2 * (N 3 * N 4) + N 2 * (D 3 * N 4 + N 3 * D 4)))
      ∈ (nest d n).toSet := by
  have h34 : N 3 * N 4 ∈ (IV.mul (n 3) (n 4)).toSet := IV_mem_mul (hN 3) (hN 4)
  have h234 : N 2 * (N 3 * N 4) ∈ (IV.mul (n 2) (IV.mul (n 3) (n 4))).toSet :=
    IV_mem_mul (hN 2) h34
  have h1234 : N 1 * (N 2 * (N 3 * N 4)) ∈
      (IV.mul (n 1) (IV.mul (n 2) (IV.mul (n 3) (n 4)))).toSet := IV_mem_mul (hN 1) h234
  have ht0 : D 0 * (N 1 * (N 2 * (N 3 * N 4))) ∈
      (IV.mul (d 0) (IV.mul (n 1) (IV.mul (n 2) (IV.mul (n 3) (n 4))))).toSet :=
    IV_mem_mul (hD 0) h1234
  have hd1 : D 1 * (N 2 * (N 3 * N 4)) ∈
      (IV.mul (d 1) (IV.mul (n 2) (IV.mul (n 3) (n 4)))).toSet := IV_mem_mul (hD 1) h234
  have hd2 : D 2 * (N 3 * N 4) ∈ (IV.mul (d 2) (IV.mul (n 3) (n 4))).toSet :=
    IV_mem_mul (hD 2) h34
  have hd3 : D 3 * N 4 ∈ (IV.mul (d 3) (n 4)).toSet := IV_mem_mul (hD 3) (hN 4)
  have hd4 : N 3 * D 4 ∈ (IV.mul (n 3) (d 4)).toSet := IV_mem_mul (hN 3) (hD 4)
  have e1 := IV.mem_add hd1
    (IV_mem_mul (hN 1) (IV.mem_add hd2 (IV_mem_mul (hN 2) (IV.mem_add hd3 hd4))))
  have e2 := IV_mem_mul (hN 0) e1
  simpa only [nest] using IV.mem_add ht0 e2

/-- **Unfolding of `dPi _ _ eX`**: the derivative of the nested product `Π`, applied to the
`x`-direction `eX`.  Each factor `Nk k` is differentiated by `dNk k`, and the smul-chain of
`Work.SeedCert.dPi` produces exactly the nested sum of `Work.SeedCert.mem_nest` (up to
commutativity of the product of real numbers). -/
private theorem dPi_apply_eX (x₀ : ℝ) (u : E3) :
    dPi x₀ u eX =
      (Nk x₀ 1 u * (Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u))) * dNk x₀ 0 u eX
      + Nk x₀ 0 u * ((Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u)) * dNk x₀ 1 u eX
        + Nk x₀ 1 u * ((Nk x₀ 3 u * Nk x₀ 4 u) * dNk x₀ 2 u eX
          + Nk x₀ 2 u * (Nk x₀ 4 u * dNk x₀ 3 u eX + Nk x₀ 3 u * dNk x₀ 4 u eX))) := by
  simp only [dPi, add_apply, smul_apply, smul_eq_mul]

/-- **Soundness of `Work.SeedCert.derPiX`**: the `x`-partial of `Π` at a point of the box.

If `z ∈ Xz` and `t ∈ Xt` then `(dPi x₀ (mkE z t)) eX` lies in the interval
`Work.SeedCert.derPiX (pbox x₀ Xt) Xz`.

Proof: `dNk k u eX = 8·Re(conj(Z_k)·(p_k+q_k))` (`dNk_eX`) and
`conj(Z_k)·(p_k+q_k) ∈ boxA k` (`mem_boxA`), so `dNk k u eX ∈ dXv k` (`IV.mem_mulScalar` on the
real part); `Nk k u ∈ boxNf k` (`mem_boxNf`); apply the nested product-rule lemma `mem_nest`
after unfolding `dPi _ _ eX` (`dPi_apply_eX`). -/
theorem mem_derPiX {x₀ : Work.SeedCert.Dya} {Xt : Work.SeedCert.IV} {Xz : Work.SeedCert.CBox}
    {z : ℂ} {t : ℝ} (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    Work.SeedCert.dPi x₀.toReal (Work.SeedCert.mkE z t) Work.SeedCert.eX ∈
      (Work.SeedCert.derPiX (Work.SeedCert.pbox x₀ Xt) Xz).toSet := by
  have hD : ∀ k : ℕ, dNk x₀.toReal k (mkE z t) eX ∈
      (dXv (pbox x₀ Xt) Xz k).toSet := by
    intro k
    have hA := mem_boxA x₀ Xt Xz k hz ht
    have hre : (star (Z x₀.toReal k (mkE z t)) *
        (p x₀.toReal k (mkE z t) + q x₀.toReal k (mkE z t))).re ∈
        ((boxA (pbox x₀ Xt) Xz k).re).toSet := ⟨hA.1, hA.2.1⟩
    have h8 := IV.mem_mulScalar (I := (boxA (pbox x₀ Xt) Xz k).re) hre (a := Dya.ofInt 8)
    rw [dNk_eX]
    simpa [dXv] using h8
  have hN : ∀ k : ℕ, Nk x₀.toReal k (mkE z t) ∈ (boxNf (pbox x₀ Xt) Xz k).toSet :=
    fun k => mem_boxNf x₀ Xt Xz k hz ht
  have hnum := mem_nest (d := fun k => dXv (pbox x₀ Xt) Xz k)
    (n := fun k => boxNf (pbox x₀ Xt) Xz k)
    (D := fun k => dNk x₀.toReal k (mkE z t) eX)
    (N := fun k => Nk x₀.toReal k (mkE z t)) hD hN
  rw [derPiX]
  convert hnum using 1
  rw [dPi_apply_eX]
  ring

end Work.SeedCertNum
