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

/-! ## Two elementary lemmas used for `mem_derPiY`

`Work.SeedCert.derPiY C X` is the interval `Work.SeedCert.nest (dYv C X) (boxNf C X)`, i.e. the
interval mirror of the *nested* product rule differentiating `Π = ∏_{k<5} N_k`.  The two lemmas
below are the general facts behind the single direction `∂/∂y`:

* `mem_nest` — soundness of the nested combination `Work.SeedCert.nest`, the interval mirror of the
  product rule;
* `dPi_eY_apply` — the unfolding of `Work.SeedCert.dPi` in the `eY`-direction. -/

/-- **Soundness of the nested product-rule combination `Work.SeedCert.nest`.**

If `dk k ∈ d k` and `nk k ∈ n k` for `k = 0,…,4`, then the nested product-rule combination
`dk₀·(nk₁·(nk₂·(nk₃nk₄))) + nk₀·(dk₁·(nk₂·(nk₃nk₄)) + nk₁·(dk₂·(nk₃nk₄) + nk₂·(dk₃nk₄ + nk₃dk₄)))`
lies in the interval combination `nest d n`, which is the same expression with the `dk`, `nk`
replaced by the intervals `d k`, `n k`.

Each product is enclosed by `Work.SeedCertNum.IV_mem_mul` and each sum by `IV.mem_add`; the
grouping of `nest` (a right-associated product, then a left-associated sum) is followed exactly. -/
private theorem mem_nest {d n : ℕ → IV} {dk nk : ℕ → ℝ}
    (hd : ∀ k, dk k ∈ (d k).toSet) (hn : ∀ k, nk k ∈ (n k).toSet) :
    dk 0 * (nk 1 * (nk 2 * (nk 3 * nk 4))) +
        nk 0 * (dk 1 * (nk 2 * (nk 3 * nk 4)) +
          nk 1 * (dk 2 * (nk 3 * nk 4) + nk 2 * (dk 3 * nk 4 + nk 3 * dk 4)))
      ∈ (Work.SeedCert.nest d n).toSet := by
  have h34 : nk 3 * nk 4 ∈ (IV.mul (n 3) (n 4)).toSet := IV_mem_mul (hn 3) (hn 4)
  have hG : dk 3 * nk 4 + nk 3 * dk 4 ∈
      (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4))).toSet :=
    IV.mem_add (IV_mem_mul (hd 3) (hn 4)) (IV_mem_mul (hn 3) (hd 4))
  have hF : dk 2 * (nk 3 * nk 4) ∈ (IV.mul (d 2) (IV.mul (n 3) (n 4))).toSet :=
    IV_mem_mul (hd 2) h34
  have hIn2 : dk 2 * (nk 3 * nk 4) + nk 2 * (dk 3 * nk 4 + nk 3 * dk 4) ∈
      (IV.add (IV.mul (d 2) (IV.mul (n 3) (n 4)))
        (IV.mul (n 2) (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4))))).toSet :=
    IV.mem_add hF (IV_mem_mul (hn 2) hG)
  have h234 : nk 2 * (nk 3 * nk 4) ∈ (IV.mul (n 2) (IV.mul (n 3) (n 4))).toSet :=
    IV_mem_mul (hn 2) h34
  have hE : dk 1 * (nk 2 * (nk 3 * nk 4)) ∈
      (IV.mul (d 1) (IV.mul (n 2) (IV.mul (n 3) (n 4)))).toSet :=
    IV_mem_mul (hd 1) h234
  have hIn1 : dk 1 * (nk 2 * (nk 3 * nk 4)) +
      nk 1 * (dk 2 * (nk 3 * nk 4) + nk 2 * (dk 3 * nk 4 + nk 3 * dk 4)) ∈
      (IV.add (IV.mul (d 1) (IV.mul (n 2) (IV.mul (n 3) (n 4))))
        (IV.mul (n 1) (IV.add (IV.mul (d 2) (IV.mul (n 3) (n 4)))
          (IV.mul (n 2) (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4))))))).toSet :=
    IV.mem_add hE (IV_mem_mul (hn 1) hIn2)
  have h234' : nk 1 * (nk 2 * (nk 3 * nk 4)) ∈
      (IV.mul (n 1) (IV.mul (n 2) (IV.mul (n 3) (n 4)))).toSet :=
    IV_mem_mul (hn 1) h234
  have hD : dk 0 * (nk 1 * (nk 2 * (nk 3 * nk 4))) ∈
      (IV.mul (d 0) (IV.mul (n 1) (IV.mul (n 2) (IV.mul (n 3) (n 4))))).toSet :=
    IV_mem_mul (hd 0) h234'
  have hOut : nk 0 * (dk 1 * (nk 2 * (nk 3 * nk 4)) +
      nk 1 * (dk 2 * (nk 3 * nk 4) + nk 2 * (dk 3 * nk 4 + nk 3 * dk 4))) ∈
      (IV.mul (n 0) (IV.add (IV.mul (d 1) (IV.mul (n 2) (IV.mul (n 3) (n 4))))
        (IV.mul (n 1) (IV.add (IV.mul (d 2) (IV.mul (n 3) (n 4)))
          (IV.mul (n 2) (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4)))))))).toSet :=
    IV_mem_mul (hn 0) hIn1
  simpa only [Work.SeedCert.nest] using IV.mem_add hD hOut

/-- **Unfolding of `Work.SeedCert.dPi` in the `eY`-direction.**  The nested product-rule
combination, written with the factor `dNk x₀ k u eY` on the *left* of each of the nested
products (matching the order produced by evaluating the `• dNk` terms of `dPi` on `eY`). -/
private theorem dPi_eY_apply (x₀ : ℝ) (u : E3) :
    Work.SeedCert.dPi x₀ u eY =
      dNk x₀ 0 u eY * (Nk x₀ 1 u * (Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u))) +
        Nk x₀ 0 u * (dNk x₀ 1 u eY * (Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u)) +
          Nk x₀ 1 u * (dNk x₀ 2 u eY * (Nk x₀ 3 u * Nk x₀ 4 u) +
            Nk x₀ 2 u * (dNk x₀ 3 u eY * Nk x₀ 4 u + Nk x₀ 3 u * dNk x₀ 4 u eY))) := by
  simp only [Work.SeedCert.dPi, add_apply, smul_apply, smul_eq_mul]
  ring

/-- The `y`-derivative of `Π` at a point of `Xz × Xt` lies in the interval `derPiY`.

This is the `∂/∂y` row of the Jacobian enclosure `Jint`: `mem_boxB` encloses
`conj(Z_k)·(p_k - q_k)` (whose imaginary part is `-∂_yN_k/8`), `dYv` turns that into an enclosure
of `∂_yN_k = dNk x₀ k u eY`, and `mem_nest` propagates the enclosures through the nested product
rule, which is `derPiY`. -/
theorem mem_derPiY {x₀ : Work.SeedCert.Dya} {Xt : Work.SeedCert.IV} {Xz : Work.SeedCert.CBox}
    {z : ℂ} {t : ℝ} (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    Work.SeedCert.dPi x₀.toReal (Work.SeedCert.mkE z t) Work.SeedCert.eY ∈
      (Work.SeedCert.derPiY (Work.SeedCert.pbox x₀ Xt) Xz).toSet := by
  -- `∂_y N_k = dNk x₀ k u eY` lies in `dYv C X k`
  have hd : ∀ k, dNk x₀.toReal k (mkE z t) eY ∈ (dYv (pbox x₀ Xt) Xz k).toSet := by
    intro k
    have hB := mem_boxB x₀ Xt Xz k hz ht
    have him : (star (Z x₀.toReal k (mkE z t)) *
        (p x₀.toReal k (mkE z t) - q x₀.toReal k (mkE z t))).im ∈
        ((boxB (pbox x₀ Xt) Xz k).im).toSet := ⟨hB.2.2.1, hB.2.2.2⟩
    have hmul := IV.mem_mulScalar (I := (boxB (pbox x₀ Xt) Xz k).im) him (a := Dya.ofInt 8)
    have hneg := IV.mem_neg hmul
    rw [dNk_eY]
    simpa [dYv] using hneg
  -- `N_k = Nk x₀ k u` lies in `boxNf C X k`
  have hn : ∀ k, Nk x₀.toReal k (mkE z t) ∈ (boxNf (pbox x₀ Xt) Xz k).toSet :=
    fun k => mem_boxNf x₀ Xt Xz k hz ht
  have hkey := mem_nest (d := dYv (pbox x₀ Xt) Xz) (n := boxNf (pbox x₀ Xt) Xz)
      (dk := fun k => dNk x₀.toReal k (mkE z t) eY)
      (nk := fun k => Nk x₀.toReal k (mkE z t)) hd hn
  rw [dPi_eY_apply (x₀ := x₀.toReal) (u := mkE z t)]
  exact hkey

end Work.SeedCertNum
