import Mathlib
import Submission.Work.SeedCertNum.A1Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Soundness of the interval enclosure `derPiT` of `∂_t Π`

`Work.SeedCert.dPi x₀ u eT` is the `t`-partial of the product `Π = ∏_{k<5} 4‖Z_k‖²` at `u`,
and `Work.SeedCert.derPiT (pbox x₀ Xt) Xz = nest (dTv …) (boxNf …)` is the interval
enclosure of that partial derivative over the box `Xz × Xt` (`A1Defs.lean`).

This file proves the soundness statement `mem_derPiT`: for every `z ∈ Xz.toSet` and
`t ∈ Xt.toSet`,

`dPi x₀.toReal (mkE z t) eT ∈ (derPiT (pbox x₀ Xt) Xz).toSet`.

The proof evaluates `dPi _ _ eT` in the nested shape mirrored by `nest` (`dPi_apply_eT`), then
feeds the five enclosures `Nk … ∈ boxNf …` (`mem_boxNf`) and
`dNk … eT ∈ dTv …` (from `dNk_eT`, `mem_boxC`, `IV.mem_mulScalar`) through the interval
product rule (`Work.SeedCertNum.IV_mem_mul`) and interval addition (`IV.mem_add`), in the same
nesting order as `nest` itself (`mem_nest`).
-/

namespace Work.SeedCertNum

open Work.SeedCert

/-- Membership of the real part: `z ∈ B` implies `z.re ∈ B.re`. -/
private theorem mem_re {B : CBox} {z : ℂ} (hz : z ∈ B.toSet) : z.re ∈ (B.re).toSet :=
  ⟨hz.1, hz.2.1⟩

/-- The `t`-partial `dPi x₀ u eT` of the product `Π`, written out in the nested shape that the
interval expression `nest` mirrors. -/
private theorem dPi_apply_eT (x₀ : ℝ) (u : E3) :
    dPi x₀ u eT =
      dNk x₀ 0 u eT * (Nk x₀ 1 u * (Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u)))
      + Nk x₀ 0 u *
          (dNk x₀ 1 u eT * (Nk x₀ 2 u * (Nk x₀ 3 u * Nk x₀ 4 u))
            + Nk x₀ 1 u *
                (dNk x₀ 2 u eT * (Nk x₀ 3 u * Nk x₀ 4 u)
                  + Nk x₀ 2 u * (dNk x₀ 3 u eT * Nk x₀ 4 u + Nk x₀ 3 u * dNk x₀ 4 u eT))) := by
  simp only [dPi, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The nested product rule, at the level of interval enclosures: if `D k ∈ d k` and `A k ∈ n k`
for all `k`, then the nested combination

`D₀A₁A₂A₃A₄ + A₀(D₁A₂A₃A₄ + A₁(D₂A₃A₄ + A₂(D₃A₄ + A₃D₄)))`

lies in the interval `nest d n`. -/
private theorem mem_nest {d n : ℕ → IV} {A D : ℕ → ℝ}
    (hD : ∀ k, D k ∈ (d k).toSet) (hA : ∀ k, A k ∈ (n k).toSet) :
    D 0 * (A 1 * (A 2 * (A 3 * A 4)))
        + A 0 * (D 1 * (A 2 * (A 3 * A 4))
          + A 1 * (D 2 * (A 3 * A 4) + A 2 * (D 3 * A 4 + A 3 * D 4))) ∈
      (nest d n).toSet := by
  have h34 : A 3 * A 4 ∈ (IV.mul (n 3) (n 4)).toSet :=
    IV_mem_mul (hA 3) (hA 4)
  have h234 : A 2 * (A 3 * A 4) ∈ (IV.mul (n 2) (IV.mul (n 3) (n 4))).toSet :=
    IV_mem_mul (hA 2) h34
  have h1234 : A 1 * (A 2 * (A 3 * A 4)) ∈
      (IV.mul (n 1) (IV.mul (n 2) (IV.mul (n 3) (n 4)))).toSet :=
    IV_mem_mul (hA 1) h234
  have h0 : D 0 * (A 1 * (A 2 * (A 3 * A 4))) ∈
      (IV.mul (d 0) (IV.mul (n 1) (IV.mul (n 2) (IV.mul (n 3) (n 4))))).toSet :=
    IV_mem_mul (hD 0) h1234
  have hi34 : D 3 * A 4 + A 3 * D 4 ∈
      (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4))).toSet :=
    IV.mem_add (IV_mem_mul (hD 3) (hA 4)) (IV_mem_mul (hA 3) (hD 4))
  have hi2 : D 2 * (A 3 * A 4) + A 2 * (D 3 * A 4 + A 3 * D 4) ∈
      (IV.add (IV.mul (d 2) (IV.mul (n 3) (n 4)))
        (IV.mul (n 2) (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4))))).toSet :=
    IV.mem_add (IV_mem_mul (hD 2) h34) (IV_mem_mul (hA 2) hi34)
  have hi1 : D 1 * (A 2 * (A 3 * A 4)) + A 1 * (D 2 * (A 3 * A 4) + A 2 * (D 3 * A 4 + A 3 * D 4))
      ∈ (IV.add (IV.mul (d 1) (IV.mul (n 2) (IV.mul (n 3) (n 4))))
          (IV.mul (n 1)
            (IV.add (IV.mul (d 2) (IV.mul (n 3) (n 4)))
              (IV.mul (n 2) (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4))))))).toSet :=
    IV.mem_add (IV_mem_mul (hD 1) h234) (IV_mem_mul (hA 1) hi2)
  have h1 : A 0 * (D 1 * (A 2 * (A 3 * A 4)) + A 1 * (D 2 * (A 3 * A 4) + A 2 * (D 3 * A 4 + A 3 * D 4)))
      ∈ (IV.mul (n 0)
          (IV.add (IV.mul (d 1) (IV.mul (n 2) (IV.mul (n 3) (n 4))))
            (IV.mul (n 1)
              (IV.add (IV.mul (d 2) (IV.mul (n 3) (n 4)))
                (IV.mul (n 2) (IV.add (IV.mul (d 3) (n 4)) (IV.mul (n 3) (d 4)))))))).toSet :=
    IV_mem_mul (hA 0) hi1
  exact IV.mem_add h0 h1

theorem mem_derPiT {x₀ : Work.SeedCert.Dya} {Xt : Work.SeedCert.IV} {Xz : Work.SeedCert.CBox}
    {z : ℂ} {t : ℝ} (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    Work.SeedCert.dPi x₀.toReal (Work.SeedCert.mkE z t) Work.SeedCert.eT ∈
      (Work.SeedCert.derPiT (Work.SeedCert.pbox x₀ Xt) Xz).toSet := by
  -- the five box enclosures of `Nk`
  have hn : ∀ k : ℕ, Nk x₀.toReal k (mkE z t) ∈ (boxNf (pbox x₀ Xt) Xz k).toSet :=
    fun k => mem_boxNf x₀ Xt Xz k hz ht
  -- the five box enclosures of `∂_t Nk`
  have hd : ∀ k : ℕ, dNk x₀.toReal k (mkE z t) eT ∈ (dTv (pbox x₀ Xt) Xz k).toSet := by
    intro k
    have h := IV.mem_mulScalar (I := (boxC (pbox x₀ Xt) Xz k).re)
      (mem_re (mem_boxC x₀ Xt Xz k hz ht)) (a := Dya.ofInt 8)
    simpa [dNk_eT, dTv, Dya.toReal_ofInt] using h
  rw [dPi_apply_eT]
  exact mem_nest hd hn

end Work.SeedCertNum
