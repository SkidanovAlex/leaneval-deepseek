import Mathlib
import Submission.Work.SeedCertNum.Mat3
import Submission.Work.SeedCertNum.hasFDerivAt_Phi
import Submission.Work.SeedCertNum.mem_derPiX
import Submission.Work.SeedCertNum.mem_derPiY
import Submission.Work.SeedCertNum.mem_derPiT

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- **Every entry of `matOf (LPhi x₀ u)` lies in the interval matrix `Jint`** over the box
`Xz × Xt`.

`LPhi x₀ u = LTheta x₀ u` on the first two components and `dPi x₀ u` on the third, so the
`(0,·)`- and `(1,·)`-rows are the real and imaginary parts of `LTheta _ _ eX`, `eY`, `eT` and the
`(2,·)`-row is the `(x,y,t)`-partials of `Π`.  Unfolding `LTheta = LZ 5 - Lz` and
`LZ _ _ eX = p+q`, `LZ _ _ eY = i(p-q)`, `LZ _ _ eT = s`, `Lz eX = 1`, `Lz eY = i`, `Lz eT = 0`
identifies the rows with `Re/Im` of `(p+q-1)`, `i(p-q-1)`, `s`, while
`LTheta _ _ eX = LZ_eX - 1` etc. match the boxes `(boxPQ 5).1 ± (boxPQ 5).2` shifted by `oneBox`
and the box `boxS 5` built in `A1Defs.lean`; the third row is
`mem_derPiX`/`mem_derPiY`/`mem_derPiT`. -/
theorem jentry_mem_Jint {x₀ : Work.SeedCert.Dya} {Xt : Work.SeedCert.IV} {Xz : Work.SeedCert.CBox}
    {z : ℂ} {t : ℝ} (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) (i j : Fin 3) :
    Work.SeedCert.matOf (Work.SeedCert.LPhi x₀.toReal (Work.SeedCert.mkE z t)) i j ∈
      (Work.SeedCert.Jint (Work.SeedCert.pbox x₀ Xt) Xz i j).toSet := by
  have h1box : (1 : ℂ) ∈ oneBox.toSet := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [oneBox]
  fin_cases i <;> fin_cases j
  · -- `(0,0)`: `Re (p₅ + q₅ - 1)`
    have hpq : p x₀.toReal 5 (mkE z t) + q x₀.toReal 5 (mkE z t) ∈
        ((boxPQ (pbox x₀ Xt) Xz 5).1.add ((boxPQ (pbox x₀ Xt) Xz 5).2)).toSet :=
      CBox.mem_add (mem_boxP x₀ Xt Xz 5 hz ht) (mem_boxQ x₀ Xt Xz 5 hz ht)
    have hsub := CBox.mem_sub hpq h1box
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 0 0 =
        (p x₀.toReal 5 (mkE z t) + q x₀.toReal 5 (mkE z t) - 1).re from by
      simp [matOf, proj3_apply, LPhi, vec3, LTheta, LZ_eX, Lz_apply]]
    exact ⟨hsub.1, hsub.2.1⟩
  · -- `(0,1)`: `Re (i (p₅ - q₅ - 1)) = -Im (p₅ - q₅ - 1)`
    have hpq : p x₀.toReal 5 (mkE z t) - q x₀.toReal 5 (mkE z t) ∈
        ((boxPQ (pbox x₀ Xt) Xz 5).1.sub ((boxPQ (pbox x₀ Xt) Xz 5).2)).toSet :=
      CBox.mem_sub (mem_boxP x₀ Xt Xz 5 hz ht) (mem_boxQ x₀ Xt Xz 5 hz ht)
    have hsub := CBox.mem_sub hpq h1box
    have hneg : -(((p x₀.toReal 5 (mkE z t) - q x₀.toReal 5 (mkE z t)) - 1).im) ∈
        (IV.neg (((((boxPQ (pbox x₀ Xt) Xz 5).1).sub
          ((boxPQ (pbox x₀ Xt) Xz 5).2)).sub oneBox).im)).toSet :=
      IV.mem_neg ⟨hsub.2.2.1, hsub.2.2.2⟩
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 0 1 =
        -(((p x₀.toReal 5 (mkE z t) - q x₀.toReal 5 (mkE z t)) - 1).im) from by
      simp only [matOf, proj3_apply, LPhi, vec3, LTheta]
      simp [LZ_eY, Lz_apply, Complex.mul_re]]
    exact hneg
  · -- `(0,2)`: `Re s₅`
    have h := mem_boxS x₀ Xt Xz 5 hz ht
    have hre : (ss x₀.toReal 5 (mkE z t)).re ∈ ((boxS (pbox x₀ Xt) Xz 5).re).toSet :=
      ⟨h.1, h.2.1⟩
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 0 2 = (ss x₀.toReal 5 (mkE z t)).re from by
      simp [matOf, proj3_apply, LPhi, vec3, LTheta, LZ_eT, Lz_apply]]
    exact hre
  · -- `(1,0)`: `Im (p₅ + q₅ - 1)`
    have hpq : p x₀.toReal 5 (mkE z t) + q x₀.toReal 5 (mkE z t) ∈
        ((boxPQ (pbox x₀ Xt) Xz 5).1.add ((boxPQ (pbox x₀ Xt) Xz 5).2)).toSet :=
      CBox.mem_add (mem_boxP x₀ Xt Xz 5 hz ht) (mem_boxQ x₀ Xt Xz 5 hz ht)
    have hsub := CBox.mem_sub hpq h1box
    have him : (p x₀.toReal 5 (mkE z t) + q x₀.toReal 5 (mkE z t) - 1).im ∈
        (((((boxPQ (pbox x₀ Xt) Xz 5).1).add
          ((boxPQ (pbox x₀ Xt) Xz 5).2)).sub oneBox).im).toSet :=
      ⟨hsub.2.2.1, hsub.2.2.2⟩
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 1 0 =
        (p x₀.toReal 5 (mkE z t) + q x₀.toReal 5 (mkE z t) - 1).im from by
      simp [matOf, proj3_apply, LPhi, vec3, LTheta, LZ_eX, Lz_apply]]
    exact him
  · -- `(1,1)`: `Im (i (p₅ - q₅ - 1)) = Re (p₅ - q₅ - 1)`
    have hpq : p x₀.toReal 5 (mkE z t) - q x₀.toReal 5 (mkE z t) ∈
        ((boxPQ (pbox x₀ Xt) Xz 5).1.sub ((boxPQ (pbox x₀ Xt) Xz 5).2)).toSet :=
      CBox.mem_sub (mem_boxP x₀ Xt Xz 5 hz ht) (mem_boxQ x₀ Xt Xz 5 hz ht)
    have hsub := CBox.mem_sub hpq h1box
    have hre : ((p x₀.toReal 5 (mkE z t) - q x₀.toReal 5 (mkE z t)) - 1).re ∈
        (((((boxPQ (pbox x₀ Xt) Xz 5).1).sub
          ((boxPQ (pbox x₀ Xt) Xz 5).2)).sub oneBox).re).toSet :=
      ⟨hsub.1, hsub.2.1⟩
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 1 1 =
        ((p x₀.toReal 5 (mkE z t) - q x₀.toReal 5 (mkE z t)) - 1).re from by
      simp only [matOf, proj3_apply, LPhi, vec3, LTheta]
      simp [LZ_eY, Lz_apply, Complex.mul_im]]
    exact hre
  · -- `(1,2)`: `Im s₅`
    have h := mem_boxS x₀ Xt Xz 5 hz ht
    have him : (ss x₀.toReal 5 (mkE z t)).im ∈ ((boxS (pbox x₀ Xt) Xz 5).im).toSet :=
      ⟨h.2.2.1, h.2.2.2⟩
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 1 2 = (ss x₀.toReal 5 (mkE z t)).im from by
      simp [matOf, proj3_apply, LPhi, vec3, LTheta, LZ_eT, Lz_apply]]
    exact him
  · -- `(2,0)`: the `x`-partial of `Π`
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 2 0 = dPi x₀.toReal (mkE z t) eX from by
      simp [matOf, proj3_apply, LPhi, vec3]]
    exact mem_derPiX hz ht
  · -- `(2,1)`: the `y`-partial of `Π`
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 2 1 = dPi x₀.toReal (mkE z t) eY from by
      simp [matOf, proj3_apply, LPhi, vec3]]
    exact mem_derPiY hz ht
  · -- `(2,2)`: the `t`-partial of `Π`
    simp [Jint]
    rw [show matOf (LPhi x₀.toReal (mkE z t)) 2 2 = dPi x₀.toReal (mkE z t) eT from by
      simp [matOf, proj3_apply, LPhi, vec3]]
    exact mem_derPiT hz ht

end Work.SeedCertNum
