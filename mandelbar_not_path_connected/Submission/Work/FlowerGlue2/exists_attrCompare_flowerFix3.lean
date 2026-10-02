import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue.ecalle_eq_ref_add_const
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

open Classical

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The comparison constant of the flower's attracting coordinate with a reference
coordinate** (the core of item N1 of `Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.3).

Both `fl.φa` and `R.φ` are attracting Fatou coordinates of the same parabolic germ
(`fl.φa_shift`: `φa ∘ Ft c₀ = φa + 1` on `fl.Pa`; `R.shift`: `R.φ ∘ Ft c₀ = R.φ + 1` on `R.P`),
and `Work.FlowerGlue.ecalle_eq_ref_add_const` identifies every Écalle coordinate with the
ℤ-saturating reference coordinate `R` up to one additive constant — this is the machine-checked
form of the classical uniqueness of the attracting Fatou coordinate at a simple parabolic point.

The conclusion is stated on the **intersection** `R.P ∩ fl.Pa` of the two petals, which is all
that the consumers (the asymptotic `AttrCompare.asymp`, and `box_deep_attr`) ever use: the
orbit-entry property is never needed, the constant is produced by the saturation of `R`. -/
theorem exists_const_φa_eq_ref (fl : Work.FatouCoordFix.ParabolicFlowerFix
      (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁) (R : Work.FlowerGlue.RefCoord d) :
    ∃ s : ℂ, ∀ z : ℂ, z ∈ R.P → z ∈ fl.Pa → fl.φa z = R.φ z + s := by
  set E : Work.FQC.EcalleData d := Work.FQC.EcalleData.ofFlower d fl with hE
  obtain ⟨s, hs⟩ := Work.FlowerGlue.ecalle_eq_ref_add_const R E
  have hEPa : E.Pa = fl.Pa := rfl
  have hEφa : E.φa = fl.φa := rfl
  refine ⟨s, fun z hzR hzPa => ?_⟩
  have h := hs z hzR 0 (by rw [hEPa]; exact hzPa)
  rw [hEφa] at h
  simpa using h

/-- **The attracting comparison datum (N1) exists for every flower**, given the reference
coordinate of the parameter normal form's chart (`hR`).

`hR` is the conclusion of `Work.FlowerGlue2.exists_refCoord_P_normalForm` (L0.6 of the design
note): a reference coordinate `Rf` whose asymptotic in the `c₀`-chart `w0 P` of `ParNormal` is
`approxCoord (P.κ c₀)` up to `O(1/Re w0)`, on the whole half-plane `Re w0 > N`.

The datum is assembled from
* the four dynamical fields of the flower (`fl.isOpen_Pa`, `mapsTo_Pa`, `tendsto_Pa`,
  `enters_Pa`) and the two coordinate fields (`fl.φa_fatou.2` injectivity, `fl.φa_shift`);
* `exists_const_φa_eq_ref`, which gives `fl.φa = Rf.φ + s` on `Rf.P ∩ fl.Pa`;
* `hR` itself, which supplies `Rf`, the depth `N`, the constant `K`, and both the petal
  membership `z ∈ Rf.P` and the asymptotic for `Rf.φ`.

The phase constant is `sa := s` and the error constant is `K` — no loss: on the relevant
half-plane the two `O(1/Re w0)` errors are literally the same function. -/
theorem exists_attrCompare_flowerFix3 {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (hR : ∃ Rf : Work.FlowerGlue.RefCoord d, ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧
      (∀ z : ℂ, z ≠ d.z₁ → N < (Work.FlowerGlue2.w0 P z).re → z ∈ Rf.P) ∧
      ∀ z : ℂ, z ≠ d.z₁ → N < (Work.FlowerGlue2.w0 P z).re →
        ‖Rf.φ z - Work.FatouCoord.approxCoord (P.κ c₀) (Work.FlowerGlue2.w0 P z)‖
          ≤ K / (Work.FlowerGlue2.w0 P z).re) :
    Nonempty (Work.FlowerGlue2.AttrCompare P fl.Pa fl.φa) := by
  obtain ⟨Rf, N, K, hN, hK, hmem, hasym⟩ := hR
  obtain ⟨s, hs⟩ := exists_const_φa_eq_ref fl Rf
  refine ⟨{ isOpen_Pa := fl.isOpen_Pa
            mapsTo_Pa := fl.mapsTo_Pa
            tendsto_Pa := fl.tendsto_Pa
            enters_Pa := fl.enters_Pa
            φa_inj := fl.φa_fatou.2
            φa_shift := fl.φa_shift
            Rf := Rf
            sa := s
            N := N
            K := K
            N_pos := hN
            K_nonneg := hK
            mem_P := hmem
            asymp := ?_ }⟩
  intro z hzPa hz1 hNw
  have hzx : fl.φa z = Rf.φ z + s := hs z (hmem z hz1 hNw) hzPa
  rw [hzx]
  have h2 := hasym z hz1 hNw
  convert h2 using 2
  ring

end

end Work.FlowerGlue2
