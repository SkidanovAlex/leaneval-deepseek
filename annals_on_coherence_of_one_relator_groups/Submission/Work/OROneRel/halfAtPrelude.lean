import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.rho_magnet
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.freiheitssatz_at

/-!
# The prelude shared by the two cases of Weinbaum's induction

This module holds the declarations shared between the exponent-sum-zero step
(`Submission.Work.OROneRel.weinbaum_sigma_zero_half`), the no-zero-exponent-sum step
(`Submission.Work.OROneRel.weinbaum_half_noZero`) and the descent lemma
(`Submission.Work.OROneRel.wneDescentNoHzB`), so that those modules can import one another's
ingredients without a cycle:

* `Work.OROneRel.HalfAt` : the half-length statement at a relator;
* `Work.OROneRel.not_isProperPower_mmW` : the Magnus rewriting of a relator which is not a proper
  power is not a proper power, in the decorated alphabet;
* the descent to the Magnus base (`mmBaseHom_injective`, `mmBaseHom_mk_eq_mk_rho`,
  `rho_magShiftAut`, `mk_mmW_eq_one_of_mk_eq_one`).
-/

namespace Work.OROneRel

universe u

/-- The **half-length statement** at a relator: every nontrivial subword of a power of `R` of length
at most half of `R` is nontrivial in `⟨β | R⟩`. -/
def HalfAt {α : Type u} (R : FreeGroup α) : Prop :=
  ∀ (k : ℕ) (w : FreeGroup α), IsSubwordOf w (R ^ k) → 2 * relatorNorm w ≤ relatorNorm R →
    w ≠ 1 → PresentedGroup.mk ({R} : Set (FreeGroup α)) w ≠ 1

/-! ### Supporting lemmas for the exponent-sum-zero step -/


/-- **The Magnus rewriting of a relator which is not a proper power is not a proper power**, in the
form in which the rewriting is viewed in the decorated alphabet `mmBeta z R` (the analogue for `mmW`
of `not_isProperPower_magRewRel`). -/
theorem not_isProperPower_mmW {β : Type u} {T : FreeGroup β} {y : β}
    (hpp : ¬ IsProperPower T) (hε : eps y T = 0) : ¬ IsProperPower (mmW y T) := by
  classical
  have hmr : rho y (magRewRel y T) = T := by
    rw [show magRewRel y T = magnet T y from by
      rw [magRewRel, magnet, magRew_zero_eq_rewrite]]
    exact rho_magnet T y hε
  rintro ⟨u, m, hm, hu⟩
  refine hpp ⟨rho y (FreeGroup.map (fun p : mmBeta y T =>
      ((p.1.1, p.1.2) : ({x : β // x ≠ y} × ℤ))) u), m, hm, ?_⟩
  have hmap : FreeGroup.map (fun p : mmBeta y T =>
        ((p.1.1, p.1.2) : ({x : β // x ≠ y} × ℤ))) (mmW y T) = magRewRel y T := by
    have h := mmW_map_val y T
    rw [show (fun p : mmBeta y T => ((p.1.1, p.1.2) : ({x : β // x ≠ y} × ℤ)))
        = (fun p : mmBeta y T => (p.1 : MMAlpha y)) from rfl] at h
    rw [h, magRewRel, show mmList y T = magRew y 0 T.toWord from rfl, magRew_zero_eq_rewrite]
  have hmain : T = (rho y (FreeGroup.map (fun p : mmBeta y T =>
      ((p.1.1, p.1.2) : ({x : β // x ≠ y} × ℤ))) u)) ^ m := by
    have h2 : rho y (FreeGroup.map (fun p : mmBeta y T =>
        ((p.1.1, p.1.2) : ({x : β // x ≠ y} × ℤ))) (u ^ m)) = T := by
      rw [show FreeGroup.map (fun p : mmBeta y T =>
            ((p.1.1, p.1.2) : ({x : β // x ≠ y} × ℤ))) (u ^ m) = magRewRel y T from by
          rw [← hu, hmap]]
      exact hmr
    calc T = rho y (FreeGroup.map (fun p : mmBeta y T =>
          ((p.1.1, p.1.2) : ({x : β // x ≠ y} × ℤ))) (u ^ m)) := h2.symm
      _ = (rho y (FreeGroup.map (fun p : mmBeta y T =>
          ((p.1.1, p.1.2) : ({x : β // x ≠ y} × ℤ))) u)) ^ m := by rw [map_pow, map_pow]
  exact hmain

/-! ### The descent to the Magnus base

`⟨β | R⟩` is isomorphic to the HNN extension `mmK z R` of the base `mmH z R = ⟨mmBeta z R | mmW z R⟩`
with stable letter `z` (`mmTheta`, `mmPsi`).  The base sits in the whole group through `mmBaseHom`,
which expands the decorated letter `(x, i)` to the conjugate `z ^ i * x * z ^ (-i)`:

* `mmBaseHom_injective` : the base injects in `⟨β | R⟩` (it is the composite of
  `HNNExtension.of` with the inverse of the isomorphism `mmTheta`);
* `mmBaseHom_mk_eq_mk_rho` : the two ways of pushing an element of `F(mmBeta z R)` into `⟨β | R⟩` —
  through the base, or through the expansion `rho` — agree.

Together with `rho_magnet` (`rho z (magRewRel z w) = w` when `σ_z w = 0`) these give the descent
`mk_mmW_eq_one_of_mk_eq_one`: an element of the base whose expansion is a conjugate of a trivial
element of `⟨β | R⟩` is itself trivial in the base. -/

section Descent

variable {β : Type u} {R : FreeGroup β} {z : β}

/-- The canonical map from the Magnus base `⟨mmBeta z R | mmW z R⟩` into `⟨β | R⟩` is injective. -/
theorem mmBaseHom_injective (hR1 : R ≠ 1) (hz : z ∈ relatorLetters R) (hε : eps z R = 0)
    (hcyc : IsCyclicallyReducedRelator R) :
    Function.Injective (mmBaseHom (t := z) (r := R) hε) := by
  classical
  have hFw : FreiheitssatzAt (mmW z R) := freiheitssatz_at _
  have hc : IsCyclicallyReducedRelator (mmW z R) := mmW_isCyclicallyReduced hcyc hε
  have hred : FreeGroup.IsReduced (mmWL z R) := mmWL_isReduced z R hcyc hε
  have hA : mmW z R ∉ Subgroup.closure (FreeGroup.of '' mmTA z R) :=
    mmW_notMem_closure_TA hR1 hz hε hred
  have hB : mmW z R ∉ Subgroup.closure (FreeGroup.of '' mmTB z R) :=
    mmW_notMem_closure_TB hR1 hz hε hred
  have hrel : FreeGroup.lift (mmThetaFun (r := R) hFw hc hA hB) R = 1 :=
    mmThetaFun_relator hε hFw hc hA hB
  have hinjΨ : Function.Injective (mmPsi (r := R) hε hFw hc hA hB) := by
    refine Function.LeftInverse.injective (g := mmTheta (r := R) hFw hc hA hB hrel) fun x => ?_
    have h := DFunLike.congr_fun (mmTheta_comp_mmPsi (r := R) hε hFw hc hA hB hrel) x
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  refine fun x y hxy => HNNExtension.of_injective _
    (hinjΨ ?_)
  rw [mmPsi_of (r := R) hε hFw hc hA hB, mmPsi_of (r := R) hε hFw hc hA hB]
  exact hxy

/-- The two ways of pushing an element of the free group on the decorated letters into `⟨β | R⟩`
agree: through the base of the Magnus decomposition, or through the expansion `rho`. -/
theorem mmBaseHom_mk_eq_mk_rho (hε : eps z R = 0) (u : FreeGroup (mmBeta z R)) :
    mmBaseHom (t := z) (r := R) hε
        (PresentedGroup.mk ({mmW z R} : Set (FreeGroup (mmBeta z R))) u)
      = PresentedGroup.mk ({R} : Set (FreeGroup β))
          (rho z (FreeGroup.map (fun p : mmBeta z R =>
            ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ))) u)) := by
  classical
  have hcomp : ((mmBaseHom (t := z) (r := R) hε).comp
        (PresentedGroup.mk ({mmW z R} : Set (FreeGroup (mmBeta z R)))))
      = ((PresentedGroup.mk ({R} : Set (FreeGroup β))).comp ((rho z).comp
          (FreeGroup.map (fun p : mmBeta z R =>
            ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ)))))) := by
    refine FreeGroup.ext_hom _ _ fun p => ?_
    simp only [MonoidHom.comp_apply, FreeGroup.map.of]
    change mmBaseHom (t := z) (r := R) hε (PresentedGroup.of p)
      = (PresentedGroup.mk ({R} : Set (FreeGroup β)))
          (rho z (FreeGroup.of (((p : mmBeta z R).1.1, (p : mmBeta z R).1.2) :
            ({x : β // x ≠ z} × ℤ))))
    rw [mmBaseHom_gen, rho_eq_magnusMap, magnusMap_apply, map_mul, map_mul, map_zpow, map_zpow]
    simp only [PresentedGroup.of]
  exact DFunLike.congr_fun hcomp u

/-- The expansion of a decoration shift is the conjugate by the corresponding power of `z`. -/
theorem rho_magShiftAut (j : ℤ) (y : FreeGroup ({x : β // x ≠ z} × ℤ)) :
    rho z (magShiftAut z j y) = FreeGroup.of z ^ j * rho z y * (FreeGroup.of z ^ j)⁻¹ := by
  have h := DFunLike.congr_fun (magConj_magnusMap z j) y
  simp only [MonoidHom.comp_apply] at h
  rw [← rho_eq_magnusMap] at h
  show rho z ((magShiftHom z j) y) = FreeGroup.of z ^ j * rho z y * (FreeGroup.of z ^ j)⁻¹
  rw [← h]
  simp [magConjHom]

/-- **Descent.**  An element of the Magnus base whose expansion is a conjugate of an element which is
trivial in `⟨β | R⟩` is itself trivial in the base. -/
theorem mk_mmW_eq_one_of_mk_eq_one (w : FreeGroup β) (hR1 : R ≠ 1) (hz : z ∈ relatorLetters R)
    (hε : eps z R = 0) (hcyc : IsCyclicallyReducedRelator R) (hεw : eps z w = 0)
    (hcontra : PresentedGroup.mk ({R} : Set (FreeGroup β)) w = 1)
    (j : ℤ) (u : FreeGroup (mmBeta z R))
    (hu : FreeGroup.map (fun p : mmBeta z R =>
        ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ))) u = magShiftAut z j (magRewRel z w)) :
    PresentedGroup.mk ({mmW z R} : Set (FreeGroup (mmBeta z R))) u = 1 := by
  classical
  have hinj := mmBaseHom_injective (z := z) (R := R) hR1 hz hε hcyc
  refine hinj ?_
  have hmr : rho z (magRewRel z w) = w := by
    rw [show magRewRel z w = magnet w z from by
      rw [magRewRel, magnet, magRew_zero_eq_rewrite]]
    exact rho_magnet w z hεw
  have hexp : rho z (FreeGroup.map (fun p : mmBeta z R =>
        ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ))) u)
      = FreeGroup.of z ^ j * w * (FreeGroup.of z ^ j)⁻¹ := by
    rw [hu, rho_magShiftAut (z := z) j (magRewRel z w), hmr]
  rw [mmBaseHom_mk_eq_mk_rho hε u, hexp, map_one]
  simp only [map_mul, map_inv, map_zpow]
  rw [hcontra]
  simp

end Descent

end Work.OROneRel
