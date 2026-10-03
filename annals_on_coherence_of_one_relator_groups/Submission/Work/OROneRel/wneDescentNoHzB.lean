import Mathlib
import Submission.Work.OROneRel.halfAtPrelude
import Submission.Work.OROneRel.magRew_attach_of_notMem
import Submission.Work.OROneRel.mmStepData_of_expsum_zero

namespace Work.OROneRel

universe u

variable {β : Type u}

/-! ## The descent to the Magnus base, when the stable letter does not occur in the relator

`Work.OROneRel.mk_mmW_eq_one_of_mk_eq_one` proves the descent

  "`u` is a subword of the base whose expansion is the Magnus rewriting of `w`; if `w` is trivial in
  `⟨β | R⟩` then `u` is trivial in the base `⟨mmW z R⟩`"

under the hypothesis `z ∈ relatorLetters R`.  This module removes that hypothesis.

The proof splits: if `z` does occur in `R` we are done by the existing descent.  If `z` does not occur
in `R`, then (by `Work.OROneRel.magRew_attach_of_notMem`) *all* decorations of the Magnus rewriting of
`R` are `0`; consequently `mmDecSet z R` is the level-`0` slice, the associated sets `mmTA z R`,
`mmTB z R` are empty, and the injectivity of `mmBaseHom` -- the only place where the hypothesis
`z ∈ relatorLetters R` is used inside the MMP decomposition, through
`Work.OROneRel.mmW_notMem_closure_TA` -- follows from `mmW z R ≠ 1`. -/

/-- If `z` does not occur in `R`, all decorations of the Magnus rewriting of `R` are `0`. -/
theorem wne_mmList_snd_eq_zero {z : β} {R : FreeGroup β} (hz : z ∉ relatorLetters R) :
    ∀ q ∈ mmList z R, q.1.2 = 0 := by
  classical
  have hL : ∀ p ∈ FreeGroup.toWord R, p.1 ≠ z := by
    intro p hp h
    exact hz (by rw [relatorLetters]; exact ⟨p.2, h ▸ hp⟩)
  have h1 : mmList z R = (FreeGroup.toWord R).attach.map
      (fun q => (((⟨q.1.1, hL q.1 q.2⟩, 0) : {x : β // x ≠ z} × ℤ), q.1.2)) :=
    magRew_attach_of_notMem z 0 (FreeGroup.toWord R) hL
  intro q hq
  rw [h1] at hq
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hq
  rfl

/-- In the non-degenerate case every element of `mmBeta z R` has decoration `0`. -/
theorem wne_mmDecs_eq_zero {z : β} {R : FreeGroup β} (hz : z ∉ relatorLetters R)
    (x : {x : β // x ≠ z}) : ∀ k ∈ mmDecs z R x, k = 0 := by
  intro k hk
  obtain ⟨b, hb⟩ := (mem_mmDecs_iff z R x k).mp hk
  exact wne_mmList_snd_eq_zero hz ((x, k), b) hb

/-- In the non-degenerate case the minimum decoration of any letter is `0`. -/
theorem wne_mmLo_eq_zero {z : β} {R : FreeGroup β} (hz : z ∉ relatorLetters R)
    (x : {x : β // x ≠ z}) : mmLo z R x = 0 := by
  classical
  rw [mmLo]
  by_cases h : (mmDecs z R x).Nonempty
  · rw [dif_pos h]
    exact wne_mmDecs_eq_zero hz x _ (Finset.min'_mem _ h)
  · rw [dif_neg h]

/-- In the non-degenerate case the maximum decoration of any letter is `0`. -/
theorem wne_mmHi_eq_zero {z : β} {R : FreeGroup β} (hz : z ∉ relatorLetters R)
    (x : {x : β // x ≠ z}) : mmHi z R x = 0 := by
  classical
  rw [mmHi]
  by_cases h : (mmDecs z R x).Nonempty
  · rw [dif_pos h]
    exact wne_mmDecs_eq_zero hz x _ (Finset.max'_mem _ h)
  · rw [dif_neg h]

/-- In the non-degenerate case every decorated letter of `mmBeta z R` has decoration `0`. -/
theorem wne_mmBeta_snd_eq_zero {z : β} {R : FreeGroup β} (hz : z ∉ relatorLetters R)
    (e : mmBeta z R) : e.1.2 = 0 := by
  obtain ⟨h1, h2⟩ := e.2
  rw [wne_mmLo_eq_zero hz e.1.1] at h1
  rw [wne_mmHi_eq_zero hz e.1.1] at h2
  omega

/-- In the non-degenerate case the associated set `mmTA` is empty. -/
theorem wne_mmTA_eq_empty {z : β} {R : FreeGroup β} (hz : z ∉ relatorLetters R) :
    mmTA z R = ∅ := by
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  intro he
  have h : e.1.2 + 1 ≤ mmHi z R e.1.1 :=
    (show ((e.1.1, e.1.2 + 1) : MMAlpha z) ∈ mmDecSet z R from he).2
  rw [wne_mmHi_eq_zero hz e.1.1] at h
  have h0 : e.1.2 = 0 := wne_mmBeta_snd_eq_zero hz e
  omega

/-- In the non-degenerate case the associated set `mmTB` is empty. -/
theorem wne_mmTB_eq_empty {z : β} {R : FreeGroup β} (hz : z ∉ relatorLetters R) :
    mmTB z R = ∅ := by
  ext e
  simp only [Set.mem_empty_iff_false, iff_false]
  intro he
  have h : mmLo z R e.1.1 ≤ e.1.2 - 1 :=
    (show ((e.1.1, e.1.2 - 1) : MMAlpha z) ∈ mmDecSet z R from he).1
  rw [wne_mmLo_eq_zero hz e.1.1] at h
  have h0 : e.1.2 = 0 := wne_mmBeta_snd_eq_zero hz e
  omega

/-- In the non-degenerate case the Magnus rewriting of `R` is nontrivial. -/
theorem wne_mmW_ne_one {z : β} {R : FreeGroup β} (hR1 : R ≠ 1)
    (hcyc : IsCyclicallyReducedRelator R) (hε : eps z R = 0) (hz : z ∉ relatorLetters R) :
    mmW z R ≠ 1 := by
  classical
  intro h
  have hred : FreeGroup.IsReduced (mmWL z R) := mmWL_isReduced z R hcyc hε
  have hL : ∀ p ∈ FreeGroup.toWord R, p.1 ≠ z := by
    intro p hp hpz
    exact hz (by rw [relatorLetters]; exact ⟨p.2, hpz ▸ hp⟩)
  have hne : mmWL z R ≠ [] := by
    intro hnil
    have hlen1 : (mmWL z R).length = (mmList z R).length := by
      rw [show mmWL z R = (mmList z R).map (fun p => (mmBetaOf z R p.1, p.2)) from rfl,
        List.length_map]
    have hlen2 : (mmList z R).length = (FreeGroup.toWord R).length := by
      rw [show mmList z R = magRew z 0 (FreeGroup.toWord R) from rfl,
        magRew_attach_of_notMem z 0 (FreeGroup.toWord R) hL, List.length_map, List.length_attach]
    rw [hnil, List.length_nil] at hlen1
    have hz0 : (FreeGroup.toWord R).length = 0 := by
      rw [← hlen2]
      exact hlen1.symm
    exact hR1 (FreeGroup.toWord_eq_nil_iff.mp (List.length_eq_zero_iff.mp hz0))
  have htw : FreeGroup.toWord (mmW z R) = mmWL z R := by
    rw [mmW, FreeGroup.toWord_mk, hred.reduce_eq]
  rw [h, FreeGroup.toWord_one] at htw
  exact hne htw.symm

/-- **Injectivity of `mmBaseHom` when the stable letter does not occur in the relator.**  This is the
proof of `Work.OROneRel.mmBaseHom_injective` with the two invocations of
`Work.OROneRel.mmW_notMem_closure_TA`/`mmW_notMem_closure_TB` replaced by the fact that (in this case)
the associated sets `mmTA z R` and `mmTB z R` are empty, so that the two non-membership hypotheses
reduce to `mmW z R ≠ 1`. -/
theorem wne_mmBaseHom_injective {z : β} {R : FreeGroup β} (hR1 : R ≠ 1) (hε : eps z R = 0)
    (hcyc : IsCyclicallyReducedRelator R) (hz : z ∉ relatorLetters R) :
    Function.Injective (mmBaseHom (t := z) (r := R) hε) := by
  classical
  have hFw : FreiheitssatzAt (mmW z R) := freiheitssatz_at _
  have hc : IsCyclicallyReducedRelator (mmW z R) := mmW_isCyclicallyReduced hcyc hε
  have hA : mmW z R ∉ Subgroup.closure (FreeGroup.of '' mmTA z R) := by
    rw [wne_mmTA_eq_empty hz, Set.image_empty, Subgroup.closure_empty]
    exact fun h => wne_mmW_ne_one hR1 hcyc hε hz (Subgroup.mem_bot.mp h)
  have hB : mmW z R ∉ Subgroup.closure (FreeGroup.of '' mmTB z R) := by
    rw [wne_mmTB_eq_empty hz, Set.image_empty, Subgroup.closure_empty]
    exact fun h => wne_mmW_ne_one hR1 hcyc hε hz (Subgroup.mem_bot.mp h)
  have hrel : FreeGroup.lift (mmThetaFun (r := R) hFw hc hA hB) R = 1 :=
    mmThetaFun_relator hε hFw hc hA hB
  have hinjΨ : Function.Injective (mmPsi (r := R) hε hFw hc hA hB) := by
    refine Function.LeftInverse.injective (g := mmTheta (r := R) hFw hc hA hB hrel) fun x => ?_
    have h := DFunLike.congr_fun (mmTheta_comp_mmPsi (r := R) hε hFw hc hA hB hrel) x
    simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using h
  refine fun x y hxy => HNNExtension.of_injective _ (hinjΨ ?_)
  rw [mmPsi_of (r := R) hε hFw hc hA hB, mmPsi_of (r := R) hε hFw hc hA hB]
  exact hxy

/-- **The descent to the Magnus base, without the hypothesis that the stable letter occurs in the
relator.** -/
theorem wneDescentNoHzB {R : FreeGroup β} {z : β} (w : FreeGroup β)
    (hR1 : R ≠ 1) (hε : Work.OROneRel.eps z R = 0)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator R) (hεw : Work.OROneRel.eps z w = 0)
    (hcontra : PresentedGroup.mk ({R} : Set (FreeGroup β)) w = 1)
    (j : ℤ) (u : FreeGroup (Work.OROneRel.mmBeta z R))
    (hu : FreeGroup.map (fun p : Work.OROneRel.mmBeta z R =>
        ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ))) u
        = Work.OROneRel.magShiftAut z j (Work.OROneRel.magRewRel z w)) :
    PresentedGroup.mk ({Work.OROneRel.mmW z R} : Set (FreeGroup (Work.OROneRel.mmBeta z R))) u = 1 := by
  classical
  by_cases hz : z ∈ relatorLetters R
  · exact mk_mmW_eq_one_of_mk_eq_one w hR1 hz hε hcyc hεw hcontra j u hu
  · have hinj : Function.Injective (mmBaseHom (t := z) (r := R) hε) :=
      wne_mmBaseHom_injective hR1 hε hcyc hz
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

end Work.OROneRel
