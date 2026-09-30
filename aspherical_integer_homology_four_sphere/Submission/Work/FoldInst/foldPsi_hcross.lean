/-
# The cross (injectivity) lemma for the glued fold value `foldPsi`

This file proves that the glued value `foldPsi i` of a fold class `i` is injective on the union of the
Voronoi pieces *up to the identification relation* `rel` of `M̄ = Xbar / ~₁`:

  `foldPsi i x = foldPsi i x'  ⟹  rel x x'`,

for `x, x'` in the union of the pieces `Dvor i r`.

The proof is the blueprint's `hcross`:

* `foldPsi i` on a piece is `foldTheta i ·` (`foldPsi_eq`), so the hypothesis reads
  `foldTheta i r x₀ = foldTheta i s x'₀` where `x ∈ Dvor i r`, `x' ∈ Dvor i s`;
* the common value lies in the two orthants `orthant (signVecNeg r)` and `orthant (signVecNeg s)`
  (`fold_theta_orthant`), hence all its coordinates at positions where `r` and `s` differ vanish;
* by the coordinate formula `fold_theta_coord` (the height is positive and `√(1-‖·‖²) > 0`) the
  corresponding *wall slacks* of `r` at `x` vanish, so `γ := wallSum i Δ`
  (`Δ = {t | r t ≠ s t}`) lies in the identification group `Ksub x₀` (`Ksub_eq_wallSum`);
* `actX γ` carries `Dvor i r` onto `Dvor i (flipSet r Δ) = Dvor i s` (`actX_image_Dvor`), and by the
  flip identity (`foldTheta_flip`) and the vanishing of the slacks (`reflCoords_eq_self`) it does not
  change the chart value;
* injectivity of `foldTheta i s` on the ball (`foldTheta_injOn`) then gives `actX γ x = x'`, i.e.
  `rel x x'`.
-/
import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.foldPsi_eq
import Submission.Work.FoldInst.foldTheta_injOn
import Submission.Work.FoldInst.actX_image_Dvor
import Submission.Work.FoldInst.Ksub_eq_wallSum
import Submission.Work.FoldInst.foldTheta_flip
import Submission.Work.FoldInst.fold_theta_coord
import Submission.Work.FoldInst.fold_theta_orthant
import Submission.Work.FoldInst.foldPsi_hagree

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-! ### Elementary consequences of the Voronoi conditions -/

/-- Every Voronoi piece is contained in the corresponding closed piece: the non-wall slacks of a
point of `Dvor i r` are strictly positive, hence nonnegative. -/
theorem hcross_Dvor_subset_Clift (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    Dvor i r ⊆ Clift i r := by
  intro x hx
  rw [mem_Dvor] at hx
  rw [mem_VoronoiOpen] at hx
  exact ⟨hx.1, fun S hS => le_of_lt (hx.2.1 S hS).1⟩

/-- The sign stored in `signVecNeg r` at a coordinate, as an explicit `if`. -/
@[simp] theorem hcross_signVal_signVecNeg {c : ℕ} (r : Fin c → Bool) (t : Fin c) :
    Work.Fold.signVal (Work.Fold.signVecNeg r) t = if r t then (-1 : ℝ) else 1 := by
  rw [Work.Fold.signVal, Work.Fold.signVecNeg]
  cases r t <;> simp

/-- **A coordinate where two sign indices differ vanishes in a common point of their orthants.**
If `z` lies both in the orthant of `signVecNeg r` and in the orthant of `signVecNeg s`, and
`r j ≠ s j`, then the `j`-th coordinate of `z` is `0`: the two orthant conditions give `z j ≥ 0`
and `z j ≤ 0`. -/
theorem hcross_orthant_coord_eq_zero {c : ℕ} {r s : Fin c → Bool} {z : E4}
    (hzr : z ∈ Work.Fold.orthant (Work.Fold.signVecNeg r))
    (hzs : z ∈ Work.Fold.orthant (Work.Fold.signVecNeg s))
    {j : Fin 4} (hj : (j : ℕ) < c) (hne : r ⟨j, hj⟩ ≠ s ⟨j, hj⟩) : z j = 0 := by
  rw [Work.Fold.mem_orthant_iff] at hzr hzs
  have h1 := hzr j hj
  have h2 := hzs j hj
  simp only [hcross_signVal_signVecNeg] at h1 h2
  cases hr : r ⟨j, hj⟩ <;> cases hs : s ⟨j, hj⟩
  · exact absurd (by rw [hr, hs]) hne
  · simp only [hr, hs, Bool.false_eq_true, ite_true, ite_false, one_mul, neg_mul] at h1 h2
    linarith
  · simp only [hr, hs, Bool.false_eq_true, ite_true, ite_false, one_mul, neg_mul] at h1 h2
    linarith
  · exact absurd (by rw [hr, hs]) hne

/-! ### The main lemma -/

theorem foldPsi_hcross (i : Fin 98) {x x' : Xbar}
    (hx : x ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r)
    (hx' : x' ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r)
    (h : foldPsi i x = foldPsi i x') : rel x x' := by
  classical
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx'
  -- The set of walls at which the two sign indices differ.
  set Δ : Finset (Fin (foldCodim i)) := Finset.univ.filter (fun t => r t ≠ s t) with hΔdef
  have hflip : flipSet r Δ = s := by
    funext t
    rw [hΔdef, flipSet_apply]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases hr' : r t <;> cases hs' : s t <;> simp_all
  -- The common chart value.
  have hz : foldTheta i r x.2.1 = foldTheta i s x'.2.1 := by
    rw [← foldPsi_eq i hr, ← foldPsi_eq i hs]
    exact h
  -- The walls in `Δ` are tight at `x`.
  have hslack0 : ∀ t ∈ Δ, sideSlack (foldWalls i r t) x.2.1 = 0 := by
    intro t ht
    have hne : r t ≠ s t := by
      rw [hΔdef] at ht
      simpa using ht
    have hballx : x.2.1 ∈ HypModel.ball := Dvor_subset_ball i r hr
    have hzr : foldTheta i r x.2.1 ∈ Work.Fold.orthant (Work.Fold.signVecNeg r) :=
      fold_theta_orthant i r x (hcross_Dvor_subset_Clift i r hr)
    have hzs : foldTheta i s x'.2.1 ∈ Work.Fold.orthant (Work.Fold.signVecNeg s) :=
      fold_theta_orthant i s x' (hcross_Dvor_subset_Clift i s hs)
    -- the `t`-th coordinate of the common value vanishes
    have hzero : (foldTheta i s x'.2.1)
        ⟨t.1, by have h1 := t.isLt; have h2 := foldCodim_le i; omega⟩ = 0 :=
      hcross_orthant_coord_eq_zero (hz ▸ hzr) hzs t.isLt (by simpa using hne)
    -- the coordinate formula converts this into a vanishing slack
    have hcoord := fold_theta_coord i r x.2.1 hballx t
    rw [hz, hzero, mul_zero] at hcoord
    have hH : 0 < (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) x.2.1)) 3 :=
      HypModel.mobiusKlein_mem (FoldThetaOrthantAux.foldNr_isLorentz i)
        (Qbar_subset_ball ((Qbar_act (toG (foldKr i r)) x.2.1).mpr x.2.2))
    rcases mul_eq_zero.mp hcoord.symm with hh | hh
    · rcases mul_eq_zero.mp hh with hh' | hh'
      · exact absurd hh' (by split <;> norm_num)
      · exact hh'
    · exact absurd hh (ne_of_gt hH)
  -- The corresponding group element lies in the identification group of `x`.
  have hγK : wallSum i Δ ∈ Ksub x.2.1 :=
    (Ksub_eq_wallSum i hr (wallSum i Δ)).mpr ⟨Δ, hslack0, rfl⟩
  -- Its action carries `x` into the piece of `s`.
  have hxD : actX (wallSum i Δ) x ∈ Dvor i s := by
    rw [← hflip, ← actX_image_Dvor i r Δ]
    exact ⟨x, hr, rfl⟩
  -- and does not change the chart value.
  have hval : foldTheta i s (actX (wallSum i Δ) x).2.1 = foldTheta i s x'.2.1 := by
    have hstep : foldTheta i s (actX (wallSum i Δ) x).2.1
        = foldTheta i (flipSet r Δ) (act (wallSum i Δ).1 x.2.1) := by
      rw [← hflip, actX_snd]
    rw [hstep, foldTheta_flip i r Δ x.2.1,
      reflCoords_eq_self i r (Dvor_subset_ball i r hr) hslack0,
      (foldPsi_eq i hr).symm, h, foldPsi_eq i hs]
  -- Injectivity of the chart on the ball identifies `actX γ x` with `x'`.
  have hsnd : (actX (wallSum i Δ) x).2.1 = x'.2.1 :=
    foldTheta_injOn i s (Qbar_subset_ball (actX (wallSum i Δ) x).2.2)
      (Qbar_subset_ball x'.2.2) hval
  exact ⟨wallSum i Δ, hγK, Prod.ext (by rw [hxD.1, hs.1]) (Subtype.ext hsnd)⟩

end Work.FoldInst
