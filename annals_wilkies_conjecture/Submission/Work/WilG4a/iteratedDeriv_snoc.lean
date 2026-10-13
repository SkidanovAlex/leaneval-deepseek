import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells

namespace Work.WilG4a

theorem iteratedDeriv_snoc (p : ℕ) (g : (Fin (p + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (j : ℕ)
    (hg : ContDiffAt ℝ j g (Fin.snoc l x)) :
    iteratedDeriv j (fun y : ℝ => g (Fin.snoc l y)) x =
      iteratedFDeriv ℝ j g (Fin.snoc l x) (fun _ : Fin j => Pi.single (Fin.last p) 1) := by
  classical
  -- Affine decomposition of `Fin.snoc l ·`
  set e : Fin (p + 1) → ℝ := Pi.single (Fin.last p) (1 : ℝ) with he
  set a : Fin (p + 1) → ℝ := Fin.snoc l 0 with ha
  set T : ℝ →L[ℝ] (Fin (p + 1) → ℝ) := ContinuousLinearMap.toSpanSingleton ℝ e with hT
  have hTapply : ∀ y : ℝ, T y = y • e := fun y => by
    rw [hT, ContinuousLinearMap.toSpanSingleton_apply]
  have hTone : T 1 = e := by rw [hTapply 1, one_smul]
  have hsnoc_eq : ∀ y : ℝ, Fin.snoc l y = a + y • e := by
    intro y
    rw [ha, he]
    funext i
    induction i using Fin.lastCases with
    | last => simp [Fin.snoc_last, Pi.single_eq_same]
    | cast k => simp [Fin.snoc_castSucc]
  have hsnocT : ∀ y : ℝ, Fin.snoc l y = a + T y := by
    intro y; rw [hsnoc_eq y, hTapply y]
  -- An open neighbourhood on which `g` is `C^j`
  obtain ⟨u, huo, hxu, hucd⟩ := hg.contDiffOn' le_rfl (by simp)
  have hucd' : ContDiffOn ℝ (j:ℕ∞) g u := by
    rw [Set.insert_eq_of_mem (Set.mem_univ _), Set.univ_inter] at hucd
    exact hucd
  set u₁ : Set (Fin (p + 1) → ℝ) := (fun z => a + z) ⁻¹' u with hu₁def
  have hu₁open : IsOpen u₁ := by
    rw [hu₁def]
    exact IsOpen.preimage (continuous_const.add continuous_id) huo
  have hu₁ud : UniqueDiffOn ℝ u₁ := hu₁open.uniqueDiffOn
  have hTmem : T x ∈ u₁ := by
    rw [hu₁def]
    show a + T x ∈ u
    rw [← hsnocT x]
    exact hxu
  have hpre_open : IsOpen (T ⁻¹' u₁) := IsOpen.preimage T.continuous hu₁open
  have hpre_ud : UniqueDiffOn ℝ (T ⁻¹' u₁) := hpre_open.uniqueDiffOn
  have hgcd : ContDiffOn ℝ (j:ℕ∞) (fun z : Fin (p + 1) → ℝ => g (a + z)) u₁ := by
    have hmap : Set.MapsTo (fun z : Fin (p + 1) → ℝ => a + z) u₁ u := fun z hz => hz
    have hf : ContDiffOn ℝ (j:ℕ∞) (fun z : Fin (p + 1) → ℝ => a + z) u₁ :=
      (((contDiff_const (c := a)).add contDiff_id).contDiffOn)
    exact hucd'.comp hf hmap
  -- Chain rule for the composition with the linear map `T`
  have hcomp := ContinuousLinearMap.iteratedFDerivWithin_comp_right T hgcd hu₁ud hpre_ud hTmem
    (i := j) le_rfl
  have hFF : (fun y : ℝ => g (Fin.snoc l y)) = (fun y : ℝ => g (a + T y)) :=
    funext (fun y => by rw [hsnocT y])
  have hFat : ContDiffAt ℝ (j:ℕ∞) (fun y : ℝ => g (a + T y)) x := by
    have hg' : ContDiffAt ℝ (j:ℕ∞) g (a + T x) := hsnocT x ▸ hg
    exact hg'.comp x (((contDiff_const (c := a)).add T.contDiff).contDiffAt)
  have hL : iteratedFDerivWithin ℝ j (fun y : ℝ => g (a + T y)) (T ⁻¹' u₁) x
      = iteratedFDeriv ℝ j (fun y : ℝ => g (a + T y)) x :=
    iteratedFDerivWithin_eq_iteratedFDeriv hpre_ud hFat hTmem
  have hcomp' : iteratedFDerivWithin ℝ j (fun y : ℝ => g (a + T y)) (T ⁻¹' u₁) x
      = (iteratedFDerivWithin ℝ j (fun z : Fin (p+1) → ℝ => g (a + z)) u₁ (T x)).compContinuousLinearMap
          (fun _ => T) := hcomp
  have hR : iteratedFDerivWithin ℝ j (fun z : Fin (p+1) → ℝ => g (a + z)) u₁ (T x)
      = iteratedFDeriv ℝ j g (Fin.snoc l x) := by
    have hGat : ContDiffAt ℝ (j:ℕ∞) (fun z : Fin (p+1) → ℝ => g (a + z)) (T x) :=
      hgcd.contDiffAt (hu₁open.mem_nhds hTmem)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hu₁ud hGat hTmem,
        iteratedFDeriv_comp_add_left j a (T x), ← hsnocT x]
  simp only [hFF, iteratedDeriv, ← hL, hcomp',
    ContinuousMultilinearMap.compContinuousLinearMap_apply, hTone, he, hR]

end Work.WilG4a
