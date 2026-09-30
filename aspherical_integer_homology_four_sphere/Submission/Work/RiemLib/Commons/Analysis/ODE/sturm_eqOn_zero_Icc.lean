import Mathlib
import Submission.Work.RiemLib.Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg
import Submission.Work.RiemLib.Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg_endpoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Analysis.ODE

open Set Filter
open scoped Topology

theorem sturm_eqOn_zero_Icc {lam a b : ℝ} (hlam : 0 < lam) (hab : a < b)
    (hb : b - a < Real.pi / Real.sqrt lam) {h g G : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Icc a b)) (ha : h a = 0)
    (hnn : ∀ t ∈ Set.Icc a b, 0 ≤ h t)
    (hd1 : ∀ t ∈ Set.Ioo a b, HasDerivAt h (g t) t)
    (hd2 : ∀ t ∈ Set.Ioo a b, HasDerivAt g (G t) t)
    (hineq : ∀ t ∈ Set.Ioo a b, 0 ≤ G t + lam * h t)
    (hb0 : h b = 0) : Set.EqOn h (fun _ => 0) (Set.Icc a b) := by
  set T : ℝ := b - a with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  have hTπ : T < Real.pi / Real.sqrt lam := by rw [hTdef]; exact hb
  have haT : a + T = b := by rw [hTdef]; ring
  have memIcc : ∀ t ∈ Set.Icc (0:ℝ) T, a + t ∈ Set.Icc a b := by
    intro t ht
    exact ⟨by linarith [ht.1], by rw [← haT]; linarith [ht.2]⟩
  have memIoo : ∀ t ∈ Set.Ioo (0:ℝ) T, a + t ∈ Set.Ioo a b := by
    intro t ht
    exact ⟨by linarith [ht.1], by rw [← haT]; linarith [ht.2]⟩
  have hcont' : ContinuousOn (fun s : ℝ => h (a + s)) (Set.Icc (0:ℝ) T) := by
    have hmap : Set.MapsTo (fun t : ℝ => a + t) (Set.Icc (0:ℝ) T) (Set.Icc a b) := memIcc
    have hc : ContinuousOn (fun t : ℝ => a + t) (Set.Icc (0:ℝ) T) :=
      (continuous_const.add continuous_id).continuousOn
    simpa only [Function.comp_def] using hcont.comp hc hmap
  have h0' : (fun s : ℝ => h (a + s)) 0 = 0 := by simpa using ha
  have hnn' : ∀ t ∈ Set.Icc (0:ℝ) T, 0 ≤ (fun s : ℝ => h (a + s)) t := by
    intro t ht; exact hnn (a + t) (memIcc t ht)
  have hd1' : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt (fun s : ℝ => h (a + s)) (g (a + t)) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ => a + s) 1 t := (hasDerivAt_id t).const_add a
    have hd := (hd1 (a + t) (memIoo t ht)).comp t hlin
    simpa only [Function.comp_def, mul_one] using hd
  have hd2' : ∀ t ∈ Set.Ioo (0:ℝ) T, HasDerivAt (fun s : ℝ => g (a + s)) (G (a + t)) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ => a + s) 1 t := (hasDerivAt_id t).const_add a
    have hd := (hd2 (a + t) (memIoo t ht)).comp t hlin
    simpa only [Function.comp_def, mul_one] using hd
  have hineq' : ∀ t ∈ Set.Ioo (0:ℝ) T, 0 ≤ G (a + t) + lam * h (a + t) := by
    intro t ht; exact hineq (a + t) (memIoo t ht)
  have hb' : (fun s : ℝ => h (a + s)) T = 0 := by
    show h (a + T) = 0
    rw [haT]; exact hb0
  have key : Set.EqOn (fun s : ℝ => h (a + s)) (fun _ => 0) (Set.Icc (0:ℝ) T) :=
    sturm_eqOn_zero_of_second_deriv_add_nonneg_endpoint (lam := lam) (t₁ := T)
      hlam hT hTπ
      (h := fun s : ℝ => h (a + s)) (g := fun s : ℝ => g (a + s))
      (G := fun s : ℝ => G (a + s))
      hcont' h0' hnn' hd1' hd2' hineq' hb'
  intro x hx
  have hxT : x - a ∈ Set.Icc (0:ℝ) T := ⟨by linarith [hx.1], by rw [hTdef]; linarith [hx.2]⟩
  have h1 : h (a + (x - a)) = 0 := key hxT
  rwa [add_sub_cancel] at h1

end Commons.Analysis.ODE
