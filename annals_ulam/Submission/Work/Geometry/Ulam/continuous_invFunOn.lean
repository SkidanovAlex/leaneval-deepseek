import Mathlib

namespace Commons.Geometry.Ulam

open Set

/-- A continuous strictly monotone function on a compact interval has a
continuous inverse on its image.  This is the compact-to-Hausdorff
homeomorphism argument, stated for `Function.invFunOn`. -/
lemma continuousOn_invFunOn_of_strictMonoOn_of_continuousOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_mono : StrictMonoOn f (Set.Icc a b)) :
    ContinuousOn (Function.invFunOn f (Set.Icc a b)) (f '' Set.Icc a b) := by
  let s : Set ℝ := Set.Icc a b
  let t : Set ℝ := f '' s
  let F : s → t := fun x => ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩
  have hF_cont : Continuous F := by
    have hcont : Continuous (fun x : s => f x.1) := by
      rw [← continuousOn_univ]
      exact hf_cont.comp continuous_subtype_val.continuousOn (fun x _ => x.2)
    exact hcont.subtype_mk (fun x => ⟨x.1, x.2, rfl⟩)
  have hF_inj : Function.Injective F := by
    intro x y h
    have hval : f x.1 = f y.1 := congrArg Subtype.val h
    exact Subtype.ext (hf_mono.injOn x.2 y.2 hval)
  have hF_surj : Function.Surjective F := by
    intro y
    rcases y.2 with ⟨x, hx, hfx⟩
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : T2Space t := inferInstance
  have hF_homeo : IsHomeomorph F :=
    (isHomeomorph_iff_continuous_bijective).2 ⟨hF_cont, hF_inj, hF_surj⟩
  let G : t → s := hF_homeo.homeomorph.symm
  have hG_cont : Continuous G := hF_homeo.homeomorph.continuous_invFun
  have hG_eq : ∀ y : t, (G y).1 = Function.invFunOn f s y.1 := by
    intro y
    apply hf_mono.injOn (G y).2 (Function.invFunOn_mem (f := f) (s := s) y.2)
    have h1 : F (G y) = y := hF_homeo.homeomorph.apply_symm_apply y
    have h2 : f (G y).1 = y.1 := congrArg Subtype.val h1
    have h3 : f (Function.invFunOn f s y.1) = y.1 :=
      Function.invFunOn_eq (f := f) (s := s) y.2
    exact h2.trans h3.symm
  have hR_cont : Continuous (fun y : t => Function.invFunOn f s y.1) := by
    convert (continuous_subtype_val.comp hG_cont) using 1
    ext y
    exact (hG_eq y).symm
  exact continuousOn_iff_continuous_restrict.mpr hR_cont

/-- The antitone version, used for the right arc. -/
lemma continuousOn_invFunOn_of_strictAntiOn_of_continuousOn
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_anti : StrictAntiOn f (Set.Icc a b)) :
    ContinuousOn (Function.invFunOn f (Set.Icc a b)) (f '' Set.Icc a b) := by
  let s : Set ℝ := Set.Icc a b
  have hmono : StrictMonoOn (fun x => -f x) s := by
    intro x hx y hy hxy
    linarith [hf_anti hx hy hxy]
  have hcont_neg : ContinuousOn (fun x => -f x) s := hf_cont.neg
  have h := continuousOn_invFunOn_of_strictMonoOn_of_continuousOn
    (f := fun x => -f x) hab hcont_neg hmono
  have hneg : ContinuousOn (fun y => -y) (f '' s) := continuous_neg.continuousOn
  have hmaps : Set.MapsTo (fun y => -y) (f '' s) ((-f) '' s) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx, by simp⟩
  have hcomp := h.comp hneg hmaps
  refine hcomp.congr ?_
  intro y hy
  refine hf_anti.injOn ?_ ?_ ?_
  · exact Function.invFunOn_mem (f := f) (s := s) hy
  · exact Function.invFunOn_mem (f := fun x => -f x) (s := s) (hmaps hy)
  · have h1 : f (Function.invFunOn f s y) = y :=
      Function.invFunOn_eq (f := f) (s := s) hy
    have h2 : f (Function.invFunOn (fun x => -f x) s (-y)) = y := by
      have hneg_mem : -y ∈ (fun x => -f x) '' s := hmaps hy
      have h3 : (fun x => -f x) (Function.invFunOn (fun x => -f x) s (-y)) = -y :=
        Function.invFunOn_eq hneg_mem
      linarith
    exact h1.trans h2.symm

end Commons.Geometry.Ulam
