import Mathlib
import Submission.Work.WilE8.Star.LiftDefs

set_option autoImplicit false
noncomputable section
namespace Work.WilE8.Star

/-- Joint continuity of `consV` in the pair `(t, w)`. -/
lemma continuous_consV_joint (n m : ℕ) :
    Continuous (fun p : ℝ × (Fin (n + m) → ℝ) => consV n m p.1 p.2) := by
  rw [continuous_pi_iff]
  intro i
  by_cases h : (i : ℕ) = 0
  · have hfun : (fun p : ℝ × (Fin (n + m) → ℝ) => consV n m p.1 p.2 i) = fun p => p.1 := by
      funext p
      simp only [consV]
      rw [dif_pos h]
    rw [hfun]
    exact continuous_fst
  · have hfun : (fun p : ℝ × (Fin (n + m) → ℝ) => consV n m p.1 p.2 i) =
        fun p => p.2 ⟨i.val - 1, by omega⟩ := by
      funext p
      simp only [consV]
      rw [dif_neg h]
    rw [hfun]
    exact (continuous_apply _).comp continuous_snd

/-- The connected component, inside the cylinder over `S`, of the point sitting over `q` is the
cylinder over the connected component of `q` in `S`. -/
private lemma cylinder_component_aux {n m : ℕ} {S : Set (Fin (n + m) → ℝ)}
    (hS : S ⊆ WilkiesDesign.E.cubeC (n + m)) (q : Fin (n + m) → ℝ)
    (T : Set (Fin ((n + 1) + m) → ℝ))
    (hT : T = {x : Fin ((n + 1) + m) → ℝ | tailM n m x ∈ S} ∩
      WilkiesDesign.E.cubeC ((n + 1) + m)) :
    connectedComponentIn T (liftPt n m q) =
      {x : Fin ((n + 1) + m) → ℝ | x ∈ T ∧ tailM n m x ∈ connectedComponentIn S q} := by
  have hsub : tailM n m '' T ⊆ S := by
    rintro y ⟨z, hz, rfl⟩
    rw [hT] at hz
    exact hz.1
  refine Set.Subset.antisymm ?_ ?_
  · -- the component of the cylinder projects into the component of `S`
    intro x hx
    have hxT : x ∈ T := connectedComponentIn_subset T _ hx
    have hmem : liftPt n m q ∈ T := connectedComponentIn_nonempty_iff.mp ⟨x, hx⟩
    refine ⟨hxT, ?_⟩
    have himg := (continuous_tailM n m).continuousOn.image_connectedComponentIn_subset
      (s := T) (a := liftPt n m q) hmem
    have h1 : tailM n m x ∈
        connectedComponentIn (tailM n m '' T) (tailM n m (liftPt n m q)) :=
      himg ⟨x, hx, rfl⟩
    rw [tailM_liftPt] at h1
    exact connectedComponentIn_mono q hsub h1
  · -- the cylinder over the component is a connected set containing the base point
    intro x hx
    by_cases hq : q ∈ S
    · have hsm : tailM n m (liftPt n m q) ∈ S := by
        rw [tailM_liftPt]
        exact hq
      have hlift : liftPt n m q ∈
          {x : Fin ((n + 1) + m) → ℝ | x ∈ T ∧ tailM n m x ∈ connectedComponentIn S q} := by
        refine ⟨?_, ?_⟩
        · rw [hT]
          exact ⟨hsm, liftPt_mem_cubeC (hS hq)⟩
        · rw [tailM_liftPt]
          exact mem_connectedComponentIn hq
      have hpre : IsPreconnected
          {x : Fin ((n + 1) + m) → ℝ | x ∈ T ∧ tailM n m x ∈ connectedComponentIn S q} := by
        have hR_eq : {x : Fin ((n + 1) + m) → ℝ |
              x ∈ T ∧ tailM n m x ∈ connectedComponentIn S q} =
            (fun p : ℝ × (Fin (n + m) → ℝ) => consV n m p.1 p.2) ''
              (Set.Icc (-1 : ℝ) 1 ×ˢ connectedComponentIn S q) := by
          ext y
          constructor
          · rintro ⟨hyT, hyC⟩
            rw [hT] at hyT
            exact ⟨(y 0, tailM n m y), ⟨abs_le.mp (hyT.2 0), hyC⟩, consV_tailM n m y⟩
          · rintro ⟨⟨t, w⟩, hp, rfl⟩
            obtain ⟨hp0, hp1⟩ := hp
            have hp2 : w ∈ S := connectedComponentIn_subset S q hp1
            have hp3 : w ∈ WilkiesDesign.E.cubeC (n + m) := hS hp2
            have hsm' : tailM n m (consV n m t w) ∈ S := by
              rw [tailM_consV]
              exact hp2
            refine ⟨?_, ?_⟩
            · rw [hT]
              exact ⟨hsm', by rw [consV_mem_cubeC]; exact ⟨hp0, hp3⟩⟩
            · rw [tailM_consV]
              exact hp1
        rw [hR_eq]
        exact (isPreconnected_Icc.prod isPreconnected_connectedComponentIn).image
          (fun p : ℝ × (Fin (n + m) → ℝ) => consV n m p.1 p.2)
          (continuous_consV_joint n m).continuousOn
      exact hpre.subset_connectedComponentIn hlift (fun _ hy => hy.1) hx
    · rw [connectedComponentIn_eq_empty hq] at hx
      exact absurd hx.2 (Set.notMem_empty (tailM n m x))

theorem cylinder_component {n m : ℕ} {S : Set (Fin (n + m) → ℝ)}
    (hS : S ⊆ WilkiesDesign.E.cubeC (n + m)) (q : Fin (n + m) → ℝ) :
    connectedComponentIn ({x : Fin ((n + 1) + m) → ℝ |
          Work.WilE8.Star.tailM n m x ∈ S} ∩ WilkiesDesign.E.cubeC ((n + 1) + m))
        (Work.WilE8.Star.liftPt n m q)
      = {x : Fin ((n + 1) + m) → ℝ |
          x ∈ ({x : Fin ((n + 1) + m) → ℝ | Work.WilE8.Star.tailM n m x ∈ S} ∩
                WilkiesDesign.E.cubeC ((n + 1) + m)) ∧
          Work.WilE8.Star.tailM n m x ∈ connectedComponentIn S q} :=
  cylinder_component_aux hS q
    ({x : Fin ((n + 1) + m) → ℝ | Work.WilE8.Star.tailM n m x ∈ S} ∩
      WilkiesDesign.E.cubeC ((n + 1) + m)) rfl

end Work.WilE8.Star
