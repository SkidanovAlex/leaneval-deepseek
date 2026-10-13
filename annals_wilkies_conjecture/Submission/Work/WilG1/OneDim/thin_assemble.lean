import Submission.Work.WilG1.OneDim.thin_finite

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.OneDim

open WilkiesDesign

/-! ## 13. Transport between `ℝ` and `Fin 1 → ℝ` -/

/-- The canonical homeomorphism `(Fin 1 → ℝ) ≃ₜ ℝ` is evaluation at `0`. -/
theorem funUnique_fin1 (z : Fin 1 → ℝ) :
    (Homeomorph.funUnique (Fin 1) ℝ) z = z 0 := by
  have h : (Homeomorph.funUnique (Fin 1) ℝ) z = z default := rfl
  rwa [Subsingleton.elim (default : Fin 1) 0] at h

theorem mem_closure_liftR {P : Set ℝ} {x : ℝ} :
    (fun _ : Fin 1 => x) ∈ closure (Work.WilG1.liftR P) ↔ x ∈ closure P := by
  have h : Work.WilG1.liftR P = (Homeomorph.funUnique (Fin 1) ℝ) ⁻¹' P := by
    ext z
    simp only [Work.WilG1.liftR, Set.mem_setOf_eq, Set.mem_preimage, funUnique_fin1]
  rw [h, ← Homeomorph.preimage_closure, Set.mem_preimage]
  rfl

theorem liftR_compl (P : Set ℝ) :
    (Work.WilG1.liftR P)ᶜ = Work.WilG1.liftR Pᶜ := by
  ext z; simp [Work.WilG1.liftR]

/-! ## 14. Intervals are uncountable; countable preconnected sets are points -/

theorem not_countable_Ioo {a b : ℝ} (h : a < b) : ¬ (Set.Ioo a b).Countable := by
  intro hc
  have h1 : Cardinal.mk (Set.Ioo a b) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr hc.to_subtype
  rw [Cardinal.mk_Ioo_real h] at h1
  exact absurd h1 (not_le.mpr Cardinal.aleph0_lt_continuum)

theorem subsingleton_of_countable_of_preconnected {T : Set ℝ} (hT : IsPreconnected T)
    (hc : T.Countable) : T.Subsingleton := by
  intro x hx y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hIcc : Set.Icc x y ⊆ T := hT.Icc_subset hx hy
    exact not_countable_Ioo hlt ((hc.mono hIcc).mono Set.Ioo_subset_Icc_self)
  · have hIcc : Set.Icc y x ⊆ T := hT.Icc_subset hy hx
    exact not_countable_Ioo hlt ((hc.mono hIcc).mono Set.Ioo_subset_Icc_self)

/-! ## 15. An `Ω`-definable countable subset of `ℝ¹` is finite -/

theorem finite_of_omega_countable {S : WilkiesDesign.SOMin} {a b : ℕ} {P : Set ℝ}
    (hA : Work.WilG1.liftR P ∈ S.Ω a b 1) (hc : P.Countable) : P.Finite := by
  obtain ⟨p, hp⟩ := S.comps a
  obtain ⟨s, hcard, hconn, hAeq⟩ := hp b (Work.WilG1.liftR P) hA
  set e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ with he
  have hpiece : ∀ κ ∈ s, κ.Subsingleton := by
    intro κ hκ
    have hpre : IsPreconnected (e '' κ) := (hconn κ hκ).image e e.continuous.continuousOn
    have hcnt : (e '' κ).Countable := by
      have hsub : e '' κ ⊆ P := by
        rintro x ⟨w, hw, rfl⟩
        have hw' : w ∈ Work.WilG1.liftR P := by
          rw [hAeq]; exact Set.mem_sUnion.mpr ⟨κ, hκ, hw⟩
        have hw'' : w 0 ∈ P := by simpa [Work.WilG1.liftR] using hw'
        rw [funUnique_fin1 w]
        exact hw''
      exact hc.mono hsub
    have hsub' : (e '' κ).Subsingleton := subsingleton_of_countable_of_preconnected hpre hcnt
    intro a ha b hb
    have : e a = e b := hsub' ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact e.injective this
  have hset : P = ⋃ κ ∈ (s : Set (Set (Fin 1 → ℝ))),
      {x : ℝ | (fun _ : Fin 1 => x) ∈ κ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      have : (fun _ : Fin 1 => x) ∈ Work.WilG1.liftR P := by
        simpa [Work.WilG1.liftR] using hx
      rw [hAeq] at this
      obtain ⟨κ, hκ, hxκ⟩ := Set.mem_sUnion.mp this
      exact ⟨κ, hκ, hxκ⟩
    · rintro ⟨κ, hκ, hxκ⟩
      have : (fun _ : Fin 1 => x) ∈ Work.WilG1.liftR P := by
        rw [hAeq]; exact Set.mem_sUnion.mpr ⟨κ, hκ, hxκ⟩
      simpa [Work.WilG1.liftR] using this
  rw [hset]
  refine Set.Finite.biUnion s.finite_toSet (fun κ hκ => ?_)
  refine Set.Subsingleton.finite ?_
  intro x hx y hy
  have : (fun _ : Fin 1 => x) = (fun _ : Fin 1 => y) := hpiece κ hκ hx hy
  exact congrFun this 0

end Work.WilG1.OneDim
