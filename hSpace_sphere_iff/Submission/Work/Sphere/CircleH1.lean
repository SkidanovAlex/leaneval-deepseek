import Mathlib
import Submission.Work.Sphere.Suspension
import Submission.Work.Cohomology.H_zero_connected
import Submission.Work.Cohomology.mvConnecting_ker_eq_range
import Submission.Work.Cohomology.mvBetaH_ker_eq_range
import Submission.Work.Cohomology.H_subsingleton_of_contractible
import Submission.Work.Cohomology.H_zero_two_points
import Submission.Work.Cohomology.MVH
import Submission.Work.Cohomology.mvConnecting_surjective
import Submission.Work.Sphere.H_sph_zero
import Submission.Work.Sphere.pathConnected_sph

open CategoryTheory Simplicial Opposite
open SSet

namespace Work.Sphere

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

/-! ## A linear-algebra lemma: the quotient of `ℚ × ℚ` by a line is `ℚ` -/

/-- A nonzero submodule of `ℚ` is everything. -/
theorem rat_submodule_eq_top {S : Submodule ℚ ℚ} (h : S ≠ ⊥) : S = ⊤ := by
  rw [Submodule.ne_bot_iff] at h
  obtain ⟨x, hxS, hx0⟩ := h
  rw [Submodule.eq_top_iff']
  intro y
  have : y = (y / x) • x := by rw [smul_eq_mul, div_mul_cancel₀ y hx0]
  rw [this]
  exact S.smul_mem _ hxS

/-- **A subspace `S` of a `ℚ`-vector space isomorphic to `ℚ × ℚ` that is itself isomorphic to `ℚ`
has quotient isomorphic to `ℚ`.**  Concretely, if `u` spans `S`, the functional
`a ↦ u₂ a₁ - u₁ a₂` descends to an isomorphism `W ⧸ S ≃ₗ ℚ`. -/
theorem quotient_rat_sq_iso_rat {W : Type*} [AddCommGroup W] [Module ℚ W]
    (e : W ≃ₗ[ℚ] ℚ × ℚ) (S : Submodule ℚ W) (eS : S ≃ₗ[ℚ] ℚ) :
    Nonempty ((W ⧸ S) ≃ₗ[ℚ] ℚ) := by
  classical
  obtain ⟨s, hs1, hsne⟩ : ∃ s : S, eS s = 1 ∧ s ≠ 0 := by
    refine ⟨eS.symm 1, eS.apply_symm_apply 1, fun h0 => ?_⟩
    have h1 : eS (eS.symm 1) = eS 0 := by rw [h0]
    rw [eS.apply_symm_apply, map_zero] at h1
    exact one_ne_zero h1
  set u : ℚ × ℚ := e (s : W) with hu
  have hune : u ≠ 0 := by
    intro h
    have h2 : (e (s : W)) = e 0 := by rw [← hu, h, map_zero]
    exact hsne (by simpa using e.injective h2)
  have hSspan : S = Submodule.span ℚ {(s : W)} := by
    apply le_antisymm
    · intro w hw
      rw [Submodule.mem_span_singleton]
      refine ⟨eS ⟨w, hw⟩, ?_⟩
      have h2 : (⟨w, hw⟩ : S) = eS ⟨w, hw⟩ • s := by
        apply eS.injective
        rw [map_smul, hs1, smul_eq_mul, mul_one]
      have h3 := congrArg (Subtype.val) h2
      rw [Submodule.coe_smul] at h3
      exact h3.symm
    · exact (Submodule.span_singleton_le_iff_mem (s : W) S).mpr s.2
  have hSmap : S.map (e : W →ₗ[ℚ] ℚ × ℚ) = Submodule.span ℚ {u} := by
    rw [hSspan, Submodule.map_span, Set.image_singleton]
    rfl
  let ψ : ℚ × ℚ →ₗ[ℚ] ℚ := u.2 • LinearMap.fst ℚ ℚ ℚ - u.1 • LinearMap.snd ℚ ℚ ℚ
  have hψ : ∀ a : ℚ × ℚ, ψ a = u.2 * a.1 - u.1 * a.2 := fun a => by simp [ψ]
  have hψu : ψ u = 0 := by rw [hψ]; ring
  have hker : LinearMap.ker ψ = Submodule.span ℚ {u} := by
    apply le_antisymm
    · intro a ha
      rw [LinearMap.mem_ker, hψ] at ha
      rw [Submodule.mem_span_singleton]
      rcases eq_or_ne u.1 0 with h1 | h1
      · have h2 : u.2 ≠ 0 := fun h2 => hune (Prod.ext h1 h2)
        have ha1 : a.1 = 0 := by
          rw [h1, zero_mul, sub_zero] at ha
          exact (mul_eq_zero.mp ha).resolve_left h2
        refine ⟨a.2 / u.2, ?_⟩
        ext
        · simp only [Prod.smul_fst, smul_eq_mul]; rw [h1, mul_zero, ha1]
        · simp only [Prod.smul_snd, smul_eq_mul]; exact div_mul_cancel₀ a.2 h2
      · refine ⟨a.1 / u.1, ?_⟩
        ext
        · simp only [Prod.smul_fst, smul_eq_mul]; exact div_mul_cancel₀ a.1 h1
        · simp only [Prod.smul_snd, smul_eq_mul]
          have h : u.1 * a.2 = u.2 * a.1 := by linarith
          field_simp
          linarith
    · intro a ha
      rw [Submodule.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [LinearMap.mem_ker, map_smul, hψu, smul_zero]
  have hTker : S.map (e : W →ₗ[ℚ] ℚ × ℚ) = LinearMap.ker ψ := hSmap.trans hker.symm
  let Φ : W →ₗ[ℚ] ℚ := ψ.comp (e : W →ₗ[ℚ] ℚ × ℚ)
  have hΦapply : ∀ w, Φ w = ψ ((e : W →ₗ[ℚ] ℚ × ℚ) w) := fun w => rfl
  have hkerΦ : LinearMap.ker Φ = S := by
    apply le_antisymm
    · intro w hw
      rw [LinearMap.mem_ker, hΦapply] at hw
      have hmem : (e : W →ₗ[ℚ] ℚ × ℚ) w ∈ S.map (e : W →ₗ[ℚ] ℚ × ℚ) := by
        rw [hTker]; exact hw
      rw [Submodule.mem_map] at hmem
      obtain ⟨w', hw', heq⟩ := hmem
      rw [← e.injective heq]; exact hw'
    · intro w hw
      rw [LinearMap.mem_ker, hΦapply]
      have hmem : (e : W →ₗ[ℚ] ℚ × ℚ) w ∈ LinearMap.ker ψ := by
        rw [← hTker]; exact Submodule.mem_map_of_mem hw
      exact hmem
  have hΦsurj : Function.Surjective Φ := by
    have hψne : ψ ≠ 0 := by
      rcases eq_or_ne u.1 0 with h1 | h1
      · have h2 : u.2 ≠ 0 := fun h2 => hune (Prod.ext h1 h2)
        intro h
        have := congrArg (fun f : ℚ × ℚ →ₗ[ℚ] ℚ => f (1, 0)) h
        rw [hψ] at this
        simp [h2] at this
      · intro h
        have := congrArg (fun f : ℚ × ℚ →ₗ[ℚ] ℚ => f (0, 1)) h
        rw [hψ] at this
        simp [h1] at this
    have hψsurj : Function.Surjective ψ := by
      rw [← LinearMap.range_eq_top]
      exact rat_submodule_eq_top (fun h => hψne (LinearMap.range_eq_bot.mp h))
    intro y
    obtain ⟨x, hx⟩ := hψsurj y
    refine ⟨(e.symm x : W), ?_⟩
    rw [hΦapply, show (e : W →ₗ[ℚ] ℚ × ℚ) (e.symm x) = x from e.apply_symm_apply x, hx]
  exact ⟨(Submodule.quotEquivOfEq (LinearMap.ker Φ) S hkerΦ).symm.trans
    (Φ.quotKerEquivOfSurjective hΦsurj)⟩

end

/-- **`H¹(S¹; ℚ) ≅ ℚ`.**  The rational cohomology of the circle in degree one is one dimensional.

The proof runs the Mayer–Vietoris long exact sequence for the two-cap cover of `S¹`.  With
`S = smallC 0` (the subcomplex of simplices lying in one of the two caps), `A = capAsub 0`,
`B = capBsub 0` the two (contractible) pieces and `C = A ⊓ B` their intersection, the sequence

`H⁰(S) →ᶠ H⁰(A) × H⁰(B) →ᵍ H⁰(C) →ᵟ H¹(S) → H¹(A) × H¹(B) = 0`

is exact, so `H¹(S) ≅ H⁰(C) ⧸ im g`.  Now `H⁰(S) ≅ ℚ`, `H⁰(A) ≅ ℚ`, `H⁰(B) ≅ ℚ` (path
connected / contractible), while `H⁰(C) ≅ ℚ × ℚ` (the doubly punctured circle is homotopy
equivalent to `S⁰`), so `f` is injective with `ℚ`-dimensional image, hence `ker g = im f ≅ ℚ` and
`im g ≅ ℚ² ⧸ ℚ ≅ ℚ`; applying the same lemma once more to `H⁰(C) ≅ ℚ × ℚ` and `im g ≅ ℚ`
gives `H¹(S) ≅ ℚ ⧸ (line) ≅ ℚ`.  Finally `H¹(S¹) ≅ H¹(S)` by the small-simplex theorem. -/
theorem CircleH1 :
    Nonempty (Submission.Cohomology.H (Submission.Sphere.singSph 1) ℚ 1 ≃ₗ[ℚ] ℚ) := by
  classical
  haveI hpath : PathConnectedSpace (Submission.Sphere.Sph 1) :=
    Work.Sphere.pathConnected_sph 1 (by norm_num)
  haveI hcapP : ContractibleSpace ↥(Submission.Sphere.capPlus 0) := by
    rw [Submission.Sphere.capPlus_eq]
    exact Classical.choice
      (Work.Sphere.contractibleSpace_sph_compl (n := 1) (Submission.Sphere.polePt 1))
  haveI hcapM : ContractibleSpace ↥(Submission.Sphere.capMinus 0) := by
    rw [Submission.Sphere.capMinus_eq]
    exact Classical.choice
      (Work.Sphere.contractibleSpace_sph_compl (n := 1) (Submission.Sphere.negPolePt 1))
  -- degree `0` of the small complex, the two pieces, and their intersection
  have e_V : Submission.Cohomology.H (Submission.Sphere.smallC 0) ℚ 0 ≃ₗ[ℚ] ℚ :=
    (Submission.Sphere.smallSphereIso 0 0).trans
      (Classical.choice (Work.Cohomology.H_zero_connected (Submission.Sphere.Sph 1)))
  have e_A : Submission.Cohomology.H (Submission.Sphere.capAsub 0) ℚ 0 ≃ₗ[ℚ] ℚ :=
    (Classical.choice (Submission.Sphere.H_iso_of_iso
        (Submission.Sphere.preimageIso (Submission.Sphere.smallSub 0)
          (Submission.Sphere.capPlusSub 0) le_sup_left) 0)).trans
      ((Classical.choice (Submission.Sphere.H_iso_of_iso
        (Classical.choice (Work.Cohomology.singIn_iso (Submission.Sphere.Sph 1)
          (Submission.Sphere.capPlus 0))) 0)).trans
        (Classical.choice (Work.Cohomology.H_zero_connected
          (TopCat.of ↥(Submission.Sphere.capPlus 0)))))
  have e_B : Submission.Cohomology.H (Submission.Sphere.capBsub 0) ℚ 0 ≃ₗ[ℚ] ℚ :=
    (Classical.choice (Submission.Sphere.H_iso_of_iso
        (Submission.Sphere.preimageIso (Submission.Sphere.smallSub 0)
          (Submission.Sphere.capMinusSub 0) le_sup_right) 0)).trans
      ((Classical.choice (Submission.Sphere.H_iso_of_iso
        (Classical.choice (Work.Cohomology.singIn_iso (Submission.Sphere.Sph 1)
          (Submission.Sphere.capMinus 0))) 0)).trans
        (Classical.choice (Work.Cohomology.H_zero_connected
          (TopCat.of ↥(Submission.Sphere.capMinus 0)))))
  have e_C : Submission.Cohomology.H
      (Submission.Sphere.capAsub 0 ⊓ Submission.Sphere.capBsub 0 :
        (Submission.Sphere.smallC 0).Subcomplex) ℚ 0 ≃ₗ[ℚ] ℚ × ℚ :=
    (Submission.Sphere.capCIso 0 0).trans ((Submission.Sphere.capPrimeIso 0 0).trans
      ((Submission.Sphere.dpSpaceIso 0 0).trans ((Submission.Sphere.dpSphereIso 0 0).trans
        (Classical.choice Work.Sphere.H_sph_zero.2))))
  -- the Mayer–Vietoris maps
  have hAB : Submission.Sphere.capAsub 0 ⊔ Submission.Sphere.capBsub 0 = ⊤ :=
    Submission.Sphere.capAsub_sup_capBsub 0
  have hfinj : Function.Injective (Submission.Cohomology.mvAlphaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0) :=
    Submission.Cohomology.mvAlphaH_injective_zero (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB
  have hkerf : LinearMap.ker (Submission.Cohomology.mvAlphaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hfinj
  have hkg : LinearMap.ker (Submission.Cohomology.mvBetaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0)
      = LinearMap.range (Submission.Cohomology.mvAlphaH (Submission.Sphere.smallC 0)
        (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0) :=
    Work.Cohomology.mvBetaH_ker_eq_range (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0
  have hkerδ : LinearMap.ker (Submission.Cohomology.mvConnecting (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0)
      = LinearMap.range (Submission.Cohomology.mvBetaH (Submission.Sphere.smallC 0)
        (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0) :=
    Work.Cohomology.mvConnecting_ker_eq_range (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0
  have hδsurj : Function.Surjective (Submission.Cohomology.mvConnecting (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0) :=
    Work.Cohomology.mvConnecting_surjective (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0
      (Submission.Sphere.subsingleton_H_capAsub 0 1 (by norm_num))
      (Submission.Sphere.subsingleton_H_capBsub 0 1 (by norm_num))
  -- `range f ≅ ℚ`
  have e_rangef : LinearMap.range (Submission.Cohomology.mvAlphaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0) ≃ₗ[ℚ] ℚ :=
    (LinearMap.quotKerEquivRange (Submission.Cohomology.mvAlphaH (Submission.Sphere.smallC 0)
        (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0)).symm.trans
      ((Submodule.quotEquivOfEqBot (LinearMap.ker (Submission.Cohomology.mvAlphaH
          (Submission.Sphere.smallC 0) (Submission.Sphere.capAsub 0)
          (Submission.Sphere.capBsub 0) 0)) hkerf).trans e_V)
  -- `W ≅ ℚ × ℚ`
  have e_W : (Submission.Cohomology.H (Submission.Sphere.capAsub 0) ℚ 0 ×
      Submission.Cohomology.H (Submission.Sphere.capBsub 0) ℚ 0) ≃ₗ[ℚ] ℚ × ℚ :=
    e_A.prodCongr e_B
  obtain ⟨e_Wf⟩ := quotient_rat_sq_iso_rat e_W
    (LinearMap.range (Submission.Cohomology.mvAlphaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0)) e_rangef
  -- `range g ≅ ℚ`
  have e_rangeg : LinearMap.range (Submission.Cohomology.mvBetaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0) ≃ₗ[ℚ] ℚ :=
    (LinearMap.quotKerEquivRange (Submission.Cohomology.mvBetaH (Submission.Sphere.smallC 0)
        (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0)).symm.trans
      ((Submodule.quotEquivOfEq (LinearMap.ker (Submission.Cohomology.mvBetaH
          (Submission.Sphere.smallC 0) (Submission.Sphere.capAsub 0)
          (Submission.Sphere.capBsub 0) 0))
        (LinearMap.range (Submission.Cohomology.mvAlphaH (Submission.Sphere.smallC 0)
          (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0)) hkg).trans e_Wf)
  obtain ⟨e_Ug⟩ := quotient_rat_sq_iso_rat e_C
    (LinearMap.range (Submission.Cohomology.mvBetaH (Submission.Sphere.smallC 0)
      (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0)) e_rangeg
  -- assemble
  have e_small : Submission.Cohomology.H (Submission.Sphere.smallC 0) ℚ 1 ≃ₗ[ℚ] ℚ :=
    (Submission.Cohomology.mvConnecting (Submission.Sphere.smallC 0)
        (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) hAB 0).quotKerEquivOfSurjective
        hδsurj |>.symm |>.trans
      ((Submodule.quotEquivOfEq (LinearMap.ker (Submission.Cohomology.mvConnecting
          (Submission.Sphere.smallC 0) (Submission.Sphere.capAsub 0)
          (Submission.Sphere.capBsub 0) hAB 0))
        (LinearMap.range (Submission.Cohomology.mvBetaH (Submission.Sphere.smallC 0)
          (Submission.Sphere.capAsub 0) (Submission.Sphere.capBsub 0) 0)) hkerδ).trans e_Ug)
  exact ⟨(Submission.Sphere.smallSphereIso 0 1).symm.trans e_small⟩

end Work.Sphere
