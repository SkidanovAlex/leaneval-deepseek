import Mathlib
import Submission.Work.Cohomology.crux_cap_boundary_in_U
import Submission.Work.Cohomology.mv_boundary_d_of_small_cycle
import Submission.Work.Cohomology.cap_mem_range_inclChains

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The crux identity, in the specific-witness form.**  Under the hypotheses of the crux square,
the *specific* chain `cap φ (mj+1) α₁ + cap φA (mj+1) α₂` (supported in `U`) has boundary
`(-1)^(k+1) • cap (dφA) mj (capIdx k mj ▸ α₂)`.

This is the chain-level content of `crux_cap_boundary_in_U`, but with the witness pinned down so
that it can be compared with a Mayer–Vietoris decomposition. -/
private lemma crux_eq {X : TopCat} {K L : Set X} {k mj : ℕ}
    (α₁ α₂ α₃ : (singularChains ℤ X).X (k + (mj + 1)))
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj X) k)
    (hφA : φA ∈ relKern ℤ X Kᶜ k) (hφB : φB ∈ relKern ℤ X Lᶜ k)
    (hlift : φ = φA - φB)
    (hL : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁ ∈
      LinearMap.range ((inclChains X Lᶜ).f (k + mj)).hom)
    (hK : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ ∈
      LinearMap.range ((inclChains X Kᶜ).f (k + mj)).hom)
    (hd : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃) = 0)
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φ = 0) :
    (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁
          + cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ (k + 1) • cap ℤ (TopCat.toSSet.obj X)
          (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂) := by
  obtain ⟨e', he'⟩ := hL
  obtain ⟨f', hf'⟩ := hK
  have hzeroB : cap ℤ (TopCat.toSSet.obj X) φB mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he']
    exact cap_inclChains_eq_zero X Lᶜ φB hφB mj e'
  have hzeroA : cap ℤ (TopCat.toSSet.obj X) φA mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf']
    exact cap_inclChains_eq_zero X Kᶜ φA hφA mj f'
  have hdα : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
      = - ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
            + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) := by
    have h := hd
    rw [map_add, map_add, add_assoc] at h
    exact eq_neg_of_add_eq_zero_left h
  have hP : cap ℤ (TopCat.toSSet.obj X) φ mj
        ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)
      = - cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) := by
    rw [hlift, cap_sub_apply, hzeroB, sub_zero, hdα, map_neg, map_add, hzeroA, add_zero]
  have hA : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁)
      = (-1 : ℤ) ^ k • cap ℤ (TopCat.toSSet.obj X) φ mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) := by
    have h := cap_d ℤ (TopCat.toSSet.obj X) (n := k) (m := mj) φ α₁
    rw [hφd, cap_zero, LinearMap.zero_apply, sub_zero] at h
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj X)).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj X) φ mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)))
  have hB : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ k • (cap ℤ (TopCat.toSSet.obj X) φA mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)) := by
    have h := cap_d ℤ (TopCat.toSSet.obj X) (n := k) (m := mj) φA α₂
    exact h.trans
      (int_smul_eq_zsmul (inferInstance : Module ℤ (↑((chainC ℤ (TopCat.toSSet.obj X)).X mj)))
        ((-1 : ℤ) ^ k) (cap ℤ (TopCat.toSSet.obj X) φA mj
            ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
          - cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)))
  have key : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)
      = - (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
          (cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂) := by
    rw [hA, hP, hB]
    rw [zsmul_neg]
    rw [show (-1 : ℤ) ^ (k + 1) = -(-1 : ℤ) ^ k by rw [pow_succ]; ring, neg_zsmul, zsmul_sub]
    abel
  rw [map_add]
  have hK2 := key
  rw [sub_eq_iff_eq_add] at hK2
  rw [hK2]
  abel

/-- **The `U ∩ V`-supported refinement of the crux identity.**  In the setting of the crux square,
if in addition the cycle `α₁ + α₂ + α₃` caps with `φ` to a boundary (`hbd`), then the crux
identity's right-hand side is the boundary of a chain supported in `U ∩ V` — i.e. it already dies
in `C_*(U ∩ V)`.

This is the "zero" of `pd_union_crux_zero`: the obstruction to splitting the crux over the cover
`{U, V}` vanishes, because the `U`-part of the Mayer–Vietoris decomposition of the capped cycle may
be replaced (as in `mv_boundary_d_of_small_cycle`) by a boundary supported in `U ∩ V`, and the crux
identity then computes that same boundary. -/
theorem pd_union_crux_zero {X : TopCat} {U V K L : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) {k mj : ℕ}
    (α₁ α₂ α₃ : (Work.Cohomology.singularChains ℤ X).X (k + (mj + 1)))
    (φ φA φB : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj X) k)
    (hφA : φA ∈ Work.Cohomology.relKern ℤ X Kᶜ k) (hφB : φB ∈ Work.Cohomology.relKern ℤ X Lᶜ k)
    (hlift : φ = φA - φB)
    (hα₁ : α₁ ∈ LinearMap.range (((Work.Cohomology.inclChains X (U \ L)).f (k + (mj+1))).hom))
    (hα₂ : α₂ ∈ LinearMap.range (((Work.Cohomology.inclChains X (U ∩ V)).f (k + (mj+1))).hom))
    (hα₃ : α₃ ∈ LinearMap.range (((Work.Cohomology.inclChains X (V \ K)).f (k + (mj+1))).hom))
    (hL : (Work.Cohomology.singularChains ℤ X).d (k+(mj+1)) (k+mj) α₁ ∈
      LinearMap.range (((Work.Cohomology.inclChains X Lᶜ).f (k+mj)).hom))
    (hK : (Work.Cohomology.singularChains ℤ X).d (k+(mj+1)) (k+mj) α₃ ∈
      LinearMap.range (((Work.Cohomology.inclChains X Kᶜ).f (k+mj)).hom))
    (hd : (Work.Cohomology.singularChains ℤ X).d (k+(mj+1)) (k+mj) (α₁+α₂+α₃) = 0)
    (hφd : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φ = 0)
    (hbd : ∃ β : (Work.Cohomology.singularChains ℤ X).X (mj + 2),
        (Work.Cohomology.singularChains ℤ X).d (mj+2) (mj+1) β
          = Work.Cohomology.cap ℤ (TopCat.toSSet.obj X) φ (mj+1) (α₁+α₂+α₃)) :
    ∃ γ ∈ LinearMap.range (((Work.Cohomology.inclChains X (U ∩ V)).f (mj+1)).hom),
        (Work.Cohomology.singularChains ℤ X).d (mj+1) mj γ =
          (-1:ℤ)^(k+1) • Work.Cohomology.cap ℤ (TopCat.toSSet.obj X)
            (Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
              ((Work.Cohomology.capIdx k mj) ▸ α₂) := by
  -- The crux computation, with the explicit witness `cap φ (mj+1) α₁ + cap φA (mj+1) α₂`.
  have hcrux := crux_eq α₁ α₂ α₃ φ φA φB hφA hφB hlift hL hK hd hφd
  -- The two pieces of the Mayer–Vietoris decomposition.
  -- `cap φ α₁` is supported in `U \ L ⊆ U`.
  have h₁U : cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁ ∈
      LinearMap.range ((inclChains X U).f (mj + 1)).hom :=
    mem_range_inclChains_of_subset (M := X) (S := U \ L) (T := U) (fun x hx => hx.1)
      (cap_mem_range_inclChains (M := X) (U \ L) k (mj + 1) φ hα₁)
  -- `cap φA α₂` is supported in `U ∩ V`, hence both in `U` and in `V`.
  have hA₂U : cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂ ∈
      LinearMap.range ((inclChains X U).f (mj + 1)).hom :=
    mem_range_inclChains_of_subset (M := X) (S := U ∩ V) (T := U) (fun x hx => hx.1)
      (cap_mem_range_inclChains (M := X) (U ∩ V) k (mj + 1) φA hα₂)
  have hA₂V : cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂ ∈
      LinearMap.range ((inclChains X V).f (mj + 1)).hom :=
    mem_range_inclChains_of_subset (M := X) (S := U ∩ V) (T := V) (fun x hx => hx.2)
      (cap_mem_range_inclChains (M := X) (U ∩ V) k (mj + 1) φA hα₂)
  -- `cap φ α₂` is supported in `U ∩ V`, hence in `V`.
  have h₂V : cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₂ ∈
      LinearMap.range ((inclChains X V).f (mj + 1)).hom :=
    mem_range_inclChains_of_subset (M := X) (S := U ∩ V) (T := V) (fun x hx => hx.2)
      (cap_mem_range_inclChains (M := X) (U ∩ V) k (mj + 1) φ hα₂)
  -- `cap φ α₃` is supported in `V \ K ⊆ V`.
  have h₃V : cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₃ ∈
      LinearMap.range ((inclChains X V).f (mj + 1)).hom :=
    mem_range_inclChains_of_subset (M := X) (S := V \ K) (T := V) (fun x hx => hx.1)
      (cap_mem_range_inclChains (M := X) (V \ K) k (mj + 1) φ hα₃)
  obtain ⟨β, hβ⟩ := hbd
  -- Apply the Mayer–Vietoris boundary lemma to the boundary `cap φ (α₁+α₂+α₃)`.
  obtain ⟨c, hcmem, hcd⟩ := mv_boundary_d_of_small_cycle (X := X) hU hV hcov
    (z := cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) (α₁ + α₂ + α₃))
    (zU := cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁
      + cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
    (zV := cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₂
      + cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₃
      - cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
    (add_mem h₁U hA₂U)
    (sub_mem (add_mem h₂V h₃V) hA₂V)
    (by rw [map_add, map_add]; abel)
    ⟨β, hβ⟩
  refine ⟨c, hcmem, ?_⟩
  rw [hcd]
  exact hcrux

end

end Work.Cohomology
