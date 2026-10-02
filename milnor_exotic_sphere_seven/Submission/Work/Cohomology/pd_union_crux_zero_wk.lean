import Mathlib
import Submission.Work.Cohomology.pd_union_crux_zero
import Submission.Work.Cohomology.crux_cap_boundary_in_U
import Submission.Work.Cohomology.mv_boundary_d_of_small_cycle
import Submission.Work.Cohomology.pd_crux_weak

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial CategoryTheory.Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- **The crux identity, with the total chain only assumed to have its boundary supported in
`Kᶜ`.**  This is the chain-level content of `crux_cap_boundary_in_U` with the witness pinned down,
in the weak form in which `d (α₁+α₂+α₃)` is only required to be supported in `Kᶜ` (rather than
zero).  The identity is

  `d (cap φ (mj+1) α₁ + cap φA (mj+1) α₂)
     = (-1)^(k+1) • cap (δφA) mj (capIdx k mj ▸ α₂)`.

The proof is the arithmetic of `pd_crux_weak2`: `φA` kills the `Kᶜ`-supported boundary of the
total chain, hence `cap φA mj (dα₂) = - cap φA mj (dα₁)`; `φB` kills the `Lᶜ`-supported boundary
of `α₁`; and the boundary formula `cap_d` together with `δφ = 0` then computes both sides. -/
private lemma crux_eq_weak {X : TopCat} {K L : Set X} {k mj : ℕ}
    (α₁ α₂ α₃ : (singularChains ℤ X).X (k + (mj + 1)))
    (φ φA φB : Cochain ℤ (TopCat.toSSet.obj X) k)
    (hφA : φA ∈ relKern ℤ X Kᶜ k) (hφB : φB ∈ relKern ℤ X Lᶜ k)
    (hlift : φ = φA - φB)
    (hL : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁ ∈
      LinearMap.range ((inclChains X Lᶜ).f (k + mj)).hom)
    (hK : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ ∈
      LinearMap.range ((inclChains X Kᶜ).f (k + mj)).hom)
    (hd : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃) ∈
      LinearMap.range ((inclChains X Kᶜ).f (k + mj)).hom)
    (hφd : cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φ = 0) :
    (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁
          + cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)
      = (-1 : ℤ) ^ (k + 1) • cap ℤ (TopCat.toSSet.obj X)
          (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂) := by
  obtain ⟨e', he'⟩ := hL
  obtain ⟨f', hf'⟩ := hK
  obtain ⟨g', hg'⟩ := hd
  -- `φB` kills the boundary of `α₁` (supported in `Lᶜ`)
  have hzeroB : cap ℤ (TopCat.toSSet.obj X) φB mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) = 0 := by
    rw [← he']
    exact cap_inclChains_eq_zero X Lᶜ φB hφB mj e'
  -- `φA` kills the boundary of `α₃` (supported in `Kᶜ`)
  have hzeroA3 : cap ℤ (TopCat.toSSet.obj X) φA mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃) = 0 := by
    rw [← hf']
    exact cap_inclChains_eq_zero X Kᶜ φA hφA mj f'
  -- `φA` kills the boundary of the total chain (supported in `Kᶜ`)
  have hzeroAtot : cap ℤ (TopCat.toSSet.obj X) φA mj
      ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)) = 0 := by
    rw [← hg']
    exact cap_inclChains_eq_zero X Kᶜ φA hφA mj g'
  -- the boundary of the total chain splits
  have hdsum : (singularChains ℤ X).d (k + (mj + 1)) (k + mj) (α₁ + α₂ + α₃)
      = (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁
        + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂
        + (singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₃ := by
    rw [map_add, map_add]
  -- hence `cap φA mj (dα₂) = - cap φA mj (dα₁)`
  have hA2 : cap ℤ (TopCat.toSSet.obj X) φA mj
        ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂)
      = - cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁) := by
    have hsum : cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)
        + cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) = 0 := by
      have h := hzeroAtot
      rw [hdsum] at h
      rw [map_add, map_add, hzeroA3, add_zero] at h
      exact h
    exact eq_neg_of_add_eq_zero_right hsum
  -- the cap of `d α₁` with `φ` is the cap of `d α₂` with `φA`, up to sign
  have hP : cap ℤ (TopCat.toSSet.obj X) φ mj
        ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₁)
      = - cap ℤ (TopCat.toSSet.obj X) φA mj
          ((singularChains ℤ X).d (k + (mj + 1)) (k + mj) α₂) := by
    rw [hlift, cap_sub_apply, hzeroB, sub_zero, hA2, neg_neg]
  -- the boundary formula for the cocycle `φ` applied to `α₁`
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
  -- the boundary formula for `φA` applied to `α₂`
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
  -- the arithmetic combination
  have key : (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj)
        (cap ℤ (TopCat.toSSet.obj X) φ (mj + 1) α₁)
      - (-1 : ℤ) ^ (k + 1) •
          cap ℤ (TopCat.toSSet.obj X) (cochainDiff ℤ (TopCat.toSSet.obj X) (n := k) φA) mj
            ((capIdx k mj) ▸ α₂)
      = - (ModuleCat.Hom.hom ((chainC ℤ (TopCat.toSSet.obj X)).d (mj + 1) mj))
          (cap ℤ (TopCat.toSSet.obj X) φA (mj + 1) α₂)) := by
    rw [hA, hP, hB]
    rw [zsmul_neg]
    rw [show (-1 : ℤ) ^ (k + 1) = -(-1 : ℤ) ^ k by rw [pow_succ]; ring, neg_zsmul, zsmul_sub]
    abel
  rw [map_add]
  have hK2 := key
  rw [sub_eq_iff_eq_add] at hK2
  rw [hK2]
  abel

/-- **The `U ∩ V`-supported refinement of the crux identity, weak form.**  In the setting of the
crux square, if in addition the cycle `α₁ + α₂ + α₃` caps with `φ` to a boundary (`hbd`), then the
crux identity's right-hand side is the boundary of a chain supported in `U ∩ V` — i.e. it already
dies in `C_*(U ∩ V)`.

Here the boundary of `α₁ + α₂ + α₃` is only assumed to be *supported in* `Kᶜ` (`hd`) rather than
zero; the crux identity `crux_eq_weak` is insensitive to this weakening, and the
Mayer–Vietoris step `mv_boundary_d_of_small_cycle` is applied verbatim as in
`pd_union_crux_zero`. -/
theorem pd_union_crux_zero_wk {X : TopCat} {U V K L : Set X} (hU : IsOpen U) (hV : IsOpen V)
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
    (hd : (Work.Cohomology.singularChains ℤ X).d (k+(mj+1)) (k+mj) (α₁+α₂+α₃) ∈
      LinearMap.range (((Work.Cohomology.inclChains X Kᶜ).f (k+mj)).hom))
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
  have hcrux := crux_eq_weak α₁ α₂ α₃ φ φA φB hφA hφB hlift hL hK hd hφd
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
