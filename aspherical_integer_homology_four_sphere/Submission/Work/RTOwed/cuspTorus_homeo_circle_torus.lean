import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.mbarPt_periodic
import Submission.Work.Cusp.cuspX_outerU_outerY
import Submission.Work.Cusp.outerU_cuspX
import Submission.Work.Cusp.outerY_cuspX
import Submission.Work.Cusp.mbarPt_eq_iff
import Submission.Work.Cusp.CuspCollarAux
import Submission.Work.Cusp.slope_lattice
import Submission.Work.Cusp.kv_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The cusp torus `ℝ³/Λ_v` is a 3-torus

`Work.Cusp.CuspTorus v = E3 ⧸ Λ_v` is the (flat) cusp torus of the `v`-th cusp of the
Ratcliffe–Tschantz manifold `M̄`, where `E3 = ℝ³` and `Λ_v = ⟨κ_{v,1}, κ_{v,2}, κ_{v,3}⟩` is the
cusp lattice (`Work.Cusp.lattice`).  The three generators `κ_{v,i}` of `Λ_v` are pairwise
orthogonal non-zero integral vectors, hence form an `ℝ`-basis of `ℝ³` (`Work.Cusp.kappa`, whose
columns are a signed and scaled permutation of the standard basis).

This file proves that this quotient is the standard 3-torus.  Writing `b` for the basis
`(κ_{v,1}, κ_{v,2}, κ_{v,3})` of `E3`, the coordinate map `b.equivFun : E3 ≃ₗ[ℝ] (Fin 3 → ℝ)`
sends `Λ_v` exactly onto `ℤ³`, hence descends to a homeomorphism

  `ℝ³/Λ_v ≃ₜ (Fin 3 → ℝ/ℤ)`,

and `Fin 3 → ℝ/ℤ` splits off the first coordinate as `ℝ/ℤ × (Fin 2 → ℝ/ℤ)`.

The chain of homeomorphisms is

`ℝ³/Λ_v ≃ (Fin 3 → ℝ)/(the image lattice) ≃ (Fin 3 → ℝ)/(ℤ³) ≃ (Fin 3 → ℝ/ℤ)`,

the middle identification being `Homeomorph.Quotient.congr` along `b.equivFun`, and the last one
being `Topology.IsQuotientMap.homeomorph` applied to the coordinatewise quotient map
`(Fin 3 → ℝ) → (Fin 3 → ℝ/ℤ)` (an open quotient map, being a product of the open quotient maps
`ℝ → ℝ/ℤ`).
-/

namespace Work.RTOwed

open scoped Real InnerProductSpace
open Work.Cusp

/-- The three lattice vectors `κ_{v,1}, κ_{v,2}, κ_{v,3}` of any cusp `v` are pairwise orthogonal:
the columns of `Data.kappa v` are a signed, scaled permutation of the standard basis of `ℤ³`. -/
theorem kv_inner_eq_zero (v : Fin 5) (i j : Fin 3) (h : i ≠ j) :
    ⟪kv v i, kv v j⟫_ℝ = 0 := by
  fin_cases v <;> fin_cases i <;> fin_cases j <;>
    simp_all [kv] <;> norm_num [kappa, PiLp.inner_apply, Fin.sum_univ_three]

/-- The three lattice vectors `κ_{v,1}, κ_{v,2}, κ_{v,3}` of any cusp `v` are linearly independent
over `ℝ`.  Indeed they are pairwise orthogonal and each is non-zero. -/
theorem linearIndependent_kv (v : Fin 5) : LinearIndependent ℝ (kv v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h0 : ∑ i, g i * ⟪kv v i, kv v j⟫_ℝ = 0 := by
    have : ⟪∑ i, g i • kv v i, kv v j⟫_ℝ = 0 := by rw [hg, inner_zero_left]
    rw [sum_inner] at this
    simpa only [real_inner_smul_left] using this
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [kv_inner_eq_zero v i j hij, mul_zero])
    (by simp)] at h0
  have hpos : ‖kv v j‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (kv_ne_zero v j))
  have : ⟪kv v j, kv v j⟫_ℝ = ‖kv v j‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [this] at h0
  exact (mul_eq_zero.mp h0).resolve_right hpos

/-- **The coordinate identification of the cusp torus.**  `ℝ³/Λ_v` is the standard 3-torus: the
`ℝ`-basis `(κ_{v,1}, κ_{v,2}, κ_{v,3})` of `E3` identifies `Λ_v` with `ℤ³ ⊂ ℝ³`, so the coordinate
map descends to a homeomorphism `ℝ³/Λ_v ≃ₜ (Fin 3 → ℝ/ℤ)`. -/
theorem cuspTorus_homeo_pi (v : Fin 5) :
    Nonempty (CuspTorus v ≃ₜ (Fin 3 → AddCircle (1 : ℝ))) := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp [E3]
  -- The basis of `E3` given by the three lattice vectors of the `v`-th cusp.
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 3) ℝ E3, ⇑b = kv v :=
    ⟨basisOfLinearIndependentOfCardEqFinrank (b := kv v) (linearIndependent_kv v) hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank (b := kv v) (linearIndependent_kv v) hcard⟩
  -- `Λ_v = ℤ³` in the `b`-coordinates.
  have hker : ∀ z : E3, z ∈ AddSubgroup.closure (Set.range b) ↔
      ∀ i, ∃ n : ℤ, b.equivFun z i = (n : ℝ) := by
    intro z
    let G : AddSubgroup E3 :=
      { carrier := {w | ∀ i, ∃ n : ℤ, b.equivFun w i = (n : ℝ)}
        zero_mem' := by intro i; exact ⟨0, by simp⟩
        add_mem' := by
          intro x y hx hy i
          obtain ⟨n, hn⟩ := hx i
          obtain ⟨m, hm⟩ := hy i
          refine ⟨n + m, ?_⟩
          rw [map_add, Pi.add_apply, hn, hm]; push_cast; ring
        neg_mem' := by
          intro x hx i
          obtain ⟨n, hn⟩ := hx i
          refine ⟨-n, ?_⟩
          rw [map_neg, Pi.neg_apply, hn]; push_cast; ring }
    have hle : AddSubgroup.closure (Set.range b) ≤ G := by
      rw [AddSubgroup.closure_le]
      rintro x ⟨i, rfl⟩ j
      refine ⟨if i = j then 1 else 0, ?_⟩
      rw [b.equivFun_self i j]
      split <;> simp
    have hge : G ≤ AddSubgroup.closure (Set.range b) := by
      intro w hw
      rw [← b.sum_equivFun w]
      apply AddSubgroup.sum_mem
      intro i _
      obtain ⟨n, hn⟩ := hw i
      rw [hn, Int.cast_smul_eq_zsmul ℝ n (b i)]
      exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) n
    exact ⟨fun h => hle h, fun h => hge h⟩
  -- The coordinatewise quotient map `E3 → (Fin 3 → ℝ/ℤ)` is an open quotient map.
  have hcop : IsOpenQuotientMap (fun x : ℝ => (x : AddCircle (1 : ℝ))) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  have hpc : IsOpenQuotientMap
      (Pi.map (fun _ : Fin 3 => (fun x : ℝ => (x : AddCircle (1 : ℝ))))) :=
    IsOpenQuotientMap.piMap (fun _ => hcop)
  have hS : IsOpenQuotientMap
      (⇑(b.equivFun.toContinuousLinearEquiv.toHomeomorph : E3 ≃ₜ (Fin 3 → ℝ))) :=
    Homeomorph.isOpenQuotientMap _
  have hcomp : IsOpenQuotientMap
      (Pi.map (fun _ : Fin 3 => (fun x : ℝ => (x : AddCircle (1 : ℝ)))) ∘
        ⇑(b.equivFun.toContinuousLinearEquiv.toHomeomorph)) := hpc.comp hS
  set f : C(E3, Fin 3 → AddCircle (1 : ℝ)) :=
    ⟨Pi.map (fun _ : Fin 3 => (fun x : ℝ => (x : AddCircle (1 : ℝ)))) ∘
      ⇑(b.equivFun.toContinuousLinearEquiv.toHomeomorph), hcomp.continuous⟩ with hfdef
  have hfq : Topology.IsQuotientMap ⇑f := hcomp.isQuotientMap
  have hfapply : ∀ x i, ⇑f x i = (b.equivFun x i : AddCircle (1 : ℝ)) := fun x i => rfl
  -- The fibres of `f` are the cosets of `Λ_v`.
  have key1 : ∀ x y : E3,
      (∀ i, (b.equivFun x i : AddCircle (1 : ℝ)) = (b.equivFun y i : AddCircle (1 : ℝ))) ↔
        ∀ i, ∃ n : ℤ, b.equivFun (x - y) i = (n : ℝ) := by
    intro x y
    constructor
    · intro h i
      have hi := h i
      rw [← sub_eq_zero, ← AddCircle.coe_sub (p := (1 : ℝ)), AddCircle.coe_eq_zero_iff] at hi
      obtain ⟨n, hn⟩ := hi
      rw [zsmul_one] at hn
      refine ⟨n, ?_⟩
      rw [map_sub, Pi.sub_apply]
      exact hn.symm
    · intro h i
      obtain ⟨n, hn⟩ := h i
      rw [← sub_eq_zero, ← AddCircle.coe_sub (p := (1 : ℝ)), AddCircle.coe_eq_zero_iff]
      refine ⟨n, ?_⟩
      rw [zsmul_one]
      rw [map_sub, Pi.sub_apply] at hn
      exact hn.symm
  have hrel : ∀ x y, QuotientAddGroup.leftRel (AddSubgroup.closure (Set.range b)) x y ↔
      Setoid.ker ⇑f x y := by
    intro x y
    rw [QuotientAddGroup.leftRel_apply]
    show (-x + y) ∈ AddSubgroup.closure (Set.range b) ↔ ⇑f x = ⇑f y
    rw [show -x + y = -(x - y) by abel, AddSubgroup.neg_mem_iff, funext_iff]
    constructor
    · intro h i
      have hi := (key1 x y).mpr ((hker (x - y)).mp h) i
      rwa [hfapply, hfapply]
    · intro h
      rw [hker]
      exact (key1 x y).mp (fun i => by have := h i; rwa [hfapply, hfapply] at this)
  have hlattice : lattice v = AddSubgroup.closure (Set.range b) := by rw [lattice, ← hb]
  exact ⟨(Homeomorph.Quotient.congr (X := E3) (Y := E3)
      (rX := QuotientAddGroup.leftRel (lattice v))
      (rY := QuotientAddGroup.leftRel (AddSubgroup.closure (Set.range b)))
      (Homeomorph.refl E3) (fun x y => by rw [hlattice]; rfl)).trans
    ((Homeomorph.Quotient.congrRight hrel).trans (Topology.IsQuotientMap.homeomorph hfq))⟩

/-- **The cusp torus is a 3-torus.**  For every cusp `v` the truncation torus
`T³_v = ℝ³/Λ_v = Work.Cusp.CuspTorus v` is homeomorphic to `ℝ/ℤ × (ℝ/ℤ)²`. -/
theorem cuspTorus_homeo_circle_torus (v : Work.Space.Cusp) :
    Nonempty (Work.Cusp.CuspTorus v ≃ₜ
      AddCircle (1 : ℝ) × (Fin 2 → AddCircle (1 : ℝ))) := by
  obtain ⟨h⟩ := cuspTorus_homeo_pi v
  refine ⟨h.trans ?_⟩
  exact (Fin.appendHomeomorph (X := AddCircle (1 : ℝ)) 1 2).symm.trans
    ((Homeomorph.piUnique (fun _ : Fin 1 => AddCircle (1 : ℝ))).prodCongr (Homeomorph.refl _))

end Work.RTOwed
