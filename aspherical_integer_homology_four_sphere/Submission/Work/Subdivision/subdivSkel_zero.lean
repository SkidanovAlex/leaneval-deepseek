/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.SkelLevel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The zero-th skeletal level of the subdivision

The base case of the skeletal induction for `PolyCW.subdiv`: the restriction
`PolyCW.subdivSkel P hdd haug 0` of the subdivision chain map to the `0`-skeleta
is a quasi-isomorphism.

Both `0`-skeleta are concentrated in degree zero:

* on the cellular side `cellSubMod P hdd 0 k = ⊤` for `k = 0` and `⊥` otherwise
  (`PolyCW.cellSubMod_eq_bot`), since the cellular chains in degree `k` are free
  on the `k`-cells;
* on the subdivided side `sdSubMod P 0 k` is spanned by the `k`-simplices all of
  whose vertices are `0`-dimensional cells — and by `PolyCW.dim_lt` a simplex of
  dimension `k ≥ 1` has a strictly larger second vertex, so no such simplex
  exists: `PolyCW.sdSubMod_zero_eq_bot`.

Hence the two complexes are the free `ℤ`-modules on the `0`-cells sitting in
degree `0` (and zero in positive degrees).  In degree `0` the restricted
subdivision map sends the `0`-cell `e` to the `0`-simplex `Simplex.vertex e`
(`PolyCW.subdivCell_zero`), which is an isomorphism:

* injectivity of `PolyCW.subdivLM 0` is proved by exhibiting a left inverse
  (`PolyCW.subdivLM_zero_injective`), and
* the image of `⊤` under `PolyCW.subdivLM 0` contains `sdSubMod P 0 0`
  (`PolyCW.sdSubMod_zero_le_map`).

So `PolyCW.subdivSkel P hdd haug 0` is an isomorphism of chain complexes, hence
a quasi-isomorphism (`quasiIso_of_isIso`).
-/

set_option linter.style.haveILetI false

open CategoryTheory

universe u

namespace Work.Subdivision

namespace PolyCW

variable (P : PolyCW.{u})

/-! ### The subdivided `0`-skeleton -/

/-- A simplex of dimension `k ≥ 1` has a second vertex, which is strictly larger
than the first; hence not all its vertices can be `0`-dimensional cells. -/
theorem not_forall_dim_le_zero {k : ℕ} (hk : 0 < k) (σ : Simplex P.Cell k) :
    ¬ (∀ i, P.dim (σ i) ≤ 0) := by
  intro h
  have hlt : σ ⟨0, Nat.succ_pos k⟩ < σ ⟨1, by omega⟩ :=
    σ.strictMono (by simp [Fin.lt_def])
  have hdim := P.dim_lt hlt.le (ne_of_lt hlt)
  have h1 := h ⟨1, by omega⟩
  omega

/-- The `0`-skeleton of the subdivided chain complex vanishes in positive
degrees. -/
theorem sdSubMod_zero_eq_bot (k : ℕ) (hk : 0 < k) : P.sdSubMod 0 k = ⊥ := by
  show Submodule.span ℤ {x : (P.sdChain).X k | ∃ σ : Simplex P.Cell k,
      (∀ i, P.dim (σ i) ≤ 0) ∧ x = sdElem P σ} = ⊥
  rw [Submodule.span_eq_bot]
  rintro x ⟨σ, hσ, rfl⟩
  exact absurd hσ (not_forall_dim_le_zero P hk σ)

/-! ### The subdivision in degree zero -/

/-- The image of `P.subdivLM 0` contains the whole `0`-skeleton of the
subdivided chain complex: a `0`-simplex whose vertex is a `0`-cell is the
subdivision of that cell. -/
theorem sdSubMod_zero_le_map : P.sdSubMod 0 0 ≤ Submodule.map (P.subdivLM 0) ⊤ := by
  have h : Submodule.span ℤ {x : chainMod P.Cell 0 | ∃ σ : Simplex P.Cell 0,
      (∀ i, P.dim (σ i) ≤ 0) ∧ x = Finsupp.single σ 1} ≤
      Submodule.map (P.subdivLM 0) ⊤ := by
    rw [Submodule.span_le]
    rintro x ⟨σ, hσ, rfl⟩
    have hd : P.dim (σ 0) = 0 := by have := hσ 0; omega
    have hσv : σ = Simplex.vertex (σ 0) := by ext i; fin_cases i; rfl
    refine Submodule.mem_map.mpr ⟨Finsupp.single ⟨σ 0, hd⟩ 1, Submodule.mem_top, ?_⟩
    rw [PolyCW.subdivLM_single, PolyCW.subdivCell_zero, ← hσv]
  exact h

/-- The image of `P.subdivLM 0` lies in the `0`-skeleton of the subdivided
chain complex: the subdivision of a `0`-cell is a `0`-simplex at that cell. -/
theorem subdivLM_zero_mem (x : P.cellMod 0) : P.subdivLM 0 x ∈ P.sdSubMod 0 0 := by
  have h1 : P.subdivLM 0 x = x.sum (fun e c => c • P.subdivCell 0 e) := by
    rw [PolyCW.subdivLM]; exact Finsupp.linearCombination_apply ℤ x
  rw [h1]
  refine Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ ?_
  rw [PolyCW.subdivCell_zero]
  exact sdElem_mem_sdSubMod P (n := 0) (σ := Simplex.vertex e.1) (fun i => by simp [e.2])

/-- Every `0`-chain of the subdivided side which lies in the `0`-skeleton is the
image of a `0`-chain of the cellular side. -/
theorem sdSubMod_zero_mem_image (z : chainMod P.Cell 0) (hz : z ∈ P.sdSubMod 0 0) :
    ∃ w : P.cellMod 0, P.subdivLM 0 w = z := by
  have h : z ∈ Submodule.map (P.subdivLM 0) (⊤ : Submodule ℤ (P.cellMod 0)) :=
    sdSubMod_zero_le_map P hz
  obtain ⟨w, -, hw⟩ := Submodule.mem_map.mp h
  exact ⟨w, hw⟩

/-- **Injectivity of the subdivision in degree zero**: a `0`-chain is recovered
from its subdivision by taking the coefficient of the corresponding `0`-simplex. -/
theorem subdivLM_zero_injective : Function.Injective (P.subdivLM 0) := by
  classical
  -- the left inverse: the coefficient of `Simplex.vertex e` is the coefficient of `e`
  let ψ : chainMod P.Cell 0 →ₗ[ℤ] P.cellMod 0 :=
    Finsupp.linearCombination ℤ (fun σ : Simplex P.Cell 0 =>
      if h : P.dim (σ 0) = 0 then Finsupp.single ⟨σ 0, h⟩ 1 else 0)
  have hψa : ∀ a : {e : P.Cell // P.dim e = 0},
      ψ (Finsupp.single (Simplex.vertex a.1) 1) = Finsupp.single a 1 := by
    intro a
    show (Finsupp.linearCombination ℤ (fun σ : Simplex P.Cell 0 =>
        if h : P.dim (σ 0) = 0 then Finsupp.single ⟨σ 0, h⟩ 1 else 0))
        (Finsupp.single (Simplex.vertex a.1) 1) = Finsupp.single a 1
    rw [Finsupp.linearCombination_single, one_smul, Simplex.vertex_apply]
    split_ifs with h
    · exact congrArg (fun x => Finsupp.single x (1 : ℤ)) (Subtype.ext rfl)
    · exact absurd a.2 h
  have hψ : ψ.comp (P.subdivLM 0) = LinearMap.id := by
    refine Finsupp.lhom_ext ?_
    intro a b
    have hsub : P.subdivLM 0 (Finsupp.single a b) = b • P.subdivCell 0 a := by
      rw [PolyCW.subdivLM]; exact Finsupp.linearCombination_single ℤ b a
    rw [LinearMap.comp_apply, LinearMap.id_coe, id_eq, hsub, map_smul, P.subdivCell_zero, hψa,
      Finsupp.smul_single_one]
  intro x y h
  have hx : x = ψ (P.subdivLM 0 x) := by
    have := congrArg (fun (f : P.cellMod 0 →ₗ[ℤ] P.cellMod 0) => f x) hψ
    simpa using this.symm
  have hy : y = ψ (P.subdivLM 0 y) := by
    have := congrArg (fun (f : P.cellMod 0 →ₗ[ℤ] P.cellMod 0) => f y) hψ
    simpa using this.symm
  rw [hx, hy, h]

/-- The value of the restricted subdivision map in degree zero, on an element of
the `0`-skeleton. -/
theorem subdivSkel_zero_apply (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (x : (P.cellSub hdd 0).chain.X 0) :
    (Subtype.val (((P.subdivSkel hdd haug 0).f 0) x) : (P.sdChain).X 0)
      = (ModuleCat.Hom.hom ((P.subdiv hdd haug).f 0)) (Subtype.val x) := by
  have hf : ∀ k, (P.cellSub hdd 0).sub k ≤
      Submodule.comap ((P.subdiv hdd haug).f k).hom ((P.sdSub 0).sub k) :=
    fun k => subdivCpt_mem P hdd haug 0 k
  have h1 : (P.subdivSkel hdd haug 0).f 0
      = (P.cellSub hdd 0).restrictCptMap (P.sdSub 0) (P.subdiv hdd haug) hf 0 := rfl
  conv_lhs => rw [h1]
  change Subtype.val (ModuleCat.Hom.hom
      ((P.cellSub hdd 0).restrictCptMap (P.sdSub 0) (P.subdiv hdd haug) hf 0) x)
    = (ModuleCat.Hom.hom ((P.subdiv hdd haug).f 0)) (Subtype.val x)
  rw [SubData.restrictCptMap_apply, LinearMap.restrict_apply]

/-- **The zero-th skeletal level of the subdivision is an isomorphism** (in
particular a quasi-isomorphism). -/
theorem isIso_subdivSkel_zero (hdd : P.HasDdZero) (haug : P.HasAugZero) :
    IsIso (P.subdivSkel hdd haug 0) := by
  haveI hcomp : ∀ n, IsIso ((P.subdivSkel hdd haug 0).f n) := by
    intro k
    cases k with
    | zero =>
        -- degree `0`: the subdivision of `0`-cells is a bijection
        rw [ConcreteCategory.isIso_iff_bijective]
        constructor
        · intro x y hxy
          have hx := subdivSkel_zero_apply P hdd haug x
          have hy := subdivSkel_zero_apply P hdd haug y
          have h2 : (ModuleCat.Hom.hom ((P.subdiv hdd haug).f 0)) (Subtype.val x)
              = (ModuleCat.Hom.hom ((P.subdiv hdd haug).f 0)) (Subtype.val y) := by
            rw [← hx, ← hy]
            exact congrArg (fun z => (Subtype.val z : (P.sdChain).X 0)) hxy
          have hinj : Function.Injective (ModuleCat.Hom.hom ((P.subdiv hdd haug).f 0)) := by
            rw [PolyCW.subdiv_f_apply]
            exact subdivLM_zero_injective P
          exact Subtype.ext (hinj h2)
        · intro y
          obtain ⟨w, hw⟩ := sdSubMod_zero_mem_image P (Subtype.val y) y.2
          refine ⟨⟨w, Submodule.mem_top⟩, ?_⟩
          apply Subtype.ext
          rw [subdivSkel_zero_apply P hdd haug]
          show (P.subdivLM 0) w = (Subtype.val y : (P.sdChain).X 0)
          exact hw
    | succ k =>
        -- positive degrees: both sides vanish
        have hbot : (P.cellSub hdd 0).chain.X (k + 1)
            = ModuleCat.of ℤ ↥(⊥ : Submodule ℤ (P.cellMod (k + 1))) := by
          rw [SubData.chain_X,
            show (P.cellSub hdd 0).sub (k + 1) = ⊥ from
              cellSubMod_eq_bot P hdd (n := 0) (k := k + 1) (by omega)]
          rfl
        have hbot' : (P.sdSub 0).chain.X (k + 1)
            = ModuleCat.of ℤ ↥(⊥ : Submodule ℤ (chainMod P.Cell (k + 1))) := by
          rw [SubData.chain_X,
            show (P.sdSub 0).sub (k + 1) = ⊥ from sdSubMod_zero_eq_bot P (k + 1) (by omega)]
          rfl
        haveI : Subsingleton ((P.cellSub hdd 0).chain.X (k + 1)) := by
          rw [hbot]
          exact ⟨fun a b => Subtype.ext (by
            have ha : (a : P.cellMod (k + 1)) = 0 := (Submodule.mem_bot ℤ).mp a.2
            have hb : (b : P.cellMod (k + 1)) = 0 := (Submodule.mem_bot ℤ).mp b.2
            rw [ha, hb])⟩
        haveI : Subsingleton ((P.sdSub 0).chain.X (k + 1)) := by
          rw [hbot']
          exact ⟨fun a b => Subtype.ext (by
            have ha : (a : chainMod P.Cell (k + 1)) = 0 := (Submodule.mem_bot ℤ).mp a.2
            have hb : (b : chainMod P.Cell (k + 1)) = 0 := (Submodule.mem_bot ℤ).mp b.2
            rw [ha, hb])⟩
        rw [ConcreteCategory.isIso_iff_bijective]
        exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end PolyCW

/-- **The base case of the skeletal induction for the subdivision**: the
restriction of the subdivision chain map to the `0`-skeleta is a
quasi-isomorphism. -/
theorem subdivSkel_zero (P : Work.Subdivision.PolyCW) (hdd : P.HasDdZero) (haug : P.HasAugZero) :
    QuasiIso (Work.Subdivision.PolyCW.subdivSkel P hdd haug 0) := by
  haveI := PolyCW.isIso_subdivSkel_zero P hdd haug
  exact quasiIso_of_isIso _

end Work.Subdivision
