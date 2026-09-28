import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic

/-!
# The dual of a discrete lattice of positive rank is nonzero

A discrete `ℤ`-submodule `L ⊆ ℝ^ι` with `rkR L ≥ 1` is a free `ℤ`-module of rank `rkR L`; the
dual basis of a `ℤ`-basis of `L` gives a nonzero element of `dualLat L`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem exists_dual_ne_zero (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    (hrk : 1 ≤ rkR L) : ∃ u ∈ dualLat L, u ≠ 0 := by
  classical
  haveI hfin : Module.Finite ℤ L := inferInstance
  haveI hfree : Module.Free ℤ L := inferInstance
  -- the `ℤ`-rank equals the real rank
  have hrank : Module.finrank ℤ L = rkR L := by
    have h := Real.finrank_eq_int_finrank_of_discrete (E := ι → ℝ) (s := (L : Set (ι → ℝ)))
      (by rw [Submodule.span_eq]; infer_instance)
    rw [Set.finrank, Set.finrank, Submodule.span_eq] at h
    exact h.symm
  -- a `ℤ`-basis of `L`
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = rkR L := by
    rw [← Module.finrank_eq_card_basis b]
    exact hrank
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ L) := by
    rw [← Fintype.card_pos_iff, hcard]
    omega
  let j₀ : Module.Free.ChooseBasisIndex ℤ L := Classical.arbitrary _
  -- the ambient real span and the map `ψ`
  set V : Submodule ℝ (ι → ℝ) := Submodule.span ℝ (L : Set (ι → ℝ)) with hV
  let ψ : V →ₗ[ℝ] (Module.Free.ChooseBasisIndex ℤ L → ℝ) :=
    { toFun := fun x j => dotR (b j : ι → ℝ) (x : ι → ℝ)
      map_add' := fun x y => by
        ext j
        simp [dotR_add_right, Submodule.coe_add]
      map_smul' := fun c x => by
        ext j
        simp [dotR_smul_right, Submodule.coe_smul] }
  have hrepr : ∀ z : L, ((z : L) : ι → ℝ) = ∑ j, (b.repr z j) • ((b j : L) : ι → ℝ) := by
    intro z
    have h := congrArg (fun w : L => ((w : L) : ι → ℝ)) (b.sum_repr z).symm
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  have hspanV : Submodule.span ℝ (Set.range fun j => ((b j : L) : ι → ℝ)) = V := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro y ⟨j, rfl⟩
      exact Submodule.subset_span (b j).2
    · rw [Submodule.span_le]
      intro z hz
      have hz' : z = ∑ j, (b.repr ⟨z, hz⟩ j) • ((b j : L) : ι → ℝ) := hrepr ⟨z, hz⟩
      rw [hz']
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ (b.repr ⟨z, hz⟩ j) ((b j : L) : ι → ℝ)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- `ψ` is injective
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h0 : ψ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hperp : x - y = 0 := by
      have hvan : ∀ w ∈ Submodule.span ℝ (Set.range fun j => ((b j : L) : ι → ℝ)),
          dotR w ((x - y : V) : ι → ℝ) = 0 := by
        intro w hw
        refine Submodule.span_induction
          (p := fun w _ => dotR w ((x - y : V) : ι → ℝ) = 0) ?_ ?_ ?_ ?_ hw
        · rintro w ⟨j, rfl⟩
          have h2 := congrFun h0 j
          simpa [ψ] using h2
        · simp
        · intro a c _ _ ha hc
          rw [dotR_add_left, ha, hc, add_zero]
        · intro c a _ ha
          rw [dotR_smul_left, ha, mul_zero]
      have h3 := hvan ((x - y : V) : ι → ℝ) (by rw [hspanV]; exact (x - y).2)
      exact Subtype.ext (dotR_self_eq_zero.mp h3)
    exact sub_eq_zero.mp hperp
  -- `ψ` is surjective
  have hrange : ψ.range = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h := LinearMap.finrank_range_add_finrank_ker ψ
    have hker : Module.finrank ℝ ψ.ker = 0 := by
      rw [LinearMap.ker_eq_bot.mpr hψinj, finrank_bot]
    rw [hker, add_zero] at h
    have hVcard : Module.finrank ℝ (Module.Free.ChooseBasisIndex ℤ L → ℝ) = Module.finrank ℝ V := by
      rw [Module.finrank_fintype_fun_eq_card, hcard]
      rfl
    omega
  let e : Module.Free.ChooseBasisIndex ℤ L → ℝ := fun j => if j = j₀ then 1 else 0
  obtain ⟨u, hu⟩ : ∃ u : V, ψ u = e := by
    have h1 : e ∈ ψ.range := by rw [hrange]; exact Submodule.mem_top
    exact h1
  -- `u` pairs integrally with `L`
  have hpair0 : dotR ((u : V) : ι → ℝ) ((b j₀ : L) : ι → ℝ) = 1 := by
    have h2 := congrFun hu j₀
    rw [dotR_comm]
    simpa [ψ, e] using h2
  have hpairne : ∀ j, j ≠ j₀ → dotR ((u : V) : ι → ℝ) ((b j : L) : ι → ℝ) = 0 := by
    intro j hj
    have h2 := congrFun hu j
    rw [dotR_comm]
    simpa [ψ, e, hj] using h2
  refine ⟨((u : V) : ι → ℝ), ⟨u.2, ?_⟩, ?_⟩
  · intro z hz
    have hmem : (⟨z, hz⟩ : L) ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; exact Submodule.mem_top
    refine Submodule.span_induction (p := fun w _ => ∃ k : ℤ, dotR ((u : V) : ι → ℝ) ((w : L) : ι → ℝ) = k)
      ?_ ?_ ?_ ?_ hmem
    · rintro w ⟨j, rfl⟩
      by_cases hj : j = j₀
      · exact ⟨1, by rw [hj, hpair0]; norm_num⟩
      · exact ⟨0, by rw [hpairne j hj]; norm_num⟩
    · exact ⟨0, by simp⟩
    · rintro a c _ _ ⟨ka, hka⟩ ⟨kc, hkc⟩
      refine ⟨ka + kc, ?_⟩
      rw [Submodule.coe_add, dotR_add_right, hka, hkc]
      push_cast
      ring
    · rintro (m : ℤ) a _ ⟨ka, hka⟩
      refine ⟨m * ka, ?_⟩
      rw [Submodule.coe_smul, dotR_zsmul_right, hka]
      push_cast
      ring
  · intro hzero
    have hz : u = 0 := Subtype.ext hzero
    rw [hz, map_zero] at hu
    have h2 := congrFun hu j₀
    simp [e] at h2

end Work.HP.Transf
