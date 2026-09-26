import Submission.Work.Collar3D.Defs

/-!
# Extending a chart-supported homeomorphism

This is the technical machinery behind every *local* move of the collar toolkit: a homeomorphism
of a chart `Φ : U ≃ₜ M` of `ℝ³` which is the identity outside a compact subset of the model
extends, by the identity outside `U`, to a homeomorphism of `ℝ³` supported in the chart.

* `Work.Collar3D.chartSupport U Φ K` — the *support in `ℝ³`* of a model subset `K ⊆ M`: the image
  of `K` under `Φ.symm` (which is compact whenever `K` is);
* `Work.Collar3D.chartToFun U Φ g` — the underlying *function* of the extension: it is
  `Φ.symm ∘ g ∘ Φ` on `U` and the identity outside `U`; `Work.Collar3D.chartInvFun U Φ g` is the
  same with `g` replaced by `g.symm`;
* `Work.Collar3D.chartEquiv U Φ g` — the bijection they define.

The continuity of `chartToFun` and `chartInvFun` (given that `g` is the identity outside a compact
`K`) is `Work.Collar3D.chartToFun_continuous` / `Work.Collar3D.chartInvFun_continuous`, from which
the ambient homeomorphism `Work.Collar3D.ambientOfChart` is built.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

variable {M : Type*} [TopologicalSpace M]

/-- **The support of a chart-supported homeomorphism, as a subset of `ℝ³`.** -/
def chartSupport (U : Set R3) (Φ : U ≃ₜ M) (K : Set M) : Set R3 :=
  Subtype.val '' ((Φ.symm) '' K)

theorem mem_chartSupport {U : Set R3} {Φ : U ≃ₜ M} {K : Set M} {x : R3} :
    x ∈ chartSupport U Φ K ↔ ∃ hx : x ∈ U, (Φ ⟨x, hx⟩) ∈ K := by
  constructor
  · rintro ⟨u, ⟨y, hy, hyu⟩, hux⟩
    refine ⟨hux ▸ u.2, ?_⟩
    have h1 : (⟨x, hux ▸ u.2⟩ : U) = u := Subtype.ext hux.symm
    rw [h1, ← hyu, Homeomorph.apply_symm_apply]
    exact hy
  · rintro ⟨hx, hxK⟩
    exact ⟨⟨x, hx⟩, ⟨Φ ⟨x, hx⟩, hxK, Homeomorph.symm_apply_apply Φ ⟨x, hx⟩⟩, rfl⟩

/-- The function underlying the extension of a chart-supported homeomorphism. -/
def chartToFun (U : Set R3) (Φ : U ≃ₜ M) (g : M ≃ₜ M) (x : R3) : R3 :=
  if hx : x ∈ U then (Φ.symm (g (Φ ⟨x, hx⟩)) : R3) else x

/-- The function underlying the extension of the inverse chart-supported homeomorphism. -/
def chartInvFun (U : Set R3) (Φ : U ≃ₜ M) (g : M ≃ₜ M) (x : R3) : R3 :=
  if hx : x ∈ U then (Φ.symm (g.symm (Φ ⟨x, hx⟩)) : R3) else x

theorem chartToFun_of_mem {U : Set R3} {Φ : U ≃ₜ M} {g : M ≃ₜ M} {x : R3} (hx : x ∈ U) :
    chartToFun U Φ g x = (Φ.symm (g (Φ ⟨x, hx⟩)) : R3) := by
  rw [chartToFun, dif_pos hx]

theorem chartToFun_of_notMem {U : Set R3} {Φ : U ≃ₜ M} {g : M ≃ₜ M} {x : R3} (hx : x ∉ U) :
    chartToFun U Φ g x = x := by
  rw [chartToFun, dif_neg hx]

theorem chartInvFun_of_mem {U : Set R3} {Φ : U ≃ₜ M} {g : M ≃ₜ M} {x : R3} (hx : x ∈ U) :
    chartInvFun U Φ g x = (Φ.symm (g.symm (Φ ⟨x, hx⟩)) : R3) := by
  rw [chartInvFun, dif_pos hx]

theorem chartInvFun_of_notMem {U : Set R3} {Φ : U ≃ₜ M} {g : M ≃ₜ M} {x : R3} (hx : x ∉ U) :
    chartInvFun U Φ g x = x := by
  rw [chartInvFun, dif_neg hx]

theorem chartInvFun_chartToFun (U : Set R3) (Φ : U ≃ₜ M) (g : M ≃ₜ M) (x : R3) :
    chartInvFun U Φ g (chartToFun U Φ g x) = x := by
  by_cases hx : x ∈ U
  · have hy : (Φ.symm (g (Φ ⟨x, hx⟩)) : R3) ∈ U := (Φ.symm (g (Φ ⟨x, hx⟩))).2
    rw [chartToFun_of_mem hx, chartInvFun_of_mem hy]
    have h1 : (⟨(Φ.symm (g (Φ ⟨x, hx⟩)) : R3), hy⟩ : U) = Φ.symm (g (Φ ⟨x, hx⟩)) :=
      Subtype.ext rfl
    rw [h1, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply,
      Homeomorph.symm_apply_apply]
  · rw [chartToFun_of_notMem hx, chartInvFun_of_notMem hx]

theorem chartToFun_chartInvFun (U : Set R3) (Φ : U ≃ₜ M) (g : M ≃ₜ M) (x : R3) :
    chartToFun U Φ g (chartInvFun U Φ g x) = x := by
  by_cases hx : x ∈ U
  · have hy : (Φ.symm (g.symm (Φ ⟨x, hx⟩)) : R3) ∈ U := (Φ.symm (g.symm (Φ ⟨x, hx⟩))).2
    rw [chartInvFun_of_mem hx, chartToFun_of_mem hy]
    have h1 : (⟨(Φ.symm (g.symm (Φ ⟨x, hx⟩)) : R3), hy⟩ : U) = Φ.symm (g.symm (Φ ⟨x, hx⟩)) :=
      Subtype.ext rfl
    rw [h1, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
      Homeomorph.symm_apply_apply]
  · rw [chartInvFun_of_notMem hx, chartToFun_of_notMem hx]

/-- **The extension of a chart-supported homeomorphism, as a bijection.**  It agrees with
`Φ.symm ∘ g ∘ Φ` on `U` and is the identity outside `U`.  It is a homeomorphism of `ℝ³` as soon
as `g` is the identity outside a compact subset of the model
(`Work.Collar3D.chartToFun_continuous`, `Work.Collar3D.ambientOfChart`). -/
def chartEquiv (U : Set R3) (Φ : U ≃ₜ M) (g : M ≃ₜ M) : R3 ≃ R3 where
  toFun := chartToFun U Φ g
  invFun := chartInvFun U Φ g
  left_inv := chartInvFun_chartToFun U Φ g
  right_inv := chartToFun_chartInvFun U Φ g

@[simp] theorem chartEquiv_apply (U : Set R3) (Φ : U ≃ₜ M) (g : M ≃ₜ M) (x : R3) :
    chartEquiv U Φ g x = chartToFun U Φ g x := rfl

theorem chartEquiv_symm_apply (U : Set R3) (Φ : U ≃ₜ M) (g : M ≃ₜ M) (x : R3) :
    (chartEquiv U Φ g).symm x = chartInvFun U Φ g x := rfl

theorem chartSupport_subset (U : Set R3) (Φ : U ≃ₜ M) (K : Set M) :
    chartSupport U Φ K ⊆ U := fun _ hx => (mem_chartSupport.mp hx).1

theorem chartSupport_eq_image (U : Set R3) (Φ : U ≃ₜ M) (K : Set M) :
    chartSupport U Φ K = (fun y : M => (Φ.symm y : R3)) '' K := by
  ext x
  constructor
  · rintro ⟨u, ⟨y, hy, hyu⟩, hux⟩
    refine ⟨y, hy, ?_⟩
    change ((Φ.symm y : U) : R3) = x
    rw [hyu, hux]
  · rintro ⟨y, hy, hyx⟩
    exact ⟨Φ.symm y, ⟨y, hy, rfl⟩, hyx⟩

theorem chartSupport_isCompact (U : Set R3) (Φ : U ≃ₜ M) {K : Set M} (hK : IsCompact K) :
    IsCompact (chartSupport U Φ K) := by
  rw [chartSupport_eq_image]
  exact hK.image (continuous_subtype_val.comp (Homeomorph.continuous Φ.symm))

theorem chartToFun_eq_self_of_notMem_support (U : Set R3) (Φ : U ≃ₜ M) {g : M ≃ₜ M} {K : Set M}
    (hg : ∀ y : M, y ∉ K → g y = y) {x : R3} (hx : x ∉ chartSupport U Φ K) :
    chartToFun U Φ g x = x := by
  by_cases hU : x ∈ U
  · have hK : Φ ⟨x, hU⟩ ∉ K := fun h => hx (mem_chartSupport.mpr ⟨hU, h⟩)
    rw [chartToFun_of_mem hU, hg _ hK, Homeomorph.symm_apply_apply]
  · exact chartToFun_of_notMem hU

theorem chartInvFun_eq_self_of_notMem_support (U : Set R3) (Φ : U ≃ₜ M) {g : M ≃ₜ M}
    {K : Set M} (hg : ∀ y : M, y ∉ K → g.symm y = y) {x : R3}
    (hx : x ∉ chartSupport U Φ K) : chartInvFun U Φ g x = x := by
  by_cases hU : x ∈ U
  · have hK : Φ ⟨x, hU⟩ ∉ K := fun h => hx (mem_chartSupport.mpr ⟨hU, h⟩)
    rw [chartInvFun_of_mem hU, hg _ hK, Homeomorph.symm_apply_apply]
  · exact chartInvFun_of_notMem hU

end

end Work.Collar3D
