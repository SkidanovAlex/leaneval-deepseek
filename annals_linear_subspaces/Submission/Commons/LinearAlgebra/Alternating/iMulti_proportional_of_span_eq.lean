import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option autoImplicit true

open exteriorPower
open Set
set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.Alternating

/-- Over a field, the exterior product of a linearly independent family of `k` vectors is
nonzero in the `k`th exterior power. -/
lemma ιMulti_ne_zero_of_linearIndependent {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M]
    [Module 𝕜 M] {k : ℕ} (f : Fin k → M) (hf : LinearIndependent 𝕜 f) :
    exteriorPower.ιMulti 𝕜 k f ≠ 0 := by
  classical
  let s : ↑(Set.powersetCard (Fin k) k) := ⟨Finset.univ, by simp [Finset.card_univ]⟩
  have hli : LinearIndependent 𝕜 (exteriorPower.ιMulti_family 𝕜 k f) :=
    exteriorPower.ιMulti_family_linearIndependent_field (K := 𝕜) (E := M) (n := k) hf
  have hne : exteriorPower.ιMulti_family 𝕜 k f s ≠ 0 := by
    exact LinearIndependent.ne_zero s hli
  let τ : Fin k ↪o Fin k := Set.powersetCard.ofFinEmbEquiv.symm s
  have τinj : Function.Injective (fun i : Fin k => τ i) := by
    exact RelEmbedding.injective τ
  have τbij : Function.Bijective (fun i : Fin k => τ i) := τinj.bijective_of_finite
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective (fun i : Fin k => τ i) τbij
  have hval : exteriorPower.ιMulti_family 𝕜 k f s =
      exteriorPower.ιMulti 𝕜 k (f ∘ (fun i : Fin k => σ i)) := by
    simp [exteriorPower.ιMulti_family, σ, τ]
  have hperm : exteriorPower.ιMulti 𝕜 k (f ∘ (fun i : Fin k => σ i)) =
      (Equiv.Perm.sign σ) • exteriorPower.ιMulti 𝕜 k f := by
    simpa using (exteriorPower.ιMulti 𝕜 k (M := M)).map_perm f σ
  by_contra hz
  apply hne
  calc
    exteriorPower.ιMulti_family 𝕜 k f s =
        exteriorPower.ιMulti 𝕜 k (f ∘ (fun i : Fin k => σ i)) := hval
    _ = (Equiv.Perm.sign σ) • exteriorPower.ιMulti 𝕜 k f := hperm
    _ = 0 := by simp [hz]

/-- If `u` and `v` are two linearly independent `k`-tuples spanning the same subspace of a
module over a field, then their `k`th exterior products differ by a nonzero scalar. -/
lemma iMulti_proportional_of_span_eq {𝕜 : Type*} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
    {k : ℕ} (u v : Fin k → M) (hu : LinearIndependent 𝕜 u) (hv : LinearIndependent 𝕜 v)
    (hspan : Submodule.span 𝕜 (Set.range u) = Submodule.span 𝕜 (Set.range v)) :
    ∃ a : 𝕜, a ≠ 0 ∧ exteriorPower.ιMulti 𝕜 k u = a • exteriorPower.ιMulti 𝕜 k v := by
  classical
  let W : Submodule 𝕜 M := Submodule.span 𝕜 (Set.range v)
  have huWmem : ∀ i : Fin k, u i ∈ W := by
    intro i
    change u i ∈ Submodule.span 𝕜 (Set.range v)
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  let uW : Fin k → W := fun i => ⟨u i, huWmem i⟩
  have hcompu : W.subtype ∘ uW = u := by
    ext i
    rfl
  have huW : LinearIndependent 𝕜 uW := by
    have hu' : LinearIndependent 𝕜 (W.subtype ∘ uW) := by
      rwa [hcompu]
    exact LinearIndependent.of_comp (f := W.subtype) (v := uW) hu'
  haveI : Module.Finite 𝕜 W := Module.Finite.of_basis (Module.Basis.span hv)
  haveI : Module.Free 𝕜 W := Module.Free.of_basis (Module.Basis.span hv)
  let bv : Module.Basis (Fin k) 𝕜 W := Module.Basis.span hv
  have hfinW : Module.finrank 𝕜 W = k := by
    rw [Module.finrank_eq_card_basis bv]
    simp
  have hfinP : Module.finrank 𝕜 (⋀[𝕜]^k W) = 1 := by
    rw [exteriorPower.finrank_eq (R := 𝕜) (M := W) (n := k)]
    rw [hfinW]
    simp
  let xw : ⋀[𝕜]^k W := exteriorPower.ιMulti 𝕜 k (M := W) uW
  let yw : ⋀[𝕜]^k W := exteriorPower.ιMulti 𝕜 k (M := W) (fun i => (bv i : W))
  have hxw_ne : xw ≠ 0 := by
    dsimp [xw]
    exact ιMulti_ne_zero_of_linearIndependent (𝕜 := 𝕜) (M := W) uW huW
  have hyw_ne : yw ≠ 0 := by
    dsimp [yw]
    exact ιMulti_ne_zero_of_linearIndependent (𝕜 := 𝕜) (M := W) (fun i => (bv i : W))
      bv.linearIndependent
  rcases exists_smul_eq_of_finrank_eq_one (K := 𝕜) (V := ⋀[𝕜]^k W) hfinP
      (x := yw) (hx := hyw_ne) (y := xw) with ⟨c, hc_eq⟩
  have hc_ne : c ≠ 0 := by
    intro hc0
    apply hxw_ne
    calc
      xw = c • yw := hc_eq.symm
      _ = 0 := by rw [hc0]; simp
  -- transfer the proportionality down from W to M
  have hxM : exteriorPower.ιMulti 𝕜 k (M := M) u =
      exteriorPower.map (n := k) (f := W.subtype) xw := by
    rw [exteriorPower.map_apply_ιMulti (n := k) (f := W.subtype) (m := uW)]
    rw [hcompu]
  have hcompv : W.subtype ∘ (fun i : Fin k => (bv i : W)) = v := by
    ext i
    exact Module.Basis.coe_span_apply hv i
  have hvM : exteriorPower.ιMulti 𝕜 k (M := M) v =
      exteriorPower.map (n := k) (f := W.subtype) yw := by
    rw [exteriorPower.map_apply_ιMulti (n := k) (f := W.subtype)
      (m := fun i => (bv i : W))]
    rw [hcompv]
  refine ⟨c, hc_ne, ?_⟩
  calc
    exteriorPower.ιMulti 𝕜 k (M := M) u =
        exteriorPower.map (n := k) (f := W.subtype) xw := hxM
    _ = exteriorPower.map (n := k) (f := W.subtype) (c • yw) := by
      rw [hc_eq.symm]
    _ = c • exteriorPower.map (n := k) (f := W.subtype) yw := by simp
    _ = c • exteriorPower.ιMulti 𝕜 k (M := M) v := by rw [hvM]

end Commons.LinearAlgebra.Alternating