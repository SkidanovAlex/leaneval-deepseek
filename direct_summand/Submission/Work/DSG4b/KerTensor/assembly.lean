import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSM2b.assembly_aux
import Submission.Work.DSG4b.KerTensor.mem_range_of_forall_sub_mem

/-!
# Flatness of an adic completion via the general-ideal Bhatt/Stacks criterion

This file contains the assembly step of the proof that `AdicCompletion I A` is flat over `R`,
adapting `Work.DSM2b.flat_of_flat_mod_base_aux` (Bhatt's Proposition 4.1, flat part) from the
principal case `I = (π)` to an arbitrary ideal `I ⊆ R`.

The three inputs are:

* `hA`  : `B ⧸ I ^ n B` is flat over `R ⧸ I ^ n R` for every `n`;
* `hAR` : elementwise Artin–Rees for `I`: `g x ∈ I ^ n` coordinatewise implies
          `x ∈ ker g + I ^ (n - c) R ^ k`;
* `hsyz`: the mod-`I ^ n` syzygy statement with Artin–Rees loss (`Work.DSG4b.KerTensor.syzygy_mod_pow`).

The main content is the "coordinate" statement `ker (linCombB a) ≤ spanBase (ker a)`, obtained by
combining `hsyz` with the general limit step
`Work.DSG4b.KerTensor.mem_range_of_forall_sub_mem` and a presentation of `ker a`; the transfer to
`LinearMap.lTensor B` and the flatness criterion `Module.Flat.iff_lTensor_injective` follow as in the
principal case.
-/

namespace Work.DSG4b.KerTensor

universe u

open TensorProduct

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- **Flatness of `R → B` from the three ingredients (general ideal).** -/
theorem flat_of_flat_mod_base_general [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete (I.map (algebraMap R B)) B]
    (hA : ∀ n : ℕ, Module.Flat (R ⧸ I ^ n) (B ⧸ (I ^ n).map (algebraMap R B)))
    (hAR : ∀ {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)), ∃ c, ∀ n (x : Fin k → R),
      (∀ i, g x i ∈ I ^ n) →
        ∃ z ∈ I ^ (n - c) • (⊤ : Submodule R (Fin k → R)), x - z ∈ LinearMap.ker g)
    (hsyz : ∀ {k m : ℕ} (g : (Fin k → R) →ₗ[R] (Fin m → R)) (c : ℕ),
      (∀ n (x : Fin k → R), (∀ i, g x i ∈ I ^ n) →
        ∃ z ∈ I ^ (n - c) • (⊤ : Submodule R (Fin k → R)), x - z ∈ LinearMap.ker g) →
      (∀ n : ℕ, Module.Flat (R ⧸ I ^ n) (B ⧸ (I ^ n).map (algebraMap R B))) →
      ∀ n {y : Fin k → B}, (∀ i, Work.DSM2b.coordBase g y i ∈ (I ^ n).map (algebraMap R B)) →
        ∃ w : Fin k → B, w ∈ Work.DSM2b.spanBase (LinearMap.ker g) ∧
          ∀ i, (y - w) i ∈ (I ^ (n - c)).map (algebraMap R B)) :
    Module.Flat R B := by
  -- (1) the coordinate statement
  have key : ∀ {l : ℕ} (a : (Fin l → R) →ₗ[R] R) {u : Fin l → B},
      Work.DSM2b.linCombB (fun i => a (Pi.single i 1)) u = 0 →
        u ∈ Work.DSM2b.spanBase (LinearMap.ker a) := by
    intro l a u hu
    haveI : Module.Finite R (LinearMap.ker a) := inferInstance
    obtain ⟨t, ρ₀, hρ₀⟩ := Module.Finite.exists_fin' R (LinearMap.ker a)
    set ρ : (Fin t → R) →ₗ[R] (Fin l → R) := (LinearMap.ker a).subtype.comp ρ₀ with hρdef
    have hρrange : LinearMap.range ρ = LinearMap.ker a := by
      rw [hρdef, LinearMap.range_comp, LinearMap.range_eq_top.mpr hρ₀, Submodule.map_top,
        Submodule.range_subtype]
    -- Artin–Rees constants
    obtain ⟨ca, hca⟩ := hAR (LinearMap.pi (fun _ : Fin 1 => a))
    obtain ⟨cρ, hcρ⟩ := hAR ρ
    -- the approximation property
    have happrox : ∀ N, ∃ z : Fin t → B, ∀ i, (u - Work.DSM2b.coordBase ρ z) i ∈
        (I ^ N).map (algebraMap R B) := by
      intro N
      have hcoord : ∀ i : Fin 1,
          Work.DSM2b.coordBase (LinearMap.pi (fun _ : Fin 1 => a)) u i ∈
          (I ^ (N + ca)).map (algebraMap R B) := by
        intro i
        rw [Work.DSM2b.coordBase_pi_finOne_apply]
        simp [hu]
      obtain ⟨w, hw, hwmem⟩ :=
        hsyz (LinearMap.pi (fun _ : Fin 1 => a)) ca hca hA (N + ca) hcoord
      have hw' : w ∈ Work.DSM2b.spanBase (LinearMap.ker a) := by
        rw [Work.DSM2b.ker_pi_finOne] at hw
        exact hw
      rw [← hρrange, ← Work.DSM2b.range_coordBase_eq_spanBase_range ρ] at hw'
      obtain ⟨z, hz⟩ := hw'
      refine ⟨z, fun i => ?_⟩
      have hwmem' : (u - w) i ∈ (I ^ N).map (algebraMap R B) := by
        have h := hwmem i
        rwa [Nat.add_sub_cancel] at h
      rw [hz]
      exact hwmem'
    -- the limit step
    rw [← hρrange, ← Work.DSM2b.range_coordBase_eq_spanBase_range ρ]
    refine mem_range_of_forall_sub_mem (I.map (algebraMap R B)) (Work.DSM2b.coordBase ρ) cρ ?_ u ?_
    · intro N z hz
      obtain ⟨w, hw, hwmem⟩ := hsyz ρ cρ hcρ hA N (by
        intro i
        rw [Ideal.map_pow]
        exact hz i)
      exact ⟨w, Work.DSM2b.spanBase_ker_le_ker_coordBase ρ hw, by
        intro i
        rw [← Ideal.map_pow]
        exact hwmem i⟩
    · intro N
      obtain ⟨z, hz⟩ := happrox N
      exact ⟨z, by
        intro i
        rw [← Ideal.map_pow]
        exact hz i⟩
  -- (2) transfer to `LinearMap.lTensor`
  have keyl : ∀ {l : ℕ} (a : (Fin l → R) →ₗ[R] R),
      LinearMap.ker (LinearMap.lTensor B a) ≤
        LinearMap.range (LinearMap.lTensor B (LinearMap.ker a).subtype) := by
    intro l a x hx
    have hy0 : Work.DSM2b.linCombB (fun i => a (Pi.single i 1))
        (TensorProduct.piScalarRight R B B (Fin l) x) = 0 := by
      have h := Work.DSM2b.rid_lTensor_linComb_eq (R := R) (B := B)
        (w := fun i => a (Pi.single i 1)) x
      rw [Work.DSM2b.linComb_apply_single a] at h
      rw [← h, LinearMap.mem_ker.mp hx]
      simp
    have hy : TensorProduct.piScalarRight R B B (Fin l) x ∈
        Work.DSM2b.spanBase (LinearMap.ker a) :=
      key a hy0
    obtain ⟨s, hs⟩ := Work.DSM2b.exists_map_of_mem_spanBase' (B := B) (LinearMap.ker a) hy
    refine LinearMap.mem_range.mpr ⟨s, ?_⟩
    rw [LinearEquiv.symm_apply_apply] at hs
    exact hs
  -- (3) the flatness criterion
  rw [Module.Flat.iff_lTensor_injective]
  intro J hJ
  haveI : Module.Finite R J := Module.Finite.iff_fg.mpr hJ
  obtain ⟨l, f, hf⟩ := Module.Finite.exists_fin' R J
  set a : (Fin l → R) →ₗ[R] R := J.subtype.comp f with hadef
  have haeq : LinearMap.lTensor B a =
      (LinearMap.lTensor B J.subtype).comp (LinearMap.lTensor B f) := by
    rw [hadef, LinearMap.lTensor_comp]
  have hzf : f.comp (LinearMap.ker a).subtype = 0 := by
    rw [hadef]
    exact Work.DSM2b.comp_subtype_ker_eq_zero J f
  intro x y hxy
  have hsub : (LinearMap.lTensor B J.subtype) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨x', hx'⟩ : ∃ x', LinearMap.lTensor B f x' = x - y :=
    LinearMap.lTensor_surjective B hf (x - y)
  have hax : (LinearMap.lTensor B a) x' = 0 := by
    rw [haeq, LinearMap.comp_apply, hx', hsub]
  obtain ⟨s, hs⟩ := keyl a hax
  have hz : x - y = 0 := by
    rw [← hx', ← hs, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      show f ∘ₗ (LinearMap.ker a).subtype = 0 from hzf]
    simp
  exact sub_eq_zero.mp hz

end Work.DSG4b.KerTensor
