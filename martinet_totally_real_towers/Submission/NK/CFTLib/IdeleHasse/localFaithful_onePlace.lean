import Mathlib
import Submission.NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm
import Submission.NK.HassePrinciple.IdeleCocycle
import Submission.NK.CFTLib.hilbertReciprocity_cyclic
import Submission.NK.CFTLib.IdeleHasse.onePlace_localNorm
import Submission.NK.CFTLib.IdeleHasse.Descent.hilbertReciprocity_onePlace_local

/-!
# The local components of the global Artin map are faithful at one place

The target of this file, `NK.CFTLib.IdeleHasse.localFaithful_onePlace`, is the statement that a
one-place idèle `onePlace v a` which lies in `Kˣ · N_{L/K}𝕀_L` already lies in `N_{L/K}𝕀_L`; it is
the local faithfulness of the global Artin map (Milne, *CFT*, V.5.3(a)), equivalently Hilbert's
reciprocity law, and it is exactly the arithmetic input the workspace's
`NK.CFTLib.IdeleHasse.hasseNorm_onePlace_cyclic` consumes.

Here we record the **reduction** of that statement to the classical "one place omitted" form of
Hilbert reciprocity: *a global element `x ∈ Kˣ` which is a local norm at every place except
possibly `v₀` is a local norm at `v₀`* (`NK.CFTLib.IdeleHasse.hilbertReciprocity_onePlace`).

Proof of the reduction.  Write `onePlace v₀ a = n · principalIdele K x` with `n ∈ N_{L/K}𝕀_L`,
`x ∈ Kˣ`.  Taking the component at `v ≠ v₀` gives `n v * x = 1`, i.e. `x = (n v)⁻¹`; since the
components of a norm idèle are one-place norm idèles (`onePlace_apply_mem_normImage`, which is the
local–global principle `mem_normImage_iff_localNorm`), `x` is a local norm at every `v ≠ v₀`.  By
Hilbert reciprocity `x` is then a local norm at `v₀` too, and the local–global principle upgrades
this to `principalIdele K x ∈ N_{L/K}𝕀_L`; multiplying by `n` finishes.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The image of `x : Kˣ` in the completion of `K` at the place `v`. -/
def localImage (v : Place K) (x : Kˣ) : (Place.localField K v)ˣ :=
  Units.map (algebraMap K (Place.localField K v)).toMonoidHom x

/-- A component of an idèle-norm is a one-place idèle-norm.

The witnesses may be chosen independently at each place, which is the (proved) local–global
principle for idèle norms `NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm`. -/
theorem onePlace_apply_mem_normImage (hcyc : IsCyclic (L ≃ₐ[K] L)) {n : Idele K}
    (hn : n ∈ Idele.normImage K L) (v : Place K) :
    NK.HassePrinciple.onePlace v (n v) ∈ Idele.normImage K L := by
  haveI := hcyc
  rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm]
  intro w
  by_cases hw : w = v
  · subst hw
    obtain ⟨y, hy⟩ := (Idele.mem_normImage).mp hn
    exact ⟨y, by rw [NK.HassePrinciple.onePlace_apply_self]; exact hy w⟩
  · exact ⟨1, by rw [NK.HassePrinciple.onePlace_apply_ne hw, Idele.normIdeleFun_one_apply]⟩

/-- **The reduction of `localFaithful_onePlace` to the "one place omitted" form of Hilbert
reciprocity.**

`hQ` is the statement that a global element `x ∈ Kˣ` which is a local norm at every place except
possibly `v₀` is a local norm at `v₀`. -/
theorem localFaithful_onePlace_of_onePlace (hcyc : IsCyclic (L ≃ₐ[K] L))
    (hQ : ∀ (x : Kˣ) (v₀ : Place K),
      (∀ v : Place K, v ≠ v₀ →
        NK.HassePrinciple.onePlace v (localImage v x) ∈ Idele.normImage K L) →
      NK.HassePrinciple.onePlace v₀ (localImage v₀ x) ∈ Idele.normImage K L)
    {v₀ : Place K} {a : (Place.localField K v₀)ˣ}
    (h : NK.HassePrinciple.onePlace v₀ a ∈ Idele.normImage K L ⊔ Idele.principalSubgroup K) :
    NK.HassePrinciple.onePlace v₀ a ∈ Idele.normImage K L := by
  haveI := hcyc
  obtain ⟨n, hn, p, hp, hnp⟩ := Subgroup.mem_sup.mp h
  obtain ⟨x, rfl⟩ := Idele.mem_principalSubgroup.mp hp
  -- at every `v ≠ v₀` the component of the principal idèle `x` is `(n v)⁻¹`, a local norm
  have hstep : ∀ v : Place K, v ≠ v₀ →
      NK.HassePrinciple.onePlace v (localImage v x) ∈ Idele.normImage K L := by
    intro v hv
    have hcomp : n v * localImage v x = 1 := by
      have h1 := congrArg (fun z : Idele K => z v) hnp
      rw [Idele.mul_apply, Idele.principalIdele_apply,
        NK.HassePrinciple.onePlace_apply_ne hv] at h1
      exact h1
    have hnv : localImage v x = (n⁻¹) v := by
      rw [Idele.inv_apply]
      calc localImage v x = 1 * localImage v x := (one_mul _).symm
        _ = ((n v)⁻¹ * n v) * localImage v x := by rw [inv_mul_cancel]
        _ = (n v)⁻¹ * (n v * localImage v x) := by rw [mul_assoc]
        _ = (n v)⁻¹ * 1 := by rw [hcomp]
        _ = (n v)⁻¹ := mul_one _
    rw [hnv]
    exact onePlace_apply_mem_normImage hcyc (inv_mem hn) v
  -- hence `x` is a local norm everywhere, so the principal idèle is a norm idèle
  have hPx : Idele.principalIdele K x ∈ Idele.normImage K L := by
    rw [NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm]
    intro v
    have hv : NK.HassePrinciple.onePlace v (localImage v x) ∈ Idele.normImage K L := by
      by_cases hvv : v = v₀
      · rw [hvv]
        exact hQ x v₀ hstep
      · exact hstep v hvv
    obtain ⟨y, hy⟩ := (NK.CFTLib.IdeleHasse.mem_normImage_iff_localNorm _).mp hv v
    refine ⟨y, ?_⟩
    rw [Idele.principalIdele_apply]
    change (Units.map (algebraMap K (Place.localField K v)).toMonoidHom x) =
      Idele.normIdeleFun K L y v
    rw [← NK.HassePrinciple.onePlace_apply_self v
      (Units.map (algebraMap K (Place.localField K v)).toMonoidHom x)]
    exact hy
  rw [← hnp]
  exact mul_mem hn hPx


/-- **The reduction of the target to the "product formula" form of Hilbert reciprocity**
(Milne, *CFT*, VII.8.1(a): the product of the local Artin maps — equivalently the canonical global
Artin map `Φ` — kills the principal idèles).

If `Φ : 𝕀_K →* Gal(L/K)` kills the norm idèles and the principal idèles, and if triviality of `Φ` on
a one-place idèle forces that idèle to be a norm (which is the case for the canonical `Φ`, whose
component at `v` is the local Artin map of `K_v`), then the target holds: given
`onePlace v₀ a = n · principalIdele K x`, applying `Φ` gives `1 = 1 · 1`, so `onePlace v₀ a` is a
norm. -/
theorem localFaithful_onePlace_of_killingArtinMap (hcyc : IsCyclic (L ≃ₐ[K] L))
    {Φ : Idele K →* (L ≃ₐ[K] L)}
    (hnorm : ∀ n ∈ Idele.normImage K L, Φ n = 1)
    (hkill : ∀ x : Kˣ, Φ (Idele.principalIdele K x) = 1)
    (hone : ∀ (v : Place K) (a : (Place.localField K v)ˣ),
      Φ (NK.HassePrinciple.onePlace v a) = 1 →
      NK.HassePrinciple.onePlace v a ∈ Idele.normImage K L)
    {v₀ : Place K} {a : (Place.localField K v₀)ˣ}
    (h : NK.HassePrinciple.onePlace v₀ a ∈ Idele.normImage K L ⊔ Idele.principalSubgroup K) :
    NK.HassePrinciple.onePlace v₀ a ∈ Idele.normImage K L := by
  obtain ⟨n, hn, p, hp, hnp⟩ := Subgroup.mem_sup.mp h
  obtain ⟨x, rfl⟩ := Idele.mem_principalSubgroup.mp hp
  refine hone v₀ a ?_
  rw [← hnp, map_mul, hnorm n hn, hkill x, one_mul]

/-- **The local components of the global Artin map are faithful at one place** (Milne, *CFT*,
V.5.3(a); equivalently the case "the bad set of `x ∈ Kˣ` is not a singleton" of Hilbert
reciprocity).

If the one-place idèle `onePlace v a` lies in `Kˣ · N_{L/K}𝕀_L` then it lies in `N_{L/K}𝕀_L`, i.e.
`a` is a local norm at `v`. -/
theorem localFaithful_onePlace
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hcyc : IsCyclic (L ≃ₐ[K] L))
    {v : NK.GlobalCFT.Place K} {a : (NK.GlobalCFT.Place.localField K v)ˣ}
    (h : NK.HassePrinciple.onePlace v a ∈
      NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K) :
    NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L := by
  haveI := hcyc
  -- The arithmetic input is the "one place omitted" form of Hilbert reciprocity
  -- (`NK.CFTLib.HilbertReciprocityOnePlace`), here proved (modulo the single one-place Brauer
  -- transfer `NK.CFTLib.IdeleHasse.Descent.transferOnePlaceStep`) in
  -- `NK.CFTLib.IdeleHasse.Descent.hilbertReciprocity_onePlace_local`.  Using it here (rather than
  -- the older wiring through `NK.CFTLib.hilbertReciprocity_onePlace_aux`) keeps this file's
  -- dependency cone free of the missing module `NK.CFTLib.IdeleHasse.hilbertReciprocity_cyclotomic`.
  refine localFaithful_onePlace_of_onePlace hcyc ?_ h
  intro x v₀ hx
  refine (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v₀ (localImage v₀ x)).mpr ?_
  exact NK.CFTLib.IdeleHasse.Descent.hilbertReciprocityOnePlace x v₀
    (fun v hv => (NK.CFTLib.IdeleHasse.onePlace_mem_normImage_iff (K := K) (L := L) v
      (localImage v x)).mp (hx v hv))

end NK.CFTLib.IdeleHasse
