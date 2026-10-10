import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.HS.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# First half of the inflation–restriction sequence for a decomposition group

With `D = decomp k A`, `I ⊴ D`, `C = closure (zpowers σ)`, `D = I ⋊ C` (`HS.Setup`), we prove
the elementary half of the Hochschild–Serre exactness: the restriction
`H1loc(D,M) → H1loc(I,M)` lands in the invariants of the conjugation action of `σ`, i.e. for every
locally constant `1`-cocycle `f` on `D` the twisted cocycle `n ↦ res(σ) • f (σ⁻¹ n σ)` has the
same class on `I` as `f` itself.  The difference is the coboundary of the single element `f σ`.
-/

open scoped Pointwise
open Classical

set_option maxHeartbeats 1000000

namespace Work.SSGRoute.HS

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (A : ValuationSubring Ω) (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- **The restriction lands in the invariants.**  For `f ∈ Z¹(D,M)` the class of
`n ↦ res(σ) • f (σ⁻¹ n σ)` in `H1loc(I,M)` is the class of `f` restricted to `I`. -/
theorem toClass_conj_eq (hI : I ≤ SSGRoute.decomp k A)
    (hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I)
    (hσ : σ ∈ SSGRoute.decomp k A)
    {f : (Ω ≃ₐ[k] Ω) → M} (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K M (SSGRoute.decomp k A)) :
    Work.SSGRoute.toClass p k Ω K M I (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) =
      Work.SSGRoute.toClass p k Ω K M I f := by
  rcases hf with ⟨hcoc, hloc⟩
  have hσ' : σ⁻¹ ∈ SSGRoute.decomp k A := (SSGRoute.decomp k A).inv_mem hσ
  have h1zero : f 1 = 0 := by
    have h : f 1 = f 1 + f 1 := by
      have h0 := hcoc 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
      rw [mul_one, map_one, one_smul] at h0
      exact h0
    have h2 : f 1 + (0 : M) = f 1 + f 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  -- the twisted function is a locally constant cocycle on `I`
  have hcoc' : SSGRoute.IsCocycleOn (SSGRoute.res k K) I
      (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) := by
    intro x hx y hy
    have h1 : σ⁻¹ * x * σ ∈ I := hnorm σ⁻¹ hσ' x hx
    have h2 : σ⁻¹ * y * σ ∈ I := hnorm σ⁻¹ hσ' y hy
    have hxy : σ⁻¹ * (x * y) * σ = (σ⁻¹ * x * σ) * (σ⁻¹ * y * σ) := by group
    have hcy := hcoc (σ⁻¹ * x * σ) (hI h1) (σ⁻¹ * y * σ) (hI h2)
    show SSGRoute.res k K σ • f (σ⁻¹ * (x * y) * σ)
      = SSGRoute.res k K σ • f (σ⁻¹ * x * σ) + SSGRoute.res k K x •
        (SSGRoute.res k K σ • f (σ⁻¹ * y * σ))
    rw [hxy, hcy, smul_add]
    congr 1
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul,
      show σ * (σ⁻¹ * x * σ) = x * σ from by group]
  have hloc' : SSGRoute.IsLocConstOn I (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) := by
    obtain ⟨U, hUo, hU⟩ := hloc
    refine ⟨{ carrier := {z | σ⁻¹ * z * σ ∈ U}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, ?_, ?_⟩
    · intro x y hx hy
      change σ⁻¹ * (x * y) * σ ∈ U
      have hx' : σ⁻¹ * x * σ ∈ U := hx
      have hy' : σ⁻¹ * y * σ ∈ U := hy
      rw [show σ⁻¹ * (x * y) * σ = (σ⁻¹ * x * σ) * (σ⁻¹ * y * σ) from by group]
      exact U.mul_mem hx' hy'
    · change σ⁻¹ * (1 : Ω ≃ₐ[k] Ω) * σ ∈ U
      rw [show σ⁻¹ * (1 : Ω ≃ₐ[k] Ω) * σ = 1 from by group]
      exact U.one_mem
    · intro x hx
      change σ⁻¹ * x⁻¹ * σ ∈ U
      have hx' : σ⁻¹ * x * σ ∈ U := hx
      rw [show σ⁻¹ * x⁻¹ * σ = (σ⁻¹ * x * σ)⁻¹ from by group]
      exact U.inv_mem hx'
    · have hset : {z : Ω ≃ₐ[k] Ω | σ⁻¹ * z * σ ∈ U} =
          (fun z : Ω ≃ₐ[k] Ω => σ⁻¹ * (z * σ)) ⁻¹' (U : Set (Ω ≃ₐ[k] Ω)) := by
        ext z
        show (σ⁻¹ * z * σ ∈ U) ↔ (σ⁻¹ * (z * σ) ∈ U)
        rw [mul_assoc]
      change IsOpen {z : Ω ≃ₐ[k] Ω | σ⁻¹ * z * σ ∈ U}
      rw [hset]
      exact hUo.preimage (continuous_const.mul (continuous_id.mul continuous_const))
    · intro x hx u hu huI
      have hmemU : σ⁻¹ * u * σ ∈ U := hu
      have hmemI : σ⁻¹ * u * σ ∈ I := hnorm σ⁻¹ hσ' u huI
      have hu' : σ⁻¹ * (x * u) * σ = (σ⁻¹ * x * σ) * (σ⁻¹ * u * σ) := by group
      show SSGRoute.res k K σ • f (σ⁻¹ * (x * u) * σ) = SSGRoute.res k K σ • f (σ⁻¹ * x * σ)
      rw [hu', hU (σ⁻¹ * x * σ) (hI (hnorm σ⁻¹ hσ' x hx)) (σ⁻¹ * u * σ) hmemU (hI hmemI)]
  have htw : (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) ∈
      Work.SSGRoute.lcCocycles p k Ω K M I := ⟨hcoc', hloc'⟩
  have hfI : (fun n => f n) ∈ Work.SSGRoute.lcCocycles p k Ω K M I := by
    refine ⟨fun x hx y hy => hcoc x (hI hx) y (hI hy), ?_⟩
    obtain ⟨U, hUo, hU⟩ := hloc
    exact ⟨U, hUo, fun x hx u hu huI => hU x (hI hx) u hu (hI huI)⟩
  -- the difference is the coboundary of `f σ`
  have hdiff : (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) - (fun n => f n) ∈
      Work.SSGRoute.coboundaries p k Ω K M I := by
    refine ⟨f σ, fun n hn => ?_⟩
    have hA : f (σ⁻¹ * n * σ) = f σ⁻¹ + SSGRoute.res k K σ⁻¹ • f (n * σ) :=
      hcoc σ⁻¹ hσ' (n * σ) ((SSGRoute.decomp k A).mul_mem (hI hn) hσ)
    have hB : f (n * σ) = f n + SSGRoute.res k K n • f σ := hcoc n (hI hn) σ hσ
    have hC : f σ⁻¹ = -(SSGRoute.res k K σ⁻¹ • f σ) := by
      have h0 := hcoc σ⁻¹ hσ' σ hσ
      rw [inv_mul_cancel, h1zero] at h0
      exact eq_neg_of_add_eq_zero_left h0.symm
    have hsc : ∀ x : M, SSGRoute.res k K σ • (SSGRoute.res k K σ⁻¹ • x) = x := fun x => by
      rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    show SSGRoute.res k K σ • f (σ⁻¹ * n * σ) - f n = SSGRoute.res k K n • f σ - f σ
    rw [hA, hB, hC, smul_add, smul_neg]
    simp only [hsc]
    abel
  -- conclude by additivity of `toClass`
  have hzero : Work.SSGRoute.toClass p k Ω K M I
      ((fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) - (fun n => f n)) = 0 :=
    (Work.SSGRoute.toClass_eq_zero_iff p k Ω K M I (sub_mem htw hfI)).mpr hdiff
  have hsplit : (fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) =
      (fun n => f n) + ((fun n => SSGRoute.res k K σ • f (σ⁻¹ * n * σ)) - (fun n => f n)) := by
    ext n; simp
  rw [hsplit, Work.SSGRoute.toClass_add p k Ω K M I hfI (sub_mem htw hfI), hzero, add_zero]

end

end Work.SSGRoute.HS
