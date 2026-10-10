import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Work.SSGRoute.finite_openKernel_homs_decomp_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness of the local `H¹` at a finite place

The target `Work.SSGRoute.local_tate_duality_finite`: for a number field `k`, an algebraic closure
`Ω`, a finite Galois `K/k`, a finite `𝔽_p[Gal(K/k)]`-module `M` and any place `A` of `Ω` over a
finite prime of `k`, the local `H¹`-group `H1loc p k Ω K M (decomp k A) = H¹(D_A, M)` of the
decomposition group `D_A = decomp k A` is **finite**.

## The reduction carried out here

Write `H := D_A = decomp k A` and `U := H ⊓ G_K = decomp k A ⊓ K.fixingSubgroup`; the action of
`D_A` on `M` factors through the restriction `res k K : G_k →* Gal(K/k)`, whose kernel is `G_K`,
so `U` acts trivially on `M` and the quotient of `H` by `U` is a subgroup of the finite group
`Gal(K/k)`.

A locally constant `1`-cocycle `f : H → M` is determined by

* its restriction to `U` (a continuous homomorphism `U → M`, since `U` acts trivially), and
* its values `f (s q)` on a chosen system of coset representatives `s q` of `U` in `H`,

because `x = s (res x) · ((s (res x))⁻¹ x)` for every `x ∈ H` and `f (g u) = g • f u + f g`.
Hence the injection

`{locally constant cocycles on H} ↪ Hom_cont(U, M) × (Gal(K/k) → M)`,

whose target is finite as soon as `Hom_cont(U, M)` is
(`Work.SSGRoute.finite_openKernel_homs_decomp_kernel`, the arithmetic input, proved separately).
The local `H¹` is a quotient of the cocycle group, so it is finite; transporting along the model
bridge `H1locEquivH1_decomp` gives the target.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute

noncomputable section

/-- **The reduction.**  The locally constant `1`-cocycles of the decomposition group at a place
`A` over a finite prime of `k` form a finite set, given finiteness of the continuous
homomorphisms of the kernel `D_A ⊓ G_K = decomp k A ⊓ K.fixingSubgroup` into `M`. -/
theorem finite_Z1_decomp (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type) [AddCommGroup M]
    [Module (ZMod p) M] [Finite M] [DistribMulAction ↥(SSGRoute.decomp k A) M]
    (htriv : ∀ (u : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : M),
      (Subgroup.inclusion inf_le_left u : ↥(SSGRoute.decomp k A)) • m = m) :
    Finite ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A) M) := by
  -- the arithmetic input
  have hcore : Finite {χ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →*
      Multiplicative M // IsOpen (χ.ker : Set ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup))} :=
    finite_openKernel_homs_decomp_kernel p k Ω K A hA M
  -- the finite quotient of `D_A` by `D_A ⊓ G_K`
  have hQmem : ∀ q ∈ (SSGRoute.decomp k A).map (SSGRoute.res k K),
      ∃ σ : ↥(SSGRoute.decomp k A), SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) = q := by
    intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨σ, hσ, hσq⟩
    exact ⟨⟨σ, hσ⟩, hσq⟩
  let s : (K ≃ₐ[k] K) → ↥(SSGRoute.decomp k A) := fun q =>
    if h : q ∈ (SSGRoute.decomp k A).map (SSGRoute.res k K) then Classical.choose (hQmem q h)
    else 1
  have hs : ∀ q (h : q ∈ (SSGRoute.decomp k A).map (SSGRoute.res k K)),
      SSGRoute.res k K (s q : Ω ≃ₐ[k] Ω) = q := by
    intro q h
    simp only [s]
    rw [dif_pos h]
    exact Classical.choose_spec (hQmem q h)
  -- `f 1 = 0` for a crossed homomorphism
  have hzero : ∀ f : ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A) M),
      f.1 (1 : ↥(SSGRoute.decomp k A)) = 0 := by
    intro f
    have h := (Work.AbsoluteKummer.mem_Z1_iff
      (G := ↥(SSGRoute.decomp k A)) (M := M) f.1).mp f.2 |>.1
    have h11 : f.1 (1 : ↥(SSGRoute.decomp k A)) =
        f.1 (1 : ↥(SSGRoute.decomp k A)) + f.1 (1 : ↥(SSGRoute.decomp k A)) := by
      simpa using h 1 1
    have h3 : f.1 (1 : ↥(SSGRoute.decomp k A)) + f.1 (1 : ↥(SSGRoute.decomp k A)) =
        f.1 (1 : ↥(SSGRoute.decomp k A)) + 0 := by
      rw [add_zero]
      exact h11.symm
    exact add_left_cancel h3
  -- the homomorphism induced on the kernel
  let χfun : ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A) M) →
      (↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →* Multiplicative M) := fun f =>
    { toFun := fun u => Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u))
      map_one' := by
        show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left
          (1 : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)))) = Multiplicative.ofAdd (0 : M)
        rw [show (Subgroup.inclusion inf_le_left
          (1 : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) : ↥(SSGRoute.decomp k A)) = 1
          from map_one _]
        rw [hzero f]
      map_mul' := by
        intro a b
        have h := (Work.AbsoluteKummer.mem_Z1_iff
          (G := ↥(SSGRoute.decomp k A)) (M := M) f.1).mp f.2 |>.1
        have h1 := h (Subgroup.inclusion inf_le_left a) (Subgroup.inclusion inf_le_left b)
        show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left (a * b))) =
          Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left a) +
            f.1 (Subgroup.inclusion inf_le_left b))
        rw [show (Subgroup.inclusion inf_le_left (a * b) : ↥(SSGRoute.decomp k A)) =
            Subgroup.inclusion inf_le_left a * Subgroup.inclusion inf_le_left b from map_mul _ a b]
        rw [h1, htriv a (f.1 (Subgroup.inclusion inf_le_left b)), add_comm] }
  -- the kernel of that homomorphism is open
  have hker_open : ∀ f : ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A) M),
      IsOpen ((χfun f).ker : Set ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := by
    intro f
    have hlc := (Work.AbsoluteKummer.mem_Z1_iff
      (G := ↥(SSGRoute.decomp k A)) (M := M) f.1).mp f.2 |>.2
    obtain ⟨V, hVopen, h1V, hV⟩ := hlc (1 : ↥(SSGRoute.decomp k A))
    obtain ⟨W, hWopen, hWV⟩ := isOpen_induced_iff.mp hVopen
    have h1W : (1 : Ω ≃ₐ[k] Ω) ∈ W := by
      have h : (1 : ↥(SSGRoute.decomp k A)) ∈
          (Subtype.val : ↥(SSGRoute.decomp k A) → Ω ≃ₐ[k] Ω) ⁻¹' W := by
        rw [hWV]
        exact h1V
      exact h
    refine Subgroup.isOpen_of_mem_nhds (χfun f).ker (g := 1) ?_
    have hWopen' : IsOpen
        ((fun u : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) => (u : Ω ≃ₐ[k] Ω)) ⁻¹' W) :=
      hWopen.preimage continuous_subtype_val
    have h1W' : (1 : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) ∈
        (fun u : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) => (u : Ω ≃ₐ[k] Ω)) ⁻¹' W := by
      simp only [Set.mem_preimage, Subgroup.coe_one]
      exact h1W
    refine Filter.mem_of_superset (IsOpen.mem_nhds hWopen' h1W') ?_
    intro u hu
    simp only [Set.mem_preimage] at hu
    have huin : (Subgroup.inclusion inf_le_left u : ↥(SSGRoute.decomp k A)) ∈
        (Subtype.val : ↥(SSGRoute.decomp k A) → Ω ≃ₐ[k] Ω) ⁻¹' W := by
      simp only [Set.mem_preimage]
      rwa [Subgroup.coe_inclusion]
    have hVmem : (Subgroup.inclusion inf_le_left u : ↥(SSGRoute.decomp k A)) ∈ V := by
      rw [← hWV]
      exact huin
    show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u)) = 1
    rw [hV _ hVmem, hzero f]
    rfl
  -- the key injectivity statement
  have hkey : ∀ f g : ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A) M), χfun f = χfun g →
      (∀ q : K ≃ₐ[k] K, f.1 (s q) = g.1 (s q)) → f = g := by
    intro f g hχ hval
    apply Subtype.ext
    funext x
    have hχu : ∀ u : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        f.1 (Subgroup.inclusion inf_le_left u) = g.1 (Subgroup.inclusion inf_le_left u) := by
      intro u
      have h' : Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u)) =
          Multiplicative.ofAdd (g.1 (Subgroup.inclusion inf_le_left u)) :=
        congrFun (congrArg DFunLike.coe hχ) u
      exact Multiplicative.ofAdd.injective h'
    have hq : SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.decomp k A).map (SSGRoute.res k K) :=
      ⟨(x : Ω ≃ₐ[k] Ω), x.2, rfl⟩
    have hmemU : ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥(SSGRoute.decomp k A)) :
        Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω) ∈
        SSGRoute.decomp k A ⊓ K.fixingSubgroup := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (SSGRoute.decomp k A).mul_mem
          ((SSGRoute.decomp k A).inv_mem (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))).2) x.2
      · have hres : SSGRoute.res k K (((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) :
            ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω)) = 1 := by
          rw [map_mul, map_inv, hs _ hq]
          exact inv_mul_cancel _
        have hle : (SSGRoute.res k K).ker ≤ (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) := by
          rw [IntermediateField.restrictNormalHom_ker (E := K)]
        simpa using hle (MonoidHom.mem_ker.mpr hres)
    let u : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
      ⟨((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω)⁻¹ *
        (x : Ω ≃ₐ[k] Ω), hmemU⟩
    have hxu : s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) * (Subgroup.inclusion inf_le_left u) = x := by
      apply Subtype.ext
      show ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) *
        ((Subgroup.inclusion inf_le_left u : ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) = (x : Ω ≃ₐ[k] Ω)
      rw [Subgroup.coe_inclusion]
      exact mul_inv_cancel_left _ _
    have hcrossf := (Work.AbsoluteKummer.mem_Z1_iff
      (G := ↥(SSGRoute.decomp k A)) (M := M) f.1).mp f.2 |>.1
    have hcrossg := (Work.AbsoluteKummer.mem_Z1_iff
      (G := ↥(SSGRoute.decomp k A)) (M := M) g.1).mp g.2 |>.1
    calc f.1 x = f.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) * (Subgroup.inclusion inf_le_left u)) :=
          by rw [hxu]
      _ = (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) • f.1 (Subgroup.inclusion inf_le_left u) +
            f.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) := hcrossf _ _
      _ = (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) • g.1 (Subgroup.inclusion inf_le_left u) +
            g.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) := by rw [hχu u, hval _]
      _ = g.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) * (Subgroup.inclusion inf_le_left u)) :=
          (hcrossg _ _).symm
      _ = g.1 x := by rw [hxu]
  -- the injection into a finite target
  let Φ : ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A) M) →
      ({χ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →* Multiplicative M //
        IsOpen (χ.ker : Set ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup))} ×
        ((K ≃ₐ[k] K) → M)) :=
    fun f => (⟨χfun f, hker_open f⟩, fun q => f.1 (s q))
  have hΦinj : Function.Injective Φ := by
    intro f g hfg
    refine hkey f g ?_ ?_
    · exact congrArg (fun z => (z.1 : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →*
        Multiplicative M)) hfg
    · intro q
      exact congrFun (congrArg (fun z => z.2) hfg) q
  haveI : Finite {χ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup))} := hcore
  haveI : Finite (K ≃ₐ[k] K) := inferInstance
  haveI : Finite ((K ≃ₐ[k] K) → M) := inferInstance
  exact Finite.of_injective Φ hΦinj

/-- **Finiteness of the local `H¹` at a finite place.** -/
theorem local_tate_duality_finite (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type) [AddCommGroup M]
      [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Finite (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) := by
  intro A hA M _ _ _ _ _
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M := decompDistribMulAction K M A
  haveI : Finite ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.decomp k A) M) :=
    finite_Z1_decomp p k Ω K A hA M (fun u m => by
      have hmem : ((Subgroup.inclusion inf_le_left u : ↥(SSGRoute.decomp k A)) :
          Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := u.2.2
      have hker : SSGRoute.res k K ((Subgroup.inclusion inf_le_left u :
          ↥(SSGRoute.decomp k A)) : Ω ≃ₐ[k] Ω) = 1 := by
        have hle : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) ≤ (SSGRoute.res k K).ker := by
          rw [IntermediateField.restrictNormalHom_ker (E := K)]
        exact MonoidHom.mem_ker.mp (hle hmem)
      exact (decomp_smul_eq_res K M A (Subgroup.inclusion inf_le_left u) m).trans
        (by rw [hker, one_smul]))
  have hH1 : Finite (Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) M) :=
    Finite.of_surjective (Work.AbsoluteKummer.H1π ↥(SSGRoute.decomp k A) M)
      (QuotientAddGroup.mk'_surjective _)
  exact Finite.of_injective (H1locEquivH1_decomp p k Ω K M A)
    (H1locEquivH1_decomp p k Ω K M A).injective

end

end Work.SSGRoute
