import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont
import Submission.Work.SSGRoute.finite_openKernel_homs_inertia_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Classical

noncomputable section

/-!
# Finiteness of the local `H¹` of the inertia subgroup (residue characteristic ≠ `p`)

This file proves `Work.SSGRoute.finite_H1loc_inertia_free`: the locally constant cohomology
`H1loc p k Ω K M I` of the inertia subgroup `I = inertiaSub k Ω A` of a finite place `A` with
residue characteristic different from `p`, with coefficients in a finite `𝔽_p[Gal(K/k)]`-module
`M`, is finite.

The mathematical content splits in two:

* **group theory** (this file): a locally constant `1`-cocycle of `I` with values in `M` is
  determined by its restriction to the kernel `I ⊓ G_K` (which acts trivially on `M` and on which
  the cocycle is therefore a group homomorphism) together with its values on a set of coset
  representatives of `I ⊓ G_K` in `I`; this reduces finiteness of the cocycles to finiteness of
  the open-kernel homomorphisms `I ⊓ G_K →* M`.  This is the exact analogue of
  `Work.SSGRoute.finite_Z1_decomp` for the decomposition group.

* **arithmetic** (`Work.SSGRoute.finite_openKernel_homs_inertia_kernel`, proved elsewhere): the
  open-kernel homomorphisms `I ⊓ G_K →* M` form a finite set.
-/

section GeneralCocycles

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- **The canonical action of a subgroup `H ≤ G_k` on a `Gal(K/k)`-module**, through the
restriction `res k K : G_k →* Gal(K/k)`.  This is `Work.SSGRoute.decompDistribMulAction`
generalised from the decomposition group to an arbitrary subgroup. -/
@[instance_reducible] def subgroupDistribMulAction (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [DistribMulAction (K ≃ₐ[k] K) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : DistribMulAction ↥H M where
  smul h m := SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m
  one_smul m := by
    show SSGRoute.res k K (((1 : ↥H) : Ω ≃ₐ[k] Ω)) • m = m
    rw [show ((1 : ↥H) : Ω ≃ₐ[k] Ω) = 1 from rfl, map_one, one_smul]
  mul_smul h1 h2 m := by
    show SSGRoute.res k K (((h1 * h2 : ↥H) : Ω ≃ₐ[k] Ω)) • m
      = SSGRoute.res k K ((h1 : Ω ≃ₐ[k] Ω)) • (SSGRoute.res k K ((h2 : Ω ≃ₐ[k] Ω)) • m)
    rw [show ((h1 * h2 : ↥H) : Ω ≃ₐ[k] Ω) = (h1 : Ω ≃ₐ[k] Ω) * (h2 : Ω ≃ₐ[k] Ω) from rfl,
      map_mul, mul_smul]
  smul_zero h := smul_zero _
  smul_add h m n := smul_add _ _ _

/-- **The reduction.**  For a subgroup `H ≤ G_k` such that `U = H ⊓ G_K` acts trivially on the
`𝔽_p`-module `M`, finiteness of the open-kernel homomorphisms `U →* Multiplicative M` forces
finiteness of the locally constant `1`-cocycles `Z¹_c(H, M)`.

The proof is that of `Work.SSGRoute.finite_Z1_decomp`, with the decomposition group replaced by an
arbitrary subgroup `H`: the restriction of a cocycle to `U` is a homomorphism (because `U` acts
trivially on `M`) and its values on a set-theoretic section `s` of the restriction
`res k K : H →* Gal(K/k)` together determine the cocycle, since `x = s (res x) · ((s (res x))⁻¹ x)`
and the action of `H` on `M` factors through `res k K`. -/
theorem finite_Z1_of_finite_homs
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    [DistribMulAction ↥H M]
    (htriv : ∀ (u : ↥(H ⊓ K.fixingSubgroup)) (m : M),
      (Subgroup.inclusion inf_le_left u : ↥H) • m = m)
    (h : Finite {χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))}) :
    Finite ↥(Work.AbsoluteKummer.Z1 ↥H M) := by
  -- the arithmetic input
  have hcore : Finite {χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))} := h
  -- the finite quotient of `H` by `H ⊓ G_K`
  have hQmem : ∀ q ∈ H.map (SSGRoute.res k K),
      ∃ σ : ↥H, SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) = q := by
    intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨σ, hσ, hσq⟩
    exact ⟨⟨σ, hσ⟩, hσq⟩
  let s : (K ≃ₐ[k] K) → ↥H := fun q =>
    if h : q ∈ H.map (SSGRoute.res k K) then Classical.choose (hQmem q h) else 1
  have hs : ∀ q (h : q ∈ H.map (SSGRoute.res k K)),
      SSGRoute.res k K (s q : Ω ≃ₐ[k] Ω) = q := by
    intro q h
    simp only [s]
    rw [dif_pos h]
    exact Classical.choose_spec (hQmem q h)
  -- `f 1 = 0` for a crossed homomorphism
  have hzero : ∀ f : ↥(Work.AbsoluteKummer.Z1 ↥H M),
      f.1 (1 : ↥H) = 0 := by
    intro f
    have h := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) f.1).mp f.2 |>.1
    have h11 : f.1 (1 : ↥H) = f.1 (1 : ↥H) + f.1 (1 : ↥H) := by
      simpa using h 1 1
    have h3 : f.1 (1 : ↥H) + f.1 (1 : ↥H) = f.1 (1 : ↥H) + 0 := by
      rw [add_zero]
      exact h11.symm
    exact add_left_cancel h3
  -- the homomorphism induced on the kernel
  let χfun : ↥(Work.AbsoluteKummer.Z1 ↥H M) →
      (↥(H ⊓ K.fixingSubgroup) →* Multiplicative M) := fun f =>
    { toFun := fun u => Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u))
      map_one' := by
        show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left
          (1 : ↥(H ⊓ K.fixingSubgroup)))) = Multiplicative.ofAdd (0 : M)
        rw [show (Subgroup.inclusion inf_le_left
          (1 : ↥(H ⊓ K.fixingSubgroup)) : ↥H) = 1 from map_one _]
        rw [hzero f]
      map_mul' := by
        intro a b
        have h := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) f.1).mp f.2 |>.1
        have h1 := h (Subgroup.inclusion inf_le_left a) (Subgroup.inclusion inf_le_left b)
        show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left (a * b))) =
          Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left a) +
            f.1 (Subgroup.inclusion inf_le_left b))
        rw [show (Subgroup.inclusion inf_le_left (a * b) : ↥H) =
            Subgroup.inclusion inf_le_left a * Subgroup.inclusion inf_le_left b from map_mul _ a b]
        rw [h1, htriv a (f.1 (Subgroup.inclusion inf_le_left b)), add_comm] }
  -- the kernel of that homomorphism is open
  have hker_open : ∀ f : ↥(Work.AbsoluteKummer.Z1 ↥H M),
      IsOpen ((χfun f).ker : Set ↥(H ⊓ K.fixingSubgroup)) := by
    intro f
    have hlc := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) f.1).mp f.2 |>.2
    obtain ⟨V, hVopen, h1V, hV⟩ := hlc (1 : ↥H)
    obtain ⟨W, hWopen, hWV⟩ := isOpen_induced_iff.mp hVopen
    have h1W : (1 : Ω ≃ₐ[k] Ω) ∈ W := by
      have h : (1 : ↥H) ∈ (Subtype.val : ↥H → Ω ≃ₐ[k] Ω) ⁻¹' W := by
        rw [hWV]
        exact h1V
      exact h
    refine Subgroup.isOpen_of_mem_nhds (χfun f).ker (g := 1) ?_
    have hWopen' : IsOpen
        ((fun u : ↥(H ⊓ K.fixingSubgroup) => (u : Ω ≃ₐ[k] Ω)) ⁻¹' W) :=
      hWopen.preimage continuous_subtype_val
    have h1W' : (1 : ↥(H ⊓ K.fixingSubgroup)) ∈
        (fun u : ↥(H ⊓ K.fixingSubgroup) => (u : Ω ≃ₐ[k] Ω)) ⁻¹' W := by
      simp only [Set.mem_preimage, Subgroup.coe_one]
      exact h1W
    refine Filter.mem_of_superset (IsOpen.mem_nhds hWopen' h1W') ?_
    intro u hu
    simp only [Set.mem_preimage] at hu
    have huin : (Subgroup.inclusion inf_le_left u : ↥H) ∈
        (Subtype.val : ↥H → Ω ≃ₐ[k] Ω) ⁻¹' W := by
      simp only [Set.mem_preimage]
      rwa [Subgroup.coe_inclusion]
    have hVmem : (Subgroup.inclusion inf_le_left u : ↥H) ∈ V := by
      rw [← hWV]
      exact huin
    show Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u)) = 1
    rw [hV _ hVmem, hzero f]
    rfl
  -- the key injectivity statement
  have hkey : ∀ f g : ↥(Work.AbsoluteKummer.Z1 ↥H M), χfun f = χfun g →
      (∀ q : K ≃ₐ[k] K, f.1 (s q) = g.1 (s q)) → f = g := by
    intro f g hχ hval
    apply Subtype.ext
    funext x
    have hχu : ∀ u : ↥(H ⊓ K.fixingSubgroup),
        f.1 (Subgroup.inclusion inf_le_left u) = g.1 (Subgroup.inclusion inf_le_left u) := by
      intro u
      have h' : Multiplicative.ofAdd (f.1 (Subgroup.inclusion inf_le_left u)) =
          Multiplicative.ofAdd (g.1 (Subgroup.inclusion inf_le_left u)) :=
        congrFun (congrArg DFunLike.coe hχ) u
      exact Multiplicative.ofAdd.injective h'
    have hq : SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) ∈ H.map (SSGRoute.res k K) :=
      ⟨(x : Ω ≃ₐ[k] Ω), x.2, rfl⟩
    have hmemU : ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥H) :
        Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω) ∈ H ⊓ K.fixingSubgroup := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact H.mul_mem (H.inv_mem (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))).2) x.2
      · have hres : SSGRoute.res k K (((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) :
            ↥H) : Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω)) = 1 := by
          rw [map_mul, map_inv, hs _ hq]
          exact inv_mul_cancel _
        have hle : (SSGRoute.res k K).ker ≤ (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) := by
          rw [IntermediateField.restrictNormalHom_ker (E := K)]
        simpa using hle (MonoidHom.mem_ker.mpr hres)
    let u : ↥(H ⊓ K.fixingSubgroup) :=
      ⟨((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥H) : Ω ≃ₐ[k] Ω)⁻¹ *
        (x : Ω ≃ₐ[k] Ω), hmemU⟩
    have hxu : s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) * (Subgroup.inclusion inf_le_left u) = x := by
      apply Subtype.ext
      show ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥H) : Ω ≃ₐ[k] Ω) *
        ((Subgroup.inclusion inf_le_left u : ↥H) : Ω ≃ₐ[k] Ω) = (x : Ω ≃ₐ[k] Ω)
      rw [Subgroup.coe_inclusion]
      exact mul_inv_cancel_left _ _
    have hcrossf := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) f.1).mp f.2 |>.1
    have hcrossg := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥H) (M := M) g.1).mp g.2 |>.1
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
  let Φ : ↥(Work.AbsoluteKummer.Z1 ↥H M) →
      ({χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
        IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))} ×
        ((K ≃ₐ[k] K) → M)) :=
    fun f => (⟨χfun f, hker_open f⟩, fun q => f.1 (s q))
  have hΦinj : Function.Injective Φ := by
    intro f g hfg
    refine hkey f g ?_ ?_
    · exact congrArg (fun z => (z.1 : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M)) hfg
    · intro q
      exact congrFun (congrArg (fun z => z.2) hfg) q
  haveI : Finite {χ : ↥(H ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(H ⊓ K.fixingSubgroup))} := hcore
  haveI : Finite (K ≃ₐ[k] K) := inferInstance
  haveI : Finite ((K ≃ₐ[k] K) → M) := inferInstance
  exact Finite.of_injective Φ hΦinj

end GeneralCocycles


/-! ## The target theorem -/

/-- **Finiteness of the local `H¹` of the inertia subgroup (residue characteristic ≠ `p`).** -/
theorem finite_H1loc_inertia_free
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Finite (Work.SSGRoute.H1loc p k Ω K M (Work.SSGRoute.inertiaSub k Ω A)) := by
  intro M _ _ _ _ _
  letI : DistribMulAction ↥(SSGRoute.inertiaSub k Ω A) M :=
    subgroupDistribMulAction k Ω K M (SSGRoute.inertiaSub k Ω A)
  have htriv : ∀ (u : ↥(SSGRoute.inertiaSub k Ω A ⊓ K.fixingSubgroup)) (m : M),
      (Subgroup.inclusion inf_le_left u : ↥(SSGRoute.inertiaSub k Ω A)) • m = m := by
    intro u m
    have hker : SSGRoute.res k K
        ((Subgroup.inclusion inf_le_left u : ↥(SSGRoute.inertiaSub k Ω A)) : Ω ≃ₐ[k] Ω) = 1 := by
      have hle : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) ≤ (SSGRoute.res k K).ker := by
        rw [IntermediateField.restrictNormalHom_ker (E := K)]
      exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_inf.mp u.2).2)
    show SSGRoute.res k K
      ((Subgroup.inclusion inf_le_left u : ↥(SSGRoute.inertiaSub k Ω A)) : Ω ≃ₐ[k] Ω) • m = m
    rw [hker, one_smul]
  haveI hZ1 : Finite ↥(Work.AbsoluteKummer.Z1 ↥(SSGRoute.inertiaSub k Ω A) M) :=
    finite_Z1_of_finite_homs p k Ω K (SSGRoute.inertiaSub k Ω A) M htriv
      (finite_openKernel_homs_inertia_kernel p k Ω K A hA h M)
  haveI hH1 : Finite (Work.AbsoluteKummer.H1 ↥(SSGRoute.inertiaSub k Ω A) M) :=
    Finite.of_surjective (Work.AbsoluteKummer.H1π ↥(SSGRoute.inertiaSub k Ω A) M)
      (QuotientAddGroup.mk'_surjective _)
  exact Finite.of_injective
    (H1locEquivH1 p k Ω K M (SSGRoute.inertiaSub k Ω A) (fun _ _ => rfl))
    (H1locEquivH1 p k Ω K M (SSGRoute.inertiaSub k Ω A) (fun _ _ => rfl)).injective

end

end Work.SSGRoute
