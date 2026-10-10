import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.e1a_can_aux
import Submission.Work.SSGRoute.PT.homCoindFree_coind_iso
import Submission.Work.SSGRoute.PT.shapiro_kernel_transfer
import Submission.Work.SSGRoute.sha2_restrict_vanish
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: the class of a locally trivial cocycle lies in the range of `δ` (arbitrary coefficient iso)

This is the "Shapiro computation" of `Work.SSGRoute.PT.e1a_sha2_mem_deltaRange`, generalised from
the `Classical.choose`-based coefficient isomorphism `e1aCoeffMap` to an *arbitrary* equivariant
additive isomorphism `Ψ : E ≃+ Hom_ℤ(E',Ωˣ)` (with the composite coefficient map
`Work.SSGRoute.PT.e1aCoeffMapOf Ψ hΨ`).  The proof is the transcription of the existing one: `Ψ` is
used only through its equivariance, so nothing in the Shapiro argument changes.

The point of the generalisation: the naturality clause of
`Work.SSGRoute.PT.e1a_ext_sha2_bridge` needs the coefficient identification to be the *canonical*
`e1aCoeffEquiv` (natural in `E`), and this lemma supplies the crux for it, `Ψ := e1aCoeffEquiv`,
`hΨ := e1aCoeffEquiv_equivariant`.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

section LocConstConv

variable {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **Locality.** A cochain which is locally constant on a subgroup in the `SSGRoute` sense
(`SSGRoute.IsLocConstOn`, i.e. constant on the right translates by the elements of an open
subgroup that lie in `H`) is locally constant on `H`, viewed as a topological space. -/
theorem isLocallyConstant_subtype_of_isLocConstOn (H : Subgroup Γ) {b : Γ → M}
    (hb : SSGRoute.IsLocConstOn H b) :
    Work.AbsoluteKummer.IsLocallyConstant (fun u : H => b (u : Γ)) := by
  obtain ⟨U, hU, hUb⟩ := hb
  intro g
  refine ⟨{x : H | (g : Γ)⁻¹ * (x : Γ) ∈ U}, hU.preimage (by continuity), ?_, ?_⟩
  · show (g : Γ)⁻¹ * (g : Γ) ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem
  · intro x hx
    show b (x : Γ) = b (g : Γ)
    have huH : (g : Γ)⁻¹ * (x : Γ) ∈ H := mul_mem (inv_mem g.2) x.2
    have key := hUb (g : Γ) g.2 ((g : Γ)⁻¹ * (x : Γ)) hx huH
    rw [← key]
    congr 1
    group

end LocConstConv

/-- The `U`-equivariance of the evaluation at `1` of a `Γ`-equivariant additive isomorphism into a
coinduced module: with `ε w = (Z w) 1` one has `ε (u • w) = u • ε w` for `u ∈ U`. -/
theorem coind_eval_smul {G : Type*} [Group G] (U : Subgroup G) {M : Type*} [AddCommGroup M]
    [DistribMulAction U M] {W : Type*} [AddCommGroup W] [DistribMulAction G W]
    (Z : W ≃+ Coind G U M) (hZ : Work.GroupCohomology.IsEquivariant G Z.toAddMonoidHom)
    (u : U) (w : W) : (Z (u • w)) 1 = u • ((Z w) 1) := by
  have hkey : Z (u • w) = u • Z w := by
    show Z ((u : G) • w) = (u : G) • Z w
    exact hZ (u : G) w
  rw [hkey]
  show (Z w) (((u : G))⁻¹ * 1) = u • ((Z w) 1)
  rw [mul_one]
  have h2 := Coind.coe_mul (Z w) ((u : G))⁻¹ u
  rw [inv_mul_cancel] at h2
  have h3 : u • ((Z w) 1) = u • (u⁻¹ • (Z w) ((u : G)⁻¹)) := by rw [h2]
  rw [h3, ← mul_smul, mul_inv_cancel, one_smul]

end

theorem e1a_sha2_mem_deltaRange_gen (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (n : ℕ)
    (pic : Rep.free SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (Fin n) ⟶
      SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (hf : Function.Surjective (Rep.Hom.hom pic))
    (S : Work.AbsoluteKummer.ShortExactSeq (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (Work.SSGRoute.PT.homCoindFree k Ω K n)
      (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic)))
    (hS : S.iota = Work.SSGRoute.precompAddHom (Rep.Hom.hom pic).toAddMonoidHom)
    (δ : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic)) →+
      Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω)
        (Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))))
    (hδ : δ.range = (Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant).ker)
    (Ψ : E ≃+ Work.SSGRoute.homCoind k Ω K (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
    (hΨ : ∀ (σ : Ω ≃ₐ[k] Ω) (e : E),
      Ψ ((SSGRoute.res k K σ) • e) = σ • Ψ e) :
    ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → E)
      (hZ : (fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2) ∈
        @Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E _ _ _
          (DistribMulAction.compHom E (SSGRoute.res k K))),
      c ∈ Work.SSGRoute.Z2loc p k Ω K E →
      ∃ z : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω)
          (Work.SSGRoute.homCoind k Ω K (CategoryTheory.Limits.kernel pic)),
        δ z = Work.SSGRoute.PT.e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
          (@Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E _ _ _
            (DistribMulAction.compHom E (SSGRoute.res k K))
            ⟨fun q : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) => c q.1 q.2, hZ⟩) := by
  classical
  -- the action of `G_k` on the coefficients
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  intro c hZ hc
  -- ### the composite coefficient map
  have hΨ' : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Ψ.toAddMonoidHom :=
    fun σ e => hΨ σ e
  let Φ : E →+ Work.SSGRoute.PT.homCoindFree k Ω K n := S.iota.comp Ψ.toAddMonoidHom
  have hΦ : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Φ :=
    S.iota_equivariant.comp hΨ
  have hΦexp : ∀ (σ : Ω ≃ₐ[k] Ω) (e : E),
      Φ ((SSGRoute.res k K σ) • e) = S.iota (σ • Ψ e) := by
    intro σ e
    exact congrArg S.iota (hΨ' σ e)
  -- ### the cocycle, transported into the free (coinduced) coefficient
  let cZ : Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E := ⟨fun q => c q.1 q.2, hZ⟩
  let zZ : Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.PT.homCoindFree k Ω K n) :=
    Work.AbsoluteKummer.mapZ2 Φ hΦ cZ
  have hzZval : ∀ (σ τ : Ω ≃ₐ[k] Ω),
      (zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.homCoindFree k Ω K n) (σ, τ) =
        Φ (c σ τ) := by
    intro σ τ
    dsimp only [zZ, cZ]
    rw [Work.AbsoluteKummer.mapZ2_apply]
  -- ### the primitive of `c` on `G_K`, and the primitive of its transport
  obtain ⟨b₀, hb₀loc, hb₀eq⟩ :=
    Work.SSGRoute.sha2_restrict_vanish p k Ω K ζ hζ hζK E c hc
  let B' : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.homCoindFree k Ω K n := fun σ => Φ (b₀ σ)
  -- ### the Shapiro isomorphism
  obtain ⟨Zc, hZc⟩ : ∃ Zc : Work.SSGRoute.PT.homCoindFree k Ω K n ≃+
      Coind (Ω ≃ₐ[k] Ω) (K.fixingSubgroup) (Fin n → Additive Ωˣ),
      Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω) Zc.toAddMonoidHom :=
    homCoindFree_coind_iso_conj k Ω K n
  let b : K.fixingSubgroup → (Fin n → Additive Ωˣ) :=
    fun u => (Zc (B' (u : Ω ≃ₐ[k] Ω))) 1
  have hUopen : IsOpen (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen K
  haveI hFI : (K.fixingSubgroup).FiniteIndex := by
    have hker : (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) = (SSGRoute.res k K).ker :=
      (IntermediateField.restrictNormalHom_ker K).symm
    have hres : (SSGRoute.res k K).ker.FiniteIndex := by
      have hsurj : Function.Surjective (SSGRoute.res k K) :=
        AlgEquiv.restrictNormalHom_surjective Ω
      haveI : Fintype (K ≃ₐ[k] K) := AlgEquiv.fintype k ↥K
      haveI : Fintype ((Ω ≃ₐ[k] Ω) ⧸ (SSGRoute.res k K).ker) :=
        Fintype.ofEquiv (K ≃ₐ[k] K)
          (QuotientGroup.quotientKerEquivOfSurjective (SSGRoute.res k K) hsurj).toEquiv.symm
      exact Subgroup.finiteIndex_of_finite_quotient
    rwa [hker]
  have hbloc : b ∈ Work.AbsoluteKummer.C1c (K.fixingSubgroup) (Fin n → Additive Ωˣ) := by
    refine (Work.AbsoluteKummer.mem_C1c_iff b).mpr ?_
    have h1 : Work.AbsoluteKummer.IsLocallyConstant
        (fun u : K.fixingSubgroup => B' (u : Ω ≃ₐ[k] Ω)) :=
      isLocallyConstant_subtype_of_isLocConstOn K.fixingSubgroup
        (isLocConstOn_push hb₀loc Φ)
    exact h1.map (fun w => (Zc w) 1)
  have hbeq : Work.GroupCohomology.d1 (K.fixingSubgroup) (Fin n → Additive Ωˣ) b =
      fun p : K.fixingSubgroup × K.fixingSubgroup =>
        (Zc ((zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) →
          Work.SSGRoute.PT.homCoindFree k Ω K n) (p.1, p.2))) 1 := by
    funext p
    obtain ⟨u, v⟩ := p
    show u • b v - b (u * v) + b u =
      (Zc ((zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) →
        Work.SSGRoute.PT.homCoindFree k Ω K n) (u, v))) 1
    rw [hzZval (u : Ω ≃ₐ[k] Ω) (v : Ω ≃ₐ[k] Ω)]
    rw [hb₀eq (u : Ω ≃ₐ[k] Ω) u.2 (v : Ω ≃ₐ[k] Ω) v.2, map_add, map_sub,
      hΦexp (u : Ω ≃ₐ[k] Ω) (b₀ (v : Ω ≃ₐ[k] Ω)),
      S.iota_equivariant (u : Ω ≃ₐ[k] Ω) (Ψ (b₀ (v : Ω ≃ₐ[k] Ω)))]
    rw [show b v = (Zc (B' (v : Ω ≃ₐ[k] Ω))) 1 from rfl,
      show b (u * v) = (Zc (B' (((u * v : K.fixingSubgroup) : Ω ≃ₐ[k] Ω)))) 1 from rfl,
      show b u = (Zc (B' (u : Ω ≃ₐ[k] Ω))) 1 from rfl]
    rw [← coind_eval_smul K.fixingSubgroup Zc hZc u (B' (v : Ω ≃ₐ[k] Ω))]
    rw [map_add, map_sub]
    rfl
  -- ### the Shapiro kernel half
  have hzB : (zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.homCoindFree k Ω K n) ∈
      Work.AbsoluteKummer.B2 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.PT.homCoindFree k Ω K n) :=
    shapiro_kernel_transfer K.fixingSubgroup hUopen Zc hZc
      (zZ : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.homCoindFree k Ω K n) zZ.2
      ⟨b, hbloc, hbeq⟩
  -- ### the cohomological chain
  have hchain : Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant
      (e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
        (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ)) =
      Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.PT.homCoindFree k Ω K n) zZ := by
    calc Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant
          (e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
            (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ))
        = Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant
            (Work.AbsoluteKummer.mapH2 Ψ.toAddMonoidHom hΨ'
              (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ)) := rfl
      _ = Work.AbsoluteKummer.mapH2 (S.iota.comp Ψ.toAddMonoidHom)
            (S.iota_equivariant.comp hΨ')
            (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ) :=
          (Work.AbsoluteKummer.mapH2_comp_H2π Ψ.toAddMonoidHom S.iota hΨ'
            S.iota_equivariant cZ).symm
      _ = Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) (Work.SSGRoute.PT.homCoindFree k Ω K n) zZ :=
          Work.AbsoluteKummer.mapH2_H2π (S.iota.comp Ψ.toAddMonoidHom)
            (S.iota_equivariant.comp hΨ') cZ
  have hmem : Work.AbsoluteKummer.mapH2 S.iota S.iota_equivariant
      (e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
        (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ)) = 0 := by
    rw [hchain, Work.AbsoluteKummer.H2π_eq_zero_iff]
    exact hzB
  have hmem' : e1aCoeffMapOf p k Ω K ζ hζ hζK T hT E Ψ hΨ
      (Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E cZ) ∈ δ.range := by
    rw [hδ, AddMonoidHom.mem_ker]
    exact hmem
  obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mpr hmem'
  exact ⟨z, hz⟩

end Work.SSGRoute.PT
