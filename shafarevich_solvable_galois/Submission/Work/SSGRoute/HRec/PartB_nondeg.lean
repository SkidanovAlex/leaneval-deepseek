/-
# Part B, node B8: nondegeneracy of the reciprocity functional from the parity law

`HRec/HRECJOINT_DESIGN.md` (node `B8`, `exists_nondeg_of_parity2`): for `p = 2`, the parity law
`Parity2` produces a functional `χ` on `LocV` which kills the reciprocity span, is `1` on the
scalar (archimedean) slot, and is *nondegenerate at every finite place* (`FinNondeg`).  This turns
`Parity2` into `ArchConsistent` **and** the finite-place nondegeneracy of `recipChi`, i.e. into the
`p = 2` half of the perfectness clause `h4` of `G1`.

Construction: for every finite place `A`, `dim H²(D_A, M^∨(1)) = 1`
(`PTCore.h2loc_mup_finrank`), so there is a functional on the `2`-cochain space of `decomp k A`
killing the coboundaries and nonzero on every nonzero locally constant class; extend it off
`lcCocycles2` by `LinearMap.exists_extend`.  Summing these over a finite support with the scalar
slot is the linear map `χ`; on a reciprocity relation vector its value is
`Σ_A [class ≠ 0] + Σ_c archPair = 0` by `Parity2`.
-/
import Mathlib
import Submission.Work.SSGRoute.HRec.HrecDefs
import Submission.Work.SSGRoute.PTCore.h2loc_mup_finrank
import Submission.Work.SSGRoute.E7Fin.cupLcCocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.SSGRoute.HRec

open NK.GlobalCFT

/-- In `ZMod p` with `p = 2` there is only one nonzero element. -/
theorem eq_one_of_ne_zero_of_eq_two (p : ℕ) [Fact p.Prime] (hp : p = 2) {x : ZMod p}
    (hx : x ≠ 0) : x = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hne : x.val ≠ 0 := fun h => hx ((ZMod.val_eq_zero x).mp h)
  have hval : x.val = 1 := by
    have := ZMod.val_lt x
    omega
  calc x = (x.val : ZMod p) := (ZMod.natCast_zmod_val x).symm
    _ = ((1 : ℕ) : ZMod p) := by rw [hval]
    _ = 1 := Nat.cast_one

/-- A globally-defined `1`-cocycle is a `1`-cocycle on every subgroup. -/
theorem isCocycleOn_of_top {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) {H : Subgroup Γ} {f : Γ → M}
    (h : SSGRoute.IsCocycleOn act ⊤ f) : SSGRoute.IsCocycleOn act H f :=
  fun g _ h' _ => h g trivial h' trivial

/-- A globally-defined locally constant function is locally constant on every subgroup. -/
theorem isLocConstOn_of_top {Γ M : Type} [Group Γ] [TopologicalSpace Γ] {H : Subgroup Γ}
    {f : Γ → M} (h : SSGRoute.IsLocConstOn ⊤ f) : SSGRoute.IsLocConstOn H f := by
  obtain ⟨U, hUo, hU⟩ := h
  exact ⟨U, hUo, fun g _ u hu _ => hU g trivial u hu trivial⟩

set_option maxHeartbeats 2000000 in
/-- **The quotient map `lcCocycles2 → H2loc`**, in the general form (mirroring
`Work.SSGRoute.PT.toClass2`): the class of a locally constant `2`-cocycle. -/
noncomputable def toH2loc (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction (K ≃ₐ[k] K) N] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    ↥(Work.SSGRoute.lcCocycles2 p k Ω K N H) →ₗ[ZMod p] (Work.SSGRoute.H2loc p k Ω K N H) :=
  Submodule.mkQ (Submodule.comap (Work.SSGRoute.lcCocycles2 p k Ω K N H).subtype
    (Work.SSGRoute.coboundaries2 p k Ω K N H))

set_option maxHeartbeats 2000000 in
/-- The computation rule of `toH2loc`. -/
theorem toH2loc_apply (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction (K ≃ₐ[k] K) N] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → N)
    (hc : c ∈ Work.SSGRoute.lcCocycles2 p k Ω K N H) :
    toH2loc p k Ω K N H ⟨c, hc⟩ =
      Submodule.mkQ (Submodule.comap (Work.SSGRoute.lcCocycles2 p k Ω K N H).subtype
        (Work.SSGRoute.coboundaries2 p k Ω K N H)) ⟨c, hc⟩ := rfl

/-- **A local functional at a finite place**: a linear functional on the `2`-cochain space of
`decomp k A` which kills the locally constant `2`-coboundaries and is nonzero on every nonzero
locally constant `2`-class. -/
theorem exists_localFunctional (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ χA : ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) →ₗ[ZMod p] ZMod p,
      (∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
        c ∈ Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
            (SSGRoute.decomp k A) → χA c = 0) ∧
      (∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
        c ∈ Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T)
            (SSGRoute.decomp k A) →
          c ∉ Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
            (SSGRoute.decomp k A) → χA c ≠ 0) := by
  classical
  have hdim : Module.finrank (ZMod p)
      (Work.SSGRoute.H2loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A)) = 1 :=
    Work.SSGRoute.PTCore.h2loc_mup_finrank p k Ω K ζ hζ hζK T hT A hA
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (R := ZMod p) hdim
  let f : ↥(Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T)
      (SSGRoute.decomp k A)) →ₗ[ZMod p] ZMod p :=
    e.symm.toLinearMap.comp (toH2loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A))
  obtain ⟨χA, hχA⟩ := LinearMap.exists_extend
    (p := Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A))
    (f := f)
  have hχA_app : ∀ (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T)
      (hc : c ∈ Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T)
        (SSGRoute.decomp k A)), χA c = f ⟨c, hc⟩ := by
    intro c hc
    have h := congrArg (fun (g : ↥(Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T)
        (SSGRoute.decomp k A)) →ₗ[ZMod p] ZMod p) => g ⟨c, hc⟩) hχA
    simpa using h
  refine ⟨χA, ?_, ?_⟩
  · intro c hc
    have hmem : c ∈ Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T)
        (SSGRoute.decomp k A) :=
      Work.SSGRoute.coboundaries2_le_lcCocycles2 p k Ω K
        (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) hc
    rw [hχA_app c hmem]
    have hq : toH2loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) ⟨c, hmem⟩ = 0 := by
      rw [toH2loc_apply p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) c hmem, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hc
    show e.symm (toH2loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) ⟨c, hmem⟩) = 0
    rw [hq, map_zero]
  · intro c hc hcnot
    rw [hχA_app c hc]
    intro hzero
    have hq : toH2loc p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) ⟨c, hc⟩ = 0 := by
      have h1 : e.symm (toH2loc p k Ω K (Work.SSGRoute.DualMod p T)
          (SSGRoute.decomp k A) ⟨c, hc⟩) = 0 := hzero
      exact e.symm.injective (by rw [h1, map_zero])
    have hmemB : (⟨c, hc⟩ : ↥(Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T)
        (SSGRoute.decomp k A))) ∈
        Submodule.comap (Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T)
          (SSGRoute.decomp k A)).subtype
          (Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
            (SSGRoute.decomp k A)) := by
      rw [toH2loc_apply p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A) c hc,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      exact hq
    rw [Submodule.mem_comap] at hmemB
    exact hcnot hmemB

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- **B8 (`exists_nondeg_of_parity2`)**. -/
theorem exists_nondeg_of_parity2 (hp : p = 2) (hpar : Parity2 p k Ω K ζ hζ hζK T hT) :
    ∃ χ : LocV p k Ω K T →ₗ[ZMod p] ZMod p,
      recipSpan p k Ω K ζ hζ hζK T hT ≤ LinearMap.ker χ ∧ χ (0, 1) = 1 ∧
        FinNondeg p k Ω K T χ := by
  classical
  -- the functional attached to every subgroup
  let ψ : (H : Subgroup (Ω ≃ₐ[k] Ω)) →
      (((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T) →ₗ[ZMod p] ZMod p) :=
    fun H => if h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A
      then Classical.choose (exists_localFunctional p k Ω K ζ hζ hζK T hT (Classical.choose h)
        (Classical.choose_spec h).1)
      else 0
  have hψ_cob : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      c ∈ Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) H → ψ H c = 0 := by
    intro H c hc
    by_cases h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A
    · have hspec := Classical.choose_spec (exists_localFunctional p k Ω K ζ hζ hζK T hT
        (Classical.choose h) (Classical.choose_spec h).1)
      dsimp only [ψ]
      rw [dif_pos h]
      rw [show H = SSGRoute.decomp k (Classical.choose h) from (Classical.choose_spec h).2] at hc
      exact hspec.1 c hc
    · dsimp only [ψ]
      rw [dif_neg h]
      rfl
  have hψ_nondeg : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) →
      ∀ c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T,
        c ∈ Work.SSGRoute.lcCocycles2 p k Ω K (Work.SSGRoute.DualMod p T) H →
        c ∉ Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) H → ψ H c ≠ 0 := by
    intro H h c hc hcn
    have hspec := Classical.choose_spec (exists_localFunctional p k Ω K ζ hζ hζK T hT
      (Classical.choose h) (Classical.choose_spec h).1)
    dsimp only [ψ]
    rw [dif_pos h]
    rw [show H = SSGRoute.decomp k (Classical.choose h) from (Classical.choose_spec h).2] at hc hcn
    exact hspec.2 c hc hcn
  -- the value of `ψ` on a cup cochain
  have hψ_cup : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
      (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a → SSGRoute.IsLocConstOn ⊤ a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      ψ (SSGRoute.decomp k A) (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b) =
        if Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
            Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
              (SSGRoute.decomp k A) then (0 : ZMod p) else 1 := by
    intro M _ _ _ _ _ a b A hA ha1 ha2 hb1 hb2
    by_cases hcob : Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
        Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) (SSGRoute.decomp k A)
    · rw [if_pos hcob]
      exact hψ_cob (SSGRoute.decomp k A) _ hcob
    · rw [if_neg hcob]
      refine eq_one_of_ne_zero_of_eq_two p hp ?_
      exact hψ_nondeg (SSGRoute.decomp k A) ⟨A, hA, rfl⟩ _
        (Work.SSGRoute.E7Fin.evCupFun_mem_lcCocycles2 p k Ω K T M (SSGRoute.decomp k A) a b
          ⟨isCocycleOn_of_top (SSGRoute.res k K) ha1, isLocConstOn_of_top ha2⟩
          ⟨isCocycleOn_of_top (SSGRoute.res k K) hb1, isLocConstOn_of_top hb2⟩)
        hcob
  -- the relation vector is killed
  have hψ_rel : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
      (S' : Finset (ValuationSubring Ω)) (C' : Finset (Ω ≃ₐ[k] Ω)),
      IsRecipDatum p k Ω K T M a b S' C' →
      (∑ A ∈ S', ψ (SSGRoute.decomp k A)
          (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b)) +
        (∑ c ∈ C', Work.SSGRoute.E7Arch.pairArchFamily p k Ω K ζ hζ hζK T hT M
          (Subgroup.zpowers c) a b) = 0 := by
    intro M _ _ _ _ _ a b S' C' hd
    have hdk := hd
    obtain ⟨ha1, ha2, hb1, hb2, hSfin, -, -, -, -, -⟩ := hd
    have hval : ∀ A ∈ S', ψ (SSGRoute.decomp k A)
        (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b) =
        (if Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
            Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
              (SSGRoute.decomp k A) then 0 else 1) :=
      fun A hA => hψ_cup M a b A (hSfin A hA) ha1 ha2 hb1 hb2
    rw [Finset.sum_congr rfl hval]
    exact hpar hp M a b S' C' hdk
  -- the assembled functional
  let χpi : LocPi p k Ω K T →ₗ[ZMod p] ZMod p := DFinsupp.lsum (S := ZMod p) ψ
  let χ : LocV p k Ω K T →ₗ[ZMod p] ZMod p :=
    χpi.coprod (LinearMap.id : ZMod p →ₗ[ZMod p] ZMod p)
  have hχ_apply : ∀ x : LocV p k Ω K T, χ x = χpi x.1 + x.2 := fun x => rfl
  have hχ_single : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω))
      (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T),
      χ (DFinsupp.single H c, 0) = ψ H c := by
    intro H c
    rw [hχ_apply]
    show χpi (DFinsupp.single H c) + (0 : ZMod p) = ψ H c
    rw [add_zero]
    exact DFinsupp.lsum_single (S := ZMod p) ψ H c
  refine ⟨χ, ?_, ?_, ?_⟩
  · -- kills the reciprocity span
    unfold recipSpan
    rw [Submodule.span_le]
    rintro v (⟨M, _, _, _, _, _, a, b, S', C', hd, rfl⟩ | ⟨H, c, hc, rfl⟩)
    · -- a relation vector
      show χ (relVec p k Ω K ζ hζ hζK T hT M a b S' C') = 0
      have h1 : (relVec p k Ω K ζ hζ hζK T hT M a b S' C').1 =
          ∑ A ∈ S', DFinsupp.single (SSGRoute.decomp k A)
            (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b) := rfl
      have h2 : (relVec p k Ω K ζ hζ hζK T hT M a b S' C').2 =
          ∑ c ∈ C', Work.SSGRoute.E7Arch.pairArchFamily p k Ω K ζ hζ hζK T hT M
            (Subgroup.zpowers c) a b := rfl
      rw [hχ_apply, h1, h2, map_sum]
      have h3 : ∀ A ∈ S', χpi (DFinsupp.single (SSGRoute.decomp k A)
          (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b)) =
          ψ (SSGRoute.decomp k A) (Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b) :=
        fun A _ => DFinsupp.lsum_single (S := ZMod p) ψ (SSGRoute.decomp k A) _
      rw [Finset.sum_congr rfl h3]
      exact hψ_rel M a b S' C' hd
    · -- a coboundary vector
      show χ (DFinsupp.single H c, 0) = 0
      rw [hχ_single]
      exact hψ_cob H c hc
  · -- value on the scalar slot
    show χ (0, 1) = 1
    rw [hχ_apply]
    show χpi 0 + (1 : ZMod p) = 1
    rw [map_zero, zero_add]
  · -- finite-place nondegeneracy
    intro A hA c hc hcnot
    rw [hχ_single]
    exact hψ_nondeg (SSGRoute.decomp k A) ⟨A, hA, rfl⟩ c hc hcnot

end Work.SSGRoute.HRec
