import Mathlib
import Submission.Work.SSGRoute.PT.natCard_addHom_of_card_prime
import Submission.Work.SSGRoute.PT.mkb_ld02_defs
import Submission.Work.SSGRoute.PT.HomFormReduction
import Submission.Work.SSGRoute.Nakayama.br_pTorsion
import Submission.Work.SSGRoute.hom_dualMod_local_units
import Submission.Work.SSGRoute.dualPairingEquiv
import Submission.Work.SSGRoute.PT.alphaTwo_trivAction_of_trivMod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `α²`-bijectivity implies the degree-`0`/`2` dimension identity at `D_A`

The last formal step of the `α²`-dévissage of Milne, *Arithmetic Duality Theorems*, Theorem I.1.8
at `r = 2`: from the bijectivity of the cupping map

`α² : H²(D_A, Hom_ℤ(N, \bar Ωˣ)) → (N^{D_A} →⁺ H²(D_A, \bar Ωˣ))`,  `N = M^∨(1) = DualMod p (M ⊗ T)`,

deduce the dimension identity of local Tate duality

`dim H²(D_A, M) = dim H⁰(D_A, M^∨(1))`.

The two ingredients (both proved in the workspace) are

* the twist cancellation `Hom_ℤ(M^∨(1), \bar Ωˣ) ≅ M`
  (`Work.SSGRoute.dualPairingEquiv`), which identifies the source of `α²` with `H²(D_A, M)`;
* the `p`-torsion of the local Brauer group, `Nat.card {x : H²(D_A,\bar Ωˣ) // p • x = 0} = p`
  (`Work.SSGRoute.Nakayama.br_pTorsion`), which makes the target of `α²` — the homomorphisms
  into the `p`-torsion part of `H²(D_A,\bar Ωˣ)` — have the same cardinality as `N^{D_A}`.

Both sides are finite `𝔽_p`-vector spaces, so the cardinality identity is a dimension identity.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

open Classical

namespace Work.SSGRoute.PT

/-- **`Nat.card V = p ^ k` for a finite `𝔽_p`-module forces `finrank V = k`.**  (`p ^ k ≥ 1`
already forces `V` to be finite, since `Nat.card` of an infinite type is `0`.) -/
theorem finrank_eq_of_natCard_eq_prime_pow {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (k : ℕ) (h : Nat.card V = p ^ k) :
    Module.finrank (ZMod p) V = k := by
  have hne : Nat.card V ≠ 0 := by
    rw [h]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  obtain ⟨-, hfin⟩ := Nat.card_ne_zero.mp hne
  haveI := hfin
  haveI : Fintype V := Fintype.ofFinite V
  have hzc : Fintype.card (ZMod p) = p := ZMod.card p
  have h1 : Fintype.card V = p ^ Module.finrank (ZMod p) V := by
    have h0 : Fintype.card V = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) V :=
      Module.card_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hzc] at h0
    exact h0
  have h2 : Fintype.card V = p ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact h
  rw [h1] at h2
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h2

theorem finrank_eq_of_alphaTwo_bijective
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    [instN : DistribMulAction ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))]
    (hpinN : instN = SSGRoute.decompDistribMulAction K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) A)
    (h : Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := ↥(SSGRoute.decomp k A))
      (N := Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (C := Additive (Units Ω)))) :
    Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
      Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) := by
  classical
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M := SSGRoute.decompDistribMulAction K M A
  haveI hTfin : Finite T := Work.SSGRoute.finite_of_finrank_eq_one T hT.1
  haveI hAfin : Finite (TensorProduct (ZMod p) M T) := Work.SSGRoute.finite_tensor M T
  haveI hNfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    Work.SSGRoute.finite_dualMod (TensorProduct (ZMod p) M T)
  have hpN : ∀ x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T), p • x = 0 := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self, zero_smul]
  have hsmulN : ∀ (g : ↥(SSGRoute.decomp k A))
      (n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      g • n = SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • n := by
    intro g n
    rw [hpinN]
    rfl
  -- ## Step 1: the twist
  obtain ⟨Φ, hΦ⟩ := Work.SSGRoute.dualPairingEquiv p k Ω K ζ hζ hζK T hT M
  let Ψ : M ≃+ Work.SSGRoute.PT.ConjHom
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω)) :=
    { toFun := fun m => ⟨Φ m⟩
      invFun := fun f => Φ.symm f.toHom
      left_inv := fun m => Φ.left_inv m
      right_inv := fun f => ConjHom.ext_apply (fun n =>
        congrArg (fun g : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T) →+
          Additive (Units Ω) => g n) (Φ.right_inv f.toHom))
      map_add' := fun a b => ConjHom.ext_apply (fun n =>
        congrArg (fun g : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T) →+
          Additive (Units Ω) => g n) (map_add Φ a b)) }
  have hsm : ∀ (g : ↥(SSGRoute.decomp k A))
      (n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      (g⁻¹) • n = (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω))⁻¹ • n := by
    intro g n
    have hX : (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) • ((g⁻¹ : ↥(SSGRoute.decomp k A)) • n) = n := by
      rw [← hsmulN g ((g⁻¹ : ↥(SSGRoute.decomp k A)) • n), ← mul_smul, mul_inv_cancel, one_smul]
    have hY : (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)) • ((SSGRoute.res k K (g : Ω ≃ₐ[k] Ω))⁻¹ • n) = n :=
      smul_inv_smul _ _
    exact (smul_left_cancel_iff (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω))).mp (hX.trans hY.symm)
  have hΨ : Work.GroupCohomology.IsEquivariant ↥(SSGRoute.decomp k A)
      (Ψ : M →+ Work.SSGRoute.PT.ConjHom
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω))) := by
    intro g m
    refine ConjHom.ext_apply (fun n => ?_)
    rw [ConjHom.smul_apply, hsm g n]
    exact hΦ (g : Ω ≃ₐ[k] Ω) m n
  have hΨ' : Work.GroupCohomology.IsEquivariant ↥(SSGRoute.decomp k A)
      ((Ψ.symm) : Work.SSGRoute.PT.ConjHom
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω)) →+ M) := by
    intro g f
    refine Ψ.injective ?_
    have h1 : Ψ (g • Ψ.symm f) = g • f := by
      show (Ψ : M →+ Work.SSGRoute.PT.ConjHom
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω))) (g • Ψ.symm f) = g • f
      rw [hΨ g (Ψ.symm f)]
      exact congrArg (fun x : Work.SSGRoute.PT.ConjHom
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω)) => g • x)
        (AddEquiv.apply_symm_apply Ψ f)
    calc Ψ (Ψ.symm (g • f)) = g • f := AddEquiv.apply_symm_apply Ψ (g • f)
      _ = Ψ (g • Ψ.symm f) := h1.symm
  have hbij : Function.Bijective (Work.AbsoluteKummer.mapH2
      (Ψ : M →+ Work.SSGRoute.PT.ConjHom
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω))) hΨ) :=
    ⟨(Function.LeftInverse.injective (fun x => congrFun (congrArg DFunLike.coe
        (mapH2_symm_comp_eq_id (G := ↥(SSGRoute.decomp k A)) (e := Ψ) hΨ hΨ')) x)),
     (Function.RightInverse.surjective (fun y => congrFun (congrArg DFunLike.coe
        (mapH2_comp_symm_eq_id (G := ↥(SSGRoute.decomp k A)) (e := Ψ) hΨ hΨ')) y))⟩
  have htwist : Nat.card (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Additive (Units Ω))))
      = Nat.card (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) M) :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  -- ## Step 2: corestriction onto the `p`-torsion homs
  have hpt : ∀ x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω))),
      ∀ n : ↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))),
      p • (Work.SSGRoute.PT.alphaTwo x n) = 0 := by
    intro x n
    have h1 : Work.SSGRoute.PT.alphaTwo x (p • n) = p • (Work.SSGRoute.PT.alphaTwo x n) :=
      map_nsmul (Work.SSGRoute.PT.alphaTwo x) p n
    rw [← h1]
    have h2 : (p • n : ↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))) = 0 := by
      refine Subtype.ext ?_
      show p • (n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) p
          (n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)), ZMod.natCast_self, zero_smul]
    rw [h2, map_zero]
  have hcore : Nat.card (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω))))
      = Nat.card (↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) →+
          ↥(AddSubgroup.torsionBy (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) p)) := by
    let F : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
          (Work.SSGRoute.PT.ConjHom (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Additive (Units Ω))) →
        (↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) →+
          ↥(AddSubgroup.torsionBy (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) p)) :=
      fun x => { toFun := fun n => ⟨Work.SSGRoute.PT.alphaTwo x n, hpt x n⟩
                 map_zero' := Subtype.ext (map_zero (Work.SSGRoute.PT.alphaTwo x))
                 map_add' := fun a b => Subtype.ext (map_add (Work.SSGRoute.PT.alphaTwo x) a b) }
    have hF : Function.Bijective F := by
      constructor
      · intro x y hxy
        have h3 : ∀ n, Work.SSGRoute.PT.alphaTwo x n = Work.SSGRoute.PT.alphaTwo y n := by
          intro n
          have h2 := congrArg (fun f : ↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) →+
              ↥(AddSubgroup.torsionBy (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
                (Additive (Units Ω))) p) =>
              (f n : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))) hxy
          exact h2
        exact h.injective (AddMonoidHom.ext h3)
      · intro f
        obtain ⟨x, hx⟩ := h.surjective ((AddSubgroup.subtype (AddSubgroup.torsionBy
          (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) p)).comp f)
        refine ⟨x, AddMonoidHom.ext (fun n => Subtype.ext ?_)⟩
        show Work.SSGRoute.PT.alphaTwo x n = (f n : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
        rw [hx]
        rfl
    exact Nat.card_congr (Equiv.ofBijective F hF)
  -- ## Step 3: counting the `p`-torsion-homs
  haveI hBfin : Finite ↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) :=
    Finite.of_injective (fun x => (x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
      Subtype.val_injective
  haveI : Module (ZMod p) ↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) :=
    AddCommGroup.zmodModule (fun x => Subtype.ext (hpN (x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
  haveI : Module (ZMod p) ↥(AddSubgroup.torsionBy
      (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) p) :=
    AddCommGroup.zmodModule (fun x => Subtype.ext x.2)
  have hDp : Nat.card ↥(AddSubgroup.torsionBy
      (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) p) = p :=
    Work.SSGRoute.Nakayama.br_pTorsion p k Ω A hA
  have hcount : Nat.card (↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) →+
        ↥(AddSubgroup.torsionBy (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω))) p))
      = Nat.card ↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) :=
    natCard_addHom_of_card_prime (p := p)
      (B := ↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
      (D := ↥(AddSubgroup.torsionBy (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (Additive (Units Ω))) p))
      hDp
  -- ## Step 4: the invariants vs `H0loc` bridge
  have hmemiff : ∀ n : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T),
      n ∈ Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        ↔ n ∈ Work.SSGRoute.H0loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A) := by
    intro n
    constructor
    · intro hn g hg
      have h1 : (⟨g, hg⟩ : ↥(SSGRoute.decomp k A)) • n = n := hn ⟨g, hg⟩
      rwa [hsmulN ⟨g, hg⟩ n] at h1
    · intro hn g
      rw [hsmulN g n]
      exact hn g g.2
  have hBH0 : Nat.card ↥(Work.GroupCohomology.invariants ↥(SSGRoute.decomp k A)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
      = Nat.card ↥(Work.SSGRoute.H0loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hmemiff)
  -- ## Step 5: the `H2loc` model bridge
  have hbridge : Nat.card (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A))
      = Nat.card (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) M) :=
    Nat.card_congr (Work.SSGRoute.PT.H2locEquivH2_decomp p k Ω K M A).toEquiv
  -- ## Step 6: assemble
  have hBpow : Nat.card ↥(Work.SSGRoute.H0loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))
      = p ^ Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) := by
    haveI : Finite ↥(Work.SSGRoute.H0loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) :=
      Finite.of_injective (fun x => (x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))
        Subtype.val_injective
    haveI : Fintype ↥(Work.SSGRoute.H0loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) :=
      Fintype.ofFinite _
    have h0 := Module.card_eq_pow_finrank (K := ZMod p)
      (V := ↥(Work.SSGRoute.H0loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)))
    rw [ZMod.card] at h0
    exact Nat.card_eq_fintype_card.trans h0
  have key : Nat.card (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
      p ^ Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) :=
    hbridge.trans (htwist.symm.trans (hcore.trans (hcount.trans (hBH0.trans hBpow))))
  exact finrank_eq_of_natCard_eq_prime_pow _ key

end Work.SSGRoute.PT
