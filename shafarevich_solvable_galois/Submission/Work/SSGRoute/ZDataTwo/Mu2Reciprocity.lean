import Submission.Work.SSGRoute.ZDataTwo.Mu2PairForm
import Submission.Work.SSGRoute.ZDataTwo.Mu2FiniteForm
import Submission.Work.ZDataTwo.localNormSubgroup_eq_normGroup_quadLevel
import Submission.Work.SSGRoute.ZDataTwo.exists_kummerChar_of_additive_locConst_base
import Submission.Work.HilbertSymbolGeneral.hilbertReciprocityTwo
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The reciprocity clause of the `μ₂` local Tate system with archimedean terms

This file collects the transport lemmas by which the two branches of `mu2Form` are evaluated on
Kummer classes, together with the two arithmetic statements (the behaviour at the finite places
outside `S'` and the archimedean count) to which the reciprocity clause reduces.
-/

namespace Work.SSGRoute.ZDataTwo

open _root_.SSGRoute
open scoped IntermediateField Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod 2)] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) (ZMod 2)]

/-! ## Transport lemmas -/

/-- Transport of a class along an equality of subgroups. -/
lemma eqRec_toClass {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H = H') (f : (Ω ≃ₐ[k] Ω) → ZMod 2) :
    h ▸ (toClass 2 k Ω K (ZMod 2) H f) = toClass 2 k Ω K (ZMod 2) H' f := by
  cases h; rfl

/-- Transport of a Kummer class along an equality of subgroups. -/
lemma eqRec_kummerClass (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (h : H = H') (α : kˣ) :
    h ▸ (kummerClass k Ω K ζ hζ H α) = kummerClass k Ω K ζ hζ H' α := by
  cases h; rfl

/-- Transport of an application of a transported linear map. -/
lemma eqRec_symm_apply {H₁ H₂ : Subgroup (Ω ≃ₐ[k] Ω)} (h : H₁ = H₂)
    (F : H1loc 2 k Ω K (ZMod 2) H₂ →ₗ[ZMod 2]
      (H1loc 2 k Ω K (ZMod 2) H₂ →ₗ[ZMod 2] ZMod 2))
    (x y : H1loc 2 k Ω K (ZMod 2) H₁) :
    (h.symm ▸ F) x y = F (h ▸ x) (h ▸ y) := by
  cases h; rfl

/-- The prime below a place depends only on the place (proof irrelevance). -/
lemma primeBelow_eq_of_eq {A A' : ValuationSubring Ω} (hA : IsFinPlace k A)
    (hA' : IsFinPlace k A') (h : A = A') :
    primeBelow k Ω A hA = primeBelow k Ω A' hA' := by
  subst h
  unfold primeBelow
  exact congrArg Exists.choose (Subsingleton.elim _ _)

/-! ## The Kummer character at involutions -/

/-- The Kummer character of `α` vanishes at the identity. -/
lemma kummerChar_apply_one (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (α : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α 1 = 0 := by
  have h : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α 1 =
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α 1 +
        Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α 1 := by
    have h0 := Work.SSGRoute.kummerChar_mul_apply (K := k) (Ω := Ω) ζ hζ α 1 1
    rwa [mul_one] at h0
  have hg : Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α 1 + 0 =
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α 1 +
        Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α 1 := by
    rw [add_zero]; exact h
  exact (add_left_cancel hg).symm

/-- The Kummer character of `α` is the same at two involutions generating the same subgroup. -/
lemma kummerChar_eq_of_zpowers_eq (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (α : kˣ)
    {c d : Ω ≃ₐ[k] Ω} (hc : c ^ 2 = 1) (hd : d ^ 2 = 1)
    (h : Subgroup.zpowers d = Subgroup.zpowers c) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α d =
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α c := by
  rcases mem_zpowers_eq_one_or k Ω c hc (show d ∈ Subgroup.zpowers c from h ▸ Subgroup.mem_zpowers d)
    with h1 | h1
  · rw [h1]
    have hc1 : c = 1 := by
      have hbot : (Subgroup.zpowers c : Subgroup (Ω ≃ₐ[k] Ω)) = ⊥ := by
        rw [← h, h1]; exact Subgroup.zpowers_one_eq_bot
      exact Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers c)
    rw [hc1, kummerChar_apply_one]
  · rw [h1]

/-- Two involutions generating the same subgroup coincide. -/
lemma eq_of_zpowers_eq {c d : Ω ≃ₐ[k] Ω} (hc : c ^ 2 = 1) (hd : d ^ 2 = 1)
    (h : Subgroup.zpowers d = Subgroup.zpowers c) : d = c := by
  rcases mem_zpowers_eq_one_or k Ω c hc (show d ∈ Subgroup.zpowers c from h ▸ Subgroup.mem_zpowers d)
    with h1 | h1
  · rw [h1]
    have hc1 : c = 1 := by
      have hbot : (Subgroup.zpowers c : Subgroup (Ω ≃ₐ[k] Ω)) = ⊥ := by
        rw [← h, h1]; exact Subgroup.zpowers_one_eq_bot
      exact Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers c)
    rw [hc1]
  · exact h1


/-! ## Evaluating the two branches on Kummer classes -/

/-- **The value of `mu2Form` at a decomposition group, on Kummer classes.** -/
lemma mu2Form_decomp_kummerClass (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (A : ValuationSubring Ω)
    (hA : IsFinPlace k A) (α β : kˣ) :
    mu2Form k Ω K ζ hζ (decomp k A) (kummerClass k Ω K ζ hζ (decomp k A) α)
        (kummerClass k Ω K ζ hζ (decomp k A) β)
      = finPair k (primeBelow k Ω A hA) α β := by
  have hneg : ¬ ∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ decomp k A = Subgroup.zpowers c := by
    rintro ⟨c, hc, hcA⟩
    exact Work.SSGRoute.E7Arch.localGroupDisjoint k Ω A hA c hc hcA
  have hh : ∃ A' : ValuationSubring Ω, IsFinPlace k A' ∧ decomp k A = decomp k A' :=
    ⟨A, hA, rfl⟩
  rw [mu2Form_eq_fin k Ω K ζ hζ hneg hh]
  obtain ⟨h1, h2⟩ := hh.choose_spec
  calc (h2.symm ▸ finForm k Ω K ζ hζ hh.choose h1)
        (kummerClass k Ω K ζ hζ (decomp k A) α)
        (kummerClass k Ω K ζ hζ (decomp k A) β)
      = finForm k Ω K ζ hζ hh.choose h1
          (h2 ▸ kummerClass k Ω K ζ hζ (decomp k A) α)
          (h2 ▸ kummerClass k Ω K ζ hζ (decomp k A) β) :=
        eqRec_symm_apply k Ω K (h := h2) (finForm k Ω K ζ hζ hh.choose h1)
          (kummerClass k Ω K ζ hζ (decomp k A) α) (kummerClass k Ω K ζ hζ (decomp k A) β)
    _ = finForm k Ω K ζ hζ hh.choose h1
          (kummerClass k Ω K ζ hζ (decomp k hh.choose) α)
          (kummerClass k Ω K ζ hζ (decomp k hh.choose) β) := by
        rw [eqRec_kummerClass, eqRec_kummerClass]
    _ = finPair k (primeBelow k Ω hh.choose h1) α β :=
        finForm_kummerClass k Ω K ζ hζ hh.choose h1 α β
    _ = finPair k (primeBelow k Ω A hA) α β :=
        congrArg (fun Q => finPair k Q α β)
          (primeBelow_eq_of_eq (k := k) (Ω := Ω) hA h1
            (place_eq_of_decomp_eq (k := k) (Ω := Ω) hA h1 h2)).symm

/-- **The value of `mu2Form` at an involution group, on Kummer classes.** -/
lemma mu2Form_zpowers_kummerClass (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (c : Ω ≃ₐ[k] Ω)
    (hc : c ^ 2 = 1) (α β : kˣ) :
    mu2Form k Ω K ζ hζ (Subgroup.zpowers c)
        (kummerClass k Ω K ζ hζ (Subgroup.zpowers c) α)
        (kummerClass k Ω K ζ hζ (Subgroup.zpowers c) β)
      = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α c *
        Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ β c := by
  have h : ∃ d : Ω ≃ₐ[k] Ω, d ^ 2 = 1 ∧ Subgroup.zpowers c = Subgroup.zpowers d :=
    ⟨c, hc, rfl⟩
  rw [mu2Form_eq_arch k Ω K ζ hζ h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  calc (h2.symm ▸ archForm k Ω K h.choose)
        (kummerClass k Ω K ζ hζ (Subgroup.zpowers c) α)
        (kummerClass k Ω K ζ hζ (Subgroup.zpowers c) β)
      = archForm k Ω K h.choose
          (h2 ▸ kummerClass k Ω K ζ hζ (Subgroup.zpowers c) α)
          (h2 ▸ kummerClass k Ω K ζ hζ (Subgroup.zpowers c) β) :=
        eqRec_symm_apply k Ω K (h := h2) (archForm k Ω K h.choose)
          (kummerClass k Ω K ζ hζ (Subgroup.zpowers c) α)
          (kummerClass k Ω K ζ hζ (Subgroup.zpowers c) β)
    _ = archForm k Ω K h.choose
          (toClass 2 k Ω K (ZMod 2) (Subgroup.zpowers h.choose)
            (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α))
          (toClass 2 k Ω K (ZMod 2) (Subgroup.zpowers h.choose)
            (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ β)) := by
        rw [eqRec_kummerClass, eqRec_kummerClass, kummerClass, kummerClass]
    _ = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α h.choose *
          Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ β h.choose :=
        archForm_toClass k Ω K
          (kummerChar_mem_lcCocycles k Ω K ζ hζ (Subgroup.zpowers h.choose) α)
          (kummerChar_mem_lcCocycles k Ω K ζ hζ (Subgroup.zpowers h.choose) β)
    _ = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α c *
          Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ β c := by
        rw [(kummerChar_eq_of_zpowers_eq (k := k) (Ω := Ω) ζ hζ α h1 hc h2).symm,
            (kummerChar_eq_of_zpowers_eq (k := k) (Ω := Ω) ζ hζ β h1 hc h2).symm]


/-! ## The finite pairing as the local-norm indicator -/

/-- **The finite pairing detects the local-norm condition.**  For a quadratic extension `L = k(√α)`
of `k`, the finite pairing of `α` and `β` at the prime below `A` is trivial exactly when `β` is a
local norm at that prime from `L`. -/
theorem finPair_eq_zero_iff_isLocalNorm (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : IsFinPlace k A) (α β : kˣ)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (h2 : Nat.card (L ≃ₐ[k] L) = 2)
    (hy : ∃ y : L, y * y = algebraMap k L (α : k) ∧ y ∉ Set.range (algebraMap k L)) :
    finPair k (primeBelow k Ω A hA) α β = 0 ↔
      NK.NUV2.LC.IsLocalNorm k L β (NK.GlobalCFT.Place.ofFinite (primeBelow k Ω A hA)) := by
  obtain ⟨y, hy_sq, hy_ne⟩ := hy
  obtain ⟨y₀, hy₀, hN⟩ := Work.ZDataTwo.localNormSubgroup_eq_normGroup_quadLevel
    (Q := primeBelow k Ω A hA) α L h2 ⟨y, hy_sq, hy_ne⟩
  rw [finPair, toAdd_eq_zero_iff, Work.HilbertSymbolGeneral.hilbertSymbol_comm,
    NK.NUV2.LC.hilbertSymbol_eq_one_iff_normGroup]
  constructor
  · rintro ⟨y', hy', hmem⟩
    rw [Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup, hN]
    exact (Work.HilbertSymbolGeneral.mem_normGroup_quadLevel_iff y₀ _
        (Units.ne_zero (localImage k (primeBelow k Ω A hA) α)) hy₀
        (localImage k (primeBelow k Ω A hA) β)).mpr
      ((Work.HilbertSymbolGeneral.mem_normGroup_quadLevel_iff y' _
        (Units.ne_zero (localImage k (primeBelow k Ω A hA) α)) hy'
        (localImage k (primeBelow k Ω A hA) β)).mp hmem)
  · intro h
    rw [Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup, hN] at h
    exact ⟨y₀, hy₀, h⟩


/-! ## Assembling the two sums -/

/-- The class of the Kummer character is the Kummer class (definitionally). -/
lemma toClass_kummerChar (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (α : kˣ)
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    toClass 2 k Ω K (ZMod 2) H (Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α) =
      kummerClass k Ω K ζ hζ H α := rfl

/-- A cochain agreeing with a Kummer character has the same class. -/
lemma toClass_eq_kummerClass_of_agree (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    {a : (Ω ≃ₐ[k] Ω) → ZMod 2} {α : kˣ}
    (h : ∀ σ : Ω ≃ₐ[k] Ω, a σ = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α σ)
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    toClass 2 k Ω K (ZMod 2) H a = kummerClass k Ω K ζ hζ H α := by
  rw [show a = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α from funext h]
  rfl

/-- The zero cochain has zero class. -/
lemma toClass_zero (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    toClass 2 k Ω K (ZMod 2) H (0 : (Ω ≃ₐ[k] Ω) → ZMod 2) = 0 := by
  rw [toClass_eq_zero_iff 2 k Ω K (ZMod 2) H (Submodule.zero_mem _), mem_coboundaries]
  exact (isCoboundaryOn_iff_eq_zero k Ω K H 0).mpr (fun g _ => rfl)

/-- The Kummer character of a square vanishes. -/
lemma kummerChar_eq_zero_of_sq (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (d : kˣ) :
    Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ (d * d) = 0 := by
  rw [Work.SSGRoute.kummerChar_mul (K := k) (Ω := Ω) ζ hζ d d]
  exact add_self_eq_zero_zmodTwo _

lemma mu2Form_zero_left (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (H : Subgroup (Ω ≃ₐ[k] Ω))
    (y : H1loc 2 k Ω K (ZMod 2) H) : mu2Form k Ω K ζ hζ H 0 y = 0 := by
  rw [map_zero, LinearMap.zero_apply]

lemma mu2Form_zero_right (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (H : Subgroup (Ω ≃ₐ[k] Ω))
    (x : H1loc 2 k Ω K (ZMod 2) H) : mu2Form k Ω K ζ hζ H x 0 = 0 := map_zero _

/-- **The finite part of the reciprocity sum**, on Kummer classes. -/
lemma mu2Form_sum_fin (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (α β : kˣ)
    (S' : Finset (ValuationSubring Ω)) (hS'fin : ∀ A ∈ S', IsFinPlace k A) :
    (∑ A ∈ S', mu2Form k Ω K ζ hζ (decomp k A)
        (kummerClass k Ω K ζ hζ (decomp k A) α) (kummerClass k Ω K ζ hζ (decomp k A) β))
      = ∑ A ∈ S'.attach, finPair k (primeBelow k Ω A.1 (hS'fin A.1 A.2)) α β := by
  rw [← Finset.sum_attach (s := S') (f := fun A => mu2Form k Ω K ζ hζ (decomp k A)
    (kummerClass k Ω K ζ hζ (decomp k A) α) (kummerClass k Ω K ζ hζ (decomp k A) β))]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  exact mu2Form_decomp_kummerClass k Ω K ζ hζ A.1 (hS'fin A.1 A.2) α β

/-- **The archimedean part of the reciprocity sum**, on Kummer classes. -/
lemma mu2Form_sum_arch (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (α β : kˣ)
    (C' : Finset (Ω ≃ₐ[k] Ω)) (hC'inv : ∀ c ∈ C', c ^ 2 = 1) :
    (∑ c ∈ C', mu2Form k Ω K ζ hζ (Subgroup.zpowers c)
        (kummerClass k Ω K ζ hζ (Subgroup.zpowers c) α)
        (kummerClass k Ω K ζ hζ (Subgroup.zpowers c) β))
      = ∑ c ∈ C', Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α c *
          Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ β c := by
  refine Finset.sum_congr rfl ?_
  intro c hc
  exact mu2Form_zpowers_kummerClass k Ω K ζ hζ c (hC'inv c hc) α β

end Work.SSGRoute.ZDataTwo
