import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDArch.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! ## Non-degeneracy of the real-place pairing `Ach.archPair`

This is the archimedean half of local Tate duality: the two non-degeneracy conjuncts of
`Work.SSGRoute.local_tate_duality_archimedean`, with the pairing instantiated to the explicit
`Ach.archPair p (Ω ≃ₐ[k] Ω) E T hT.1 c` of `Defs.lean`. -/


/-
## STATUS (2026-09-26): what is proved here, and what remains

`Work.SSGRoute.local_tate_duality_archimedean` asserts the existence of a pairing on
`Z¹(⟨c⟩, E) × Z¹(⟨c⟩, DualMod p (E ⊗ T))` whose two radicals are the coboundaries.  With the
explicit pairing `Ach.archPair p (Ω ≃ₐ[k] Ω) E T hT.1 c` of `Defs.lean` the *radical* conjuncts are
what this file is about.  Proved here (sorry-free):

* `exists_isOpen_subgroup_notMem_zpowers` : for `c ≠ 1` some open subgroup of `G_k` meets `⟨c⟩`
  trivially (fixing subgroup of `k⟮α⟯` for an `α` moved by `c`).  Consequently
  `isLocConstOn_zpowers_of_meet` : on `⟨c⟩` the predicate `IsLocConstOn` holds for *every* cochain
  — this is what makes the quantified cocycles in the archimedean duality "thick" and is needed by
  any proof that uses the pairing hypothesis to separate cocycles.
* `isCoboundaryOn_zpowers_of_ne_two` : for **odd `p`** every cocycle on `⟨c⟩` is a coboundary
  (`2` is invertible in `ZMod p`), on both sides.  Hence for `p ≠ 2` both radicals are the
  coboundaries unconditionally (`archPair ≡ 0` for `p ≠ 2`, `Ach.archPair_apply_of_ne_two`), and the
  archimedean duality is trivial.

Remaining genuine content: the case `p = 2`, now reduced to two sharp sub-targets.

`T` is `⟨c⟩`-trivial — **proved above** as `smul_eq_self_of_isCyclotomicDual_two` (a primitive
second root of unity is `-1`, so `c • ζ = ζ` and `hT.2` at `n = 1` applies).  Let
`S_E : E →ₗ[ZMod p] E` be `x ↦ x + act c • x` and `S_M : M →ₗ[ZMod p] M` the same on
`M = E ⊗ T`.  The tensor action on `E ⊗ T` is diagonal — `r • (y ⊗ₜ t) = (r • y) ⊗ₜ (r • t)`
holds by `rfl` (checked) — so by the triviality above `act c • (y ⊗ₜ t) = (act c • y) ⊗ₜ t`, whence
`S_M (y ⊗ t) = S_E y ⊗ t` on tensors and by additivity on all of `M`.  In characteristic two the
cocycle condition on `⟨c⟩` reads `x = act c • x`, i.e. `x ∈ ker S_E`, and the coboundary condition
reads `x ∈ range S_E` (same on `M`).

* **Left radical.**  For `η : E →ₗ[ZMod p] ZMod p` vanishing on `range S_E`, the functional
  `ψ := Ach.tensorLift p E T (Ach.coord p T hT.1) η` on `M` vanishes on `range S_M` (compute on
  tensors with `Ach.tensorLift_tmul`) and satisfies `ψ (x ⊗ t0) = η x` (`Ach.tensorLift_tmul_t0`).
  The cochain `g` with `g 1 = 0`, `g c = ψ` is a cocycle (`Ach.isCocycleOn_zpowers_iff`, using
  `ψ ∘ S_M = 0`) and locally constant (`isLocConstOn_zpowers_of_meet` together with
  `exists_isOpen_subgroup_notMem_zpowers`, the `c = 1` case being trivial).  Hence the pairing
  hypothesis gives `η x = 0`; by the double annihilator
  (`Ach.mem_range_iff_forall_dual` with `S_E`) this is `x ∈ range S_E`.
* **Right radical.**  Put `y := g c ∈ M →ₗ[ZMod p] ZMod p`; the cocycle condition is
  `y ∈ ker (LinearMap.dualMap S_M)`, and the coboundary condition is `y ∈ range (LinearMap.dualMap
  S_M)`.  A cocycle `f : Γ → E` on `⟨c⟩` has `f c ∈ ker S_E`, and the pairing hypothesis gives
  `y (x ⊗ t0) = 0` for all such `x`; since `ker S_M` is spanned by the `x ⊗ t` with `x ∈ ker S_E`
  and `y (x ⊗ t) = (Ach.coord t) * y (x ⊗ t0)`, the functional `y` vanishes on `ker S_M`.  The
  identification `LinearMap.range_dualMap_eq_dualAnnihilator_ker` then reads
  `y ∈ (ker S_M).dualAnnihilator = range (LinearMap.dualMap S_M)`.
* **Finished.**  `definable` with `two_eq_zero_of_eq_two`, `sub_eq_add_of_eq_two`,
  `neg_eq_self_of_eq_two` (`Defs.lean`), and `IsPrimitiveRoot` supplies `ζ ^ p = 1`.
-/

namespace Work.SSGRoute

open scoped Pointwise TensorProduct

/-- `c ≠ 1` moves some `α : Ω`. -/
private lemma exists_apply_ne {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (c : Ω ≃ₐ[k] Ω) (hc : c ≠ 1) : ∃ α : Ω, c α ≠ α := by
  by_contra h
  refine hc (AlgEquiv.ext (fun α => ?_))
  by_contra hα
  exact h ⟨α, hα⟩

/-- Some open subgroup of `G_k` meets `⟨c⟩` trivially when `c ≠ 1`: the fixing subgroup of the
finite simple extension `k⟮α⟯` for an `α` moved by `c`. -/
lemma exists_isOpen_subgroup_notMem_zpowers
    (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (c : Ω ≃ₐ[k] Ω) (hc : c ≠ 1) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ c ∉ U := by
  obtain ⟨α, hα⟩ := exists_apply_ne c hc
  have hInt : IsIntegral k α := IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic α)
  haveI : FiniteDimensional k ↥(IntermediateField.adjoin k {α}) :=
    IntermediateField.adjoin.finiteDimensional hInt
  refine ⟨(IntermediateField.adjoin k {α}).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin k {α}), ?_⟩
  intro hmem
  exact hα ((IntermediateField.mem_fixingSubgroup_iff (IntermediateField.adjoin k {α}) c).mp
    hmem α (IntermediateField.mem_adjoin_simple_self k α))


/-- On `⟨c⟩`, `IsLocConstOn` follows from an open subgroup meeting `⟨c⟩` trivially. -/
lemma isLocConstOn_zpowers_of_meet {Γ M : Type} [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] (c : Γ) {f : Γ → M}
    (h : ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧
      ∀ u ∈ U, u ∈ Subgroup.zpowers c → u = 1) :
    SSGRoute.IsLocConstOn (Subgroup.zpowers c) f := by
  obtain ⟨U, hUo, hU⟩ := h
  exact ⟨U, hUo, fun g _ u hu huc => by rw [hU u hu huc, mul_one]⟩

/-- `(2 : ZMod p) ≠ 0` for odd `p`. -/
lemma two_ne_zero_of_ne_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp h' with h1 | h2
  · exact absurd h1 (Fact.out : p.Prime).ne_one
  · exact hp h2

/-- For odd `p` every cocycle on `⟨c⟩` with values in a `ZMod p`-module is a coboundary
(`2` is invertible). -/
lemma isCoboundaryOn_zpowers_of_ne_two (p : ℕ) [Fact p.Prime]
    {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (c : Γ) (hc : c ^ 2 = 1) (hp : p ≠ 2) (f : Γ → M)
    (hf : SSGRoute.IsCocycleOn act (Subgroup.zpowers c) f) :
    SSGRoute.IsCoboundaryOn act (Subgroup.zpowers c) f := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two p hp
  obtain ⟨h1, hsum⟩ := (Ach.isCocycleOn_zpowers_iff act c hc f).mp hf
  have hcx : act c • f c = - f c := eq_neg_of_add_eq_zero_right hsum
  refine (Ach.isCoboundaryOn_zpowers_iff act c hc f).mpr ⟨h1, (-(2 : ZMod p)⁻¹) • f c, ?_⟩
  show f c = act c • ((-(2 : ZMod p)⁻¹) • f c) - ((-(2 : ZMod p)⁻¹) • f c)
  have hm : act c • ((-(2 : ZMod p)⁻¹) • f c) = (2 : ZMod p)⁻¹ • f c := by
    rw [smul_comm (act c) (-(2 : ZMod p)⁻¹) (f c), hcx, smul_neg, neg_smul, neg_neg]
  have hneg : - ((-(2 : ZMod p)⁻¹) • f c) = (2 : ZMod p)⁻¹ • f c := by
    rw [← neg_smul, neg_neg]
  rw [hm]
  show f c = (2 : ZMod p)⁻¹ • f c - ((-(2 : ZMod p)⁻¹) • f c)
  rw [sub_eq_add_neg, hneg, ← add_smul]
  have h3 : (2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  rw [h3, one_smul]


/-- **`T` is trivial as a `⟨c⟩`-module when `p = 2`.**  A primitive second root of unity is
`ζ = -1`, so `c • ζ = ζ` and `hT` applied with `n = 1` gives `act c • t = t`.  (Equivalently: apply
`hT` at `n = 0` or `n = 2` when `c • ζ = 1`, which forces `T = 0`, impossible by `Ach.t0_ne_zero`.) -/
lemma smul_eq_self_of_isCyclotomicDual_two (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hp : p = 2) (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (t : T) :
    SSGRoute.res k K c • t = t := by
  have hfix : c • ζ = ζ := by
    have h2 : ζ = -1 := by
      have hpow : ζ ^ 2 = 1 := by rw [← hp]; exact hζ.pow_eq_one
      have hne : ζ ≠ 1 := hζ.ne_one (by have := (Fact.out : p.Prime).two_le; omega)
      have hmul : (ζ - 1) * (ζ + 1) = 0 := by linear_combination hpow
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact eq_neg_of_add_eq_zero_left h
    rw [h2]
    simp
  have h := hT.2 c 1 (by rw [hfix, pow_one]) t
  simpa using h


section AddSelf

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [IsGalois k K]

/-- The `𝔽_p`-linear map `S_E : x ↦ x + act c • x` on a `ZMod p`-module `M` with a compatible action
of `Gal(K/k)`.  In characteristic two this is `act c • x - x`, so that for a cocycle `f` on `⟨c⟩`
the value `f c` lies in `S.ker` and the coboundary condition reads `f c ∈ S.range`. -/
noncomputable def addSelf (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : Ω ≃ₐ[k] Ω) : M →ₗ[ZMod p] M where
  toFun x := x + SSGRoute.res k K c • x
  map_add' x y := by
    show x + y + SSGRoute.res k K c • (x + y)
      = (x + SSGRoute.res k K c • x) + (y + SSGRoute.res k K c • y)
    rw [smul_add]
    abel
  map_smul' r x := by
    show r • x + SSGRoute.res k K c • (r • x)
      = r • (x + SSGRoute.res k K c • x)
    rw [smul_add]
    congr 1
    exact smul_comm (SSGRoute.res k K c) r x

@[simp] lemma addSelf_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : Ω ≃ₐ[k] Ω) (x : M) :
    addSelf p k Ω K M c x = x + SSGRoute.res k K c • x := rfl

variable (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
  [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- The tensor action on `E ⊗ T` is diagonal: `r • (y ⊗ₜ t) = (r • y) ⊗ₜ (r • t)` (definitionally). -/
lemma smul_tmul_diagonal (c : Ω ≃ₐ[k] Ω) (y : E) (t : T) :
    SSGRoute.res k K c • (y ⊗ₜ[ZMod p] t)
      = (SSGRoute.res k K c • y) ⊗ₜ[ZMod p] (SSGRoute.res k K c • t) := rfl

/-- Hence, when `T` is `⟨c⟩`-trivial (`p = 2`), the tensor version of `addSelf` acts on tensors as
`(y ⊗ t) ↦ S_E y ⊗ t`; by additivity this determines it on all of `E ⊗ T`. -/
lemma addSelf_tmul (c : Ω ≃ₐ[k] Ω) (y : E) (t : T)
    (htriv : SSGRoute.res k K c • t = t) :
    addSelf p k Ω K (TensorProduct (ZMod p) E T) c (y ⊗ₜ[ZMod p] t)
      = addSelf p k Ω K E c y ⊗ₜ[ZMod p] t := by
  simp only [addSelf_apply, smul_tmul_diagonal, htriv, TensorProduct.add_tmul]

/-- **Left radical, linear-algebra half.**  A functional `η` on `E` killing `range (addSelf E c)`
lifts via `Ach.tensorLift` (with `Ach.coord`) to a functional killing the cocycle map
`m ↦ m + act c • m` on all of `E ⊗ T`: on tensors this is the diagonal action together with the
`⟨c⟩`-triviality of `T`, and it extends by `TensorProduct.induction_on`. -/
lemma tensorLift_addSelf_eq_zero (ζ : Ω)
    (hT : SSGRoute.IsCyclotomicDual (Γ := Ω ≃ₐ[k] Ω) (G := K ≃ₐ[k] K) p (T := T)
      (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (htriv : ∀ t : T, SSGRoute.res k K c • t = t)
    (η : E →ₗ[ZMod p] ZMod p) (hη : ∀ y : E, η (y + SSGRoute.res k K c • y) = 0)
    (m : E ⊗[ZMod p] T) :
    Ach.tensorLift p E T (Ach.coord p T hT.1) η (m + SSGRoute.res k K c • m) = 0 := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul y t =>
      rw [smul_tmul_diagonal, htriv t, ← TensorProduct.add_tmul, Ach.tensorLift_tmul, hη y,
        mul_zero]
  | add m₁ m₂ h₁ h₂ =>
      have hsplit : m₁ + m₂ + SSGRoute.res k K c • (m₁ + m₂)
          = (m₁ + SSGRoute.res k K c • m₁) + (m₂ + SSGRoute.res k K c • m₂) := by
        rw [smul_add]
        abel
      rw [hsplit]
      conv_lhs => rw [map_add]
      rw [h₁, h₂, add_zero]

end AddSelf

end Work.SSGRoute
