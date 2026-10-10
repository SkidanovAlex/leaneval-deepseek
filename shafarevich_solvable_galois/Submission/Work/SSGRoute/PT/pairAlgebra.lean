import Mathlib.FieldTheory.KrullTopology
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Elementary algebra of the local pairings of `pt_selmer_relaxed`

The space of locally constant `1`-cocycles `Γ → M` on a subgroup `H ≤ Γ` is a module under
pointwise operations, and the local pairing `pair H · ·` of `pt_selmer_relaxed` is additive on it and
vanishes when either argument is a coboundary.  Consequently the pairing depends only on the
cohomology classes of its arguments: a local datum may be replaced by any global cocycle that
differs from it by a coboundary.  This is the step "the local data `α A` may be replaced by the
global witness `ε`" in the reciprocity half of the argument.
-/

namespace Work.SSGRoute

open SSGRoute
open scoped TensorProduct

section CocycleAlgebra

variable {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M]

/-- The pointwise sum of two `1`-cocycles on `H` is a `1`-cocycle on `H`. -/
theorem IsCocycleOn.add {act : Γ →* G} {H : Subgroup Γ} {f g : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H f) (hg : SSGRoute.IsCocycleOn act H g) :
    SSGRoute.IsCocycleOn act H (f + g) := by
  intro x hx y hy
  simp only [Pi.add_apply]
  rw [hf x hx y hy, hg x hx y hy, smul_add]
  abel

/-- The pointwise difference of two `1`-cocycles on `H` is a `1`-cocycle on `H`. -/
theorem IsCocycleOn.sub {act : Γ →* G} {H : Subgroup Γ} {f g : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H f) (hg : SSGRoute.IsCocycleOn act H g) :
    SSGRoute.IsCocycleOn act H (f - g) := by
  intro x hx y hy
  simp only [Pi.sub_apply]
  rw [hf x hx y hy, hg x hx y hy, smul_sub]
  abel

/-- The pointwise negation of a `1`-cocycle on `H` is a `1`-cocycle on `H`. -/
theorem IsCocycleOn.neg {act : Γ →* G} {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H f) : SSGRoute.IsCocycleOn act H (-f) := by
  intro x hx y hy
  simp only [Pi.neg_apply]
  rw [hf x hx y hy, smul_neg]
  abel

/-- The pointwise sum of two functions locally constant on `H` is locally constant on `H`. -/
theorem IsLocConstOn.add {H : Subgroup Γ} {f g : Γ → M}
    (hf : SSGRoute.IsLocConstOn H f) (hg : SSGRoute.IsLocConstOn H g) :
    SSGRoute.IsLocConstOn H (f + g) := by
  obtain ⟨U, hU, hfU⟩ := hf
  obtain ⟨V, hV, hgV⟩ := hg
  refine ⟨U ⊓ V, hU.inter hV, ?_⟩
  intro x hx u hu huH
  rw [Pi.add_apply, Pi.add_apply, hfU x hx u hu.1 huH, hgV x hx u hu.2 huH]

/-- The pointwise difference of two functions locally constant on `H` is locally constant on `H`. -/
theorem IsLocConstOn.sub {H : Subgroup Γ} {f g : Γ → M}
    (hf : SSGRoute.IsLocConstOn H f) (hg : SSGRoute.IsLocConstOn H g) :
    SSGRoute.IsLocConstOn H (f - g) := by
  obtain ⟨U, hU, hfU⟩ := hf
  obtain ⟨V, hV, hgV⟩ := hg
  refine ⟨U ⊓ V, hU.inter hV, ?_⟩
  intro x hx u hu huH
  rw [Pi.sub_apply, Pi.sub_apply, hfU x hx u hu.1 huH, hgV x hx u hu.2 huH]

/-- The pointwise negation of a function locally constant on `H` is locally constant on `H`. -/
theorem IsLocConstOn.neg {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsLocConstOn H f) : SSGRoute.IsLocConstOn H (-f) := by
  obtain ⟨U, hU, hfU⟩ := hf
  refine ⟨U, hU, ?_⟩
  intro x hx u hu huH
  rw [Pi.neg_apply, Pi.neg_apply, hfU x hx u hu huH]

end CocycleAlgebra

section Coboundary

variable {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- The negation of a coboundary on `H` is a coboundary on `H`. -/
theorem IsCoboundaryOn.neg {act : Γ →* G} {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn act H f) : SSGRoute.IsCoboundaryOn act H (-f) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨-m, fun g hg => ?_⟩
  rw [Pi.neg_apply, hm g hg, smul_neg]
  abel

/-- A function cohomologous to a coboundary is a coboundary. -/
theorem IsCoboundaryOn.of_eq {act : Γ →* G} {H : Subgroup Γ} {f g : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn act H f) (h : f = g) :
    SSGRoute.IsCoboundaryOn act H g := h ▸ hf

end Coboundary

section PairReplace

variable {p : ℕ} {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω} [Normal k K]
variable {M : Type} [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
variable {M' : Type} [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction (K ≃ₐ[k] K) M']
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M']

/-- **The first slot of the local pairing only depends on the cohomology class.**  If `a` and `a'`
are locally constant `1`-cocycles on `H` whose difference is a coboundary, then `pair H a b =
pair H a' b` (additivity plus vanishing on coboundaries). -/
theorem pair_eq_of_sub_coboundary
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → M') → ZMod p)
    (hadd : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (a a' : (Ω ≃ₐ[k] Ω) → M)
      (b : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      pair H (a + a') b = pair H a b + pair H a' b)
    (hz : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
      pair H a b = 0)
    {H : Subgroup (Ω ≃ₐ[k] Ω)} {a a' : (Ω ≃ₐ[k] Ω) → M} {b : (Ω ≃ₐ[k] Ω) → M'}
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (ha' : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a')
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b)
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H (a - a')) :
    pair H a b = pair H a' b := by
  have hsub : SSGRoute.IsCocycleOn (SSGRoute.res k K) H (a - a') ∧
      SSGRoute.IsLocConstOn H (a - a') :=
    ⟨IsCocycleOn.sub ha.1 ha'.1, IsLocConstOn.sub ha.2 ha'.2⟩
  have hdecomp : a = a' + (a - a') := by
    ext σ
    simp
  rw [hdecomp, hadd H a' (a - a') b ha' hsub hb,
    hz H (a - a') b hsub hb (Or.inl hcob), add_zero]

/-- **The second slot of the local pairing only depends on the cohomology class.** -/
theorem pair_eq_of_sub_coboundary_right
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → M') → ZMod p)
    (hadd : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
      (b b' : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
      pair H a (b + b') = pair H a b + pair H a b')
    (hz : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
      pair H a b = 0)
    {H : Subgroup (Ω ≃ₐ[k] Ω)} {a : (Ω ≃ₐ[k] Ω) → M} {b b' : (Ω ≃ₐ[k] Ω) → M'}
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b')
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H (b - b')) :
    pair H a b = pair H a b' := by
  have hsub : SSGRoute.IsCocycleOn (SSGRoute.res k K) H (b - b') ∧
      SSGRoute.IsLocConstOn H (b - b') :=
    ⟨IsCocycleOn.sub hb.1 hb'.1, IsLocConstOn.sub hb.2 hb'.2⟩
  have hdecomp : b = b' + (b - b') := by
    ext σ
    simp
  rw [hdecomp, hadd H a b' (b - b') ha hb' hsub,
    hz H a (b - b') ha hsub (Or.inr hcob), add_zero]

end PairReplace

end Work.SSGRoute
