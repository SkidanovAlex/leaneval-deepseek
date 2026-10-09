import Mathlib
import Submission.Work.SSGRoute.HSTwoRow.extFunAux
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The normal-form construction for the transgression `H²_loc(D,M) → H¹_loc(I,M)_σ`

Setting: `k` a number field, `Ω` an algebraic closure, `K/k` a finite Galois subextension,
`M` an `𝔽_p`-module with a `Gal(K/k)`-action, `A` a place of `Ω`, `D = decomp k A` its
decomposition group, `I ≤ D` a closed subgroup normalised by `D`, `σ ∈ D`,
`C = closure (zpowers σ)`, with `D ≤ I ⊔ C` and `I ⊓ C = ⊥` (so `D = I ⋊ C`).

`DCtx` collects the hypotheses.  For a locally constant `2`-cocycle `c` on `D`, a locally constant
`1`-cochain `β` on `I` with `d¹β = c` on `I × I`, and a locally constant `1`-cochain `χ` on `C`
with `d¹χ = c₀` on `C × C` (`c₀` below), the *normal form* is

`nform S c β χ = c₀ - d¹ (corrE S c₀) - d¹ (chiExt S χ)`,  `c₀ = c - d¹ (betaExt S β)`,

where

* `betaG S β = β ∘ ip` extends `β` to `D` (with `0` outside `D`),
* `corrE S c₀ g = - c₀ (projG g) (coorG g)` with `coorG g = (projG g)⁻¹ * g`,
* `chiExt S χ = extFun χ = χ ∘ projG` (with `0` outside `D`).

The slice `slice S F = fun n => F n σ` is the representative of the transgression class.
-/

open scoped Pointwise
open Classical

namespace Work.PTCore

open Work.SSGRoute
open Work.SSGRoute.HSTwoRow

noncomputable section

/-- The hypotheses of the transgression construction. -/
structure DCtx (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] where
  /-- the place -/
  A : ValuationSubring Ω
  /-- the normal subgroup -/
  I : Subgroup (Ω ≃ₐ[k] Ω)
  /-- the procyclic generator -/
  σ : Ω ≃ₐ[k] Ω
  hI : I ≤ SSGRoute.decomp k A
  hIclosed : IsClosed (I : Set (Ω ≃ₐ[k] Ω))
  hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I
  hσ : σ ∈ SSGRoute.decomp k A
  hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ)
  hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The `C`-coordinate `proj g` of `g ∈ D`, as an element of `G_k` (`1` outside `D`). -/
def projG (S : DCtx k Ω) (g : Ω ≃ₐ[k] Ω) : Ω ≃ₐ[k] Ω :=
  if h : g ∈ SSGRoute.decomp k S.A then
    ((HS.proj S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup ⟨g, h⟩ :
      ↥(Subgroup.topologicalClosure (Subgroup.zpowers S.σ))) : Ω ≃ₐ[k] Ω)
  else 1

@[simp] theorem projG_of_mem (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω}
    (hg : g ∈ SSGRoute.decomp k S.A) :
    projG S g = ((HS.proj S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup
      ⟨g, hg⟩ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers S.σ))) : Ω ≃ₐ[k] Ω) :=
  dif_pos hg

/-- The `I`-coordinate `ip g` of `g ∈ D`, as an element of `G_k` (`1` outside `D`). -/
def ipG (S : DCtx k Ω) (g : Ω ≃ₐ[k] Ω) : Ω ≃ₐ[k] Ω :=
  if h : g ∈ SSGRoute.decomp k S.A then
    ((HS.ip S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup ⟨g, h⟩ :
      ↥S.I) : Ω ≃ₐ[k] Ω)
  else 1

@[simp] theorem ipG_of_mem (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω}
    (hg : g ∈ SSGRoute.decomp k S.A) :
    ipG S g = ((HS.ip S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup
      ⟨g, hg⟩ : ↥S.I) : Ω ≃ₐ[k] Ω) := dif_pos hg

/-- The "coordinate" `coorG g = (projG g)⁻¹ * g` of `g ∈ D`; it lies in `I`. -/
def coorG (S : DCtx k Ω) (g : Ω ≃ₐ[k] Ω) : Ω ≃ₐ[k] Ω :=
  if h : g ∈ SSGRoute.decomp k S.A then (projG S g)⁻¹ * g else 1

@[simp] theorem coorG_of_mem (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω}
    (hg : g ∈ SSGRoute.decomp k S.A) : coorG S g = (projG S g)⁻¹ * g := dif_pos hg

theorem ipG_mem_I (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) :
    ipG S g ∈ S.I := by
  rw [ipG_of_mem S hg]
  exact (HS.ip S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup ⟨g, hg⟩).2

theorem projG_mem_C (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) :
    projG S g ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ) := by
  rw [projG_of_mem S hg]
  exact (HS.proj S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup ⟨g, hg⟩).2

theorem projG_mem_D (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) :
    projG S g ∈ SSGRoute.decomp k S.A := (HS.CC_le_DD S.A S.σ S.hσ) (projG_mem_C S hg)

theorem ipG_mul_projG (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) :
    ipG S g * projG S g = g := by
  rw [ipG_of_mem S hg, projG_of_mem S hg]
  simpa only [Subtype.coe_mk] using
    HS.ip_mul_proj S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup ⟨g, hg⟩

theorem projG_mul (S : DCtx k Ω) {a b : Ω ≃ₐ[k] Ω}
    (ha : a ∈ SSGRoute.decomp k S.A) (hb : b ∈ SSGRoute.decomp k S.A) :
    projG S (a * b) = projG S a * projG S b := by
  rw [projG_of_mem S (mul_mem ha hb), projG_of_mem S ha, projG_of_mem S hb]
  exact congrArg _ (HS.proj_mul S.A S.I S.σ S.hI S.hnorm (HS.CC_le_DD S.A S.σ S.hσ) S.hsup
    S.hinf ⟨a, ha⟩ ⟨b, hb⟩)

theorem ipG_projG_of_mem_I (S : DCtx k Ω) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ S.I) :
    ipG S n = n ∧ projG S n = 1 := by
  have hnD : n ∈ SSGRoute.decomp k S.A := S.hI hn
  have h1 : ipG S n * projG S n = n * 1 := by rw [ipG_mul_projG S hnD, mul_one]
  exact HS.factor_unique (i₁ := ipG S n) (i₂ := n) (γ₁ := projG S n) (γ₂ := 1)
    S.A S.I S.σ S.hinf (ipG_mem_I S hnD) hn (projG_mem_C S hnD)
    (Subgroup.one_mem _) h1

theorem projG_eq_one_of_mem_I (S : DCtx k Ω) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ S.I) :
    projG S n = 1 := (ipG_projG_of_mem_I S hn).2

theorem ipG_eq_self_of_mem_I (S : DCtx k Ω) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ S.I) :
    ipG S n = n := (ipG_projG_of_mem_I S hn).1

theorem projG_eq_self_of_mem_C (S : DCtx k Ω) {γ : Ω ≃ₐ[k] Ω}
    (hγ : γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ)) :
    projG S γ = γ := by
  have hγD : γ ∈ SSGRoute.decomp k S.A := (HS.CC_le_DD S.A S.σ S.hσ) hγ
  have h1 : ipG S γ * projG S γ = 1 * γ := by rw [ipG_mul_projG S hγD, one_mul]
  exact (HS.factor_unique (i₁ := ipG S γ) (i₂ := 1) (γ₁ := projG S γ) (γ₂ := γ)
    S.A S.I S.σ S.hinf (ipG_mem_I S hγD) (S.I.one_mem) (projG_mem_C S hγD) hγ h1).2

theorem ipG_eq_one_of_mem_C (S : DCtx k Ω) {γ : Ω ≃ₐ[k] Ω}
    (hγ : γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ)) :
    ipG S γ = 1 := by
  have hγD : γ ∈ SSGRoute.decomp k S.A := (HS.CC_le_DD S.A S.σ S.hσ) hγ
  have h1 : ipG S γ * projG S γ = 1 * γ := by rw [ipG_mul_projG S hγD, one_mul]
  exact (HS.factor_unique (i₁ := ipG S γ) (i₂ := 1) (γ₁ := projG S γ) (γ₂ := γ)
    S.A S.I S.σ S.hinf (ipG_mem_I S hγD) (S.I.one_mem) (projG_mem_C S hγD) hγ h1).1

theorem coorG_eq_conj (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) :
    coorG S g = (projG S g)⁻¹ * ipG S g * projG S g := by
  have key : (projG S g)⁻¹ * g = (projG S g)⁻¹ * (ipG S g * projG S g) := by
    rw [ipG_mul_projG S hg]
  rw [coorG_of_mem S hg, key]
  group

theorem coorG_mem_I (S : DCtx k Ω) {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) :
    coorG S g ∈ S.I := by
  rw [coorG_eq_conj S hg]
  exact S.hnorm (projG S g)⁻¹ (Subgroup.inv_mem _ (projG_mem_D S hg)) (ipG S g)
    (ipG_mem_I S hg)

theorem coorG_mul_of_mem_I (S : DCtx k Ω) {g n : Ω ≃ₐ[k] Ω}
    (hg : g ∈ SSGRoute.decomp k S.A) (hn : n ∈ S.I) :
    coorG S (g * n) = coorG S g * n := by
  have hnD : n ∈ SSGRoute.decomp k S.A := S.hI hn
  rw [coorG_of_mem S (mul_mem hg hnD), coorG_of_mem S hg,
    projG_mul S hg hnD, projG_eq_one_of_mem_I S hn]
  group

theorem coorG_eq_self_of_mem_I (S : DCtx k Ω) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ S.I) :
    coorG S n = n := by
  have hnD : n ∈ SSGRoute.decomp k S.A := S.hI hn
  rw [coorG_of_mem S hnD, projG_eq_one_of_mem_I S hn, inv_one, one_mul]

theorem coorG_eq_one_of_mem_C (S : DCtx k Ω) {γ : Ω ≃ₐ[k] Ω}
    (hγ : γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ)) : coorG S γ = 1 := by
  have hγD : γ ∈ SSGRoute.decomp k S.A := (HS.CC_le_DD S.A S.σ S.hσ) hγ
  rw [coorG_of_mem S hγD, projG_eq_self_of_mem_C S hγ, inv_mul_cancel]

/-- The extension `β̃ = β ∘ ip` of a cochain on `I` to the decomposition group (`0` outside). -/
def betaG (S : DCtx k Ω) {M : Type} [Zero M] (β : (Ω ≃ₐ[k] Ω) → M) : (Ω ≃ₐ[k] Ω) → M :=
  fun g => if h : g ∈ SSGRoute.decomp k S.A then β (ipG S g) else 0

@[simp] theorem betaG_of_mem (S : DCtx k Ω) {M : Type} [Zero M] (β : (Ω ≃ₐ[k] Ω) → M)
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) : betaG S β g = β (ipG S g) := dif_pos hg

theorem betaG_eq_of_mem_I (S : DCtx k Ω) {M : Type} [Zero M] (β : (Ω ≃ₐ[k] Ω) → M)
    {n : Ω ≃ₐ[k] Ω} (hn : n ∈ S.I) : betaG S β n = β n := by
  rw [betaG_of_mem S β (S.hI hn), ipG_eq_self_of_mem_I S hn]

/-- The extension `χ ∘ proj` of a cochain on `C` to the decomposition group. -/
def chiExt (S : DCtx k Ω) {M : Type} [Zero M] (χ : (Ω ≃ₐ[k] Ω) → M) : (Ω ≃ₐ[k] Ω) → M :=
  extFun S.A S.I S.σ S.hI S.hnorm S.hσ S.hsup χ

theorem chiExt_of_mem (S : DCtx k Ω) {M : Type} [Zero M] (χ : (Ω ≃ₐ[k] Ω) → M)
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k S.A) : chiExt S χ g = χ (projG S g) := by
  show extFun S.A S.I S.σ S.hI S.hnorm S.hσ S.hsup χ g = χ (projG S g)
  rw [extFun_apply_of_mem S.A S.I S.σ S.hI S.hnorm S.hσ S.hsup χ hg]
  exact congrArg χ (projG_of_mem S hg).symm

theorem chiExt_eq_of_mem_C (S : DCtx k Ω) {M : Type} [Zero M] (χ : (Ω ≃ₐ[k] Ω) → M)
    {γ : Ω ≃ₐ[k] Ω} (hγ : γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers S.σ)) :
    chiExt S χ γ = χ γ := by
  rw [chiExt_of_mem S χ ((HS.CC_le_DD S.A S.σ S.hσ) hγ), projG_eq_self_of_mem_C S hγ]

/-- The `E`-correction attached to a `2`-cochain `c₀`: `-c₀ (projG g) (coorG g)` on `D`, `0`
outside. -/
def corrE (S : DCtx k Ω) {M : Type} [AddCommGroup M]
    (c₀ : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) : (Ω ≃ₐ[k] Ω) → M :=
  fun g => if h : g ∈ SSGRoute.decomp k S.A then -c₀ (projG S g) (coorG S g) else 0

@[simp] theorem corrE_of_mem (S : DCtx k Ω) {M : Type} [AddCommGroup M]
    (c₀ : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) {g : Ω ≃ₐ[k] Ω}
    (hg : g ∈ SSGRoute.decomp k S.A) : corrE S c₀ g = -c₀ (projG S g) (coorG S g) := dif_pos hg

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- The inhomogeneous `1`-coboundary of a cochain: `d¹b (g,h) = g·b h - b (gh) + b g`. -/
def d1c (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] (b : (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M :=
  fun g h => SSGRoute.res k K g • b h - b (g * h) + b g

@[simp] theorem d1c_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] (b : (Ω ≃ₐ[k] Ω) → M) (g h : Ω ≃ₐ[k] Ω) :
    d1c (p := p) (K := K) M b g h = SSGRoute.res k K g • b h - b (g * h) + b g := rfl

/-- The `2`-cochain `c - d¹ β̃` whose restriction to `I × I` vanishes. -/
def corrC (S : DCtx k Ω) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M :=
  c - d1c (p := p) (K := K) M (betaG (M := M) S β)

/-- The normal form of a `2`-cochain `c` from the data `β` (on `I`) and `χ` (on `C`). -/
def nform (S : DCtx k Ω) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β χ : (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M :=
  corrC (p := p) (K := K) S M c β - d1c (p := p) (K := K) M (corrE (M := M) S (corrC (p := p) (K := K) S M c β))
    - d1c (p := p) (K := K) M (chiExt (M := M) S χ)

/-- The slice at `σ`: the representative of the transgression class. -/
def slice (S : DCtx k Ω) {M : Type} (F : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → M := fun n => F n S.σ

end

end Work.PTCore
