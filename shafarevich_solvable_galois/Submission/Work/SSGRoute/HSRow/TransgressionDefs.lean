import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.HSRow.Coords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The explicit transgression map `H²_loc(D,M) → H¹_loc(I,M) ⧸ range (conj₁ - 1)`

Setting: `D = decomp k A = I ⋊ C`, `C = closure (zpowers σ)`, `M` a finite `𝔽_p`-module with a
`Gal(K/k)`-action, `ρ = res k K`.

For a locally constant `2`-cocycle `c` on `D` and a primitive `β` of its restriction to `I`
(`d¹β = c` on `I × I`, which exists by `hvan : H²_loc(I,M) = 0`), the *transgression cochain* on
`I` is the difference

  `tcoch I σ c β n = tprim σ c β n - β n`  (`n ∈ I`),

where `tprim` is the primitive of `c|_I` obtained as the graph of the `σ`-conjugate of the graph
of `-β` in the extension `M ⋊_c D`:

  `tprim σ c β x = ρ(σ) • β (σ⁻¹ * x * σ) - c σ (σ⁻¹ * x * σ) + ρ(x) • c σ σ⁻¹ - c (x * σ) σ⁻¹ + c 1 1`.

The lemma `tprim_primitive` (in the sibling files) shows `d¹ (tprim σ c β) = c` on `I × I`,
so `tcoch I σ c β` is a locally constant `1`-cocycle on `I`, and its class in `H¹_loc(I,M)`,
modulo `range (conj₁ - 1)`, is the transgression of `c`.

`normC` is the linear normalisation `c ↦ c - d¹ (const (c 1 1))`, which kills the "junk" values
`c g 1 = ρ(g) • c 1 1` of the non-normalised cocycles of `LTDDefs.Basic`; it is a coboundary
correction (so it changes no cohomology class).
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

/-- The primitive of `c|_{I × I}` obtained by conjugating the graph of `-β` by `σ`:
the `M`-component of `(0,σ) · (-β(n),n) · (0,σ)⁻¹` in the extension `M ⋊_c D`, reflected. -/
def tprim (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (σ : Ω ≃ₐ[k] Ω) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → M :=
  fun x => SSGRoute.res k K σ • β (σ⁻¹ * x * σ) - c σ (σ⁻¹ * x * σ)
    + SSGRoute.res k K x • c σ σ⁻¹ - c (x * σ) σ⁻¹ + c 1 1

/-- The transgression `1`-cochain on `I`: `tprim σ c β - β` (and `0` off `I`). -/
def tcoch (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → M :=
  fun x => if x ∈ I then tprim p k Ω K M σ c β x - β x else 0

/-- The linear normalisation of a `2`-cochain: `c ↦ c - d¹(const (c 1 1))`, i.e.
`normC c g h = c g h - ρ(g) • c 1 1`.  For a cocycle this is a cohomologous normalised cocycle
(`normC c g 1 = 0`, `normC c 1 h = 0`). -/
def normC (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M :=
  fun g h => c g h - SSGRoute.res k K g • c 1 1


/-- The `𝔽_p`-submodule of the locally constant (on `I`) `1`-cochains `G_k → M`. -/
def lcOneCoins (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {f | SSGRoute.IsLocConstOn I f}
  zero_mem' := ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨U, hUo, hU⟩ ⟨V, hVo, hV⟩
    exact ⟨U ⊓ V, by rw [Subgroup.coe_inf]; exact hUo.inter hVo, fun a ha u hu huI => by
      have h1 : u ∈ U := (Subgroup.mem_inf.mp hu).1
      have h2 : u ∈ V := (Subgroup.mem_inf.mp hu).2
      simp only [Pi.add_apply, hU a ha u h1 huI, hV a ha u h2 huI]⟩
  smul_mem' := by
    rintro r f ⟨U, hUo, hU⟩
    exact ⟨U, hUo, fun a ha u hu huI => by
      simp only [Pi.smul_apply, hU a ha u hu huI]⟩

@[simp] lemma mem_lcOneCoins (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (f : (Ω ≃ₐ[k] Ω) → M) :
    f ∈ lcOneCoins p k Ω K M I ↔ SSGRoute.IsLocConstOn I f := Iff.rfl

@[simp] lemma tprim_apply (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (σ : Ω ≃ₐ[k] Ω) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M)
    (x : Ω ≃ₐ[k] Ω) :
    tprim p k Ω K M σ c β x = SSGRoute.res k K σ • β (σ⁻¹ * x * σ) - c σ (σ⁻¹ * x * σ)
      + SSGRoute.res k K x • c σ σ⁻¹ - c (x * σ) σ⁻¹ + c 1 1 := rfl

@[simp] lemma tcoch_apply_of_mem (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M)
    {x : Ω ≃ₐ[k] Ω} (hx : x ∈ I) :
    tcoch p k Ω K M I σ c β x = tprim p k Ω K M σ c β x - β x := dif_pos hx

@[simp] lemma tcoch_apply_of_not_mem (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (β : (Ω ≃ₐ[k] Ω) → M)
    {x : Ω ≃ₐ[k] Ω} (hx : x ∉ I) :
    tcoch p k Ω K M I σ c β x = 0 := dif_neg hx

@[simp] lemma normC_apply (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (g h : Ω ≃ₐ[k] Ω) :
    normC p k Ω K M c g h = c g h - SSGRoute.res k K g • c 1 1 := rfl

end

end Work.SSGRoute.HSRow
