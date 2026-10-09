import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The third local cohomology of the model, and the `2 → 3` segment of its long exact sequence

The local Euler characteristic (Milne, *ADT*, I.2.8) is proved by *additivity of
`M ↦ [H⁰][H²]/[H¹]` over short exact sequences of coefficient modules*.  Additivity is read off
the long exact sequence

`0 → H⁰(M') → H⁰(M) → H⁰(M'') → H¹(M') → H¹(M) → H¹(M'') → H²(M') → H²(M) → H²(M'') → 0`,

whose final `0` is the vanishing of `H³` for the coefficient module involved (equivalently
`cd_p(G_{k_v}) ≤ 2`).  The model of `LTDDefs/Basic.lean` stops at `H2loc`, so the *end* of the
sequence cannot even be stated there.  This file supplies it:

* `dCochain2` — the inhomogeneous `2`-coboundary operator
  `d²b (g,h,k) = g·b(h,k) - b(gh,k) + b(g,hk) - b(g,h)`;
* `IsCocycle3On`, `IsLocConst3On`, `lcCocycles3` — the locally constant `3`-cocycles on `H`,
  with the `3`-cocycle condition imposed only on `H` (exactly as `lcCocycles2` does in degree `2`);
* `IsCoboundary3On`, `coboundaries3` — the `d²` of locally constant `2`-cochains on `H`;
* `H3loc` — the third local cohomology group of the model;
* `isCocycle3On_dCochain2` — `d³ ∘ d² = 0`, the identity that makes `d²` of a locally constant
  `2`-cochain a `3`-cocycle (the input to the connecting map `H²(M'') → H³(M')`);
* `coboundaries3_le_lcCocycles3` — the `3`-coboundaries are locally constant `3`-cocycles.

With `H3loc` in place, the deep arithmetic input can be isolated as the explicit hypothesis
`Subsingleton (H3loc p k Ω K M' (SSGRoute.decomp k A))` — "`H³ = 0` at the place" — and the
additivity step becomes statable in the model.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-! ## The differential `d²` on `2`-cochains -/

/-- The inhomogeneous `2`-coboundary operator, matching the formula of
`SSGRoute.IsCoboundary2On` (which is `d¹` on `1`-cochains):
`d²b (g,h,k) = g·b(h,k) - b(gh,k) + b(g,hk) - b(g,h)`. -/
def dCochain2 (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (b : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :
    (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M :=
  fun g h l => SSGRoute.res k K g • b h l - b (g * h) l + b g (h * l) - b g h

@[simp] theorem dCochain2_apply (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (b : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (g h l : Ω ≃ₐ[k] Ω) :
    dCochain2 p k Ω K M b g h l
      = SSGRoute.res k K g • b h l - b (g * h) l + b g (h * l) - b g h := rfl

/-! ## Locally constant `3`-cocycles -/

/-- The inhomogeneous `3`-cocycle condition, imposed only on `H`:
`g·e(h,k,l) - e(gh,k,l) + e(g,hk,l) - e(g,h,kl) + e(g,h,k) = 0` for `g,h,k,l ∈ H`. -/
def IsCocycle3On (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ l ∈ H, ∀ m ∈ H,
    SSGRoute.res k K g • e h l m - e (g * h) l m + e g (h * l) m - e g h (l * m) + e g h l = 0

/-- Local constancy of a `3`-cochain on `H` (uniform right-invariance by an open subgroup of
`G_k`, in all three variables, at points of `H`). -/
def IsLocConst3On (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) : Prop :=
  ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
    ∀ g ∈ H, ∀ h ∈ H, ∀ l ∈ H, ∀ u ∈ U, ∀ v ∈ U, ∀ w ∈ U,
      u ∈ H → v ∈ H → w ∈ H → e (g * u) (h * v) (l * w) = e g h l

/-- The locally constant `3`-cocycles on `H`, as an `𝔽_p`-submodule of the `3`-cochains. -/
def lcCocycles3 (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {e | IsCocycle3On p k Ω K M H e ∧ IsLocConst3On p k Ω K M H e}
  zero_mem' := ⟨fun g _ h _ l _ m _ => by simp,
    ⟨⊤, isOpen_univ, fun g _ h _ l _ u _ v _ w _ _ _ _ => rfl⟩⟩
  add_mem' := by
    rintro f e ⟨hf1, hf2⟩ ⟨he1, he2⟩
    refine ⟨?_, ?_⟩
    · intro g hg h hh l hl m hm
      have h1 := hf1 g hg h hh l hl m hm
      have h2 := he1 g hg h hh l hl m hm
      have key : SSGRoute.res k K g • (f + e) h l m - (f + e) (g * h) l m
            + (f + e) g (h * l) m - (f + e) g h (l * m) + (f + e) g h l
          = (SSGRoute.res k K g • f h l m - f (g * h) l m + f g (h * l) m
              - f g h (l * m) + f g h l)
            + (SSGRoute.res k K g • e h l m - e (g * h) l m + e g (h * l) m
              - e g h (l * m) + e g h l) := by
        simp only [Pi.add_apply, smul_add]
        abel
      rw [key, h1, h2, add_zero]
    · obtain ⟨U1, ho1, hU1⟩ := hf2
      obtain ⟨U2, ho2, hU2⟩ := he2
      refine ⟨U1 ⊓ U2, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact ho1.inter ho2
      · intro g hg h hh l hl u hu v hv w hw huH hvH hwH
        have h1u : u ∈ U1 := (Subgroup.mem_inf.mp hu).1
        have h1v : v ∈ U1 := (Subgroup.mem_inf.mp hv).1
        have h1w : w ∈ U1 := (Subgroup.mem_inf.mp hw).1
        have h2u : u ∈ U2 := (Subgroup.mem_inf.mp hu).2
        have h2v : v ∈ U2 := (Subgroup.mem_inf.mp hv).2
        have h2w : w ∈ U2 := (Subgroup.mem_inf.mp hw).2
        simp only [Pi.add_apply, hU1 g hg h hh l hl u h1u v h1v w h1w huH hvH hwH,
          hU2 g hg h hh l hl u h2u v h2v w h2w huH hvH hwH]
  smul_mem' := by
    rintro r e ⟨he1, he2⟩
    refine ⟨?_, ?_⟩
    · intro g hg h hh l hl m hm
      have h1 := he1 g hg h hh l hl m hm
      have key : SSGRoute.res k K g • (r • e) h l m - (r • e) (g * h) l m
            + (r • e) g (h * l) m - (r • e) g h (l * m) + (r • e) g h l
          = r • (SSGRoute.res k K g • e h l m - e (g * h) l m + e g (h * l) m
              - e g h (l * m) + e g h l) := by
        simp only [Pi.smul_apply, smul_sub, smul_add]
        rw [smul_comm (SSGRoute.res k K g) r (e h l m)]
      rw [key, h1, smul_zero]
    · obtain ⟨U, ho, hU⟩ := he2
      exact ⟨U, ho, fun g hg h hh l hl u hu v hv w hw huH hvH hwH => by
        simp only [Pi.smul_apply, hU g hg h hh l hl u hu v hv w hw huH hvH hwH]⟩

@[simp] theorem mem_lcCocycles3 (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :
    e ∈ lcCocycles3 p k Ω K M H ↔
      IsCocycle3On p k Ω K M H e ∧ IsLocConst3On p k Ω K M H e := Iff.rfl

/-! ## `3`-coboundaries, and the differential identity `d³ ∘ d² = 0` -/

/-- A `3`-coboundary on `H`: the `d²` of a locally constant `2`-cochain on `H`. -/
def IsCoboundary3On (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) : Prop :=
  ∃ b : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M, IsLocConst2On p k Ω K M H b ∧
    ∀ g ∈ H, ∀ h ∈ H, ∀ l ∈ H, e g h l = dCochain2 p k Ω K M b g h l

/-- The `3`-coboundaries on `H`, as an `𝔽_p`-submodule of the `3`-cochains. -/
def coboundaries3 (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {e | IsCoboundary3On p k Ω K M H e}
  zero_mem' := ⟨0, ⟨⊤, isOpen_univ, fun g _ h _ u _ v _ _ _ => rfl⟩,
    fun g _ h _ l _ => by simp [dCochain2]⟩
  add_mem' := by
    rintro f e ⟨b, hb, hbf⟩ ⟨b', hb', hb'e⟩
    refine ⟨b + b', ?_, ?_⟩
    · obtain ⟨U1, ho1, hU1⟩ := hb
      obtain ⟨U2, ho2, hU2⟩ := hb'
      refine ⟨U1 ⊓ U2, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact ho1.inter ho2
      · intro g hg h hh u hu v hv huH hvH
        simp only [Pi.add_apply, hU1 g hg h hh u (Subgroup.mem_inf.mp hu).1 v
          (Subgroup.mem_inf.mp hv).1 huH hvH,
          hU2 g hg h hh u (Subgroup.mem_inf.mp hu).2 v (Subgroup.mem_inf.mp hv).2 huH hvH]
    · intro g hg h hh l hl
      simp only [dCochain2_apply, Pi.add_apply, hbf g hg h hh l hl, hb'e g hg h hh l hl,
        smul_add]
      abel
  smul_mem' := by
    rintro r e ⟨b, hb, hbe⟩
    refine ⟨r • b, ?_, ?_⟩
    · obtain ⟨U, ho, hU⟩ := hb
      exact ⟨U, ho, fun g hg h hh u hu v hv huH hvH => by
        simp only [Pi.smul_apply, hU g hg h hh u hu v hv huH hvH]⟩
    · intro g hg h hh l hl
      simp only [dCochain2_apply, Pi.smul_apply, hbe g hg h hh l hl, smul_sub, smul_add]
      rw [smul_comm (SSGRoute.res k K g) r (b h l)]

@[simp] theorem mem_coboundaries3 (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (e : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :
    e ∈ coboundaries3 p k Ω K M H ↔ IsCoboundary3On p k Ω K M H e := Iff.rfl

/-- **The differential squares to zero**: `d²` of *any* `2`-cochain satisfies the `3`-cocycle
condition.  (Local constancy of `d²b` needs a locally constant `b`, which is why the *coboundaries*
are defined from locally constant representatives; this identity is the algebraic content of
`d³ ∘ d² = 0` and is what makes the connecting map `H²(M'') → H³(M')` a cocycle.) -/
theorem isCocycle3On_dCochain2 (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (b : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :
    IsCocycle3On p k Ω K M H (dCochain2 p k Ω K M b) := by
  intro g hg h hh l hl m hm
  simp only [dCochain2_apply, smul_sub, smul_add, smul_neg, map_mul, mul_smul, mul_assoc,
    neg_smul, one_smul]
  abel

/-- **The third local cohomology of the model**: locally constant `3`-cocycles on `H`, modulo the
`d²` of locally constant `2`-cochains on `H` — defined exactly as `H2loc` is defined from
`lcCocycles2` and `coboundaries2`. -/
abbrev H3loc (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Type :=
  ↥(lcCocycles3 p k Ω K M H) ⧸ (Submodule.comap (lcCocycles3 p k Ω K M H).subtype
    (coboundaries3 p k Ω K M H))

end

end Work.SSGRoute
