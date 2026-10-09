import Mathlib
import Submission.Work.SSGRoute.EulerSymm.Defs
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The locally constant model for coefficients in a module for a *subgroup*

`LTDDefs/Basic.lean` defines `H0loc`, `H1loc`, `H2loc` for coefficients in a `Gal(K/k)`-module.
The Mackey/Shapiro computation of the cohomology of `Ind_C^G N` at `D_A = decomp k A` produces
coefficients that are only modules for the open subgroup
`D_d = decomp k A ⊓ comap (res k K) (d C d⁻¹) ≤ G_k`, so a model with coefficients in a module for
an *arbitrary* subgroup `H ≤ G_k` is needed.  This file provides it, as a faithful copy of
`LTDDefs/Basic.lean` with the `res k K`-action replaced by the given `↥H`-action; the cocycle
condition uses the *first* variable, exactly as `SSGRoute.IsCocycleOn` does.

The model is a `Submodule`-quotient, hence carries `Module (ZMod p)` instances, so the Euler
characteristic `chiSubH` can be formed.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.EulerSymm

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The locally constant `1`-cocycles on `H ≤ G_k` with coefficients in a `↥H`-module. -/
def lcCocyclesH (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {f | (∀ g (hg : g ∈ H) h (hh : h ∈ H),
      f (g * h) = f g + (⟨g, hg⟩ : ↥H) • f h) ∧ SSGRoute.IsLocConstOn H f}
  zero_mem' := ⟨fun g _ h _ => by simp, ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      simp only [Pi.add_apply, hf1 a ha b hb, hg1 a ha b hb, smul_add]
      abel
    · obtain ⟨U1, hU1o, hU1⟩ := hf2
      obtain ⟨U2, hU2o, hU2⟩ := hg2
      refine ⟨U1 ⊓ U2, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hU1o.inter hU2o
      · intro a ha u hu huH
        simp only [Pi.add_apply, hU1 a ha u (Subgroup.mem_inf.mp hu).1 huH,
          hU2 a ha u (Subgroup.mem_inf.mp hu).2 huH]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    refine ⟨?_, ?_⟩
    · intro a ha b hb
      simp only [Pi.smul_apply, hf1 a ha b hb, smul_add]
      rw [smul_comm (⟨a, ha⟩ : ↥H) c (f b)]
    · obtain ⟨U, hUo, hU⟩ := hf2
      exact ⟨U, hUo, fun a ha u hu huH => by
        simp only [Pi.smul_apply, hU a ha u hu huH]⟩

/-- The `1`-coboundaries on `H` with coefficients in a `↥H`-module. -/
def coboundariesH (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {f | ∃ m : M, ∀ g (hg : g ∈ H), f g = (⟨g, hg⟩ : ↥H) • m - m}
  zero_mem' := ⟨0, fun g _ => by simp⟩
  add_mem' := by
    rintro f g ⟨m, hm⟩ ⟨m', hm'⟩
    refine ⟨m + m', fun x hx => ?_⟩
    simp only [Pi.add_apply, hm x hx, hm' x hx, smul_add]
    abel
  smul_mem' := by
    rintro c f ⟨m, hm⟩
    refine ⟨c • m, fun x hx => ?_⟩
    simp only [Pi.smul_apply, hm x hx, smul_sub]
    rw [smul_comm (⟨x, hx⟩ : ↥H) c m]

/-- The local `H¹` with coefficients in a `↥H`-module. -/
abbrev H1locH (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] : Type _ :=
  ↥(lcCocyclesH p k Ω H M) ⧸ (Submodule.comap (lcCocyclesH p k Ω H M).subtype
    (coboundariesH p k Ω H M))

/-- The local `H⁰` with coefficients in a `↥H`-module. -/
def H0locH (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] : Submodule (ZMod p) M where
  carrier := {m | ∀ g (hg : g ∈ H), (⟨g, hg⟩ : ↥H) • m = m}
  zero_mem' := fun g _ => by simp
  add_mem' := by
    rintro m n hm hn g hg
    rw [smul_add, hm g hg, hn g hg]
  smul_mem' := by
    rintro c m hm g hg
    rw [smul_comm (⟨g, hg⟩ : ↥H) c m, hm g hg]


/-- The locally constant `2`-cocycles on `H` with coefficients in a `↥H`-module. -/
def lcCocycles2H (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {c | (∀ g (hg : g ∈ H) h (hh : h ∈ H) l (hl : l ∈ H),
      (⟨g, hg⟩ : ↥H) • c h l - c (g * h) l + c g (h * l) - c g h = 0) ∧
    (∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ g ∈ H, ∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ U, u ∈ H → v ∈ H → c (g * u) (h * v) = c g h)}
  zero_mem' := ⟨fun g _ h _ l _ => by simp, ⟨⊤, isOpen_univ, fun g _ h _ u _ v _ _ _ => rfl⟩⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · intro a ha b hb d hd
      have h1 := hf1 a ha b hb d hd
      have h2 := hg1 a ha b hb d hd
      have key : (⟨a, ha⟩ : ↥H) • (f + g) b d - (f + g) (a * b) d + (f + g) a (b * d)
            - (f + g) a b
          = ((⟨a, ha⟩ : ↥H) • f b d - f (a * b) d + f a (b * d) - f a b)
            + ((⟨a, ha⟩ : ↥H) • g b d - g (a * b) d + g a (b * d) - g a b) := by
        simp only [Pi.add_apply, smul_add]; abel
      rw [key, h1, h2, add_zero]
    · obtain ⟨U1, ho1, hU1⟩ := hf2
      obtain ⟨U2, ho2, hU2⟩ := hg2
      refine ⟨U1 ⊓ U2, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact ho1.inter ho2
      · intro a ha b hb u hu v hv huH hvH
        simp only [Pi.add_apply, hU1 a ha b hb u (Subgroup.mem_inf.mp hu).1 v
          (Subgroup.mem_inf.mp hv).1 huH hvH, hU2 a ha b hb u (Subgroup.mem_inf.mp hu).2 v
          (Subgroup.mem_inf.mp hv).2 huH hvH]
  smul_mem' := by
    rintro r c ⟨hc1, hc2⟩
    refine ⟨?_, ?_⟩
    · intro a ha b hb d hd
      have h1 := hc1 a ha b hb d hd
      have key : (⟨a, ha⟩ : ↥H) • (r • c) b d - (r • c) (a * b) d + (r • c) a (b * d)
            - (r • c) a b
          = r • ((⟨a, ha⟩ : ↥H) • c b d - c (a * b) d + c a (b * d) - c a b) := by
        simp only [Pi.smul_apply, smul_sub, smul_add]
        rw [← smul_comm (⟨a, ha⟩ : ↥H) r (c b d)]
      rw [key, h1, smul_zero]
    · obtain ⟨U, ho, hU⟩ := hc2
      exact ⟨U, ho, fun a ha b hb u hu v hv huH hvH => by
        simp only [Pi.smul_apply, hU a ha b hb u hu v hv huH hvH]⟩

/-- The locally constant `2`-coboundaries on `H` with coefficients in a `↥H`-module. -/
def coboundaries2H (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {c | ∃ b : (Ω ≃ₐ[k] Ω) → M, SSGRoute.IsLocConstOn H b ∧
    ∀ g (hg : g ∈ H) h (hh : h ∈ H),
      c g h = (⟨g, hg⟩ : ↥H) • b h - b (g * h) + b g}
  zero_mem' := ⟨0, ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩, fun g _ h _ => by simp⟩
  add_mem' := by
    rintro f g ⟨β, hβ, hβf⟩ ⟨β', hβ', hβ'f⟩
    refine ⟨β + β', ?_, ?_⟩
    · obtain ⟨U1, ho1, hU1⟩ := hβ
      obtain ⟨U2, ho2, hU2⟩ := hβ'
      refine ⟨U1 ⊓ U2, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact ho1.inter ho2
      · intro a ha u hu huH
        rw [Pi.add_apply, Pi.add_apply, hU1 a ha u (Subgroup.mem_inf.mp hu).1 huH,
          hU2 a ha u (Subgroup.mem_inf.mp hu).2 huH]
    · intro a ha b hb
      simp only [Pi.add_apply, hβf a ha b hb, hβ'f a ha b hb, smul_add]
      abel
  smul_mem' := by
    rintro r c ⟨β, hβ, hβc⟩
    refine ⟨r • β, ?_, ?_⟩
    · obtain ⟨U, ho, hU⟩ := hβ
      exact ⟨U, ho, fun a ha u hu huH => by rw [Pi.smul_apply, Pi.smul_apply, hU a ha u hu huH]⟩
    · intro a ha b hb
      simp only [Pi.smul_apply, hβc a ha b hb, smul_sub, smul_add]
      rw [← smul_comm (⟨a, ha⟩ : ↥H) r (β b)]

/-- The local `H²` with coefficients in a `↥H`-module. -/
abbrev H2locH (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] : Type _ :=
  ↥(lcCocycles2H p k Ω H M) ⧸ (Submodule.comap (lcCocycles2H p k Ω H M).subtype
    (coboundaries2H p k Ω H M))

/-- The Euler characteristic of `H ≤ G_k` with coefficients in an arbitrary `↥H`-module. -/
noncomputable def chiSubH (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M] : ℤ :=
  (Module.finrank (ZMod p) ↥(H0locH p k Ω H M) : ℤ)
    - (Module.finrank (ZMod p) (H1locH p k Ω H M) : ℤ)
    + (Module.finrank (ZMod p) (H2locH p k Ω H M) : ℤ)


section Bridge

variable (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **Model bridge.**  For a `Gal(K/k)`-module `M` carrying a compatible `↥H`-action, the
generalized invariant `chiSubH` agrees with the `LTDDefs` invariant `chiH`. -/
theorem chiSubH_bridge (H : Subgroup (Ω ≃ₐ[k] Ω)) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [DistribMulAction ↥H M] [SMulCommClass ↥H (ZMod p) M]
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    chiSubH p k Ω H M = chiH p k Ω K H M := by
  have h0 : H0locH p k Ω H M = Work.SSGRoute.H0loc p k Ω K M H := by
    apply le_antisymm
    · intro m hm g hg
      have h := hm g hg
      rwa [hcompat ⟨g, hg⟩ m] at h
    · intro m hm g hg
      have h := hm g hg
      rwa [← hcompat ⟨g, hg⟩ m] at h
  have h1c : lcCocyclesH p k Ω H M = Work.SSGRoute.lcCocycles p k Ω K M H := by
    ext f
    simp only [lcCocyclesH, Work.SSGRoute.lcCocycles, SetLike.mem_coe, Set.mem_setOf_eq,
      SSGRoute.IsCocycleOn, SSGRoute.IsLocConstOn]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun g hg h hh => by
        have hh1 := h1 g hg h hh
        rwa [hcompat ⟨g, hg⟩ (f h)] at hh1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun g hg h hh => by
        have hh1 := h1 g hg h hh
        rwa [← hcompat ⟨g, hg⟩ (f h)] at hh1, h2⟩
  have h1b : coboundariesH p k Ω H M = Work.SSGRoute.coboundaries p k Ω K M H := by
    ext f
    simp only [coboundariesH, Work.SSGRoute.coboundaries, SetLike.mem_coe, Set.mem_setOf_eq,
      SSGRoute.IsCoboundaryOn]
    constructor
    · rintro ⟨m, hm⟩; exact ⟨m, fun g hg => by rw [hm g hg, hcompat ⟨g, hg⟩]⟩
    · rintro ⟨m, hm⟩; exact ⟨m, fun g hg => by rw [hm g hg, hcompat ⟨g, hg⟩]⟩
  have h2c : lcCocycles2H p k Ω H M = Work.SSGRoute.lcCocycles2 p k Ω K M H := by
    ext c
    simp only [lcCocycles2H, Work.SSGRoute.lcCocycles2, SetLike.mem_coe, Set.mem_setOf_eq,
      Work.SSGRoute.IsCocycle2On, Work.SSGRoute.IsLocConst2On]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun g hg h hh l hl => by
        have hh1 := h1 g hg h hh l hl
        rwa [hcompat ⟨g, hg⟩ (c h l)] at hh1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun g hg h hh l hl => by
        have hh1 := h1 g hg h hh l hl
        rwa [← hcompat ⟨g, hg⟩ (c h l)] at hh1, h2⟩
  have h2b : coboundaries2H p k Ω H M = Work.SSGRoute.coboundaries2 p k Ω K M H := by
    ext c
    simp only [coboundaries2H, Work.SSGRoute.coboundaries2, SetLike.mem_coe, Set.mem_setOf_eq,
      SSGRoute.IsCoboundary2On]
    constructor
    · rintro ⟨b, hb, hbc⟩
      exact ⟨b, hb, fun g hg h hh => by rw [hbc g hg h hh, hcompat ⟨g, hg⟩]⟩
    · rintro ⟨b, hb, hbc⟩
      exact ⟨b, hb, fun g hg h hh => by rw [hbc g hg h hh, hcompat ⟨g, hg⟩]⟩
  unfold chiSubH chiH H1locH H2locH
  rw [h0, h1c, h1b, h2c, h2b]

end Bridge 

end

end Work.SSGRoute.EulerSymm
