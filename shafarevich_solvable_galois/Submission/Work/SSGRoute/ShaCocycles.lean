import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute
open scoped Pointwise

universe u v w

section Closure

variable {Γ G M M₂ : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
  [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M₂] [DistribMulAction G M₂]
  {act : Γ →* G}

/-! ## The zero cochains -/

theorem isLocConstOn_zero {H : Subgroup Γ} :
    SSGRoute.IsLocConstOn H (fun _ : Γ => (0 : M)) :=
  ⟨⊤, isOpen_univ, fun _ _ _ _ _ => rfl⟩

theorem isCocycleOn_zero {H : Subgroup Γ} :
    SSGRoute.IsCocycleOn act H (fun _ : Γ => (0 : M)) := by
  intro g _ h _
  simp

theorem isCoboundaryOn_zero {H : Subgroup Γ} :
    SSGRoute.IsCoboundaryOn act H (fun _ : Γ => (0 : M)) :=
  ⟨0, by intro g _; simp⟩

theorem isLocConst2_zero :
    SSGRoute.IsLocConst2 (fun _ _ : Γ => (0 : M)) :=
  ⟨⊤, isOpen_univ, fun _ _ _ _ _ _ => rfl⟩

theorem isCocycle2_zero : SSGRoute.IsCocycle2 act (fun _ _ : Γ => (0 : M)) := by
  intro g h l
  simp

theorem isCoboundary2On_zero {H : Subgroup Γ} :
    SSGRoute.IsCoboundary2On act H (fun _ _ : Γ => (0 : M)) :=
  ⟨0, isLocConstOn_zero, by intro g _ h _; simp⟩

/-! ## Additivity and negation -/

theorem isLocConstOn_add {H : Subgroup Γ} {f g : Γ → M}
    (hf : SSGRoute.IsLocConstOn H f) (hg : SSGRoute.IsLocConstOn H g) :
    SSGRoute.IsLocConstOn H (fun σ => f σ + g σ) := by
  obtain ⟨U, hU, hfU⟩ := hf
  obtain ⟨V, hV, hgV⟩ := hg
  refine ⟨U ⊓ V, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact hU.inter hV
  · intro g₀ hg₀ u hu huH
    obtain ⟨huU, huV⟩ := Subgroup.mem_inf.mp hu
    show f (g₀ * u) + g (g₀ * u) = f g₀ + g g₀
    rw [hfU g₀ hg₀ u huU huH, hgV g₀ hg₀ u huV huH]

theorem isLocConstOn_neg {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsLocConstOn H f) :
    SSGRoute.IsLocConstOn H (fun σ => - f σ) := by
  obtain ⟨U, hU, hfU⟩ := hf
  exact ⟨U, hU, fun g hg u hu huH => by
    show - f (g * u) = - f g
    rw [hfU g hg u hu huH]⟩

theorem isCocycleOn_add {H : Subgroup Γ} {f g : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H f) (hg : SSGRoute.IsCocycleOn act H g) :
    SSGRoute.IsCocycleOn act H (fun σ => f σ + g σ) := by
  intro x hx y hy
  show f (x * y) + g (x * y) = f x + g x + act x • (f y + g y)
  rw [smul_add, hf x hx y hy, hg x hx y hy]
  abel

theorem isCocycleOn_neg {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCocycleOn act H f) :
    SSGRoute.IsCocycleOn act H (fun σ => - f σ) := by
  intro x hx y hy
  show - f (x * y) = - f x + act x • (- f y)
  rw [smul_neg, hf x hx y hy]
  abel

theorem isCoboundaryOn_add {H : Subgroup Γ} {f g : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn act H f) (hg : SSGRoute.IsCoboundaryOn act H g) :
    SSGRoute.IsCoboundaryOn act H (fun σ => f σ + g σ) := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m + n, fun g₀ hg₀ => ?_⟩
  show f g₀ + g g₀ = act g₀ • (m + n) - (m + n)
  rw [hm g₀ hg₀, hn g₀ hg₀, smul_add]
  abel

theorem isCoboundaryOn_neg {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn act H f) :
    SSGRoute.IsCoboundaryOn act H (fun σ => - f σ) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨-m, fun g₀ hg₀ => ?_⟩
  show - f g₀ = act g₀ • (-m) - (-m)
  rw [hm g₀ hg₀, smul_neg]
  abel

theorem isLocConst2_add {c d : Γ → Γ → M}
    (hc : SSGRoute.IsLocConst2 c) (hd : SSGRoute.IsLocConst2 d) :
    SSGRoute.IsLocConst2 (fun σ τ => c σ τ + d σ τ) := by
  obtain ⟨U, hU, hcU⟩ := hc
  obtain ⟨V, hV, hdU⟩ := hd
  refine ⟨U ⊓ V, ?_, ?_⟩
  · rw [Subgroup.coe_inf]; exact hU.inter hV
  · intro g h u v hu hv
    obtain ⟨huU, huV⟩ := Subgroup.mem_inf.mp hu
    obtain ⟨hvU, hvV⟩ := Subgroup.mem_inf.mp hv
    show c (g * u) (h * v) + d (g * u) (h * v) = c g h + d g h
    rw [hcU g h u v huU hvU, hdU g h u v huV hvV]

theorem isLocConst2_neg {c : Γ → Γ → M} (hc : SSGRoute.IsLocConst2 c) :
    SSGRoute.IsLocConst2 (fun σ τ => - c σ τ) := by
  obtain ⟨U, hU, hcU⟩ := hc
  exact ⟨U, hU, fun g h u v hu hv => by
    show - c (g * u) (h * v) = - c g h
    rw [hcU g h u v hu hv]⟩

theorem isCocycle2_add {c d : Γ → Γ → M}
    (hc : SSGRoute.IsCocycle2 act c) (hd : SSGRoute.IsCocycle2 act d) :
    SSGRoute.IsCocycle2 act (fun σ τ => c σ τ + d σ τ) := by
  intro g h l
  have h1 := hc g h l
  have h2 := hd g h l
  have key : act g • (c h l + d h l) - (c (g * h) l + d (g * h) l)
        + (c g (h * l) + d g (h * l)) - (c g h + d g h)
      = (act g • c h l - c (g * h) l + c g (h * l) - c g h)
        + (act g • d h l - d (g * h) l + d g (h * l) - d g h) := by
    rw [smul_add]; abel
  rw [key, h1, h2, add_zero]

theorem isCocycle2_neg {c : Γ → Γ → M} (hc : SSGRoute.IsCocycle2 act c) :
    SSGRoute.IsCocycle2 act (fun σ τ => - c σ τ) := by
  intro g h l
  have h1 := hc g h l
  have key : act g • (- c h l) - (- c (g * h) l) + (- c g (h * l)) - (- c g h)
      = -(act g • c h l - c (g * h) l + c g (h * l) - c g h) := by
    rw [smul_neg]; abel
  rw [key, h1, neg_zero]

theorem isCoboundary2On_add {H : Subgroup Γ} {c d : Γ → Γ → M}
    (hc : SSGRoute.IsCoboundary2On act H c) (hd : SSGRoute.IsCoboundary2On act H d) :
    SSGRoute.IsCoboundary2On act H (fun σ τ => c σ τ + d σ τ) := by
  obtain ⟨b, hb, hbc⟩ := hc
  obtain ⟨b', hb', hbc'⟩ := hd
  refine ⟨fun σ => b σ + b' σ, isLocConstOn_add hb hb', ?_⟩
  intro g hg h hh
  show c g h + d g h = act g • (b h + b' h) - (b (g * h) + b' (g * h)) + (b g + b' g)
  rw [hbc g hg h hh, hbc' g hg h hh, smul_add]
  abel

theorem isCoboundary2On_neg {H : Subgroup Γ} {c : Γ → Γ → M}
    (hc : SSGRoute.IsCoboundary2On act H c) :
    SSGRoute.IsCoboundary2On act H (fun σ τ => - c σ τ) := by
  obtain ⟨b, hb, hbc⟩ := hc
  refine ⟨fun σ => - b σ, isLocConstOn_neg hb, ?_⟩
  intro g hg h hh
  show - c g h = act g • (- b h) - (- b (g * h)) + (- b g)
  rw [hbc g hg h hh, smul_neg]
  abel

/-! ## Push-forward along a `G`-equivariant additive map -/

theorem isLocConstOn_push {H : Subgroup Γ} {b : Γ → M}
    (hb : SSGRoute.IsLocConstOn H b) (φ : M → M₂) :
    SSGRoute.IsLocConstOn H (fun σ => φ (b σ)) := by
  obtain ⟨U, hU, hUb⟩ := hb
  exact ⟨U, hU, fun g hg u hu huH => by
    show φ (b (g * u)) = φ (b g)
    rw [hUb g hg u hu huH]⟩

theorem isLocConst2_push {c : Γ → Γ → M} (hc : SSGRoute.IsLocConst2 c) (φ : M → M₂) :
    SSGRoute.IsLocConst2 (fun σ τ => φ (c σ τ)) := by
  obtain ⟨U, hU, hUb⟩ := hc
  exact ⟨U, hU, fun g h u v hu hv => by
    show φ (c (g * u) (h * v)) = φ (c g h)
    rw [hUb g h u v hu hv]⟩

theorem isCocycleOn_push {H : Subgroup Γ} {f : Γ → M} (hf : SSGRoute.IsCocycleOn act H f)
    (φ : M →+ M₂) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SSGRoute.IsCocycleOn act H (fun σ => φ (f σ)) := by
  intro x hx y hy
  have h := hf x hx y hy
  show φ (f (x * y)) = φ (f x) + act x • φ (f y)
  rw [h, map_add, hφ]

theorem isCoboundaryOn_push {H : Subgroup Γ} {f : Γ → M} (hf : SSGRoute.IsCoboundaryOn act H f)
    (φ : M →+ M₂) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SSGRoute.IsCoboundaryOn act H (fun σ => φ (f σ)) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨φ m, fun g hg => ?_⟩
  show φ (f g) = act g • φ m - φ m
  rw [hm g hg, map_sub, hφ]

theorem isCocycle2_push {c : Γ → Γ → M} (hc : SSGRoute.IsCocycle2 act c)
    (φ : M →+ M₂) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SSGRoute.IsCocycle2 act (fun σ τ => φ (c σ τ)) := by
  intro g h l
  have key : φ (act g • c h l - c (g * h) l + c g (h * l) - c g h) = 0 := by
    rw [hc g h l, map_zero]
  simpa only [map_sub, map_add, hφ] using key

theorem isCoboundary2On_push {H : Subgroup Γ} {c : Γ → Γ → M}
    (hc : SSGRoute.IsCoboundary2On act H c) (φ : M →+ M₂)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) :
    SSGRoute.IsCoboundary2On act H (fun σ τ => φ (c σ τ)) := by
  obtain ⟨b, hb, hbc⟩ := hc
  refine ⟨fun σ => φ (b σ), isLocConstOn_push hb φ, fun g hg h hh => ?_⟩
  show φ (c g h) = act g • φ (b h) - φ (b (g * h)) + φ (b g)
  rw [hbc g hg h hh]
  simp only [map_sub, map_add, hφ]

theorem isCoboundary2On_mono {H H' : Subgroup Γ} (hsub : H ≤ H') {c : Γ → Γ → M}
    (hc : SSGRoute.IsCoboundary2On act H' c) : SSGRoute.IsCoboundary2On act H c := by
  obtain ⟨b, hb, hbc⟩ := hc
  refine ⟨b, ?_, fun g hg h hh => hbc g (hsub hg) h (hsub hh)⟩
  obtain ⟨U, hU, hUb⟩ := hb
  exact ⟨U, hU, fun g hg u hu huH => hUb g (hsub hg) u hu (hsub huH)⟩

theorem isCoboundaryOn_mono {H H' : Subgroup Γ} (hsub : H ≤ H') {f : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn act H' f) : SSGRoute.IsCoboundaryOn act H f := by
  obtain ⟨m, hm⟩ := hf
  exact ⟨m, fun g hg => hm g (hsub hg)⟩

theorem isCocycle2_one_right {c : Γ → Γ → M} (hc : SSGRoute.IsCocycle2 act c) (g : Γ) :
    act g • c 1 1 = c g 1 := by
  have h := hc g 1 1
  simp only [mul_one] at h
  rw [sub_add_cancel] at h
  exact sub_eq_zero.mp h

theorem isCocycle2_one_left {c : Γ → Γ → M} (hc : SSGRoute.IsCocycle2 act c) (x : Γ) :
    c 1 x = c 1 1 := by
  have h := hc 1 1 x
  simp only [map_one, one_mul, one_smul] at h
  rw [sub_self, zero_add] at h
  exact sub_eq_zero.mp h

/-- The coboundary of a `1`-cochain is a `2`-cocycle (`δ ∘ δ = 0`). -/
theorem isCocycle2_of_isCoboundary2_top {c : Γ → Γ → M}
    (hc : SSGRoute.IsCoboundary2On act ⊤ c) : SSGRoute.IsCocycle2 act c := by
  obtain ⟨b, -, hb⟩ := hc
  intro g h l
  rw [hb h trivial l trivial, hb (g * h) trivial l trivial, hb g trivial (h * l) trivial,
    hb g trivial h trivial]
  simp only [map_mul, mul_smul, mul_assoc, smul_add, smul_neg, neg_smul, one_smul, sub_eq_add_neg,
    add_assoc]
  abel

/-- A locally constant `1`-coboundary made explicit: the primitive of a `2`-coboundary is
locally constant, hence so is the `1`-coboundary it defines. -/
theorem isCocycleOn_of_isCoboundaryOn {H : Subgroup Γ} {f : Γ → M}
    (hf : SSGRoute.IsCoboundaryOn act H f) : SSGRoute.IsCocycleOn act H f := by
  obtain ⟨m, hm⟩ := hf
  intro g hg h hh
  rw [hm g hg, hm (g * h) (H.mul_mem hg hh), hm h hh, map_mul, mul_smul, smul_sub]
  abel

end Closure

/-! ## `𝔽_p`-scalar closure -/

section SmulClosure

variable {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
  [AddCommGroup M] [DistribMulAction G M] {act : Γ →* G}

theorem isLocConstOn_smul {p : ℕ} {H : Subgroup Γ} {f : Γ → M} [SMul (ZMod p) M]
    (hf : SSGRoute.IsLocConstOn H f) (a : ZMod p) :
    SSGRoute.IsLocConstOn H (fun σ => a • f σ) := by
  obtain ⟨U, hU, hfU⟩ := hf
  exact ⟨U, hU, fun g hg u hu huH => by
    show a • f (g * u) = a • f g
    rw [hfU g hg u hu huH]⟩

theorem isLocConst2_smul {p : ℕ} {c : Γ → Γ → M} [SMul (ZMod p) M]
    (hc : SSGRoute.IsLocConst2 c) (a : ZMod p) :
    SSGRoute.IsLocConst2 (fun σ τ => a • c σ τ) := by
  obtain ⟨U, hU, hcU⟩ := hc
  exact ⟨U, hU, fun g h u v hu hv => by
    show a • c (g * u) (h * v) = a • c g h
    rw [hcU g h u v hu hv]⟩

theorem isCocycleOn_smul {p : ℕ} {H : Subgroup Γ} {f : Γ → M} [Module (ZMod p) M]
    [SMulCommClass G (ZMod p) M]
    (hf : SSGRoute.IsCocycleOn act H f) (a : ZMod p) :
    SSGRoute.IsCocycleOn act H (fun σ => a • f σ) := by
  intro x hx y hy
  have h := hf x hx y hy
  show a • f (x * y) = a • f x + act x • (a • f y)
  rw [h, smul_add, ← smul_comm (act x) a]

theorem isCocycle2_smul {p : ℕ} {c : Γ → Γ → M} [Module (ZMod p) M]
    [SMulCommClass G (ZMod p) M]
    (hc : SSGRoute.IsCocycle2 act c) (a : ZMod p) :
    SSGRoute.IsCocycle2 act (fun σ τ => a • c σ τ) := by
  intro g h l
  have hcl := hc g h l
  have key : a • (act g • c h l - c (g * h) l + c g (h * l) - c g h) = 0 := by
    rw [hcl, smul_zero]
  rw [smul_sub, smul_add, smul_sub, ← smul_comm (act g) a] at key
  exact key

theorem isCoboundaryOn_smul {p : ℕ} {H : Subgroup Γ} {f : Γ → M} [Module (ZMod p) M]
    [SMulCommClass G (ZMod p) M]
    (hf : SSGRoute.IsCoboundaryOn act H f) (a : ZMod p) :
    SSGRoute.IsCoboundaryOn act H (fun σ => a • f σ) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨a • m, fun g hg => ?_⟩
  show a • f g = act g • (a • m) - a • m
  rw [hm g hg, smul_sub, ← smul_comm (act g) a]

theorem isCoboundary2On_smul {p : ℕ} {H : Subgroup Γ} {c : Γ → Γ → M} [Module (ZMod p) M]
    [SMulCommClass G (ZMod p) M] (hc : SSGRoute.IsCoboundary2On act H c) (a : ZMod p) :
    SSGRoute.IsCoboundary2On act H (fun σ τ => a • c σ τ) := by
  obtain ⟨b, hb, hbc⟩ := hc
  refine ⟨fun σ => a • b σ, isLocConstOn_smul hb a, ?_⟩
  intro g hg h hh
  show a • c g h = act g • (a • b h) - a • b (g * h) + a • b g
  rw [hbc g hg h hh, smul_add, smul_sub, ← smul_comm (act g) a]

end SmulClosure

/-! ## The Tate--Shafarevich groups -/

/-- The locally trivial continuous `1`-cocycles `G_k → M`: continuous (locally constant)
`1`-cocycles which are coboundaries on the decomposition group of every finite place of `Ω` and on
the group generated by every involution of `G_k`. -/
def Z1loc (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {φ | SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ φ ∧ SSGRoute.IsLocConstOn ⊤ φ ∧
    (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) φ) ∧
    (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers σ) φ)}
  zero_mem' := ⟨isCocycleOn_zero, isLocConstOn_zero, fun _ _ => isCoboundaryOn_zero,
    fun _ _ => isCoboundaryOn_zero⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3, hf4⟩ ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨isCocycleOn_add hf1 hg1, isLocConstOn_add hf2 hg2,
      fun A hA => isCoboundaryOn_add (hf3 A hA) (hg3 A hA),
      fun σ hσ => isCoboundaryOn_add (hf4 σ hσ) (hg4 σ hσ)⟩
  smul_mem' := by
    rintro a f ⟨hf1, hf2, hf3, hf4⟩
    exact ⟨isCocycleOn_smul hf1 a, isLocConstOn_smul hf2 a,
      fun A hA => isCoboundaryOn_smul (hf3 A hA) a,
      fun σ hσ => isCoboundaryOn_smul (hf4 σ hσ) a⟩

/-- The locally trivial continuous `2`-cocycles `G_k × G_k → M`. -/
def Z2loc (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {c | SSGRoute.IsCocycle2 (SSGRoute.res k K) c ∧ SSGRoute.IsLocConst2 c ∧
    (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c) ∧
    (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c)}
  zero_mem' := ⟨isCocycle2_zero, isLocConst2_zero, fun _ _ => isCoboundary2On_zero,
    fun _ _ => isCoboundary2On_zero⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3, hf4⟩ ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨isCocycle2_add hf1 hg1, isLocConst2_add hf2 hg2,
      fun A hA => isCoboundary2On_add (hf3 A hA) (hg3 A hA),
      fun σ hσ => isCoboundary2On_add (hf4 σ hσ) (hg4 σ hσ)⟩
  smul_mem' := by
    rintro a f ⟨hf1, hf2, hf3, hf4⟩
    exact ⟨isCocycle2_smul hf1 a, isLocConst2_smul hf2 a,
      fun A hA => isCoboundary2On_smul (hf3 A hA) a,
      fun σ hσ => isCoboundary2On_smul (hf4 σ hσ) a⟩

/-- The continuous `1`-coboundaries `G_k → M`. -/
def B1top (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {φ | SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ φ}
  zero_mem' := isCoboundaryOn_zero
  add_mem' := fun hf hg => isCoboundaryOn_add hf hg
  smul_mem' := fun a f hf => isCoboundaryOn_smul hf a

/-- The continuous `2`-coboundaries `G_k × G_k → M`. -/
def B2top (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {c | SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ c}
  zero_mem' := isCoboundary2On_zero
  add_mem' := fun hf hg => isCoboundary2On_add hf hg
  smul_mem' := fun a f hf => isCoboundary2On_smul hf a

/-- `Ш¹(k,M) = Z¹_loc / B¹`: the first Tate--Shafarevich group of `k` with coefficients in `M`,
for the local conditions (all finite places and all involutions) of the present route. -/
abbrev Sha1 (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] : Type :=
  ↥(Z1loc p k Ω K M) ⧸ (B1top p k Ω K M).comap (Z1loc p k Ω K M).subtype

/-- `Ш²(k,M) = Z²_loc / B²`: the second Tate--Shafarevich group of `k` with coefficients in `M`. -/
abbrev Sha2 (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] : Type :=
  ↥(Z2loc p k Ω K M) ⧸ (B2top p k Ω K M).comap (Z2loc p k Ω K M).subtype

/-- The class in `Ш²(k,E)` of a continuous `2`-cocycle satisfying the local conditions. -/
def sha2Class (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M}
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    Sha2 p k Ω K M :=
  Submodule.Quotient.mk ⟨c, hc, hcc, hloc, hinf⟩

/-- The class in `Ш²(k,E)` of `c` is zero exactly when `c` is a global continuous coboundary. -/
theorem sha2Class_eq_zero_iff (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M}
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    sha2Class p k Ω K M hc hcc hloc hinf = 0 ↔
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ c := by
  unfold sha2Class
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

/-! ## Functoriality of `Ш²` in the coefficient module -/

section Functoriality

variable (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K]

/-- Push-forward of `2`-cochains along an `𝔽_p`-linear map of coefficient modules. -/
def pushC2 (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) :
    ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) →ₗ[ZMod p] ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → N) where
  toFun c := fun σ τ => f (c σ τ)
  map_add' c d := by funext σ τ; exact map_add f (c σ τ) (d σ τ)
  map_smul' a c := by funext σ τ; exact map_smul f a (c σ τ)

@[simp]
theorem pushC2_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (σ τ : Ω ≃ₐ[k] Ω) : pushC2 p k Ω K M N f c σ τ = f (c σ τ) := rfl

/-- The push-forward of a locally trivial `2`-cocycle along a `G`-equivariant map is again
locally trivial. -/
theorem Z2loc_pushC2_mem (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z2loc p k Ω K M) :
    pushC2 p k Ω K M N f c ∈ Z2loc p k Ω K N := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  exact ⟨isCocycle2_push h1 f.toAddMonoidHom hf, isLocConst2_push h2 f.toAddMonoidHom,
    fun A hA => isCoboundary2On_push (h3 A hA) f.toAddMonoidHom hf,
    fun σ hσ => isCoboundary2On_push (h4 σ hσ) f.toAddMonoidHom hf⟩

/-- **Functoriality of `Ш²`** in the coefficient module: push-forward of `2`-cocycles along a
`G`-equivariant `𝔽_p`-linear map `E → E₂`. -/
noncomputable def Sha2Map (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m) :
    Sha2 p k Ω K M →ₗ[ZMod p] Sha2 p k Ω K N :=
  Submodule.mapQ _ _
    (LinearMap.codRestrict (Z2loc p k Ω K N)
      ((pushC2 p k Ω K M N f).comp (Z2loc p k Ω K M).subtype)
      (fun x => Z2loc_pushC2_mem p k Ω K M N f hf x.1 x.2))
    (by
      intro x hx
      have hx' : SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤
          (x : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) := hx
      rw [Submodule.mem_comap, Submodule.mem_comap]
      show SSGRoute.IsCoboundary2On (SSGRoute.res k K) ⊤ (fun σ τ => f (x.1 σ τ))
      exact isCoboundary2On_push hx' f.toAddMonoidHom hf)

/-- The computation of `Sha2Map` on a class: it is the class of the push-forward. -/
theorem Sha2Map_mk (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (x : ↥(Z2loc p k Ω K M)) :
    Sha2Map p k Ω K M N f hf (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨pushC2 p k Ω K M N f x.1, Z2loc_pushC2_mem p k Ω K M N f hf x.1 x.2⟩ :=
  Submodule.mapQ_apply _ _ _ x

/-- `Sha2Map` on the class of a cocycle: the class of the push-forward. -/
theorem Sha2Map_sha2Class (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M}
    (hc : SSGRoute.IsCocycle2 (SSGRoute.res k K) c) (hcc : SSGRoute.IsLocConst2 c)
    (hloc : ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (SSGRoute.decomp k A) c)
    (hinf : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
      SSGRoute.IsCoboundary2On (SSGRoute.res k K) (Subgroup.zpowers σ) c) :
    Sha2Map p k Ω K M N f hf (sha2Class p k Ω K M hc hcc hloc hinf) =
      sha2Class p k Ω K N (isCocycle2_push hc f.toAddMonoidHom hf)
        (isLocConst2_push hcc f.toAddMonoidHom)
        (fun A hA => isCoboundary2On_push (hloc A hA) f.toAddMonoidHom hf)
        (fun σ hσ => isCoboundary2On_push (hinf σ hσ) f.toAddMonoidHom hf) := by
  unfold sha2Class
  rw [Sha2Map_mk]
  congr 1

end Functoriality

/-! ## Functoriality of `Ш¹` in the coefficient module -/

section FunctorialityOne

variable (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K]

/-- Push-forward of `1`-cochains along an `𝔽_p`-linear map of coefficient modules. -/
def pushC1 (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) : ((Ω ≃ₐ[k] Ω) → M) →ₗ[ZMod p] ((Ω ≃ₐ[k] Ω) → N) where
  toFun c := fun σ => f (c σ)
  map_add' c d := by funext σ; exact map_add f (c σ) (d σ)
  map_smul' a c := by funext σ; exact map_smul f a (c σ)

@[simp]
theorem pushC1_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (c : (Ω ≃ₐ[k] Ω) → M) (σ : Ω ≃ₐ[k] Ω) :
    pushC1 p k Ω K M N f c σ = f (c σ) := rfl

/-- The push-forward of a locally trivial continuous `1`-cocycle along a `G`-equivariant map is
again locally trivial. -/
theorem Z1loc_pushC1_mem (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (c : (Ω ≃ₐ[k] Ω) → M) (hc : c ∈ Z1loc p k Ω K M) :
    pushC1 p k Ω K M N f c ∈ Z1loc p k Ω K N := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  exact ⟨isCocycleOn_push h1 f.toAddMonoidHom hf, isLocConstOn_push h2 f,
    fun A hA => isCoboundaryOn_push (h3 A hA) f.toAddMonoidHom hf,
    fun σ hσ => isCoboundaryOn_push (h4 σ hσ) f.toAddMonoidHom hf⟩

/-- **Functoriality of `Ш¹`** in the coefficient module. -/
noncomputable def Sha1Map (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m) :
    Sha1 p k Ω K M →ₗ[ZMod p] Sha1 p k Ω K N :=
  Submodule.mapQ _ _
    (LinearMap.codRestrict (Z1loc p k Ω K N)
      ((pushC1 p k Ω K M N f).comp (Z1loc p k Ω K M).subtype)
      (fun x => Z1loc_pushC1_mem p k Ω K M N f hf x.1 x.2))
    (by
      intro x hx
      have hx' : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤
          (x : (Ω ≃ₐ[k] Ω) → M) := hx
      rw [Submodule.mem_comap, Submodule.mem_comap]
      show SSGRoute.IsCoboundaryOn (SSGRoute.res k K) ⊤ (fun σ => f (x.1 σ))
      exact isCoboundaryOn_push hx' f.toAddMonoidHom hf)

/-- The computation of `Sha1Map` on a class: it is the class of the push-forward. -/
theorem Sha1Map_mk (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction (K ≃ₐ[k] K) N]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N]
    (f : M →ₗ[ZMod p] N) (hf : ∀ (g : K ≃ₐ[k] K) (m : M), f (g • m) = g • f m)
    (x : ↥(Z1loc p k Ω K M)) :
    Sha1Map p k Ω K M N f hf (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨pushC1 p k Ω K M N f x.1, Z1loc_pushC1_mem p k Ω K M N f hf x.1 x.2⟩ :=
  Submodule.mapQ_apply _ _ _ x

end FunctorialityOne

end Work.SSGRoute
