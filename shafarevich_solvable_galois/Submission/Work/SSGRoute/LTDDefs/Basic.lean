import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local cohomology of decomposition groups: the vocabulary of local Tate duality

Support file for `Work.SSGRoute.local_tate_duality`.  It defines the locally constant cohomology
`H⁰`, `H¹`, `H²` of a decomposition group `D_A = decomp k A ⊆ G_k = Ω ≃ₐ[k] Ω` with coefficients
in a finite `𝔽_p[Gal(K/k)]`-module, together with

* `toClass`, the class map from all cochains, which turns an additive function of cochains into a
  pairing of local `H¹`-groups;
* `exists_perfect_pairing`, the linear algebra of a perfect pairing between two finite
  `𝔽_p`-vector spaces of the same dimension;
* `HasPerfectLocalPairing`, the per-place perfect-pairing statement that the arithmetic inputs
  (`Work.SSGRoute.LTDDefs.Euler`, `Work.SSGRoute.LTDDefs.Deg02`) establish.

Nothing here is arithmetic: it is the interface used by the arithmetic lemmas.
-/

open scoped TensorProduct Pointwise
open Classical

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The locally constant `1`-cocycles on `H ≤ G_k` with values in a `Gal(K/k)`-module `M`,
regarded as an `𝔽_p`-submodule of the module of all functions `G_k → M`. -/
def lcCocycles (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {f | SSGRoute.IsCocycleOn (SSGRoute.res k K) H f ∧ SSGRoute.IsLocConstOn H f}
  zero_mem' := ⟨fun g _ h _ => by simp, ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    obtain ⟨U1, hU1o, hU1⟩ := hf2
    obtain ⟨U2, hU2o, hU2⟩ := hg2
    refine ⟨?_, U1 ⊓ U2, ?_, ?_⟩
    · intro a ha b hb
      simp only [Pi.add_apply, hf1 a ha b hb, hg1 a ha b hb, smul_add]
      abel
    · rw [Subgroup.coe_inf]; exact hU1o.inter hU2o
    · intro a ha u hu huH
      have h1 : u ∈ U1 := (Subgroup.mem_inf.mp hu).1
      have h2 : u ∈ U2 := (Subgroup.mem_inf.mp hu).2
      simp only [Pi.add_apply, hU1 a ha u h1 huH, hU2 a ha u h2 huH]
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    obtain ⟨U, hUo, hU⟩ := hf2
    refine ⟨?_, U, hUo, ?_⟩
    · intro a ha b hb
      simp only [Pi.smul_apply, hf1 a ha b hb, smul_add]
      rw [smul_comm (SSGRoute.res k K a) c (f b)]
    · intro a ha u hu huH
      simp only [Pi.smul_apply, hU a ha u hu huH]

/-- The `1`-coboundaries on `H` with values in `M`, as a `𝔽_p`-submodule of the functions. -/
def coboundaries (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {f | SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f}
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
    rw [smul_comm (SSGRoute.res k K x) c m]

/-- **The local `H¹`**: locally constant `1`-cocycles modulo coboundaries; this is the continuous
cohomology `H¹_cont(D_A, M)` of the decomposition group `D_A = decomp k A`. -/
abbrev H1loc (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Type :=
  ↥(lcCocycles p k Ω K M H) ⧸ (Submodule.comap (lcCocycles p k Ω K M H).subtype
    (coboundaries p k Ω K M H))

@[simp] theorem mem_lcCocycles (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (f : (Ω ≃ₐ[k] Ω) → M) :
    f ∈ lcCocycles p k Ω K M H ↔
      SSGRoute.IsCocycleOn (SSGRoute.res k K) H f ∧ SSGRoute.IsLocConstOn H f := Iff.rfl

@[simp] theorem mem_coboundaries (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (f : (Ω ≃ₐ[k] Ω) → M) :
    f ∈ coboundaries p k Ω K M H ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H f := Iff.rfl

/-- A coboundary is a locally constant cocycle. -/
theorem coboundaries_le_lcCocycles (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    coboundaries p k Ω K M H ≤ lcCocycles p k Ω K M H := by
  intro f hf
  obtain ⟨m, hm⟩ := hf
  refine ⟨?_, ?_⟩
  · intro g hg h hh
    rw [hm (g * h) (mul_mem hg hh), hm g hg, hm h hh, map_mul, mul_smul, smul_sub]
    abel
  · refine ⟨(SSGRoute.res k K).ker, ?_, ?_⟩
    · have h : (SSGRoute.res k K).ker = K.fixingSubgroup :=
        IntermediateField.restrictNormalHom_ker (E := K)
      rw [h]
      exact IntermediateField.fixingSubgroup_isOpen K
    · intro g hg u hu huH
      rw [hm (g * u) (mul_mem hg huH), hm g hg, map_mul, MonoidHom.mem_ker.mp hu, mul_one]

/-- The class of `f` in the local `H¹`; `0` if `f` is not a locally constant cocycle.  This is
the map through which the local Tate pairing is defined on all cochains. -/
def toClass (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (f : (Ω ≃ₐ[k] Ω) → M) : H1loc p k Ω K M H :=
  if hf : f ∈ lcCocycles p k Ω K M H then
    Submodule.mkQ (Submodule.comap (lcCocycles p k Ω K M H).subtype (coboundaries p k Ω K M H))
      ⟨f, hf⟩ else 0

theorem toClass_add (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) {f f' : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ lcCocycles p k Ω K M H) (hf' : f' ∈ lcCocycles p k Ω K M H) :
    toClass p k Ω K M H (f + f') = toClass p k Ω K M H f + toClass p k Ω K M H f' := by
  rw [toClass, dif_pos (add_mem hf hf'), toClass, dif_pos hf, toClass, dif_pos hf', ← map_add]
  exact congrArg _ (Subtype.ext rfl)

theorem toClass_eq_zero_iff (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ lcCocycles p k Ω K M H) :
    toClass p k Ω K M H f = 0 ↔ f ∈ coboundaries p k Ω K M H := by
  rw [toClass, dif_pos hf, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.mem_comap

theorem toClass_surjective (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (y : H1loc p k Ω K M H) :
    ∃ g ∈ lcCocycles p k Ω K M H, toClass p k Ω K M H g = y := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (p := Submodule.comap
    (lcCocycles p k Ω K M H).subtype (coboundaries p k Ω K M H)) y
  exact ⟨x.1, x.2, by rw [toClass, dif_pos x.2]; rfl⟩

end

end Work.SSGRoute

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-! ## The higher locally constant cohomology -/

/-- The `0`-th local cohomology `H⁰(D_A, M) = M^{D_A}`. -/
def H0loc (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) M where
  carrier := {m | ∀ g ∈ H, SSGRoute.res k K g • m = m}
  zero_mem' := fun g _ => by simp
  add_mem' := by
    rintro m n hm hn g hg
    rw [smul_add, hm g hg, hn g hg]
  smul_mem' := by
    rintro c m hm g hg
    rw [smul_comm (SSGRoute.res k K g) c m, hm g hg]

/-- `c` is an inhomogeneous `2`-cocycle on `H` (the cocycle condition is imposed only on `H`). -/
def IsCocycle2On (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ l ∈ H,
    SSGRoute.res k K g • c h l - c (g * h) l + c g (h * l) - c g h = 0

/-- `c` is locally constant on `H × H`. -/
def IsLocConst2On (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) : Prop :=
  ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
    ∀ g ∈ H, ∀ h ∈ H, ∀ u ∈ U, ∀ v ∈ U, u ∈ H → v ∈ H → c (g * u) (h * v) = c g h

/-- The locally constant `2`-cocycles on `H`. -/
def lcCocycles2 (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {c | IsCocycle2On p k Ω K M H c ∧ IsLocConst2On p k Ω K M H c}
  zero_mem' := ⟨fun g _ h _ l _ => by simp, ⟨⊤, isOpen_univ, fun g _ h _ u _ v _ _ _ => rfl⟩⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨?_, ?_⟩
    · intro a ha b hb d hd
      have h1 := hf1 a ha b hb d hd
      have h2 := hg1 a ha b hb d hd
      have key : SSGRoute.res k K a • (f + g) b d - (f + g) (a * b) d + (f + g) a (b * d)
            - (f + g) a b
          = (SSGRoute.res k K a • f b d - f (a * b) d + f a (b * d) - f a b)
            + (SSGRoute.res k K a • g b d - g (a * b) d + g a (b * d) - g a b) := by
        simp only [Pi.add_apply, smul_add]; abel
      have hsum : (SSGRoute.res k K a • f b d - f (a * b) d + f a (b * d) - f a b)
            + (SSGRoute.res k K a • g b d - g (a * b) d + g a (b * d) - g a b) = 0 := by
        rw [h1, h2]; abel
      rw [key, hsum]
    · obtain ⟨U1, ho1, hU1⟩ := hf2
      obtain ⟨U2, ho2, hU2⟩ := hg2
      refine ⟨U1 ⊓ U2, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact ho1.inter ho2
      · intro a ha b hb u hu v hv huH hvH
        have h1 : u ∈ U1 := (Subgroup.mem_inf.mp hu).1
        have h2 : v ∈ U1 := (Subgroup.mem_inf.mp hv).1
        have h3 : u ∈ U2 := (Subgroup.mem_inf.mp hu).2
        have h4 : v ∈ U2 := (Subgroup.mem_inf.mp hv).2
        simp only [Pi.add_apply, hU1 a ha b hb u h1 v h2 huH hvH,
          hU2 a ha b hb u h3 v h4 huH hvH]
  smul_mem' := by
    rintro r c ⟨hc1, hc2⟩
    refine ⟨?_, ?_⟩
    · intro a ha b hb d hd
      have h1 := hc1 a ha b hb d hd
      have key : SSGRoute.res k K a • (r • c) b d - (r • c) (a * b) d + (r • c) a (b * d)
            - (r • c) a b
          = r • (SSGRoute.res k K a • c b d - c (a * b) d + c a (b * d) - c a b) := by
        simp only [Pi.smul_apply, smul_sub, smul_add]
        rw [← smul_comm (SSGRoute.res k K a) r (c b d)]
      rw [key, h1, smul_zero]
    · obtain ⟨U, ho, hU⟩ := hc2
      exact ⟨U, ho, fun a ha b hb u hu v hv huH hvH => by
        simp only [Pi.smul_apply, hU a ha b hb u hu v hv huH hvH]⟩

/-- The locally constant `2`-coboundaries on `H`. -/
def coboundaries2 (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {c | SSGRoute.IsCoboundary2On (SSGRoute.res k K) H c}
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
      rw [← smul_comm (SSGRoute.res k K a) r (β b)]

/-- The `2`-nd local cohomology `H²(D_A, M)`. -/
abbrev H2loc (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Type :=
  ↥(lcCocycles2 p k Ω K M H) ⧸ (Submodule.comap (lcCocycles2 p k Ω K M H).subtype
    (coboundaries2 p k Ω K M H))

end

end Work.SSGRoute

namespace Work.SSGRoute

noncomputable section

open scoped TensorProduct

/-- Two finite `𝔽_p`-vector spaces of the same dimension admit a pairing with trivial kernel in
each variable. -/
theorem exists_perfect_pairing (p : ℕ) [Fact p.Prime] (V W : Type)
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] [Module.Finite (ZMod p) W]
    (h : Module.finrank (ZMod p) V = Module.finrank (ZMod p) W) :
    ∃ Φ : V →ₗ[ZMod p] W →ₗ[ZMod p] ZMod p,
      (∀ x, (∀ y, Φ x y = 0) → x = 0) ∧ (∀ y, (∀ x, Φ x y = 0) → y = 0) := by
  have hd : Module.finrank (ZMod p) V = Module.finrank (ZMod p) (Module.Dual (ZMod p) W) := by
    rw [Subspace.dual_finrank_eq]; exact h
  refine ⟨(LinearEquiv.ofFinrankEq V (Module.Dual (ZMod p) W) hd).toLinearMap, ?_, ?_⟩
  · intro v hv
    have h0 : (LinearEquiv.ofFinrankEq V (Module.Dual (ZMod p) W) hd) v = 0 := LinearMap.ext hv
    exact (LinearEquiv.ofFinrankEq V (Module.Dual (ZMod p) W) hd).injective (by rw [h0, map_zero])
  · intro w hw
    have hφ : ∀ φ : Module.Dual (ZMod p) W, φ w = 0 := by
      intro φ
      obtain ⟨v, rfl⟩ := (LinearEquiv.ofFinrankEq V (Module.Dual (ZMod p) W) hd).surjective φ
      exact hw v
    have h0 : (Module.evalEquiv (ZMod p) W) w = 0 := by
      rw [Module.evalEquiv_apply]
      ext φ
      rw [Module.Dual.eval_apply]
      simpa using hφ φ
    exact (Module.evalEquiv (ZMod p) W).injective (by rw [h0, map_zero])


/-! ## Elementary finiteness and dimension facts for the coefficient modules -/

section Modules

variable {p : ℕ} [Fact p.Prime]

/-- A rank-one `𝔽_p`-module is finite. -/
theorem finite_of_finrank_eq_one (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    (h : Module.finrank (ZMod p) T = 1) : Finite T := by
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one h
  exact Finite.of_injective e.symm e.symm.injective

/-- The tensor product of two finite `𝔽_p`-modules is finite. -/
theorem finite_tensor (M T : Type) [AddCommGroup M] [Module (ZMod p) M] [Finite M]
    [AddCommGroup T] [Module (ZMod p) T] [Finite T] : Finite (M ⊗[ZMod p] T) := by
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) T := Module.Finite.of_finite
  haveI : Module.Finite (ZMod p) (M ⊗[ZMod p] T) := Module.Finite.tensorProduct _ _ _
  haveI : Module.Free (ZMod p) (M ⊗[ZMod p] T) := inferInstance
  let b := Module.finBasis (ZMod p) (M ⊗[ZMod p] T)
  exact Finite.of_injective b.repr b.repr.injective

/-- The `𝔽_p`-linear dual of a finite module is finite. -/
theorem finite_dualMod (X : Type) [AddCommGroup X] [Module (ZMod p) X] [Finite X] :
    Finite (DualMod p X) := by
  haveI : Finite (X → ZMod p) := inferInstance
  exact Finite.of_injective (fun f : DualMod p X => (f : X → ZMod p))
    (fun a b h => LinearMap.ext (congrFun h))

/-- The `𝔽_p`-dual has the same dimension. -/
theorem finrank_dualMod (X : Type) [AddCommGroup X] [Module (ZMod p) X] :
    Module.finrank (ZMod p) (DualMod p X) = Module.finrank (ZMod p) X :=
  Subspace.dual_finrank_eq

/-- Tensoring with a rank-one module does not change the dimension. -/
theorem finrank_tensor_rankOne (M T : Type) [AddCommGroup M] [Module (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] (h : Module.finrank (ZMod p) T = 1) :
    Module.finrank (ZMod p) (M ⊗[ZMod p] T) = Module.finrank (ZMod p) M := by
  rw [Module.finrank_tensorProduct, h, mul_one]

end Modules

end

end Work.SSGRoute

namespace Work.SSGRoute

noncomputable section

open scoped TensorProduct

