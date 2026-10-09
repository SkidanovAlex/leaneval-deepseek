import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ext_idele_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

/-!
# The level decomposition in all degrees (E2, induction step)

Given the degree-`0` level decomposition `thetaL k K R M 0 S` (the hypothesis `h0`), this file
derives the decomposition in **all** degrees by the standard dimension shift: for an arbitrary
representation `M` one takes a free cover `p : F ↠ M` with kernel `K`, uses the long exact sequences
in the first variable of the two sides (source: `Ext^•_G(-, lvl S)`, target: the product over the
transversal of `Ext^•_{D_w}(res_w -, B_w^S)`), and the fact that both sides vanish on the projective
`F` (and on `res_w F`) in positive degrees.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

noncomputable section

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- The target of `thetaL`: the product over the transversal `R` of the local `Ext`-groups. -/
def Tgt (R : Set (NK.GlobalCFT.Place K)) (S : NK.HassePrinciple.GStableSet k K)
    (N : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (n : ℕ) : Type :=
  (w : R) → Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype N) (BOf k K w.1 S) n

/-- The pointwise additive group structure on `Tgt`, stated explicitly. On Lean v4.35, with `Tgt`
an `abbrev`, instance search went through `Pi.addGroup` and had to find `HasExt` under the binder
`w` (unfolded to `∀ X Y a b, Localization.HasSmallLocalizedHom …`), which took tens of CPU-minutes;
`Tgt` is therefore a `def` (same value) and this is its only additive-group instance. -/
instance instAddCommGroupTgt (R : Set (NK.GlobalCFT.Place K))
    (S : NK.HassePrinciple.GStableSet k K) (N : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (n : ℕ) :
    AddCommGroup (Tgt k K R S N n) :=
  @Pi.addCommGroup R (fun w => Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype N)
    (BOf k K w.1 S) n) (fun _ => inferInstance)

/-- The restriction of a short complex along the decomposition group `D_w`, built by hand so that
its objects reduce definitionally to `res_w Xᵢ`. -/
abbrev resShortComplex (w : NK.GlobalCFT.Place K)
    (Sc : ShortComplex (Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))) :
    ShortComplex (Rep.{0, 0, 0} Coeff (decompK (k := k) w)) :=
  ShortComplex.mk (Rep.resMap (decompK (k := k) w).subtype Sc.f)
    (Rep.resMap (decompK (k := k) w).subtype Sc.g)
    (Sc.map (Rep.resFunctor (decompK (k := k) w).subtype)).zero

/-- `resShortComplex` is short exact when `Sc` is. -/
theorem resShortComplex_shortExact (w : NK.GlobalCFT.Place K)
    {Sc : ShortComplex (Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))} (hSc : Sc.ShortExact) :
    (resShortComplex k K w Sc).ShortExact :=
  show (resShortComplex k K w Sc).ShortExact from
    hSc.map_of_exact (Rep.resFunctor (decompK (k := k) w).subtype)

/-- **Naturality of `thetaL` in the source variable.** -/
theorem thetaL_naturality (R : Set (NK.GlobalCFT.Place K))
    (M M' : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (f : M' ⟶ M) (r : ℕ)
    (S : NK.HassePrinciple.GStableSet k K) (x : Abelian.Ext M (lvl k K S) r) :
    thetaL k K R M' r S ((Abelian.Ext.mk₀ f).comp x (zero_add r))
      = fun w => (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w.1).subtype f)).comp
          (thetaL k K R M r S x w) (zero_add r) := by
  funext w
  simp only [thetaL, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- **Compatibility of `thetaL` with the connecting map of a short exact sequence.** -/
theorem thetaL_extClass (R : Set (NK.GlobalCFT.Place K))
    {Sc : ShortComplex (Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))} (hSc : Sc.ShortExact)
    (S : NK.HassePrinciple.GStableSet k K) {n₀ : ℕ}
    (x : Abelian.Ext Sc.X₁ (lvl k K S) n₀) {n₁ : ℕ} (h : 1 + n₀ = n₁) :
    thetaL k K R Sc.X₃ n₁ S (hSc.extClass.comp x h)
      = fun w => (hSc.map_of_exact
          (Rep.resFunctor (decompK (k := k) w.1).subtype)).extClass.comp
          (thetaL k K R Sc.X₁ n₀ S x w) h := by
  funext w
  simp only [thetaL, extRes, Abelian.Ext.mapExactFunctor_comp]
  rw [Abelian.Ext.mapExactFunctor_extClass]
  exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ h

/-- **Additivity of `thetaL` in the source variable.** -/
theorem thetaL_add (R : Set (NK.GlobalCFT.Place K))
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (r : ℕ) (S : NK.HassePrinciple.GStableSet k K)
    (x y : Abelian.Ext M (lvl k K S) r) :
    thetaL k K R M r S (x + y)
      = thetaL k K R M r S x + thetaL k K R M r S y := by
  funext w
  simp only [thetaL, extRes, Pi.add_apply]
  rw [Abelian.Ext.mapExactFunctor_add, Abelian.Ext.add_comp]

/-- `thetaL` as an additive homomorphism. -/
def thetaLHom (R : Set (NK.GlobalCFT.Place K))
    (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (r : ℕ) (S : NK.HassePrinciple.GStableSet k K) :
    Abelian.Ext M (lvl k K S) r →+ Tgt k K R S M r :=
  AddMonoidHom.mk' (thetaL k K R M r S) (fun x y => thetaL_add k K R M r S x y)

/-- The restriction of a projective representation is projective. -/
theorem projective_res (w : NK.GlobalCFT.Place K) {X : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)}
    [Projective X] : Projective (Rep.res (decompK (k := k) w).subtype X) := by
  haveI : (Rep.resFunctor (k := Coeff) (G := K ≃ₐ[k] K) (H := decompK (k := k) w)
      (decompK (k := k) w).subtype).PreservesProjectiveObjects := inferInstance
  exact Functor.projective_obj _ _

/-- Every representation admits a surjection from a free (hence projective) representation. -/
theorem free_cover (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) :
    ∃ (F : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) (p : F ⟶ M), Projective F ∧ Epi p := by
  refine ⟨Rep.free Coeff (K ≃ₐ[k] K) M.V,
    Rep.freeLift (k := Coeff) (G := K ≃ₐ[k] K) M (id : M.V → M.V), inferInstance, ?_⟩
  rw [Rep.epi_iff_surjective]
  intro m
  refine ⟨Finsupp.single m (MonoidAlgebra.single 1 1), ?_⟩
  show Representation.freeLift M.ρ (id : M.V → M.V)
    (Finsupp.single m (MonoidAlgebra.single 1 1)) = m
  rw [Representation.freeLift_single_single]
  simp

/-- A commuting diagram of sets with an isomorphism `f'` from `A` forces `g` to be bijective. -/
theorem bijective_of_comp_comm {A B C A' : Type*}
    (f : A → B) (g : B → C) (f' : A → A') (g' : A' → C)
    (hf : Function.Bijective f) (hf' : Function.Bijective f') (hg' : Function.Bijective g')
    (h : ∀ a, g (f a) = g' (f' a)) : Function.Bijective g := by
  constructor
  · intro b₁ b₂ hb
    obtain ⟨a₁, rfl⟩ := hf.2 b₁
    obtain ⟨a₂, rfl⟩ := hf.2 b₂
    rw [h a₁, h a₂] at hb
    rw [hf'.1 (hg'.1 hb)]
  · intro c
    obtain ⟨b', hb'⟩ := hg'.2 c
    obtain ⟨a, ha⟩ := hf'.2 b'
    exact ⟨f a, by rw [h a, ha, hb']⟩

/-- The pointwise bijectivity of a family of maps gives the bijectivity of the induced map on
dependent functions. -/
theorem bijective_pi {ι : Type*} {A B : ι → Type*} {f : ∀ i, A i → B i}
    (h : ∀ i, Function.Bijective (f i)) :
    Function.Bijective (fun (g : ∀ i, A i) => fun i => f i (g i)) := by
  constructor
  · intro g g' hgg
    funext i
    exact (h i).1 (congrFun hgg i)
  · intro g'
    choose g hg using fun i => (h i).2 (g' i)
    exact ⟨g, funext hg⟩

/-- The right-hand half of the short five lemma: a morphism of two `3`-term exact sequences with
surjective right maps, an isomorphism on the middle terms and an isomorphism `f'` on the left
inputs, is an isomorphism on the right ends. -/
theorem bijective_of_exact_square {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (f : A →+ B) (g : B →+ C) (f' : A' →+ B') (g' : B' →+ C')
    (θA : A →+ A') (θB : B →+ B') (θC : C →+ C')
    (hex : Function.Exact f g) (hex' : Function.Exact f' g')
    (hsurj : Function.Surjective g) (hsurj' : Function.Surjective g')
    (hA : Function.Bijective θA) (hB : Function.Bijective θB)
    (hcomm : ∀ a, θB (f a) = f' (θA a))
    (hcommC : ∀ b, θC (g b) = g' (θB b)) :
    Function.Bijective θC := by
  constructor
  · intro c₁ c₂ hcc
    have hker : θC (c₁ - c₂) = 0 := by rw [map_sub, hcc, sub_self]
    have hzero : c₁ - c₂ = 0 := by
      obtain ⟨b, hb⟩ := hsurj (c₁ - c₂)
      have h₁ : g' (θB b) = 0 := by rw [← hcommC b, hb, hker]
      obtain ⟨a', ha'⟩ := Set.mem_range.mp ((hex' (θB b)).mp h₁)
      obtain ⟨a, ha⟩ := hA.2 a'
      have h₂ : θB (f a) = θB b := by rw [hcomm a, ha, ha']
      have h₃ : f a = b := hB.1 h₂
      have h₄ : g b = 0 := by
        rw [← h₃]
        exact (hex (f a)).mpr (Set.mem_range.mpr ⟨a, rfl⟩)
      rw [← hb, h₄]
    exact sub_eq_zero.mp hzero
  · intro c'
    obtain ⟨b', hb'⟩ := hsurj' c'
    obtain ⟨b, hb⟩ := hB.2 b'
    exact ⟨g b, by rw [hcommC b, hb, hb']⟩

/-- Exactness of the sequence `Ext⁰(X₂) → Ext⁰(X₁) → Ext¹(X₃)` coming from a short exact
sequence. -/
theorem exact_mk0_extClass {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C) {n₀ n₁ : ℕ} (h : 1 + n₀ = n₁) :
    Function.Exact (fun y : Abelian.Ext S.X₂ Y n₀ => (Abelian.Ext.mk₀ S.f).comp y (zero_add n₀))
      (fun x : Abelian.Ext S.X₁ Y n₀ => hS.extClass.comp x h) := by
  intro x
  rw [Set.mem_range]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y x h hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact ShortComplex.ShortExact.extClass_comp_assoc hS y (h := h)

/-- The connecting map of a short exact sequence with projective middle term is surjective. -/
theorem surjective_extClass {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C) [Projective S.X₂]
    {n₀ n₁ : ℕ} (h : 1 + n₀ = n₁) :
    Function.Surjective (fun x : Abelian.Ext S.X₁ Y n₀ => hS.extClass.comp x h) := by
  haveI : Subsingleton (Abelian.Ext S.X₂ Y n₁) :=
    (show n₀ + 1 = n₁ by omega) ▸ (Abelian.Ext.subsingleton_of_projective S.X₂ Y n₀)
  intro z
  exact Abelian.Ext.contravariant_sequence_exact₃ hS Y z (Subsingleton.elim _ _) h

/-- The connecting map of a short exact sequence is injective when the middle term is
projective and the source degree is positive. -/
theorem injective_extClass_of_subsingleton {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : C) {n₀ n₁ : ℕ} (h : 1 + n₀ = n₁)
    [Subsingleton (Abelian.Ext S.X₂ Y n₀)] :
    Function.Injective (fun x : Abelian.Ext S.X₁ Y n₀ => hS.extClass.comp x h) := by
  intro x y hxy
  have hzero : hS.extClass.comp (x - y) h = 0 := by
    have hxy' : hS.extClass.comp x h = hS.extClass.comp y h := hxy
    rw [sub_eq_add_neg, Abelian.Ext.comp_add, Abelian.Ext.comp_neg, hxy', add_neg_cancel]
  obtain ⟨z, hz⟩ := Set.mem_range.mp ((exact_mk0_extClass hS Y h (x - y)).mp hzero)
  have hz0 : z = 0 := Subsingleton.elim z 0
  have hz1 : (Abelian.Ext.mk₀ S.f).comp (0 : Abelian.Ext S.X₂ Y n₀) (zero_add n₀) = 0 := by simp
  rw [hz0, hz1] at hz
  exact sub_eq_zero.mp hz.symm

/-! ## The main theorem -/

theorem level_decomp_step (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (h0 : ∀ (M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
      (S : NK.HassePrinciple.GStableSet k K),
      S.carrier.Finite → Function.Bijective (Work.SSGRoute.thetaL k K R M 0 S))
    (M : Rep.{0, 0, 0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (r : ℕ)
    (S : NK.HassePrinciple.GStableSet k K) (hS : S.carrier.Finite) :
    Function.Bijective (Work.SSGRoute.thetaL k K R M r S) := by
  suffices H : ∀ r : ℕ, ∀ (M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K))
      (S : NK.HassePrinciple.GStableSet k K),
      S.carrier.Finite → Function.Bijective (thetaL k K R M r S) from H r M S hS
  intro r
  induction r with
  | zero => exact h0
  | succ r ih =>
    intro M S hS
    -- a free cover of `M`, with kernel `K'`
    let F : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K) := Rep.free Coeff (K ≃ₐ[k] K) M.V
    let p : F ⟶ M := Rep.freeLift (k := Coeff) (G := K ≃ₐ[k] K) M (id : M.V → M.V)
    haveI hprojF : Projective F := inferInstance
    have hp : Epi p := by
      rw [Rep.epi_iff_surjective]
      intro m
      refine ⟨Finsupp.single m (MonoidAlgebra.single 1 1), ?_⟩
      show Representation.freeLift M.ρ (id : M.V → M.V)
        (Finsupp.single m (MonoidAlgebra.single 1 1)) = m
      rw [Representation.freeLift_single_single]
      simp
    let K' : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K) := Limits.kernel p
    let i : K' ⟶ F := Limits.kernel.ι p
    let Sc : ShortComplex (Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)) :=
      ShortComplex.mk i p (Limits.kernel.condition p)
    have hSc : Sc.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel Sc (CategoryTheory.Limits.kernelIsKernel p) }
    -- projectivity of the local middle terms
    have hprojW : ∀ w : R, Projective (resShortComplex k K w.1 Sc).X₂ := fun w =>
      projective_res k K (X := Sc.X₂) w.1
    by_cases hr0 : r = 0
    · -- ## Low degree: `r = 0`, so the target degree is `1`
      subst hr0
      have h1 : 1 + 0 = 1 := by omega
      -- source side
      let eS : Abelian.Ext F (lvl k K S) 0 →+ Abelian.Ext K' (lvl k K S) 0 :=
        AddMonoidHom.mk' (fun y => (Abelian.Ext.mk₀ i).comp y (zero_add 0))
          (fun a b => by rw [Abelian.Ext.comp_add])
      let dS : Abelian.Ext K' (lvl k K S) 0 →+ Abelian.Ext M (lvl k K S) 1 :=
        AddMonoidHom.mk' (fun x => hSc.extClass.comp x h1)
          (fun a b => by rw [Abelian.Ext.comp_add])
      have hexS : Function.Exact eS dS := exact_mk0_extClass hSc (lvl k K S) h1
      have hsurjS : Function.Surjective dS := surjective_extClass hSc (lvl k K S) (h := h1)
      -- target side, locally
      let eTw : ∀ w : R, Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype F)
          (BOf k K w.1 S) 0 →+ Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype K')
          (BOf k K w.1 S) 0 := fun w =>
        AddMonoidHom.mk' (fun y => (Abelian.Ext.mk₀ (resShortComplex k K w.1 Sc).f).comp y
            (zero_add 0)) (fun a b => by rw [Abelian.Ext.comp_add])
      let dTw : ∀ w : R, Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype K')
          (BOf k K w.1 S) 0 →+ Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype M)
          (BOf k K w.1 S) 1 := fun w =>
        AddMonoidHom.mk' (fun x => (resShortComplex_shortExact k K w.1 hSc).extClass.comp x h1)
          (fun a b => by rw [Abelian.Ext.comp_add])
      have hexTw : ∀ w : R, Function.Exact (eTw w) (dTw w) := fun w =>
        exact_mk0_extClass (resShortComplex_shortExact k K w.1 hSc) (BOf k K w.1 S) h1
      have hsurjTw : ∀ w : R, Function.Surjective (dTw w) := fun w =>
        surjective_extClass (resShortComplex_shortExact k K w.1 hSc) (BOf k K w.1 S) (h := h1)
      let eT : Tgt k K R S F 0 →+ Tgt k K R S K' 0 :=
        AddMonoidHom.mk' (fun z => fun w => eTw w (z w))
          (fun a b => by funext w; exact map_add (eTw w) (a w) (b w))
      let dT : Tgt k K R S K' 0 →+ Tgt k K R S M 1 :=
        AddMonoidHom.mk' (fun c => fun w => dTw w (c w))
          (fun a b => by funext w; exact map_add (dTw w) (a w) (b w))
      have hexT : Function.Exact eT dT := by
        intro c
        rw [Set.mem_range]
        constructor
        · intro hc
          have hpt : ∀ w : R, ∃ z : Abelian.Ext
              (Rep.res (decompK (k := k) w.1).subtype F) (BOf k K w.1 S) 0,
              eTw w z = c w := by
            intro w
            have hw : dTw w (c w) = 0 := congrFun hc w
            exact Set.mem_range.mp ((hexTw w (c w)).mp hw)
          choose z hz using hpt
          exact ⟨z, funext hz⟩
        · rintro ⟨z, rfl⟩
          funext w
          exact (hexTw w (eTw w (z w))).mpr (Set.mem_range.mpr ⟨z w, rfl⟩)
      have hsurjT : Function.Surjective dT := by
        intro c
        choose z hz using fun w : R => hsurjTw w (c w)
        exact ⟨z, funext hz⟩
      -- the two commuting squares
      have hcomm : ∀ a, thetaLHom k K R K' 0 S (eS a) = eT (thetaLHom k K R F 0 S a) :=
        fun a => thetaL_naturality k K R F K' i 0 S a
      have hcommC : ∀ b, thetaLHom k K R M 1 S (dS b) = dT (thetaLHom k K R K' 0 S b) :=
        fun b => thetaL_extClass k K R hSc S b h1
      exact bijective_of_exact_square eS dS eT dT
        (thetaLHom k K R F 0 S) (thetaLHom k K R K' 0 S) (thetaLHom k K R M 1 S)
        hexS hexT hsurjS hsurjT (ih F S hS) (ih K' S hS) hcomm hcommC
    · -- ## High degree: `r = r' + 1 ≥ 1`, so the target degree is `r + 1 ≥ 2`
      obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr0
      have h1 : 1 + (r' + 1) = (r' + 1) + 1 := by omega
      let eS : Abelian.Ext F (lvl k K S) (r' + 1) →+ Abelian.Ext K' (lvl k K S) (r' + 1) :=
        AddMonoidHom.mk' (fun y => (Abelian.Ext.mk₀ i).comp y (zero_add (r' + 1)))
          (fun a b => by rw [Abelian.Ext.comp_add])
      let dS : Abelian.Ext K' (lvl k K S) (r' + 1) →+
          Abelian.Ext M (lvl k K S) ((r' + 1) + 1) :=
        AddMonoidHom.mk' (fun x => hSc.extClass.comp x h1)
          (fun a b => by rw [Abelian.Ext.comp_add])
      have hsurjS : Function.Surjective dS := surjective_extClass hSc (lvl k K S) (h := h1)
      haveI hsubF : Subsingleton (Abelian.Ext Sc.X₂ (lvl k K S) (r' + 1)) :=
        Abelian.Ext.subsingleton_of_projective Sc.X₂ (lvl k K S) r'
      have hinjS : Function.Injective dS :=
        injective_extClass_of_subsingleton hSc (lvl k K S) h1
      -- target side, locally
      let dTw : ∀ w : R, Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype K')
          (BOf k K w.1 S) (r' + 1) →+ Abelian.Ext (Rep.res (decompK (k := k) w.1).subtype M)
          (BOf k K w.1 S) ((r' + 1) + 1) := fun w =>
        AddMonoidHom.mk' (fun x => (resShortComplex_shortExact k K w.1 hSc).extClass.comp x h1)
          (fun a b => by rw [Abelian.Ext.comp_add])
      have hbijTw : ∀ w : R, Function.Bijective (dTw w) := fun w => by
        haveI hsubw : Subsingleton (Abelian.Ext (resShortComplex k K w.1 Sc).X₂
            (BOf k K w.1 S) (r' + 1)) :=
          Abelian.Ext.subsingleton_of_projective (resShortComplex k K w.1 Sc).X₂
            (BOf k K w.1 S) r'
        exact ⟨injective_extClass_of_subsingleton (resShortComplex_shortExact k K w.1 hSc)
            (BOf k K w.1 S) h1,
          surjective_extClass (resShortComplex_shortExact k K w.1 hSc) (BOf k K w.1 S) (h := h1)⟩
      let dT : Tgt k K R S K' (r' + 1) →+ Tgt k K R S M ((r' + 1) + 1) :=
        AddMonoidHom.mk' (fun c => fun w => dTw w (c w))
          (fun a b => by funext w; exact map_add (dTw w) (a w) (b w))
      have hbijT : Function.Bijective dT := bijective_pi (fun w => hbijTw w)
      have hcommC : ∀ b, thetaLHom k K R M ((r' + 1) + 1) S (dS b) =
          dT (thetaLHom k K R K' (r' + 1) S b) :=
        fun b => thetaL_extClass k K R hSc S b h1
      exact bijective_of_comp_comm dS (thetaLHom k K R M ((r' + 1) + 1) S)
        (thetaLHom k K R K' (r' + 1) S) dT ⟨hinjS, hsurjS⟩ (ih K' S hS) hbijT hcommC

end

end Work.SSGRoute
