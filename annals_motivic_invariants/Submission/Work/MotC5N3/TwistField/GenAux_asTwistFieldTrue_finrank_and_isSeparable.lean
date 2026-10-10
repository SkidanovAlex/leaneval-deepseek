import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The twist field `L(E)^σ'` is a degree-`5` separable extension of `L(E)`

Let `K = 𝕜(t)`, `Ω = Work.MotC5N3.OmA K D = K̄(E)` the function field of the Klein curve over `K̄ = Work.MotC5N3.KbA K`,
`L = asFieldL D g = K(E) ⊔ K(asRoot g) = L(E)` (with `L = K(asRoot g)`), and let
`σ' = asTwistAction D τ σS` be the twisted Artin–Schreier action on `Ω`.  The corrected twist field
is `F = asTwistFieldTrue D g τ σS = asTwistFieldFix D τ σS ⊓ L`, i.e. the fixed points of `σ'`
*inside* `L(E)`.

This file proves that whenever `σ'` has order `5` on `L` (hypotheses `h5L`, `hneL`) and preserves
`L` (`hpres`), the extension `L/F` has degree `5` and is separable:

* `F.relfinrank L = 5` — Artin's theorem `FixedPoints.finrank_eq_card` applied to the restriction
  `φ` of `σ'` to `L`, transported from `↥L` to the ambient field by ring isomorphism;
* every `z ∈ L` is separable over `F` — likewise from `FixedPoints.isSeparable`, through
  `IntermediateField.isSeparable_of_mem_isSeparable`.

The two transfer steps use `Algebra.finrank_eq_of_equiv_equiv` and
`Algebra.IsSeparable.of_equiv_equiv` for the ring equivalences `↥S ≃+* ↥F` (given by the identity
on the ambient field) and `↥L ≃+* ↥L'` (the identity, since the carriers coincide).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.MotC5N3
open Work.MotV5
open IntermediateField

theorem GenAux_asTwistFieldTrue_finrank_and_isSeparable (𝕜 : Type) [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (g : K)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (h5L : ∀ x ∈ Work.MotC5N3.asFieldL D g, ((Work.MotC5N3.asTwistAction D τ σS) ^ 5) x = x)
    (hneL : ∃ x ∈ Work.MotC5N3.asFieldL D g, Work.MotC5N3.asTwistAction D τ σS x ≠ x)
    (hpres : ∀ x ∈ Work.MotC5N3.asFieldL D g, Work.MotC5N3.asTwistAction D τ σS x ∈ Work.MotC5N3.asFieldL D g) :
    (Work.MotC5N3.asTwistFieldTrue D g τ σS).relfinrank (Work.MotC5N3.asFieldL D g) = 5 ∧
      ∀ z ∈ Work.MotC5N3.asFieldL D g, IsSeparable ↥(Work.MotC5N3.asTwistFieldTrue D g τ σS) z := by
  classical
  let σ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D := Work.MotC5N3.asTwistAction D τ σS
  let L : IntermediateField (K) (Work.MotC5N3.OmA K D) := Work.MotC5N3.asFieldL D g
  -- `σ ^ n` preserves `L` for every `n`
  have hpresPow : ∀ n : ℕ, ∀ x ∈ L, (σ ^ n) x ∈ L := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
        intro x hx
        rw [pow_succ', AlgEquiv.mul_apply]
        exact hpres _ (ih x hx)
  -- the restriction of `σ` to `L`, as an algebra endomorphism
  let φ₀ : ↥L →ₐ[K] ↥L :=
    { toFun := fun x => ⟨σ x, hpres x x.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ (x:Work.MotC5N3.OmA K D) (y:Work.MotC5N3.OmA K D))
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ (x:Work.MotC5N3.OmA K D) (y:Work.MotC5N3.OmA K D))
      commutes' := fun c => Subtype.ext (by
        have h1 : (((algebraMap (K) ↥L) c : ↥L) : Work.MotC5N3.OmA K D) =
            algebraMap (K) (Work.MotC5N3.OmA K D) c :=
          (IsScalarTower.algebraMap_apply (K) ↥L (Work.MotC5N3.OmA K D) c).symm
        show σ (((algebraMap (K) ↥L) c : ↥L) : Work.MotC5N3.OmA K D) =
          (((algebraMap (K) ↥L) c : ↥L) : Work.MotC5N3.OmA K D)
        rw [h1, AlgEquiv.commutes]) }
  have hφ₀_inj : Function.Injective φ₀ := by
    intro a b hab
    refine Subtype.ext (σ.injective ?_)
    show σ (a : Work.MotC5N3.OmA K D) = σ (b : Work.MotC5N3.OmA K D)
    exact congrArg (fun y : ↥L => (y : Work.MotC5N3.OmA K D)) hab
  -- `σ ^ 5 = 1` on `L` and `σ` preserves `L` make the restriction bijective
  have hφ₀_surj : Function.Surjective φ₀ := by
    intro y
    refine ⟨⟨(σ ^ 4) y, hpresPow 4 y y.2⟩, ?_⟩
    apply Subtype.ext
    show σ ((σ ^ 4) (y : Work.MotC5N3.OmA K D)) = (y : Work.MotC5N3.OmA K D)
    have h5' : (σ ^ 5) (y : Work.MotC5N3.OmA K D) = (y : Work.MotC5N3.OmA K D) := h5L y y.2
    rw [show (5:ℕ) = 4 + 1 from rfl, pow_succ', AlgEquiv.mul_apply] at h5'
    exact h5'
  let φ : ↥L ≃ₐ[K] ↥L := AlgEquiv.ofBijective φ₀ ⟨hφ₀_inj, hφ₀_surj⟩
  have hφφ : ∀ x : ↥L, ((φ x : ↥L) : Work.MotC5N3.OmA K D) = σ (x : Work.MotC5N3.OmA K D) := fun x => rfl
  have hpow : ∀ n : ℕ, ∀ x : ↥L,
      (((φ ^ n) x : ↥L) : Work.MotC5N3.OmA K D) = ((σ ^ n) (x : Work.MotC5N3.OmA K D)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ', AlgEquiv.mul_apply, hφφ, ih, pow_succ', AlgEquiv.mul_apply]
  -- `φ` has order exactly `5`
  have h5φ : φ ^ 5 = 1 := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    rw [hpow 5 x]
    exact h5L x x.2
  have hneφ : φ ≠ 1 := by
    intro h
    obtain ⟨x, hxL, hxne⟩ := hneL
    refine hxne ?_
    have h1 := hφφ ⟨x, hxL⟩
    rw [h] at h1
    simpa using h1.symm
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have horder : orderOf φ = 5 := orderOf_eq_prime h5φ hneφ
  -- the fixed field of `⟨φ⟩` in `↥L` has degree `5` over `↥L` (Artin)
  let S : Subfield ↥L := FixedPoints.subfield ↥(Subgroup.zpowers φ) ↥L
  have hSmem : ∀ x : ↥L, x ∈ S ↔ ∀ m : ↥(Subgroup.zpowers φ), m • x = x := by
    intro x
    exact MulAction.mem_fixedPoints
  have hfin : Finite ↥(Subgroup.zpowers φ) :=
    finite_zpowers.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, h5φ⟩)
  haveI : Fintype ↥(Subgroup.zpowers φ) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(Subgroup.zpowers φ) = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, horder]
  have hfr : Module.finrank ↥S ↥L = 5 := by
    rw [show (5:ℕ) = Fintype.card ↥(Subgroup.zpowers φ) from hcard.symm]
    exact FixedPoints.finrank_eq_card ↥(Subgroup.zpowers φ) ↥L
  -- the target field `F` unfolds to the fixed field of `⟨σ⟩` intersected with `L`
  let F : IntermediateField (K) (Work.MotC5N3.OmA K D) := Work.MotC5N3.asTwistFieldTrue D g τ σS
  have hFdef : F = IntermediateField.fixedField (Subgroup.zpowers σ) ⊓ L := rfl
  have hFmem : ∀ x : Work.MotC5N3.OmA K D, x ∈ F ↔ x ∈ L ∧ ∀ g ∈ Subgroup.zpowers σ, g x = x := by
    intro x
    rw [hFdef, IntermediateField.mem_inf, IntermediateField.mem_fixedField_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hfixφ : ∀ x : ↥L, x ∈ S → φ x = x := by
    intro x hx
    have h := (hSmem x).mp hx ⟨φ, Subgroup.mem_zpowers φ⟩
    simpa [Subgroup.mk_smul, AlgEquiv.smul_def] using h
  -- the identity on the ambient field restricts to a ring equivalence `↥S ≃+* ↥F`
  have hSmemF : ∀ s : ↥S, ((s.1 : ↥L) : Work.MotC5N3.OmA K D) ∈ F := by
    intro s
    rw [hFmem]
    refine ⟨s.1.2, ?_⟩
    intro g hg
    have hσs : σ (s.1 : Work.MotC5N3.OmA K D) = (s.1 : Work.MotC5N3.OmA K D) := by
      have h := congrArg (fun y : ↥L => (y : Work.MotC5N3.OmA K D)) (hfixφ s.1 s.2)
      rwa [hφφ s.1] at h
    have hstab : σ ∈ MulAction.stabilizer (Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
        (s.1 : Work.MotC5N3.OmA K D) :=
      (MulAction.mem_stabilizer_iff).mpr (by simpa [AlgEquiv.smul_def] using hσs)
    have hmem : g ∈ MulAction.stabilizer (Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
        (s.1 : Work.MotC5N3.OmA K D) := (Subgroup.zpowers_le (g := σ)).mpr hstab hg
    simpa [AlgEquiv.smul_def] using (MulAction.mem_stabilizer_iff).mp hmem
  let iHom : ↥S →+* ↥F :=
    { toFun := fun s => ⟨((s.1 : ↥L) : Work.MotC5N3.OmA K D), hSmemF s⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hinj : Function.Injective iHom := by
    intro a b hab
    have h1 : ((a.1 : ↥L) : Work.MotC5N3.OmA K D) = ((b.1 : ↥L) : Work.MotC5N3.OmA K D) :=
      congrArg (fun y : ↥F => (y : Work.MotC5N3.OmA K D)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hsurj : Function.Surjective iHom := by
    intro y
    have hyF := (hFmem (y : Work.MotC5N3.OmA K D)).mp y.2
    have hs : (⟨(y : Work.MotC5N3.OmA K D), hyF.1⟩ : ↥L) ∈ S := by
      rw [hSmem]
      intro m
      have hφy : φ ⟨(y : Work.MotC5N3.OmA K D), hyF.1⟩ = ⟨(y : Work.MotC5N3.OmA K D), hyF.1⟩ := by
        apply Subtype.ext
        show σ (y : Work.MotC5N3.OmA K D) = (y : Work.MotC5N3.OmA K D)
        exact hyF.2 σ (Subgroup.mem_zpowers σ)
      have hstab : φ ∈ MulAction.stabilizer (↥L ≃ₐ[K] ↥L)
          (⟨(y : Work.MotC5N3.OmA K D), hyF.1⟩ : ↥L) :=
        (MulAction.mem_stabilizer_iff).mpr (by simpa [AlgEquiv.smul_def] using hφy)
      have hmem : (m : ↥L ≃ₐ[K] ↥L) ∈ MulAction.stabilizer (↥L ≃ₐ[K] ↥L)
          (⟨(y : Work.MotC5N3.OmA K D), hyF.1⟩ : ↥L) := (Subgroup.zpowers_le (g := φ)).mpr hstab m.2
      have h2 := (MulAction.mem_stabilizer_iff).mp hmem
      show (m : ↥L ≃ₐ[K] ↥L) • (⟨(y : Work.MotC5N3.OmA K D), hyF.1⟩ : ↥L) =
        ⟨(y : Work.MotC5N3.OmA K D), hyF.1⟩
      simpa [AlgEquiv.smul_def] using h2
    refine ⟨(⟨⟨(y : Work.MotC5N3.OmA K D), hyF.1⟩, hs⟩ : ↥S), ?_⟩
    exact Subtype.ext rfl
  let i : ↥S ≃+* ↥F := RingEquiv.ofBijective iHom ⟨hinj, hsurj⟩
  have hi : ∀ s : ↥S, ((i s : ↥F) : Work.MotC5N3.OmA K D) = ((s.1 : ↥L) : Work.MotC5N3.OmA K D) :=
    fun s => rfl
  -- `L` as an extension of `F`
  have hFL : F ≤ L := inf_le_right
  let L' : IntermediateField ↥F (Work.MotC5N3.OmA K D) := IntermediateField.extendScalars hFL
  have hj : (algebraMap ↥F ↥L').comp i.toRingHom =
      (RingEquiv.refl ↥L).toRingHom.comp (algebraMap ↥S ↥L) := by
    ext s
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
      SubalgebraClass.coe_algebraMap, IntermediateField.algebraMap_apply, hi,
      RingEquiv.coe_ringHom_refl, RingHomCompTriple.comp_eq]
    rw [Subfield.algebraMap_ofSubfield]
    rfl
  let j : ↥L ≃+* ↥L' := RingEquiv.refl ↥L
  have hj' : (algebraMap ↥F ↥L').comp i.toRingHom = j.toRingHom.comp (algebraMap ↥S ↥L) := hj
  -- degree transfer
  have hfr2 : Module.finrank ↥F ↥L' = 5 := by
    have h := Algebra.finrank_eq_of_equiv_equiv i j hj'
    rw [← h]
    exact hfr
  refine ⟨?_, ?_⟩
  · rw [IntermediateField.relfinrank_eq_finrank_of_le hFL]
    exact hfr2
  · -- separability transfer
    haveI : Algebra.IsSeparable ↥S ↥L := FixedPoints.isSeparable ↥(Subgroup.zpowers φ) ↥L
    haveI : Algebra.IsSeparable ↥F ↥L' := Algebra.IsSeparable.of_equiv_equiv i j hj'
    intro z hz
    exact IntermediateField.isSeparable_of_mem_isSeparable ↥F (Work.MotC5N3.OmA K D)
      (L := L') ((IntermediateField.mem_extendScalars hFL).mpr hz)

end Work.MotC5N3