import Mathlib
import Submission.NK.NUV2.LC.RouteB.DictionaryDeps

/-!
# Auxiliary lemmas for the explicit-cocycle avatar

This module proves the ingredients of `NK.NUV2.LC.RouteB.cycClassUnitsAvatar` that are stated
about the *explicit* cyclic class `NK.CFTLib.Descent.cycClass` /
`NK.CFTLib.IdeleHasse.Descent.cycClassOf`:

* `cycClass_add` / `cycClassOf_add` — the explicit cyclic class is additive in its coefficient,
  hence in the global element `Kˣ`;
* `cycClassOf_eq_zero_iff_mem_range` — the class of `x` vanishes iff `x` is a norm, in the
  `Units.map (Algebra.norm K)`-form of `NK.CFTLib.IdeleHasse.Descent.cycClassOf_eq_zero_iff`.

(The variant of the last statement in
`Submission/Work/CFTLib/IdeleHasse/Descent/cycClassOf_eq_zero_iff.lean` does not build: its proof
rewrites with `LinearMap.mem_range` under a membership whose instance is elaborated for the
definitionally equal, but not syntactically equal, carrier `Additive Fˣ`.  The proof below avoids
that rewrite, using `LinearMap.mem_range` as a term instead.)
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory

namespace NK.NUV2.LC.RouteB

/-- **Additivity of the explicit cyclic class `NK.CFTLib.Descent.cycClass` in its coefficient.**

The 2-cocycle `cycFun A g hg a (γ, δ) = carry g hg γ δ • a` is *pointwise* `zsmul` of `a`, hence
additive in `a`, and `groupCohomology.H2π` (the quotient map to `H²`) is additive.  The proof
obligations (invariance of the coefficient) are `Prop`s, so proof irrelevance removes them. -/
lemma cycClass_add {G : Type} [Group G] [Fintype G]
    (A : Rep NK.HassePrinciple.CoeffInt G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) (a a' : A)
    (ha : ∀ γ : G, A.ρ γ a = a) (ha' : ∀ γ : G, A.ρ γ a' = a') :
    NK.CFTLib.Descent.cycClass A g hg (a + a') (fun γ => by rw [map_add, ha γ, ha' γ]) =
      NK.CFTLib.Descent.cycClass A g hg a ha +
        NK.CFTLib.Descent.cycClass A g hg a' ha' := by
  have hfun : NK.CFTLib.Descent.cycFun A g hg (a + a') =
      NK.CFTLib.Descent.cycFun A g hg a + NK.CFTLib.Descent.cycFun A g hg a' := by
    funext p
    simp only [NK.CFTLib.Descent.cycFun, Pi.add_apply]
    rw [zsmul_add]
  rw [NK.CFTLib.Descent.cycClass, NK.CFTLib.Descent.cycClass, NK.CFTLib.Descent.cycClass,
    ← map_add]
  congr 1
  exact Subtype.ext hfun

/-- **Additivity of the cyclic class of a global element**: `cycClassOf` is a homomorphism
`Kˣ → H²(Gal(F/K), Fˣ)`, because `unitsImage` is multiplicative and `cycClass` is additive. -/
lemma cycClassOf_add {K F : Type} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
    (g : F ≃ₐ[K] F) (hg : ∀ σ : F ≃ₐ[K] F, σ ∈ Subgroup.zpowers g) (x y : Kˣ) :
    NK.CFTLib.IdeleHasse.Descent.cycClassOf g hg (x * y) =
      NK.CFTLib.IdeleHasse.Descent.cycClassOf g hg x +
        NK.CFTLib.IdeleHasse.Descent.cycClassOf g hg y := by
  unfold NK.CFTLib.IdeleHasse.Descent.cycClassOf
  simp only [NK.CFTLib.IdeleHasse.Descent.unitsImage, map_mul]
  exact cycClass_add _ g hg _ _ _ _

/-- The existential norm condition of `Descent.cycClassOf_eq_zero_iff` rewritten in the
`Units.map (Algebra.norm K)`-range form (`algebraMap` is injective). -/
lemma mem_range_units_map_norm_iff {K F : Type} [Field K] [Field F] [Algebra K F] (x : Kˣ) :
    x ∈ MonoidHom.range (Units.map (Algebra.norm K : F →* K)) ↔
      ∃ y : Fˣ, algebraMap K F (Algebra.norm K (y : F)) = algebraMap K F (x : K) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have h : (Algebra.norm K) (y : F) = (x : K) := by
      have hc := congrArg (fun u : Kˣ => (u : K)) hy
      rwa [Units.coe_map] at hc
    rw [h]
  · rintro ⟨y, hy⟩
    have h : (Algebra.norm K) (y : F) = (x : K) := (algebraMap K F).injective hy
    exact ⟨y, Units.ext (by rw [Units.coe_map]; exact h)⟩

/-- **The cyclic class of a global element vanishes iff the element is a norm**, with the norm
expressed through the norm endomorphism of the units representation (`unitsRep_norm_apply`). -/
lemma cycClassOf_eq_zero_iff_norm {K F : Type} [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    (g : F ≃ₐ[K] F) (hg : ∀ σ : F ≃ₐ[K] F, σ ∈ Subgroup.zpowers g) (x : Kˣ) :
    NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := F) g hg x = 0 ↔
      ∃ y : Fˣ, algebraMap K F (Algebra.norm K (y : F)) = algebraMap K F (x : K) := by
  have h1 : NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := F) g hg x = 0 ↔
      (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := F) x :
        ↑(NK.HassePrinciple.unitsRep K F)) ∈
        LinearMap.range (NK.HassePrinciple.unitsRep K F).ρ.norm := by
    unfold NK.CFTLib.IdeleHasse.Descent.cycClassOf
    exact NK.CFTLib.IdeleHasse.Descent.cycClass_eq_zero_iff _ g hg _ _
  have h2 : NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := F) g hg x = 0 ↔
      ∃ v : ↑(NK.HassePrinciple.unitsRep K F),
        (NK.HassePrinciple.unitsRep K F).ρ.norm v =
          NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := F) x :=
    h1.trans (LinearMap.mem_range (f := (NK.HassePrinciple.unitsRep K F).ρ.norm))
  have hnorm' : ∀ v : ↑(NK.HassePrinciple.unitsRep K F),
      ((Additive.toMul ((NK.HassePrinciple.unitsRep K F).ρ.norm v) : Fˣ) : F)
        = algebraMap K F (Algebra.norm K ((Additive.toMul v : Fˣ) : F)) := by
    intro v
    rw [show v = Additive.ofMul (Additive.toMul v) from rfl]
    exact NK.CFTLib.IdeleHasse.Descent.unitsRep_norm_apply (K := K) (F := F) (Additive.toMul v)
  have hU : ((Additive.toMul (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := F) x) :
      Fˣ) : F) = algebraMap K F (x : K) := rfl
  refine h2.trans ?_
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨Additive.toMul v, ?_⟩
    have hc := congrArg (fun u : Additive Fˣ => ((Additive.toMul u : Fˣ) : F)) hv
    rw [hnorm' v, hU] at hc
    exact hc
  · rintro ⟨y, hy⟩
    refine ⟨Additive.ofMul y, ?_⟩
    have hc : ((Additive.toMul ((NK.HassePrinciple.unitsRep K F).ρ.norm
        (Additive.ofMul y)) : Fˣ) : F)
        = ((Additive.toMul (NK.CFTLib.IdeleHasse.Descent.unitsImage (K := K) (F := F) x) :
          Fˣ) : F) := by
      rw [hnorm' (Additive.ofMul y), hU]
      exact hy
    exact Additive.ofMul.injective (Units.ext hc)

/-- **The cyclic class of a global element vanishes iff the element is a norm** (range form). -/
lemma cycClassOf_eq_zero_iff_mem_range {K F : Type} [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    (g : F ≃ₐ[K] F) (hg : ∀ σ : F ≃ₐ[K] F, σ ∈ Subgroup.zpowers g) (x : Kˣ) :
    NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := K) (F := F) g hg x = 0 ↔
      x ∈ MonoidHom.range (Units.map (Algebra.norm K : F →* K)) :=
  (cycClassOf_eq_zero_iff_norm g hg x).trans (mem_range_units_map_norm_iff x).symm

end NK.NUV2.LC.RouteB

namespace NK.NUV2.LC.RouteB

/-- **The cyclic-algebra class built from the explicit cocycle `Descent.cycClassOf`, and its `μ_p`-avatar.**

This is the variant of `NK.NUV2.LC.RouteB.exists_muColim_avatar` in which the units class `γ` is
built from the *explicit* cyclic cocycle `NK.CFTLib.IdeleHasse.Descent.cycClassOf` (rather than
from RouteC's `powHom b ∪ deltaHomChar`), so that the localisation dictionary of
`Descent.localNormSubgroup_iff_cycClass_finite` applies verbatim.

Route (mirror `exists_muColim_avatar`, whose proof is a complete template):
* take `g, hg` from `IsCyclic.exists_generator` (with `hcyc`), and set
  `γ b := H2Units.ofLevel ⊤ ⟨E⟩ ((unitsTransport ⟨E⟩).symm (cycClassOf g hg b))`; the first conjunct
  is then `rfl`;
* **additivity**: prove `NK.CFTLib.Descent.cycClass_add` — for a `CoeffInt`-representation `A`,
  `cycClass A g hg (a + a') ha = cycClass A g hg a ha₁ + cycClass A g hg a' ha₂` — from the
  definition `cycFun A g hg a (γ,δ) = carry g hg γ δ • a` (`NK.CFTLib.Descent/CyclicCocycle.lean`),
  which is *pointwise `smul_add`*, together with the additivity of `groupCohomology.H2π` (the proof
  obligations `ha` are `Prop`s, so proof irrelevance handles them). Then use
  `unitsImage (b₁ * b₂) = unitsImage b₁ + unitsImage b₂`, `map_add` and `H2Units.ofLevel_add`;
* **norm criterion**: `NK.CFTLib.IdeleHasse.Descent.cycClassOf_eq_zero_iff` (the class vanishes iff
  `x` is a norm) together with the injectivity of `unitsTransport ⟨E⟩` and
  `NK.NUV2.LC.RouteB.H2Units_ofLevel_injective_top` / `H2Units_ofLevel_zero`;
* **`p`-torsion and the avatar**: `p • γ b = γ (b ^ p)` (from additivity) and
  `b ^ p = N_{E/F}(algebraMap F ↥E b) = Units.map (Algebra.norm F) (Units.map (algebraMap F ↥E) b)`
  (`Algebra.norm_algebraMap` and `hdeg`), so `p • γ b = 0`; then
  `NK.NUV2.ABHN.kummerColim_surjective_pTorsion` gives `Y b` for each `b`, additivity of `Y`
  follows from `NK.HassePrinciple.kummerColim_injective`, and the norm criterion for `Y` from the
  same injectivity. -/
theorem cycClassUnitsAvatar (p : ℕ) (hp : p.Prime)
    {F : Type} [Field F] [NumberField F] (F' : Type) [Field F'] [Algebra F F']
    [IsSepClosure F F'] (E : IntermediateField F F') [FiniteDimensional F E] [IsGalois F E]
    [NumberField ↥E] (hdeg : Module.finrank F E = p) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E)) :
    ∃ (g : ↥E ≃ₐ[F] ↥E) (hg : ∀ σ : ↥E ≃ₐ[F] ↥E, σ ∈ Subgroup.zpowers g)
      (γ : Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)))
      (Y : Fˣ → NK.HassePrinciple.MuColim (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F))),
      (∀ b : Fˣ, NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
          (⊤ : Subgroup Gal(F'/F)) (⟨E⟩ : FiniteGaloisIntermediateField F F')
          ((NK.NUV2.LC.unitsTransport (K := F) (K' := F')
            (⟨E⟩ : FiniteGaloisIntermediateField F F')).symm
            (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b)) = γ b) ∧
      (∀ b₁ b₂ : Fˣ, γ (b₁ * b₂) = γ b₁ + γ b₂) ∧
      (∀ b : Fˣ, NK.HassePrinciple.kummerColim (K := F) (K' := F') p
          (⊤ : Subgroup Gal(F'/F)) (Y b) = γ b) ∧
      (∀ b₁ b₂ : Fˣ, Y (b₁ * b₂) = Y b₁ + Y b₂) ∧
      (∀ b : Fˣ, γ b = 0 ↔ b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F))) ∧
      (∀ b : Fˣ, Y b = 0 ↔ b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F))) := by
  classical
  haveI hcycI : IsCyclic (↥E ≃ₐ[F] ↥E) := hcyc
  obtain ⟨g, hgsurj⟩ := IsCyclic.exists_zpow_surjective (G := ↥E ≃ₐ[F] ↥E)
  have hg : ∀ σ : ↥E ≃ₐ[F] ↥E, σ ∈ Subgroup.zpowers g := fun σ => by
    obtain ⟨k, hk⟩ := hgsurj σ
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hk⟩
  -- the explicit cyclic-algebra class, transported into the units colimit
  let γ : Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) :=
    fun b => NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
      (⊤ : Subgroup Gal(F'/F)) (⟨E⟩ : FiniteGaloisIntermediateField F F')
      ((NK.NUV2.LC.unitsTransport (K := F) (K' := F')
        (⟨E⟩ : FiniteGaloisIntermediateField F F')).symm
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b))
  have hγdef : ∀ b : Fˣ, γ b = NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
      (⊤ : Subgroup Gal(F'/F)) (⟨E⟩ : FiniteGaloisIntermediateField F F')
      ((NK.NUV2.LC.unitsTransport (K := F) (K' := F')
        (⟨E⟩ : FiniteGaloisIntermediateField F F')).symm
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b)) := fun b => rfl
  -- additivity of `γ`, from the additivity of the explicit cyclic class
  have hγadd : ∀ b₁ b₂ : Fˣ, γ (b₁ * b₂) = γ b₁ + γ b₂ := by
    intro b₁ b₂
    rw [hγdef, hγdef, hγdef, cycClassOf_add g hg b₁ b₂, map_add,
      NK.NUV2.ABHN.H2Units.ofLevel_add]
  -- the norm criterion for `γ`, from the injectivity of the level structure map
  have hγnorm : ∀ b : Fˣ,
      γ b = 0 ↔ b ∈ MonoidHom.range (Units.map (Algebra.norm F : ↥E →* F)) := by
    intro b
    have h1 : γ b = 0 ↔
        NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b = 0 := by
      rw [hγdef]
      constructor
      · intro h
        have h2 : (NK.NUV2.LC.unitsTransport (K := F) (K' := F')
            (⟨E⟩ : FiniteGaloisIntermediateField F F')).symm
            (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b) = 0 :=
          H2Units_ofLevel_injective_top (⟨E⟩ : FiniteGaloisIntermediateField F F')
            (by rw [h, H2Units_ofLevel_zero ⟨E⟩])
        exact (NK.NUV2.LC.unitsTransport (K := F) (K' := F')
          (⟨E⟩ : FiniteGaloisIntermediateField F F')).symm.injective (by rw [h2, map_zero])
      · intro h
        rw [h, map_zero, H2Units_ofLevel_zero]
    exact h1.trans (cycClassOf_eq_zero_iff_mem_range (K := F) (F := ↥E) g hg b)
  have hγone : γ 1 = 0 := by
    have h := hγadd 1 1
    rw [mul_one] at h
    exact (add_left_cancel (a := γ 1) (b := 0)
      (show γ 1 + 0 = γ 1 + γ 1 from by rw [add_zero]; exact h)).symm
  have hγpow : ∀ (b : Fˣ) (n : ℕ), γ (b ^ n) = n • γ b := by
    intro b n
    induction n with
    | zero => simpa using hγone
    | succ k ih => rw [pow_succ, hγadd, ih, succ_nsmul]
  -- `b ^ p` is the norm of `algebraMap F ↥E b`, so `γ b` is `p`-torsion
  have hnorm : ∀ x : Fˣ, Units.map (Algebra.norm F : ↥E →* F)
      (Units.map (algebraMap F ↥E : F →* ↥E) x) = x ^ p := by
    intro x
    haveI : Module.Free F ↥E := Module.Free.of_divisionRing F ↥E
    have h := Algebra.norm_algebraMap (R := F) (S := ↥E) (x : F)
    rw [hdeg] at h
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map]
    exact h
  have hpγ : ∀ b : Fˣ, p • γ b = 0 := by
    intro b
    rw [← hγpow b p]
    exact (hγnorm (b ^ p)).mpr ⟨Units.map (algebraMap F ↥E : F →* ↥E) b, hnorm b⟩
  -- the `μ_p`-avatar, from exactness of the Kummer sequence in the limit
  choose Y hYspec using fun b =>
    NK.NUV2.ABHN.kummerColim_surjective_pTorsion p hp (γ b) (hpγ b)
  refine ⟨g, hg, γ, Y, ?_, hγadd, hYspec, ?_, hγnorm, ?_⟩
  · exact fun b => (hγdef b).symm
  · -- `Y` is additive, by injectivity of the Kummer map and additivity of `γ`
    intro b₁ b₂
    refine (NK.HassePrinciple.kummerColim_injective (K := F) (K' := F') p hp
      (⊤ : Subgroup Gal(F'/F))) ?_
    rw [kummerColim_add, hYspec b₁, hYspec b₂, hYspec (b₁ * b₂), hγadd b₁ b₂]
  · -- `Y` detects the norm condition exactly as `γ` does
    intro b
    have hz : NK.HassePrinciple.kummerColim (K := F) (K' := F') p
        (⊤ : Subgroup Gal(F'/F)) (0 : NK.HassePrinciple.MuColim (K := F) (K' := F') p
          (⊤ : Subgroup Gal(F'/F))) = 0 := kummerColim_zero p (⊤ : Subgroup Gal(F'/F))
    constructor
    · intro h
      refine (hγnorm b).mp ?_
      rw [← hYspec b, h, hz]
    · intro h
      exact (NK.HassePrinciple.kummerColim_injective (K := F) (K' := F') p hp
        (⊤ : Subgroup Gal(F'/F))) (by rw [hYspec b, hz]; exact (hγnorm b).mpr h)

end NK.NUV2.LC.RouteB
