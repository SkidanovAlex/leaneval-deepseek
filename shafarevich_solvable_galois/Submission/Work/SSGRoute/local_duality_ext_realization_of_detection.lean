import Mathlib
import Submission.Work.SSGRoute.local_duality_ext
import Submission.Work.SSGRoute.local_duality_ext_extH_finite
import Submission.Work.SSGRoute.local_pTorsion_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option maxHeartbeats 4000000

/-! ## Finite duality for the level pairing

The realisation clause (ii) of E7b (`Work.SSGRoute.local_duality_ext`) is the statement that the
Yoneda pairing `levelPair f ι : Ext¹_{D_w}(M, K_wˣ) × H¹(D_{w'}, M) → H²(D_{w'}, L_{w'}ˣ)`
surjects onto the `p`-torsion functionals as soon as it detects every nonzero class of the second
variable.

Everything below is the elementary finite-dimensional duality argument.  Since `M` is `p`-torsion,
both `V = Ext¹_{D_w}(M, K_wˣ)` and `W = H¹(D_{w'}, M)` are `𝔽_p`-vector spaces
(`Work.SSGRoute.ext_nsmul_p_torsion_left`, `Work.SSGRoute.ext_nsmul_p_torsion`), the pairing values
lie in the `p`-torsion `T[p]` of `T = H²(D_{w'}, L_{w'}ˣ)` (they are multiples of `p • v = 0`), and
`T[p] ≅ 𝔽_p` is one-dimensional (`Work.SSGRoute.local_pTorsion_card`).  After a `ZMod p`-linear
identification `e : T[p] ≃ₗ ZMod p` the pairing becomes an `𝔽_p`-bilinear form
`B : V →ₗ W →ₗ 𝔽_p`; detection says exactly that `B.flip` is injective, and finite duality
(`LinearMap.flip_injective_iff₂`, with `W` finite-dimensional because it is finite by
`Work.SSGRoute.local_duality_ext_extH_finite`) turns that into the surjectivity of `B`. -/

/-- **A finite `ZMod p`-module of cardinality `p` is `ZMod p`.**

For `p` prime and `A` a `ZMod p`-module with `Nat.card A = p`, the map `c ↦ c • x` for any
`x ≠ 0` is an injective linear map from a `p`-element set into a `p`-element set, hence a linear
equivalence `A ≃ₗ[ZMod p] ZMod p`. -/
theorem zmod_prime_linearEquiv_of_card_eq (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod p) A] [Finite A] (hcard : Nat.card A = p) :
    Nonempty (A ≃ₗ[ZMod p] ZMod p) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    omega
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  have hinj : Function.Injective (LinearMap.toSpanSingleton (ZMod p) A x) := by
    intro c d hcd
    simp only [LinearMap.toSpanSingleton_apply] at hcd
    have h : (c - d) • x = 0 := by rw [sub_smul, hcd, sub_self]
    rcases smul_eq_zero.mp h with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hx
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (ZMod p) A x) := by
    have hcu : (Finset.univ.image (LinearMap.toSpanSingleton (ZMod p) A x)).card
        = Fintype.card A := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod, hcard]
    have huniv : Finset.univ.image (LinearMap.toSpanSingleton (ZMod p) A x) = Finset.univ :=
      Finset.eq_univ_of_card _ hcu
    intro a
    have hmem : a ∈ Finset.univ.image (LinearMap.toSpanSingleton (ZMod p) A x) := by
      rw [huniv]; exact Finset.mem_univ a
    rw [Finset.mem_image] at hmem
    obtain ⟨b, _, hb⟩ := hmem
    exact ⟨b, hb⟩
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).symm⟩

/-- **Detection implies realisation for a `1`-dimensional-valued bilinear pairing.**

`V`, `W` are `ZMod p`-modules with `W` finite, `T` an additive group whose `p`-torsion has been
identified with `ZMod p` by `e`, and `pair : V → W → T` is bilinear (with the `p`-torsion
hypothesis `htors` ensuring the values land in `T[p]`).  If `pair` detects every nonzero `w ∈ W`,
then every additive `lam : W →+ T` which is `p`-torsion on values is `pair v ·` for some `v`.

The proof builds the `𝔽_p`-bilinear form `B v w = e ⟨pair v w, _⟩ : V →ₗ W →ₗ 𝔽_p`; detection is
exactly the injectivity of `B.flip`, so `B` is surjective by `LinearMap.flip_injective_iff₂`, and
`lam` is read off as an `𝔽_p`-linear functional through `e`. -/
theorem realization_of_detection_pairing
    (p : ℕ) [Fact p.Prime]
    (V W T : Type) [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Module (ZMod p) V] [Module (ZMod p) W] [Finite W]
    [Module (ZMod p) ↥(AddSubgroup.torsionBy (A := T) p)]
    (e : ↥(AddSubgroup.torsionBy (A := T) p) ≃ₗ[ZMod p] ZMod p)
    (pair : V → W → T)
    (hadd_v : ∀ v₁ v₂ w, pair (v₁ + v₂) w = pair v₁ w + pair v₂ w)
    (hsmul_v : ∀ (c : ZMod p) v w, pair (c • v) w = c.val • pair v w)
    (hadd_w : ∀ v w₁ w₂, pair v (w₁ + w₂) = pair v w₁ + pair v w₂)
    (hsmul_w : ∀ (c : ZMod p) v w, pair v (c • w) = c.val • pair v w)
    (htors : ∀ v w, (p : ℕ) • pair v w = 0)
    (hdet : ∀ w, w ≠ 0 → ∃ v, pair v w ≠ 0)
    (lam : W →+ T) (hlam : ∀ w, (p : ℕ) • lam w = 0) :
    ∃ v, ∀ w, pair v w = lam w := by
  classical
  haveI : FiniteDimensional (ZMod p) W := Module.Finite.of_finite
  have memTors : ∀ v w, pair v w ∈ AddSubgroup.torsionBy (A := T) p :=
    fun v w => AddSubgroup.torsionBy.nsmul_iff.mpr (htors v w)
  have hcoe : ∀ (c : ZMod p) (x : ↥(AddSubgroup.torsionBy (A := T) p)),
      ((c • x : ↥(AddSubgroup.torsionBy (A := T) p)) : T) = c.val • (x : T) := by
    intro c x
    have h1 : c • x = c.val • x := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val x, ZMod.natCast_zmod_val c]
    rw [h1]
    exact AddSubgroup.coe_nsmul _ x c.val
  let B : V →ₗ[ZMod p] W →ₗ[ZMod p] ZMod p :=
    LinearMap.mk₂ (ZMod p) (fun v w => e ⟨pair v w, memTors v w⟩)
      (fun v₁ v₂ w => by
        have h : (⟨pair (v₁+v₂) w, memTors (v₁+v₂) w⟩ :
              ↥(AddSubgroup.torsionBy (A := T) p))
            = ⟨pair v₁ w, memTors v₁ w⟩ + ⟨pair v₂ w, memTors v₂ w⟩ :=
          Subtype.ext (hadd_v v₁ v₂ w)
        rw [h, map_add])
      (fun c v w => by
        have h : (⟨pair (c • v) w, memTors (c • v) w⟩ : ↥(AddSubgroup.torsionBy (A := T) p))
            = c • ⟨pair v w, memTors v w⟩ := by
          apply Subtype.ext
          rw [hcoe c ⟨pair v w, memTors v w⟩]
          exact hsmul_v c v w
        rw [h, map_smul])
      (fun v w₁ w₂ => by
        have h : (⟨pair v (w₁+w₂), memTors v (w₁+w₂)⟩ :
              ↥(AddSubgroup.torsionBy (A := T) p))
            = ⟨pair v w₁, memTors v w₁⟩ + ⟨pair v w₂, memTors v w₂⟩ :=
          Subtype.ext (hadd_w v w₁ w₂)
        rw [h, map_add])
      (fun c v w => by
        have h : (⟨pair v (c • w), memTors v (c • w)⟩ : ↥(AddSubgroup.torsionBy (A := T) p))
            = c • ⟨pair v w, memTors v w⟩ := by
          apply Subtype.ext
          rw [hcoe c ⟨pair v w, memTors v w⟩]
          exact hsmul_w c v w
        rw [h, map_smul])
  have hdetB : ∀ w : W, w ≠ 0 → ∃ v, B v w ≠ 0 := by
    intro w hw
    obtain ⟨v, hv⟩ := hdet w hw
    refine ⟨v, fun h0 => hv ?_⟩
    have h1 : (⟨pair v w, memTors v w⟩ : ↥(AddSubgroup.torsionBy (A := T) p)) = 0 := by
      refine e.injective ?_
      rw [map_zero]
      exact h0
    exact congrArg Subtype.val h1
  have hflip : Function.Injective B.flip := by
    intro w w' hww'
    by_contra hne
    obtain ⟨v, hv⟩ := hdetB (w - w') (sub_ne_zero.mpr hne)
    exact hv (by
      have h0 : B.flip (w - w') = 0 := by rw [map_sub, hww', sub_self]
      have := congrArg (fun g : V →ₗ[ZMod p] ZMod p => g v) h0
      simpa [LinearMap.flip_apply] using this)
  have hsurj : Function.Surjective B := LinearMap.flip_injective_iff₂.mp hflip
  have memTorsL : ∀ w, lam w ∈ AddSubgroup.torsionBy (A := T) p :=
    fun w => AddSubgroup.torsionBy.nsmul_iff.mpr (hlam w)
  let ψ : W →ₗ[ZMod p] ZMod p :=
    { toFun := fun w => e ⟨lam w, memTorsL w⟩
      map_add' := fun w₁ w₂ => by
        have h : (⟨lam (w₁+w₂), memTorsL (w₁+w₂)⟩ : ↥(AddSubgroup.torsionBy (A := T) p))
            = ⟨lam w₁, memTorsL w₁⟩ + ⟨lam w₂, memTorsL w₂⟩ :=
          Subtype.ext (map_add lam w₁ w₂)
        rw [h, map_add]
      map_smul' := fun c w => by
        have h1 : c • w = c.val • w := by
          rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val w, ZMod.natCast_zmod_val c]
        have h : (⟨lam (c • w), memTorsL (c • w)⟩ : ↥(AddSubgroup.torsionBy (A := T) p))
            = c • ⟨lam w, memTorsL w⟩ := by
          apply Subtype.ext
          rw [hcoe c ⟨lam w, memTorsL w⟩]
          change lam (c • w) = c.val • lam w
          rw [h1, map_nsmul lam c.val w]
        rw [h, map_smul]
        simp }
  obtain ⟨v, hv⟩ := hsurj ψ
  refine ⟨v, fun w => ?_⟩
  have h2 : B v w = ψ w := by rw [hv]
  exact congrArg Subtype.val (e.injective h2)

/-- **E7b, clause (ii) from detection (finite duality).**

Fix the level data `(L, w', f, hf, ι, hι)` of E7b with `p ∣ |D_{w'}|`, and suppose the Yoneda
pairing detects every nonzero class of the second variable: for every `h ≠ 0` in
`W = H¹(D_{w'}, M) = extH (Rep.res f (Rep.res (decompK w).subtype M)) 1` there is
`y ∈ V = Ext¹_{D_w}(M, K_wˣ)` with `levelPair f ι y h ≠ 0`.

Then every additive `lam : W →+ H²(D_{w'}, L_{w'}ˣ)` is `levelPair f ι y ·` for some `y ∈ V`:
the pairing values and `lam h` are `p`-torsion, the `p`-torsion `T[p]` of `T = H²(D_{w'},L_{w'}ˣ)`
is a one-dimensional `ZMod p`-space (`Work.SSGRoute.local_pTorsion_card`), and finite duality
(`LinearMap.flip_injective_iff₂`, with `W` finite by
`Work.SSGRoute.local_duality_ext_extH_finite`) turns the detection into surjectivity. -/
theorem local_duality_ext_realization_of_detection
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* decompK (k := k) w)
    (hf : ∀ σ, ((f σ : decompK (k := k) w) : K ≃ₐ[k] K) = galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (localUnitsK (k := k) w) ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (hp : p ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w'))
    (hdet : ∀ h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1, h ≠ 0 →
      ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
        levelPair f ι y h ≠ 0) :
    ∀ lam : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1 →+
        extH (NK.HassePrinciple.localUnitsRep k L w') 2,
      (∀ h, p • lam h = 0) →
      ∃ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
        ∀ h, levelPair f ι y h = lam h := by
  classical
  intro lam hlam
  -- abbreviations for the three groups appearing
  -- `V = Ext¹_{D_w}(M, K_wˣ)`, `W = H¹(D_{w'}, M)`, `T = H²(D_{w'}, L_{w'}ˣ)`
  -- `p`-torsion of the coefficient module `M`, transported through restriction
  have hMres : ∀ x : Rep.res (decompK (k := k) w).subtype M, p • x = 0 := fun x => hM x
  have hMres' : ∀ x : Rep.res f (Rep.res (decompK (k := k) w).subtype M), p • x = 0 :=
    fun x => hM x
  -- the source `V` is a `ZMod p`-module
  have hVp : ∀ v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
      (localUnitsK (k := k) w) 1, p • v = 0 :=
    fun v => ext_nsmul_p_torsion_left p hMres v
  letI : Module (ZMod p) (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
      (localUnitsK (k := k) w) 1) := AddCommGroup.zmodModule (n := p) hVp
  -- the target `W` is a `ZMod p`-module, and finite
  have hWp : ∀ h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1, p • h = 0 :=
    fun h => ext_nsmul_p_torsion p hMres' h
  letI : Module (ZMod p) (extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1) :=
    AddCommGroup.zmodModule (n := p) hWp
  haveI : Finite (MulAction.stabilizer (L ≃ₐ[k] L) w') := inferInstance
  haveI : Finite (extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1) :=
    local_duality_ext_extH_finite _ 1
  -- the `p`-torsion of `T = H²(D_{w'}, L_{w'}ˣ)` is `ZMod p`
  haveI : Module (ZMod p)
      ↥(AddSubgroup.torsionBy (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) p) :=
    AddSubgroup.torsionBy.zmodModule
  have hcardT : Nat.card
      ↥(AddSubgroup.torsionBy (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) p) = p :=
    (Nat.card_congr (Equiv.subtypeEquivRight
        (fun x => AddSubgroup.torsionBy.nsmul_iff (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) (n := p)))).trans
      (local_pTorsion_card p k L w' hp)
  haveI : Finite ↥(AddSubgroup.torsionBy (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) p) :=
    (Nat.card_ne_zero.mp (by rw [hcardT]; exact (Fact.out : p.Prime).ne_zero)).2
  obtain ⟨e⟩ := zmod_prime_linearEquiv_of_card_eq p
    ↥(AddSubgroup.torsionBy (A := extH (NK.HassePrinciple.localUnitsRep k L w') 2) p) hcardT
  have hv_add : ∀ (v₁ v₂ : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
        (localUnitsK (k := k) w) 1)
      (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      levelPair f ι (v₁ + v₂) h = levelPair f ι v₁ h + levelPair f ι v₂ h :=
    fun v₁ v₂ h => levelPair_add f ι v₁ v₂ h
  have hv_smul : ∀ (c : ZMod p)
      (v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
      (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      levelPair f ι (c • v) h = c.val • levelPair f ι v h := by
    intro c v h
    have hcv : c • v = c.val • v := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val v, ZMod.natCast_zmod_val c]
    let hvadd : (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
          (localUnitsK (k := k) w) 1) →+ extH (NK.HassePrinciple.localUnitsRep k L w') 2 :=
      { toFun := fun x => levelPair f ι x h
        map_zero' := levelPair_zero f ι h
        map_add' := fun a b => levelPair_add f ι a b h }
    rw [hcv]
    simpa [hvadd] using map_nsmul hvadd c.val v
  have hw_add : ∀ (v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
        (localUnitsK (k := k) w) 1)
      (h₁ h₂ : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      levelPair f ι v (h₁ + h₂) = levelPair f ι v h₁ + levelPair f ι v h₂ :=
    fun v h₁ h₂ => levelPair_add_h f ι v h₁ h₂
  have hw_smul : ∀ (c : ZMod p)
      (v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
      (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      levelPair f ι v (c • h) = c.val • levelPair f ι v h := by
    intro c v h
    have hcw : c • h = c.val • h := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val h, ZMod.natCast_zmod_val c]
    rw [hcw]
    exact map_nsmul (levelPairFunctional (f := f) (ι := ι) (r := 1) (s := 1) v) c.val h
  have htors : ∀ (v : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
        (localUnitsK (k := k) w) 1)
      (h : extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1),
      p • levelPair f ι v h = 0 := by
    intro v h
    let hvadd : (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M)
          (localUnitsK (k := k) w) 1) →+ extH (NK.HassePrinciple.localUnitsRep k L w') 2 :=
      { toFun := fun x => levelPair f ι x h
        map_zero' := levelPair_zero f ι h
        map_add' := fun a b => levelPair_add f ι a b h }
    have h1 := map_nsmul hvadd p v
    rw [hVp v, map_zero] at h1
    simpa [hvadd] using h1.symm
  -- assemble: the pairing is bilinear and detects, so finite duality realises `lam`
  exact realization_of_detection_pairing p
    (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1)
    (extH (Rep.res f (Rep.res (decompK (k := k) w).subtype M)) 1)
    (extH (NK.HassePrinciple.localUnitsRep k L w') 2)
    e (fun v h => levelPair f ι v h) hv_add hv_smul hw_add hw_smul htors hdet lam hlam

end Work.SSGRoute
