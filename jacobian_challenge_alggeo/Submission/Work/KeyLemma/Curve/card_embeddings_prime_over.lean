import Mathlib
import Submission.Work.KeyLemma.Curve.count_embeddings

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.KeyLemma.Curve

open Ideal

universe u

/-- **The number of `K`-embeddings of `E` into `L` sending the prime `q` into the prime `P` is
`e(q|p) * f(q|p)`.**

Mathematically: composing with the projection `Gal(L/K) → Gal(L/K)/Gal(L/E)` identifies
`K`-embeddings `E → L` with left cosets of `H = Gal(L/E)`, and the set
`X = {g ∈ Gal(L/K) | g(q)·C ≤ P}` of group elements inducing such an embedding with the required
property is a union of right `H`-cosets, so the number of embeddings equals `|X| / |H|`.
Since `Gal(L/K)` acts transitively on the primes over `p`, the map `g ↦ g⁻¹(P)` makes `X` a union
of `|S_q|` fibres, each of size `|D(P)| = e(P|p) f(P|p)`, where `S_q` is the set of primes over
`p` containing `q·C`; and `|S_q|` is the number of primes of `C` over `q`.  The fundamental
identity applied to `E ⊆ L` gives `|S_q| * e(q|p) * f(q|p) = |H|`, whence the count is
`e(P|p) f(P|p) / (e(q|p) f(q|p)) = e(q|p) f(q|p)` by multiplicativity of `e` and `f` along
`A ⊆ B ⊆ C`.

Note that this argument never uses that `P` lies over `q` (only over `p`); the count is the same
for every prime `P` of the integral closure `C` above `p`, as it must be, since `Gal(L/K)` permutes
them. -/
theorem card_embeddings_prime_over {A : Type u} [CommRing A] [IsDedekindDomain A]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    {E : Type u} [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E]
    {L : Type u} [Field L] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A E L] [FiniteDimensional K L] [IsGalois K L]
    {B : Type u} [CommRing B] [IsDomain B] [Algebra A B] [Algebra B E] [IsScalarTower A B E]
    [IsIntegralClosure B A E]
    {C : Type u} [CommRing C] [IsDomain C] [Algebra A C] [Algebra C L] [IsScalarTower A C L]
    [IsIntegralClosure C A L]
    [Algebra B C] [IsScalarTower A B C]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (P : Ideal C) [P.IsPrime] [P.LiesOver p] :
    Nat.card {σ : E →ₐ[K] L // ∀ x ∈ q,
        ∃ c ∈ P, algebraMap C L c = σ (algebraMap B E x)}
      = q.ramificationIdx A * q.inertiaDeg A := by
  let Tpred : (E →ₐ[K] L) → Prop := fun σ => ∀ x ∈ q, ∃ c ∈ P, algebraMap C L c = σ (algebraMap B E x)
  change Nat.card {σ : E →ₐ[K] L // Tpred σ} = q.ramificationIdx A * q.inertiaDeg A
  -- ============================= setup =============================
  let j : B →ₐ[A] C := galRestrict' A B C (IsScalarTower.toAlgHom K E L)
  have hj : ∀ x : B, algebraMap C L (j x) = algebraMap E L (algebraMap B E x) := fun x => by
    rw [algebraMap_galRestrict'_apply]; rfl
  haveI hsep : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  haveI hdedB : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K E B
  haveI hIntAB : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A E
  haveI hIntAC : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  have hfB : IsFractionRing B E := IsIntegralClosure.isFractionRing_of_finite_extension A K E B
  have hfC : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  letI algBC : Algebra B C := j.toRingHom.toAlgebra
  have hBC : ∀ x : B, algebraMap B C x = j x := fun x => by
    rw [RingHom.algebraMap_toAlgebra]; rfl
  haveI stABC : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hBC, j.commutes]
  letI algBL : Algebra B L := ((algebraMap C L).comp j.toRingHom).toAlgebra
  have hBL : ∀ x : B, algebraMap B L x = algebraMap C L (j x) := fun x => by
    rw [RingHom.algebraMap_toAlgebra]; rfl
  haveI stBCL : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hBL, hBC]
  haveI stABL : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hBL, j.commutes, IsScalarTower.algebraMap_apply A C L]
  haveI stBEL : IsScalarTower B E L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hBL, hj]
  haveI hIC : IsIntegralClosure C B L := IsIntegralClosure.tower_top (R := A) (A := B) (B := L) (C := C)
  haveI hIntBC : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  haveI hgalEL : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  letI hMSA : MulSemiringAction (Gal(L/E)) C := IsIntegralClosure.MulSemiringAction B E L C
  haveI hgalGC : IsGaloisGroup (Gal(L/E)) B C := IsGaloisGroup.of_isFractionRing (Gal(L/E)) B C E L
  -- ============================= rho, X =============================
  let Eimg : IntermediateField K L := (IsScalarTower.toAlgHom K E L).fieldRange
  let rho : Gal(L/K) → (E →ₐ[K] L) := fun g => (g : L →ₐ[K] L).comp (IsScalarTower.toAlgHom K E L)
  let X : Set (Gal(L/K)) :=
    {g | Ideal.map (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)) (q.map (algebraMap B C)) ≤ P}
  have hrho : ∀ a b : Gal(L/K), rho a = rho b ↔ a⁻¹ * b ∈ Eimg.fixingSubgroup := by
    intro a b
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y hy
      obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
      have hx : a (IsScalarTower.toAlgHom K E L x) = b (IsScalarTower.toAlgHom K E L x) := by
        have h1 := DFunLike.congr_fun h x
        simpa [rho, AlgHom.comp_apply] using h1
      show (a⁻¹ * b) (IsScalarTower.toAlgHom K E L x) = _
      rw [AlgEquiv.mul_apply, ← hx]
      exact AlgEquiv.symm_apply_apply a (IsScalarTower.toAlgHom K E L x)
    · intro h
      ext x
      have hx : (a⁻¹ * b) (IsScalarTower.toAlgHom K E L x) = IsScalarTower.toAlgHom K E L x :=
        h _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
      rw [AlgEquiv.mul_apply] at hx
      have h2 : b (IsScalarTower.toAlgHom K E L x) = a (IsScalarTower.toAlgHom K E L x) :=
        (AlgEquiv.apply_symm_apply a (b (IsScalarTower.toAlgHom K E L x))).symm.trans (congrArg a hx)
      simpa [rho, AlgHom.comp_apply] using h2.symm
  have hXstab : ∀ g ∈ X, ∀ h ∈ Eimg.fixingSubgroup, g * h ∈ X := by
    intro g hg h hh
    change Ideal.map (((galRestrict A K L C (g * h) : C →ₐ[A] C) : C →+* C)) (q.map (algebraMap B C)) ≤ P
    have hgal : ((galRestrict A K L C (g * h) : C →ₐ[A] C) : C →+* C) =
        (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)).comp
          (((galRestrict A K L C h : C →ₐ[A] C) : C →+* C)) := by
      ext x
      rw [RingHom.comp_apply]
      change (galRestrict A K L C (g * h) : C →ₐ[A] C) x
        = (galRestrict A K L C g : C →ₐ[A] C) ((galRestrict A K L C h : C →ₐ[A] C) x)
      rw [map_mul]
      exact AlgEquiv.mul_apply _ _ x
    have hfix : Ideal.map (((galRestrict A K L C h : C →ₐ[A] C)) : C →+* C) (q.map (algebraMap B C))
        = q.map (algebraMap B C) := by
      have hcomp : (((galRestrict A K L C h : C →ₐ[A] C) : C →+* C)).comp (algebraMap B C)
          = (algebraMap B C : B →+* C) := by
        ext b
        rw [RingHom.comp_apply]
        apply IsIntegralClosure.algebraMap_injective (A := C) (R := A) (B := L)
        change (algebraMap C L) ((galRestrict A K L C h) (algebraMap B C b)) = (algebraMap C L) (algebraMap B C b)
        rw [algebraMap_galRestrict_apply]
        rw [show (algebraMap C L) (algebraMap B C b) = algebraMap E L (algebraMap B E b) from by
          rw [← IsScalarTower.algebraMap_apply B C L, hBL, hj]]
        exact (IntermediateField.mem_fixingSubgroup_iff Eimg h).mp hh _
          (AlgHom.mem_fieldRange.mpr ⟨algebraMap B E b, rfl⟩)
      rw [Ideal.map_map (algebraMap B C) (((galRestrict A K L C h : C →ₐ[A] C)) : C →+* C), hcomp]
    change Ideal.map (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)) (q.map (algebraMap B C)) ≤ P at hg
    rw [hgal]
    rw [← Ideal.map_map (((galRestrict A K L C h : C →ₐ[A] C)) : C →+* C)
        (((galRestrict A K L C g : C →ₐ[A] C)) : C →+* C), hfix]
    exact hg
  -- ============== embedding of E extends to Gal(L/K) ==============
  let ext (σ : E →ₐ[K] L) : Gal(L/K) :=
    AlgEquiv.ofBijective (σ.liftNormal L) (AlgHom.normal_bijective K L L _)
  have ext_apply : ∀ (σ : E →ₐ[K] L) (x : E), ext σ (algebraMap E L x) = σ x := fun σ x => by
    show (σ.liftNormal L) (algebraMap E L x) = σ x
    rw [AlgHom.liftNormal_commutes]; rfl
  have rho_ext : ∀ σ : E →ₐ[K] L, rho (ext σ) = σ := fun σ => by
    ext x; exact ext_apply σ x
  -- ============== the key rewriting of the ideal containment ==============
  have hmap_gen : ∀ (σ : E →ₐ[K] L) (g : Gal(L/K)),
      (∀ x : E, g (algebraMap E L x) = σ x) →
      Ideal.map (((galRestrict' A B C σ : B →ₐ[A] C) : B →+* C)) q
        = Ideal.map (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)) (q.map (algebraMap B C)) := by
    intro σ g hg
    have hgr : galRestrict' A B C σ = (galRestrict A K L C g : C →ₐ[A] C).comp j := by
      have h1 : g.toAlgHom.comp (IsScalarTower.toAlgHom K E L) = σ := by
        ext x; exact hg x
      rw [← h1, galRestrict'_comp (A := A) (K := K) (L := E) (L₂ := L) (L₃ := L) (B := B) (B₂ := C) (B₃ := C)
          (σ := IsScalarTower.toAlgHom K E L) (σ' := g.toAlgHom)]
      ext x
      rw [AlgHom.comp_apply, AlgHom.comp_apply]
      rw [show galRestrict' A B C (IsScalarTower.toAlgHom K E L) = j from rfl]
      rw [coe_galRestrict_apply, galRestrictHom_apply]
    have hgr2 : (((galRestrict' A B C σ : B →ₐ[A] C)) : B →+* C)
        = (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)).comp (((j : B →ₐ[A] C)) : B →+* C) := by
      rw [hgr]; rfl
    have hjring : (((j : B →ₐ[A] C)) : B →+* C) = algebraMap B C := by
      ext b; exact (hBC b).symm
    rw [hgr2, ← Ideal.map_map (((j : B →ₐ[A] C)) : B →+* C)
        (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)), hjring]
  -- ============== T is the image of X under rho ==============
  have hTpred : ∀ σ : E →ₐ[K] L, Tpred σ ↔ σ ∈ rho '' X := by
    intro σ
    constructor
    · intro h
      refine ⟨ext σ, ?_, rho_ext σ⟩
      change Ideal.map (((galRestrict A K L C (ext σ) : C →ₐ[A] C) : C →+* C)) (q.map (algebraMap B C)) ≤ P
      rw [← hmap_gen σ (ext σ) (fun x => ext_apply σ x)]
      exact (mem_condition_iff_map_le (A := A) q P σ).mp h
    · rintro ⟨g, hg, rfl⟩
      change (∀ x ∈ q, ∃ c ∈ P, algebraMap C L c = (rho g) (algebraMap B E x))
      rw [mem_condition_iff_map_le (A := A) q P (rho g)]
      rw [hmap_gen (rho g) g (fun x => rfl)]
      change Ideal.map (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)) (q.map (algebraMap B C)) ≤ P at hg
      exact hg
  -- ============== |T| * |H| = |X| ==============
  have hcard1 : Nat.card {σ : E →ₐ[K] L // Tpred σ} = Nat.card (rho '' X) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun σ => hTpred σ))
  have hcard2 : Nat.card X = Nat.card (rho '' X) * Nat.card Eimg.fixingSubgroup :=
    card_eq_card_image_mul_card Eimg.fixingSubgroup rho hrho X hXstab
  -- ============== |X| = |S_q| * |D| ==============
  haveI hfinG : Finite (Gal(L/K)) := inferInstance
  haveI hfinAC : Module.Finite A C := IsIntegralClosure.finite A K L C
  letI hMSAC : MulSemiringAction (Gal(L/K)) C := IsIntegralClosure.MulSemiringAction A K L C
  haveI hgalGAC : IsGaloisGroup (Gal(L/K)) A C := IsGaloisGroup.of_isFractionRing (Gal(L/K)) A C K L
  haveI hfinPC : Fintype (primesOver p C) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  let Pq : primesOver p C := primesOver.mk p P
  let S_q : Set (primesOver p C) := {Q | Ideal.map (algebraMap B C) q ≤ Q.1}
  haveI hpretrans : MulAction.IsPretransitive (Gal(L/K)) (primesOver p C) :=
    Ideal.isPretransitive_of_isGaloisGroup p (Gal(L/K))
  have hSqorbit : ∀ Q ∈ S_q, Q ∈ MulAction.orbit (Gal(L/K)) Pq := by
    intro Q _
    rw [MulAction.mem_orbit_iff]
    exact MulAction.IsPretransitive.exists_smul_eq Pq Q
  have hcomap : ∀ g : Gal(L/K),
      (g⁻¹ • Pq).1 = Ideal.comap (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)) P := by
    intro g
    have hgm : (g⁻¹ • Pq).1
        = Ideal.map (((galRestrict A K L C g⁻¹ : C →ₐ[A] C) : C →+* C)) P := rfl
    have hcomp2 : (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)).comp
        (((galRestrict A K L C g⁻¹ : C →ₐ[A] C) : C →+* C)) = 1 := by
      ext y
      rw [RingHom.comp_apply]
      change (galRestrict A K L C g) ((galRestrict A K L C g⁻¹) y) = y
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    rw [hgm]
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap]
      have hmem := Ideal.mem_map_of_mem (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)) hx
      rw [Ideal.map_map, hcomp2] at hmem
      rw [show (1 : C →+* C) = RingHom.id C from rfl, Ideal.map_id] at hmem
      simpa using hmem
    · intro x hx
      rw [Ideal.mem_comap] at hx
      have hgx : (galRestrict A K L C g⁻¹) ((galRestrict A K L C g) x) = x := by
        rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]
      rw [← hgx]
      exact Ideal.mem_map_of_mem _ hx
  have hXeq : X = (fun g : Gal(L/K) => g⁻¹ • Pq) ⁻¹' S_q := by
    ext g
    rw [Set.mem_preimage]
    change (Ideal.map (((galRestrict A K L C g : C →ₐ[A] C) : C →+* C)) (q.map (algebraMap B C)) ≤ P)
      ↔ (Ideal.map (algebraMap B C) q ≤ (g⁻¹ • Pq).1)
    rw [hcomap g, Ideal.map_le_iff_le_comap]
  have hcard3 : Nat.card X = Nat.card S_q * Nat.card (MulAction.stabilizer (Gal(L/K)) Pq) := by
    rw [hXeq]
    refine (Nat.card_congr ?_).trans (card_preimage_smul_eq Pq S_q hSqorbit)
    exact Equiv.subtypeEquiv (Equiv.inv (Gal(L/K))) (fun g => by
      rw [Set.mem_preimage, Set.mem_preimage, Equiv.inv_apply])
  -- ============== injectivity / torsion-freeness / flatness ==============
  have hinjAL : Function.Injective (algebraMap A L) := fun a b hab =>
    IsFractionRing.injective A K (FaithfulSMul.algebraMap_injective K L (by
      rw [← IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply A K L]
      exact hab))
  have hinjAE : Function.Injective (algebraMap A E) := fun a b hab =>
    IsFractionRing.injective A K (FaithfulSMul.algebraMap_injective K E (by
      rw [← IsScalarTower.algebraMap_apply A K E, ← IsScalarTower.algebraMap_apply A K E]
      exact hab))
  have hinjAB : Function.Injective (algebraMap A B) := fun a b hab => hinjAE (by
    rw [IsScalarTower.algebraMap_apply A B E, IsScalarTower.algebraMap_apply A B E]
    exact congr_arg (algebraMap B E) hab)
  have hinjAC : Function.Injective (algebraMap A C) := fun a b hab => hinjAL (by
    rw [IsScalarTower.algebraMap_apply A C L, IsScalarTower.algebraMap_apply A C L]
    exact congr_arg (algebraMap C L) hab)
  have hinjBC : Function.Injective (algebraMap B C) := fun a b hab =>
    IsIntegralClosure.algebraMap_injective B A E (FaithfulSMul.algebraMap_injective E L (by
      rw [← IsScalarTower.algebraMap_apply B E L, ← IsScalarTower.algebraMap_apply B E L]
      rw [IsScalarTower.algebraMap_apply B C L a, IsScalarTower.algebraMap_apply B C L b]
      exact congr_arg (algebraMap C L) hab))
  haveI hTFAC : Module.IsTorsionFree A C := by
    refine ⟨fun r hr => fun x y hxy => ?_⟩
    change r • x = r • y at hxy
    rw [Algebra.smul_def, Algebra.smul_def] at hxy
    exact mul_left_cancel₀ (fun h => hr.ne_zero (hinjAC (by rw [h, map_zero]))) hxy
  haveI hTFAB : Module.IsTorsionFree A B := by
    refine ⟨fun r hr => fun x y hxy => ?_⟩
    change r • x = r • y at hxy
    rw [Algebra.smul_def, Algebra.smul_def] at hxy
    exact mul_left_cancel₀ (fun h => hr.ne_zero (hinjAB (by rw [h, map_zero]))) hxy
  haveI hTFBC : Module.IsTorsionFree B C := by
    refine ⟨fun r hr => fun x y hxy => ?_⟩
    change r • x = r • y at hxy
    rw [Algebra.smul_def, Algebra.smul_def] at hxy
    exact mul_left_cancel₀ (fun h => hr.ne_zero (hinjBC (by rw [h, map_zero]))) hxy
  haveI hFlatAC : Module.Flat A C := inferInstance
  haveI hFlatBC : Module.Flat B C := inferInstance
  haveI hfinBC : Module.Finite B C := Module.Finite.of_restrictScalars_finite A B C
  -- ============== S_q vs primesOver q C ==============
  have hmemS : ∀ Q : primesOver p C, Q ∈ S_q ↔ Q.1 ∈ primesOver q C := by
    intro Q
    haveI hQp : Q.1.IsPrime := Q.2.1
    have hle : (Q ∈ S_q) ↔ q ≤ Q.1.comap (algebraMap B C) := by
      change Ideal.map (algebraMap B C) q ≤ Q.1 ↔ _
      rw [Ideal.map_le_iff_le_comap]
    rw [hle]
    have heq : q ≤ Q.1.comap (algebraMap B C) ↔ Q.1.comap (algebraMap B C) = q := by
      constructor
      · intro h
        by_cases hq0 : q = ⊥
        · have hp0 : p = ⊥ := by
            rw [q.over_def p, hq0, Ideal.under_def,
              Ideal.comap_bot_of_injective (algebraMap A B) hinjAB]
          have hr0 : Q.1.comap (algebraMap B C) = ⊥ := by
            have hmem : Q.1.comap (algebraMap B C) ∈ primesOver (⊥ : Ideal A) B := by
              refine ⟨Ideal.IsPrime.comap (algebraMap B C), ?_⟩
              rw [Ideal.liesOver_iff]
              change (⊥ : Ideal A) = (Q.1.comap (algebraMap B C)).comap (algebraMap A B)
              rw [Ideal.comap_comap (algebraMap A B) (algebraMap B C),
                ← IsScalarTower.algebraMap_eq A B C]
              rw [show (Q.1).comap (algebraMap A C) = p from
                ((Ideal.liesOver_iff Q.1 p).mp Q.2.2).symm]
              exact hp0.symm
            rwa [Ideal.primesOver_bot A B] at hmem
          rw [hr0, hq0]
        · exact ((Ideal.IsPrime.isMaximal ‹q.IsPrime› hq0).eq_of_le
            (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap (algebraMap B C))) h).symm
      · intro h; rw [h]
    rw [heq]
    exact ⟨fun h => ⟨hQp, (Ideal.liesOver_iff Q.1 q).mpr h.symm⟩,
      fun h => ((Ideal.liesOver_iff Q.1 q).mp h.2).symm⟩
  have hSqcard : Nat.card S_q = (primesOver q C).ncard := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun Q : S_q => (⟨Q.1.1, (hmemS Q.1).mp Q.2⟩ : primesOver q C)) ⟨?_, ?_⟩)
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congr_arg (fun x : primesOver q C => x.1) hab))
    · intro b
      refine ⟨⟨⟨b.1, b.2.1, LiesOver.trans b.1 q p⟩, (hmemS ⟨b.1, b.2.1, LiesOver.trans b.1 q p⟩).mpr b.2⟩, ?_⟩
      rfl
  -- ============== fundamental identity for L/E ==============
  haveI hgalEL2 : IsGalois E L := hgalEL
  haveI hfinEL : Module.Finite E L := Module.Finite.of_restrictScalars_finite K E L
  have hfinrank : Module.finrank E L = Module.finrank Eimg L := by
    have ht1 : Module.finrank K E * Module.finrank E L = Module.finrank K L :=
      Module.finrank_mul_finrank K E L
    have ht2 : Module.finrank K Eimg * Module.finrank Eimg L = Module.finrank K L :=
      Module.finrank_mul_finrank K Eimg L
    have hKE : Module.finrank K E = Module.finrank K Eimg :=
      LinearEquiv.finrank_eq (AlgEquiv.toLinearEquiv (AlgHom.equivFieldRange (IsScalarTower.toAlgHom K E L)))
    have hpos : 0 < Module.finrank K E := Module.finrank_pos
    have hkey : Module.finrank K E * Module.finrank E L = Module.finrank K E * Module.finrank Eimg L := by
      rw [ht1, ← ht2, hKE]
    exact Nat.mul_left_cancel hpos hkey
  have hE : (primesOver q C).ncard * (q.ramificationIdxIn C * q.inertiaDegIn C)
      = Nat.card Eimg.fixingSubgroup := by
    rw [Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn q C (Gal(L/E))]
    rw [IsGalois.card_aut_eq_finrank E L, hfinrank]
    exact (IsGaloisGroup.card_fixingSubgroup_eq_finrank (Gal(L/K)) K L Eimg).symm
  -- ============== |Stab(P)| = e(q|p) * f(q|p) ==============
  have hDval : Nat.card (MulAction.stabilizer (Gal(L/K)) Pq)
      = P.ramificationIdx A * P.inertiaDeg A := by
    have hker : Nat.card (Gal(L/K))
        = (primesOver p C).ncard * Nat.card (MulAction.stabilizer (Gal(L/K)) Pq) := by
      rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Gal(L/K)) Pq), Nat.card_prod]
      congr 1
      rw [MulAction.orbit_eq_univ]
      exact Nat.card_congr (Equiv.Set.univ (primesOver p C))
    have hfib := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p C (Gal(L/K))
    have hpos : (primesOver p C).ncard ≠ 0 :=
      ((Set.ncard_pos).mpr (⟨Pq, Pq.2⟩ : (primesOver p C).Nonempty)).ne'
    have hN : Nat.card (MulAction.stabilizer (Gal(L/K)) Pq)
        = p.ramificationIdxIn C * p.inertiaDegIn C := by
      have h1 : (primesOver p C).ncard * Nat.card (MulAction.stabilizer (Gal(L/K)) Pq)
          = (primesOver p C).ncard * (p.ramificationIdxIn C * p.inertiaDegIn C) := by
        rw [← hker, hfib]
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hpos) h1
    rw [hN, Ideal.ramificationIdxIn_eq_ramificationIdx p P (Gal(L/K)),
        Ideal.inertiaDegIn_eq_inertiaDeg p P (Gal(L/K))]
  -- ============== the ratio ==============
  haveI hQne : Nonempty (primesOver q C) := Ideal.nonempty_primesOver q
  let Q : primesOver q C := Classical.choice hQne
  haveI hQlp : Q.1.LiesOver p := LiesOver.trans Q.1 q p
  haveI hQE : Finite (Gal(L/E)) := Finite.of_fintype _
  have hQtower_r := Ideal.ramificationIdx_tower (R := A) (S := B) (T := C) q Q.1
  have hQtower_f := Ideal.inertiaDeg_tower (R := A) (S := B) (T := C) q Q.1
  have hPQ_r : P.ramificationIdx A = Q.1.ramificationIdx A :=
    Ideal.ramificationIdx_eq_of_isGaloisGroup p P Q.1 (Gal(L/K))
  have hPQ_f : P.inertiaDeg A = Q.1.inertiaDeg A :=
    Ideal.inertiaDeg_eq_of_isGaloisGroup p P Q.1 (Gal(L/K))
  have hQB_r : Q.1.ramificationIdx B = q.ramificationIdxIn C :=
    (Ideal.ramificationIdxIn_eq_ramificationIdx q Q.1 (Gal(L/E))).symm
  have hQB_f : Q.1.inertiaDeg B = q.inertiaDegIn C :=
    (Ideal.inertiaDegIn_eq_inertiaDeg q Q.1 (Gal(L/E))).symm
  have hDfac : Nat.card (MulAction.stabilizer (Gal(L/K)) Pq)
      = (q.ramificationIdx A * q.inertiaDeg A) * (q.ramificationIdxIn C * q.inertiaDegIn C) := by
    rw [hDval, hPQ_r, hPQ_f, hQtower_r, hQtower_f, hQB_r, hQB_f]
    ring
  -- ============== final arithmetic ==============
  have h1 : Nat.card {σ : E →ₐ[K] L // Tpred σ} * Nat.card Eimg.fixingSubgroup = Nat.card X := by
    rw [hcard1, hcard2]
  have h2 : Nat.card X = (q.ramificationIdx A * q.inertiaDeg A) * Nat.card Eimg.fixingSubgroup := by
    rw [hcard3, hSqcard, hDfac, ← hE]
    ring
  exact Nat.mul_right_cancel Nat.card_pos (h1.trans h2)



end Work.KeyLemma.Curve
