import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_level_index
import Submission.Work.SSGRoute.phi1_level_system
import Submission.Work.SSGRoute.phi1_level_limit
import Submission.Work.SSGRoute.phi1_class_level
import Submission.Work.SSGRoute.phi1_level_trivial_two
import Submission.Work.SSGRoute.phi0_realization_in
import Submission.Work.SSGRoute.pt_char_pTorsion
set_option synthInstance.maxHeartbeats 400000

/-!
# Descent of a `p`-torsion functional `Λ : V →+ A` to a compatible family of levels

Let `V = colim_L H²(Gal(L/k), 𝔽_p)` and `A = colim_L H²(Gal(L/k), C_L)` be the two level colimits
of `Submission/Work/SSGRoute/phi1_level_limit.lean` and
`Submission/Work/SSGRoute/phi1_class_level.lean`, over the finite Galois levels `K ≤ L ≤ Ω`.

This file proves the *class-field-theoretic* half of the realisation step: an additive map
`Λ : V →+ A` with `p`-torsion values is induced by a **compatible family** of levelwise maps
`lam L : H²(Gal(L/k), 𝔽_p) →+ H²(Gal(L/k), C_L)` which are `p`-torsion valued:

* `classLevelMap_pTorsion_surj'` — at levels with `p ∣ [L : k]`, every `p`-torsion class of a higher
  level is the inflation of a `p`-torsion class of `L` (both `p`-torsion subgroups are cyclic of
  order `p` by `Work.SSGRoute.pt_char_pTorsion`, and inflation is injective by
  `Work.SSGRoute.classLevelMap_injective`);
* `exists_classLevel_of_pTorsion` — every `p`-torsion element of the colimit `A` is the image of a
  `p`-torsion element at any level `L` with `p ∣ [L : k]`;
* `descentLam`, with the characterisation `dFun_mem` and the uniqueness `dFun_unique`:
  `lam L x` is the *unique* `p`-torsion `w ∈ H²(Gal(L/k), C_L)` with
  `ofA_L w = Λ (ofV_L x)`; injectivity of `ofA_L` (`ClassLevelLimit.of_injective`) gives uniqueness.
-/

namespace Work.SSGRoute

namespace LF

open SSGRoute.PTExt CategoryTheory

noncomputable section

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
  [IsScalarTower k K Ω]

/-! ## The `p`-torsion is realised at every level -/

/-- **Every `p`-torsion class of a higher level comes from the level `L`** (`p ∣ [L : k]`). -/
theorem classLevelMap_pTorsion_surj' (p : ℕ) [Fact p.Prime] (L L' : Lvl k K Ω) (h : L ≤ L')
    (hp : p ∣ Module.finrank k ↥L.1) (y : ClassLevel L') (hy : p • y = 0) :
    ∃ w : ClassLevel L, p • w = 0 ∧ classLevelMap (k := k) L L' h w = y := by
  letI : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower k ↥L.1 ↥L'.1 := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Free ↥L.1 ↥L'.1 := Module.Free.of_divisionRing _ _
  have hp' : p ∣ Module.finrank k ↥L'.1 :=
    dvd_trans hp (Module.finrank_dvd_finrank_right (F := k) (K := ↥L.1) (A := ↥L'.1))
  obtain ⟨P, χ, hP, hχ⟩ := pt_char_pTorsion p k K ↥L.1 hp
  obtain ⟨P', χ', hP', hχ'⟩ := pt_char_pTorsion p k K ↥L'.1 hp'
  -- the restriction of the inflation to the `p`-torsion subgroups
  let f : P → P' := fun w => ⟨classLevelMap (k := k) L L' h (w : ClassLevel L),
    (hP' _).mpr (by rw [← map_nsmul, (hP _).mp w.2, map_zero])⟩
  have hf_inj : Function.Injective f := by
    intro w₁ w₂ hw
    apply Subtype.ext
    exact classLevelMap_injective L L' h (Subtype.ext_iff.mp hw)
  have hcard_P : Nat.card P = p := by
    rw [Nat.card_congr (Equiv.ofBijective χ hχ), Nat.card_eq_fintype_card, ZMod.card]
  have hcard_P' : Nat.card P' = p := by
    rw [Nat.card_congr (Equiv.ofBijective χ' hχ'), Nat.card_eq_fintype_card, ZMod.card]
  haveI : Finite P' := (Equiv.ofBijective χ' hχ').finite_iff.mpr inferInstance
  have hsurj : Function.Surjective f :=
    (hf_inj.bijective_of_nat_card_le (by rw [hcard_P, hcard_P'])).2
  obtain ⟨w, hw⟩ := hsurj ⟨y, (hP' _).mpr hy⟩
  exact ⟨w, (hP _).mp w.2, congrArg Subtype.val hw⟩

set_option maxHeartbeats 1000000 in
/-- **Every `p`-torsion element of `A` is the image of a `p`-torsion element at the level `L`**
(for `p ∣ [L : k]`). -/
theorem exists_classLevel_of_pTorsion (p : ℕ) [Fact p.Prime] (L : Lvl k K Ω)
    (hp : p ∣ Module.finrank k ↥L.1) (a : ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    (ha : p • a = 0) :
    ∃ w : ClassLevel L, p • w = 0 ∧ ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L w = a := by
  refine ClassLevelLimit.induction (k := k) (K := K) (Ω := Ω)
    (C := fun a => p • a = 0 → ∃ w : ClassLevel L, p • w = 0 ∧
      ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L w = a) ?_ a ha
  intro L' y hy
  -- `p • y` dies after inflation: pass to a higher level
  obtain ⟨L'', hL'', hz⟩ :=
    (ClassLevelLimit.of_eq_zero_iff (k := k) (K := K) (Ω := Ω) L' (p • y)).mp (by
      rw [map_nsmul, hy])
  have hy'' : p • classLevelMap (k := k) L' L'' hL'' y = 0 := by
    rw [← map_nsmul]
    exact hz
  -- an upper bound of `L` and `L''`
  obtain ⟨Lc, hLc, hLc'⟩ : ∃ Lc : Lvl k K Ω, L ≤ Lc ∧ L'' ≤ Lc :=
    exists_ge_ge L L''
  obtain ⟨w, hwp, hw⟩ := classLevelMap_pTorsion_surj' p L Lc hLc hp
    (classLevelMap (k := k) L'' Lc hLc' (classLevelMap (k := k) L' L'' hL'' y))
    (by rw [← map_nsmul, hy'', map_zero])
  refine ⟨w, hwp, ?_⟩
  rw [← ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hLc w, hw]
  rw [ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hLc'
    (classLevelMap (k := k) L' L'' hL'' y)]
  exact ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) hL'' y

/-! ## The descent -/

/-- The levelwise value of the descended family: the `p`-torsion preimage of `Λ (ofV_L x)`. -/
noncomputable def dFun (p : ℕ) [Fact p.Prime]
    (Λ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    (hΛ : ∀ v, p • Λ v = 0) (L : Lvl k K Ω) (x : LevelCoh p L) : ClassLevel L :=
  if hp : p ∣ Module.finrank k ↥L.1 then
    Classical.choose (exists_classLevel_of_pTorsion (k := k) (K := K) (Ω := Ω) p L hp
      (Λ (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x)) (hΛ _))
  else 0

/-- **The defining properties of the descended value.** -/
theorem dFun_mem (p : ℕ) [Fact p.Prime]
    (Λ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    (hΛ : ∀ v, p • Λ v = 0) (L : Lvl k K Ω) (x : LevelCoh p L) :
    p • dFun (k := k) (K := K) (Ω := Ω) p Λ hΛ L x = 0 ∧
      ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (dFun (k := k) (K := K) (Ω := Ω) p Λ hΛ L x)
        = Λ (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x) := by
  unfold dFun
  split_ifs with hp
  · exact Classical.choose_spec (exists_classLevel_of_pTorsion (k := k) (K := K) (Ω := Ω) p L hp
      (Λ (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x)) (hΛ _))
  · have hp' : ¬ p ∣ Nat.card (↥L.1 ≃ₐ[k] ↥L.1) := by
      intro hc
      exact hp (by rwa [IsGalois.card_aut_eq_finrank k ↥L.1] at hc)
    haveI : Subsingleton (LevelCoh p L) :=
      subsingleton_extH_trivial_two_of_not_dvd_card p (G := ↥L.1 ≃ₐ[k] ↥L.1) hp'
    have hx : x = 0 := Subsingleton.elim x 0
    rw [hx]
    exact ⟨smul_zero p, by rw [map_zero, map_zero, map_zero]⟩

/-- **Uniqueness of the `p`-torsion preimage.** -/
theorem dFun_unique (p : ℕ) [Fact p.Prime]
    (Λ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    (hΛ : ∀ v, p • Λ v = 0) (L : Lvl k K Ω) (x : LevelCoh p L) (w : ClassLevel L)
    (hw : p • w = 0)
    (hw' : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L w
        = Λ (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x)) :
    w = dFun (k := k) (K := K) (Ω := Ω) p Λ hΛ L x :=
  (ClassLevelLimit.of_injective (k := k) (K := K) (Ω := Ω) L) (by
    rw [hw', (dFun_mem (k := k) (K := K) (Ω := Ω) p Λ hΛ L x).2])

/-- **The descended compatible family.** -/
noncomputable def descentLam (p : ℕ) [Fact p.Prime]
    (Λ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    (hΛ : ∀ v, p • Λ v = 0) (L : Lvl k K Ω) : LevelCoh p L →+ ClassLevel L where
  toFun := dFun (k := k) (K := K) (Ω := Ω) p Λ hΛ L
  map_zero' := by
    rw [← dFun_unique (k := k) (K := K) (Ω := Ω) p Λ hΛ L 0 (0 : ClassLevel L) (smul_zero p)
      (by rw [map_zero, map_zero, map_zero])]
  map_add' x y := by
    rw [← dFun_unique (k := k) (K := K) (Ω := Ω) p Λ hΛ L (x + y)
      (dFun (k := k) (K := K) (Ω := Ω) p Λ hΛ L x
        + dFun (k := k) (K := K) (Ω := Ω) p Λ hΛ L y)
      (by rw [smul_add, (dFun_mem (k := k) (K := K) (Ω := Ω) p Λ hΛ L x).1,
        (dFun_mem (k := k) (K := K) (Ω := Ω) p Λ hΛ L y).1, add_zero])
      (by rw [map_add, (dFun_mem (k := k) (K := K) (Ω := Ω) p Λ hΛ L x).2,
        (dFun_mem (k := k) (K := K) (Ω := Ω) p Λ hΛ L y).2, ← map_add, ← map_add])]

/-- The defining properties of `descentLam`. -/
theorem descentLam_mem (p : ℕ) [Fact p.Prime]
    (Λ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    (hΛ : ∀ v, p • Λ v = 0) (L : Lvl k K Ω) (x : LevelCoh p L) :
    p • descentLam (k := k) (K := K) (Ω := Ω) p Λ hΛ L x = 0 ∧
      ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (descentLam (k := k) (K := K) (Ω := Ω) p Λ hΛ L x)
        = Λ (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x) :=
  dFun_mem (k := k) (K := K) (Ω := Ω) p Λ hΛ L x

/-- Uniqueness for `descentLam`. -/
theorem descentLam_unique (p : ℕ) [Fact p.Prime]
    (Λ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    (hΛ : ∀ v, p • Λ v = 0) (L : Lvl k K Ω) (x : LevelCoh p L) (w : ClassLevel L)
    (hw : p • w = 0)
    (hw' : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L w
        = Λ (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L x)) :
    w = descentLam (k := k) (K := K) (Ω := Ω) p Λ hΛ L x :=
  dFun_unique (k := k) (K := K) (Ω := Ω) p Λ hΛ L x w hw hw'

end

end LF

end Work.SSGRoute
