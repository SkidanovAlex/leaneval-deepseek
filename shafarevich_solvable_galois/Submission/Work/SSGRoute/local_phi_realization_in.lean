import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.E4R3.inflC_injective
import Submission.Work.SSGRoute.E7cOmega.lam_zero_of_no_p_dvd_level
import Submission.Work.SSGRoute.Sha2Lib.clause3_of_detector
import Submission.Work.SSGRoute.Sha2Lib.pt_core_assembly
import Submission.Work.SSGRoute.e7comega_S
import Submission.Work.SSGRoute.e9c_transport_unram
import Submission.Work.SSGRoute.exists_finset_unramifiedPlaces
import Submission.Work.SSGRoute.ext_localUnits_finite
import Submission.Work.SSGRoute.phiAt_extToClasses_eq
import Submission.Work.SSGRoute.unramifiedDetector_closed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_FIX.md, INCLUDING its final addendum on E7c-Ω. A previous prover declared this statement FALSE with a ℚ counterexample (v=1 only at ℚ(√5), w=3). That counterexample is INVALID: its family is not additive. At level ℚ(√5,√11), additivity gives lam(χ₅+χ₁₁)=1, but χ₅+χ₁₁ is inflated from ℚ(√55), where 3 splits, so hloc and hcompat force 0. Step 1 of the proof is exactly this: additivity + hcompat + hloc at compositum levels force lam to depend only on the restriction to D_w. Definitions: PTDefs.lean + PTDefsOmega.lean (do NOT edit).

**E7cΩ `local_phi_realization_in`**
- The E7c content with `Ω`-levels.
- Replaces E7c. **Cancel the old E7c** unless its agent re-targets to E7cΩ.
- Size: 0.8–1.5k.

**Unchanged:** E0b, E0c (PROVED), E1a–c, E2, E7a, E7b, E8′, E9.

The exact Lean texts are the `.lean` files next to this note. For reference, the heart of the new
vocabulary and of E5s:

```lean
def PhiOneVanishesIn [FiniteDimensional k K] [IsGalois k K] {M : Rep Coeff (K ≃ₐ[k] K)}
    (x : Abelian.Ext.{0} M (classesK k K) 1) : Prop :=
  ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (h : extH (Rep.res (galRes k K L) M) 1), phiAt (k := k) (K := K) (L := L) x h = 0

theorem phi1_mono_step_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (S : ShortComplex (Rep Coeff (K ≃ₐ[k] K))) (hS : S.ShortExact)
    (e : S.X₁ ≅ Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p))
    (hX₃ : ∀ z : Abelian.Ext S.X₃ (classesK k K) 1, PhiOneVanishesIn Ω z → z = 0)
    (x : Abelian.Ext S.X₂ (classesK k K) 1) (hx : PhiOneVanishesIn Ω x) : x = 0 := by exact Work.SSGRoute.phi1_mono_step_in p k K Ω ζ hζ S hS e hX₃ x hx
```

**Gotcha.** `NumberField ↥L` is not inferred for `L : IntermediateField K Ω` (`Ω` is not a number
field), so every `Ω`-level binder carries `[NumberField L]`. It is a `Prop` class, so this is
harmless.

## Summary

1. **E5 circularity: FALSE mathematically.** The extension `Λ` is linear algebra on the direct limit
   `V = colim H²(Gal(L/k), 𝔽_p)`, and `λ` is well defined thanks to injectivity of `inflC`. The
   agent's step lemma was over-general: it lacked `S.X₁ ≅ 𝔽_p` and the induction hypothesis on
   `S.X₃`.
2. **Real defect:** `PhiOneVanishes` / E4 / E7c families range over all *types*, so no colimit or
   choice is possible. Repaired by `PTDefsOmega` with `Ω`-indexed levels.
3. **E7b real-place counterexample: FALSE.** It violates `p ∣ |D_{w'}|` and confuses
   `H²(1, ℝˣ) = 0` with `Br(ℝ)`. E7b is unchanged; E7c changes only for (2).
4. **E9 unchanged.** It uses E6Ω and E7cΩ with `Ω = AlgebraicClosure K`.
5. **Lead places** `Submission/Work/SSGRoute/PTDefsOmega.lean`.
6. **Re-dispatch** E3→E3Ω, E5→E5s + E5Ω, E6→E6Ω and E7c→E7cΩ. The E3, E5 and E6 agents can simply
   re-target; old statements become ≤0.2k corollaries.
7. **Cancel** the old E4 and the old E7c, and H383's `phi_one_step_of_annihilates_ker_delta`.
   **Keep** E0b, E1a–c, E2, E7a, E7b, E8′ and E9.
8. **New total:** about 18–31k lines, +1k for E5s and the Ω glue.
9. **Risk:** unchanged, medium-high. E7b, E1a and the `Ω`-colimit bookkeeping (E5s/E9) are the
   heaviest. No design-level circularity remains.
10. **Feasibility:** the PT core still looks feasible. The problem-level risk remains
    `shafarevich_z_construction` Z4 (DESIGN_EXT §5), not the Ext core.

## Addendum: the E7cΩ "FALSE" verdict (report `lemma-SSGRoute_local_phi_realization_in.md`)

**Verdict on the verdict: the counterexample is invalid. E7cΩ stands unchanged, and no consumer
changes.**

**The proposed family.** `k = K = ℚ`, `p = 2`, `M = ℤ/2`, `w = 3`. The report defines
`lam_L h := infl(v_{F_h})`, where `F_h = L^{ker h}`, with `v_{ℚ(√5)} = 1` and `v_F = 0` otherwise.
This is **not additive**, and `lam L` is required to be `→+`. The failure shows at the level
`L' = ℚ(√5, √11)`:
- 3 is inert in `ℚ(√5)` (5 ≡ 2) and in `ℚ(√11)` (11 ≡ 2), and splits in `ℚ(√55)` (55 ≡ 1 mod 3).
- Additivity forces `lam(χ₅ + χ₁₁) = lam(χ₅) + lam(χ₁₁) = 1 + 0 = 1`. The report's rule gives
  `lam(χ₅₅) = 0` instead.
- The additive extension, with `lam(χ₅) = 1` and `lam(χ₁₁) = 0`, violates `hloc` at `L'`.
  - `L'/ℚ` is abelian, and 3 is unramified with Frobenius nontrivial on both quadratic subfields.
  - So every `D_{w'}` over 3 is the order-2 "diagonal" subgroup, on which `χ₅ + χ₁₁` vanishes.
  - `hloc` then demands `lam(χ₅ + χ₁₁) = 0`.

**The general principle.** Additivity, `hcompat` and `hloc` together already force local
determination: `lam` factors through a functional on the local `H¹(k_v, M)`.
- Suppose two classes at levels `L₁` and `L₂` have the same local restriction at `w`.
- Inflate both to the compositum. There the difference restricts to 0 on `D_{w''}`, since inflation
  `H¹(D) → H¹(k_v)` is injective.
- Vanishing of a restriction does not depend on which place over `w` is chosen: restrictions at
  conjugate places differ by the inner-conjugation isomorphism.
- `hloc` kills the difference, and `hcompat` transports the values.

So the "same bit at every inert level" is exactly what the hypotheses already imply. The report's
point that `lam` is "free across levels" overlooks the compositum levels.
-/

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-! ## Auxiliary facts feeding the reduction of `local_phi_realization_in`

### What is proved here (all complete)

* `inflCIn_injective_aux` — the level inflation `H²(Gal(L/k), C_L) → H²(Gal(L₀/k), C_{L₀})` along a
  level inclusion `L ≤ L₀` in a fixed `Ω` is injective (wrapper around the proved
  `Work.SSGRoute.SylowLevel.inflCIn_injective`).
* `phiAt_extToClasses_eq_of_le` — **clause 2 propagates downwards along levels**: if the pairing with
  `extToClasses z` reproduces `lam` at a level `L₀`, then it reproduces `lam` at every level
  `L ≤ L₀`.  This uses the level naturality `Work.SSGRoute.phiAt_level_infl` of the pairing,
  `hcompat`, and the injectivity above.  Consequently it suffices to produce `z` realising `lam` at
  *one* level of `Ω` that contains every other level of interest (e.g. a compositum of levels:
  composita of finite Galois intermediate fields of `Ω` are again finite Galois levels).
* `lam_eq_zero_of_extHRestrict_eq_zero` — **`hloc` upgraded to every place over `w`**: using the
  proved `Work.SSGRoute.lam_local_determination` (Step 1 below), `lam L` vanishes on the kernel of
  the restriction to the decomposition group of *any* place over `w`, not only of the witness
  produced by `hloc`.

### The state of the route (see `DESIGN_FIX.md` addendum and the lead's note of the `E7b` redesign)

1. **Step 1 (local determination).**  `lam L h` depends only on `res_{w'}(h)`; proved as
   `Work.SSGRoute.lam_local_determination`
   (`Submission/Work/SSGRoute/lam_local_determination.lean`), together with the conjugation-transfer
   `Work.SSGRoute.extHRestrict_conj_eq_zero` it rests on.
2. **Clause 2 at one level.**  This is where the arithmetic enters, and it is *not* available in this
   workspace:
   * **(C) the local realisation** (node `E7b`, `local_duality_ext_in`): every compatible `p`-torsion
     family of level-by-level *local* functionals is the Yoneda pairing with one class
     `y ∈ Ext¹_{D_w}(M, K_wˣ)`.  Per the lead's note, the intended consumption is through
     **clause (ii)** of `E7b` (realisation of every `p`-torsion functional at a level with
     `p ∣ |D_{w'}|`), plus the finiteness input `ext_localUnits_finite` (`F1`, finiteness of
     `Ext¹_{D_w}(M, K_wˣ)` for finite `p`-torsion `M`), plus a minimality argument choosing the
     level `L₀`; *clause (i)* is not needed.
   * **(D) the local–global cup formula** for the class formation: for `z` supported on the orbit of
     `w`, the class `phiAt (extToClasses z) h ∈ H²(Gal(L/k), C_L)` is the image of the local pairings
     `⟨extLoc_{w'} z, res_{w'} h⟩ ∈ Br(L_{w'}/k_v)` (`w' | w`) under the natural map
     `⊕_{w'|w} Br(L_{w'}/k_v) → H²(Gal(L/k), C_L)`; equivalently the (already proved, for idèle
     coefficients) computation pattern of `Work.SSGRoute.zeta_idele_class_pairing`, generalised from
     the `μ_p`-idèles to an arbitrary idèle class and an arbitrary finite `p`-torsion `M`.
   * Shapiro's decomposition `Work.SSGRoute.ext_idele_shapiro` (E2, proved) turns the local class `y`
     of (C) into `z ∈ Ext¹_G(M, 𝕀_K)` supported on the orbit of `w` (clause 1), and
     `Work.SSGRoute.brauer_single_place` (E8', proved) is the rigidity used off the orbit.
3. **The unramified clause** is the unramified half of local duality (`E7b` + the annihilator of the
   unramified classes), assembled with `IsUnramifiedExt`/`IsUnramifiedClassAt`.

-/

/-- **The transition maps of the class-group level system are injective**: inflation
`H²(Gal(L/k), C_L) → H²(Gal(L₀/k), C_{L₀})` along a level inclusion `L ≤ L₀` inside a fixed
algebraically closed `Ω` is injective.  This is the `Ω`-level form of
`Work.SSGRoute.SylowLevel.inflCIn_injective` (proved, complete, in
`Submission/Work/SSGRoute/sylow_infl_injective.lean`). -/
theorem inflCIn_injective_aux {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (L L₀ : IntermediateField K Ω) [NumberField L] [NumberField L₀]
    [FiniteDimensional k L] [FiniteDimensional k L₀] [IsGalois k L] [IsGalois k L₀]
    (h : L ≤ L₀) :
    Function.Injective (fun y : extH (classesK k L) 2 => inflCIn (k := k) h y) :=
  SylowLevel.inflCIn_injective (k := k) (K := K) (Ω := Ω) L L₀ h

/-- **Clause 2 propagates downwards along levels.**  If the pairing with the idèle class
`extToClasses z` reproduces the family `lam` at a level `L₀`, then it reproduces `lam` at every
level `L ≤ L₀`: `hcompat` compares the two values after inflation to `L₀`, the level naturality
`Work.SSGRoute.phiAt_level_infl` says that the pairing value inflates to the pairing value of the
inflated class, and `inflCIn_injective_aux` cancels the inflation. -/
theorem phiAt_extToClasses_eq_of_le {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K))
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.res (galRes k K L) M) 1 →+ extH (classesK k L) 2)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
      (hLL : L ≤ L') (h : extH (Rep.res (galRes k K L) M) 1),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflHIn (k := k) hLL h))
    (z : Abelian.Ext M (idelesK k K) 1)
    (L L₀ : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L₀] [FiniteDimensional k L₀] [IsGalois k L₀] (hLL : L ≤ L₀)
    (h₀ : ∀ h : extH (Rep.res (galRes k K L₀) M) 1,
      phiAt (k := k) (K := K) (L := L₀) (extToClasses z) h = lam L₀ h) :
    ∀ h : extH (Rep.res (galRes k K L) M) 1,
      phiAt (k := k) (K := K) (L := L) (extToClasses z) h = lam L h := by
  intro h
  have hnat := phiAt_level_infl (k := k) (K := K) (Ω := Ω) L L₀ hLL M (extToClasses z) h
  have hcom := hcompat L L₀ hLL h
  have key : inflCIn (k := k) hLL (phiAt (k := k) (K := K) (L := L) (extToClasses z) h)
      = inflCIn (k := k) hLL (lam L h) := by
    rw [hnat, h₀ (inflHIn (k := k) hLL h), ← hcom]
  exact inflCIn_injective_aux L L₀ hLL key


open SSGRoute.PTExt CategoryTheory


/-- **`hloc` upgraded to every place over `w`.**  By `Work.SSGRoute.lam_local_determination` (Step 1
of the route, proved) the family `lam L` vanishes on the kernel of the restriction to the
decomposition group of *any* place `w'` over `w`, not merely of the witness produced by `hloc`. -/
theorem lam_eq_zero_of_extHRestrict_eq_zero {p : ℕ} [Fact p.Prime] {k K Ω : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.res (galRes k K L) M) 1 →+ extH (classesK k L) 2)
    (hloc : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      ∃ w' : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w' w ∧
        ∀ h : extH (Rep.res (galRes k K L) M) 1,
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0 → lam L h = 0)
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (h : extH (Rep.res (galRes k K L) M) 1)
    (h0 : extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0) :
    lam L h = 0 := by
  have hzero : extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (0 : extH (Rep.res (galRes k K L) M) 1) = 0 := by
    simp only [extHRestrict]
    exact E6Util.extHMap_zero (MulAction.stabilizer (L ≃ₐ[k] L) w').subtype (𝟙 _)
  have hdet := lam_local_determination (p := p) (k := k) (K := K) (Ω := Ω) M w lam hloc
    L w' hw' h 0
  rw [hdet (by rw [h0, hzero]), map_zero]


/-! ## Generic `Ext`-calculus for the level pairing with idèle coefficients

The pairing value with *class-group* coefficients of a class pushed from the idèles is the
push-forward to `C_L` of an *idèle-valued* pairing value, and the latter localises at a place `w`
to the Yoneda product of the localisations (E2's localisation map `extLoc`).  This is the "idèle
lifting" glue through which the pairing with a class supported on the orbit of a place becomes
computable from local data.

The companion fact that `classIncl` factors through an idèle-level map `J : 𝕀_K → 𝕀_L` commuting
with the maps to the class groups (the hypothesis `hJ` of `Work.SSGRoute.phiAt_extToClasses_eq`) is
supplied by `Work.SSGRoute.exists_ideleIncl_level`; only *consequences* of `hJ` are recorded here,
for an arbitrary such `J`. -/

namespace LevelPair

/-- **`levelPair` in Yoneda form.** -/
theorem levelPair_eq_yonedaPair {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0, 0, 0} Coeff G} {B : Rep.{0, 0, 0} Coeff H} (ι : Rep.res f A ⟶ B)
    {r s : ℕ} (x : Abelian.Ext M A r) (h : extH (Rep.res f M) s) :
    levelPair f ι x h
      = yonedaPair ((extRes f x).comp (Abelian.Ext.mk₀ ι) (add_zero r)) h :=
  rfl

end LevelPair

/-- **Localisation of the idèle-valued pairing class.**  For any level map `J : 𝕀_K → 𝕀_L` of
`Gal(L/k)`-modules, a class `z ∈ Ext¹_G(M, 𝕀_K)` and `h ∈ H¹(Gal(L/k), M)`, the `w`-component of
the idèle-valued pairing value is the Yoneda product of the `w`-component of the pushed class with
the restriction of `h` to the decomposition group of `w`. -/
theorem extLoc_levelPair_eq (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (J : Rep.res (galRes k K L) (idelesK k K) ⟶ idelesK k L)
    {M : Rep Coeff (K ≃ₐ[k] K)} (z : Abelian.Ext M (idelesK k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) (w : NK.GlobalCFT.Place L) :
    extLoc (k := k) (K := L) w (levelPair (galRes k K L) J z h)
      = (extRes (decompK (k := k) (K := L) w).subtype h).comp
          (extLoc (k := k) (K := L) w ((extRes (galRes k K L) z).comp
            (Abelian.Ext.mk₀ J) (add_zero 1))) rfl := by
  rw [LevelPair.levelPair_eq_yonedaPair]
  rw [yonedaPair, extLoc, extRes, Abelian.Ext.mapExactFunctor_comp]
  exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _

/-- **The idèle-valued pairing class vanishes if the local data do.**

If the pushed class `Z = J_*(z) ∈ Ext¹_{Gal(L/k)}(res M, 𝕀_L)` localises to `0` at every place outside
the `Gal(L/k)`-orbit of a place `w₀` of `L`, and `h` has vanishing restriction to the decomposition
group of `w₀`, then the idèle-valued pairing value `levelPair galRes J z h` is zero.

The proof is E2's injectivity of localisation on `Ext²(ℤ, 𝕀_L)`: the `w`-component of the pairing
value is the Yoneda product of the two localisations (`extLoc_levelPair_eq`), which vanishes at the
places of the orbit (because `h` restricts to `0` there, and vanishing of the restriction is
invariant under conjugation) and off the orbit (because `Z` localises to `0` there). -/
theorem levelPair_eq_zero_of_support (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    (J : Rep.res (galRes k K L) (idelesK k K) ⟶ idelesK k L)
    {M : Rep Coeff (K ≃ₐ[k] K)} (z : Abelian.Ext M (idelesK k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) (w₀ : NK.GlobalCFT.Place L)
    (hz : ∀ w' : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w') →
      extLoc (k := k) (K := L) w' ((extRes (galRes k K L) z).comp
        (Abelian.Ext.mk₀ J) (add_zero 1)) = 0)
    (hh : extHRestrict (decompK (k := k) (K := L) w₀) h = 0) :
    levelPair (galRes k K L) J z h = 0 := by
  obtain ⟨R, hR⟩ := Sha2Lib.exists_transversal_of_mulAction (L ≃ₐ[k] L)
    (NK.GlobalCFT.Place L)
  refine (ext_idele_shapiro_aux (k := k) (K := L) (unitRep (L ≃ₐ[k] L))
    (by infer_instance) 2 R hR).1 _ (fun w _hw => ?_)
  rw [extLoc_levelPair_eq]
  by_cases hw : ∃ σ : L ≃ₐ[k] L, σ • w₀ = w
  · obtain ⟨σ, rfl⟩ := hw
    have hconj : extHRestrict (decompK (k := k) (K := L) (σ • w₀)) h = 0 := by
      rw [show decompK (k := k) (K := L) (σ • w₀) =
          (decompK (k := k) (K := L) w₀).map (MulAut.conj σ).toMonoidHom from
        MulAction.stabilizer_smul_eq_stabilizer_map_conj σ w₀]
      exact extHRestrict_conj_eq_zero (decompK (k := k) (K := L) w₀) σ h hh
    rw [Sha2Lib.extRes_eq_zero_of_extHRestrict_eq_zero
      (decompK (k := k) (K := L) (σ • w₀)) h hconj]
    simp
  · rw [hz w (fun σ hs => (not_exists.mp hw) σ hs)]
    simp


/-- **Additive maps defined on a submodule extend.**  Over a field every submodule is a direct
summand; composing with the projection onto the submodule along a complement extends a map defined
on it. -/
theorem exists_addMonoidHom_extend_of_submodule {p : ℕ} [Fact p.Prime] {A T : Type}
    [AddCommGroup A] [Module (ZMod p) A] [AddCommGroup T] (C : Submodule (ZMod p) A)
    (f : ↥C →+ T) : ∃ F : A →+ T, ∀ c : ↥C, F c = f c := by
  obtain ⟨D, hD⟩ := C.exists_isCompl
  exact ⟨f.comp (C.projectionOnto D hD).toAddMonoidHom,
    fun c => congrArg f (Submodule.projectionOnto_apply_left (p := C) (q := D) hD c)⟩

/-- **Additive maps defined on a subgroup of a `p`-torsion abelian group extend.**

If `A` is an abelian group with `p · a = 0` for all `a`, then `A` is an `𝔽_p`-vector space
(`AddCommGroup.zmodModule`) and every additive subgroup `C ≤ A` is a subspace, hence a direct
summand.  This is the algebraic input that lets a functional defined only on the image of the local
restriction — all that local determination gives — be extended to the whole local cohomology, so
that the local realisation input can be applied to it. -/
theorem exists_addHom_extend_of_pTorsion {p : ℕ} [Fact p.Prime] {A T : Type} [AddCommGroup A]
    [AddCommGroup T] (hpA : ∀ a : A, p • a = 0) (C : AddSubgroup A) (f : C →+ T) :
    ∃ F : A →+ T, ∀ c : C, F c = f c := by
  classical
  letI : Module (ZMod p) A := AddCommGroup.zmodModule hpA
  let C' : Submodule (ZMod p) A :=
    { carrier := (C : Set A), zero_mem' := C.zero_mem,
      add_mem' := fun hx hy => C.add_mem hx hy, smul_mem' := fun c x hx => zmod_smul_mem hx c }
  obtain ⟨F, hF⟩ := exists_addMonoidHom_extend_of_submodule (p := p) C' f
  exact ⟨F, fun c => hF c⟩


/-- **Additive maps defined on a submodule extend, preserving `p`-torsion values.** -/
theorem exists_addMonoidHom_extend_of_submodule' {p : ℕ} [Fact p.Prime] {A T : Type}
    [AddCommGroup A] [Module (ZMod p) A] [AddCommGroup T] (C : Submodule (ZMod p) A)
    (f : ↥C →+ T) (hf : ∀ c : ↥C, p • f c = 0) :
    ∃ F : A →+ T, (∀ c : ↥C, F c = f c) ∧ ∀ a : A, p • F a = 0 := by
  obtain ⟨D, hD⟩ := C.exists_isCompl
  refine ⟨f.comp (C.projectionOnto D hD).toAddMonoidHom, fun c => ?_, fun a => ?_⟩
  · exact congrArg f (Submodule.projectionOnto_apply_left (p := C) (q := D) hD c)
  · change p • f (C.projectionOnto D hD a) = 0
    exact hf _

/-- **Additive maps defined on a subgroup of a `p`-torsion abelian group extend, preserving
`p`-torsion values.** -/
theorem exists_addHom_extend_of_pTorsion' {p : ℕ} [Fact p.Prime] {A T : Type} [AddCommGroup A]
    [AddCommGroup T] (hpA : ∀ a : A, p • a = 0) (C : AddSubgroup A) (f : C →+ T)
    (hf : ∀ c : C, p • f c = 0) :
    ∃ F : A →+ T, (∀ c : C, F c = f c) ∧ ∀ a : A, p • F a = 0 := by
  classical
  letI : Module (ZMod p) A := AddCommGroup.zmodModule hpA
  let C' : Submodule (ZMod p) A :=
    { carrier := (C : Set A), zero_mem' := C.zero_mem,
      add_mem' := fun hx hy => C.add_mem hx hy, smul_mem' := fun c x hx => zmod_smul_mem hx c }
  obtain ⟨F, hF, hFp⟩ := exists_addMonoidHom_extend_of_submodule' (p := p) C' f hf
  exact ⟨F, fun c => hF c, hFp⟩

/-- **Injectivity of the one-orbit localisation, in `extToClasses` form.**  A class of
`H²(Gal(L/k), 𝕀_L)` supported off the `Gal(L/k)`-orbit of `w₀` and with vanishing class-group image
localises to `0` at `w₀` (this is `Work.SSGRoute.classLocIncl_injective`, i.e. Hasse–Brauer–Noether
at a single place together with the exactness of the class formation). -/
theorem extLoc_eq_zero_of_locTrivial_off_orbit (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (w₀ : NK.GlobalCFT.Place L) (q : extH (idelesK k L) 2)
    (hq : ∀ v : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ v) →
      extLoc (k := k) (K := L) v q = 0)
    (h : extToClasses q = 0) :
    extLoc (k := k) (K := L) w₀ q = 0 :=
  classLocIncl_injective_clean k L w₀ q hq h


/-- **The pairing with a class supported on the orbit of `w₀` vanishes when the local data do.**

This is the "local determination" property of the family `h ↦ phiAt (extToClasses z) h` at a fixed
level: if the pushed class `Z = J_*(z)` localises to `0` at every place outside the `Gal(L/k)`-orbit
of `w₀`, and `h` has vanishing restriction to the decomposition group of `w₀`, then the pairing
value is `0`.  (For the family attached to a class supported on the orbit of a place `w` of `K`,
the hypothesis `hz` is the push-forward of that support and `hh` is the vanishing of `h` on the
decomposition group at `w`.) -/
theorem phiAt_extToClasses_eq_zero_of_support (k K L : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L]
    (J : Rep.res (galRes k K L) (idelesK k K) ⟶ idelesK k L)
    (hJ : Rep.resMap (galRes k K L) (NK.HassePrinciple.classGroupMap k K) ≫ classIncl k K L =
        J ≫ NK.HassePrinciple.classGroupMap k L)
    {M : Rep Coeff (K ≃ₐ[k] K)} (z : Abelian.Ext M (idelesK k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) (w₀ : NK.GlobalCFT.Place L)
    (hz : ∀ w' : NK.GlobalCFT.Place L, (∀ σ : L ≃ₐ[k] L, σ • w₀ ≠ w') →
      extLoc (k := k) (K := L) w' ((extRes (galRes k K L) z).comp
        (Abelian.Ext.mk₀ J) (add_zero 1)) = 0)
    (hh : extHRestrict (decompK (k := k) (K := L) w₀) h = 0) :
    phiAt (k := k) (K := K) (L := L) (extToClasses z) h = 0 := by
  rw [Work.SSGRoute.phiAt_extToClasses_eq k K L J hJ z h,
    levelPair_eq_zero_of_support k K L J z h w₀ hz hh]
  simp


attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **Positive-degree `Ext`-cohomology with `p`-torsion coefficients is killed by `p`.**

`p • y = y ∘ mk₀ (p • 𝟙 A)` (`mk₀_nsmul_aux`, `comp_nsmul_aux`) and `p • 𝟙 A = 0` because `A` has
exponent `p`; this is the general form of
`Work.SSGRoute.extH_trivial_zmodp_smul_eq_zero`. -/
theorem extH_smul_eq_zero_of_pTorsion {G : Type} [Group G] {p : ℕ} (A : Rep Coeff G)
    (hA : ∀ a : A, p • a = 0) {n : ℕ} (y : extH A n) : p • y = 0 := by
  have hone : (p : ℕ) • (𝟙 A) = 0 := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    rw [Rep.nsmul_hom]
    rw [show (p • Rep.Hom.hom (𝟙 A)).toLinearMap v = p • ((Rep.Hom.hom (𝟙 A)).toLinearMap v)
      from rfl]
    simpa using hA v
  have hid : p • y
      = y.comp (Abelian.Ext.mk₀ (p • (𝟙 A))) (add_zero n) := by
    rw [Work.SSGRoute.mk₀_nsmul_aux p (𝟙 A)]
    rw [Work.SSGRoute.comp_nsmul_aux p y (Abelian.Ext.mk₀ (𝟙 A)) (add_zero n)]
    rw [Abelian.Ext.comp_mk₀_id]
  rw [hid, hone, Abelian.Ext.mk₀_zero]
  exact Abelian.Ext.comp_zero y _ 0 n (add_zero n)


/-- **The local functional of a locally determined family.**

If `lam` vanishes on the kernel of the restriction to the decomposition group of a place `w'` over
`w` (local determination, `hwd`), then it factors through that restriction, and — because the local
cohomology is killed by `p` and every subgroup of a `p`-torsion group is a direct summand — the
induced functional on the image extends to an additive map on the whole local `H¹`. -/
theorem exists_local_functional (p : ℕ) [Fact p.Prime] {k K Ω : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {M : Rep Coeff (K ≃ₐ[k] K)} (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.res (galRes k K L) M) 1 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) M) 1), p • lam L h = 0)
    (hloc : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      ∃ w' : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w' w ∧
        ∀ h : extH (Rep.res (galRes k K L) M) 1,
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0 → lam L h = 0)
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w) :
    ∃ ν : extH (Rep.res (decompK (k := k) (K := ↥L) w').subtype
          (Rep.res (galRes k K ↥L) M)) 1 →+ extH (classesK k ↥L) 2,
      (∀ h : extH (Rep.res (galRes k K ↥L) M) 1,
        ν (extHRestrict (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w') h) = lam L h) ∧
      ∀ x, p • ν x = 0 := by
  classical
  let rH : extH (Rep.res (galRes k K ↥L) M) 1 →+
      extH (Rep.res (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w').subtype
        (Rep.res (galRes k K ↥L) M)) 1 :=
    { toFun := extHRestrict (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w')
      map_zero' := E6Util.extHMap_zero (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w').subtype (𝟙 _)
      map_add' := fun a b => extHRestrict_add _ a b }
  have hwd : ∀ h₁ h₂ : extH (Rep.res (galRes k K ↥L) M) 1, rH h₁ = rH h₂ →
      lam L h₁ = lam L h₂ :=
    fun h₁ h₂ h => lam_local_determination (p := p) (k := k) (K := K) (Ω := Ω) M w lam hloc
      L w' hw' h₁ h₂ h
  have hpA : ∀ x : extH (Rep.res (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w').subtype
      (Rep.res (galRes k K ↥L) M)) 1, p • x = 0 :=
    fun x => extH_smul_eq_zero_of_pTorsion
      (Rep.res (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w').subtype (Rep.res (galRes k K ↥L) M))
      (fun m => hM m) x
  let ν₀ : rH.range →+ extH (classesK k ↥L) 2 :=
    { toFun := fun x => lam L x.2.choose
      map_zero' := by
        have h0 : rH ((0 : ↥rH.range).2.choose) = rH 0 := by
          simpa using (0 : ↥rH.range).2.choose_spec
        rw [hwd _ _ h0, map_zero]
      map_add' := fun x y => by
        have h0 : rH ((x + y).2.choose) = rH (x.2.choose + y.2.choose) := by
          rw [(x + y).2.choose_spec, map_add, x.2.choose_spec, y.2.choose_spec]
          rfl
        rw [hwd _ _ h0, map_add] }
  have hν₀ : ∀ c : ↥rH.range, p • ν₀ c = 0 := fun c => hp L c.2.choose
  obtain ⟨ν, hν, hνp⟩ := exists_addHom_extend_of_pTorsion' hpA rH.range ν₀ hν₀
  refine ⟨ν, fun h => ?_, hνp⟩
  change ν (rH h) = lam L h
  have hmem : rH h ∈ rH.range := (AddMonoidHom.mem_range).mpr ⟨h, rfl⟩
  rw [hν (⟨rH h, hmem⟩ : ↥rH.range)]
  exact hwd _ h (⟨rH h, hmem⟩ : ↥rH.range).2.choose_spec


/-! ## State of the route to `local_phi_realization_in` (E7cΩ)

### Proved in this file (all complete)

* `inflCIn_injective_aux` — injectivity of the level inflation `H²(·,C_·)` along `L ≤ L'`.
* `phiAt_extToClasses_eq_of_le` — **clause 2 propagates downwards along levels**: realising `lam`
  by the pairing with `extToClasses z` at one level `L₀` realises it at every level `L ≤ L₀`.
* `lam_eq_zero_of_extHRestrict_eq_zero` — `hloc` upgraded from the witness place to *every* place
  over `w` (via `Work.SSGRoute.lam_local_determination`, Step 1 of the design).
* `LevelPair.levelPair_eq_yonedaPair`, `extLoc_levelPair_eq` — the idèle-valued pairing value
  localises at `w` to the Yoneda product of the localisations (E2's `extLoc`).
* `levelPair_eq_zero_of_support`, `phiAt_extToClasses_eq_zero_of_support` — **the pairing family
  attached to a class supported on the orbit of `w₀` is `0` on classes whose restriction to the
  decomposition group at `w₀` vanishes** (E2 injectivity of localisation).  This is the "local
  determination" property of the pairing family, dual to `hloc` for `lam`.
* `exists_addMonoidHom_extend_of_submodule`, `exists_addHom_extend_of_pTorsion` — an additive map
  defined on a subgroup of a `p`-torsion abelian group extends to the whole group (a subgroup of an
  `𝔽_p`-vector space is a direct summand).
* `extH_smul_eq_zero_of_pTorsion` — positive-degree `extH` with `p`-torsion coefficients is killed
  by `p`.
* `exists_local_functional` — **the local functional**: `lam L` factors through the restriction to
  the decomposition group of any place over `w` (`hloc` + Step 1), and the induced additive map on
  the image extends to an additive map `ν` on the whole local `H¹` with `p`-torsion values.

### Proved by children (importable)

* `Work.SSGRoute.phiAt_extToClasses_eq` — `phiAt (extToClasses z) h` is the `C_L`-image of the
  idèle-valued pairing value (`levelPair galRes J z h` for `J` the idèle level map).
* `Work.SSGRoute.exists_ideleIncl_level` — the idèle level map `J : 𝕀_K → 𝕀_L` and the square
  `resMap galRes (classGroupMap k K) ≫ classIncl = J ≫ classGroupMap k L`.
* `Work.SSGRoute.ext_units_single_place` — E8′ (Hasse) in the `Ext` vocabulary: a global Brauer
  class `H²(Gal(L/k), Lˣ)` whose localisations vanish outside the orbit of one place is `0`.
* `Work.SSGRoute.extH_classesK_two_card` — `Nat.card (H²(Gal(L/k), C_L)) = |Gal(L/k)|`; together
  with `Work.SSGRoute.extH_classesK_two_fundamental` this makes `H²(Gal(L/k), C_L)` cyclic of order
  `[L : k]`, so its `p`-torsion is `ℤ/p`.

### Remaining pieces (delegated or to be built)

1. **E7b clause (ii)** (`Work.SSGRoute.local_duality_ext_in`): local realisation of `p`-torsion
   functionals `H¹(D_{w'},M) → H²(D_{w'},L_{w'}ˣ)` by a single class `y ∈ Ext¹_{D_w}(M,K_wˣ)`, when
   `p ∣ |D_{w'}|`.  Being built by the lead's Sylow-project (X1–X6, Y1–Y5).
2. **The localisation inclusion** `H²(D_{w₀},L_{w₀}ˣ) → H²(Gal(L/k),C_L)` (E2 lift with prescribed
   one-place components) together with:
   * `Work.SSGRoute.classLocIncl_injective` (delegated) — a class of `H²(Gal(L/k),𝕀_L)` supported on
     the orbit of `w₀` with trivial class-group image has vanishing `w₀`-component (E8′ +
     exactness of the class formation);
   * `Work.SSGRoute.exists_classLoc_lift_ptorsion` (delegated) — every `p`-torsion class of
     `H²(Gal(L/k),C_L)` has such a lift when `p ∣ |D_{w₀}|` (cyclicity + `eb_loc_card`).
3. **Level naturality of `extLoc` under the idèle level map** `J`: the localisation at `w'` over `w`
   of the pushed class `(extRes (galRes k K L) z).comp (mk₀ J)` is the image of `extLoc w z` under
   the local coefficient map `K_wˣ → L_{w'}ˣ` and the group change `D_{w'} → D_w` (to be stated with
   the same `f`, `hf`, `ι`, `hι` data as E7b).
4. **The assembly**: build `z` from the E7b class `y` with E2 (`ext_idele_shapiro` clause 3), using
   1–3 for the level-by-level comparison (`phiAt (extToClasses z) h = Ψ_L(q)` where `q` is the
   `𝕀_L`-lift of the local functional, equal to the E2-lift by E2 injectivity), and
   `phiAt_extToClasses_eq_of_le` for the levels below the chosen one.
5. **The unramified clause**: with `z` supported on the orbit of `w`, `extLoc w z = y`; the
   hypothesis of clause 3 makes `y` unramified (`IsUnramifiedExt`).

### The key idea that resolves the level-uniformity of the realising class

Per `DESIGN_E7B.md` §3(d) (the designer's consumer note), the level-uniformity is a *minimality*
argument, not a compatibility theorem.  For a level `λ = (L, w', f, ι)` let

* `ℓ_λ` be the local functional of `lam` at `λ`, transported to a functional
  `H¹(D_{w'},M) → H²(D_{w'},L_{w'}ˣ)` (piece 2 above);
* `R_λ := {y ∈ Ext¹_{D_w}(M,K_wˣ) : ⟨y,·⟩_λ = ℓ_λ}`.

Then `R_λ` is nonempty by clause (ii) of E7b, finite by F1 (`Work.SSGRoute.ext_localUnits_finite`),
and **decreasing along levels**: for `λ ≤ λ'`, `R_{λ'} ⊆ R_λ`, because for `y ∈ R_{λ'}` and
`r ∈ H¹(D_{w'},M)`, the naturality of `levelPair` under inflation gives
`⟨y, infl r⟩_{λ'} = infl'(⟨y,r⟩_λ)` while the compatibility of `lam` gives
`ℓ_{λ'}(infl r) = infl'(ℓ_λ(r))`, and `infl'` on `H²(·,L^ˣ)` is injective.  A level `λ₀` of minimal
`|R_{λ₀}|` then satisfies `R_{λ₀} ⊆ R_λ` for *every* level `λ` (take `λ'' ≥ λ, λ₀`; the inclusion
`R_{λ''} ⊆ R_{λ₀}` forces equality by minimality).  Any `y ∈ R_{λ₀}` therefore realises `lam` at
every level, and the idèle class `z` built from `y` (piece 4) satisfies clause 2 directly, without
any uniqueness/detection statement for the level pairing.

### What is available in the workspace for the assembly (all complete)

* E7b clause (ii): derive it inline from
  `Work.SSGRoute.local_duality_ext_detect_h` and
  `Work.SSGRoute.local_duality_ext_realization_of_detection` (do **not** import
  `local_duality_ext_in`, whose clause (i) still carries an inadmissible axiom).
* F1: `Work.SSGRoute.ext_localUnits_finite`.
* The E9c lane (same glue, different packaging): `Work.SSGRoute.e9c_transport_zero`
  (`extLoc` vanishes on the push of a class whose `extLoc` vanishes), `e9c_transport_unram`,
  `e9c_extLoc_conj_zero`, `e9c_phiAt_eq_zero_of_local` (the pairing with a class supported off a
  finite set `T` and unramified outside `T` vanishes at levels with ramification index `1`),
  `e9_glue_phiAt_assembly` (the pairing with `z` is the finite sum of the pairings with the
  per-orbit components `z_v` whenever the local data agree), and the definitions
  `Work.SSGRoute.idlesRepP`, `idleRepMap`, `decompKRestrict` in `Submission/Work/SSGRoute/E9c/`.
* Local class field theory at a finite place: `Work.SSGRoute.eb_loc_card` — `H²(Γ, E_ŵˣ)` has
  order `|Γ|` and an element of that order, `Γ = Stab_{Gal(E/K)}(ŵ)`; with the cyclicity of
  `H²(Gal(L/k),C_L)` this supplies the `p`-torsion of the local Brauer group when `p ∣ |D_{w'}|`.

### Handoff (2026-09-28)

Proved in this file: `inflCIn_injective_aux`, `phiAt_extToClasses_eq_of_le`,
`lam_eq_zero_of_extHRestrict_eq_zero`, `LevelPair.levelPair_eq_yonedaPair`, `extLoc_levelPair_eq`,
`levelPair_eq_zero_of_support`, `phiAt_extToClasses_eq_zero_of_support`,
`exists_addMonoidHom_extend_of_submodule`, `exists_addHom_extend_of_pTorsion`,
`extH_smul_eq_zero_of_pTorsion`, `exists_local_functional`, `extLoc_push_ideleMap` (the level
transport of `extLoc` along the idèle level map; this one uses `idleRepMap`,
`decompKRestrict_res_res`, `resMap_idleRepMap_comp_ideleToLocalUnits` and
`ext_mapExactFunctor_comp_functor_aux` from the sibling lane `Submission/Work/SSGRoute/E9c/`).

Proved by children (imported here): `Work.SSGRoute.phiAt_extToClasses_eq`,
`exists_ideleIncl_level`, `ext_units_single_place`, `extH_classesK_two_card`,
`classLocIncl_injective`, `exists_classLoc_lift_ptorsion`.

**Import caveat.** E7b clause (ii) is to be derived inline from
`local_duality_ext_detect_h` + `local_duality_ext_realization_of_detection`.  At handoff time
`Submission/Work/SSGRoute/local_duality_ext.lean` did **not** build (`Unknown identifier
exists_section_of_fixed_generator`, `rightDetect_sylowLevelStabIncl`, `detect_h_trivial`), so those
three imports were removed from this file; re-add them once the E7b lane is consistent.  Do **not**
import `local_duality_ext_in` itself (its clause (i) carries an inadmissible axiom).

**Remaining assembly steps, in the order they should be attempted.**
1. *The local functional into the local Brauer group.*  For a level `λ = (L, u)` (`u` a finite place
   of `L`, `p ∣ |D_u|`), use `exists_classLoc_lift_ptorsion` to lift every value of the `C_L`-valued
   local functional `ν` of `exists_local_functional` to an `𝕀_L`-class supported on the orbit of `u`,
   and `classLocIncl_injective` for the uniqueness of that lift; unwinding `q.comp (mk₀ classGroupMap)`
   gives the functional `ℓ_λ : H¹(D_u,M) → H²(D_u,L_uˣ)`.  Additivity is the additivity of the lift
   (choose a basis of the `𝔽_p`-space `H²(G_L,C_L)[p]`, use
   `exists_addHom_extend_of_pTorsion`-style linear algebra).  The archimedean case `p = 2`, `D_u =
   ℤ/2`, `Br(ℂ/ℝ) = ℤ/2` is completely analogous with `Work.SSGRoute.eb_brauer_single_place_arch`
   for the rigidity.
2. *Realisation.*  E7b clause (ii) applied to `ℓ_λ` (with `f = decompKRestrict k K ↥L u w hw`,
   `ι` from `localUnitsMap_exists`) gives `y_λ ∈ Ext¹_{D_w}(M,K_wˣ)` with `⟨y_λ,·⟩_λ = ℓ_λ`.
3. *Minimality.*  `R_λ := {y : ⟨y,·⟩_λ = ℓ_λ}` is nonempty (step 2), finite
   (`ext_localUnits_finite`) and decreasing in `λ` (naturality of `levelPair` under inflation,
   `PT/levelPair_functoriality.lean`, plus injectivity of the level inflation of `H²(·,L^ˣ)`); a
   level of minimal `|R_λ|` realises every level.  Pick `y` in it.
4. *The idèle class.*  E2 (`ext_idele_shapiro` clause 3) with a transversal `R ∋ w` of the
   `Gal(K/k)`-orbits and the family `a w = y`, `a v = 0` (`v ≠ w`) gives `z` with `extLoc w z = y`
   and vanishing off the orbit (clause 1 of the conclusion); vanishing at conjugates is
   `Work.SSGRoute.e9c_extLoc_conj_zero`.
5. *The comparison.*  `phiAt (extToClasses z) h = Ψ_L(levelPair galRes J z h)`
   (`phiAt_extToClasses_eq`); the `u`-component of `levelPair galRes J z h` is
   `⟨extLoc u z_L, res_u h⟩` (`extLoc_levelPair_eq`), and `extLoc u z_L` is the push of `y` at the
   level of `u` (`extLoc_push_ideleMap`, restricted to `D_u`), which pairs to `ℓ_λ(res_u h)`.  So
   `levelPair galRes J z h` and the lift of `lam L h` (step 1) have equal local components, hence are
   equal (E2 injectivity), hence `phiAt (extToClasses z) h = lam L h` at every level `λ` (steps 2, 3).
   `phiAt_extToClasses_eq_of_le` then repropagates to the levels below the chosen ones.
6. *The unramified clause.*  With the hypothesis of clause 3, `ℓ_λ` vanishes on the unramified
   classes; `Work.SSGRoute.e9c_phiAt_eq_zero_of_local`/`e9c_unram_pairing` give the vanishing of the
   pairing, and `Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified` identifies unramified local
   classes.
-/



/-- **Level transport of `extLoc` along the idèle level map.**

For `z ∈ Ext^r_{Gal(K/k)}(M, 𝕀_K)` and places `w | u` (`u` of `K`, `w` of `L`), the `w`-component of
the pushed class `(extRes (galRes k K L) z) ≫ idleRepMap k K L` is the image of the `u`-component of
`z` under the restriction `D_w → D_u` and the local coefficient map `K_uˣ → L_wˣ`.

This is the naturality that makes the global pairing with an idèle class computable level by level:
with `extLoc_levelPair_eq` it identifies the `w`-component of `extLoc w (levelPair galRes J z h)`
with the local Yoneda product of the localisations. -/
theorem extLoc_push_ideleMap (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (z : Abelian.Ext M (idelesK k K) r)
    (u : NK.GlobalCFT.Place K) (w : NK.GlobalCFT.Place L)
    (hw : NK.GlobalCFT.Place.LiesOver w u)
    (ι : Rep.res (decompKRestrict k K L u w hw) (localUnitsK (k := k) (K := K) u) ⟶
      localUnitsK (k := k) (K := L) w)
    (hι : ∀ y : (NK.GlobalCFT.Place.localField K u)ˣ,
      ι.hom (Additive.ofMul y)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w u hw y)) :
    extLoc (k := k) (K := L) w
        ((extRes (galRes k K L) z).comp (Abelian.Ext.mk₀ (idleRepMap k K L)) (add_zero r))
      = (extRes (decompKRestrict k K L u w hw) (extLoc (k := k) (K := K) u z)).comp
          (Abelian.Ext.mk₀ ι) (add_zero r) := by
  classical
  have hcoeff : Rep.resMap (decompK (k := k) (K := L) w).subtype (idleRepMap k K L) ≫
        NK.HassePrinciple.ideleToLocalUnits k L w
      = Rep.resMap (decompKRestrict k K L u w hw)
          (NK.HassePrinciple.ideleToLocalUnits k K u) ≫ ι :=
    resMap_idleRepMap_comp_ideleToLocalUnits (k := k) (K := K) (L := L) u w hw ι hι
  simp only [extLoc, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  rw [ext_mapExactFunctor_comp_functor_aux (Rep.resFunctor (galRes k K L))
        (Rep.resFunctor (decompK (k := k) (K := L) w).subtype) r M
        (Work.SSGRoute.idelesRepP k K) z,
    ext_mapExactFunctor_comp_functor_aux (Rep.resFunctor (decompK (k := k) (K := K) u).subtype)
        (Rep.resFunctor (decompKRestrict k K L u w hw)) r M (Work.SSGRoute.idelesRepP k K) z,
    hcoeff]
  have hfun : Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (galRes k K L) ⋙
          Rep.resFunctor (decompK (k := k) (K := L) w).subtype) z
      = Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (decompK (k := k) (K := K) u).subtype ⋙
          Rep.resFunctor (decompKRestrict k K L u w hw)) z := rfl
  rw [hfun]
  try simp only [Abelian.Ext.mk₀_comp_mk₀]
  try rfl

/-! ## Auxiliary lemmas and the main assembly

The construction of `z` (clauses 1 and 2 of the target) is by a minimality argument on the finite
space `V = Ext¹_{D_w}(M, K_wˣ)`: for each level `L` the set
`S_L = {y ∈ V | ∀ h, phiAt (extToClasses (z_y)) h = lam L h}` (where `z_y` is the orbit-supported
class with `w`-component `y`, `exists_orbitSupported_extLoc_gen`) is nonempty and decreasing in
`L`, and its total intersection — nonempty because `V` is finite — is what we need.
-/

/-- **The places of an `Ω`-level over the `Gal(K/k)`-orbit of a place of `K` form one
`Gal(L/k)`-orbit.** -/
theorem SSG.exists_smul_eq_of_liesOver_under {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (u : NK.GlobalCFT.Place ↥L)
    (hu : NK.GlobalCFT.Place.LiesOver u w)
    (v : NK.GlobalCFT.Place ↥L) (u' : NK.GlobalCFT.Place K)
    (hu' : NK.GlobalCFT.Place.LiesOver v u')
    (σ : K ≃ₐ[k] K) (hσ : σ • w = u') :
    ∃ τ : ↥L ≃ₐ[k] ↥L, τ • u = v := by
  haveI : IsGalois K ↥L := IsGalois.tower_top_of_isGalois k K ↥L
  haveI : FiniteDimensional K ↥L := FiniteDimensional.right k K ↥L
  obtain ⟨σ₀, hσ₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) ↥L σ
  have hσ₀' : galRes k K ↥L σ₀ = σ := hσ₀
  have hlies0 : NK.GlobalCFT.Place.LiesOver (σ₀ • u) (galRes k K ↥L σ₀ • w) :=
    NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := ↥L) σ₀
      (galRes k K ↥L σ₀) (fun y => AlgEquiv.restrictNormal_commutes σ₀ K y) hu
  rw [hσ₀', hσ] at hlies0
  obtain ⟨ρ, hρ⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver
    (K := K) (L := ↥L) hlies0 hu'
  refine ⟨(AlgEquiv.restrictScalars k ρ) * σ₀, ?_⟩
  have hsmul : ∀ x : NK.GlobalCFT.Place ↥L, (AlgEquiv.restrictScalars k ρ) • x = ρ • x :=
    fun x => rfl
  rw [mul_smul, hsmul, hρ]

/-- **Finite intersection property for a downward-directed family of nonempty sets**
(universe-polymorphic form of `Work.SSGRoute.iInter_nonempty_of_directed_finite`). -/
theorem iInter_nonempty_of_directed_finite' {α : Type u} {β : Type v} [Nonempty α] [Finite β]
    (F : α → Set β) (hne : ∀ a, (F a).Nonempty) (hdir : ∀ a b, ∃ c, F c ⊆ F a ∩ F b) :
    (⋂ a, F a).Nonempty := by
  classical
  have hfin : (Set.range F).Finite := Set.toFinite _
  obtain ⟨s₀, hs₀, hmin⟩ := hfin.exists_minimal (Set.range_nonempty F)
  obtain ⟨a₀, rfl⟩ := hs₀
  have key : ∀ b, F a₀ ⊆ F b := by
    intro b
    obtain ⟨c, hc⟩ := hdir a₀ b
    exact (hmin (Set.mem_range_self c) (hc.trans Set.inter_subset_left)).trans
      (hc.trans Set.inter_subset_right)
  exact (hne a₀).mono fun x hx => Set.mem_iInter.mpr fun b => key b hx

/-- **Finite intersection property with an explicit starting point.** -/
theorem iInter_nonempty_of_directed_finite'' {α : Type u} {β : Type v} [Finite β]
    (a₀ : α) (F : α → Set β) (hne : ∀ a, (F a).Nonempty)
    (hdir : ∀ a b, ∃ c, F c ⊆ F a ∩ F b) :
    (⋂ a, F a).Nonempty := by
  classical
  have hfin : (Set.range F).Finite := Set.toFinite _
  obtain ⟨s₀, hs₀, hmin⟩ := hfin.exists_minimal ⟨F a₀, Set.mem_range_self a₀⟩
  obtain ⟨a₀, rfl⟩ := hs₀
  have key : ∀ b, F a₀ ⊆ F b := by
    intro b
    obtain ⟨c, hc⟩ := hdir a₀ b
    exact (hmin (Set.mem_range_self c) (hc.trans Set.inter_subset_left)).trans
      (hc.trans Set.inter_subset_right)
  exact (hne a₀).mono fun x hx => Set.mem_iInter.mpr fun b => key b hx

/-- **`extLoc` is additive in the class**, in `nsmul` form. -/
theorem extLoc_nsmul (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : NK.GlobalCFT.Place K) (n : ℕ)
    (q : Abelian.Ext M (idelesK k K) r) :
    extLoc (k := k) (K := K) u (n • q) = n • extLoc (k := k) (K := K) u q := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, extLoc_zero]
  | succ m ih => rw [succ_nsmul, succ_nsmul, extLoc_add, ih]

/-- The pairing with the zero idèle class vanishes (the `Ω`-level form of `phiAt_zero'`). -/
theorem phiAt_extToClasses_zero_ssg {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)}
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (h : extH (Rep.res (galRes k K L) M) 1) :
    phiAt (k := k) (K := K) (L := L)
      (extToClasses (0 : Abelian.Ext M (idelesK k K) 1)) h = 0 := by
  rw [show extToClasses (0 : Abelian.Ext M (idelesK k K) 1) = 0 from by
    show (0 : Abelian.Ext M (idelesK k K) 1).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k K)) (add_zero 1) = 0
    rw [Abelian.Ext.zero_comp]]
  rw [phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp,
    Abelian.Ext.comp_zero]

/-- **E7cΩ, clauses 1 and 2.**  A compatible `p`-torsion family `lam` which at every level is
locally determined at `w` is the family of pairings with a single idèle class `z` supported on the
`Gal(K/k)`-orbit of `w`.

The proof is the minimality argument on the finite set `V = Ext¹_{D_w}(M, K_wˣ)`
(`Work.SSGRoute.ext_localUnits_finite`): `S_L` is the set of `y ∈ V` such that the orbit-supported
class `z_y` with `w`-component `y` reproduces `lam` at the level `L`.

* `S_L` is decreasing in `L`: the pairing value at a level inflates to the pairing value at a
  higher level (`Work.SSGRoute.phiAt_level_infl`), `hcompat` compares the two values of `lam`
  there, and the level inflation `inflCIn` is injective.
* `S_L` is nonempty: if `lam L = 0` this is `0` (whose pairing value vanishes because the pushed
  class is supported off the orbit); otherwise `L` has a place `u` over `w` with `p ∣ |D_u|`, and
  the local functional `ν` of `lam L` at `u` (`Work.SSGRoute.exists_local_functional`), together
  with the orbit-supported lift `classLift` of its values and the resulting local Brauer
  functional `localBrauerFunctional`, is realised by some `yt ∈ V` (E7b (ii),
  `Work.SSGRoute.SSG.exists_realisesLevel`); the induced global family of `yt` at the level `L` is
  `lam L` because the difference of the two idèle classes is supported on the orbit of `u` and has
  the same `u`-component.
-/
theorem local_phi_realization_in_aux (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.res (galRes k K L) M) 1 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) M) 1), p • lam L h = 0)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.res (galRes k K L) M) 1),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflHIn (k := k) hLL h))
    (hloc : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      ∃ w' : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w' w ∧
        ∀ h : extH (Rep.res (galRes k K L) M) 1,
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0 → lam L h = 0) :
    ∃ z : Abelian.Ext M (idelesK k K) 1,
      (∀ u : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • w ≠ u) → extLoc u z = 0) ∧
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        phiAt (k := k) (K := K) (L := L) (extToClasses z) h = lam L h) := by
  classical
  let V := Abelian.Ext (Rep.res (decompK (k := k) (K := K) w).subtype M)
    (localUnitsK (k := k) w) 1
  let zOf : V → Abelian.Ext M (idelesK k K) 1 := fun y =>
    (SSG.exists_orbitSupported_extLoc_gen (k := k) (K := K) M 1 w y).choose
  have zOf_w : ∀ y : V, extLoc (k := k) (K := K) w (zOf y) = y := fun y =>
    (SSG.exists_orbitSupported_extLoc_gen (k := k) (K := K) M 1 w y).choose_spec.1
  have zOf_off : ∀ y : V, ∀ v : NK.GlobalCFT.Place K,
      (∀ σ : K ≃ₐ[k] K, σ • w ≠ v) → extLoc (k := k) (K := K) v (zOf y) = 0 := fun y =>
    (SSG.exists_orbitSupported_extLoc_gen (k := k) (K := K) M 1 w y).choose_spec.2
  let α := {L : IntermediateField K Ω // NumberField L ∧ FiniteDimensional k L ∧ IsGalois k L}
  let Sz : α → Set V := fun L => by
    haveI h1 : NumberField ↥L.1 := L.2.1
    haveI h2 : FiniteDimensional k ↥L.1 := L.2.2.1
    haveI h3 : IsGalois k ↥L.1 := L.2.2.2
    exact {y : V | ∀ h : extH (Rep.res (galRes k K ↥L.1) M) 1,
      phiAt (k := k) (K := K) (L := L.1) (extToClasses (zOf y)) h = lam L.1 h}
  have hmono : ∀ a b : α, a.1 ≤ b.1 → Sz b ⊆ Sz a := by
    intro a b hab y hy
    haveI h1 : NumberField ↥a.1 := a.2.1
    haveI h2 : FiniteDimensional k ↥a.1 := a.2.2.1
    haveI h3 : IsGalois k ↥a.1 := a.2.2.2
    haveI h1' : NumberField ↥b.1 := b.2.1
    haveI h2' : FiniteDimensional k ↥b.1 := b.2.2.1
    haveI h3' : IsGalois k ↥b.1 := b.2.2.2
    intro h
    have hnat := phiAt_level_infl (k := k) (K := K) (Ω := Ω) a.1 b.1 hab M (extToClasses (zOf y)) h
    have hcom := hcompat a.1 b.1 hab h
    have key : inflCIn (k := k) hab
          (phiAt (k := k) (K := K) (L := a.1) (extToClasses (zOf y)) h)
        = inflCIn (k := k) hab (lam a.1 h) := by
      rw [hnat, hy (inflHIn (k := k) hab h), ← hcom]
    exact inflCIn_injective_aux a.1 b.1 hab key
  have hlamzero : ∀ a : α, (¬ ∃ u : NK.GlobalCFT.Place ↥a.1,
      NK.GlobalCFT.Place.LiesOver u w ∧
        p ∣ Nat.card (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) u)) →
      ∀ h : extH (Rep.res (galRes k K ↥a.1) M) 1, lam a.1 h = 0 := by
    intro a hno h
    haveI h1 : NumberField ↥a.1 := a.2.1
    haveI h2 : FiniteDimensional k ↥a.1 := a.2.2.1
    haveI h3 : IsGalois k ↥a.1 := a.2.2.2
    obtain ⟨w', hw', hwd⟩ := hloc a.1
    by_contra hne
    have hres : extHRestrict (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w') h ≠ 0 :=
      fun h0 => hne (hwd h h0)
    haveI : Fintype (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w') := Fintype.ofFinite _
    have hpdiv : p ∣ Nat.card (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w') := by
      by_contra hpnd
      have hpT : ∀ x : extH (Rep.res (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w').subtype
          (Rep.res (galRes k K ↥a.1) M)) 1, p • x = 0 :=
        fun x => extH_smul_eq_zero_of_pTorsion
          (Rep.res (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w').subtype
            (Rep.res (galRes k K ↥a.1) M)) (fun m => hM m) x
      have hnT : ∀ x : extH (Rep.res (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w').subtype
          (Rep.res (galRes k K ↥a.1) M)) 1,
          Nat.card (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w') • x = 0 :=
        fun x => extH_natCard_smul_eq_zero
          (Rep.res (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w').subtype
            (Rep.res (galRes k K ↥a.1) M)) (by norm_num) x
      have htriv : Subsingleton (extH (Rep.res
          (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w').subtype
          (Rep.res (galRes k K ↥a.1) M)) 1) := by
        refine ⟨fun x y => ?_⟩
        have hc : p.Coprime (Nat.card (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) w')) :=
          (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpnd
        exact sub_eq_zero.mp (E7cOmega.eq_zero_of_pTorsion_of_coprime (x := x - y)
          (hpT (x - y)) hc.symm (hnT (x - y)))
      exact hres (Subsingleton.elim _ _)
    exact hno ⟨w', hw', hpdiv⟩
  have hne : ∀ a : α, (Sz a).Nonempty := by
    intro a
    haveI h1 : NumberField ↥a.1 := a.2.1
    haveI h2 : FiniteDimensional k ↥a.1 := a.2.2.1
    haveI h3 : IsGalois k ↥a.1 := a.2.2.2
    by_cases hpd : ∃ u : NK.GlobalCFT.Place ↥a.1, NK.GlobalCFT.Place.LiesOver u w ∧
        p ∣ Nat.card (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) u)
    · obtain ⟨uL, huL, hpu⟩ := hpd
      obtain ⟨ν, hν, hνp⟩ := exists_local_functional (p := p) (k := k) (K := K) (Ω := Ω) hM w
        lam hp hloc a.1 uL huL
      let A : Type := extH (Rep.res (decompKRestrict k K ↥a.1 w uL huL)
        (Rep.res (decompK (k := k) (K := K) w).subtype M)) 1
      let ν' : A →+ extH (classesK k ↥a.1) 2 := ν
      have hν'p : ∀ x : A, p • ν' x = 0 := hνp
      have hν't : ∀ h : extH (Rep.res (galRes k K ↥a.1) M) 1,
          ν' (extHRestrict (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) uL) h) = lam a.1 h := hν
      let Q : A → extH (idelesK k ↥a.1) 2 := fun x =>
        SSG.classLift p k ↥a.1 uL hpu (ν' x) (hν'p x)
      have hQsup : ∀ x : A, SSG.SupportedOff k ↥a.1 uL (Q x) := fun x =>
        SSG.classLift_supported p k ↥a.1 uL hpu (ν' x) (hν'p x)
      have hQcl : ∀ x : A, extToClasses (Q x) = ν' x := fun x =>
        SSG.classLift_extToClasses p k ↥a.1 uL hpu (ν' x) (hν'p x)
      have hlamp : ∀ x : A,
          p • (SSG.localBrauerFunctional k ↥a.1 uL ν' Q hQsup hQcl x) = 0 := by
        intro x
        rw [SSG.localBrauerFunctional_apply]
        calc p • extLoc (k := k) (K := ↥a.1) uL (Q x)
            = extLoc (k := k) (K := ↥a.1) uL (p • Q x) :=
              (extLoc_nsmul k ↥a.1 uL p (Q x)).symm
          _ = 0 := by
              rw [SSG.classLift_ptorsion p k ↥a.1 uL hpu (ν' x) (hν'p x)]
              exact extLoc_zero (k := k) (K := ↥a.1) uL
      obtain ⟨yt, hreal⟩ := SSG.exists_realisesLevel (p := p) (k := k) (K := K) (ζ := ζ)
        (hζ := hζ) M hM w ↥a.1 uL huL
        (decompKRestrict k K ↥a.1 w uL huL)
        (fun σ => decompKRestrict_coe k K ↥a.1 w uL huL σ)
        (localUnitsMap k K ↥a.1 w uL huL)
        (fun x => localUnitsMap_spec k K ↥a.1 w uL huL x) hpu
        (SSG.localBrauerFunctional k ↥a.1 uL ν' Q hQsup hQcl) hlamp
      refine ⟨yt, ?_⟩
      intro h
      let A : extH (idelesK k ↥a.1) 2 :=
        levelPair (galRes k K ↥a.1) (idleRepMap k K ↥a.1) (zOf yt) h
      let Qh : extH (idelesK k ↥a.1) 2 :=
        SSG.classLift p k ↥a.1 uL hpu (lam a.1 h) (hp a.1 h)
      have hA : phiAt (k := k) (K := K) (L := a.1) (extToClasses (zOf yt)) h
          = extToClasses A :=
        phiAt_extToClasses_eq_idleRepMap (k := k) (K := K) (L := ↥a.1) M (zOf yt) h
      have hQhsup : SSG.SupportedOff k ↥a.1 uL Qh :=
        SSG.classLift_supported p k ↥a.1 uL hpu (lam a.1 h) (hp a.1 h)
      have hAQ : A = Qh := by
        refine SSG.eq_of_extLoc_eq_of_orbitSupported (k := k) (L := ↥a.1) uL A Qh ?_ hQhsup ?_
        · intro v hv
          rw [extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := ↥a.1) M (zOf yt) h v]
          obtain ⟨u, hu⟩ := exists_place_under (L := K) (L' := ↥a.1) v
          have hzu : extLoc (k := k) (K := K) u (zOf yt) = 0 := by
            refine zOf_off yt u (fun σ hσ => ?_)
            exact hv _ (SSG.exists_smul_eq_of_liesOver_under (k := k) (K := K) (Ω := Ω) a.1 w uL
              huL v u hu σ hσ).choose_spec
          have hpush0 : extLoc (k := k) (K := ↥a.1) v
              ((extRes (galRes k K ↥a.1) (zOf yt)).comp
                (Abelian.Ext.mk₀ (idleRepMap k K ↥a.1)) (add_zero 1)) = 0 := by
            rw [extLoc_push_ideleMap (k := k) (K := K) (L := ↥a.1) (zOf yt) u v hu
              (localUnitsMap k K ↥a.1 u v hu)
              (fun x => localUnitsMap_spec k K ↥a.1 u v hu x),
              hzu, E6Util.extRes_zero, Abelian.Ext.zero_comp]
          rw [hpush0]
          exact yonedaPair_zero_right _
        · rw [extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := ↥a.1) M (zOf yt) h uL]
          have hpush : extLoc (k := k) (K := ↥a.1) uL
              ((extRes (galRes k K ↥a.1) (zOf yt)).comp
                (Abelian.Ext.mk₀ (idleRepMap k K ↥a.1)) (add_zero 1))
              = (extRes (decompKRestrict k K ↥a.1 w uL huL) yt).comp
                  (Abelian.Ext.mk₀ (localUnitsMap k K ↥a.1 w uL huL)) (add_zero 1) := by
            rw [extLoc_push_ideleMap (k := k) (K := K) (L := ↥a.1) (zOf yt) w uL huL
              (localUnitsMap k K ↥a.1 w uL huL)
              (fun x => localUnitsMap_spec k K ↥a.1 w uL huL x), zOf_w yt]
          rw [hpush]
          change levelPair (decompKRestrict k K ↥a.1 w uL huL)
              (localUnitsMap k K ↥a.1 w uL huL) yt
              (extHRestrict (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) uL) h)
            = extLoc (k := k) (K := ↥a.1) uL Qh
          rw [hreal (extHRestrict (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) uL) h)]
          rw [SSG.localBrauerFunctional_apply]
          have hloc_eq : extLoc (k := k) (K := ↥a.1) uL
              (Q (extHRestrict (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) uL) h))
              = extLoc (k := k) (K := ↥a.1) uL Qh := by
            have h0 := ((hQsup (extHRestrict (MulAction.stabilizer (↥a.1 ≃ₐ[k] ↥a.1) uL) h)).sub
              hQhsup).extLoc_eq_zero (by
                rw [extToClasses_sub, hQcl, SSG.classLift_extToClasses, hν't h, sub_self])
            rw [SSG.extLoc_sub_local] at h0
            exact sub_eq_zero.mp h0
          exact hloc_eq
      rw [hA, hAQ, SSG.classLift_extToClasses p k ↥a.1 uL hpu (lam a.1 h) (hp a.1 h)]
    · refine ⟨0, ?_⟩
      intro h
      rw [hlamzero a hpd h]
      have h0 : phiAt (k := k) (K := K) (L := a.1) (extToClasses (zOf (0 : V))) h
          = phiAt (k := k) (K := K) (L := a.1) (extToClasses (0 : Abelian.Ext M (idelesK k K) 1)) h :=
        SSG.phiAt_eq_of_extLoc_eq (k := k) (K := K) (Ω := Ω) w (zOf 0) 0
          (zOf_off 0) (fun u _ => extLoc_zero (k := k) (K := K) u)
          ((zOf_w 0).trans (extLoc_zero (k := k) (K := K) w).symm)
          a.1 h
      rw [h0, phiAt_extToClasses_zero_ssg (Ω := Ω) a.1 h]
  haveI : Finite V := ext_localUnits_finite p k K w
    (Rep.res (decompK (k := k) (K := K) w).subtype M) (fun n => hM n)
  have hdir : ∀ a b : α, ∃ c : α, Sz c ⊆ Sz a ∩ Sz b := by
    intro a b
    haveI h1 : NumberField ↥a.1 := a.2.1
    haveI h2 : FiniteDimensional k ↥a.1 := a.2.2.1
    haveI h3 : IsGalois k ↥a.1 := a.2.2.2
    haveI h1' : NumberField ↥b.1 := b.2.1
    haveI h2' : FiniteDimensional k ↥b.1 := b.2.2.1
    haveI h3' : IsGalois k ↥b.1 := b.2.2.2
    obtain ⟨hN, hFD, hG⟩ := level_sup_instances (k := k) (K := K) (Ω := Ω) a.1 b.1
    refine ⟨⟨a.1 ⊔ b.1, ⟨hN, hFD, hG⟩⟩, fun y hy => ⟨?_, ?_⟩⟩
    · exact hmono a ⟨a.1 ⊔ b.1, ⟨hN, hFD, hG⟩⟩ le_sup_left hy
    · exact hmono b ⟨a.1 ⊔ b.1, ⟨hN, hFD, hG⟩⟩ le_sup_right hy
  by_cases hα : Nonempty α
  · obtain ⟨a₀⟩ := hα
    obtain ⟨y, hy⟩ := iInter_nonempty_of_directed_finite'' a₀ Sz hne hdir
    refine ⟨zOf y, zOf_off y, ?_⟩
    intro L h1 h2 h3 h
    exact (Set.mem_iInter.mp hy ⟨L, ⟨h1, h2, h3⟩⟩) h
  · refine ⟨0, fun u _hu => extLoc_zero (k := k) (K := K) u, fun L h1 h2 h3 _h => ?_⟩
    exact (hα ⟨⟨L, h1, h2, h3⟩⟩).elim

/-! ## Session state (2026-09-29): the file is complete except for one arithmetic node

* **`local_phi_realization_in_aux`** (clauses 1 and 2 of the target) is **proved**, complete:
  the minimality argument on the finite `p`-torsion space
  `V = Ext¹_{D_w}(M, K_wˣ)` (`Work.SSGRoute.ext_localUnits_finite`), with the levelwise realisation
  sets `S_L ⊆ V`, nonempty by E7b(ii) (`Work.SSGRoute.SSG.exists_realisesLevel`, assembled from the
  proved `Work.SSGRoute.local_duality_ext_detect_h` and
  `…_realization_of_detection`) and decreasing along the level order
  (`Work.SSGRoute.phiAt_level_infl` + `hcompat` + `Work.SSGRoute.inflCIn_injective_aux`).
* **`levelPair_extLoc_eq_push`** (proved): the level pairing of `extLoc w z` is the localisation of
  the idèle-level pairing of `z` (`extLoc_levelPair_idleRepMap_eq` + `extLoc_push_ideleMap`).
* **`local_phi_realization_in`** (the requested theorem) is **proved from the two items above and
  the single remaining node** `isUnramifiedExt_of_levelPair_unramified_aux`: the proof is the
  `⟨z, hz1, hz2, clause3⟩` assembly, with clause 3 derived from clause 2 + the hypothesis `hkill`
  (the pairing of `z` with an unramified global class vanishes by Hasse–Brauer–Noether at one place,
  `Work.SSGRoute.extLoc_eq_zero_of_locTrivial_off_orbit`), and the only unproved input of the file is the
  node `isUnramifiedExt_of_levelPair_unramified_aux` itself.
* The remaining node is **clause 3** = the unramified half of local Tate duality.  It is TRUE (the
  project lead's verdict, `Submission/Work/SSGRoute/E7cOmega/lead_notes/E7COMEGA.md` §1), and that
  note gives the complete route: nodes C1–C7, ~2k lines, **no dévissage over `M`** is needed —
  C1 the valuation criterion `IsUnramifiedExt w y ↔ y ≫ mk₀ valRep = 0` for the short exact
  sequence `0 → 𝒪_wˣ → K_wˣ →v ℤ → 0` of `D_w`-modules (exactness of the covariant `Ext` sequence
  plus `Hom_{D_w}(M,ℤ) = 0`), C2 the case `p ∣ e(w/v)` where *every* class is unramified (free
  win), C3 a level with `e = 1` and `p ∣ f` (`E7cOmega.exists_level_unramified_p_dvd_inertiaDeg`),
  C4–C5 the valuation-pushed pairing and its nonvanishing at Frobenius, C6 the global unramified
  detector (the risky step), C7 assembly.
* **The single remaining mathematical gap of the whole E7cΩ route (as of 2026-10-01).**  The
  detector input of the ported node ultimately rests on node `C6` in its general-`M` form, whose
  status is recorded in `Submission/Work/Sha2Lib/unramifiedDetector.lean` (node
  `Work.Sha2Lib.unramifiedDetector`, one unproved input): the *local* detecting cocycle and every
  reduction (`Sha2Lib.isUnramifiedDetector_of_induced`, `Sha2Lib.unramifiedDetector_trivial`,
  `Sha2Lib.detector_of_submodule`, `Sha2Lib.detectsAt_of_coeff_surjection`,
  `SSGStage.divRep_detecting_class`, `SSGStage.exists_local_cocycle_detecting`,
  `E7cOmega.levelPair_ratDivSES_mk0_ne_zero_iff`, the one-generator case
  `Sha2Lib.grunwald_odd_single_place_unramified`) are **proved**; what is missing is the
  **`Gal(K/k)`-equivariant multi-generator Grünwald–Wang level** (a Kummer level `L` over `K(ζ_p)`
  with `p ∤ e(q'|q)` and a global unramified class whose value at some `d ∈ D_{q'}` is outside
  `ker μ`).  No change on my side is needed: when that node is closed, `E7cC.exists_unramifiedDetector_ExtZ`
  (or its replacement using `detectsAt_of_coeff_surjection` + `grunwald_over_K_general`, per the
  lead's message of 2026-10-01) becomes clean, hence so does the port and this theorem.
* **The rewiring to the designed C6 interface: LANDED (2026-10).**  `local_phi_realization_in` now
  calls `Sha2Lib.clause3_of_detector.isUnramifiedExt_of_levelPair_unramified_of_detector` with the
  provider built from the frontier declaration `Work.Sha2Lib.unramifiedDetector` (the C6 leaf), so the
  whole clause-3 gap of this file is exactly that one design-level node.  What made it work:
  (i) unfold the provider's `Sha2Lib.DetectsAt` conclusion with `change ... _ at h` (the `def` resisted
  `exact`, `simpa only [DetectsAt]` and a Π-type ascription; the
  `backward.isDefEq.respectTransparency` option was a red herring); (ii) after destructuring the `∃`,
  convert the coprimality clause from `q.asIdeal.ramificationIdx' q'.asIdeal` (the `DetectsAt` form) to
  `q'.asIdeal.ramificationIdx (𝓞 K)` (the `_of_detector` form) via the self-contained
  `liesOver_asIdeal_ssg` and `Ideal.ramificationIdx'_eq_ramificationIdx`.
* **Historical note on the earlier attempt at the same rewiring.** (attempted 2026-10, blocked on one elaboration
  step, not on mathematics).**  The intended wire is
  `Sha2Lib.clause3_of_detector.isUnramifiedExt_of_levelPair_unramified_of_detector` applied with the
  provider `fun M' _ hM' hI' => Work.Sha2Lib.unramifiedDetector p k K Ω w q hwq hpq M' hM' hI'`
  (the frontier declaration `Work.Sha2Lib.unramifiedDetector`), which makes this file depend on the
  *single* design-level C6 node instead of the `E7cC` repackaging used today.  The provider's
  expected type has `Sha2Lib.DetectsAt ...` **unfolded** to its `∃ L, …` body, and the elaborator
  would not unfold the `def DetectsAt` when checking the provider (tried: a λ with an implicit
  `[Finite M']` binder, an explicit Π-type ascription, `intro`-plus-`exact`, and
  `simpa only [Sha2Lib.DetectsAt]`; the last two failed with "After simplification, term … has type
  `DetectsAt …` but is expected to have type `∃ L, …`").  The fix is to ascribe the provider in the
  **unfolded** shape — copy the conclusion of `E7cOmega.exists_level_unramified_detecting_class`
  (same `∃ L (… : NumberField ↥L) (… : FiniteDimensional k ↥L) (… : IsGalois k ↥L) (q') (hq') (h), …`
  form) — or to set `backward.isDefEq.respectTransparency true` for that one `have`.  Everything
  else of the wire is in place (the call sites, the `hkill`/clause-2 glue and the hy proof are
  unchanged).

* **Assets added for the route.**  `Submission/Work/SSGRoute/ssg_levelNorm_valuation.lean`
  (`Work.SSGRoute.SSG.levelNorm_valuation`) is a port of the sibling
  `E7cOmega/levelNorm_valuation.lean` **with its two errors fixed** (that file does not compile:
  the arguments of `Finset.sum_apply` were in the wrong order, and the closing `∏_const`
  computation is now `map_sum (LinearMap.applyₗ _)`); statement unchanged.  Also available:
  `Work.SSGRoute.extLoc_eq_zero_of_locTrivial_off_orbit`,
  `Work.SSGRoute.levelPair_extLoc_eq_push`, `Work.SSGRoute.phiAt_extToClasses_zero_ssg`,
  `Work.SSGRoute.iInter_nonempty_of_directed_finite''`, `Work.SSGRoute.SSG.*` (`e7comega_S.lean`),
  and the proved easy direction of the node: `Work.SSGRoute.e9c_unram_pairing` together with
  `Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified`.
* **2026-10-01: the node is reduced to a single unproved input, and a drop-in replacement exists.**
  `Submission/Work/SSGRoute/ssg_node_final.lean` (module
  `Submission.Work.SSGRoute.ssg_node_final`, theorem
  `Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified_ssg`) is the node's statement, **fully
  proved**, by porting the sibling node file
  `Submission/Work/SSGRoute/isUnramifiedExt_of_levelPair_unramified.lean` (same proof, names
  suffixed `_ssg` to avoid a clash) and replacing its single unproved input
  (`E7cOmega.exists_level_unramified_detecting_class`, which inherits an inadmissible axiom from
  `E7cOmega.exists_level_detecting_functional`) by the **proved** node
  `Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ`.  The port therefore inherits an inadmissible axiom
  *only* through that last lemma (checked with `#print axioms`); as soon as
  `E7cC.exists_unramifiedDetector_ExtZ` / `E7cC.exists_unramifiedDetector` /
  `E7cOmega.exists_level_detecting_functional` is closed by its lane (the `E7cC` lane has the
  𝔽_p case `E7cC.exists_unramifiedDetector_ExtZ_trivial` axiom-clean, so only the dévissage over
  `M` is missing), **this file has already been rewired**: `local_phi_realization_in` calls the ported node
  directly (the former in-file unproved node is deleted), so no further edit to this file is needed
  — the moment the upstream node is closed, `#print axioms Work.SSGRoute.local_phi_realization_in`
  becomes clean and the theorem is verified.
* **Next step for the next session.**  A colleague has been requested to prove the node in
  `Submission/Work/SSGRoute/isUnramifiedExt_of_levelPair_unramified.lean` under the name
  `Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified` (identical statement).  When it lands:
  import that module, delete `isUnramifiedExt_of_levelPair_unramified_aux` here and replace its one
  call in `local_phi_realization_in` by the imported name.  Nothing else changes. -/

/-! ## The remaining arithmetic input: the unramified half of local Tate duality -/

/-- **Level transport of the pairing of an idèle class.**  For `z ∈ Ext¹_{Gal(K/k)}(M, 𝕀_K)`, a
place `w` of `K` and a place `w'` of a level `L ⊇ K` over `w`, the pairing at the level `w'` of the
localisation `extLoc w z` with the restriction of `h` is the localisation at `w'` of the
idèle-valued pairing value of `z` with `h`. -/
theorem levelPair_extLoc_eq_push (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    {M : Rep Coeff (K ≃ₐ[k] K)} (z : Abelian.Ext M (idelesK k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) (w : NK.GlobalCFT.Place K)
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w) :
    levelPair (decompKRestrict k K L w w' hw') (localUnitsMap k K L w w' hw')
        (extLoc (k := k) (K := K) w z)
        (extHRestrict (decompK (k := k) (K := L) w') h)
      = extLoc (k := k) (K := L) w'
          (levelPair (galRes k K L) (idleRepMap k K L) z h) := by
  rw [extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := L) M z h w']
  rw [extLoc_push_ideleMap (k := k) (K := K) (L := L) z w w' hw'
    (localUnitsMap k K L w w' hw') (localUnitsMap_spec k K L w w' hw')]
  rfl

/-- Place-level `LiesOver` of finite places gives the ideal-level relation (self-contained copy of
`Work.SSGRoute.E7cC.liesOver_asIdeal_extZ`, so that this file does not depend on that lane). -/
theorem liesOver_asIdeal_ssg {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L]
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q)) : q'.asIdeal.LiesOver Q.asIdeal := by
  rcases h with ⟨w', v', h1, h2, h3⟩ | ⟨q, Q', h1, h2, h3⟩
  · exact (Sum.inr_ne_inl h1).elim
  · obtain rfl : q' = q := Sum.inr_injective h1
    obtain rfl : Q = Q' := Sum.inr_injective h2
    exact h3

/-- **E7cΩ.** Local duality at `w`, with values in the class formation, over the levels
`K ≤ L ≤ Ω`: a compatible `p`-torsion family of functionals `H¹(Gal(L/k), M) → H²(Gal(L/k), C_L)`
that at each level only depends on the restriction to the decomposition group of a place over `w`
is the pairing with an idèle class `z ∈ Ext¹_G(M, 𝕀_K)` supported on the orbit of `w`; `z` is
unramified at a good `w = q` when every functional kills the classes unramified above `q`. -/
theorem local_phi_realization_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (lam : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      extH (Rep.res (galRes k K L) M) 1 →+ extH (classesK k L) 2)
    (hp : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) M) 1), p • lam L h = 0)
    (hcompat : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L] (L' : IntermediateField K Ω) [NumberField L'] [FiniteDimensional k L'] [IsGalois k L'] (hLL : L ≤ L')
      (h : extH (Rep.res (galRes k K L) M) 1),
      inflCIn (k := k) hLL (lam L h) = lam L' (inflHIn (k := k) hLL h))
    (hloc : ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
      ∃ w' : NK.GlobalCFT.Place L, NK.GlobalCFT.Place.LiesOver w' w ∧
        ∀ h : extH (Rep.res (galRes k K L) M) 1,
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0 → lam L h = 0) :
    ∃ z : Abelian.Ext M (idelesK k K) 1,
      (∀ u : NK.GlobalCFT.Place K, (∀ σ : K ≃ₐ[k] K, σ • w ≠ u) → extLoc u z = 0) ∧
      (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        phiAt (k := k) (K := K) (L := L) (extToClasses z) h = lam L h) ∧
      ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        w = NK.GlobalCFT.Place.ofFinite q →
        ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal) →
        (∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) →
        (∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
          (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
          (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
          (h : extH (Rep.res (galRes k K L) M) 1),
          IsUnramifiedClassAt q' h → lam L h = 0) →
        IsUnramifiedExt w (extLoc w z) := by
  classical
  obtain ⟨z, hz1, hz2⟩ :=
    local_phi_realization_in_aux (p := p) (k := k) (K := K) (Ω := Ω) ζ hζ M hM w lam hp
      hcompat hloc
  refine ⟨z, hz1, hz2, ?_⟩
  intro q hwq hpq hI hkill
  have hdet : ∀ (M' : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M'],
      (∀ m : M', p • m = 0) →
      (∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M', M'.ρ σ m = m) →
      ∀ φ : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M')
        (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1,
        φ ≠ 0 →
        ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
          (_ : IsGalois k ↥L)
          (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
          (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
          (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M') 1),
          SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
          Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
          SSGRoute.PTExt.levelPair
            (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
            (SSGRoute.PTExt.trivResInv
              (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
              SSGRoute.PTExt.Coeff)
            φ
            (SSGRoute.PTExt.extHRestrict
              (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
                (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
    intro M' hMfin hM' hI' φ hφ
    haveI : Finite M' := hMfin
    have h := Work.SSGRoute.unramifiedDetector_closed p k K Ω w q hwq hpq M' hM' hI' φ hφ
    change ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
        (_ : IsGalois k ↥L)
        (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
        (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
        (h2 : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M') 1), _ at h
    obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h2, hunr, hcop, hne⟩ := h
    exact ⟨L, hLnf, hLfd, hLgal, q', hq', h2, hunr, by
      haveI : q'.asIdeal.LiesOver q.asIdeal :=
        liesOver_asIdeal_ssg (K := K) (L := ↥L) (hwq ▸ hq')
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx (p := q.asIdeal) (q := q'.asIdeal) q.ne_bot]
      exact hcop, hne⟩
  refine isUnramifiedExt_of_levelPair_unramified_of_detector (p := p) (k := k) (K := K) (Ω := Ω)
    M hM w q hwq hpq hI hdet (extLoc (k := k) (K := K) w z) ?_
  intro L hnf hfd hgal q' hq' h hunr
  have hphi : phiAt (k := k) (K := K) (L := L) (extToClasses z) h = 0 := by
    rw [hz2 L h]
    exact hkill L q' hq' h hunr
  rw [levelPair_extLoc_eq_push (k := k) (K := K) (L := ↥L) (M := M) z h w
    (NK.GlobalCFT.Place.ofFinite q') hq']
  refine extLoc_eq_zero_of_locTrivial_off_orbit k ↥L (NK.GlobalCFT.Place.ofFinite q') _ ?_ ?_
  · intro v hv
    rw [extLoc_levelPair_idleRepMap_eq (k := k) (K := K) (L := ↥L) M z h v]
    obtain ⟨u, hu⟩ := exists_place_under (L := K) (L' := ↥L) v
    have hzu : extLoc (k := k) (K := K) u z = 0 := by
      refine hz1 u (fun σ hσ => ?_)
      have hlies : NK.GlobalCFT.Place.LiesOver v (σ • w) := by rw [hσ]; exact hu
      obtain ⟨τ, hτ⟩ := SSG.exists_smul_eq_of_liesOver_under (k := k) (K := K) (Ω := Ω) L w
        (NK.GlobalCFT.Place.ofFinite q') hq' v (σ • w) hlies σ rfl
      exact hv τ hτ
    have hpush : extLoc (k := k) (K := ↥L) v
        ((extRes (galRes k K ↥L) z).comp (Abelian.Ext.mk₀ (idleRepMap k K ↥L))
          (add_zero 1)) = 0 :=
      e9c_transport_zero z u v hu hzu
    rw [hpush]
    exact yonedaPair_zero_right _
  · have hkey := phiAt_extToClasses_eq_idleRepMap (k := k) (K := K) (L := ↥L) M z h
    rw [hkey] at hphi
    simpa only [extToClasses] using hphi

end Work.SSGRoute
