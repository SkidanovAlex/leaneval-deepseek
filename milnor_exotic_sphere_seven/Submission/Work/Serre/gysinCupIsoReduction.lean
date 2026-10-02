import Submission.Work.Serre.Engine
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.ratCup_unit_exists
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.Serre.gysinCupIso`, reduced to its additive content

**Import-island fix (H5, 2026-09-27).**  The three generic helpers below are declared a *second*
time in this file (with `_dup` suffixed names): `Work.Serre.isZero_dual_of_isZero`,
`Work.Serre.isZero_ratCoh_of_isZero_ratH` and `Work.Serre.isZero_ratH_of_conn` are also declared in
`Submission/Work/Serre/EulerFibreRoot.lean` / `Submission/Work/Serre/periodicity_of_serreFibration.lean`,
and the two copies made `Submission.Work.Serre.serreE3b` and `Submission.Work.Drive.rh3OfE3b`
(the whole E3(b) node and the rational-Hurewicz drive) *impossible to import together*
(`import Submission.Work.Serre.gysinCupIsoReduction failed, environment already contains
'Work.Serre.isZero_ratH_of_conn._proof_1_1'`).  The copies here carry the suffix; the canonical
names are the E3(b) ones.  **Do not rename them back.**  See `Submission/Work/Serre/E3B_STATUS.md`
§8 and `HANDOFF.md` (addendum "H5: import-island de-duplication").

The requested lemma `Work.Serre.gysinCupIso` (`Submission/Work/Serre/gysinCupIso.lean`) asks, for a
Serre fibration with rationally acyclic total space and rationally `S^r`-fibre over a
`(b-1)`-connected base `B`, for a class `e ∈ H^{r+1}(B;ℚ)` whose cup product
`⌣ e : H^m(B;ℚ) → H^{m+r+1}(B;ℚ)` is an isomorphism for every `m < b`.

This module contains the part of that statement that **does not use the fibration at all**, and
which is therefore independent of the missing geometric input:

* `isZero_ratCoh_of_isZero_ratH_dup` — the field universal coefficient theorem
  (`Work.StemsB.ratDualUCT`) turns vanishing of rational homology into vanishing of rational
  cohomology;
* `isZero_ratH_of_conn_dup` — the connectivity hypothesis `Conn B b₀ b` gives
  `H_k(B;ℚ) = 0` for `0 < k < b` (`Work.Serre.serreE0Range`, Serre's `E0` in range form);
* `isIso_toSpanSingleton_of_iso_rat` — the linear-algebra core of the `m = 0` case;
* `exists_cupWith_zero_isIso` — **the `m = 0` case of the conclusion**: if `H_{r+1}(B;ℚ) ≅ ℚ`
  then there is `e ∈ H^{r+1}(B;ℚ)` with `⌣ e : H^0(B;ℚ) ≅ H^{r+1}(B;ℚ)`;
* `exists_cupWith_isIso_of_vanishing` — **the reduction**: the connectivity vanishing, the
  additive vanishing `H_k(B;ℚ) = 0` for `r+1 < k ≤ b+r` and the `m = 0` case together give the
  full conclusion of `Work.Serre.gysinCupIso`.

Since for `1 ≤ m < b` the class `e` plays no role (both sides are zero modules), the *only*
remaining input needed for `Work.Serre.gysinCupIso` is the additive statement

  `H_{r+1}(B;ℚ) ≅ ℚ`  and  `H_k(B;ℚ) = 0` for `r+1 < k ≤ b+r`,

which is the content of the requester's own `Work.Serre.periodicity_of_serreFibration`; see
`Submission/Work/Serre/GYSIN_CUP_LOCAL_ISO_NOTES.md` for the route to it from the fibration
(the Serre exact sequence in the stable range plus the one-degree-beyond surjectivity).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-! ## The `ℚ`-dual of a zero module is zero -/

/-- The `ℚ`-dual of a zero module is zero. -/
theorem isZero_dual_of_isZero_dup (M : ModuleCat ℚ) (h : IsZero M) :
    IsZero (ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ)) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun f g => LinearMap.ext fun x => by
      haveI : Subsingleton ↥M := ModuleCat.isZero_iff_subsingleton.mp h
      rw [Subsingleton.elim x 0]
      simp⟩

/-- **Vanishing of rational homology implies vanishing of rational cohomology** (field universal
coefficients, `Work.StemsB.ratDualUCT`). -/
theorem isZero_ratCoh_of_isZero_ratH_dup {B : Type} [TopologicalSpace B] {k : ℕ}
    (h : IsZero (ratH (TopCat.of B) k)) : IsZero (ratCoh (TopCat.of B) k) :=
  IsZero.of_iso (isZero_dual_of_isZero_dup _ h)
    (Classical.choice (Work.StemsB.ratDualUCT (ratChains (TopCat.of B)) k))

/-- **Connectivity gives vanishing of rational homology below `b`** (`Work.Serre.serreE0Range`). -/
theorem isZero_ratH_of_conn_dup {B : Type} [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 1 ≤ b)
    (hconn : Conn B b₀ b) :
    ∀ k : ℕ, 0 < k → k < b → IsZero (ratH (TopCat.of B) k) := by
  have hV : RatVanishingBelow B ((b - 1) + 1) :=
    serreE0Range B b₀ (b - 1) (fun i hi => hconn i (by omega))
  exact fun k hk hkb => hV k hk (by omega)

/-! ## Elementary facts about `ℚ`-modules -/

/-- A nonzero endomorphism of `ℚ` is an isomorphism. -/
theorem isIso_ofHom_rat_ne_zero (g : ℚ →ₗ[ℚ] ℚ) (hg : g ≠ 0) :
    IsIso (ModuleCat.ofHom g) := by
  have hg1 : g 1 ≠ 0 := by
    intro h
    apply hg
    refine LinearMap.ext (fun x => ?_)
    have hx : g x = x * g 1 := by
      have h' := map_smul g x (1 : ℚ)
      simpa using h'
    rw [hx, h, mul_zero]
    rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective g
  constructor
  · intro x y hxy
    have hx : g x = x * g 1 := by
      have h' := map_smul g x (1 : ℚ)
      simpa using h'
    have hy : g y = y * g 1 := by
      have h' := map_smul g y (1 : ℚ)
      simpa using h'
    rw [hx, hy] at hxy
    exact mul_right_cancel₀ hg1 hxy
  · intro y
    refine ⟨y / g 1, ?_⟩
    have hx : g (y / g 1) = (y / g 1) * g 1 := by
      have h' := map_smul g (y / g 1) (1 : ℚ)
      simpa using h'
    rw [hx]
    field_simp

/-- The dual of `ℚ` over itself is `ℚ`. -/
def ratDualSelfIso : ModuleCat.of ℚ (ℚ →ₗ[ℚ] ℚ) ≅ ModuleCat.of ℚ ℚ :=
  LinearEquiv.toModuleIso
    { toFun := fun f => f 1
      invFun := fun c => c • LinearMap.id
      left_inv := fun f => by
        refine LinearMap.ext (fun x => ?_)
        have h' := map_smul f x (1 : ℚ)
        simpa [smul_eq_mul, mul_comm] using h'.symm
      right_inv := fun c => by simp
      map_add' := fun f g => by simp
      map_smul' := fun c f => by simp }

/-- `c ↦ c • u` is an isomorphism when `u ≠ 0` and the module is isomorphic to `ℚ`. -/
theorem isIso_toSpanSingleton_of_iso_rat (A : ModuleCat ℚ) (u : ↥A) (e : A ≅ ModuleCat.of ℚ ℚ)
    (hu : u ≠ 0) : IsIso (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ↥A u)) := by
  have hbij : Function.Bijective e.hom.hom :=
    (ConcreteCategory.isIso_iff_bijective e.hom).mp (Iso.isIso_hom e)
  have heu : e.hom.hom u ≠ 0 := fun h => hu (hbij.1 (by rw [h]; simp))
  have hcomp : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ↥A u)) ≫ e.hom =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℚ (e.hom.hom u)) := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
    refine LinearMap.ext (fun c => ?_)
    simp [LinearMap.toSpanSingleton_apply, LinearMap.comp_apply]
  have hone : (LinearMap.toSpanSingleton ℚ ℚ (e.hom.hom u)) ≠ 0 := by
    intro h
    exact heu (by simpa using LinearMap.congr_fun h 1)
  haveI : IsIso ((ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ↥A u)) ≫ e.hom) := by
    rw [hcomp]; exact isIso_ofHom_rat_ne_zero _ hone
  exact IsIso.of_isIso_comp_right (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ↥A u)) e.hom

end

end Work.Serre


namespace Work.Serre

noncomputable section

/-! ## Cast lemmas for the degree bookkeeping of `cupWith` -/

/-- `h.symm ▸ (c • z) = c • (h.symm ▸ z)`: the degree cast commutes with scalar multiplication. -/
theorem cast_smul_gen {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b) (c : ℚ)
    (z : ratCoh (TopCat.of B) b) : h.symm ▸ (c • z) = c • (h.symm ▸ z) := by cases h; rfl

/-- `h.symm ▸ (h ▸ z) = z` for `z` in the *source* degree. -/
theorem cast_cancel_src {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (z : ratCoh (TopCat.of B) a) : h.symm ▸ (h ▸ z) = z := by cases h; rfl

/-- Cancellation of a cast: `h ▸ (h.symm ▸ z) = z`. -/
theorem cast_cancel {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b)
    (z : ratCoh (TopCat.of B) a) : h ▸ (h.symm ▸ z) = z := by cases h; rfl

/-- `h ▸ z = w` implies `z = h.symm ▸ w`. -/
theorem cast_eq_symm {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b)
    {z : ratCoh (TopCat.of B) a} {w : ratCoh (TopCat.of B) b} (hz : h ▸ z = w) :
    z = h.symm ▸ w := by cases h; simpa using hz

/-- `h.symm ▸ w = 0` implies `w = 0`. -/
theorem eq_zero_of_cast_symm_eq_zero {B : Type} [TopologicalSpace B] {a b : ℕ} (h : a = b)
    {w : ratCoh (TopCat.of B) b} (hz : h.symm ▸ w = 0) : w = 0 := by cases h; simpa using hz

/-! ## `H^{n}(B;ℚ) ≅ ℚ` from `H_{n}(B;ℚ) ≅ ℚ` -/

/-- The dual of a one-dimensional `ℚ`-module is `ℚ`. -/
def dualIsoRat {M : Type*} [AddCommGroup M] [Module ℚ M] (l : M ≃ₗ[ℚ] ℚ) :
    (M →ₗ[ℚ] ℚ) ≃ₗ[ℚ] ℚ where
  toFun := fun f => f (l.symm 1)
  invFun := fun c => c • (l : M →ₗ[ℚ] ℚ)
  left_inv := fun f => by
    refine LinearMap.ext (fun x => ?_)
    have hx : x = (l x) • (l.symm 1) := by
      have h2 : l.symm ((l x) • (1 : ℚ)) = (l x) • l.symm 1 := map_smul l.symm (l x) 1
      calc x = l.symm (l x) := (l.symm_apply_apply x).symm
        _ = l.symm ((l x) • (1 : ℚ)) := by rw [smul_eq_mul, mul_one]
        _ = (l x) • l.symm 1 := h2
    have hkey : f x = (l x) • f (l.symm 1) := by
      conv_lhs => rw [hx]
      rw [map_smul]
    rw [hkey]
    show f (l.symm 1) * l x = l x * f (l.symm 1)
    ring
  right_inv := fun c => by simp
  map_add' := fun f g => by simp
  map_smul' := fun c f => by simp

/-- **Cohomology is `ℚ` when homology is** (field universal coefficients). -/
theorem ratCoh_iso_rat_of_ratH_iso {B : Type} [TopologicalSpace B] (n : ℕ)
    (h : ratH (TopCat.of B) n ≅ ModuleCat.of ℚ ℚ) :
    Nonempty (ratCoh (TopCat.of B) n ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨uct⟩ := Work.StemsB.ratDualUCT (ratChains (TopCat.of B)) n
  have hbij : Function.Bijective h.hom.hom :=
    (ConcreteCategory.isIso_iff_bijective h.hom).mp (Iso.isIso_hom h)
  exact ⟨uct ≪≫ LinearEquiv.toModuleIso (dualIsoRat (LinearEquiv.ofBijective h.hom.hom hbij))⟩

/-! ## The `m = 0` case -/

/-- **The `m = 0` case of the conclusion of `Work.Serre.gysinCupIso`**: if `H_{r+1}(B;ℚ) ≅ ℚ` then
there is `e ∈ H^{r+1}(B;ℚ)` such that `⌣ e : H^0(B;ℚ) → H^{r+1}(B;ℚ)` is an isomorphism.

`H^0(B;ℚ) ≅ ℚ` (path-connectedness and field universal coefficients), its unit `u`
(`Work.Serre.ratCup_unit_exists`) generates it, and `u ⌣ e = e ≠ 0`. -/
theorem exists_cupWith_zero_isIso {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    (r : ℕ) (hG : Nonempty (ratH (TopCat.of B) (r + 1) ≅ ModuleCat.of ℚ ℚ)) :
    ∃ e : ratCoh (TopCat.of B) (r + 1),
      IsIso (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e 0)) := by
  obtain ⟨h0H⟩ := ratH_zero_of_pathConnected B
  obtain ⟨e0⟩ := ratCoh_iso_rat_of_ratH_iso (B := B) 0 h0H
  obtain ⟨hGH⟩ := hG
  obtain ⟨e1⟩ := ratCoh_iso_rat_of_ratH_iso (B := B) (r + 1) hGH
  obtain ⟨u, hu⟩ := ratCup_unit_exists B
  have hu_law : ∀ (n : ℕ) (y : ratCoh (TopCat.of B) n),
      (Nat.zero_add n) ▸ ((ratCup (TopCat.of B) 0 n) u) y = y := fun n y => (hu n y).1
  have hbij0 : Function.Bijective e0.hom.hom :=
    (ConcreteCategory.isIso_iff_bijective e0.hom).mp (Iso.isIso_hom e0)
  have hinv : ∀ z : ratCoh (TopCat.of B) (r + 1), e1.inv.hom (e1.hom.hom z) = z := by
    intro z
    have h := congrArg (fun φ => ModuleCat.Hom.hom φ z) (Iso.hom_inv_id e1)
    simpa using h
  have he_ne : e1.inv.hom (1 : ℚ) ≠ 0 := by
    intro h
    have h0 : e1.hom.hom (e1.inv.hom (1 : ℚ)) = (1 : ℚ) := by
      have h4 := congrArg (fun φ => ModuleCat.Hom.hom φ (1 : ℚ)) (Iso.inv_hom_id e1)
      simpa using h4
    have h1 : e1.hom.hom (e1.inv.hom (1 : ℚ)) = 0 := by rw [h]; simp
    exact one_ne_zero (h0.symm.trans h1)
  set F : ratCoh (TopCat.of B) 0 →ₗ[ℚ] ratCoh (TopCat.of B) (0 + (r + 1)) :=
    (ratCup (TopCat.of B) 0 (r + 1)).flip (e1.inv.hom 1) with hF
  have hFu : F u = (Nat.zero_add (r + 1)).symm ▸ (e1.inv.hom 1) := by
    rw [hF]
    simp only [LinearMap.flip_apply]
    exact cast_eq_symm (Nat.zero_add (r + 1)) (hu_law (r + 1) (e1.inv.hom 1))
  have hz : F u ≠ 0 := by
    rw [hFu]
    intro h
    exact he_ne (eq_zero_of_cast_symm_eq_zero (Nat.zero_add (r + 1)) h)
  have hu_ne : u ≠ 0 := fun h0 => hz (by rw [h0, map_zero])
  have he0u : e0.hom.hom u ≠ 0 := fun h => hu_ne (hbij0.1 (by rw [h, map_zero]))
  have hgen : ∀ x : ratCoh (TopCat.of B) 0, ∃ c : ℚ, x = c • u := by
    intro x
    refine ⟨(e0.hom.hom u)⁻¹ * (e0.hom.hom x), ?_⟩
    have key : e0.hom.hom x = e0.hom.hom (((e0.hom.hom u)⁻¹ * (e0.hom.hom x)) • u) := by
      rw [map_smul, smul_eq_mul]
      field_simp
    exact hbij0.1 key
  have hvalue : ∀ c : ℚ, F (c • u) = c • F u := fun c => map_smul F c u
  refine ⟨e1.inv.hom (1 : ℚ), ?_⟩
  have hgoal : ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) (e1.inv.hom 1) 0) =
      ModuleCat.ofHom F := rfl
  rw [hgoal, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective F
  constructor
  · intro x y hxy
    obtain ⟨c, rfl⟩ := hgen x
    obtain ⟨d, rfl⟩ := hgen y
    have hcd : c = d := by
      have h6 : (c - d) • F u = 0 := by
        rw [sub_smul, ← hvalue c, ← hvalue d, hxy, sub_self]
      rcases smul_eq_zero.mp h6 with h7 | h7
      · exact sub_eq_zero.mp h7
      · exact absurd h7 hz
    rw [hcd]
  · intro y
    have hsym : e1.inv.hom (e1.hom.hom ((Nat.zero_add (r + 1)) ▸ y)) = (Nat.zero_add (r + 1)) ▸ y :=
      hinv _
    have hcz : (e1.hom.hom ((Nat.zero_add (r + 1)) ▸ y)) • (e1.inv.hom (1 : ℚ))
        = e1.inv.hom (e1.hom.hom ((Nat.zero_add (r + 1)) ▸ y)) := by
      rw [← map_smul]
      simp
    refine ⟨(e1.hom.hom ((Nat.zero_add (r + 1)) ▸ y)) • u, ?_⟩
    rw [hvalue, hFu, ← cast_smul_gen (Nat.zero_add (r + 1)), hcz, hsym]
    exact cast_cancel_src (Nat.zero_add (r + 1)) y

/-! ## The reduction -/

/-- **The reduction of `Work.Serre.gysinCupIso` to its additive content.**  Assume

* `hV1` : `H_k(B;ℚ) = 0` for `0 < k < b` (connectivity, see `isZero_ratH_of_conn_dup`);
* `hV2` : `H_k(B;ℚ) = 0` for `r+1 < k ≤ b+r` (the additive vanishing of the periodicity);
* `hm0` : the `m = 0` case (`exists_cupWith_zero_isIso`);

then there is `e ∈ H^{r+1}(B;ℚ)` with `⌣ e : H^m(B;ℚ) ≅ H^{m+r+1}(B;ℚ)` for all `m < b`.  For
`1 ≤ m < b` the class `e` plays no role: both sides are zero modules. -/
theorem exists_cupWith_isIso_of_vanishing {B : Type} [TopologicalSpace B]
    (b r : ℕ)
    (hV1 : ∀ k : ℕ, 0 < k → k < b → IsZero (ratH (TopCat.of B) k))
    (hV2 : ∀ k : ℕ, r + 1 < k → k ≤ b + r → IsZero (ratH (TopCat.of B) k))
    (hm0 : ∃ e : ratCoh (TopCat.of B) (r + 1),
      IsIso (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e 0))) :
    ∃ e : ratCoh (TopCat.of B) (r + 1),
      ∀ m : ℕ, m < b →
        IsIso (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e m)) := by
  obtain ⟨e, he⟩ := hm0
  refine ⟨e, fun m hm => ?_⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact he
  · have hz1 : IsZero (ratCoh (TopCat.of B) m) := isZero_ratCoh_of_isZero_ratH_dup (hV1 m hmpos hm)
    have hz2 : IsZero (ratCoh (TopCat.of B) (m + (r + 1))) :=
      isZero_ratCoh_of_isZero_ratH_dup (hV2 (m + (r + 1)) (by omega) (by omega))
    have hiso : ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e m) =
        (IsZero.iso hz1 hz2).hom := IsZero.eq_of_src hz1 _ _
    rw [hiso]
    exact Iso.isIso_hom _

/-! ## The reverse duality facts over `ℚ` -/

/-- Every nonzero element of a `ℚ`-vector space is detected by a linear functional. -/
theorem exists_dual_ne_zero (M : Type*) [AddCommGroup M] [Module ℚ M] (x : M) (hx : x ≠ 0) :
    ∃ g : M →ₗ[ℚ] ℚ, g x ≠ 0 := by
  haveI : Module.Free ℚ M := Module.Free.of_divisionRing ℚ M
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis ℚ M
  have h1 : b.repr x ≠ 0 := fun h => hx ((b.repr.map_eq_zero_iff).mp h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp h1
  exact ⟨b.coord i, by rwa [Module.Basis.coord_apply]⟩

/-- The `ℚ`-dual of `M` vanishes only if `M` does. -/
theorem isZero_of_isZero_dual (M : ModuleCat ℚ)
    (h : IsZero (ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ))) : IsZero M := by
  by_contra hM
  obtain ⟨x, hx⟩ : ∃ x : ↥M, x ≠ 0 := by
    by_contra hcon
    exact hM ((ModuleCat.isZero_iff_subsingleton).mpr ⟨fun a b => by
      by_contra hab
      exact hcon ⟨a - b, sub_ne_zero.mpr hab⟩⟩)
  obtain ⟨g, hg⟩ := exists_dual_ne_zero ↥M x hx
  haveI : Subsingleton (↥M →ₗ[ℚ] ℚ) := (ModuleCat.isZero_iff_subsingleton).mp h
  exact hg (by rw [Subsingleton.elim g 0]; rfl)

/-- A `ℚ`-module whose dual is `ℚ` is `ℚ`. -/
theorem nonempty_iso_rat_of_dual_iso_rat (M : ModuleCat ℚ)
    (e : ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ) ≅ ModuleCat.of ℚ ℚ) :
    Nonempty (M ≅ ModuleCat.of ℚ ℚ) := by
  have hval0 : e.hom.hom (e.inv.hom (1 : ℚ)) = 1 := by
    have h4 := congrArg (fun φ => ModuleCat.Hom.hom φ (1 : ℚ)) (Iso.inv_hom_id e)
    rw [ModuleCat.hom_comp] at h4
    simpa using h4
  have hf0_ne : e.inv.hom (1 : ℚ) ≠ 0 := fun h => one_ne_zero (by rw [← hval0, h, map_zero])
  set f₀ : ↥M →ₗ[ℚ] ℚ := e.inv.hom 1 with hf0
  have hval : e.hom.hom f₀ = 1 := by simpa [hf0] using hval0
  have hfinj : Function.Injective e.hom.hom :=
    ((ConcreteCategory.isIso_iff_bijective e.hom).mp (Iso.isIso_hom e)).1
  have hprop : ∀ g : ↥M →ₗ[ℚ] ℚ, ∃ c : ℚ, g = c • f₀ := by
    intro g
    refine ⟨e.hom.hom g, ?_⟩
    apply hfinj
    rw [map_smul, hval]
    simp
  have hker : ∀ x : ↥M, f₀ x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    obtain ⟨g, hg⟩ := exists_dual_ne_zero ↥M x hx0
    obtain ⟨c, hc⟩ := hprop g
    rw [hc] at hg
    simp [hx] at hg
  have hinj : Function.Injective f₀ := fun x y h => by
    have h2 : f₀ (x - y) = 0 := by rw [map_sub, h, sub_self]
    have h3 := hker (x - y) h2
    exact sub_eq_zero.mp h3
  have hsurj : Function.Surjective f₀ := by
    rw [← LinearMap.range_eq_top]
    rcases Ideal.eq_bot_or_top f₀.range with h | h
    · exfalso
      apply hf0_ne
      refine LinearMap.ext (fun x => ?_)
      by_contra hx
      have hmem : f₀ x ∈ f₀.range := ⟨x, rfl⟩
      rw [h] at hmem
      exact hx (by simpa using hmem)
    · exact h
  exact ⟨LinearEquiv.toModuleIso (LinearEquiv.ofBijective f₀ ⟨hinj, hsurj⟩)⟩

/-! ## The converse of the reduction -/

/-- **The converse of `exists_cupWith_isIso_of_vanishing`**: the conclusion of
`Work.Serre.gysinCupIso` gives back the additive vanishing `H_k(B;ℚ) = 0` for `r+1 < k ≤ b+r`,
which is the content of the requester's `Work.Serre.periodicity_of_serreFibration`.  Thus the
requested lemma is *equivalent* to that periodicity statement (together with
`H_{r+1}(B;ℚ) ≅ ℚ`, obtained from the `m = 0` instance of the conclusion in the same way). -/
theorem vanishing_of_exists_cupWith {B : Type} [TopologicalSpace B] (b r : ℕ)
    (hV1 : ∀ k : ℕ, 0 < k → k < b → IsZero (ratCoh (TopCat.of B) k))
    (h : ∃ e : ratCoh (TopCat.of B) (r + 1),
      ∀ m : ℕ, m < b → IsIso (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e m))) :
    ∀ k : ℕ, r + 1 < k → k ≤ b + r → IsZero (ratH (TopCat.of B) k) := by
  obtain ⟨e, he⟩ := h
  intro k hk1 hk2
  have hm : k - (r + 1) < b := by omega
  have hpos : 0 < k - (r + 1) := by omega
  have hz : IsZero (ratCoh (TopCat.of B) (k - (r + 1))) := hV1 (k - (r + 1)) hpos hm
  haveI hinst : IsIso (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e (k - (r + 1)))) :=
    he (k - (r + 1)) hm
  have hiso : ratCoh (TopCat.of B) (k - (r + 1)) ≅
      ratCoh (TopCat.of B) (k - (r + 1) + (r + 1)) :=
    @asIso _ _ _ _ (ModuleCat.ofHom (cupWith (TopCat.of B) (r + 1) e (k - (r + 1)))) hinst
  have hz2 : IsZero (ratCoh (TopCat.of B) (k - (r + 1) + (r + 1))) := IsZero.of_iso hz hiso.symm
  have hk : k - (r + 1) + (r + 1) = k := Nat.sub_add_cancel (by omega)
  rw [hk] at hz2
  have hz3 : IsZero (ModuleCat.of ℚ (↥(ratH (TopCat.of B) k) →ₗ[ℚ] ℚ)) :=
    IsZero.of_iso hz2 (Classical.choice (Work.StemsB.ratDualUCT (ratChains (TopCat.of B)) k)).symm
  exact isZero_of_isZero_dual _ hz3

end

end Work.Serre
