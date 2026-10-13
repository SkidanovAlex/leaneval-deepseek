import Mathlib
import Submission.Work.DSMap.Mix2

/-!
# DSM5b — coordinates on the honest chart Čech complex

Vocabulary for `Work.DSM5b.chartCech_cycle_iff_pairwise`: the degree-`0` (and `1`) terms of the
honest chart Čech complex `chartCech t = Č({D(t_i)}, W[J/t_i])` of `DSMap.Mix2` are read in the
coordinates given by the Čech nerve of the cover `i ↦ {i}`, and the localisation maps `locRes` are
assembled into a small transport toolkit.

* `ccIdx x = (∏ᶜ_a op {x a}).unop` is the value at the tuple `x` of the Čech nerve index
  (`ccIdx_eq_image : ccIdx x = univ.image x`);
* `ccZ W ι n t` is the family whose product is the degree-`n` term: `∏ᶜ ccZ = (chartCech t).X n`
  definitionally, so `ccC0`/`ccC1` are the coordinate linear equivalences;
* `ccDel a σ = σ ∘ Fin.succAbove a` is "delete the `a`-th entry" and `ccIdx_del_subset` the
  corresponding inclusion of index finsets;
* `ccRestr`/`ccCast` are the restriction of `locRes` to the chart rings, resp. its transport along
  an equality of finsets, and `ccAway` is the same transport on the localisations;
* `e0` is the linear equivalence `(chartCech t).X 0 ≃ₗ[W] ∀ i, W[J/t_i]`, compatible with the
  coaugmentation `chartCoaugW`.

Do NOT use the frozen sorried declarations of `DSMap.Mix2`.
-/

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite
open scoped Simplicial BigOperators

universe a

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! ## 1. The Čech nerve index of a tuple -/

/-- The Čech nerve index of a tuple `x : Fin (n+1) → ι`: the product in `(Finset ι)ᵒᵖ` of the
objects `op {x a}` corresponds to the union `⋃_a {x a} = {x 0, …, x n}`. -/
noncomputable abbrev ccIdx {ι : Type a} [DecidableEq ι] {n : ℕ} (x : Fin (n+1) → ι) : Finset ι :=
  (∏ᶜ (chartIdx ι ∘ x)).unop

lemma ccIdx_eq_image {ι : Type a} [DecidableEq ι] {n : ℕ} (x : Fin (n+1) → ι) :
    ccIdx x = Finset.univ.image x := by
  refine le_antisymm ?_ ?_
  · intro m hm
    have h : (∏ᶜ (chartIdx ι ∘ x)).unop ⊆ Finset.univ.image x :=
      leOfHom (Pi.lift (f := fun a => chartIdx ι (x a))
        (fun a => (homOfLE (Finset.singleton_subset_iff.mpr
          (Finset.mem_image_of_mem x (Finset.mem_univ a)))).op)).unop
    exact h hm
  · intro m hm
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hm
    have h : ({x a} : Finset ι) ≤ (∏ᶜ (chartIdx ι ∘ x)).unop :=
      leOfHom (Pi.π (fun a => chartIdx ι (x a)) a).unop
    exact h (Finset.mem_singleton_self _)

/-! ## 2. Tuples of indices: `ccConst`, `ccDel` -/

/-- The constant tuple at `i`. -/
abbrev ccConst {ι : Type a} (i : ι) : Fin 1 → ι := fun _ => i

lemma ccConst_zero {ι : Type a} (i : ι) : ccConst i 0 = i := rfl

/-- There is only one tuple `Fin 1 → ι` with a given value. -/
lemma ccUniq {ι : Type a} (x : Fin 1 → ι) : x = ccConst (x 0) := by
  funext b
  exact congrArg x (Subsingleton.elim b 0)

lemma ccIdx_singleton {ι : Type a} [DecidableEq ι] (x : Fin 1 → ι) : ccIdx x = {x 0} := by
  rw [ccIdx_eq_image, show (Finset.univ : Finset (Fin 1)) = {0} from rfl, Finset.image_singleton]

/-- The tuple `σ` with its `a`-th entry deleted. -/
abbrev ccDel {ι : Type a} {m : ℕ} (a : Fin (m+2)) (σ : Fin (m+2) → ι) : Fin (m+1) → ι :=
  σ ∘ Fin.succAbove a

lemma ccDel_apply {ι : Type a} {m : ℕ} (a : Fin (m+2)) (σ : Fin (m+2) → ι) (b : Fin (m+1)) :
    ccDel a σ b = σ (Fin.succAbove a b) := rfl

lemma ccImg_del_subset {ι : Type a} [DecidableEq ι] {m : ℕ} (a : Fin (m+2)) (σ : Fin (m+2) → ι) :
    Finset.univ.image (ccDel a σ) ⊆ Finset.univ.image σ := by
  intro x hx
  rw [Finset.mem_image] at hx ⊢
  obtain ⟨b, -, rfl⟩ := hx
  exact ⟨Fin.succAbove a b, Finset.mem_univ _, rfl⟩

lemma ccIdx_del_subset {ι : Type a} [DecidableEq ι] {m : ℕ} (a : Fin (m+2))
    (σ : Fin (m+2) → ι) : ccIdx (ccDel a σ) ⊆ ccIdx σ :=
  (le_of_eq (ccIdx_eq_image (ccDel a σ))).trans
    ((ccImg_del_subset a σ).trans (le_of_eq (ccIdx_eq_image σ).symm))

lemma ccDel_zero {ι : Type a} (σ : Fin 2 → ι) : ccDel 0 σ = ccConst (σ 1) := by
  funext b; fin_cases b; rfl

lemma ccDel_one {ι : Type a} (σ : Fin 2 → ι) : ccDel 1 σ = ccConst (σ 0) := by
  funext b; fin_cases b; rfl

lemma ccIdx_pair {ι : Type a} [DecidableEq ι] (σ : Fin 2 → ι) :
    ccIdx σ = ({σ 0} : Finset ι) ∪ {σ 1} := by
  rw [ccIdx_eq_image]
  ext m
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb⟩
    fin_cases b
    · exact Or.inl hb.symm
    · exact Or.inr hb.symm
  · rintro (h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

/-! ## 3. Coordinates on the chart Čech complex -/

/-- The family of modules whose product is the degree-`n` term of the chart Čech complex:
`∏ᶜ (ccZ W ι n t) = (chartCech t).X n` definitionally. -/
noncomputable abbrev ccZ.{u} (W : Type u) [CommRing W] (ι : Type u) [DecidableEq ι] (n : ℕ)
    (t : ι → W) : (Fin (n+1) → ι) → ModuleCat.{u} W :=
  fun x => ModuleCat.of W ↥(chartRing t (ccIdx x))

noncomputable def ccC0 (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W) :
    ↥((chartCech t).X 0) ≃ₗ[W] (∀ x : Fin 1 → ι, ↥(chartRing t (ccIdx x))) :=
  (ModuleCat.piIsoPi (ccZ W ι 0 t)).toLinearEquiv

noncomputable def ccC1 (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W) :
    ↥((chartCech t).X 1) ≃ₗ[W] (∀ x : Fin 2 → ι, ↥(chartRing t (ccIdx x))) :=
  (ModuleCat.piIsoPi (ccZ W ι 1 t)).toLinearEquiv

lemma ccC0_apply (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    (z : (chartCech t).X 0) (x : Fin 1 → ι) :
    ccC0 W ι t z x = (Pi.π (ccZ W ι 0 t) x).hom z := by
  rw [ccC0]
  erw [CategoryTheory.Iso.toLinearEquiv_apply]
  rw [ModuleCat.piIsoPi_hom_ker_subtype_apply]

lemma ccC1_apply (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    (z : (chartCech t).X 1) (x : Fin 2 → ι) :
    ccC1 W ι t z x = (Pi.π (ccZ W ι 1 t) x).hom z := by
  rw [ccC1]
  erw [CategoryTheory.Iso.toLinearEquiv_apply]
  rw [ModuleCat.piIsoPi_hom_ker_subtype_apply]

/-! ## 4. The `locRes` toolkit -/

lemma ccLocRes_comp {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V) :
    (locRes t h₂).comp (locRes t h₁) = locRes t (h₁.trans h₂) :=
  locRes_eq t (h₁.trans h₂) _

lemma ccLocRes_comp_apply {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T V : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ V) (x : Localization.Away (tS t S)) :
    locRes t h₂ (locRes t h₁ x) = locRes t (h₁.trans h₂) x :=
  congrArg (fun f : Localization.Away (tS t S) →ₐ[W] Localization.Away (tS t V) => f x)
    (ccLocRes_comp t h₁ h₂)

lemma ccLocRes_congr {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h h' : S ⊆ T) : locRes t h = locRes t h' :=
  (locRes_eq t h (locRes t h')).symm

lemma ccLocRes_rfl {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    (S : Finset ι) : locRes t (le_rfl : S ⊆ S) = AlgHom.id W _ :=
  (locRes_eq t le_rfl (AlgHom.id W _)).symm

/-- Transport of the localisation `W_{t_S}` along an equality of finsets. -/
noncomputable def ccAway {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S = T) :
    Localization.Away (tS t S) ≃+* Localization.Away (tS t T) where
  toFun := locRes t (le_of_eq h)
  invFun := locRes t (le_of_eq h.symm)
  left_inv x := by
    rw [ccLocRes_comp_apply t (le_of_eq h) (le_of_eq h.symm),
      ccLocRes_congr t ((le_of_eq h).trans (le_of_eq h.symm)) le_rfl, ccLocRes_rfl t S]
    rfl
  right_inv x := by
    rw [ccLocRes_comp_apply t (le_of_eq h.symm) (le_of_eq h),
      ccLocRes_congr t ((le_of_eq h.symm).trans (le_of_eq h)) le_rfl, ccLocRes_rfl t T]
    rfl
  map_mul' := map_mul _
  map_add' := map_add _

@[simp] lemma ccAway_apply {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S = T) (x : Localization.Away (tS t S)) :
    ccAway t h x = locRes t (le_of_eq h) x := rfl

lemma ccAway_src {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T T' : Finset ι} (hST : S = T) (h : T ⊆ T') (h' : S ⊆ T')
    (x : Localization.Away (tS t S)) : locRes t h (ccAway t hST x) = locRes t h' x := by
  rw [ccAway_apply, ccLocRes_comp_apply t (le_of_eq hST) h,
    ccLocRes_congr t ((le_of_eq hST).trans h) h']

lemma ccAway_tgt {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T T' : Finset ι} (hTT' : T = T') (h : S ⊆ T) (h' : S ⊆ T')
    (x : Localization.Away (tS t S)) : ccAway t hTT' (locRes t h x) = locRes t h' x := by
  rw [ccAway_apply, ccLocRes_comp_apply t h (le_of_eq hTT'),
    ccLocRes_congr t (h.trans (le_of_eq hTT')) h']

lemma ccAway_eq_zero {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S = T) (x : Localization.Away (tS t S)) :
    ccAway t h x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h1 := congrArg (locRes t (le_of_eq h.symm)) hx
    rw [map_zero, ccAway_apply, ccLocRes_comp_apply t (le_of_eq h) (le_of_eq h.symm),
      ccLocRes_congr t ((le_of_eq h).trans (le_of_eq h.symm)) le_rfl, ccLocRes_rfl t S,
      AlgHom.id_apply] at h1
    exact h1
  · intro hx; rw [hx, map_zero]

/-! ## 5. Restriction and transport of the chart rings -/

/-- The restriction map between chart rings, induced by `locRes`. -/
noncomputable def ccRestr {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S ⊆ T) : ↥(chartRing t S) →ₐ[W] ↥(chartRing t T) where
  toFun x := ⟨locRes t h x.1, chartRing_map_le t h ⟨x.1, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (locRes t h))
  map_mul' x y := Subtype.ext (map_mul (locRes t h) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (locRes t h))
  map_add' x y := Subtype.ext (map_add (locRes t h) x.1 y.1)
  commutes' r := Subtype.ext ((locRes t h).commutes r)

@[simp] lemma ccRestr_coe {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S ⊆ T) (x : ↥(chartRing t S)) :
    ((ccRestr t h x : ↥(chartRing t T)) : Localization.Away (tS t T)) = locRes t h x.1 := rfl

/-- Transport of the chart ring along an equality of finsets. -/
noncomputable def ccCast {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S = T) : ↥(chartRing t S) ≃ₗ[W] ↥(chartRing t T) where
  toFun := ccRestr t (le_of_eq h)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := ccRestr t (le_of_eq h.symm)
  left_inv x := by
    apply Subtype.ext
    simp only [ccRestr_coe]
    rw [ccLocRes_comp_apply t (le_of_eq h) (le_of_eq h.symm),
      ccLocRes_congr t ((le_of_eq h).trans (le_of_eq h.symm)) le_rfl, ccLocRes_rfl t S]
    rfl
  right_inv x := by
    apply Subtype.ext
    simp only [ccRestr_coe]
    rw [ccLocRes_comp_apply t (le_of_eq h.symm) (le_of_eq h),
      ccLocRes_congr t ((le_of_eq h.symm).trans (le_of_eq h)) le_rfl, ccLocRes_rfl t T]
    rfl

@[simp] lemma ccCast_apply {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S = T) (x : ↥(chartRing t S)) :
    ccCast t h x = ccRestr t (le_of_eq h) x := rfl

lemma ccCast_rfl {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    (S : Finset ι) : ccCast t (rfl : S = S) = LinearEquiv.refl W ↥(chartRing t S) := by
  ext x
  simp only [ccCast_apply, ccRestr_coe, LinearEquiv.refl_apply]
  rw [ccLocRes_congr t (le_of_eq (rfl : S = S)) le_rfl, ccLocRes_rfl t S]
  rfl

lemma ccCast_trans {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T V : Finset ι} (h : S = T) (h' : T = V) (y : ↥(chartRing t S)) :
    ccCast t h' (ccCast t h y) = ccCast t (h.trans h') y := by
  apply Subtype.ext
  simp only [ccCast_apply, ccRestr_coe]
  rw [ccLocRes_comp_apply t (le_of_eq h) (le_of_eq h'),
    ccLocRes_congr t ((le_of_eq h).trans (le_of_eq h')) (le_of_eq (h.trans h'))]

lemma ccCast_symm_apply {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S = T) (y : ↥(chartRing t T)) :
    (ccCast t h).symm y = ccCast t h.symm y := rfl

lemma ccCast_coe {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S = T) (y : ↥(chartRing t S)) :
    ((ccCast t h y : ↥(chartRing t T)) : Localization.Away (tS t T))
      = ccAway t h (y : Localization.Away (tS t S)) := rfl

lemma ccCast_algebraMap {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (h : S = T) (w : W) :
    ccCast t h (algebraMap W ↥(chartRing t S) w) =
      ⟨algebraMap W (Localization.Away (tS t T)) w, (chartRing t T).algebraMap_mem w⟩ := by
  apply Subtype.ext
  rw [ccCast_apply, ccRestr_coe, Subalgebra.coe_algebraMap, AlgHom.commutes]

/-! ## 6. Components of the coaugmentation -/

lemma ccPiLift_apply {M : Type*} [Ring M] {β : Type*} {f : β → ModuleCat M} [HasProduct f]
    {P : ModuleCat M} (p : (b : β) → P ⟶ f b) (b : β) (x : ↥P) :
    (Pi.π f b).hom ((Pi.lift p).hom x) = (p b).hom x := by
  rw [← ModuleCat.comp_apply, Pi.lift_comp_π]

lemma ccCoaug_apply (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W) (w : W)
    (x : Fin 1 → ι) :
    (Pi.π (ccZ W ι 0 t) x).hom ((chartCoaugW t).hom w)
      = algebraMap W ↥(chartRing t (ccIdx x)) w := by
  rw [chartCoaugW]
  exact ccPiLift_apply (f := ccZ W ι 0 t)
    (p := fun y => ModuleCat.ofHom (Algebra.linearMap W ↥(chartRing t (ccIdx y)))) x w

/-! ## 7. The equivalence `e0 : (chartCech t).X 0 ≃ₗ[W] ∀ i, W[J/t_i]` -/

abbrev ccPiEquiv (ι : Type a) : (Fin 1 → ι) ≃ ι where
  toFun x := x 0
  invFun i := fun _ => i
  left_inv x := by funext b; fin_cases b; rfl
  right_inv i := rfl

noncomputable def ccReindex (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W) :
    (∀ x : Fin 1 → ι, ↥(chartRing t {x 0})) ≃ₗ[W] (∀ i : ι, ↥(chartRing t {i})) :=
  LinearEquiv.piCongrLeft' W (fun x : Fin 1 → ι => ↥(chartRing t {x 0})) (ccPiEquiv ι)

lemma ccReindex_apply (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    (f : ∀ x : Fin 1 → ι, ↥(chartRing t {x 0})) (i : ι) :
    ccReindex W ι t f i = f (ccConst i) := by
  rw [ccReindex]
  erw [LinearEquiv.piCongrLeft'_apply]
  rfl

/-- The degree-`0` term of the chart Čech complex, in the coordinates given by the chart cover. -/
noncomputable def e0 (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W) :
    ↥((chartCech t).X 0) ≃ₗ[W] (∀ i : ι, ↥(chartRing t {i})) :=
  (ccC0 W ι t).trans
    ((LinearEquiv.piCongrRight (fun x : Fin 1 → ι => ccCast t (ccIdx_singleton x))).trans
      (ccReindex W ι t))

lemma ccPiCongrRight_apply' (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    (f : ∀ x : Fin 1 → ι, ↥(chartRing t (ccIdx x))) (i : ι) :
    (LinearEquiv.piCongrRight (fun x : Fin 1 → ι => ccCast t (ccIdx_singleton x))) f (ccConst i)
      = ccCast t (ccIdx_singleton (ccConst i)) (f (ccConst i)) := by
  erw [LinearEquiv.piCongrRight_apply]

lemma e0_apply (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    (z : ↥((chartCech t).X 0)) (i : ι) :
    e0 W ι t z i = ccCast t (ccIdx_singleton (ccConst i)) (ccC0 W ι t z (ccConst i)) := by
  show (ccReindex W ι t) ((LinearEquiv.piCongrRight
    (fun x : Fin 1 → ι => ccCast t (ccIdx_singleton x))) ((ccC0 W ι t) z)) i = _
  rw [ccReindex_apply]
  exact ccPiCongrRight_apply' W ι t (ccC0 W ι t z) i

lemma e0_coaug (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W) (w : W)
    (i : ι) :
    e0 W ι t ((chartCoaugW t).hom w) i = algebraMap W ↥(chartRing t {i}) w := by
  rw [e0_apply, ccC0_apply, ccCoaug_apply, ccCast_algebraMap]
  apply Subtype.ext
  rw [Subalgebra.coe_algebraMap]

/-! ## 8. Transport of the coordinates along an equality of tuples -/

/-- The coordinates of the Čech complex commute with the canonical transport of the index
tuples: the `x`-component of `z` transported along `ccIdx x = ccIdx x'` is the `x'`-component. -/
lemma ccC0_congr (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    {x x' : Fin 1 → ι} (h : x = x') (z : ↥((chartCech t).X 0)) :
    ccCast t (congrArg ccIdx h) (ccC0 W ι t z x) = ccC0 W ι t z x' := by
  cases h
  rw [ccCast_rfl]
  rfl

/-- The same, read in the localisation. -/
lemma ccC0_congr_coe (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    {x x' : Fin 1 → ι} (h : x = x') (z : ↥((chartCech t).X 0)) :
    ccAway t (congrArg ccIdx h) ((ccC0 W ι t z x : ↥(chartRing t (ccIdx x)))
        : Localization.Away (tS t (ccIdx x)))
      = ((ccC0 W ι t z x' : ↥(chartRing t (ccIdx x')))
        : Localization.Away (tS t (ccIdx x'))) := by
  have h2 := congrArg (fun y : ↥(chartRing t (ccIdx x')) =>
    (y : Localization.Away (tS t (ccIdx x')))) (ccC0_congr W ι t h z)
  rw [ccCast_coe] at h2
  exact h2

end Work.DSM5b
