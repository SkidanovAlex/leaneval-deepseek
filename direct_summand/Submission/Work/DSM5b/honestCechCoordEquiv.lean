import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSM5b.H0Defs
import Submission.Work.DSM5b.perfChartCoaug_kernel
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSSEC.Defs

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open Opposite Limits
open scoped Simplicial BigOperators

universe a

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

/-!
# Coordinates for the degree-`0` part of the honest chart Čech complex

Infrastructure for `Work.DSM5b.honestCechCoordEquiv` (see the docstring of the theorem at the end of
this file): the degree-`n` term `((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).X n` of
the chart Čech complex is the product, over the `n`-simplices `x : Fin (n+1) → ι`, of the chart
rings `chartRing t (SIdx x)`, where `SIdx x = (∏ᶜ (chartIdx ι ∘ x)).unop` is the underlying finset
of the `x`-th index object of the Čech nerve of the cover `i ↦ {i}`.  Since a product in the thin
category `(Finset ι)ᵒᵖ` of singletons is their union, `SIdx x = tupRng x` (`SIdx_eq_tupRng`), which
is the combinatorial content of the coordinate description.

The restriction maps between the chart rings are `locRes t h`, and the transports between the two
presentations `chartRing t (SIdx x)` and `chartRing t (tupRng x)` are realised by `locRes` (rather
than by `Eq.rec`), so that all computations are done with the proof-irrelevant composition and
congruence rules `locRes_comp`, `locRes_congr`, `locRes_rfl`.
-/

/-- The nerve index type of the degree-`n` term of the chart Čech complex. -/
noncomputable abbrev IdxN {ι : Type a} [DecidableEq ι] (n : ℕ) : Type a :=
  ((FormalCoproduct.mk ι (chartIdx ι)).cech.obj (op ⦋n⦌)).I

/-- The underlying finset of the `x`-th index object of the Čech nerve of the chart cover
`i ↦ {i}`, in the nerve form of the indexing type. -/
noncomputable abbrev SIdxN {ι : Type a} [DecidableEq ι] {n : ℕ} (x : IdxN (ι := ι) n) : Finset ι :=
  (∏ᶜ (chartIdx ι ∘ x)).unop

/-- `SIdxN x` is the range of the tuple: a product in the thin category `(Finset ι)ᵒᵖ` of
singletons is their union. -/
lemma SIdxN_eq_tupRng {ι : Type a} [DecidableEq ι] {n : ℕ} (x : IdxN (ι := ι) n) :
    SIdxN x = tupRng x := by
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

/-- The underlying finset of the `x`-th index object of the Čech nerve of the chart cover
`i ↦ {i}`, for `Fin`-indexed tuples. -/
noncomputable abbrev SIdx {ι : Type a} [DecidableEq ι] {n : ℕ} (x : Fin (n + 1) → ι) : Finset ι :=
  (∏ᶜ (chartIdx ι ∘ x)).unop

lemma SIdx_eq_tupRng {ι : Type a} [DecidableEq ι] {n : ℕ} (x : Fin (n + 1) → ι) :
    SIdx x = tupRng x := by
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

/-! ## Elementary `ℤ`/`R`-scalar and sum bookkeeping -/

lemma zsmul_neg_one_eq (R : Type*) [Ring R] {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ)
    (x : M) : ((-1 : ℤ) ^ n) • x = ((-1 : R) ^ n) • x := by
  rw [← Int.cast_smul_eq_zsmul (R := R), Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- Distributing a sum of linear maps over an element. -/
lemma sum_apply_linearMap {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (g : ι → (M →ₗ[R] N)) (z : M) :
    (∑ i ∈ s, f i • g i) z = ∑ i ∈ s, f i • g i z := by
  have h := map_sum ({ toFun := fun g : M →ₗ[R] N => g z
                       map_zero' := rfl
                       map_add' := fun a b => by simp } : (M →ₗ[R] N) →+ N)
    (fun i => f i • g i) s
  simpa using h

/-- A linear equivalence distributes over a finite sum of scalar multiples. -/
lemma le_map_sum_smul {R : Type*} [Ring R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) {ι : Type*} (s : Finset ι) (c : ι → R) (f : ι → M) :
    e (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • e (f i) := by
  have h := map_sum e.toLinearMap (fun i => c i • f i) s
  simpa only [LinearEquiv.coe_toLinearMap, map_smul, LinearMap.smul_apply] using h

section Loc
variable {ι : Type a} [DecidableEq ι] {R : Type a} [CommRing R]

lemma locRes_comp (t : ι → R) {S T V : Finset ι} (h₁ : S ≤ T) (h₂ : T ≤ V)
    (x : Localization.Away (tS t S)) :
    locRes t h₂ (locRes t h₁ x) = locRes t (h₁.trans h₂) x :=
  DFunLike.congr_fun (locRes_eq t (h₁.trans h₂) ((locRes t h₂).comp (locRes t h₁))) x

lemma locRes_congr (t : ι → R) {S T : Finset ι} (h h' : S ≤ T) : locRes t h = locRes t h' :=
  (locRes_eq t h (locRes t h')).symm

lemma locRes_rfl (t : ι → R) (S : Finset ι) : locRes t (le_rfl : S ≤ S) = AlgHom.id R _ :=
  (locRes_eq t le_rfl (AlgHom.id R _)).symm

noncomputable def chartLift (t : ι → R) {S T : Finset ι} (h : S = T) :
    ↥(chartRing t S) ≃ₗ[R] ↥(chartRing t T) where
  toFun x := rhoH t (le_of_eq h) x
  map_add' x y := map_add _ x y
  map_smul' r x := map_smul _ r x
  invFun y := rhoH t (le_of_eq h.symm) y
  left_inv x := by
    apply Subtype.ext
    refine (locRes_comp t (le_of_eq h) (le_of_eq h.symm) x.1).trans ?_
    rw [locRes_congr t ((le_of_eq h).trans (le_of_eq h.symm)) (le_rfl : S ≤ S), locRes_rfl]
    rfl
  right_inv y := by
    apply Subtype.ext
    refine (locRes_comp t (le_of_eq h.symm) (le_of_eq h) y.1).trans ?_
    rw [locRes_congr t ((le_of_eq h.symm).trans (le_of_eq h)) (le_rfl : T ≤ T), locRes_rfl]
    rfl

@[simp] lemma chartLift_apply (t : ι → R) {S T : Finset ι} (h : S = T) (x : ↥(chartRing t S)) :
    chartLift t h x = rhoH t (le_of_eq h) x := rfl

@[simp] lemma chartLift_coe (t : ι → R) {S T : Finset ι} (h : S = T) (x : ↥(chartRing t S)) :
    (chartLift t h x : Localization.Away (tS t T)) = locRes t (le_of_eq h) x.1 := rfl

/-- The action of a chart presheaf map on underlying elements. -/
lemma chartPresheaf_map_apply (t : ι → R) {X Y : (Finset ι)ᵒᵖᵒᵖ} (F : X ⟶ Y)
    (y : ↥((chartPresheaf t).obj X)) :
    ((chartPresheaf t).map F y).1 = locRes t (leOfHom F.unop.unop) y.1 := rfl

lemma chartLift_rfl (t : ι → R) (S : Finset ι) (x : ↥(chartRing t S)) :
    chartLift t (rfl : S = S) x = x := by
  apply Subtype.ext
  rw [chartLift_apply, rhoH_coe, locRes_rfl]
  rfl

/-- `chartLift` is the identity on the images of `R`. -/
lemma chartLift_algebraMap (t : ι → R) {S T : Finset ι} (h : S = T) (w : R) :
    chartLift t h (algebraMap R ↥(chartRing t S) w) =
      ⟨algebraMap R (Localization.Away (tS t T)) w, (chartRing t T).algebraMap_mem w⟩ := by
  apply Subtype.ext
  rw [chartLift_apply, rhoH_coe, Subalgebra.coe_algebraMap, AlgHom.commutes]

end Loc
noncomputable abbrev chartCechK (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) : CochainComplex (ModuleCat.{a} R) ℕ :=
  (cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)

noncomputable abbrev YfN (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (n : ℕ) : IdxN (ι := ι) n → ModuleCat.{a} R :=
  fun x => (chartPresheaf t).obj (op (((FormalCoproduct.mk ι (chartIdx ι)).cech.obj (op ⦋n⦌)).obj x))

noncomputable abbrev cofN {ι : Type a} [DecidableEq ι] {n : ℕ} (a : Fin (n+2))
    (σ : IdxN (ι := ι) (n+1)) : IdxN (ι := ι) n :=
  (((FormalCoproduct.mk ι (chartIdx ι)).cech.map (SimplexCategory.δ a).op).f σ)

noncomputable abbrev cophiN (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) {n : ℕ} (a : Fin (n+2)) (σ : IdxN (ι := ι) (n+1)) :
    YfN R t n (cofN a σ) ⟶ YfN R t (n+1) σ :=
  (chartPresheaf t).map
    (((FormalCoproduct.mk ι (chartIdx ι)).cech.map (SimplexCategory.δ a).op).φ σ).op

lemma d01_apply_nerve {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R)
    (z : ↥(∏ᶜ (YfN R t 0))) (σ : IdxN (ι := ι) (0+1)) :
    (Pi.π (YfN R t (0+1)) σ).hom
        (show ↥(∏ᶜ (YfN R t (0+1))) from ((chartCechK R t).d 0 (0+1)).hom
          (show ↥((chartCechK R t).X 0) from z))
      = ∑ a : Fin (0+2), ((-1 : ℤ) ^ (a : ℕ)) •
          (cophiN R t a σ).hom ((Pi.π (YfN R t 0) (cofN a σ)).hom z) := by
  have h := cech_d_π (U := chartIdx ι) (P := chartPresheaf t) (n := 0) σ
  have h2 := congrArg (fun φ => φ.hom (show ↥((chartCechK R t).X 0) from z)) h
  have hL : ((chartCechK R t).d 0 (0+1) ≫ Pi.π (YfN R t (0+1)) σ).hom
        (show ↥((chartCechK R t).X 0) from z)
      = (Pi.π (YfN R t (0+1)) σ).hom
        (show ↥(∏ᶜ (YfN R t (0+1))) from ((chartCechK R t).d 0 (0+1)).hom
          (show ↥((chartCechK R t).X 0) from z)) := by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    rfl
  have hR : (∑ a : Fin (0+2), ((-1 : ℤ) ^ (a : ℕ)) •
        (Pi.π (YfN R t 0) (cofN a σ) ≫ cophiN R t a σ)).hom
          (show ↥((chartCechK R t).X 0) from z)
      = ∑ a : Fin (0+2), ((-1 : ℤ) ^ (a : ℕ)) •
          (cophiN R t a σ).hom ((Pi.π (YfN R t 0) (cofN a σ)).hom z) := by
    rw [ModuleCat.hom_sum]
    simp only [ModuleCat.hom_zsmul]
    rw [sum_apply_linearMap]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hL] at h2
  erw [hR] at h2
  exact h2

-- the transport of projections
lemma pi_π_transport {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) {n : ℕ}
    {X Y : IdxN (ι := ι) n} (h : X = Y) (z : ↥(∏ᶜ (YfN R t n))) :
    (Pi.π (YfN R t n) Y).hom z
      = chartLift t (congrArg (SIdx (ι := ι)) h) ((Pi.π (YfN R t n) X).hom z) := by
  cases h
  rw [chartLift_rfl]

-- the nerve-side Pi type
noncomputable abbrev QN (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) (n : ℕ) :
    Type a := (i : IdxN (ι := ι) n) → ↥(YfN R t n i)

noncomputable abbrev PhiN (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) (n : ℕ) :
    ↥(∏ᶜ (YfN R t n)) ≃ₗ[R] QN R t n :=
  (ModuleCat.piIsoPi (YfN R t n)).toLinearEquiv

lemma PhiN_apply {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) (n : ℕ)
    (z : ↥(∏ᶜ (YfN R t n))) (i : IdxN (ι := ι) n) :
    PhiN R t n z i = (Pi.π (YfN R t n) i).hom z :=
  ModuleCat.piIsoPi_hom_ker_subtype_apply (YfN R t n) i z

-- the second factor: SIdx-rings to tupRng-rings
noncomputable def e (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) (n : ℕ) :
    QN R t n ≃ₗ[R] ((x : Fin (n+1) → ι) → ↥(chartRing t (tupRng x))) where
  toFun u := fun x => chartLift t (SIdxN_eq_tupRng x) (u x)
  map_add' u v := by funext x; simp [Pi.add_apply, map_add]
  map_smul' r u := by funext x; simp [Pi.smul_apply, map_smul]
  invFun v := fun i => (chartLift t (SIdxN_eq_tupRng i)).symm (v i)
  left_inv u := by funext i; exact (chartLift t (SIdxN_eq_tupRng i)).symm_apply_apply (u i)
  right_inv v := by funext i; exact (chartLift t (SIdxN_eq_tupRng i)).apply_symm_apply (v i)

noncomputable abbrev Phi (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) (n : ℕ) :
    ↥(∏ᶜ (YfN R t n)) ≃ₗ[R] ((x : Fin (n+1) → ι) → ↥(chartRing t (tupRng x))) :=
  (PhiN R t n).trans (e R t n)

lemma Phi_apply {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) (n : ℕ)
    (z : ↥(∏ᶜ (YfN R t n))) (x : Fin (n+1) → ι) :
    Phi R t n z x = chartLift t (SIdxN_eq_tupRng x) ((Pi.π (YfN R t n) x).hom z) := by
  show e R t n (PhiN R t n z) x = _
  show chartLift t (SIdxN_eq_tupRng x) (PhiN R t n z x) = _
  rw [PhiN_apply]



-- the face map of the Cech nerve is tupDel
lemma cof_eq_tupDel {ι : Type a} [DecidableEq ι] (a : Fin (0+2)) (σ : IdxN (ι := ι) (0+1)) :
    cofN a σ = tupDel a σ := by
  funext b
  rfl


-- nerve-native tuple operations
noncomputable abbrev rngN {ι : Type a} [DecidableEq ι] {n : ℕ} (x : IdxN (ι := ι) n) : Finset ι :=
  Finset.univ.image x

noncomputable abbrev delN {ι : Type a} [DecidableEq ι] {n : ℕ} (a : Fin (n+2))
    (σ : IdxN (ι := ι) (n+1)) : IdxN (ι := ι) n := σ ∘ Fin.succAbove a

lemma cof_eq_delN {ι : Type a} [DecidableEq ι] (a : Fin (0+2)) (σ : IdxN (ι := ι) (0+1)) :
    cofN a σ = delN a σ := by
  funext b
  rfl

-- the inclusion of the deleted tuple's chart set
lemma SIdxN_delN_subset {ι : Type a} [DecidableEq ι] {n : ℕ} (a : Fin (n+2))
    (σ : IdxN (ι := ι) (n+1)) : SIdx (delN a σ) ⊆ SIdx σ := by
  intro m hm
  have h : (∏ᶜ (chartIdx ι ∘ delN a σ)).unop ⊆ Finset.univ.image (delN a σ) :=
    leOfHom (Pi.lift (f := fun b => chartIdx ι (delN a σ b))
      (fun b => (homOfLE (Finset.singleton_subset_iff.mpr
        (Finset.mem_image_of_mem (delN a σ) (Finset.mem_univ b)))).op)).unop
  have hm' : m ∈ Finset.univ.image (delN a σ) := h hm
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hm'
  -- m = delN a σ b = σ (Fin.succAbove a b) ∈ SIdx σ
  have h2 : ({σ (Fin.succAbove a b)} : Finset ι) ≤ (∏ᶜ (chartIdx ι ∘ σ)).unop :=
    leOfHom (Pi.π (fun b => chartIdx ι (σ b)) (Fin.succAbove a b)).unop
  exact h2 (Finset.mem_singleton_self _)

-- the nerve-native differential
noncomputable def HCdN (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) (n : ℕ) :
    (∀ x : IdxN (ι := ι) n, ↥(chartRing t (SIdx x))) →ₗ[R]
      (∀ x : IdxN (ι := ι) (n+1), ↥(chartRing t (SIdx x))) where
  toFun u := fun σ => ∑ i : Fin (n+2), ((-1 : R) ^ (i : ℕ)) •
    rhoH t (SIdxN_delN_subset (ι := ι) i σ) (u (delN i σ))
  map_add' u v := by
    funext σ
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' r u := by
    funext σ
    simp only [Pi.smul_apply, RingHom.id_apply, map_smul, smul_comm r, Finset.smul_sum]

lemma HCdN_apply (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) (n : ℕ)
    (u : ∀ x : IdxN (ι := ι) n, ↥(chartRing t (SIdx x))) (σ : IdxN (ι := ι) (n+1)) :
    HCdN R t n u σ = ∑ i : Fin (n+2), ((-1 : R) ^ (i : ℕ)) •
      rhoH t (SIdxN_delN_subset (ι := ι) i σ) (u (delN i σ)) := rfl

-- the per-summand comparison for the chain identity
lemma key {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R)
    (a : Fin (0+2)) (σ : IdxN (ι := ι) (0+1)) (w : ↥(YfN R t 0 (cofN a σ))) :
    (cophiN R t a σ).hom w
      = rhoH t (SIdxN_delN_subset (ι := ι) a σ)
          (chartLift t (congrArg (SIdx (ι := ι)) (cof_eq_delN a σ)) w) := by
  apply Subtype.ext
  rw [rhoH_coe, chartLift_coe, chartPresheaf_map_apply]
  rw [locRes_comp]
  exact DFunLike.congr_fun (locRes_congr t _ _) w.1

-- the chain identity in nerve coordinates
lemma chainN {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R)
    (z : ↥(∏ᶜ (YfN R t 0))) :
    PhiN R t (0+1) (show ↥(∏ᶜ (YfN R t (0+1))) from ((chartCechK R t).d 0 (0+1)).hom
        (show ↥((chartCechK R t).X 0) from z))
      = HCdN R t 0 (PhiN R t 0 z) := by
  funext σ
  rw [PhiN_apply, d01_apply_nerve, HCdN_apply]
  have hconv : (∑ a : Fin (0+2), ((-1 : ℤ) ^ (a : ℕ)) •
        (cophiN R t a σ).hom ((Pi.π (YfN R t 0) (cofN a σ)).hom z))
      = ∑ a : Fin (0+2), ((-1 : R) ^ (a : ℕ)) •
        (cophiN R t a σ).hom ((Pi.π (YfN R t 0) (cofN a σ)).hom z) :=
    Finset.sum_congr rfl (fun a _ =>
      zsmul_neg_one_eq R (a : ℕ) ((cophiN R t a σ).hom ((Pi.π (YfN R t 0) (cofN a σ)).hom z)))
  rw [hconv]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [PhiN_apply]
  rw [pi_π_transport (t := t) (X := cofN a σ) (Y := delN a σ) (cof_eq_delN a σ) z]
  rw [key t a σ]



/-- The coordinate equivalence used in the main theorem (nerve-native, transported to the
`tupRng`-presentation of the chart rings). -/
noncomputable abbrev PhiT (R : Type a) [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R) :
    ↥(((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).X 0) ≃ₗ[R] HCX t 0 :=
  Phi R t 0

/-- The component of the coaugmentation of the chart Čech complex. -/
lemma caug_component {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R)
    (w : R) (x : IdxN (ι := ι) 0) :
    (Pi.π (YfN R t 0) x).hom (show ↥(∏ᶜ (YfN R t 0)) from (chartCoaugW t).hom w)
      = algebraMap R ↥(chartRing t (SIdxN x)) w := by
  have hpc : (show ↥(∏ᶜ (YfN R t 0)) from (chartCoaugW t).hom w)
      = (Pi.lift (fun y : IdxN (ι := ι) 0 =>
          ModuleCat.ofHom (Algebra.linearMap R ↥(chartRing t (SIdxN y))))).hom w := rfl
  rw [hpc]
  exact pi_lift_apply_π (M := R)
    (f := fun y : IdxN (ι := ι) 0 => ModuleCat.of R ↥(chartRing t (SIdxN y)))
    (p := fun y => ModuleCat.ofHom (Algebra.linearMap R ↥(chartRing t (SIdxN y)))) x w

/-- The tuple `delN a σ` is the deleted tuple, in the `Fin`-form. -/
lemma delN_eq_tupDel {ι : Type a} [DecidableEq ι] (a : Fin (0+2)) (σ : IdxN (ι := ι) (0+1)) :
    delN a σ = tupDel a σ := by
  funext b
  rfl

/-- The per-coface comparison between the chart Čech differential (in nerve coordinates) and the
concrete `tupRng`/`tupDel`-based alternating coface differential `HCd`. -/
lemma keyHCd {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R)
    (z : ↥(∏ᶜ (YfN R t 0))) (a : Fin (0+2)) (σ : IdxN (ι := ι) (0+1)) :
    chartLift t (SIdxN_eq_tupRng σ)
        (rhoH t (SIdxN_delN_subset a σ)
          (chartLift t (congrArg (SIdxN (ι := ι)) (cof_eq_delN a σ))
            ((Pi.π (YfN R t 0) (cofN a σ)).hom z)))
      = rhoH t (tupRng_del_subset a σ) ((Phi R t 0 z) (tupDel a σ)) := by
  rw [Phi_apply]
  rw [pi_π_transport (t := t) (X := delN a σ) (Y := tupDel a σ) (delN_eq_tupDel a σ) z]
  rw [← pi_π_transport (t := t) (X := cofN a σ) (Y := delN a σ) (cof_eq_delN a σ) z]
  apply Subtype.ext
  simp only [chartLift_coe, rhoH_coe, locRes_comp]

/-- The coface comparison of `keyHCd` in terms of the nerve-coordinate equivalence `PhiN`. -/
lemma keyHCd' {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R)
    (z : ↥(∏ᶜ (YfN R t 0))) (a : Fin (0+2)) (σ : IdxN (ι := ι) (0+1)) :
    chartLift t (SIdxN_eq_tupRng σ)
        (rhoH t (SIdxN_delN_subset a σ) ((PhiN R t 0 z) (delN a σ)))
      = rhoH t (tupRng_del_subset a σ) ((Phi R t 0 z) (tupDel a σ)) := by
  rw [PhiN_apply]
  rw [pi_π_transport (t := t) (X := cofN a σ) (Y := delN a σ) (cof_eq_delN a σ) z]
  exact keyHCd t z a σ

/-- The component formula of `HCd t 0`, for nerve-typed simplices. -/
lemma HCd_component {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R)
    (u : HCX t 0) (σ : IdxN (ι := ι) (0+1)) :
    HCd t 0 u σ = ∑ i : Fin (0+2), ((-1 : R) ^ (i : ℕ)) •
      rhoH t (tupRng_del_subset i σ) (u (tupDel i σ)) := rfl

/-- **The chain identity**: the coordinate equivalence `Phi` intertwines the chart Čech
differential `d 0 1` with the concrete alternating coface differential `HCd`. -/

lemma chainPhi {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι] (t : ι → R)
    (z : ↥(∏ᶜ (YfN R t 0))) (σ : IdxN (ι := ι) (0+1)) :
    Phi R t (0+1) (show ↥(∏ᶜ (YfN R t (0+1))) from ((chartCechK R t).d 0 (0+1)).hom
        (show ↥((chartCechK R t).X 0) from z)) σ
      = HCd t 0 (Phi R t 0 z) σ := by
  rw [Phi_apply]
  rw [← PhiN_apply]
  rw [congrFun (chainN (t := t) z) σ]
  rw [HCdN_apply]
  rw [le_map_sum_smul]
  rw [HCd_component]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [keyHCd' t z a σ]

/-- The component of the coaugmentation of the chart Čech complex. -/
theorem honestCechCoordEquiv (R : Type a) [CommRing R] {ι : Type a} [Finite ι] [DecidableEq ι]
    (t : ι → R) :
    ∃ Φ : ↥(((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).X 0) ≃ₗ[R] HCX t 0,
      (∀ w : R, Φ ((chartCoaugW t).hom w) =
        fun τ : Fin 1 → ι =>
          ⟨algebraMap R (Localization.Away (tS t (tupRng τ))) w,
            (chartRing t (tupRng τ)).algebraMap_mem w⟩) ∧
      (∀ z : ↥(((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).X 0),
        ((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).d 0 1 z = 0 ↔
          HCd t 0 (Φ z) = 0) := by
  refine ⟨Phi R t 0, ?_, ?_⟩
  · intro w
    funext τ
    change Phi R t 0 (show ↥(∏ᶜ (YfN R t 0)) from (chartCoaugW t).hom w) τ =
      ⟨algebraMap R (Localization.Away (tS t (tupRng τ))) w,
        (chartRing t (tupRng τ)).algebraMap_mem w⟩
    rw [Phi_apply]
    rw [caug_component t w τ]
    rw [chartLift_algebraMap]
  · intro z
    constructor
    · intro hz
      have hz' : ((chartCechK R t).d 0 (0+1)).hom
          (show ↥((chartCechK R t).X 0) from (show ↥(∏ᶜ (YfN R t 0)) from z)) = 0 := hz
      funext σ
      erw [← chainPhi (t := t) (show ↥(∏ᶜ (YfN R t 0)) from z) σ, hz']
      simp
    · intro hz
      have h1 : Phi R t (0+1) (show ↥(∏ᶜ (YfN R t (0+1))) from
          ((chartCechK R t).d 0 (0+1)).hom
            (show ↥((chartCechK R t).X 0) from (show ↥(∏ᶜ (YfN R t 0)) from z))) = 0 := by
        funext σ
        erw [chainPhi (t := t) (show ↥(∏ᶜ (YfN R t 0)) from z) σ]
        exact congrFun hz σ
      have h2 : ((chartCechK R t).d 0 (0+1)).hom
          (show ↥((chartCechK R t).X 0) from (show ↥(∏ᶜ (YfN R t 0)) from z)) = 0 := by
        apply (Phi R t (0+1)).injective
        show Phi R t (0+1) (show ↥(∏ᶜ (YfN R t (0+1))) from
            ((chartCechK R t).d 0 (0+1)).hom
              (show ↥((chartCechK R t).X 0) from (show ↥(∏ᶜ (YfN R t 0)) from z)))
          = Phi R t (0+1) 0
        rw [h1, map_zero]
      exact h2

end Work.DSM5b
