import Mathlib
import Submission.Work.ORReductions.SubgroupAlg

set_option autoImplicit false

namespace Work.ORReductions.Coherent

open MonoidAlgebra

/-- The linear combination map commutes with `Finsupp.mapRange` along a ring homomorphism:
applying `φ` to `∑ c i • y i` is the same as combining the image coefficients `φ ∘ c` with the
image of `y`. -/
lemma idealMap_linearCombination_mapRange {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B)
    {ι : Type*} (y : ι → A) (c : ι →₀ A) :
    Finsupp.linearCombination B (fun i => φ (y i))
        (Finsupp.mapRange (φ : A → B) (map_zero φ) c) =
      φ (Finsupp.linearCombination A y c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b c ha hb ih =>
    rw [Finsupp.mapRange_add (map_add φ), Finsupp.mapRange_single,
      map_add (Finsupp.linearCombination B (fun i => φ (y i))),
      map_add (Finsupp.linearCombination A y),
      Finsupp.linearCombination_single, Finsupp.linearCombination_single, ih,
      map_add φ, smul_eq_mul, smul_eq_mul, map_mul]

/-- A ring homomorphism maps the span of a family into the span of the images of that family. -/
lemma map_mem_span_of_mem_span {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B)
    {ι : Type*} (y : ι → A) {x : A}
    (hx : x ∈ Submodule.span A (Set.range y)) :
    φ x ∈ Submodule.span B (Set.range (fun i => φ (y i))) := by
  refine Submodule.span_induction
    (p := fun z _ => φ z ∈ Submodule.span B (Set.range fun i => φ (y i)))
    ?_ ?_ ?_ ?_ hx
  · rintro z ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro z w hz hw ihz ihw
    rw [map_add]; exact Submodule.add_mem _ ihz ihw
  · intro a z hz ih
    have : φ (a • z) = φ a • φ z := by simp only [smul_eq_mul, map_mul]
    rw [this]
    exact Submodule.smul_mem _ (φ a) ih

variable {G : Type*} [Group G] {K : Type*}

noncomputable def cosetCoord (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) : MonoidAlgebra K H :=
  MonoidAlgebra.ofCoeff (Finsupp.comapDomain (fun h : H => Quotient.out q * (h : G)) x.coeff
    (fun x _ y _ hab => Subtype.ext (mul_left_cancel hab)))

@[simp] lemma coeff_cosetCoord (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) (h : H) :
    (cosetCoord H K q x).coeff h = x.coeff (Quotient.out q * (h : G)) := rfl

@[simp] lemma cosetCoord_zero (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H) :
    cosetCoord H K q (0 : MonoidAlgebra K G) = 0 := by
  ext h; simp

lemma cosetCoord_add (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x y : MonoidAlgebra K G) :
    cosetCoord H K q (x + y) = cosetCoord H K q x + cosetCoord H K q y := by
  ext h; simp [MonoidAlgebra.coeff_add]

lemma mk_out_inv_mul_mem_iff (H : Subgroup G) (q : G ⧸ H) (g : G) :
    Quotient.mk (QuotientGroup.leftRel H) g = q ↔ (Quotient.out q)⁻¹ * g ∈ H := by
  have key : Quotient.mk (QuotientGroup.leftRel H) g
      = Quotient.mk (QuotientGroup.leftRel H) (Quotient.out q) ↔ g⁻¹ * Quotient.out q ∈ H :=
    QuotientGroup.eq
  rw [Quotient.out_eq q] at key
  rw [key, show g⁻¹ * Quotient.out q = ((Quotient.out q)⁻¹ * g)⁻¹ by group,
    Subgroup.inv_mem_iff]

lemma mk_out_mul_eq (H : Subgroup G) (q : G ⧸ H) (h : H) :
    Quotient.mk (QuotientGroup.leftRel H) (Quotient.out q * (h : G)) = q := by
  have key : Quotient.mk (QuotientGroup.leftRel H) (Quotient.out q * (h : G))
      = Quotient.mk (QuotientGroup.leftRel H) (Quotient.out q) := by
    rw [QuotientGroup.eq]
    have : ((Quotient.out q * (h : G)))⁻¹ * Quotient.out q = (h : G)⁻¹ := by group
    rw [this]
    exact H.inv_mem h.2
  rwa [Quotient.out_eq q] at key

/-- The `q`-coset component of `x` is `single (out q) 1` times the image of `cosetCoord q x`. -/
lemma cosetComponent_eq_single_mul_cosetCoord (H : Subgroup G) (K : Type*) [Semiring K]
    (q : G ⧸ H) (x : MonoidAlgebra K G) :
    Work.ORReductions.cosetComponent H K q x
      = MonoidAlgebra.single (Quotient.out q) 1 * subgroupAlgMap H K (cosetCoord H K q x) := by
  classical
  ext g
  rw [MonoidAlgebra.coeff_single_mul_apply, one_mul]
  rw [show subgroupAlgMap H K (cosetCoord H K q x)
      = MonoidAlgebra.mapDomain (⇑H.subtype) (cosetCoord H K q x) from rfl]
  rw [MonoidAlgebra.coeff_mapDomain]
  rw [Work.ORReductions.cosetComponent, MonoidAlgebra.coeff_ofCoeff, Finsupp.filter_apply]
  by_cases hg : (Quotient.out q)⁻¹ * g ∈ H
  · have hval : (Finsupp.mapDomain (⇑H.subtype) (cosetCoord H K q x).coeff)
        ((Quotient.out q)⁻¹ * g)
        = (cosetCoord H K q x).coeff ⟨(Quotient.out q)⁻¹ * g, hg⟩ :=
      Finsupp.mapDomain_apply_of_injective (f := ⇑H.subtype) H.subtype_injective (cosetCoord H K q x).coeff
        (⟨(Quotient.out q)⁻¹ * g, hg⟩ : H)
    rw [hval, coeff_cosetCoord, if_pos ((mk_out_inv_mul_mem_iff H q g).mpr hg)]
    congr 1
    change g = Quotient.out q * ((Quotient.out q)⁻¹ * g)
    group
  · have hval : (Finsupp.mapDomain (⇑H.subtype) (cosetCoord H K q x).coeff)
        ((Quotient.out q)⁻¹ * g) = 0 :=
      Finsupp.mapDomain_of_notMem_range (cosetCoord H K q x).coeff _
        (by
          rw [show Set.range (⇑H.subtype) = (H : Set G) from Subtype.range_coe]
          exact hg)
    rw [hval, if_neg (fun h => hg ((mk_out_inv_mul_mem_iff H q g).mp h))]

/-- `cosetCoord` is right `K[H]`-linear. -/
lemma cosetCoord_mul_subgroupAlgMap (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x : MonoidAlgebra K G) (a : MonoidAlgebra K H) :
    cosetCoord H K q (x * subgroupAlgMap H K a) = cosetCoord H K q x * a := by
  ext h
  rw [coeff_cosetCoord]
  rw [show subgroupAlgMap H K a = MonoidAlgebra.mapDomain (⇑H.subtype) a from rfl]
  rw [MonoidAlgebra.coeff_mul_apply_right]
  rw [MonoidAlgebra.coeff_mul_apply_right]
  rw [MonoidAlgebra.coeff_mapDomain]
  rw [Finsupp.sum_mapDomain_index (fun b => by simp) (fun b m₁ m₂ => by rw [mul_add])]
  apply Finsupp.sum_congr
  intro k hk
  rw [coeff_cosetCoord]
  congr 1
  congr 1
  show (Quotient.out q * (h : G)) * ((k : G))⁻¹ = Quotient.out q * ((h * k⁻¹ : H) : G)
  push_cast
  group


/-- The multiplication by `single (out q) 1` after applying `subgroupAlgMap`. -/
noncomputable def cosetShift (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (a : MonoidAlgebra K H) : MonoidAlgebra K G :=
  MonoidAlgebra.single (Quotient.out q) 1 * subgroupAlgMap H K a

@[simp] lemma cosetShift_zero (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H) :
    cosetShift H K q 0 = 0 := by
  simp [cosetShift]

lemma cosetShift_add (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    (x y : MonoidAlgebra K H) :
    cosetShift H K q (x + y) = cosetShift H K q x + cosetShift H K q y := by
  simp only [cosetShift, map_add, mul_add]

lemma sum_cosetComponent_eq_self_of_subset (H : Subgroup G) (K : Type*) [Semiring K]
    (x : MonoidAlgebra K G) (Q : Finset (G ⧸ H))
    (hQ : ∀ q, (∃ g ∈ x.coeff.support,
      Quotient.mk (QuotientGroup.leftRel H) g = q) → q ∈ Q) :
    ∑ q ∈ Q, Work.ORReductions.cosetComponent H K q x = x := by
  classical
  apply MonoidAlgebra.coeffAddEquiv.injective
  change (∑ q ∈ Q, Work.ORReductions.cosetComponent H K q x).coeff = x.coeff
  rw [MonoidAlgebra.coeff_sum]
  ext a
  rw [Finsupp.finsetSum_apply]
  simp only [Work.ORReductions.cosetComponent, MonoidAlgebra.coeff_ofCoeff,
    Finsupp.filter_apply]
  by_cases ha : a ∈ x.coeff.support
  · rw [@Finset.sum_ite_eq (G ⧸ H) K _ (Classical.decEq (G ⧸ H)) Q
        (Quotient.mk (QuotientGroup.leftRel H) a) (fun _ => x.coeff a),
      if_pos (hQ _ ⟨a, ha, rfl⟩)]
  · rw [Finsupp.notMem_support_iff.mp ha]; simp

/-- `cosetCoord q` commutes with linear combinations. -/
lemma cosetCoord_linearCombination (H : Subgroup G) (K : Type*) [Semiring K] (q : G ⧸ H)
    {ι : Type*} (y : ι → MonoidAlgebra K H) (c : ι →₀ MonoidAlgebra K G) :
    cosetCoord H K q (Finsupp.linearCombination (MonoidAlgebra K G)
        (fun j => subgroupAlgMap H K (y j)) c)
      = Finsupp.linearCombination (MonoidAlgebra K H) y
          (c.mapRange (cosetCoord H K q) (cosetCoord_zero H K q)) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add i v c' hv hc' ih =>
    rw [map_add, cosetCoord_add]
    rw [Finsupp.mapRange_add (fun x y => cosetCoord_add H K q x y), map_add]
    rw [Finsupp.linearCombination_single, Finsupp.mapRange_single,
      Finsupp.linearCombination_single]
    rw [smul_eq_mul, cosetCoord_mul_subgroupAlgMap, smul_eq_mul]
    rw [ih]

/-- The linear combination map is compatible with the `q`-th coset shift. -/
lemma linearCombination_mapRange_cosetShift (H : Subgroup G) (K : Type*) [Semiring K]
    (q : G ⧸ H) {ι κ : Type*} (k : κ → (ι →₀ MonoidAlgebra K H))
    (w : κ →₀ MonoidAlgebra K H) :
    Finsupp.linearCombination (MonoidAlgebra K G)
        (fun l => Finsupp.mapRange (subgroupAlgMap H K) (map_zero _) (k l))
        (w.mapRange (cosetShift H K q) (cosetShift_zero H K q))
      = (Finsupp.linearCombination (MonoidAlgebra K H) k w).mapRange
          (cosetShift H K q) (cosetShift_zero H K q) := by
  induction w using Finsupp.induction with
  | zero => simp
  | single_add l al w' hv hc' ih =>
    simp only [Finsupp.mapRange_add (cosetShift_add H K q), map_add,
      Finsupp.mapRange_single, Finsupp.linearCombination_single]
    rw [ih]
    congr 1
    ext i
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, cosetShift]
    rw [map_mul, mul_assoc]

theorem ker_le_span_of_subgroup_idealMap {G : Type*} [Group G] (H : Subgroup G) (K : Type*)
    [Semiring K] {ι κ : Type*} (y : ι → MonoidAlgebra K H)
    (k : κ → (ι →₀ MonoidAlgebra K H))
    (hk : Submodule.span (MonoidAlgebra K H) (Set.range k) =
      LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K H) y)) :
    LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K G)
        (fun j => subgroupAlgMap H K (y j))) ≤
      Submodule.span (MonoidAlgebra K G)
        (Set.range (fun l => Finsupp.mapRange (subgroupAlgMap H K) (map_zero _) (k l))) := by
  classical
  intro c hc
  rw [LinearMap.mem_ker] at hc
  set mkq : G → G ⧸ H := Quotient.mk (QuotientGroup.leftRel H) with hmkq
  set Q : Finset (G ⧸ H) := c.support.biUnion (fun i => (c i).coeff.support.image mkq) with hQdef
  have hcq : ∀ q : G ⧸ H, Finsupp.linearCombination (MonoidAlgebra K H) y
      (c.mapRange (cosetCoord H K q) (cosetCoord_zero H K q)) = 0 := by
    intro q
    rw [← cosetCoord_linearCombination H K q y c, hc]
    simp
  have hmem_ker : ∀ q : G ⧸ H, c.mapRange (cosetCoord H K q) (cosetCoord_zero H K q) ∈
      Submodule.span (MonoidAlgebra K H) (Set.range k) := by
    intro q
    rw [hk]
    exact LinearMap.mem_ker.mpr (hcq q)
  choose aq haq using fun q => Finsupp.mem_span_range_iff_exists_finsupp.mp (hmem_ker q)
  have haq' : ∀ q : G ⧸ H, Finsupp.linearCombination (MonoidAlgebra K H) k (aq q)
      = c.mapRange (cosetCoord H K q) (cosetCoord_zero H K q) := by
    intro q
    rw [Finsupp.linearCombination_apply]
    exact haq q
  have hQmem : ∀ i, ∀ q, (∃ g ∈ (c i).coeff.support, mkq g = q) → q ∈ Q := by
    intro i q hq
    by_cases hi : i ∈ c.support
    · rw [hQdef]
      obtain ⟨g, hg, hgq⟩ := hq
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨g, hg, hgq⟩⟩
    · rw [Finsupp.notMem_support_iff.mp hi] at hq
      obtain ⟨g, hg, -⟩ := hq
      simp at hg
  have hdecomp : ∑ q ∈ Q,
      (c.mapRange (cosetCoord H K q) (cosetCoord_zero H K q)).mapRange
        (cosetShift H K q) (cosetShift_zero H K q) = c := by
    apply Finsupp.ext
    intro i
    rw [Finsupp.finsetSum_apply]
    rw [← sum_cosetComponent_eq_self_of_subset H K (c i) Q (hQmem i)]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [Finsupp.mapRange_apply, cosetShift]
    exact (cosetComponent_eq_single_mul_cosetCoord H K q (c i)).symm
  set b : κ →₀ MonoidAlgebra K G :=
    ∑ q ∈ Q, (aq q).mapRange (cosetShift H K q) (cosetShift_zero H K q) with hbdef
  refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨b, ?_⟩
  have hb : Finsupp.linearCombination (MonoidAlgebra K G)
      (fun l => Finsupp.mapRange (subgroupAlgMap H K) (map_zero _) (k l)) b = c := by
    rw [hbdef, map_sum]
    trans ∑ q ∈ Q,
      (c.mapRange (cosetCoord H K q) (cosetCoord_zero H K q)).mapRange
        (cosetShift H K q) (cosetShift_zero H K q)
    · apply Finset.sum_congr rfl
      intro q hq
      rw [linearCombination_mapRange_cosetShift, haq']
    · exact hdecomp
  rw [Finsupp.linearCombination_apply] at hb
  exact hb

/-- **Extension of finitely presented ideals along a subgroup inclusion.** If `I` is a finitely
presented ideal of the group algebra `K[H]` of a subgroup `H ≤ G`, then the ideal of `K[G]` that
it generates is a finitely presented `K[G]`-module. -/
theorem ideal_map_finitePresentation_of_subgroup {G : Type*} [Group G] (H : Subgroup G)
    (K : Type*) [Field K] (I : Ideal (MonoidAlgebra K H))
    (hI : Module.FinitePresentation (MonoidAlgebra K H) I) :
    Module.FinitePresentation (MonoidAlgebra K G)
      (Ideal.map (Work.ORReductions.subgroupAlgMap H K) I) := by
  classical
  haveI : Module.FinitePresentation (MonoidAlgebra K H) I := hI
  -- Step 1: a finite family `y` generating `I` as a `K[H]`-submodule of `K[H]`.
  have hIFG : (I : Submodule (MonoidAlgebra K H) (MonoidAlgebra K H)).FG := by
    have htop : (⊤ : Submodule (MonoidAlgebra K H) I).FG := Module.Finite.fg_top
    have h := Submodule.FG.map (f := Submodule.subtype I) htop
    rwa [Submodule.map_top, Submodule.range_subtype] at h
  obtain ⟨n, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hIFG
  -- Step 2: the syzygy module of `y` is finitely generated.
  let fA : (Fin n →₀ MonoidAlgebra K H) →ₗ[MonoidAlgebra K H] MonoidAlgebra K H :=
    Finsupp.linearCombination (MonoidAlgebra K H) y
  have hrangeA : LinearMap.range fA =
      (I : Submodule (MonoidAlgebra K H) (MonoidAlgebra K H)) := by
    rw [Finsupp.range_linearCombination, hy]
  let lA : (Fin n →₀ MonoidAlgebra K H) →ₗ[MonoidAlgebra K H] I :=
    fA.codRestrict I fun c => by
      have h : fA c ∈ LinearMap.range fA := LinearMap.mem_range_self fA c
      rwa [hrangeA] at h
  have hlA : Function.Surjective lA := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict, hrangeA,
      Submodule.comap_subtype_self]
  have hkerAfg : (LinearMap.ker fA).FG := by
    have h : (LinearMap.ker lA).FG := Module.FinitePresentation.fg_ker lA hlA
    rwa [LinearMap.ker_codRestrict] at h
  obtain ⟨t, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hkerAfg
  have hk' : Submodule.span (MonoidAlgebra K H) (Set.range k) =
      LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K H) y) := hk
  -- Step 3: transport to `K[G]`.
  let y' : Fin n → MonoidAlgebra K G := fun j => Work.ORReductions.subgroupAlgMap H K (y j)
  let k' : Fin t → (Fin n →₀ MonoidAlgebra K G) := fun l =>
    Finsupp.mapRange (Work.ORReductions.subgroupAlgMap H K) (map_zero _) (k l)
  have hC2 : LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K G) y') ≤
      Submodule.span (MonoidAlgebra K G) (Set.range k') :=
    ker_le_span_of_subgroup_idealMap H K y k hk'
  have heasy : Submodule.span (MonoidAlgebra K G) (Set.range k') ≤
      LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K G) y') := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    show Finsupp.linearCombination (MonoidAlgebra K G) y'
      (Finsupp.mapRange (Work.ORReductions.subgroupAlgMap H K) (map_zero _) (k l)) = 0
    rw [idealMap_linearCombination_mapRange (Work.ORReductions.subgroupAlgMap H K) y (k l)]
    have h0 : Finsupp.linearCombination (MonoidAlgebra K H) y (k l) = 0 := by
      have hmem : k l ∈ Submodule.span (MonoidAlgebra K H) (Set.range k) :=
        Submodule.subset_span (Set.mem_range_self l)
      rw [hk'] at hmem
      exact LinearMap.mem_ker.mp hmem
    rw [h0, map_zero]
  have hkerBfg : (LinearMap.ker (Finsupp.linearCombination (MonoidAlgebra K G) y')).FG := by
    rw [le_antisymm hC2 heasy]
    exact Submodule.fg_span (Set.finite_range k')
  -- Step 4: `Ideal.map` is the span of the images of the generators.
  have hBmap : Ideal.map (Work.ORReductions.subgroupAlgMap H K) I =
      Submodule.span (MonoidAlgebra K G) (Set.range y') := by
    apply le_antisymm
    · rw [Ideal.map]
      apply Ideal.span_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      exact map_mem_span_of_mem_span (Work.ORReductions.subgroupAlgMap H K) y (hy.symm ▸ hi)
    · rw [Ideal.map]
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨y j, hy ▸ Submodule.subset_span (Set.mem_range_self j), rfl⟩
  -- Step 5: conclude finite presentation.
  let lB : (Fin n →₀ MonoidAlgebra K G) →ₗ[MonoidAlgebra K G]
      Ideal.map (Work.ORReductions.subgroupAlgMap H K) I :=
    (Finsupp.linearCombination (MonoidAlgebra K G) y').codRestrict
      (Ideal.map (Work.ORReductions.subgroupAlgMap H K) I) fun c => by
        have h : Finsupp.linearCombination (MonoidAlgebra K G) y' c ∈
            Submodule.span (MonoidAlgebra K G) (Set.range y') := by
          rw [← Finsupp.range_linearCombination]
          exact LinearMap.mem_range_self _ c
        rwa [← hBmap] at h
  have hlB : Function.Surjective lB := by
    rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
      Finsupp.range_linearCombination, ← hBmap, Submodule.comap_subtype_self]
  have hkerB : (LinearMap.ker lB).FG := by
    rw [LinearMap.ker_codRestrict]
    exact hkerBfg
  exact Module.finitePresentation_of_surjective lB hlB hkerB

end Work.ORReductions.Coherent
