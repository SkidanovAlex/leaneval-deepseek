import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.glue_sections
import Submission.Work.DSEQP.sections_eq_zero_of_restrict_eq_zero

/-!
# `Work.DSEQP.Geom.geomD0_ker_iso_gamma` — the `0`-cocycles of the geometric chart complex

This file proves that the kernel of the degree-`0` differential `Work.DSEQP.geomD0 i f` of the
*geometric* chart Čech complex of `X ⊆ ℙᴺ_A` — the alternating complex of the chart cover
`j ↦ U_j = i⁻¹D₊(x_j)` of `X`, with the sign convention of `Work.DSCOH.cechDiffComp` — is the
`A`-module `Γ(X, 𝒪_X)` of global sections, for the `A`-structure induced by `f`.

The proof is the standard sheaf-theoretic one:

* the restriction-to-charts map `Work.DSEQP.Geom.restrictToCharts i f : Γ(X, ⊤) → GC0` is a
  linear map whose image consists of `0`-cocycles (`geomD0_restrictToCharts`);
* it is injective (`restrictToCharts_injective`), because a section of a sheaf which restricts to
  `0` on a cover is `0` (`Work.DSEQP.sections_eq_zero_of_restrict_eq_zero`);
* it is surjective (`exists_glue`): a `0`-cocycle is compatible on pairwise intersections
  (`ker_compat`, extracted from the vanishing of the degree-`1` component via the alternating sum
  computation) and hence glues (`Work.DSEQP.glue_sections`), the charts covering `X`
  (`Work.DSEQP.chartCover_iSup_eq_top`).

-/

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Work.DSEQP.Geom

universe a

variable {A : Type a} [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}

/-! ## 1. The restriction map and its functoriality -/

/-- Restriction of sections of `𝒪_X` (with its `A`-module structure induced by `f`) from the open
`U` to the open `V ≤ U`. -/
noncomputable abbrev rho (f : X ⟶ Spec (CommRingCat.of A)) {U V : X.Opens} (h : V ≤ U) :
    ↥((DSMap.cechPresheaf A X f).obj (Opposite.op U)) →ₗ[A]
      ↥((DSMap.cechPresheaf A X f).obj (Opposite.op V)) :=
  ((DSMap.cechPresheaf A X f).map (homOfLE h).op).hom

/-- The underlying map of `cechPresheaf` is the restriction of sections of the structure sheaf. -/
lemma cechPresheaf_map_hom (f : X ⟶ Spec (CommRingCat.of A)) {U V : X.Opens} (h : V ≤ U)
    (x : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op U))) :
    ((DSMap.cechPresheaf A X f).map (homOfLE h).op).hom x
      = (X.presheaf.map (homOfLE h).op).hom x := rfl

/-- Restrictions of sections compose. -/
theorem res_res (f : X ⟶ Spec (CommRingCat.of A)) {U V W : X.Opens}
    (h1 : W ≤ V) (h2 : V ≤ U) (h3 : W ≤ U)
    (s : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op U))) :
    rho f h1 (rho f h2 s) = rho f h3 s := by
  rw [rho, rho, rho, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp]
  congr 1

/-! ## 2. The restriction-to-charts map `Γ(X, ⊤) → GC0` -/

/-- Restriction of the global sections of `𝒪_X` to the charts `Ucmp i S` (`S` a singleton),
i.e. the map `Γ(X, ⊤) → ∏_S Γ(U_S, 𝒪_X)`; its `A`-linear structure is the one induced by `f`. -/
noncomputable def restrictToCharts (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ Spec (CommRingCat.of A)) :
    ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens))) →ₗ[A] Work.DSEQP.GC0 i f :=
  LinearMap.pi fun S => ((DSMap.cechPresheaf A X f).map
    (homOfLE (le_top : Work.DSEQP.Ucmp i S.1 ≤ ⊤)).op).hom

@[simp] lemma restrictToCharts_apply (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ Spec (CommRingCat.of A))
    (s : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens))))
    (S : {S : Finset (Fin (N + 1)) // S.card = 1}) :
    restrictToCharts i f s S =
      ((DSMap.cechPresheaf A X f).map
        (homOfLE (le_top : Work.DSEQP.Ucmp i S.1 ≤ ⊤)).op).hom s :=
  LinearMap.pi_apply _ _ _

/-! ## 3. Combinatorial preliminaries for the alternating sum -/

section Filters

variable {ι : Type*} [LinearOrder ι] [DecidableEq ι]

lemma filter_pair_lt_self_of_lt {a b : ι} (h : a < b) :
    ({a, b} : Finset ι).filter (fun j => j < a) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x hx hlt
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hxa | hxb
  · rw [hxa] at hlt; exact absurd hlt (lt_irrefl a)
  · rw [hxb] at hlt; exact absurd hlt (not_lt.mpr (le_of_lt h))

lemma filter_pair_lt_other_of_lt {a b : ι} (h : a < b) :
    ({a, b} : Finset ι).filter (fun j => j < b) = {a} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hlt⟩
    rcases hx with hxa | hxb
    · exact hxa
    · rw [hxb] at hlt; exact absurd hlt (lt_irrefl b)
  · rintro rfl
    exact ⟨Or.inl rfl, h⟩

lemma filter_pair_lt_self_of_gt {a b : ι} (h : b < a) :
    ({a, b} : Finset ι).filter (fun j => j < a) = {b} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hlt⟩
    rcases hx with hxa | hxb
    · rw [hxa] at hlt; exact absurd hlt (lt_irrefl a)
    · exact hxb
  · rintro rfl
    exact ⟨Or.inr rfl, h⟩

lemma filter_pair_lt_other_of_gt {a b : ι} (h : b < a) :
    ({a, b} : Finset ι).filter (fun j => j < b) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro x hx hlt
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hxa | hxb
  · rw [hxa] at hlt; exact absurd hlt (not_lt.mpr (le_of_lt h))
  · rw [hxb] at hlt; exact absurd hlt (lt_irrefl b)

end Filters

/-- The alternating sum `∑_{i ∈ T} (-1)^{#{j ∈ T : j < i}}` over a two-element finset vanishes. -/
theorem altSum_card_two {ι : Type*} [LinearOrder ι] [DecidableEq ι] (T : Finset ι)
    (hT : T.card = 2) :
    (∑ i ∈ T, ((-1 : ℤ) ^ ((T.filter (fun j => j < i)).card))) = 0 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT
  rw [Finset.sum_pair hab]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [filter_pair_lt_self_of_lt h, filter_pair_lt_other_of_lt h,
      Finset.card_empty, Finset.card_singleton]
    norm_num
  · rw [filter_pair_lt_self_of_gt h, filter_pair_lt_other_of_gt h,
      Finset.card_singleton, Finset.card_empty]
    norm_num

/-- The chart `Ucmp i {a, b}` is the intersection of the coordinate charts `Ucmp i {a}` and
`Ucmp i {b}`. -/
lemma Ucmp_pair (i : X ⟶ DSMap.PSpace A N) (a b : Fin (N + 1)) :
    Work.DSEQP.Ucmp i ({a, b} : Finset (Fin (N + 1))) =
      Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} := by
  simp only [Work.DSEQP.Ucmp_eq_iInf, Finset.iInf_insert, Finset.iInf_singleton]

/-- The component of `y` over the erased chart, phrased with a variable `S` so that the transport
along an equality `S = {j}` is definitional. -/
theorem restrict_congr_finset (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ Spec (CommRingCat.of A))
    {S T : Finset (Fin (N + 1))} (hS : S.card = 1) {j : Fin (N + 1)}
    (hj : S = {j}) (hφ : Work.DSEQP.Ucmp i T ≤ Work.DSEQP.Ucmp i S)
    (hφ' : Work.DSEQP.Ucmp i T ≤ Work.DSEQP.Ucmp i {j}) (y : Work.DSEQP.GC0 i f) :
    rho f hφ (y ⟨S, hS⟩) = rho f hφ' (y ⟨{j}, by simp⟩) := by
  subst S
  rfl

/-- A sum over the `attach` of a two-element finset is the plain sum of the two values. -/
theorem sum_attach_pair {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    {a b : ι} (hab : a ≠ b) (g : ↥({a, b} : Finset ι) → M) :
    (∑ x ∈ ({a, b} : Finset ι).attach, g x) = g ⟨a, by simp⟩ + g ⟨b, by simp⟩ := by
  have hset : ({a, b} : Finset ι).attach = {⟨a, by simp⟩, ⟨b, by simp⟩} := by
    ext x
    simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases Finset.mem_insert.mp x.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp h))
  rw [hset]
  rw [Finset.sum_pair (show (⟨a, by simp⟩ : ↥({a, b} : Finset ι)) ≠ ⟨b, by simp⟩ from
    fun hh => hab (Subtype.ext_iff.mp hh))]

/-- Two-component Čech relation: from `(-1)^{e} • X + (-1)^{f} • Y = 0` with `e + f = 1` conclude
`X = Y`. -/
theorem neg_one_pow_smul_add_eq_zero {M : Type*} [AddCommGroup M] {e f : ℕ} (h : e + f = 1)
    {X Y : M} (hxy : ((-1 : ℤ) ^ e) • X + ((-1 : ℤ) ^ f) • Y = 0) : X = Y := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · have hf : f = 1 := by omega
    subst hf
    simp only [pow_zero, pow_one, one_smul] at hxy
    rw [neg_one_smul] at hxy
    simpa using add_eq_zero_iff_eq_neg.mp hxy
  · have hf : f = 0 := by omega
    subst hf
    simp only [pow_zero, pow_one, one_smul] at hxy
    rw [neg_one_smul] at hxy
    exact neg_inj.mp (add_eq_zero_iff_eq_neg.mp hxy)

/-! ## 4. The image of `restrictToCharts` consists of `0`-cocycles -/

/-- The restriction of a global section to the charts is a `0`-cocycle of the geometric chart
Čech complex. -/
theorem geomD0_restrictToCharts (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ Spec (CommRingCat.of A))
    (s : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens)))) :
    Work.DSEQP.geomD0 i f (restrictToCharts i f s) = 0 := by
  funext T
  rw [Work.DSEQP.geomD0_apply]
  have hres : ∀ i' : ↥T.1,
      ((DSMap.cechPresheaf A X f).map
          (homOfLE (Work.DSEQP.Ucmp_anti i (Finset.erase_subset i'.1 T.1))).op).hom
        (((DSMap.cechPresheaf A X f).map
          (homOfLE (le_top : Work.DSEQP.Ucmp i (T.1.erase i'.1) ≤ ⊤)).op).hom s)
      = ((DSMap.cechPresheaf A X f).map
          (homOfLE (le_top : Work.DSEQP.Ucmp i T.1 ≤ ⊤)).op).hom s :=
    fun i' => res_res f (Work.DSEQP.Ucmp_anti i (Finset.erase_subset i'.1 T.1)) le_top le_top s
  have hsum : (∑ i' ∈ T.1.attach,
        ((-1 : ℤ) ^ ((T.1.filter fun j => j < (i' : Fin (N + 1))).card)))
      = ∑ i ∈ T.1, ((-1 : ℤ) ^ ((T.1.filter fun j => j < i).card)) :=
    Finset.sum_attach T.1 (fun j => ((-1 : ℤ) ^ ((T.1.filter fun j' => j' < j).card)))
  rw [Work.DSEQP.geomD0Comp, LinearMap.sum_apply]
  trans ∑ i' ∈ T.1.attach,
      ((-1 : ℤ) ^ ((T.1.filter fun j => j < (i' : Fin (N + 1))).card)) •
      (((DSMap.cechPresheaf A X f).map
        (homOfLE (le_top : Work.DSEQP.Ucmp i T.1 ≤ ⊤)).op).hom s)
  · apply Finset.sum_congr rfl
    intro i' _
    rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      restrictToCharts_apply, hres i']
  · rw [← Finset.sum_smul, hsum, altSum_card_two T.1 T.2, zero_smul]
    rfl

/-! ## 5. `restrictToCharts` is injective -/

/-- The restriction-to-charts map is injective: a global section of a sheaf is determined by its
restrictions to a cover. -/
theorem restrictToCharts_injective (i : X ⟶ DSMap.PSpace A N)
    (f : X ⟶ Spec (CommRingCat.of A)) : Function.Injective (restrictToCharts i f) := by
  intro s t h
  have hst : (s - t : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens)))) = 0 := by
    apply Work.DSEQP.sections_eq_zero_of_restrict_eq_zero (fun j => Work.DSEQP.Ucmp i {j})
      (Work.DSEQP.chartCover_iSup_eq_top i)
    intro j
    have hc := congrFun h ⟨{j}, by simp⟩
    simp only [restrictToCharts_apply] at hc
    rw [← cechPresheaf_map_hom f (le_top : Work.DSEQP.Ucmp i {j} ≤ ⊤)]
    rw [map_sub]
    exact sub_eq_zero.mpr hc
  exact sub_eq_zero.mp hst

/-! ## 6. The pairwise compatibility of a `0`-cocycle -/

/-- The components of a `0`-cocycle agree on pairwise intersections of the coordinate charts. -/
theorem ker_compat (i : X ⟶ DSMap.PSpace A N) (f : X ⟶ Spec (CommRingCat.of A))
    (y : Work.DSEQP.GC0 i f) (hy : Work.DSEQP.geomD0 i f y = 0) (a b : Fin (N + 1)) :
    rho f (inf_le_left : Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} ≤ Work.DSEQP.Ucmp i {a})
        (y ⟨{a}, by simp⟩)
      = rho f (inf_le_right : Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} ≤ Work.DSEQP.Ucmp i {b})
        (y ⟨{b}, by simp⟩) := by
  by_cases hab : a = b
  · subst hab
    simp only [rho]
  · have hcard : ({a, b} : Finset (Fin (N + 1))).card = 2 := Finset.card_pair hab
    have h0 : Work.DSEQP.geomD0Comp i f ⟨{a, b}, hcard⟩ y = 0 := by
      have h1 := congrFun hy ⟨{a, b}, hcard⟩
      simpa [Work.DSEQP.geomD0_apply] using h1
    have hea : ({a, b} : Finset (Fin (N + 1))).erase a = {b} := by
      rw [Finset.erase_insert (by simp [hab])]
    have heb : ({a, b} : Finset (Fin (N + 1))).erase b = {a} := by
      rw [Finset.erase_insert_of_ne hab, Finset.erase_singleton, Finset.insert_empty]
    have ha' : ({a} : Finset (Fin (N + 1))) ⊆ ({a, b} : Finset (Fin (N + 1))) := by
      intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; simp
    have hb' : ({b} : Finset (Fin (N + 1))) ⊆ ({a, b} : Finset (Fin (N + 1))) := by
      intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; simp
    let BODY : ↥({a, b} : Finset (Fin (N + 1))) →
        ↥((DSMap.cechPresheaf A X f).obj
          (Opposite.op (Work.DSEQP.Ucmp i ({a, b} : Finset (Fin (N + 1)))))) :=
      fun x => ((-1 : ℤ) ^
          ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < (x : Fin (N + 1)))).card)) •
        (rho f (Work.DSEQP.Ucmp_anti i
            (Finset.erase_subset (x : Fin (N + 1)) ({a, b} : Finset (Fin (N + 1)))))
          (y ⟨({a, b} : Finset (Fin (N + 1))).erase (x : Fin (N + 1)),
            by rw [Finset.card_erase_of_mem x.2, Finset.card_pair hab]⟩))
    set Xa := rho f (Work.DSEQP.Ucmp_anti i hb') (y ⟨{b}, by simp⟩) with hXa
    set Xb := rho f (Work.DSEQP.Ucmp_anti i ha') (y ⟨{a}, by simp⟩) with hXb
    have hsplit : Work.DSEQP.geomD0Comp i f ⟨{a, b}, hcard⟩ y
        = BODY ⟨a, by simp⟩ + BODY ⟨b, by simp⟩ := by
      have e1 : Work.DSEQP.geomD0Comp i f ⟨{a, b}, hcard⟩ y
          = ∑ x ∈ ({a, b} : Finset (Fin (N + 1))).attach, BODY x := by
        rw [Work.DSEQP.geomD0Comp, LinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro x _
        simp only [BODY, rho, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      rw [e1, sum_attach_pair hab BODY]
    have h0' : BODY ⟨a, by simp⟩ + BODY ⟨b, by simp⟩ = 0 := by rw [← hsplit]; exact h0
    have hga : BODY ⟨a, by simp⟩ =
        ((-1 : ℤ) ^ ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < a)).card)) • Xa := by
      simp only [BODY, rho]
      exact congrArg (fun t => ((-1 : ℤ) ^
          ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < a)).card)) • t)
        (restrict_congr_finset i f
          (S := ({a, b} : Finset (Fin (N + 1))).erase a)
          (by rw [Finset.card_erase_of_mem (Finset.mem_insert_self a {b}), Finset.card_pair hab])
          hea (Work.DSEQP.Ucmp_anti i (Finset.erase_subset a ({a, b} : Finset (Fin (N + 1)))))
          (Work.DSEQP.Ucmp_anti i hb') y)
    have hgb : BODY ⟨b, by simp⟩ =
        ((-1 : ℤ) ^ ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < b)).card)) • Xb := by
      simp only [BODY, rho]
      exact congrArg (fun t => ((-1 : ℤ) ^
          ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < b)).card)) • t)
        (restrict_congr_finset i f
          (S := ({a, b} : Finset (Fin (N + 1))).erase b)
          (by rw [Finset.card_erase_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)),
            Finset.card_pair hab])
          heb (Work.DSEQP.Ucmp_anti i (Finset.erase_subset b ({a, b} : Finset (Fin (N + 1)))))
          (Work.DSEQP.Ucmp_anti i ha') y)
    have hsum : ((-1 : ℤ) ^ ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < a)).card)) • Xa
        + ((-1 : ℤ) ^ ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < b)).card)) • Xb
        = 0 := by
      rw [← hga, ← hgb]; exact h0'
    have hef : ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < a)).card)
        + ((({a, b} : Finset (Fin (N + 1))).filter (fun j => j < b)).card) = 1 := by
      rcases lt_or_gt_of_ne hab with h | h
      · rw [filter_pair_lt_self_of_lt h, filter_pair_lt_other_of_lt h,
          Finset.card_empty, Finset.card_singleton]
      · rw [filter_pair_lt_self_of_gt h, filter_pair_lt_other_of_gt h,
          Finset.card_singleton, Finset.card_empty]
    have hX : Xa = Xb := neg_one_pow_smul_add_eq_zero hef hsum
    have step1 : ((DSMap.cechPresheaf A X f).map (homOfLE (inf_le_left :
          Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} ≤ Work.DSEQP.Ucmp i {a})).op).hom
          (y ⟨{a}, by simp⟩)
        = rho f (le_of_eq (Ucmp_pair i a b).symm) Xb := by
      rw [hXb]
      exact (res_res f (le_of_eq (Ucmp_pair i a b).symm) (Work.DSEQP.Ucmp_anti i ha') inf_le_left
        (y ⟨{a}, by simp⟩)).symm
    have step2 : ((DSMap.cechPresheaf A X f).map (homOfLE (inf_le_right :
          Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} ≤ Work.DSEQP.Ucmp i {b})).op).hom
          (y ⟨{b}, by simp⟩)
        = rho f (le_of_eq (Ucmp_pair i a b).symm) Xa := by
      rw [hXa]
      exact (res_res f (le_of_eq (Ucmp_pair i a b).symm) (Work.DSEQP.Ucmp_anti i hb') inf_le_right
        (y ⟨{b}, by simp⟩)).symm
    rw [step1, step2, hX]

/-! ## 7. A `0`-cocycle glues to a global section -/

/-- Every `0`-cocycle is the restriction of a global section. -/
theorem exists_glue (i : X ⟶ DSMap.PSpace A N) (f : X ⟶ Spec (CommRingCat.of A))
    (y : ↥(LinearMap.ker (Work.DSEQP.geomD0 i f))) :
    ∃ t : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens))),
      restrictToCharts i f t = y.1 := by
  have hcompat : ∀ a b : Fin (N + 1),
      (X.presheaf.map (homOfLE (inf_le_left :
          Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} ≤ Work.DSEQP.Ucmp i {a})).op).hom
        (y.1 ⟨{a}, by simp⟩)
      = (X.presheaf.map (homOfLE (inf_le_right :
          Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} ≤ Work.DSEQP.Ucmp i {b})).op).hom
        (y.1 ⟨{b}, by simp⟩) := by
    intro a b
    rw [← cechPresheaf_map_hom f (inf_le_left :
          Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} ≤ Work.DSEQP.Ucmp i {a}),
      ← cechPresheaf_map_hom f (inf_le_right :
          Work.DSEQP.Ucmp i {a} ⊓ Work.DSEQP.Ucmp i {b} ≤ Work.DSEQP.Ucmp i {b})]
    exact ker_compat i f y.1 y.2 a b
  obtain ⟨t₀, ht₀⟩ := Work.DSEQP.glue_sections (fun j => Work.DSEQP.Ucmp i {j})
    (Work.DSEQP.chartCover_iSup_eq_top i) (fun j => y.1 ⟨{j}, by simp⟩) hcompat
  let t : ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens))) := t₀
  have ht : ∀ j : Fin (N + 1),
      ((DSMap.cechPresheaf A X f).map
        (homOfLE (le_top : Work.DSEQP.Ucmp i {j} ≤ ⊤)).op).hom t = y.1 ⟨{j}, by simp⟩ := by
    intro j
    rw [cechPresheaf_map_hom f (le_top : Work.DSEQP.Ucmp i {j} ≤ ⊤)]
    exact ht₀ j
  refine ⟨t, ?_⟩
  funext S
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp S.2
  have hS : S = ⟨{j}, by simp⟩ := Subtype.ext hj
  subst hS
  rw [restrictToCharts_apply]
  exact ht j

/-! ## 8. The main theorem -/

/-- The linear map `Γ(X, ⊤) → ker (geomD0 i f)` given by restricting to the charts. -/
noncomputable def toKer (i : X ⟶ DSMap.PSpace A N) (f : X ⟶ Spec (CommRingCat.of A)) :
    ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens))) →ₗ[A]
      ↥(LinearMap.ker (Work.DSEQP.geomD0 i f)) :=
  LinearMap.codRestrict (LinearMap.ker (Work.DSEQP.geomD0 i f)) (restrictToCharts i f)
    (fun s => by rw [LinearMap.mem_ker]; exact geomD0_restrictToCharts i f s)

theorem toKer_bijective (i : X ⟶ DSMap.PSpace A N) (f : X ⟶ Spec (CommRingCat.of A)) :
    Function.Bijective (toKer i f) := by
  constructor
  · intro s t h
    exact restrictToCharts_injective i f (congrArg Subtype.val h)
  · intro y
    obtain ⟨t, ht⟩ := exists_glue i f y
    exact ⟨t, Subtype.ext ht⟩

/-- The kernel of the degree-`0` differential of the *geometric* chart Čech complex of `X` (the
alternating complex of the chart cover `j ↦ U_j = i⁻¹D₊(x_j)`, with the same sign convention as
`Work.DSCOH.cechDiffComp`) is the ring of global sections `Γ(X, 𝒪_X)`, as an `A`-module for the
structure induced by `f`.  (A `0`-cocycle is a family `y_S ∈ Γ(X, U_S)` over the singleton charts
with `y_a|_{U_a ⊓ U_b} = y_b|_{U_a ⊓ U_b}` for every pair; the charts cover `X`
(`Work.DSEQP.chartCover_iSup_eq_top`) and `𝒪_X` is a sheaf, so such families glue uniquely.) -/
theorem geomD0_ker_iso_gamma (A : Type a) [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) :
    Nonempty (↥(LinearMap.ker (Work.DSEQP.geomD0 i f)) ≃ₗ[A]
      ↥((DSMap.cechPresheaf A X f).obj (Opposite.op (⊤ : X.Opens)))) :=
  ⟨(LinearEquiv.ofBijective (toKer i f) (toKer_bijective i f)).symm⟩

end Work.DSEQP.Geom
