import Mathlib
import Submission.Work.Drive.qwCollRow
import Submission.Work.Drive.collRowSlotBreak

/-!
# The slot that breaks the rank drop, restricted to the normal plane of `U`

This module proves `Work.Drive.collRowSlotBreakNormal`, the variant of
`Work.Drive.collRowSlotBreak` in which the change direction `p` is required to be
*perpendicular to a prescribed vector `U`* (the chord direction of the quadrisecant window).

Writing `R i = collRow β γ A i = rowL β γ i (A i)` with `rowL β γ i a = (c i • a, d i • a)`, the
four scalar pairs `(c i, d i)` are pairwise non-proportional and each row map is injective.  The
normal plane `P = U^⊥` is two-dimensional and the images `rowL i '' P`, `rowL j '' P` for `i ≠ j`
intersect trivially; hence at most one of them fits into a subspace of dimension at most `3`, so at
least three of the four slots are *good*, i.e. `rowL i` maps `P` outside the row span `W`.

A slot `k` is *removable* when the other three rows already span `W`.  The main work of the module
is that **a bad slot is never removable when `dim W = 3`**: if `rowL k '' P ≤ W`, pick
`v ∈ W \ rowL k '' P`; then `W = rowL k '' P ⊕ ℝ v`, and the linear map `χ(x, y) = d k • x - c k • y`
kills `rowL k '' P` and sends all of `W` into `ℝ • χ v`; hence
`χ (R j) = (d k * c j - c k * d j) • A j ∈ ℝ • χ v`, and the scalar is non-zero, so every `R j`
(`j ≠ k`) lies in the two-dimensional space spanned by `(χ v, 0)` and `(0, χ v)`.

Consequently the basis of `W` of size `m - 1` extracted from the four rows leaves `5 - m` slots
over; for `m ≤ 3` two are left, so one is good, and for `m = 4` the single left-over slot is
removable, hence good by the previous paragraph.
-/

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The normal plane of `U` -/

/-- The linear functional `p ↦ ⟪p, U⟫` on space. -/
def innerULin (U : Space) : Space →ₗ[ℝ] ℝ where
  toFun p := inner ℝ p U
  map_add' a b := inner_add_left a b U
  map_smul' c a := by
    rw [inner_smul_left]
    simp

@[simp] lemma innerULin_apply (U p : Space) : innerULin U p = inner ℝ p U := rfl

/-- The normal plane of `U`, i.e. the kernel of `p ↦ ⟪p, U⟫`. -/
def Plin (U : Space) : Submodule ℝ Space := LinearMap.ker (innerULin U)

lemma mem_Plin {U p : Space} : p ∈ Plin U ↔ inner ℝ p U = 0 := by
  rw [Plin, LinearMap.mem_ker, innerULin_apply]

/-- The span of the four rows `collRow β γ A i`. -/
def collSpan (β γ : ℝ) (A : Fin 4 → Space) : Submodule ℝ (Space × Space) :=
  Submodule.span ℝ (Set.range (collRow β γ A))

/-- The image of the normal plane of `U` under the `k`-th row map of `collRow`. -/
def LkImg (β γ : ℝ) (k : Fin 4) (U : Space) : Submodule ℝ (Space × Space) :=
  LinearMap.range ((rowL β γ k).comp (Plin U).subtype)

lemma mem_LkImg {β γ : ℝ} {k : Fin 4} {U : Space} {x : Space × Space} :
    x ∈ LkImg β γ k U ↔ ∃ p : Space, inner ℝ p U = 0 ∧ rowL β γ k p = x := by
  rw [LkImg, LinearMap.mem_range]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨(s : Space), mem_Plin.mp s.2, hs⟩
  · rintro ⟨p, hp, hpx⟩
    exact ⟨⟨p, mem_Plin.mpr hp⟩, hpx⟩

lemma finrank_Plin {U : Space} (hU : U ≠ 0) : Module.finrank ℝ (Plin U) = 2 := by
  have hU' : innerULin U U ≠ 0 := by
    rw [innerULin_apply, real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hU)
  have hsurj : Function.Surjective (innerULin U) := by
    intro r
    refine ⟨(r / innerULin U U) • U, ?_⟩
    rw [map_smul, smul_eq_mul]
    field_simp
  have hrange : Module.finrank ℝ (LinearMap.range (innerULin U)) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have h := LinearMap.finrank_range_add_finrank_ker (innerULin U)
  rw [hrange, finrank_euclideanSpace_fin] at h
  rw [Plin]
  omega

lemma finrank_LkImg {U : Space} (hU : U ≠ 0) {β γ : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1)
    (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1) (k : Fin 4) :
    Module.finrank ℝ (LkImg β γ k U) = 2 := by
  have hinj : Function.Injective ((rowL β γ k).comp (Plin U).subtype) := by
    intro a b hab
    have hab' : rowL β γ k (a : Space) = rowL β γ k (b : Space) := hab
    exact Subtype.ext (rowL_injective β γ hβ0 hβ1 hγ0 hγ1 k hab')
  rw [LkImg, LinearMap.finrank_range_of_inj hinj, finrank_Plin hU]

lemma LkImg_inf_eq_bot {U : Space} {β γ : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (hγ0 : γ ≠ 0)
    (hγ1 : γ ≠ 1) (hβγ : β ≠ γ) {i j : Fin 4} (hij : i ≠ j) :
    LkImg β γ i U ⊓ LkImg β γ j U = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro z ⟨hz1, hz2⟩
  obtain ⟨p, hp, hpz⟩ := mem_LkImg.mp hz1
  obtain ⟨q, hq, hqz⟩ := mem_LkImg.mp hz2
  have hpq : p = 0 :=
    rowL_eq_zero_of_eq β γ hβ0 hβ1 hγ0 hγ1 hβγ hij (by rw [hpz, hqz])
  rw [← hpz, hpq, map_zero]

/-- **Two slots cannot both be bad.**  If the images of the normal plane under two distinct row
maps both lie in a subspace `W` of dimension at most `3`, we get a contradiction: the two images
are disjoint two-dimensional subspaces of `W`. -/
lemma not_bad_pair {U : Space} (hU : U ≠ 0) {β γ : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1)
    (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1) (hβγ : β ≠ γ) {W : Submodule ℝ (Space × Space)}
    (hWle : Module.finrank ℝ W ≤ 3) {i j : Fin 4} (hij : i ≠ j) (hi : LkImg β γ i U ≤ W)
    (hj : LkImg β γ j U ≤ W) : False := by
  have hsup : LkImg β γ i U ⊔ LkImg β γ j U ≤ W := sup_le hi hj
  have hfin_bot : Module.finrank ℝ ↥(LkImg β γ i U ⊓ LkImg β γ j U) = 0 := by
    rw [LkImg_inf_eq_bot hβ0 hβ1 hγ0 hγ1 hβγ hij, finrank_bot]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LkImg β γ i U) (LkImg β γ j U)
  rw [hfin_bot, finrank_LkImg hU hβ0 hβ1 hγ0 hγ1 i,
    finrank_LkImg hU hβ0 hβ1 hγ0 hγ1 j, add_zero] at hsum
  have h4 : Module.finrank ℝ ↥(LkImg β γ i U ⊔ LkImg β γ j U) = 4 := by omega
  have hmono := Submodule.finrank_mono hsup
  omega

/-- **A bad slot is not removable when `dim W = 3`.**  If the image of the normal plane under
`rowL k` lies in the row span of dimension `3`, then the other three rows span at most two
dimensions, so they cannot span the row span. -/
lemma bad_le_two {U : Space} (hU : U ≠ 0) {β γ : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (hγ0 : γ ≠ 0)
    (hγ1 : γ ≠ 1) (hβγ : β ≠ γ) (A : Fin 4 → Space) {k : Fin 4}
    (h3 : Module.finrank ℝ (collSpan β γ A) = 3) (hbad : LkImg β γ k U ≤ collSpan β γ A) :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun j : {j : Fin 4 // j ≠ k} => collRow β γ A j.1))) ≤ 2 := by
  classical
  have hfin2 : Module.finrank ℝ (LkImg β γ k U) = 2 := finrank_LkImg hU hβ0 hβ1 hγ0 hγ1 k
  obtain ⟨v, hvW, hvL⟩ : ∃ v ∈ collSpan β γ A, v ∉ LkImg β γ k U := by
    by_contra h
    push Not at h
    have hle : collSpan β γ A ≤ LkImg β γ k U := fun x hx => h x hx
    have hmono := Submodule.finrank_mono hle
    omega
  have hv0 : v ≠ 0 := fun h => hvL (h ▸ Submodule.zero_mem _)
  have hsup_le : LkImg β γ k U ⊔ Submodule.span ℝ {v} ≤ collSpan β γ A := by
    refine sup_le hbad ?_
    rw [Submodule.span_le]
    rintro x rfl
    exact hvW
  have hdisj : LkImg β γ k U ⊓ Submodule.span ℝ {v} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hz2
    rw [← ht]
    by_cases ht0 : t = 0
    · rw [ht0, zero_smul]
    · exfalso
      have hz1' : t • v ∈ LkImg β γ k U := ht ▸ hz1
      have hvmem : v ∈ LkImg β γ k U := by
        have h := Submodule.smul_mem (LkImg β γ k U) t⁻¹ hz1'
        rwa [smul_smul, inv_mul_cancel₀ ht0, one_smul] at h
      exact hvL hvmem
  have hfin_sup : Module.finrank ℝ ↥(LkImg β γ k U ⊔ Submodule.span ℝ {v}) = 3 := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LkImg β γ k U) (Submodule.span ℝ {v})
    rw [hdisj, finrank_bot, hfin2, finrank_span_singleton hv0, add_zero] at hsum
    omega
  have hWeq : LkImg β γ k U ⊔ Submodule.span ℝ {v} = collSpan β γ A :=
    Submodule.eq_of_le_of_finrank_le hsup_le (by rw [hfin_sup, h3])
  -- the auxiliary linear map `χ`
  let chi : Space × Space →ₗ[ℝ] Space :=
    (rowAB β γ k).2 • LinearMap.fst ℝ Space Space
      - (rowAB β γ k).1 • LinearMap.snd ℝ Space Space
  have chi_apply (x y : Space) :
      chi (x, y) = (rowAB β γ k).2 • x - (rowAB β γ k).1 • y := by
    simp only [chi, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.fst_apply,
      LinearMap.snd_apply]
  have chi_kill (s : Plin U) : chi (rowL β γ k (s : Space)) = 0 := by
    rw [rowL_apply, chi_apply, smul_smul, smul_smul,
      mul_comm (rowAB β γ k).1 (rowAB β γ k).2, sub_self]
  have hchiW : ∀ z ∈ collSpan β γ A, chi z ∈ Submodule.span ℝ {chi v} := by
    intro z hz
    rw [← hWeq] at hz
    obtain ⟨y, hy, u, hu, hyu⟩ := Submodule.mem_sup.mp hz
    have hy0 : chi y = 0 := by
      rw [mem_LkImg] at hy
      obtain ⟨s, hs, hsy⟩ := hy
      rw [← hsy]
      exact chi_kill ⟨s, mem_Plin.mpr hs⟩
    rw [← hyu, map_add, hy0, zero_add]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hu
    rw [← ht, map_smul]
    exact Submodule.smul_mem _ t (Submodule.subset_span (Set.mem_singleton _))
  -- the two-dimensional space containing all the other rows
  let psi : ℝ × ℝ →ₗ[ℝ] (Space × Space) :=
    { toFun := fun pq => (pq.1 • chi v, pq.2 • chi v)
      map_add' := by intro a b; ext x <;> simp [add_smul]
      map_smul' := by intro c a; ext x <;> simp [mul_smul] }
  have hchi_row (j : Fin 4) :
      chi (collRow β γ A j)
        = ((rowAB β γ k).2 * (rowAB β γ j).1 - (rowAB β γ k).1 * (rowAB β γ j).2) • A j := by
    rw [← rowL_eq_collRow β γ A j, rowL_apply, chi_apply, smul_smul, smul_smul, ← sub_smul]
  have hrow_mem : ∀ j : Fin 4, j ≠ k → collRow β γ A j ∈ LinearMap.range psi := by
    intro j hjk
    have hne : (rowAB β γ k).2 * (rowAB β γ j).1 - (rowAB β γ k).1 * (rowAB β γ j).2 ≠ 0 :=
      rowAB_det_ne β γ hβ0 hβ1 hγ0 hγ1 hβγ hjk
    have hmemW : collRow β γ A j ∈ collSpan β γ A := Submodule.subset_span ⟨j, rfl⟩
    have hchiWj := hchiW _ hmemW
    rw [hchi_row j] at hchiWj
    have hAj : A j ∈ Submodule.span ℝ {chi v} := by
      have h := Submodule.smul_mem (Submodule.span ℝ {chi v})
        ((rowAB β γ k).2 * (rowAB β γ j).1 - (rowAB β γ k).1 * (rowAB β γ j).2)⁻¹ hchiWj
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hAj
    refine ⟨(a * (rowAB β γ j).1, a * (rowAB β γ j).2), ?_⟩
    show psi (a * (rowAB β γ j).1, a * (rowAB β γ j).2) = collRow β γ A j
    rw [← rowL_eq_collRow β γ A j, ← ha, rowL_apply]
    simp only [psi]
    ext x <;> simp [smul_smul, mul_comm, mul_assoc]
  have hspan_le : Submodule.span ℝ
      (Set.range (fun j : {j : Fin 4 // j ≠ k} => collRow β γ A j.1)) ≤ LinearMap.range psi := by
    rw [Submodule.span_le]
    rintro x ⟨⟨j, hjk⟩, rfl⟩
    exact hrow_mem j hjk
  have hfin_range : Module.finrank ℝ (LinearMap.range psi) ≤ 2 := by
    have h := LinearMap.finrank_range_le psi
    rw [Module.finrank_prod, Module.finrank_self] at h
    omega
  calc Module.finrank ℝ
        (Submodule.span ℝ (Set.range (fun j : {j : Fin 4 // j ≠ k} => collRow β γ A j.1)))
      ≤ Module.finrank ℝ (LinearMap.range psi) := Submodule.finrank_mono hspan_le
    _ ≤ 2 := hfin_range

/-! ## Extracting a basis of the row span -/

private lemma exists_fun_fin_span_eq {S : Set (Space × Space)} {r : ℕ}
    (hr : Module.finrank ℝ (Submodule.span ℝ S) = r) :
    ∃ f : Fin r → Space × Space, (∀ i, f i ∈ S) ∧
      Submodule.span ℝ (Set.range f) = Submodule.span ℝ S ∧ LinearIndependent ℝ f := by
  obtain ⟨f, hfmem, hfspan, hfind⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ S
  refine ⟨f ∘ Fin.cast hr.symm, fun i => hfmem _, ?_,
    hfind.comp _ (Fin.cast_injective hr.symm)⟩
  have hrange : Set.range (f ∘ Fin.cast hr.symm) = Set.range f := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hr.symm i, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.cast hr j, by simp⟩
  rw [hrange, hfspan]

/-! ## The main theorem -/

open LeanEval.KnotTheory.Quadrisecant in
/-- **The slot that breaks the rank drop, restricted to the normal plane of `U`.**  Let `U ≠ 0`,
`β, γ ∉ {0,1}` with `β ≠ γ`, and let `A : Fin 4 → Space` be arbitrary.  Put `R i = collRow β γ A i`
and suppose the span of the four rows has dimension `m - 1` with `1 ≤ m ≤ 4`.  Then there is a slot
`k`, an injective enumeration `f : Fin (m-1) → Fin 4` of `m - 1` of the other three slots, and a
vector `p` perpendicular to `U`, such that the rows `R (f i)` are linearly independent and
`R' k ∉ span {R (f i)}`, where `R' k = collRow β γ (Pi.single k p) k` is the slot-`k` change
direction.  (Geometrically `p` is a change of the transverse chord–tangent vector `A k`, and the
transverse vectors are always perpendicular to the chord `U`; the conclusion is the form in which
`Work.Drive.rank_triplet_minors` consumes it.) -/
theorem collRowSlotBreakNormal {U : Space} (hU : U ≠ 0) {β γ : ℝ}
    (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1) (hβγ : β ≠ γ)
    (A : Fin 4 → Space) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (hrk : Module.finrank ℝ (Submodule.span ℝ (Set.range (Work.Drive.collRow β γ A))) = m - 1) :
    ∃ k : Fin 4, ∃ f : Fin (m - 1) → Fin 4, Function.Injective f ∧ (∀ i, f i ≠ k) ∧
      LinearIndependent ℝ (fun i : Fin (m - 1) => Work.Drive.collRow β γ A (f i)) ∧
      ∃ p : Space, inner ℝ p U = 0 ∧ Work.Drive.collRow β γ (Pi.single k p) k ∉
        Submodule.span ℝ (Set.range (fun i : Fin (m - 1) => Work.Drive.collRow β γ A (f i))) := by
  classical
  have hrk' : Module.finrank ℝ (collSpan β γ A) = m - 1 := hrk
  -- ### Step 1: a basis of the row span, of size `m - 1`, extracted from the four rows
  obtain ⟨g, hgmem, hgspan, hgind⟩ :=
    exists_fun_fin_span_eq (S := Set.range (collRow β γ A)) hrk
  let f : Fin (m - 1) → Fin 4 := fun i => Classical.choose (hgmem i)
  have hidx : ∀ i, collRow β γ A (f i) = g i := fun i => Classical.choose_spec (hgmem i)
  have hf_eq : (fun i : Fin (m - 1) => collRow β γ A (f i)) = g := by
    funext i
    exact hidx i
  have hf_ind : LinearIndependent ℝ (fun i : Fin (m - 1) => collRow β γ A (f i)) := by
    rw [hf_eq]
    exact hgind
  have hf_inj : Function.Injective f := by
    intro i j hij
    refine hgind.injective ?_
    rw [← hidx i, ← hidx j, hij]
  have hf_span : Submodule.span ℝ (Set.range (fun i : Fin (m - 1) => collRow β γ A (f i)))
      = collSpan β γ A := by
    rw [hf_eq, hgspan]
    rfl
  -- ### Step 2: the slots left over by the basis
  have hBcard : (Finset.univ.image f : Finset (Fin 4)).card = m - 1 := by
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin (m - 1))) hf_inj,
      Finset.card_univ, Fintype.card_fin]
  have hCcard : (Finset.univ \ Finset.univ.image f : Finset (Fin 4)).card = 4 - (m - 1) := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hBcard]
  have hmemb : ∀ k : Fin 4, k ∈ Finset.univ.image f ↔ ∃ i, f i = k := by
    intro k
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, -, hi⟩
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Finset.mem_univ i, hi⟩
  -- ### Step 3: find a good slot outside the image of `f`
  have hmain : ∃ k : Fin 4, (∀ i, f i ≠ k) ∧
      ∃ p : Space, inner ℝ p U = 0 ∧ rowL β γ k p ∉ collSpan β γ A := by
    by_cases hm3 : m ≤ 3
    · -- plenty of leftover slots: two of them cannot both be bad
      have hC : 1 < (Finset.univ \ Finset.univ.image f : Finset (Fin 4)).card := by
        rw [hCcard]
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hC
      have hanot : ∀ i, f i ≠ a := by
        intro i hi
        exact (Finset.mem_sdiff.mp ha).2 ((hmemb a).mpr ⟨i, hi⟩)
      have hbnot : ∀ i, f i ≠ b := by
        intro i hi
        exact (Finset.mem_sdiff.mp hb).2 ((hmemb b).mpr ⟨i, hi⟩)
      by_cases hgood : ∃ p : Space, inner ℝ p U = 0 ∧ rowL β γ a p ∉ collSpan β γ A
      · exact ⟨a, hanot, hgood⟩
      · refine ⟨b, hbnot, ?_⟩
        by_contra hbad'
        push Not at hbad' hgood
        refine not_bad_pair hU hβ0 hβ1 hγ0 hγ1 hβγ (W := collSpan β γ A) ?_ hab ?_ ?_
        · change Module.finrank ℝ (Submodule.span ℝ (Set.range (collRow β γ A))) ≤ 3
          rw [hrk]
          omega
        · intro x hx
          rw [mem_LkImg] at hx
          obtain ⟨q, hq, hqx⟩ := hx
          rw [← hqx]
          exact hgood q hq
        · intro x hx
          rw [mem_LkImg] at hx
          obtain ⟨q, hq, hqx⟩ := hx
          rw [← hqx]
          exact hbad' q hq
    · -- `m = 4`: the single leftover slot is removable, hence not bad
      have hm4' : m = 4 := by omega
      have hC1 : (Finset.univ \ Finset.univ.image f : Finset (Fin 4)).card = 1 := by
        rw [hCcard, hm4']
      obtain ⟨k0, hk0⟩ := Finset.card_eq_one.mp hC1
      have hk0C : k0 ∈ Finset.univ \ Finset.univ.image f := by
        rw [hk0]
        exact Finset.mem_singleton_self k0
      have hk0not : ∀ i, f i ≠ k0 := by
        intro i hi
        exact (Finset.mem_sdiff.mp hk0C).2 ((hmemb k0).mpr ⟨i, hi⟩)
      have hgood0 : ∃ p : Space, inner ℝ p U = 0 ∧ rowL β γ k0 p ∉ collSpan β γ A := by
        by_contra hbad'
        push Not at hbad'
        have h3 : Module.finrank ℝ (collSpan β γ A) = 3 := by
          rw [hrk', hm4']
        have hle := bad_le_two hU hβ0 hβ1 hγ0 hγ1 hβγ A h3
          (fun x hx => by
            rw [mem_LkImg] at hx
            obtain ⟨q, hq, hqx⟩ := hx
            rw [← hqx]
            exact hbad' q hq)
        -- the other three rows span the whole row span
        have hset : Submodule.span ℝ
              (Set.range (fun j : {j : Fin 4 // j ≠ k0} => collRow β γ A j.1))
            = Submodule.span ℝ (Set.range (fun i : Fin (m - 1) => collRow β γ A (f i))) := by
          apply le_antisymm
          · rw [Submodule.span_le]
            rintro x ⟨j, hjx⟩
            have hjm : (j : Fin 4) ∈ Finset.univ.image f := by
              by_contra hjn
              have hjC : (j : Fin 4) ∈ Finset.univ \ Finset.univ.image f :=
                Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjn⟩
              rw [hk0] at hjC
              exact j.2 (Finset.mem_singleton.mp hjC)
            obtain ⟨i, hi⟩ := (hmemb (j : Fin 4)).mp hjm
            have hxj : x = collRow β γ A (f i) := by
              rw [← hjx]
              change collRow β γ A (j : Fin 4) = collRow β γ A (f i)
              rw [hi]
            rw [hxj]
            exact Submodule.subset_span ⟨i, rfl⟩
          · rw [Submodule.span_le]
            rintro x ⟨i, rfl⟩
            exact Submodule.subset_span ⟨⟨f i, hk0not i⟩, rfl⟩
        have h3' : Module.finrank ℝ
            (Submodule.span ℝ (Set.range (fun j : {j : Fin 4 // j ≠ k0} => collRow β γ A j.1)))
            = 3 := by
          rw [hset, hf_span, hrk', hm4']
        omega
      exact ⟨k0, hk0not, hgood0⟩
  -- ### Step 4: assemble
  obtain ⟨k, hkne, p, hpU, hprow⟩ := hmain
  refine ⟨k, f, hf_inj, hkne, hf_ind, p, hpU, ?_⟩
  rw [collRow_single β γ k p, hf_span]
  exact hprow

end

end Work.Drive
