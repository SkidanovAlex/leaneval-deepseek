import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.carrier_spec
import Submission.Work.Geo.DualStretch.massOf_sum
import Submission.Work.Geo.DualStretch.massOf_chain
import Submission.Work.Geo.DualStretch.massOf_pos_iff
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.coord_eq_rcoord
import Submission.Work.Geo.DualStretch.rcoord_spec
import Submission.Work.PL.Subdiv.Coord
import Submission.Work.PL.Subdiv.SdIndep

/-!
# The mass decomposition of a point given by a chain representation

If `C` is a chain of faces of `P` and `y = ∑_{τ ∈ C} wt τ • bary τ` with `wt > 0` on `C` and
`∑ wt = 1`, then the barycentric masses `massG P hP y` of the level sets are *exactly* the
prescribed weights on `C` and vanish on the other candidate level sets.

The barycentric coordinate function of `y` with respect to its carrier face is the coefficient
function `chainNu C wt v = ∑_{τ ∈ C, v ∈ τ} wt τ / |τ|` (uniqueness of barycentric coordinates on
the affinely independent carrier).  The bulk of the file computes `minVal` and `maxVal` of that
function over the level sets, using only the two facts that `C` is *totally ordered* by inclusion
and that all its weights are positive.
-/

open Set Metric
open scoped Classical BigOperators

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

/-- The barycentre of the present development is the barycentre of the subdivision development. -/
lemma bary_eq_subdiv_bary (s : Finset (E n)) : bary s = Work.PL.Subdiv.bary s := rfl

/-! ## The coefficient function of a chain representation -/

/-- The barycentric coefficient of a vertex `v`: every chain element `σ` containing `v` contributes
`wt σ / |σ|` to `v` in the representation `∑ σ ∈ C, wt σ • bary σ`. -/
noncomputable def chainNu (C : Finset (Finset (E n))) (wt : Finset (E n) → ℝ) (v : E n) : ℝ :=
  ∑ σ ∈ C.filter (fun σ => v ∈ σ), wt σ / (σ.card : ℝ)

/-! ## Vertex bookkeeping -/

lemma mem_verts {P : Cx n} {hP : P.faces.Finite} {v : E n} :
    v ∈ verts P hP ↔ ∃ σ ∈ P.faces, v ∈ σ := by
  rw [verts, Finset.mem_biUnion]
  constructor
  · rintro ⟨σ, hσ, hv⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mp hσ, hv⟩
  · rintro ⟨σ, hσ, hv⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mpr hσ, hv⟩

lemma mem_cands {P : Cx n} {hP : P.faces.Finite} {τ : Finset (E n)} :
    τ ∈ cands P hP ↔ ∃ σ ∈ P.faces, τ ⊆ σ := by
  rw [cands, Finset.mem_biUnion]
  constructor
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mp hσ, Finset.mem_powerset.mp hτ⟩
  · rintro ⟨σ, hσ, hτ⟩
    exact ⟨σ, (Set.Finite.mem_toFinset hP).mpr hσ, Finset.mem_powerset.mpr hτ⟩

lemma faces_subset_verts (P : Cx n) (hP : P.faces.Finite) {σ : Finset (E n)} (hσ : σ ∈ P.faces) :
    σ ⊆ verts P hP := by
  intro v hv
  rw [mem_verts]
  exact ⟨σ, hσ, hv⟩

/-! ## Elementary properties of `chainNu` -/

lemma chainNu_nonneg {C : Finset (Finset (E n))} {wt : Finset (E n) → ℝ}
    (hpos : ∀ σ ∈ C, 0 < wt σ) (v : E n) : 0 ≤ chainNu C wt v := by
  rw [chainNu]
  refine Finset.sum_nonneg fun σ hσ => ?_
  exact div_nonneg (le_of_lt (hpos σ (Finset.mem_of_mem_filter σ hσ))) (Nat.cast_nonneg _)

lemma chainNu_eq_zero_of_not_mem_chainTop {C : Finset (Finset (E n))} {wt : Finset (E n) → ℝ}
    {v : E n} (hv : v ∉ Work.PL.Subdiv.chainTop C) : chainNu C wt v = 0 := by
  rw [chainNu]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  obtain ⟨hσC, hvσ⟩ := Finset.mem_filter.mp hσ
  exact absurd (Work.PL.Subdiv.le_chainTop hσC hvσ) hv

/-- **Monotonicity of the coefficients along the chain**: a vertex of a chain element has larger
coefficient than a vertex outside it. -/
lemma chainNu_le_chainNu {C : Finset (Finset (E n))} {wt : Finset (E n) → ℝ}
    (hchain : IsChain C) (hpos : ∀ σ ∈ C, 0 < wt σ)
    {σ : Finset (E n)} (hσ : σ ∈ C) {a b : E n} (ha : a ∈ σ) (hb : b ∉ σ) :
    chainNu C wt b ≤ chainNu C wt a := by
  rw [chainNu, chainNu]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro σ' hσ'
    obtain ⟨hσ'C, hbσ'⟩ := Finset.mem_filter.mp hσ'
    refine Finset.mem_filter.mpr ⟨hσ'C, ?_⟩
    rcases hchain σ' hσ'C σ hσ with h | h
    · exact absurd (h hbσ') hb
    · exact h ha
  · intro σ' hσ' _
    exact div_nonneg (le_of_lt (hpos σ' (Finset.mem_filter.mp hσ' ).1)) (Nat.cast_nonneg _)

/-- The total coefficient mass over the top of the chain is `1`. -/
lemma sum_chainNu_eq_one (P : Cx n) {C : Finset (Finset (E n))}
    (hCsub : (C : Set (Finset (E n))) ⊆ P.faces) (hchain : IsChain C) {wt : Finset (E n) → ℝ}
    (hsum : ∑ σ ∈ C, wt σ = 1) :
    ∑ v ∈ Work.PL.Subdiv.chainTop C, chainNu C wt v = 1 := by
  rw [← hsum]
  simp only [chainNu]
  exact Work.PL.Subdiv.sum_coeff_filter C (Work.PL.Subdiv.chainTop C)
    (fun σ hσ => Work.PL.Subdiv.le_chainTop hσ)
    (fun σ hσ => P.nonempty_of_mem_faces (hCsub hσ)) wt

/-- The coefficients realise the point `y`. -/
lemma sum_chainNu_smul_eq {C : Finset (Finset (E n))} {wt : Finset (E n) → ℝ}
    (hchain : IsChain C) :
    ∑ v ∈ Work.PL.Subdiv.chainTop C, chainNu C wt v • v = ∑ σ ∈ C, wt σ • bary σ := by
  have h := Work.PL.Subdiv.sum_smul_bary_eq_sum_smul C (Work.PL.Subdiv.chainTop C)
    (fun σ hσ => Work.PL.Subdiv.le_chainTop hσ) wt
  have h2 : (∑ σ ∈ C, wt σ • bary σ)
      = ∑ σ ∈ C, wt σ • Work.PL.Subdiv.bary σ :=
    Finset.sum_congr rfl fun σ _ => by rw [bary_eq_subdiv_bary]
  simp only [chainNu]
  rw [h2, ← h]

/-! ## The coordinate function of a chain representation -/

lemma coord_eq_chainNu (P : Cx n) (hP : P.faces.Finite) {C : Finset (Finset (E n))}
    (hCsub : (C : Set (Finset (E n))) ⊆ P.faces) (hne : C.Nonempty) (hchain : IsChain C)
    {wt : Finset (E n) → ℝ} (hpos : ∀ σ ∈ C, 0 < wt σ) (hsum : ∑ σ ∈ C, wt σ = 1)
    {y : E n} (hy : y = ∑ σ ∈ C, wt σ • bary σ) :
    coord P y = chainNu C wt := by
  classical
  set B := Work.PL.Subdiv.chainTop C with hB
  have hBf : B ∈ P.faces := hCsub (Work.PL.Subdiv.chainTop_mem_chain hchain hne)
  have hyB : y ∈ PL.simp B := by
    rw [hy]
    refine (convex_convexHull ℝ (B : Set (E n))).sum_mem
      (fun σ hσ => le_of_lt (hpos σ hσ)) hsum (fun σ hσ => ?_)
    exact simp_mono (Work.PL.Subdiv.le_chainTop hσ)
      (bary_mem_simp (P.nonempty_of_mem_faces (hCsub hσ)))
  obtain ⟨-, hr1, hr2, hr3⟩ := rcoord_spec (P.indep hBf) hyB
  have huniq : ∀ v ∈ B, rcoord B y v = chainNu C wt v :=
    eq_on_of_sum_eq_one_of_sum_smul_eq (P.indep hBf) hr1 hr2
      (sum_chainNu_eq_one P hCsub hchain hsum)
      (by rw [sum_chainNu_smul_eq hchain]; exact hy.symm)
  funext v
  by_cases hv : v ∈ B
  · exact (coord_eq_rcoord P hP hBf hyB v).trans (huniq v hv)
  · rw [coord_eq_rcoord P hP hBf hyB v, hr3 v hv, chainNu_eq_zero_of_not_mem_chainTop hv]

/-! ## The extremal vertices of a chain element -/

/-- Every element `τ` of a chain has a vertex `u` which lies in *exactly* the chain elements
containing `τ`. -/
lemma exists_vertex_iff_subset {C : Finset (Finset (E n))} (hchain : IsChain C)
    {τ : Finset (E n)} (hτ : τ ∈ C) (hτne : τ.Nonempty) :
    ∃ u ∈ τ, ∀ σ ∈ C, (u ∈ σ ↔ τ ⊆ σ) := by
  classical
  set below := C.filter (fun σ => σ ⊂ τ) with hbelow
  have hnotsub : ¬ τ ⊆ Work.PL.Subdiv.chainTop below := by
    by_cases hb : below.Nonempty
    · have hchainb : ∀ ρ ∈ below, ∀ ρ' ∈ below, ρ ⊆ ρ' ∨ ρ' ⊆ ρ :=
        fun ρ hρ ρ' hρ' => hchain ρ (Finset.mem_of_mem_filter ρ hρ) ρ'
          (Finset.mem_of_mem_filter ρ' hρ')
      have hmem : Work.PL.Subdiv.chainTop below ∈ below :=
        Work.PL.Subdiv.chainTop_mem_chain hchainb hb
      intro hcontra
      have hlt : (Work.PL.Subdiv.chainTop below).card < τ.card :=
        Finset.card_lt_card (Finset.mem_filter.mp hmem).2
      have hle : τ.card ≤ (Work.PL.Subdiv.chainTop below).card :=
        Finset.card_le_card hcontra
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp hb, Work.PL.Subdiv.chainTop_empty]
      intro hc
      exact hτne.ne_empty (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => (Finset.notMem_empty x) (hc hx))
  obtain ⟨u, huτ, huB⟩ := Finset.not_subset.mp hnotsub
  refine ⟨u, huτ, fun σ hσC => ⟨fun huσ => ?_, fun hτσ => hτσ huτ⟩⟩
  by_contra hnot
  rcases hchain σ hσC τ hτ with h | h
  · have hssub : σ ⊂ τ := Finset.ssubset_iff_subset_ne.mpr ⟨h, fun he => hnot (by rw [he])⟩
    have hσbelow : σ ∈ below := Finset.mem_filter.mpr ⟨hσC, hssub⟩
    exact huB (Work.PL.Subdiv.le_chainTop hσbelow huσ)
  · exact hnot h

/-! ## `minVal` and `maxVal` of the coefficient function on the chain -/

lemma minVal_chainNu_eq {C : Finset (Finset (E n))} {wt : Finset (E n) → ℝ}
    (hchain : IsChain C) (hpos : ∀ σ ∈ C, 0 < wt σ)
    {τ : Finset (E n)} (hτ : τ ∈ C) (hτne : τ.Nonempty) :
    minVal τ (chainNu C wt)
      = ∑ σ ∈ C.filter (fun σ => τ ⊆ σ), wt σ / (σ.card : ℝ) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨u, huτ, hu⟩ := exists_vertex_iff_subset hchain hτ hτne
    have h1 : chainNu C wt u = ∑ σ ∈ C.filter (fun σ => τ ⊆ σ), wt σ / (σ.card : ℝ) := by
      rw [chainNu]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext σ
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨h.1, (hu σ h.1).mp h.2⟩, fun h => ⟨h.1, (hu σ h.1).mpr h.2⟩⟩
    exact le_trans (minVal_le huτ) (le_of_eq h1)
  · refine minVal_le_of_le hτne fun u hu => ?_
    rw [chainNu]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro σ hσ
      obtain ⟨hσC, hτσ⟩ := Finset.mem_filter.mp hσ
      exact Finset.mem_filter.mpr ⟨hσC, hτσ hu⟩
    · intro σ hσ _
      exact div_nonneg (le_of_lt (hpos σ (Finset.mem_filter.mp hσ).1)) (Nat.cast_nonneg _)

lemma maxVal_chainNu_eq (P : Cx n) (hP : P.faces.Finite) {C : Finset (Finset (E n))}
    (hCsub : (C : Set (Finset (E n))) ⊆ P.faces) (hchain : IsChain C)
    {wt : Finset (E n) → ℝ} (hpos : ∀ σ ∈ C, 0 < wt σ)
    {τ : Finset (E n)} (hτ : τ ∈ C) :
    maxVal (verts P hP \ τ) (chainNu C wt)
      = ∑ σ ∈ C.filter (fun σ => τ ⊂ σ), wt σ / (σ.card : ℝ) := by
  refine le_antisymm ?_ ?_
  · by_cases hs : (verts P hP \ τ).Nonempty
    · refine maxVal_le hs fun v hv => ?_
      rw [Finset.mem_sdiff] at hv
      obtain ⟨-, hvτ⟩ := hv
      rw [chainNu]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro σ hσ
        obtain ⟨hσC, hvσ⟩ := Finset.mem_filter.mp hσ
        refine Finset.mem_filter.mpr ⟨hσC, ?_⟩
        rcases hchain σ hσC τ hτ with h | h
        · exact absurd (h hvσ) hvτ
        · exact Finset.ssubset_iff_subset_ne.mpr ⟨h, fun he => hvτ (by rw [he]; exact hvσ)⟩
      · intro σ hσ _
        exact div_nonneg (le_of_lt (hpos σ (Finset.mem_filter.mp hσ).1)) (Nat.cast_nonneg _)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, maxVal_empty]
      exact Finset.sum_nonneg fun σ hσ =>
        div_nonneg (le_of_lt (hpos σ (Finset.mem_filter.mp hσ).1)) (Nat.cast_nonneg _)
  · by_cases hs : (C.filter (fun σ => τ ⊂ σ)).Nonempty
    · obtain ⟨σs, hσs, hσsmin⟩ :=
        Finset.exists_min_image (C.filter (fun σ => τ ⊂ σ)) Finset.card hs
      obtain ⟨hσsC, hτσs⟩ := Finset.mem_filter.mp hσs
      obtain ⟨v, hvσs, hvτ⟩ := Finset.exists_of_ssubset hτσs
      have hvvert : v ∈ verts P hP := faces_subset_verts P hP (hCsub hσsC) hvσs
      refine le_trans ?_ (le_maxVal (Finset.mem_sdiff.mpr ⟨hvvert, hvτ⟩))
      rw [chainNu]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro σ hσ
        obtain ⟨hσC, hτσ⟩ := Finset.mem_filter.mp hσ
        refine Finset.mem_filter.mpr ⟨hσC, ?_⟩
        have hsub : σs ⊆ σ := by
          rcases hchain σs hσsC σ hσC with h | h
          · exact h
          · have h1 : σ.card ≤ σs.card := Finset.card_le_card h
            have h2 := hσsmin σ (Finset.mem_filter.mpr ⟨hσC, hτσ⟩)
            have heq : σ = σs := Finset.eq_of_subset_of_card_le h (by omega)
            rw [heq]
        exact hsub hvσs
      · intro σ hσ _
        exact div_nonneg (le_of_lt (hpos σ (Finset.mem_filter.mp hσ).1)) (Nat.cast_nonneg _)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
      exact maxVal_nonneg fun v _ => chainNu_nonneg hpos v

/-- The two sums telescope: the sum over the chain elements containing `τ` minus the sum over those
strictly containing `τ` is the contribution `wt τ / |τ|` of `τ` itself. -/
lemma sum_filter_sub {C : Finset (Finset (E n))} {wt : Finset (E n) → ℝ}
    {τ : Finset (E n)} (hτ : τ ∈ C) :
    (∑ σ ∈ C.filter (fun σ => τ ⊆ σ), wt σ / (σ.card : ℝ))
      - (∑ σ ∈ C.filter (fun σ => τ ⊂ σ), wt σ / (σ.card : ℝ)) = wt τ / (τ.card : ℝ) := by
  have hf : C.filter (fun σ => τ ⊆ σ) = insert τ (C.filter (fun σ => τ ⊂ σ)) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hσC, hτσ⟩
      by_cases he : σ = τ
      · exact Or.inl he
      · exact Or.inr ⟨hσC, Finset.ssubset_iff_subset_ne.mpr ⟨hτσ, fun h => he h.symm⟩⟩
    · rintro (heq | ⟨hσC, hτσ⟩)
      · rw [heq]; exact ⟨hτ, Finset.Subset.refl τ⟩
      · exact ⟨hσC, (Finset.ssubset_iff_subset_ne.mp hτσ).1⟩
  have hnotmem : τ ∉ C.filter (fun σ => τ ⊂ σ) := by
    rw [Finset.mem_filter]
    rintro ⟨-, h⟩
    exact (Finset.ssubset_iff_subset_ne.mp h).2 rfl
  rw [hf, Finset.sum_insert hnotmem]
  ring

/-! ## Rewriting `massG` through the coordinate function -/

lemma massG_eq_of_coord_eq (P : Cx n) (hP : P.faces.Finite) {y : E n} {ν : E n → ℝ}
    (hcoord : coord P y = ν) (τ : Finset (E n)) :
    massG P hP y τ = max 0 ((τ.card : ℝ) * (minVal τ ν - maxVal (verts P hP \ τ) ν)) := by
  simp only [massG]
  rw [hcoord]

/-! ## The target -/

theorem massG_of_chain_repr {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) (C : Finset (Finset (PL.E n)))
    (hC : (C : Set (Finset (PL.E n))) ⊆ P.faces) (hne : C.Nonempty)
    (hchain : Work.Geo.DualStretch.IsChain C) (wt : Finset (PL.E n) → ℝ)
    (hpos : ∀ τ ∈ C, 0 < wt τ) (hsum : ∑ τ ∈ C, wt τ = 1) {y : PL.E n}
    (hy : y = ∑ τ ∈ C, wt τ • Work.Geo.DualStretch.bary τ) :
    (∀ τ ∈ C, Work.Geo.DualStretch.massG P hP y τ = wt τ) ∧
      (∀ τ ∈ Work.Geo.DualStretch.cands P hP, τ ∉ C →
        Work.Geo.DualStretch.massG P hP y τ = 0) := by
  have hcoord : coord P y = chainNu C wt := coord_eq_chainNu P hP hC hne hchain hpos hsum hy
  constructor
  · intro τ hτ
    have hτne : τ.Nonempty := P.nonempty_of_mem_faces (hC hτ)
    have hD : minVal τ (chainNu C wt) - maxVal (verts P hP \ τ) (chainNu C wt)
        = wt τ / (τ.card : ℝ) := by
      rw [minVal_chainNu_eq hchain hpos hτ hτne, maxVal_chainNu_eq P hP hC hchain hpos hτ,
        sum_filter_sub hτ]
    rw [massG_eq_of_coord_eq P hP hcoord τ, hD]
    have hcard : (τ.card : ℝ) ≠ 0 := by
      have : 0 < τ.card := hτne.card_pos
      exact_mod_cast this.ne'
    rw [max_eq_right (mul_nonneg (Nat.cast_nonneg _)
          (div_nonneg (le_of_lt (hpos τ hτ)) (Nat.cast_nonneg _))),
      mul_div_cancel₀ (wt τ) hcard]
  · intro τ _ hτnotC
    rw [massG_eq_of_coord_eq P hP hcoord τ]
    by_cases hcard : τ.card = 0
    · rw [hcard]; norm_num
    · have hτne : τ.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
      have hD : minVal τ (chainNu C wt) - maxVal (verts P hP \ τ) (chainNu C wt) ≤ 0 := by
        rw [sub_nonpos]
        by_cases hsub : τ ⊆ Work.PL.Subdiv.chainTop C
        · have hCn : (C.filter (fun σ => τ ⊆ σ)).Nonempty :=
            ⟨Work.PL.Subdiv.chainTop C, Finset.mem_filter.mpr
              ⟨Work.PL.Subdiv.chainTop_mem_chain hchain hne, hsub⟩⟩
          obtain ⟨τs, hτs, hτsmin⟩ :=
            Finset.exists_min_image (C.filter (fun σ => τ ⊆ σ)) Finset.card hCn
          obtain ⟨hτsC, hττs⟩ := Finset.mem_filter.mp hτs
          have hτssub : τ ⊂ τs := by
            rw [Finset.ssubset_iff_subset_ne]
            exact ⟨hττs, fun he => hτnotC (by rw [he]; exact hτsC)⟩
          obtain ⟨v, hvτs, hvτ⟩ := Finset.exists_of_ssubset hτssub
          set below := C.filter (fun σ => σ ⊂ τs) with hbelow
          have hchainb : ∀ ρ ∈ below, ∀ ρ' ∈ below, ρ ⊆ ρ' ∨ ρ' ⊆ ρ :=
            fun ρ hρ ρ' hρ' => hchain ρ (Finset.mem_of_mem_filter ρ hρ) ρ'
              (Finset.mem_of_mem_filter ρ' hρ')
          have hnotsub2 : ¬ τ ⊆ Work.PL.Subdiv.chainTop below := by
            by_cases hb : below.Nonempty
            · have hmem : Work.PL.Subdiv.chainTop below ∈ below :=
                Work.PL.Subdiv.chainTop_mem_chain hchainb hb
              intro hcontra
              have hlt : (Work.PL.Subdiv.chainTop below).card < τs.card :=
                Finset.card_lt_card (Finset.mem_filter.mp hmem).2
              have hmemC : Work.PL.Subdiv.chainTop below ∈ C :=
                (Finset.mem_filter.mp hmem).1
              have hle := hτsmin _ (Finset.mem_filter.mpr ⟨hmemC, hcontra⟩)
              omega
            · rw [Finset.not_nonempty_iff_eq_empty.mp hb, Work.PL.Subdiv.chainTop_empty]
              intro hc
              exact hτne.ne_empty (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => (Finset.notMem_empty x) (hc hx))
          obtain ⟨u, huτ, huB⟩ := Finset.not_subset.mp hnotsub2
          have hle : chainNu C wt u ≤ chainNu C wt v := by
            rw [chainNu, chainNu]
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro σ hσ
              obtain ⟨hσC, huσ⟩ := Finset.mem_filter.mp hσ
              refine Finset.mem_filter.mpr ⟨hσC, ?_⟩
              by_contra hvσ
              rcases hchain σ hσC τs hτsC with h | h
              · have hσne : σ ≠ τs := fun he => hvσ (by rw [he]; exact hvτs)
                have hσbelow : σ ∈ below :=
                  Finset.mem_filter.mpr ⟨hσC, Finset.ssubset_iff_subset_ne.mpr ⟨h, hσne⟩⟩
                exact huB (Work.PL.Subdiv.le_chainTop hσbelow huσ)
              · exact hvσ (h hvτs)
            · intro σ hσ _
              exact div_nonneg (le_of_lt (hpos σ (Finset.mem_filter.mp hσ).1)) (Nat.cast_nonneg _)
          refine le_trans (le_trans (minVal_le huτ) hle) (le_maxVal ?_)
          exact Finset.mem_sdiff.mpr ⟨faces_subset_verts P hP (hC hτsC) hvτs, hvτ⟩
        · obtain ⟨u, huτ, huB⟩ := Finset.not_subset.mp hsub
          refine le_trans (minVal_le huτ) ?_
          rw [chainNu_eq_zero_of_not_mem_chainTop huB]
          exact maxVal_nonneg fun v _ => chainNu_nonneg hpos v
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hD)]

end Work.Geo.DualStretch
