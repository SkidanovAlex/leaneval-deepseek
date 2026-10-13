import Mathlib
import Submission.Work.WilG1.Basic

/-!
# `thin_union`: finite unions of thin `Ω`-sets are thin

This file proves `Work.WilG1.Cell.thin_union`, the statement that a finite union of
sets of empty interior, all of bounded format and degree in a sharply o-minimal
structure, again has empty interior.

The mathematical content is the standard "refine by a cylindrical decomposition"
argument:

* `SharpCD` provides a cylindrical decomposition `C` of `ℝⁿ` every cell of which is
  either contained in `A i` or disjoint from it, for every `i`;
* hence `⋃ i, A i` is the union of the subfamily `T ⊆ C` of cells contained in some
  `A i`, and every such cell is thin;
* a finite union of thin cells of a cylindrical decomposition is thin
  (`sUnion_thin`, proved via `exists_thick_cell`).

The key analytic input is that the fibre of a cell over a point of the base cell is
either a single point (`graph` cells) or an interval (`band` cells), so a union of
thin cells has finite vertical fibres inside each base cell; a ball has infinite
vertical fibres, giving the contradiction.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.Cell

section Helpers

/-! ## Distance estimates for `Fin.snoc` -/

lemma dist_snoc_snoc {m : ℕ} (u v : Fin m → ℝ) (c : ℝ) :
    dist (Fin.snoc u c : Fin (m+1) → ℝ) (Fin.snoc v c) = dist u v := by
  refine le_antisymm ?_ ?_
  · rw [dist_pi_le_iff dist_nonneg]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact dist_le_pi_dist u v j
    · rw [Fin.snoc_last, Fin.snoc_last, dist_self]
      exact dist_nonneg
  · rw [dist_pi_le_iff dist_nonneg]
    intro j
    have := dist_le_pi_dist (f := (Fin.snoc u c : Fin (m+1) → ℝ))
      (g := (Fin.snoc v c : Fin (m+1) → ℝ)) (Fin.castSucc j)
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at this
    exact this

lemma dist_snoc_last {m : ℕ} (u : Fin m → ℝ) (a b : ℝ) :
    dist (Fin.snoc u a : Fin (m+1) → ℝ) (Fin.snoc u b) = |a - b| := by
  refine le_antisymm ?_ ?_
  · rw [dist_pi_le_iff (abs_nonneg _)]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, dist_self]
      exact abs_nonneg _
    · rw [Fin.snoc_last, Fin.snoc_last, Real.dist_eq]
  · have h := dist_le_pi_dist (f := (Fin.snoc u a : Fin (m+1) → ℝ))
      (g := (Fin.snoc u b : Fin (m+1) → ℝ)) (Fin.last m)
    rw [Fin.snoc_last, Fin.snoc_last, Real.dist_eq] at h
    exact h

lemma isOpen_preimage_snoc {m : ℕ} (c : ℝ) {s : Set (Fin (m+1) → ℝ)} (hs : IsOpen s) :
    IsOpen {u : Fin m → ℝ | Fin.snoc u c ∈ s} := by
  rw [Metric.isOpen_iff] at hs ⊢
  rintro u hu
  obtain ⟨ε, hε, hεs⟩ := hs (Fin.snoc u c) hu
  refine ⟨ε, hε, fun v hv => hεs ?_⟩
  rw [Metric.mem_ball] at hv ⊢
  rwa [dist_snoc_snoc]

/-- A nonempty ball has infinite vertical fibres. -/
lemma ball_fiber_infinite {m : ℕ} {p z : Fin (m+1) → ℝ} {r : ℝ} (_hr : 0 < r)
    (hz : z ∈ Metric.ball p r) :
    {y : Fin (m+1) → ℝ | Fin.init y = Fin.init z ∧ y ∈ Metric.ball p r}.Infinite := by
  have hdz : dist z p < r := Metric.mem_ball.mp hz
  set e : ℝ := (r - dist z p) / 2 with he
  have hdist : ∀ t : ℝ, dist (Fin.snoc (Fin.init z) t : Fin (m+1) → ℝ) z
      = |t - z (Fin.last m)| := by
    intro t
    calc dist (Fin.snoc (Fin.init z) t : Fin (m+1) → ℝ) z
        = dist (Fin.snoc (Fin.init z) t) (Fin.snoc (Fin.init z) (z (Fin.last m))) := by
          rw [Fin.snoc_init_self z]
      _ = |t - z (Fin.last m)| := dist_snoc_last _ _ _
  have hsub : (fun t : ℝ => (Fin.snoc (Fin.init z) t : Fin (m+1) → ℝ)) ''
      Set.Ioo (z (Fin.last m) - e) (z (Fin.last m) + e) ⊆
      {y : Fin (m+1) → ℝ | Fin.init y = Fin.init z ∧ y ∈ Metric.ball p r} := by
    rintro y ⟨t, ht, rfl⟩
    refine ⟨Fin.init_snoc _ _, ?_⟩
    rw [Metric.mem_ball]
    have hlt : |t - z (Fin.last m)| < e := by
      rw [Set.mem_Ioo] at ht
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    calc dist (Fin.snoc (Fin.init z) t : Fin (m+1) → ℝ) p
        ≤ dist (Fin.snoc (Fin.init z) t : Fin (m+1) → ℝ) z + dist z p := dist_triangle _ _ _
      _ = |t - z (Fin.last m)| + dist z p := by rw [hdist]
      _ < e + dist z p := by linarith
      _ = (r + dist z p) / 2 := by rw [he]; ring
      _ < r := by linarith
  refine Set.Infinite.mono hsub ?_
  have hI : (Set.Ioo (z (Fin.last m) - e) (z (Fin.last m) + e)).Infinite :=
    Set.Ioo_infinite (by linarith)
  refine hI.image ?_
  intro t₁ _ t₂ _ h
  have := congrFun h (Fin.last m)
  simpa [Fin.snoc_last] using this

/-! ## Structural facts about cells and decompositions -/

/-- A cell of dimension `m+1` is either a graph cell or a band cell over a cell of
dimension `m`. -/
lemma cell_cases {m : ℕ} {κ : Set (Fin (m+1) → ℝ)} (h : WilkiesDesign.IsCell (m+1) κ) :
    (∃ (τ : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → ℝ), ContinuousOn f τ ∧
      ∀ z : Fin (m+1) → ℝ, (z ∈ κ ↔ (Fin.init z ∈ τ ∧ z (Fin.last m) = f (Fin.init z)))) ∨
    (∃ (τ : Set (Fin m → ℝ)) (a b : (Fin m → ℝ) → EReal), ContinuousOn a τ ∧ ContinuousOn b τ ∧
      (∀ x ∈ τ, a x < b x) ∧
      ∀ z : Fin (m+1) → ℝ, (z ∈ κ ↔ (Fin.init z ∈ τ ∧ a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧ ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)))) := by
  cases h with
  | graph hC f hf => exact Or.inl ⟨_, _, hf, fun z => Iff.rfl⟩
  | band hC a b ha hb hab => exact Or.inr ⟨_, _, _, ha, hb, hab, fun z => Iff.rfl⟩

/-- A band cell over a base cell with nonempty interior has nonempty interior. -/
lemma interior_band_nonempty {m : ℕ} {τ : Set (Fin m → ℝ)} {a b : (Fin m → ℝ) → EReal}
    (ha : ContinuousOn a τ) (hb : ContinuousOn b τ) (hab : ∀ x ∈ τ, a x < b x)
    (hτ : (interior τ).Nonempty) :
    (interior {z : Fin (m+1) → ℝ | Fin.init z ∈ τ ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)}).Nonempty := by
  set U : Set (Fin m → ℝ) := interior τ with hU
  have hUne : U.Nonempty := hτ
  have hUopen : IsOpen U := isOpen_interior
  have hUsub : U ⊆ τ := interior_subset
  have ha' : ContinuousOn a U := ha.mono hUsub
  have hb' : ContinuousOn b U := hb.mono hUsub
  have hinit : Continuous (Fin.init : (Fin (m+1) → ℝ) → (Fin m → ℝ)) :=
    continuous_pi (fun i => continuous_apply (Fin.castSucc i))
  set F : (Fin (m+1) → ℝ) → EReal := fun w => a (Fin.init w) with hF
  set F' : (Fin (m+1) → ℝ) → EReal := fun w => b (Fin.init w) with hF'
  set G : (Fin (m+1) → ℝ) → EReal := fun w => ((w (Fin.last m) : ℝ) : EReal) with hG
  have hV : IsOpen {w : Fin (m+1) → ℝ | Fin.init w ∈ U} := hUopen.preimage hinit
  have hFcont : ContinuousOn F {w : Fin (m+1) → ℝ | Fin.init w ∈ U} :=
    ha'.comp hinit.continuousOn (fun w hw => hw)
  have hF'cont : ContinuousOn F' {w : Fin (m+1) → ℝ | Fin.init w ∈ U} :=
    hb'.comp hinit.continuousOn (fun w hw => hw)
  have hGcont : ContinuousOn G {w : Fin (m+1) → ℝ | Fin.init w ∈ U} :=
    (continuous_coe_real_ereal.comp (continuous_apply (Fin.last m))).continuousOn
  have hlt : IsOpen {p : EReal × EReal | p.1 < p.2} := isOpen_lt continuous_fst continuous_snd
  have h1 : IsOpen ({w : Fin (m+1) → ℝ | Fin.init w ∈ U} ∩
      (fun w => (F w, G w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) :=
    ContinuousOn.isOpen_inter_preimage (hFcont.prodMk hGcont) hV hlt
  have h2 : IsOpen ({w : Fin (m+1) → ℝ | Fin.init w ∈ U} ∩
      (fun w => (G w, F' w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) :=
    ContinuousOn.isOpen_inter_preimage (hGcont.prodMk hF'cont) hV hlt
  have hWU : IsOpen {z : Fin (m+1) → ℝ | Fin.init z ∈ U ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)} := by
    have heq : {z : Fin (m+1) → ℝ | Fin.init z ∈ U ∧
        a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
        ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)}
      = ({w : Fin (m+1) → ℝ | Fin.init w ∈ U} ∩
          (fun w => (F w, G w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) ∩
        ({w : Fin (m+1) → ℝ | Fin.init w ∈ U} ∩
          (fun w => (G w, F' w)) ⁻¹' {p : EReal × EReal | p.1 < p.2}) := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, hF, hF', hG]
      tauto
    rw [heq]; exact h1.inter h2
  have hsub : {z : Fin (m+1) → ℝ | Fin.init z ∈ U ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)} ⊆
      {z : Fin (m+1) → ℝ | Fin.init z ∈ τ ∧
      a (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
      ((z (Fin.last m) : ℝ) : EReal) < b (Fin.init z)} :=
    fun z hz => ⟨hUsub hz.1, hz.2.1, hz.2.2⟩
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab u (hUsub hu))
  refine ⟨Fin.snoc u t, interior_maximal hsub hWU ?_⟩
  exact ⟨by rw [Fin.init_snoc]; exact hu, by rw [Fin.init_snoc, Fin.snoc_last]; exact ht1,
    by rw [Fin.init_snoc, Fin.snoc_last]; exact ht2⟩

lemma isCell_of_mem_cylDecomp {m : ℕ} {C : Finset (Set (Fin m → ℝ))}
    (h : WilkiesDesign.IsCylDecomp m C) {κ : Set (Fin m → ℝ)} (hκ : κ ∈ C) :
    WilkiesDesign.IsCell m κ := by
  cases m with
  | zero =>
    rw [show C = {Set.univ} from h] at hκ
    rw [Finset.mem_singleton] at hκ
    rw [hκ]; exact WilkiesDesign.IsCell.zero
  | succ m => exact (h.1 κ hκ).1

lemma exists_mem_of_cylDecomp {m : ℕ} {C : Finset (Set (Fin m → ℝ))}
    (h : WilkiesDesign.IsCylDecomp m C) (z : Fin m → ℝ) : ∃ κ ∈ C, z ∈ κ := by
  cases m with
  | zero =>
    refine ⟨Set.univ, ?_, Set.mem_univ _⟩
    rw [show C = {Set.univ} from h]; exact Finset.mem_singleton_self _
  | succ m => exact h.2.2.1 z

lemma pairwiseDisjoint_of_cylDecomp {m : ℕ} {C : Finset (Set (Fin m → ℝ))}
    (h : WilkiesDesign.IsCylDecomp m C) :
    (C : Set (Set (Fin m → ℝ))).PairwiseDisjoint id := by
  cases m with
  | zero =>
    rw [show C = {Set.univ} from h]
    intro a ha b hb hne
    simp only [Finset.mem_coe, Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hne
  | succ m => exact h.2.1

/-! ## The main induction -/

/-- **Key lemma.** If the union of a subfamily `T` of the cells of a cylindrical
decomposition of `ℝᵐ` has nonempty interior, then one cell of `T` has nonempty
interior. -/
theorem exists_thick_cell (m : ℕ) :
    ∀ (C : Finset (Set (Fin m → ℝ))), WilkiesDesign.IsCylDecomp m C →
    ∀ T : Finset (Set (Fin m → ℝ)), T ⊆ C →
    (interior (⋃₀ (T : Set (Set (Fin m → ℝ))))).Nonempty →
    ∃ κ ∈ T, (interior κ).Nonempty := by
  induction m with
  | zero =>
    intro C hC T hT hne
    have hCu : C = {Set.univ} := hC
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h] at hne
      simp at hne
    obtain ⟨κ, hκ⟩ := hTne
    refine ⟨κ, hκ, ?_⟩
    have hκu : κ = Set.univ := by
      have := hT hκ
      rw [hCu] at this
      simpa using this
    rw [hκu]
    exact ⟨fun i => i.elim0, by rw [interior_univ]; trivial⟩
  | succ m ih =>
    intro C hC T hT hne
    classical
    obtain ⟨p, hp⟩ := hne
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
    have hc4 : WilkiesDesign.IsCylDecomp m (C.image (fun c => Fin.init '' c)) := by
      obtain ⟨_, _, _, h4⟩ := hC; exact h4
    set C' : Finset (Set (Fin m → ℝ)) := C.image (fun c => Fin.init '' c) with hC'def
    set T' : Finset (Set (Fin m → ℝ)) := T.image (fun c => Fin.init '' c) with hT'def
    have hc4' : WilkiesDesign.IsCylDecomp m C' := hc4
    have hT'sub : T' ⊆ C' := by
      rw [hT'def, hC'def]; exact Finset.image_subset_image hT
    set T'' : Finset (Set (Fin m → ℝ)) :=
      T'.filter (fun σ => (σ ∩ (Fin.init '' Metric.ball p r)).Nonempty) with hT''def
    have hT''sub : T'' ⊆ C' := by
      intro σ hσ
      rw [hT''def] at hσ
      exact hT'sub (Finset.mem_of_mem_filter σ hσ)
    have hne'' : (interior (⋃₀ (T'' : Set (Set (Fin m → ℝ))))).Nonempty := by
      set U : Set (Fin m → ℝ) :=
        {u | (Fin.snoc u (p (Fin.last m)) : Fin (m+1) → ℝ) ∈ Metric.ball p r} with hUdef
      have hUopen : IsOpen U := isOpen_preimage_snoc (p (Fin.last m)) Metric.isOpen_ball
      have hUp : Fin.init p ∈ U := by
        rw [hUdef]
        show (Fin.snoc (Fin.init p) (p (Fin.last m)) : Fin (m+1) → ℝ) ∈ Metric.ball p r
        rw [Fin.snoc_init_self]
        exact Metric.mem_ball_self hr
      have hUsub : U ⊆ ⋃₀ (T'' : Set (Set (Fin m → ℝ))) := by
        intro u hu
        rw [hUdef] at hu
        have hzT : (Fin.snoc u (p (Fin.last m)) : Fin (m+1) → ℝ) ∈
            ⋃₀ (T : Set (Set (Fin (m+1) → ℝ))) := hball hu
        obtain ⟨κ, hκT, hzκ⟩ := Set.mem_sUnion.mp hzT
        have hmem' : Fin.init '' κ ∈ T' := Finset.mem_image.mpr ⟨κ, hκT, rfl⟩
        have hint : (Fin.init '' κ ∩ (Fin.init '' Metric.ball p r)).Nonempty := by
          refine ⟨u, ?_, ?_⟩
          · exact ⟨Fin.snoc u (p (Fin.last m)), hzκ, Fin.init_snoc _ _⟩
          · exact ⟨Fin.snoc u (p (Fin.last m)), hu, Fin.init_snoc _ _⟩
        have hmem : Fin.init '' κ ∈ T'' := by
          rw [hT''def]; exact Finset.mem_filter.mpr ⟨hmem', hint⟩
        exact Set.mem_sUnion.mpr ⟨Fin.init '' κ, hmem,
          ⟨Fin.snoc u (p (Fin.last m)), hzκ, Fin.init_snoc _ _⟩⟩
      exact ⟨Fin.init p, interior_maximal hUsub hUopen hUp⟩
    obtain ⟨σ, hσT'', hσne⟩ := ih C' hc4' T'' hT''sub hne''
    have hσT' : σ ∈ T' := by
      rw [hT''def] at hσT''
      exact Finset.mem_of_mem_filter σ hσT''
    have hσint : (σ ∩ (Fin.init '' Metric.ball p r)).Nonempty := by
      rw [hT''def] at hσT''
      exact (Finset.mem_filter.mp hσT'').2
    obtain ⟨u, huσ, huW⟩ := hσint
    obtain ⟨z, hzball, hzu⟩ := huW
    have hzσ' : Fin.init z ∈ σ := by rw [hzu]; exact huσ
    by_contra hcon
    have hall : ∀ κ ∈ T, interior κ = ∅ := fun κ hκ =>
      Set.not_nonempty_iff_eq_empty.mp (fun hh => hcon ⟨κ, hκ, hh⟩)
    set F : Set (Fin (m+1) → ℝ) := {y | Fin.init y = Fin.init z ∧ y ∈ Metric.ball p r}
      with hFdef
    have hFinf : F.Infinite := ball_fiber_infinite hr hzball
    have hFinκ : ∀ κ ∈ T, (F ∩ κ).Finite := by
      intro κ hκ
      by_cases hpr : Fin.init '' κ = σ
      · have hcell : WilkiesDesign.IsCell (m+1) κ := isCell_of_mem_cylDecomp hC (hT hκ)
        rcases cell_cases hcell with ⟨τ, f, hf, hiff⟩ | ⟨τ, a', b', ha', hb', hab', hiff⟩
        · refine (Set.finite_singleton
            (Fin.snoc (Fin.init z) (f (Fin.init z)) : Fin (m+1) → ℝ)).subset ?_
          rintro y ⟨hyF, hyκ⟩
          rw [Set.mem_singleton_iff]
          obtain ⟨-, hy2⟩ := (hiff y).mp hyκ
          rw [hyF.1] at hy2
          conv_lhs => rw [← Fin.snoc_init_self y]
          rw [hyF.1, hy2]
        · have hτκ : τ = Fin.init '' κ := by
            refine Set.Subset.antisymm ?_ ?_
            · intro c hc
              obtain ⟨t, ht1, ht2⟩ := EReal.lt_iff_exists_real_btwn.mp (hab' c hc)
              exact ⟨Fin.snoc c t, (hiff (Fin.snoc c t)).mpr
                ⟨by rw [Fin.init_snoc]; exact hc,
                 by rw [Fin.init_snoc, Fin.snoc_last]; exact ht1,
                 by rw [Fin.init_snoc, Fin.snoc_last]; exact ht2⟩,
                Fin.init_snoc _ _⟩
            · rintro y ⟨w, hwκ, hwy⟩
              rw [← hwy]
              exact ((hiff w).mp hwκ).1
          have hτσ : τ = σ := by rw [hτκ, hpr]
          have hτne : (interior τ).Nonempty := by rw [hτσ]; exact hσne
          have hbne := interior_band_nonempty ha' hb' hab' hτne
          have hκeq : {z : Fin (m+1) → ℝ | Fin.init z ∈ τ ∧
              a' (Fin.init z) < ((z (Fin.last m) : ℝ) : EReal) ∧
              ((z (Fin.last m) : ℝ) : EReal) < b' (Fin.init z)} = κ :=
            Set.ext (fun z => (hiff z).symm)
          rw [hκeq] at hbne
          exact absurd hbne (by rw [hall κ hκ]; exact Set.not_nonempty_empty)
      · have hempty : F ∩ κ = ∅ := by
          rw [← Set.not_nonempty_iff_eq_empty]
          rintro ⟨y, hyF, hyκ⟩
          have hmem1 : Fin.init '' κ ∈ C' := by
            rw [hC'def]; exact Finset.mem_image.mpr ⟨κ, hT hκ, rfl⟩
          have hmem2 : σ ∈ C' := hT'sub hσT'
          have hx1 : Fin.init z ∈ Fin.init '' κ := ⟨y, hyκ, by rw [hyF.1]⟩
          exact hpr ((Set.pairwiseDisjoint_iff.mp (pairwiseDisjoint_of_cylDecomp hc4'))
            hmem1 hmem2 ⟨Fin.init z, hx1, hzσ'⟩)
        rw [hempty]; exact Set.finite_empty
    have hFfin : F.Finite := by
      have hsub : F ⊆ ⋃₀ (T : Set (Set (Fin (m+1) → ℝ))) := fun y hy => hball hy.2
      have hEq : F = ⋃₀ ((fun κ => F ∩ κ) '' (T : Set (Set (Fin (m+1) → ℝ)))) := by
        ext y; constructor
        · intro hy
          obtain ⟨κ, hκT, hyκ⟩ := Set.mem_sUnion.mp (hsub hy)
          exact ⟨F ∩ κ, ⟨κ, hκT, rfl⟩, hy, hyκ⟩
        · rintro ⟨s, ⟨κ, hκT, rfl⟩, hyF, -⟩
          exact hyF
      rw [hEq]
      exact Set.Finite.sUnion (Set.Finite.image (fun κ => F ∩ κ) T.finite_toSet)
        (by rintro s ⟨κ, hκT, rfl⟩; exact hFinκ κ hκT)
    exact hFinf hFfin

/-- A finite union of thin cells of a cylindrical decomposition is thin. -/
theorem sUnion_thin {m : ℕ} {C : Finset (Set (Fin m → ℝ))}
    (hC : WilkiesDesign.IsCylDecomp m C) (T : Finset (Set (Fin m → ℝ))) (hT : T ⊆ C)
    (hthin : ∀ κ ∈ T, interior κ = ∅) :
    interior (⋃₀ (T : Set (Set (Fin m → ℝ)))) = ∅ := by
  by_contra h
  have hne : (interior (⋃₀ (T : Set (Set (Fin m → ℝ))))).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr h
  obtain ⟨κ, hκT, hκne⟩ := exists_thick_cell m C hC T hT hne
  exact absurd hκne (by rw [hthin κ hκT]; exact Set.not_nonempty_empty)

end Helpers

theorem thin_union {S : WilkiesDesign.SOMin} (hcd : S.SharpCD) {n : ℕ} (k : ℕ) (a : ℕ)
    (b : Polynomial ℕ) (D : ℕ) (A : Fin k → Set (Fin n → ℝ))
    (hA : ∀ i, A i ∈ S.Ω a (b.eval D) n) (hint : ∀ i, interior (A i) = ∅) :
    interior (⋃ i, A i) = ∅ := by
  classical
  obtain ⟨a', b', c', H⟩ := hcd a n
  obtain ⟨C, hC, hcomp, -, -⟩ := H (b.eval D) k A hA
  set T : Finset (Set (Fin n → ℝ)) := C.filter (fun κ => ∃ i, κ ⊆ A i) with hT
  have hthin : ∀ κ ∈ T, interior κ = ∅ := by
    intro κ hκ
    rw [hT] at hκ
    obtain ⟨-, ⟨i, hi⟩⟩ := Finset.mem_filter.mp hκ
    refine Set.subset_empty_iff.mp ?_
    calc interior κ ⊆ interior (A i) := interior_mono hi
      _ = ∅ := hint i
  have hsUnion : ⋃₀ (T : Set (Set (Fin n → ℝ))) = ⋃ i, A i := by
    ext x; constructor
    · intro hx
      obtain ⟨κ, hκT, hxκ⟩ := Set.mem_sUnion.mp hx
      rw [hT] at hκT
      obtain ⟨-, ⟨i, hi⟩⟩ := Finset.mem_filter.mp hκT
      exact Set.mem_iUnion.mpr ⟨i, hi hxκ⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨κ, hκC, hxκ⟩ := exists_mem_of_cylDecomp hC x
      have hsub : κ ⊆ A i := by
        rcases hcomp i κ hκC with h | h
        · exact h
        · exact absurd h (Set.not_disjoint_iff.mpr ⟨x, hxκ, hxi⟩)
      exact Set.mem_sUnion.mpr ⟨κ, by
        rw [hT]; exact Finset.mem_filter.mpr ⟨hκC, ⟨i, hsub⟩⟩, hxκ⟩
  rw [← hsUnion]
  exact sUnion_thin hC T (Finset.filter_subset _ _) hthin

end Work.WilG1.Cell
