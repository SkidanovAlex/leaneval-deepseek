import Mathlib
import Submission.Work.Geo.Prism.Defs
import Submission.Work.PL.Defs

namespace Work.Geo.Prism.Convex

open Set
open Work.Geo.Prism
open scoped Classical

/-!
# `prism_convex_piece`

The piece `{p | p.1 ∈ j ∧ γ₀ p.1 ≤ p.2 ≤ γ₁ p.1}` for convex compact `j` of dimension `≤ d`,
a convex PL floor `γ₀` and a concave PL top `γ₁`, is convex and has `DomDim₂ ≤ d + 1`.

This file proves the statement together with the small combinatorial-geometric lemmas it
needs:

* `convexHull_prismFinset` : the convex hull of the finite set `{(v,a),(v,b) | v ∈ s}` is
  `conv(s) × [a,b]`.
* `prismFinset_subset_affineSpan` : that finite set lies in the affine span of a set of
  `|s| + 1` points.
* `cover_of_subset_affineSpan` : Carathéodory, with the cardinality bound `dim + 1`.
* `mem_prismFinset_conv` : the sandwich estimate `min f s ≤ p.2 ≤ max g s`.
-/

/-- `{(v,a), (v,b) | v ∈ s}`, the vertices of the "prism" over the simplex on `s`. -/
noncomputable def prismFinset {n : ℕ} (s : Finset (PL.E n)) (a b : ℝ) : Finset (PL.E n × ℝ) :=
  s.image (fun v => (v, a)) ∪ s.image (fun v => (v, b))

/-- `{(v,a) | v ∈ s} ∪ {(v₀,b)}`, a set of at most `|s| + 1` points whose affine span contains
`prismFinset s a b`. -/
noncomputable def prismU {n : ℕ} (s : Finset (PL.E n)) (v₀ : PL.E n) (a b : ℝ) :
    Finset (PL.E n × ℝ) :=
  insert (v₀, b) (s.image (fun v => (v, a)))

/-- The finite cover of the piece over `j`, one family of simplices for each simplex of the
`DomDim` cover of `j`.  Empty for the empty simplex. -/
noncomputable def pieceCover {n : ℕ} (Sc : Finset (Finset (PL.E n)))
    (f g : PL.E n →ᵃ[ℝ] ℝ) : Finset (Finset (PL.E n × ℝ)) :=
  Sc.biUnion (fun s =>
    if hs : s.Nonempty then
      (prismFinset s (s.inf' hs (fun v => f v)) (s.sup' hs (fun v => g v))).powerset.filter
        (fun T => T.card ≤ s.card + 1)
    else ∅)

/-- `conv{(v,a),(v,b) | v ∈ s} = conv(s) × [a,b]` for `a ≤ b`. -/
theorem convexHull_prismFinset {n : ℕ} (s : Finset (PL.E n)) {a b : ℝ} (hab : a ≤ b) :
    convexHull ℝ (prismFinset s a b : Set (PL.E n × ℝ)) =
      (convexHull ℝ (s : Set (PL.E n))) ×ˢ (Icc a b) := by
  have hset : (prismFinset s a b : Set (PL.E n × ℝ)) =
      (s : Set (PL.E n)) ×ˢ ({a, b} : Set ℝ) := by
    ext p
    constructor
    · intro hp
      simp only [prismFinset, Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · exact ⟨hv, by simp⟩
      · exact ⟨hv, by simp⟩
    · rintro ⟨hv, hc⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      simp only [prismFinset, Finset.mem_coe, Finset.mem_union, Finset.mem_image]
      rcases hc with rfl | rfl
      · exact Or.inl ⟨p.1, hv, rfl⟩
      · exact Or.inr ⟨p.1, hv, rfl⟩
  rw [hset, convexHull_prod, convexHull_pair, segment_eq_Icc hab]

/-- `prismFinset s a b` is contained in the affine span of the `|s| + 1` points of `prismU`. -/
theorem prismFinset_subset_affineSpan {n : ℕ} (s : Finset (PL.E n)) {v₀ : PL.E n}
    (hv₀ : v₀ ∈ s) (a b : ℝ) :
    (prismFinset s a b : Set (PL.E n × ℝ)) ⊆
      affineSpan ℝ (prismU s v₀ a b : Set (PL.E n × ℝ)) := by
  intro p hp
  simp only [prismFinset, Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hp
  have hva : (v₀, a) ∈ (prismU s v₀ a b : Set (PL.E n × ℝ)) :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v₀, hv₀, rfl⟩)
  have hvb : (v₀, b) ∈ (prismU s v₀ a b : Set (PL.E n × ℝ)) := by
    rw [prismU]; exact Finset.mem_insert_self _ _
  rcases hp with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · refine subset_affineSpan ℝ _ ?_
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  · have hvU : (v, a) ∈ (prismU s v₀ a b : Set (PL.E n × ℝ)) :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    have := (affineSpan ℝ (prismU s v₀ a b : Set (PL.E n × ℝ))).smul_vsub_vadd_mem
      (1:ℝ) (subset_affineSpan ℝ _ hvU) (subset_affineSpan ℝ _ hva) (subset_affineSpan ℝ _ hvb)
    simpa using this

/-- Carathéodory with cardinality bound: if `V` lies in the affine span of `U` and
`|U| ≤ m`, then `conv V` is covered by the `conv T` for `T ⊆ V`, `|T| ≤ m`. -/
theorem cover_of_subset_affineSpan {n : ℕ} (V U : Finset (PL.E n × ℝ)) (m : ℕ)
    (hVU : (V : Set (PL.E n × ℝ)) ⊆ affineSpan ℝ (U : Set (PL.E n × ℝ))) (hm : U.card ≤ m) :
    convexHull ℝ (V : Set (PL.E n × ℝ)) ⊆
      ⋃ T ∈ (V.powerset.filter (fun T => T.card ≤ m)), convexHull ℝ (T : Set (PL.E n × ℝ)) := by
  intro x hx
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  obtain ⟨T, hTV, hTind, hxT⟩ := hx
  refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨?_, hxT⟩⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.coe_subset.mp hTV,
    le_trans (AffineIndependent.card_le_card_of_subset_affineSpan hTind
      (Subset.trans hTV hVU)) hm⟩

/-- The sandwich estimate: a point over the simplex on `s` between the graphs of the affine
functions `f` and `g` lies in `conv(s) × [min f s, max g s]`. -/
theorem mem_prismFinset_conv {n : ℕ} (s : Finset (PL.E n)) (hs : s.Nonempty)
    (f g : PL.E n →ᵃ[ℝ] ℝ) {p : PL.E n × ℝ} (h1 : p.1 ∈ PL.simp s)
    (h2 : f p.1 ≤ p.2) (h3 : p.2 ≤ g p.1) :
    p ∈ (convexHull ℝ (s : Set (PL.E n))) ×ˢ
      Icc (s.inf' hs (fun v => f v)) (s.sup' hs (fun v => g v)) := by
  have h1' : p.1 ∈ convexHull ℝ (s : Set (PL.E n)) := h1
  refine ⟨h1', ?_, ?_⟩
  · have hsub : (s : Set (PL.E n)) ⊆ f ⁻¹' (Ici (s.inf' hs (fun v => f v))) := by
      intro v hv
      exact Finset.inf'_le (fun v => f v) hv
    have hconv := (convex_Ici (s.inf' hs (fun v => f v))).affine_preimage f
    exact le_trans (convexHull_min hsub hconv h1') h2
  · have hsub : (s : Set (PL.E n)) ⊆ g ⁻¹' (Iic (s.sup' hs (fun v => g v))) := by
      intro v hv
      exact Finset.le_sup' (fun v => g v) hv
    have hconv := (convex_Iic (s.sup' hs (fun v => g v))).affine_preimage g
    exact le_trans h3 (convexHull_min hsub hconv h1')

/-- `p ↦ p.2 - f p.1`, the affine function whose nonnegativity is `f p.1 ≤ p.2`. -/
noncomputable def hs_aff {n : ℕ} (f : PL.E n →ᵃ[ℝ] ℝ) : PL.E n × ℝ →ᵃ[ℝ] ℝ :=
  (AffineMap.snd : PL.E n × ℝ →ᵃ[ℝ] ℝ) -ᵥ (f.comp (AffineMap.fst : PL.E n × ℝ →ᵃ[ℝ] PL.E n))

/-- `p ↦ f p.1 - p.2`, the affine function whose nonnegativity is `p.2 ≤ f p.1`. -/
noncomputable def hs_aff' {n : ℕ} (f : PL.E n →ᵃ[ℝ] ℝ) : PL.E n × ℝ →ᵃ[ℝ] ℝ :=
  (f.comp (AffineMap.fst : PL.E n × ℝ →ᵃ[ℝ] PL.E n)) -ᵥ (AffineMap.snd : PL.E n × ℝ →ᵃ[ℝ] ℝ)

theorem hs_aff_convex {n : ℕ} (f : PL.E n →ᵃ[ℝ] ℝ) :
    Convex ℝ {p : PL.E n × ℝ | f p.1 ≤ p.2} := by
  have h : Convex ℝ (hs_aff f ⁻¹' (Ici (0:ℝ))) := (convex_Ici (0:ℝ)).affine_preimage (hs_aff f)
  convert h using 1
  ext p
  simp [hs_aff, sub_nonneg]

theorem hs_aff'_convex {n : ℕ} (f : PL.E n →ᵃ[ℝ] ℝ) :
    Convex ℝ {p : PL.E n × ℝ | p.2 ≤ f p.1} := by
  have h : Convex ℝ (hs_aff' f ⁻¹' (Ici (0:ℝ))) := (convex_Ici (0:ℝ)).affine_preimage (hs_aff' f)
  convert h using 1
  ext p
  simp [hs_aff', sub_nonneg]

/-- Convexity half of the piece. -/
theorem convex_prism_piece {q : ℕ} (j : Set (PL.E q)) (hj : Convex ℝ j)
    {γ₀ γ₁ : PL.E q → ℝ} (h₀ : ConvexPL γ₀) (h₁ : ConcavePL γ₁) :
    Convex ℝ {p : PL.E q × ℝ | p.1 ∈ j ∧ γ₀ p.1 ≤ p.2 ∧ p.2 ≤ γ₁ p.1} := by
  obtain ⟨S₀, hS₀, hγ₀⟩ := h₀
  obtain ⟨S₁, hS₁, hγ₁⟩ := h₁
  have hset : {p : PL.E q × ℝ | p.1 ∈ j ∧ γ₀ p.1 ≤ p.2 ∧ p.2 ≤ γ₁ p.1}
      = ({p | p.1 ∈ j} ∩ (⋂ f ∈ S₀, {p | f p.1 ≤ p.2}) ∩
          (⋂ g ∈ S₁, {p | p.2 ≤ g p.1})) := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · intro f hf
        have : f p.1 ≤ γ₀ p.1 := by rw [hγ₀ p.1]; exact Finset.le_sup' (fun f => f p.1) hf
        exact le_trans this h2
      · intro g hg
        have : γ₁ p.1 ≤ g p.1 := by rw [hγ₁ p.1]; exact Finset.inf'_le (fun g => g p.1) hg
        exact le_trans h3 this
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · rw [hγ₀ p.1]; exact (Finset.sup'_le_iff _ _).mpr (fun f hf => h2 f hf)
      · rw [hγ₁ p.1]; exact (Finset.le_inf'_iff _ _).mpr (fun g hg => h3 g hg)
  rw [hset]
  refine Convex.inter (Convex.inter ?_ ?_) ?_
  · exact hj.linear_preimage (LinearMap.fst ℝ (PL.E q) ℝ)
  · exact convex_iInter (fun f => convex_iInter (fun _ => hs_aff_convex f))
  · exact convex_iInter (fun g => convex_iInter (fun _ => hs_aff'_convex g))

/-- The `prism_convex_piece` of blueprint §5 item A1.6: for convex compact `j` of "dimension ≤ d" (`PL.DomDim j d`), a convex PL floor `γ₀` (a pointwise maximum of finitely many affine functions) and a concave PL top `γ₁` (a pointwise minimum), the piece `{p | p.1 ∈ j ∧ γ₀ p.1 ≤ p.2 ≤ γ₁ p.1}` is convex, and `DomDim₂ (d+1)` (covered by finitely many simplices with at most `d+2` vertices).  Convexity: `j × univ` is convex and the set is the intersection of that with the closed half-spaces `{p | f_k p.1 ≤ p.2}` and `{p | p.2 ≤ g_l p.1}` for the finitely many affine functions with `γ₀ = max_k f_k`, `γ₁ = min_l g_l`.  For the `DomDim₂` bound: for each pair `(k,l)` the set `{p | p.1 ∈ j ∧ f_k p.1 ≤ p.2 ≤ g_l p.1}` is covered by `Q_i := {p | p.1 ∈ simp σ_i ∧ f_k p.1 ≤ p.2 ≤ g_l p.1}` over the finitely many simplices `PL.simp σ_i` covering `j` (so `|σ_i| ≤ d+1`); each `Q_i` is contained in `(simp σ_i) × [a,b]` where `a := min_{v ∈ σ_i} f_k v` and `b := max_{v ∈ σ_i} g_l v`, and `(simp σ_i) × [a,b] ⊆ convexHull ℝ V` for the finite vertex set `V := {(v,a) | v ∈ σ_i} ∪ {(v,b) | v ∈ σ_i}`; Carathéodory (`convexHull_eq_union`) inside the affine span of `V` (dimension at most `|σ_i| ≤ d+1`) covers `Q_i` by the `convexHull ℝ T` for the finitely many `T ⊆ V` with `|T| ≤ d+2` (`AffineIndependent.card_le_finrank_succ` bounds the cardinality).  Prefer this direct route over an affine-subspace argument: `finrank` of the affine hull of `j` does not follow immediately from the covering hypothesis `PL.DomDim j d`. -/
theorem prism_convex_piece {q : ℕ} (j : Set (PL.E q)) (d : ℤ) (hj : Convex ℝ j)
    (hjc : IsCompact j) (hjd : PL.DomDim j d) {γ₀ γ₁ : PL.E q → ℝ}
    (h₀ : Work.Geo.Prism.ConvexPL γ₀) (h₁ : Work.Geo.Prism.ConcavePL γ₁) :
    Convex ℝ {p : PL.E q × ℝ | p.1 ∈ j ∧ γ₀ p.1 ≤ p.2 ∧ p.2 ≤ γ₁ p.1} ∧
      Work.Geo.Prism.DomDim₂ {p : PL.E q × ℝ | p.1 ∈ j ∧ γ₀ p.1 ≤ p.2 ∧ p.2 ≤ γ₁ p.1}
        (d + 1) := by
  refine ⟨convex_prism_piece j hj h₀ h₁, ?_⟩
  obtain ⟨S₀, hS₀, hγ₀⟩ := h₀
  obtain ⟨S₁, hS₁, hγ₁⟩ := h₁
  obtain ⟨Sc, hScard, hScov⟩ := hjd
  obtain ⟨f₀, hf₀⟩ := hS₀
  obtain ⟨g₀, hg₀⟩ := hS₁
  refine ⟨pieceCover Sc f₀ g₀, ?_, ?_⟩
  · intro T hT
    rw [pieceCover, Finset.mem_biUnion] at hT
    obtain ⟨s, hsS, hT'⟩ := hT
    by_cases hs : s.Nonempty
    · rw [dite_eq_left hs, Finset.mem_filter] at hT'
      have h1 : (T.card : ℤ) ≤ (s.card : ℤ) + 1 := by exact_mod_cast hT'.2
      have h2 := hScard s hsS
      linarith
    · rw [dite_eq_right hs] at hT'
      simp at hT'
  · intro p hp
    obtain ⟨hpj, hp0, hp1⟩ := hp
    have hfp : f₀ p.1 ≤ p.2 := by
      have : f₀ p.1 ≤ γ₀ p.1 := by rw [hγ₀ p.1]; exact Finset.le_sup' (fun f => f p.1) hf₀
      linarith
    have hgp : p.2 ≤ g₀ p.1 := by
      have : γ₁ p.1 ≤ g₀ p.1 := by rw [hγ₁ p.1]; exact Finset.inf'_le (fun g => g p.1) hg₀
      linarith
    have hpj' : p.1 ∈ ⋃ s ∈ Sc, PL.simp s := hScov hpj
    simp only [Set.mem_iUnion] at hpj'
    obtain ⟨s, hsS, hps⟩ := hpj'
    have hs : s.Nonempty := by
      rcases Finset.eq_empty_or_nonempty s with h0 | h
      · exfalso
        rw [h0] at hps
        simp [PL.simp] at hps
      · exact h
    obtain ⟨v₀, hv₀⟩ := hs.exists_mem
    have ha_le : s.inf' hs (fun v => f₀ v) ≤ f₀ p.1 := by
      have hsub : (s : Set (PL.E q)) ⊆ f₀ ⁻¹' (Ici (s.inf' hs (fun v => f₀ v))) := by
        intro v hv; exact Finset.inf'_le (fun v => f₀ v) hv
      exact convexHull_min hsub ((convex_Ici _).affine_preimage f₀) hps
    have hb_le : g₀ p.1 ≤ s.sup' hs (fun v => g₀ v) := by
      have hsub : (s : Set (PL.E q)) ⊆ g₀ ⁻¹' (Iic (s.sup' hs (fun v => g₀ v))) := by
        intro v hv; exact Finset.le_sup' (fun v => g₀ v) hv
      exact convexHull_min hsub ((convex_Iic _).affine_preimage g₀) hps
    have hab : s.inf' hs (fun v => f₀ v) ≤ s.sup' hs (fun v => g₀ v) := by linarith
    have hpconv : p ∈ convexHull ℝ
        (prismFinset s (s.inf' hs (fun v => f₀ v)) (s.sup' hs (fun v => g₀ v)) :
          Set (PL.E q × ℝ)) := by
      rw [convexHull_prismFinset s hab]
      exact mem_prismFinset_conv s hs f₀ g₀ hps hfp hgp
    have hUcard : (prismU s v₀ (s.inf' hs (fun v => f₀ v)) (s.sup' hs (fun v => g₀ v))).card
        ≤ s.card + 1 := by
      rw [prismU]
      exact le_trans (Finset.card_insert_le _ _) (Nat.add_le_add_right Finset.card_image_le 1)
    have hcov := cover_of_subset_affineSpan
      (prismFinset s (s.inf' hs (fun v => f₀ v)) (s.sup' hs (fun v => g₀ v)))
      (prismU s v₀ (s.inf' hs (fun v => f₀ v)) (s.sup' hs (fun v => g₀ v))) (s.card + 1)
      (prismFinset_subset_affineSpan s hv₀ _ _) hUcard
    have hcovp : p ∈ ⋃ T ∈ ((prismFinset s (s.inf' hs (fun v => f₀ v))
        (s.sup' hs (fun v => g₀ v))).powerset.filter (fun T => T.card ≤ s.card + 1)),
        convexHull ℝ (T : Set (PL.E q × ℝ)) := hcov hpconv
    simp only [Set.mem_iUnion] at hcovp
    obtain ⟨T, hTmem, hpT⟩ := hcovp
    refine Set.mem_iUnion.mpr ⟨T, Set.mem_iUnion.mpr ⟨?_, hpT⟩⟩
    rw [pieceCover, Finset.mem_biUnion]
    exact ⟨s, hsS, by rw [dite_eq_left hs]; exact hTmem⟩

end Work.Geo.Prism.Convex
