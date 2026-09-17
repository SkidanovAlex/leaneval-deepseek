import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Push-forward of a product measure under `Fin.snoc`

This file proves `Commons.MeasureTheory.Measure.map_fin_snoc_skew`, together with two
reusable auxiliary lemmas:

* `map_prod_dep`: for independent random variables `ω ~ m` and `q ~ ν` and a
  *dependent* map `g ω q`, if the conditional law `ν.map (g ω)` is the same
  measure `μ` for every `ω`, then the push-forward of `m.prod ν` under
  `(ω, q) ↦ (T ω, g ω q)` is `(m.map T).prod μ`.

* `map_fin_snoc_prod_pi`: the map `p ↦ Fin.snoc p.1 p.2` sends the product of
  `Measure.pi (fun _ : Fin n => μ)` and `μ` to `Measure.pi (fun _ : Fin (n+1) => μ)`.

Combining these two facts with a swap of the two coordinates yields the target
statement.
-/

set_option linter.style.haveILetI false

open MeasureTheory

namespace Commons.MeasureTheory.Measure

/-- `Fin.snoc` is measurable as a function of the initial vector and the last entry. -/
lemma measurable_fin_snoc_const {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (fun p : (Fin n → α) × α => @Fin.snoc n (fun _ => α) p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst
  · simp only [Fin.snoc_last]
    exact measurable_snd

/-- `Fin.snoc` identifies the product of the `n`-fold product measure with `μ`
with the `(n+1)`-fold product measure. -/
lemma map_fin_snoc_prod_pi {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    [SigmaFinite μ] (n : ℕ) :
    MeasureTheory.Measure.map (fun p : (Fin n → α) × α => @Fin.snoc n (fun _ => α) p.1 p.2)
        ((MeasureTheory.Measure.pi (fun _ : Fin n => μ)).prod μ)
      = MeasureTheory.Measure.pi (fun _ : Fin (n + 1) => μ) := by
  refine (MeasureTheory.Measure.pi_eq (μ := fun _ : Fin (n + 1) => μ) ?_).symm
  intro s hs
  rw [MeasureTheory.Measure.map_apply (measurable_fin_snoc_const n)
        (MeasurableSet.pi Set.countable_univ (fun i _ => hs i))]
  have hset : (fun p : (Fin n → α) × α => @Fin.snoc n (fun _ => α) p.1 p.2) ⁻¹'
        (Set.pi Set.univ s)
      = (Set.pi Set.univ (fun j : Fin n => s j.castSucc)) ×ˢ (s (Fin.last n)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      exact ⟨fun j => by simpa only [Fin.snoc_castSucc] using h j.castSucc,
             by simpa only [Fin.snoc_last] using h (Fin.last n)⟩
    · rintro ⟨h1, h2⟩ i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa only [Fin.snoc_castSucc] using h1 j
      · simpa only [Fin.snoc_last] using h2
  rw [hset, MeasureTheory.Measure.prod_prod, Fin.prod_univ_castSucc, MeasureTheory.Measure.pi_pi]

/-- Push-forward of a product measure under a map whose second component depends on
both coordinates, while its conditional law is constant. -/
lemma map_prod_dep {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    {m : MeasureTheory.Measure Ω} {ν : MeasureTheory.Measure X} [SFinite m] [SFinite ν]
    (T : Ω → Y) (g : Ω → X → Z) (hT : Measurable T)
    (hg : Measurable fun p : Ω × X => g p.1 p.2)
    {μ : MeasureTheory.Measure Z} [SigmaFinite μ] [SigmaFinite (m.map T)]
    (hgmap : ∀ ω, ν.map (g ω) = μ) :
    MeasureTheory.Measure.map (fun p : Ω × X => (T p.1, g p.1 p.2)) (m.prod ν)
      = (m.map T).prod μ := by
  refine (MeasureTheory.Measure.prod_eq ?_).symm
  intro s t hs ht
  have hH : Measurable fun p : Ω × X => (T p.1, g p.1 p.2) :=
    Measurable.prod (hT.comp measurable_fst) hg
  rw [MeasureTheory.Measure.map_apply hH (hs.prod ht)]
  have hmeas : MeasurableSet {p : Ω × X | T p.1 ∈ s ∧ g p.1 p.2 ∈ t} := by
    measurability
  have hset : (fun p : Ω × X => (T p.1, g p.1 p.2)) ⁻¹' (s ×ˢ t)
      = {p : Ω × X | T p.1 ∈ s ∧ g p.1 p.2 ∈ t} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq]
  rw [hset, MeasureTheory.Measure.prod_apply hmeas]
  have hinner : ∀ ω : Ω, ν (Prod.mk ω ⁻¹' {p : Ω × X | T p.1 ∈ s ∧ g p.1 p.2 ∈ t})
      = (T ⁻¹' s).indicator (fun _ => μ t) ω := by
    intro ω
    by_cases hω : ω ∈ T ⁻¹' s
    · rw [Set.indicator_of_mem hω]
      have hset2 : Prod.mk ω ⁻¹' {p : Ω × X | T p.1 ∈ s ∧ g p.1 p.2 ∈ t} = (g ω) ⁻¹' t := by
        ext q
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩
      have hgω : Measurable (g ω) := by measurability
      rw [hset2, ← MeasureTheory.Measure.map_apply hgω ht, hgmap ω]
    · rw [Set.indicator_of_notMem hω]
      have hset2 : Prod.mk ω ⁻¹' {p : Ω × X | T p.1 ∈ s ∧ g p.1 p.2 ∈ t} = ∅ := by
        ext q
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
        exact ⟨fun h => hω h.1, False.elim⟩
      rw [hset2, measure_empty]
  simp_rw [hinner]
  rw [lintegral_indicator_const (hs.preimage hT) (μ t), mul_comm,
      ← MeasureTheory.Measure.map_apply hT hs]

theorem map_fin_snoc_skew {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure (α × α)} {m : MeasureTheory.Measure Ω}
    [MeasureTheory.SigmaFinite μ] [MeasureTheory.SigmaFinite ν] [MeasureTheory.SigmaFinite m]
    (n : ℕ) (T : Ω → Fin n → α) (g : Ω → α × α → α)
    (hT : Measurable T) (hg : Measurable fun p : Ω × (α × α) => g p.1 p.2)
    (hTmap : m.map T = MeasureTheory.Measure.pi (fun _ : Fin n => μ))
    (hgmap : ∀ ω, ν.map (g ω) = μ) :
    (ν.prod m).map (fun p : (α × α) × Ω =>
        @Fin.snoc n (fun _ => α) (T p.2) (g p.2 p.1))
      = MeasureTheory.Measure.pi (fun _ : Fin (n + 1) => μ) := by
  haveI hmT : SigmaFinite (m.map T) := by rw [hTmap]; infer_instance
  set H : Ω × (α × α) → (Fin n → α) × α := fun p => (T p.1, g p.1 p.2) with hH
  have hHmeas : Measurable H := by
    rw [hH]; exact Measurable.prod (hT.comp measurable_fst) hg
  set G : Ω × (α × α) → (Fin (n + 1) → α) :=
    fun p => @Fin.snoc n (fun _ => α) (T p.1) (g p.1 p.2) with hG
  have hGmeas : Measurable G := by
    rw [hG, measurable_pi_iff]
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact (measurable_pi_apply j).comp (hT.comp measurable_fst)
    · simp only [Fin.snoc_last]
      exact hg
  have hcomp : (fun p : (α × α) × Ω => @Fin.snoc n (fun _ => α) (T p.2) (g p.2 p.1))
      = G ∘ Prod.swap := by
    rw [hG]; funext p; rfl
  have e1 : MeasureTheory.Measure.map
        (fun p : (α × α) × Ω => @Fin.snoc n (fun _ => α) (T p.2) (g p.2 p.1)) (ν.prod m)
      = MeasureTheory.Measure.map G (m.prod ν) := by
    rw [hcomp, ← MeasureTheory.Measure.map_map hGmeas measurable_swap,
        MeasureTheory.Measure.prod_swap]
  have e2 : MeasureTheory.Measure.map G (m.prod ν)
      = MeasureTheory.Measure.pi (fun _ : Fin (n + 1) => μ) := by
    have hGH : G = (fun p : (Fin n → α) × α => @Fin.snoc n (fun _ => α) p.1 p.2) ∘ H := by
      rw [hG, hH]; funext p; rfl
    rw [hGH, ← MeasureTheory.Measure.map_map (measurable_fin_snoc_const n) hHmeas, hH,
        map_prod_dep T g hT hg hgmap, hTmap]
    exact map_fin_snoc_prod_pi μ n
  rw [e1, e2]

end Commons.MeasureTheory.Measure