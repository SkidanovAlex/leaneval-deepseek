import Mathlib
import Submission.Work.LT.Defs

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/LT/DESIGN.md first (the orchestrator's design; your lemma is one node of its DAG). Shared definitions: Submission/Work/LT/Defs.lean (namespace Work.LT) — do NOT edit it; if you need a new shared definition, put it in your own file. Siblings are being proved in parallel; import them when they land.

# ltc_of_tests — guidance

**Goal.** Glue from "uniform family of local tests on an arbitrary coordinate type `X`" to the
challenge's `LTC q κ` structure on `Fin n` (after `transportCode e C`). Pure bookkeeping, no
coding theory.

**Construction.**
* Coordinates: `Sfin t : Finset (Fin n) := (S t).map e.toEmbedding`; `(Sfin t : Set _).ncard ≤ q`
  (`Set.ncard_coe_finset`, `Finset.card_map`).
* `prob := (PMF.uniformOfFintype T).map (fun t => ⟨↑(Sfin t), _⟩ : T → cardLE n q)`
  (`Mathlib.Probability.ProbabilityMassFunction.Constructions`).
* `views S := {v | ∀ t, (↑(Sfin t) : Set (Fin n)) = S.val → ∀ g : X → ZMod 2,
   (∀ x ∈ S t, g x = v ⟨e x, _⟩) → P t g}`. Different `t` may give the same set; quantifying
   over all of them is what makes `views` a function of `S` alone.
* `cond1`: `f ∈ transportCode e C` means `f ∘ e ∈ C`; then `hloc` + `hC`.
* `cond2`: if `¬ P t (f ∘ e)` then `f|_{Sfin t} ∉ views (Sfin t)` (take `g := f ∘ e`). So the
  rejection event contains the image of `{t | ¬P t (f∘e)}`, whose mass is `≥ #/|T|`.
  Use `PMF.toOuterMeasure_apply_le_toMeasure_apply` (or `toMeasure_apply_fintype` if the
  `MeasurableSpace (cardLE n q)` instance is discrete — it is `Subtype`/`Set.instMeasurableSpace`,
  check with `#synth MeasurableSingletonClass`), and `PMF.toOuterMeasure_map_apply`.
* Distance: `distanceFrom (transportCode e C) f ≤ hammingDist (f ∘ e) c`, witness `c ∘ e.symm`;
  `hammingDist f g = hammingNorm (f - g)` (`hammingDist_eq_hammingNorm`), and precomposition
  with `e` preserves `hammingNorm` (`Finset.card_map`/`Fintype.card_congr`).
* Casts: goal lives in `ℝ≥0∞`; move through `ENNReal.ofReal`/`ENNReal.coe_*`.

Expected size: 150–300 lines.
-/

namespace Work.LT

open GoodLTC NNReal Classical
open scoped ENNReal

/-- Precomposing a Hamming distance with an equivalence of the index types does not change it. -/
lemma hammingDist_equiv_comp {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (u v : β → ZMod 2) :
    hammingDist (fun x => u (e x)) (fun x => v (e x)) = hammingDist u v := by
  rw [hammingDist, hammingDist]
  rw [← Finset.card_map (s := Finset.univ.filter (fun x => u (e x) ≠ v (e x)))
    (f := e.toEmbedding)]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro hy
    exact ⟨e.symm y, by simpa [Equiv.apply_symm_apply] using hy, e.apply_symm_apply y⟩

/-- Over `𝔽₂` the Hamming distance to `c` is the Hamming weight of `f - c`. -/
lemma hammingDist_sub_eq {n : ℕ} (f c : Fin n → ZMod 2) :
    hammingDist f c = hammingNorm (f - c) := by
  rw [hammingDist_eq_hammingNorm]
  congr 1
  ext i
  simp [sub_eq_add_neg, CharTwo.neg_eq]

/-- A codeword witnesses an upper bound on the distance from a word to the code. -/
lemma distanceFrom_le_hammingDist {n : ℕ} (C : BinaryCode n) (f : Fin n → ZMod 2)
    {c : Fin n → ZMod 2} (hc : c ∈ C) : distanceFrom C f ≤ hammingDist f c := by
  apply Nat.sInf_le
  exact ⟨c, hc, (hammingDist_sub_eq f c).symm⟩

/-- **Bridge to the challenge's `LTC`.** A code on a finite coordinate type `X`, together with a
finite, uniformly weighted family of tests `t : T`, each reading at most `q` coordinates `S t` and
accepting via a predicate `P t` that only depends on those coordinates, such that codewords pass
every test and every word `f` has a codeword `c` with
`κ · dist(f,c)/n ≤ (fraction of tests rejecting f)`, yields a `κ`-locally testable code with `q`
queries after transport to `Fin n`. -/
theorem ltc_of_tests {X T : Type} [Fintype X] [Fintype T] [Nonempty T] {n : ℕ} (e : X ≃ Fin n)
    (C : Submodule (ZMod 2) (X → ZMod 2)) (q : ℕ) (κ : ℝ≥0) (S : T → Finset X)
    (hS : ∀ t, (S t).card ≤ q) (P : T → (X → ZMod 2) → Prop)
    (hloc : ∀ t (f g : X → ZMod 2), (∀ x ∈ S t, f x = g x) → P t f → P t g)
    (hC : ∀ f ∈ C, ∀ t, P t f)
    (hsound : ∀ f : X → ZMod 2, ∃ c ∈ C,
      (κ : ℝ) * ((hammingDist f c : ℝ) / n) ≤
        ((Finset.univ.filter (fun t => ¬ P t f)).card : ℝ) / Fintype.card T) :
    Nonempty (LTC q κ (transportCode e C)) := by
  classical
  -- The test sets, transported to `Fin n`.
  let Sfin : T → Finset (Fin n) := fun t => (S t).map e.toEmbedding
  have hSfin_card : ∀ t, (Sfin t).card ≤ q := by intro t; simpa [Sfin] using hS t
  have hSfin_ncard : ∀ t, ((Sfin t : Set (Fin n))).ncard ≤ q := by
    intro t; rw [Set.ncard_coe_finset]; exact hSfin_card t
  let F : T → cardLE n q := fun t => ⟨(Sfin t : Set (Fin n)), hSfin_ncard t⟩
  -- The allowed views at a set `Sm`: a view is allowed when *every* test whose support is `Sm`
  -- accepts every word inducing it.
  let views : (Sm : cardLE n q) → Set (Sm.val → ZMod 2) := fun Sm =>
    {v | ∀ (t : T) (ht : (Sfin t : Set (Fin n)) = Sm.val) (g : X → ZMod 2),
      (∀ (x : X) (hx : x ∈ S t),
        g x = v ⟨e x, by rw [← ht]; exact Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩) → P t g}
  refine ⟨⟨(PMF.uniformOfFintype T).map F, views, ?_, ?_⟩⟩
  · -- Codewords pass every test.
    intro f hf Sm
    simp only [views, Set.mem_ofPred_eq]
    intro t ht g hg
    have hfC : (fun x => f (e x)) ∈ C := by
      have h := hf
      rw [transportCode, Submodule.mem_comap] at h
      exact h
    refine hloc t (fun x => f (e x)) g (fun x hx => (hg x hx).symm) (hC _ hfC t)
  · -- Soundness: the rejection probability is at least `#rejecting tests / |T|`.
    intro f
    let g : X → ZMod 2 := fun x => f (e x)
    let R : Finset T := Finset.univ.filter (fun t => ¬ P t g)
    let reject : Set (cardLE n q) := {Sm : cardLE n q | Set.domRestrict Sm f ∉ views Sm}
    show ((PMF.uniformOfFintype T).map F).toMeasure reject ≥
      κ * normalisedDistanceFrom (transportCode e C) f
    obtain ⟨c, hcC, hc⟩ := hsound g
    let c' : Fin n → ZMod 2 := fun i => c (e.symm i)
    have hc'C : c' ∈ transportCode e C := by
      rw [transportCode, Submodule.mem_comap]
      change (fun x => c' (e x)) ∈ C
      have h3 : (fun x => c' (e x)) = c := by ext x; simp [c']
      rw [h3]; exact hcC
    -- Distance to the code vs. distance to the witnessing codeword, reindexed along `e`.
    have hhc : hammingDist f c' = hammingDist g c := by
      have h2 := hammingDist_equiv_comp e f c'
      have h3 : (fun x => c' (e x)) = c := by ext x; simp [c']
      rw [h3] at h2
      exact h2.symm
    have hdist : (distanceFrom (transportCode e C) f : ℝ) / n ≤ (hammingDist g c : ℝ) / n := by
      have h := distanceFrom_le_hammingDist (transportCode e C) f hc'C
      rw [hhc] at h
      exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
    have hreal : (κ : ℝ) * ((distanceFrom (transportCode e C) f : ℝ) / n) ≤
        ((R.card : ℝ) / (Fintype.card T : ℝ)) :=
      le_trans (mul_le_mul_of_nonneg_left hdist (by positivity)) hc
    -- Every rejecting test is rejected by its own (transported) set.
    have hsub : R ⊆ Finset.univ.filter (fun t => F t ∈ reject) := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, R, reject,
        Set.mem_ofPred_eq] at ht ⊢
      intro hmem
      exact ht (hmem t rfl g (fun x hx => rfl))
    have hcardle : R.card ≤ Fintype.card ↥(F ⁻¹' reject) := by
      rw [← Fintype.card_coe R]
      have hinj : ∀ t : ↥R, F t.1 ∈ reject := by
        intro t
        have hh := hsub t.2
        simpa [Finset.mem_coe, Finset.mem_filter] using hh
      refine Fintype.card_le_of_injective
        (fun (t : ↥R) => (⟨t.1, hinj t⟩ : ↥(F ⁻¹' reject))) ?_
      intro a b hab
      have h : (a : T) = (b : T) := congrArg (fun x : ↥(F ⁻¹' reject) => (x : T)) hab
      exact Subtype.ext h
    have hmono : (R.card : ℝ≥0∞) / (Fintype.card T : ℝ≥0∞) ≤
        (PMF.uniformOfFintype T).toOuterMeasure (F ⁻¹' reject) := by
      rw [PMF.toOuterMeasure_uniformOfFintype_apply]
      exact ENNReal.div_le_div_right (Nat.cast_le.mpr hcardle) _
    have hnd : (normalisedDistanceFrom (transportCode e C) f : ℝ) =
        (distanceFrom (transportCode e C) f : ℝ) / n := by
      rw [normalisedDistanceFrom]
      rfl
    have hL : ((κ : ℝ≥0) : ℝ≥0∞) * (normalisedDistanceFrom (transportCode e C) f : ℝ≥0∞)
        = ENNReal.ofReal ((κ : ℝ) * ((distanceFrom (transportCode e C) f : ℝ) / n)) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := κ),
          ← ENNReal.ofReal_coe_nnreal (p := normalisedDistanceFrom (transportCode e C) f),
          hnd, ENNReal.ofReal_mul (by positivity)]
    have hR : (R.card : ℝ≥0∞) / (Fintype.card T : ℝ≥0∞)
        = ENNReal.ofReal ((R.card : ℝ) / (Fintype.card T : ℝ)) := by
      have h1 : (R.card : ℝ≥0∞) = ENNReal.ofReal (R.card : ℝ) :=
        (ENNReal.ofReal_natCast _).symm
      have h2 : (Fintype.card T : ℝ≥0∞) = ENNReal.ofReal (Fintype.card T : ℝ) :=
        (ENNReal.ofReal_natCast _).symm
      rw [h1, h2, ENNReal.ofReal_div_of_pos (by exact_mod_cast Fintype.card_pos (α := T))]
    have hle : ((κ : ℝ≥0) : ℝ≥0∞) * (normalisedDistanceFrom (transportCode e C) f : ℝ≥0∞) ≤
        (R.card : ℝ≥0∞) / (Fintype.card T : ℝ≥0∞) := by
      rw [hL, hR]
      exact ENNReal.ofReal_le_ofReal hreal
    calc ((κ : ℝ≥0) : ℝ≥0∞) * (normalisedDistanceFrom (transportCode e C) f : ℝ≥0∞)
        ≤ (R.card : ℝ≥0∞) / (Fintype.card T : ℝ≥0∞) := hle
      _ ≤ (PMF.uniformOfFintype T).toOuterMeasure (F ⁻¹' reject) := hmono
      _ = ((PMF.uniformOfFintype T).map F).toOuterMeasure reject :=
            (PMF.toOuterMeasure_map_apply F (PMF.uniformOfFintype T) reject).symm
      _ ≤ ((PMF.uniformOfFintype T).map F).toMeasure reject :=
            PMF.toOuterMeasure_apply_le_toMeasure_apply _ _

end Work.LT
