import Submission.WordSpan
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Submission.Commons.Data.List.finite_setOf_count_eq
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section

/-!
# Independence of the joint weight spaces of `M(ω₁+ω₈)`

The diagonal Serre generators `H₁, …, H₈` act on `Mω = M(ω₁+ω₈)` as a commuting family of
ℂ-linear operators (`h_smul_comm`, `commutator_HH` of `Submission.E8Weights`).  This file proves
the classical consequence: **vectors belonging to pairwise distinct joint weight spaces are
linearly independent**.

The proof is the standard "interpolation" argument.  If `y i ∈ W_{ν i}` for pairwise distinct
weights `ν i` and `∑ y i = 0`, fix `i₀` and for every other `i` pick a coordinate `j i` with
`ν i (j i) ≠ ν i₀ (j i)`.  The operator `T := ∏_{i ≠ i₀} (H_{j i} - ν i (j i))` annihilates every
`y i` with `i ≠ i₀` (one factor of the product does) and acts on `y i₀` by the non-zero scalar
`∏_{i ≠ i₀} (ν i₀ (j i) - ν i (j i))`; hence `y i₀ = 0`.
-/

open UniversalEnvelopingAlgebra

namespace Submission.WeightIndependence

open Submission.E8Weights
open Submission.WordSpan

/-- The ℂ-linear operator `x ↦ Hⱼ • x` on `Mω`. -/
def hEnd (j : Fin 8) : Module.End ℂ Mω where
  toFun := fun x => h j • x
  map_add' := by intro x y; rw [smul_add]
  map_smul' := by intro c x; exact h_smul_comm j c x

@[simp] lemma hEnd_apply (j : Fin 8) (x : Mω) : hEnd j x = h j • x := rfl

/-- On the weight-`μ` space, `Hⱼ` acts by the scalar `μ j`. -/
lemma hEnd_apply_of_mem (j : Fin 8) {μ : Fin 8 → ℂ} {x : Mω} (hx : x ∈ jointWeightSpace μ) :
    hEnd j x = μ j • x := hx j

/-- The "killer" operator `H_{p.1} - p.2`. -/
def killer (p : Fin 8 × ℂ) : Module.End ℂ Mω := hEnd p.1 - p.2 • (1 : Module.End ℂ Mω)

/-- A killer acts on a weight vector of weight `ν` by the scalar `ν p.1 - p.2`. -/
lemma killer_apply_of_mem (p : Fin 8 × ℂ) {ν : Fin 8 → ℂ} {x : Mω}
    (hx : x ∈ jointWeightSpace ν) : killer p x = (ν p.1 - p.2) • x := by
  simp only [killer, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    hEnd_apply_of_mem p.1 hx, sub_smul]

/-- A product of killers acts on a weight vector by the product of the corresponding scalars. -/
lemma list_prod_killer_apply (l : List (Fin 8 × ℂ)) {ν : Fin 8 → ℂ} {x : Mω}
    (hx : x ∈ jointWeightSpace ν) :
    (l.map killer).prod x = (l.map (fun p => ν p.1 - p.2)).prod • x := by
  induction l with
  | nil => simp
  | cons p t ih =>
      have hcx : (t.map (fun p => ν p.1 - p.2)).prod • x ∈ jointWeightSpace ν :=
        Submodule.smul_mem _ _ hx
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, ih,
        killer_apply_of_mem p hcx, smul_smul]

/-- **Linear independence of vectors in pairwise distinct joint weight spaces.** -/
theorem eq_zero_of_sum_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : ι → Fin 8 → ℂ)
    (hν : Function.Injective ν) (y : ι → Mω) (hy : ∀ i, y i ∈ jointWeightSpace (ν i))
    (hsum : ∑ i, y i = 0) : ∀ i, y i = 0 := by
  classical
  intro i₀
  -- for every index choose a coordinate which either is `i₀` or separates the two weights
  have hsep : ∀ i : ι, ∃ j : Fin 8, i = i₀ ∨ ν i j ≠ ν i₀ j := by
    intro i
    by_cases h : i = i₀
    · exact ⟨0, Or.inl h⟩
    · have hne : ν i ≠ ν i₀ := fun hν' => h (hν hν')
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      exact ⟨j, Or.inr hj⟩
  choose j hj using hsep
  -- the list of killers, one for each index `i ≠ i₀`
  let l : List (Fin 8 × ℂ) := (Finset.univ.erase i₀).toList.map (fun i => (j i, ν i (j i)))
  have hmem : ∀ i ∈ Finset.univ.erase i₀, (j i, ν i (j i)) ∈ l := by
    intro i hi
    exact List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩
  -- the product of killers annihilates every `y i` with `i ≠ i₀`
  have hzero : ∀ i ∈ Finset.univ.erase i₀, ((l.map killer).prod) (y i) = 0 := by
    intro i hi
    rw [list_prod_killer_apply l (hy i)]
    have hzero_mem : (0 : ℂ) ∈ l.map (fun p => ν i p.1 - p.2) := by
      refine List.mem_map.mpr ⟨(j i, ν i (j i)), hmem i hi, ?_⟩
      simp
    rw [List.prod_eq_zero hzero_mem, zero_smul]
  -- the same product acts on `y i₀` by a non-zero scalar
  have hscalar : (l.map (fun p => ν i₀ p.1 - p.2)).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    intro hmem0
    obtain ⟨p, hp, hp0⟩ := List.mem_map.mp hmem0
    -- `p` comes from some index `i ≠ i₀`, and the factor is non-zero by construction
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    rw [Finset.mem_toList] at hi
    have hne : ν i (j i) ≠ ν i₀ (j i) := (hj i).resolve_left (Finset.mem_erase.mp hi).1
    exact hne (sub_eq_zero.mp hp0).symm
  have hstep : ((l.map killer).prod) (y i₀)
      = (l.map (fun p => ν i₀ p.1 - p.2)).prod • y i₀ := list_prod_killer_apply l (hy i₀)
  -- evaluate the product on the vanishing sum
  have h1 : ((l.map killer).prod) (∑ i, y i) = ((l.map killer).prod) (y i₀) := by
    rw [map_sum]
    refine Finset.sum_eq_single i₀ ?_ ?_
    · intro i _ hi
      exact hzero i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  rw [hsum, map_zero] at h1
  rw [hstep] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left hscalar

section WeightDecomposition

/-- The weight (i.e. the functional on the Cartan) attached to a vector `m` of letter
multiplicities: `w ↦ ω₁+ω₈ - ∑ᵢ mᵢ αᵢ`, evaluated at `Hⱼ` it is `(ω₁+ω₈)ⱼ - ∑ᵢ mᵢ Aⱼᵢ`. -/
def wtVec (m : Fin 8 → ℕ) : Fin 8 → ℂ :=
  fun j => omegaOnePlusOmegaEight j - ∑ i : Fin 8, (m i : ℂ) * (CartanMatrix.E₈ j i : ℂ)

/-- A word determines its letter multiplicities from its weight: the weights `wtVec m` are
injective (the E₈ Cartan matrix is invertible over `ℂ`, `CartanMatrix.E₈_det`). -/
lemma wtVec_injective : Function.Injective wtVec := by
  intro m m' hmm
  have hmat : ∀ j : Fin 8, (∑ i : Fin 8, (m i : ℂ) * (CartanMatrix.E₈ j i : ℂ))
      = ∑ i : Fin 8, (m' i : ℂ) * (CartanMatrix.E₈ j i : ℂ) := by
    intro j
    have h := congrFun hmm j
    simp only [wtVec] at h
    exact sub_right_inj.mp h
  -- `∑ i, m i * A j i` is `(A *ᵥ m) j` by symmetry of the Cartan matrix
  have hmv : (RingHom.mapMatrix (Int.castRingHom ℂ) CartanMatrix.E₈).mulVec (fun i => (m i : ℂ))
      = (RingHom.mapMatrix (Int.castRingHom ℂ) CartanMatrix.E₈).mulVec (fun i => (m' i : ℂ)) := by
    funext j
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply]
    calc ∑ i, ((CartanMatrix.E₈ j i : ℤ) : ℂ) * (m i : ℂ)
        = ∑ i, (m i : ℂ) * ((CartanMatrix.E₈ j i : ℤ) : ℂ) :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ = ∑ i, (m' i : ℂ) * ((CartanMatrix.E₈ j i : ℤ) : ℂ) := hmat j
      _ = ∑ i, ((CartanMatrix.E₈ j i : ℤ) : ℂ) * (m' i : ℂ) :=
          Finset.sum_congr rfl (fun i _ => by ring)
  have hdet : (RingHom.mapMatrix (Int.castRingHom ℂ) CartanMatrix.E₈).det ≠ 0 := by
    rw [← RingHom.map_det, (show CartanMatrix.E₈.det = 1 from CartanMatrix.E₈_det)]
    norm_num
  have hinj := Matrix.mulVec_injective_of_det_ne_zero hdet hmv
  funext i
  exact Nat.cast_injective (congrFun hinj i)

/-- The list-sum of a function over the letters of a word is the sum over the letters weighted by
their multiplicity. -/
lemma sum_map_eq_sum_count (w : List (Fin 8)) (g : Fin 8 → ℂ) :
    (w.map g).sum = ∑ i : Fin 8, (w.count i : ℂ) * g i := by
  induction w with
  | nil => simp
  | cons a t ih =>
      have hpt : ∀ i : Fin 8, ((List.count i (a :: t) : ℂ) * g i)
          = (List.count i t : ℂ) * g i + (if i = a then (1 : ℂ) else 0) * g i := by
        intro i
        by_cases hi : i = a
        · subst hi
          rw [List.count_cons_self, if_pos rfl]
          push_cast
          ring
        · rw [List.count_cons_of_ne (Ne.symm hi), if_neg hi]
          ring
      rw [List.map_cons, List.sum_cons, ih]
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, add_comm]
      congr 1
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hi
        rw [if_neg hi]
        ring
      · intro h
        exact absurd (Finset.mem_univ a) h

/-- A word vector lies in the joint weight space of the weight attached to its letter
multiplicities. -/
lemma wordVec_mem_wtVec (w : List (Fin 8)) :
    wordVec vω w ∈ jointWeightSpace (wtVec (fun i => w.count i)) := by
  intro j
  rw [h_smul_wordVec vω omegaOnePlusOmegaEight (fun k => by
    rw [h_acts_omega k, weightInU]; exact algebraMap_smul_Mω _ _) j w]
  congr 1
  rw [sum_map_eq_sum_count]
  simp only [wtVec]

end WeightDecomposition

section Grouping

/-- If a weight-`wtVec m` vector is a sum of vectors of the *other* weights `wtVec n` (`n ∈ T`,
`n ≠ m`), then everything vanishes. -/
theorem eq_zero_of_sum_eq_of_ne (m : Fin 8 → ℕ) (T : Finset (Fin 8 → ℕ)) (x : Mω)
    (hx : x ∈ jointWeightSpace (wtVec m)) (Y : (Fin 8 → ℕ) → Mω)
    (hY : ∀ n ∈ T, Y n ∈ jointWeightSpace (wtVec n)) (hne : ∀ n ∈ T, n ≠ m)
    (hsum : x = ∑ n ∈ T, Y n) : x = 0 ∧ ∀ n ∈ T, Y n = 0 := by
  classical
  have hindep : ∀ t : Option {n : Fin 8 → ℕ // n ∈ T},
      (match t with | none => x | some n => -Y n.val) ∈
        jointWeightSpace (match t with | none => wtVec m | some n => wtVec n.val) := by
    intro t
    match t with
    | none => exact hx
    | some n => exact Submodule.neg_mem _ (hY n.val n.2)
  have hinj : Function.Injective (fun t : Option {n : Fin 8 → ℕ // n ∈ T} =>
      match t with | none => wtVec m | some n => wtVec n.val) := by
    intro a b hab
    match a, b with
    | none, none => rfl
    | none, some n =>
        exact absurd (wtVec_injective hab) (fun h => hne n.val n.2 h.symm)
    | some n, none =>
        exact absurd (wtVec_injective hab.symm) (fun h => hne n.val n.2 h.symm)
    | some n, some n' =>
        exact congrArg some (Subtype.ext (wtVec_injective hab))
  have hsum0 : ∑ t : Option {n : Fin 8 → ℕ // n ∈ T},
      (match t with | none => x | some n => -Y n.val) = 0 := by
    rw [Fintype.sum_option]
    simp only
    rw [Finset.sum_coe_sort T (fun n => -Y n), Finset.sum_neg_distrib, hsum]
    abel
  have hzero := eq_zero_of_sum_eq_zero
    (fun t : Option {n : Fin 8 → ℕ // n ∈ T} =>
      match t with | none => wtVec m | some n => wtVec n.val)
    hinj
    (fun t => match t with | none => x | some n => -Y n.val) hindep hsum0
  refine ⟨hzero none, fun n hn => ?_⟩
  have h := hzero (some ⟨n, hn⟩)
  simpa using h

/-- Every element of a weight space is a linear combination of word vectors of that weight:
the weight-`wtVec m` space of `Mω` is contained in the span of the word vectors whose letters
have multiplicity vector `m`. -/
theorem jointWeightSpace_le_span_wordVec (m : Fin 8 → ℕ) :
    jointWeightSpace (wtVec m) ≤ Submodule.span ℂ
      {x : Mω | ∃ w : List (Fin 8), (∀ i, w.count i = m i) ∧ x = wordVec vω w} := by
  classical
  intro x hx
  -- `x` is a finite linear combination of word vectors
  have hxspan : x ∈ Submodule.span ℂ (Set.range (wordVec vω)) := by
    have hmem : x ∈ wordSpan vω := by rw [wordSpan_vω_eq_top]; trivial
    simpa [wordSpan] using hmem
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hxspan
  -- the finite set of letter-multiplicity vectors arising in the combination
  let T : Finset (Fin 8 → ℕ) := c.support.image (fun w => fun i => w.count i)
  let Y : (Fin 8 → ℕ) → Mω := fun n =>
    ∑ w ∈ c.support.filter (fun w => (fun i => w.count i) = n), c w • wordVec vω w
  have hYmem : ∀ n : Fin 8 → ℕ, Y n ∈ jointWeightSpace (wtVec n) := by
    intro n
    refine Submodule.sum_mem _ fun w hw => ?_
    rw [Finset.mem_filter] at hw
    rw [← hw.2]
    exact Submodule.smul_mem _ _ (wordVec_mem_wtVec w)
  have hfiber : ∑ n ∈ T, Y n = ∑ w ∈ c.support, c w • wordVec vω w := by
    refine Finset.sum_fiberwise_of_maps_to (fun w hw => ?_) _
    exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hxY : x = ∑ n ∈ T, Y n := by
    rw [hfiber]
    exact hc.symm
  by_cases hm : m ∈ T
  · -- the part of weight `wtVec m` is exactly `Y m`
    have hzm : x - Y m ∈ jointWeightSpace (wtVec m) := Submodule.sub_mem _ hx (hYmem m)
    have hzsum : x - Y m = ∑ n ∈ T.erase m, Y n := by
      have hsplit : (∑ n ∈ T.erase m, Y n) = (∑ n ∈ T, Y n) - Y m := by
        rw [eq_sub_iff_add_eq]
        exact Finset.sum_erase_add T Y hm
      rw [hsplit, hxY]
    have hne : ∀ n ∈ T.erase m, n ≠ m := fun n hn => (Finset.mem_erase.mp hn).1
    obtain ⟨hzero, -⟩ := eq_zero_of_sum_eq_of_ne m (T.erase m) (x - Y m) hzm Y
      (fun n _ => hYmem n) hne hzsum
    have hxm : x = Y m := sub_eq_zero.mp hzero
    rw [hxm]
    refine Submodule.sum_mem _ fun w hw => ?_
    rw [Finset.mem_filter] at hw
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, fun i => congrFun hw.2 i, rfl⟩)
  · -- no word of weight `wtVec m` occurs, so `x = 0`
    have hne : ∀ n ∈ T, n ≠ m := fun n hn => fun h => hm (h ▸ hn)
    obtain ⟨hzero, -⟩ := eq_zero_of_sum_eq_of_ne m T x hx Y (fun n _ => hYmem n) hne hxY
    rw [hzero]
    exact Submodule.zero_mem _

/-- **The weight spaces of `M(ω₁+ω₈)` are exactly the spans of the word vectors with the
corresponding letter multiplicities.** -/
theorem jointWeightSpace_eq_span_wordVec (m : Fin 8 → ℕ) :
    jointWeightSpace (wtVec m) = Submodule.span ℂ
      {x : Mω | ∃ w : List (Fin 8), (∀ i, w.count i = m i) ∧ x = wordVec vω w} := by
  refine le_antisymm (jointWeightSpace_le_span_wordVec m) ?_
  refine Submodule.span_le.mpr ?_
  rintro x ⟨w, hw, rfl⟩
  have : wtVec (fun i => w.count i) = wtVec m := by
    rw [funext hw]
  rw [← this]
  exact wordVec_mem_wtVec w

/-- **Finiteness of the weight spaces of `M(ω₁+ω₈)`.**  Since the letter multiplicities of a word
are determined by its weight (`wtVec_injective`), the words of a fixed weight form the finite set of
words with prescribed multiplicities (`Commons.Data.List.finite_setOf_count_eq`), so each weight
space is spanned by finitely many weight vectors. -/
theorem jointWeightSpace_le_span_finite (m : Fin 8 → ℕ) :
    ∃ S : Set Mω, S.Finite ∧ jointWeightSpace (wtVec m) ≤ Submodule.span ℂ S := by
  have hfin : ({w : List (Fin 8) | ∀ i, w.count i = m i} : Set (List (Fin 8))).Finite :=
    Commons.Data.List.finite_setOf_count_eq m
  refine ⟨(fun w : List (Fin 8) => wordVec vω w) '' {w : List (Fin 8) | ∀ i, w.count i = m i},
    hfin.image _, ?_⟩
  refine le_trans (jointWeightSpace_le_span_wordVec m) (Submodule.span_mono ?_)
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, hw, rfl⟩

end Grouping

end Submission.WeightIndependence
