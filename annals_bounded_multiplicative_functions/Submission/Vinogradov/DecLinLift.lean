/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.FromDecLin
import Submission.Vinogradov.Section4Exp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The even/odd lift `DecLin ⟹ DecLinScale · 2` (ROADMAP session 79 (C))

The enlarged plate `plateScale k M 2 j = plate k (1/M) (pieceCenter M j)` at level `M` is the
*un-enlarged* plate of a shifted partition of length `2/M`: the **even** pieces `j = 2i` are the
pieces of the shifted partition with origin `a₁ = -1/(2M)`, the **odd** ones those of the shifted
partition with origin `a₂ = +1/(2M)`.  Hence the un-enlarged decoupling inequality `DecLin`, which
transfers to *any* interval with the same constant (`decLinOn_of_decLin`), gives the enlarged
inequality `DecLinScale · 2` at the price of a factor `2` (the triangle inequality plus the
additivity of the `ℓ²` norms over the even/odd split).

This removes the λ-enlargement blocker of ROADMAP session 79 (B): the §2 bilinear route, which
is available in the un-enlarged convention, yields `DecLin k (2^N) C_N` for every dyadic level
`N`, and the lift converts it into `DecLinScale k M 2 C_N` for every `M`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace Submission.Vinogradov

/-! ## 1. The even/odd reindexing of a finite sum -/

/-- **Even reindexing.**  The sum over the even pieces of the `M`-fold partition, counted by
`j = 2i` with `i < m`, equals the sum over the even indices `j : Fin M`
(needs `M ≤ 2m` so that the even indices fit in `Fin m`). -/
lemma sum_fin_even_eq {M m : ℕ} (hm : M ≤ 2 * m) {α : Type*} [AddCommMonoid α] (F : ℕ → α) :
    (∑ i : Fin m, if 2 * (i : ℕ) < M then F (2 * (i : ℕ)) else 0)
      = ∑ j : Fin M, (if (j : ℕ) % 2 = 0 then F (j : ℕ) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun i hi => (⟨2 * (i : ℕ), ?_⟩ : Fin M)) ?_ ?_ ?_ ?_
  · exact (Finset.mem_filter.mp hi).2
  · intro a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact Nat.mul_mod_right 2 (a : ℕ)
  · intro a₁ ha₁ a₂ ha₂ heq
    have h : 2 * (a₁ : ℕ) = 2 * (a₂ : ℕ) := congrArg Fin.val heq
    exact Fin.ext (by omega)
  · intro b hb
    have hb2 : (b : ℕ) % 2 = 0 := (Finset.mem_filter.mp hb).2
    have hk : 2 * ((b : ℕ) / 2) = (b : ℕ) := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hb2)
    refine ⟨⟨(b : ℕ) / 2, ?_⟩, ?_, ?_⟩
    · have := b.isLt; omega
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show 2 * ((b : ℕ) / 2) < M
      omega
    · exact Fin.ext hk
  · intro a ha
    rfl

/-- **Odd reindexing.**  The sum over the odd pieces of the `M`-fold partition, counted by
`j = 2i+1` with `i < m`, equals the sum over the odd indices `j : Fin M`. -/
lemma sum_fin_odd_eq {M m : ℕ} (hm : M ≤ 2 * m) {α : Type*} [AddCommMonoid α] (F : ℕ → α) :
    (∑ i : Fin m, if 2 * (i : ℕ) + 1 < M then F (2 * (i : ℕ) + 1) else 0)
      = ∑ j : Fin M, (if (j : ℕ) % 2 = 1 then F (j : ℕ) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun i hi => (⟨2 * (i : ℕ) + 1, ?_⟩ : Fin M)) ?_ ?_ ?_ ?_
  · exact (Finset.mem_filter.mp hi).2
  · intro a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show (2 * (a : ℕ) + 1) % 2 = 1
    rw [Nat.add_mod, Nat.mul_mod_right 2 (a : ℕ), zero_add, Nat.mod_eq_of_lt (by norm_num)]
  · intro a₁ ha₁ a₂ ha₂ heq
    have h : 2 * (a₁ : ℕ) + 1 = 2 * (a₂ : ℕ) + 1 := congrArg Fin.val heq
    exact Fin.ext (by omega)
  · intro b hb
    have hb2 : (b : ℕ) % 2 = 1 := (Finset.mem_filter.mp hb).2
    have hk : 2 * ((b : ℕ) / 2) + (b : ℕ) % 2 = (b : ℕ) := Nat.div_add_mod (b : ℕ) 2
    have hk' : 2 * ((b : ℕ) / 2) + 1 = (b : ℕ) := by rw [hb2] at hk; exact hk
    refine ⟨⟨(b : ℕ) / 2, ?_⟩, ?_, ?_⟩
    · have := b.isLt; omega
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show 2 * ((b : ℕ) / 2) + 1 < M
      omega
    · exact Fin.ext hk'
  · intro a ha
    rfl

/-! ## 2. Padding a `Fin M`-family by zeros to a `Fin m`-family -/

/-- The `n`-th element of a family indexed by `Fin M`, extended by `0` for `n ≥ M`. -/
def padFin {M : ℕ} {β : Type*} [Zero β] (F : Fin M → β) (n : ℕ) : β :=
  if h : n < M then F ⟨n, h⟩ else 0

/-- The **even part** of a family indexed by `Fin M`, padded by zeros to `Fin m'`
(the index `i` carries the piece `2i`). -/
def evenPart {M m' : ℕ} {β : Type*} [Zero β] (F : Fin M → β) : Fin m' → β :=
  fun i => if h : 2 * (i : ℕ) < M then F ⟨2 * (i : ℕ), h⟩ else 0

/-- The **odd part** of a family indexed by `Fin M`, padded by zeros to `Fin m'`
(the index `i` carries the piece `2i+1`). -/
def oddPart {M m' : ℕ} {β : Type*} [Zero β] (F : Fin M → β) : Fin m' → β :=
  fun i => if h : 2 * (i : ℕ) + 1 < M then F ⟨2 * (i : ℕ) + 1, h⟩ else 0

@[simp] lemma padFin_apply {M : ℕ} {β : Type*} [Zero β] (F : Fin M → β) (j : Fin M) :
    padFin F (j : ℕ) = F j := by
  rw [padFin, dif_pos j.isLt]

@[simp] lemma evenPart_apply {M m' : ℕ} {β : Type*} [Zero β] (F : Fin M → β) (i : Fin m')
    (h : 2 * (i : ℕ) < M) : evenPart F i = F ⟨2 * (i : ℕ), h⟩ := by
  rw [evenPart, dif_pos h]

@[simp] lemma evenPart_apply_not {M m' : ℕ} {β : Type*} [Zero β] (F : Fin M → β) (i : Fin m')
    (h : ¬ 2 * (i : ℕ) < M) : evenPart F i = 0 := by
  rw [evenPart, dif_neg h]

@[simp] lemma oddPart_apply {M m' : ℕ} {β : Type*} [Zero β] (F : Fin M → β) (i : Fin m')
    (h : 2 * (i : ℕ) + 1 < M) : oddPart F i = F ⟨2 * (i : ℕ) + 1, h⟩ := by
  rw [oddPart, dif_pos h]

@[simp] lemma oddPart_apply_not {M m' : ℕ} {β : Type*} [Zero β] (F : Fin M → β) (i : Fin m')
    (h : ¬ 2 * (i : ℕ) + 1 < M) : oddPart F i = 0 := by
  rw [oddPart, dif_neg h]

/-- **The even half of a `Fin M`-family is the sum over its even indices.** -/
lemma sum_evenPart {M m' : ℕ} (hm : M ≤ 2 * m') {β : Type*} [AddCommMonoid β]
    (F : Fin M → β) :
    (∑ i : Fin m', evenPart F i) = ∑ j : Fin M, (if (j : ℕ) % 2 = 0 then F j else 0) := by
  have h1 : (∑ i : Fin m', evenPart F i)
      = ∑ i : Fin m', (if 2 * (i : ℕ) < M then padFin F (2 * (i : ℕ)) else 0) :=
    Finset.sum_congr rfl fun i _ => by
      by_cases hi : 2 * (i : ℕ) < M <;> simp [evenPart, padFin, hi]
  have h2 := sum_fin_even_eq hm (padFin F)
  rw [h1, h2]
  exact Finset.sum_congr rfl fun j _ => by simp

/-- **The odd half of a `Fin M`-family is the sum over its odd indices.** -/
lemma sum_oddPart {M m' : ℕ} (hm : M ≤ 2 * m') {β : Type*} [AddCommMonoid β]
    (F : Fin M → β) :
    (∑ i : Fin m', oddPart F i) = ∑ j : Fin M, (if (j : ℕ) % 2 = 1 then F j else 0) := by
  have h1 : (∑ i : Fin m', oddPart F i)
      = ∑ i : Fin m', (if 2 * (i : ℕ) + 1 < M then padFin F (2 * (i : ℕ) + 1) else 0) :=
    Finset.sum_congr rfl fun i _ => by
      by_cases hi : 2 * (i : ℕ) + 1 < M <;> simp [oddPart, padFin, hi]
  have h2 := sum_fin_odd_eq hm (padFin F)
  rw [h1, h2]
  exact Finset.sum_congr rfl fun j _ => by simp

/-- **The even/odd split of a sum.** -/
lemma sum_even_add_odd {M : ℕ} {β : Type*} [AddCommMonoid β] (F : Fin M → β) :
    (∑ j : Fin M, (if (j : ℕ) % 2 = 0 then F j else 0))
      + (∑ j : Fin M, (if (j : ℕ) % 2 = 1 then F j else 0)) = ∑ j : Fin M, F j := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmod : (j : ℕ) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : (j : ℕ) % 2 = 0 ∨ (j : ℕ) % 2 = 1) with h | h <;> simp [h]

/-! ## 3. The shifted partitions realising an enlarged plate

The enlarged plate `plateScale k M 2 j = plate k (1/M) (pieceCenter M j)` is the *un-enlarged*
plate `plate k (s/(2m')) (a + (i+1/2)s/m')` of a shifted partition `[a, a+s]`, `s = 2m'/M`:
* for the even piece `j = 2i` one takes the origin `a₁ = -1/(2M)` (`evOrigin`);
* for the odd piece `j = 2i+1` one takes the origin `a₂ = +1/(2M)` (`odOrigin`). -/

/-- The origin of the shifted partition realising the even enlarged pieces. -/
def evOrigin (M : ℕ) : ℝ := -1 / (2 * (M : ℝ))

/-- The origin of the shifted partition realising the odd enlarged pieces. -/
def odOrigin (M : ℕ) : ℝ := 1 / (2 * (M : ℝ))

/-- The length `2m'/M` of the shifted partition of `[a, a+s]`. -/
def shiftLen (M m' : ℕ) : ℝ := 2 * (m' : ℝ) / (M : ℝ)

/-- **The even enlarged plate is an un-enlarged shifted plate** (`j = 2i`). -/
lemma plate_shift_even {k M m' : ℕ} (hM : 0 < M) (i : Fin m') (hi : 2 * (i : ℕ) < M) :
    plateScale k M 2 (⟨2 * (i : ℕ), hi⟩ : Fin M)
      = plate k (shiftLen M m' / (2 * (m' : ℝ)))
          (evOrigin M + (((i : ℕ) : ℝ) + 1 / 2) * shiftLen M m' / (m' : ℝ)) := by
  rw [plateScale, pieceCenter, shiftLen, evOrigin]
  refine congr_arg₂ (plate k) ?_ ?_
  · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    have hm'r : (m' : ℝ) ≠ 0 := by
      have := i.isLt; exact_mod_cast (by omega : m' ≠ 0)
    field_simp
  · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    have hm'r : (m' : ℝ) ≠ 0 := by
      have := i.isLt; exact_mod_cast (by omega : m' ≠ 0)
    field_simp
    push_cast
    ring

/-- **The odd enlarged plate is an un-enlarged shifted plate** (`j = 2i+1`). -/
lemma plate_shift_odd {k M m' : ℕ} (hM : 0 < M) (i : Fin m') (hi : 2 * (i : ℕ) + 1 < M) :
    plateScale k M 2 (⟨2 * (i : ℕ) + 1, hi⟩ : Fin M)
      = plate k (shiftLen M m' / (2 * (m' : ℝ)))
          (odOrigin M + (((i : ℕ) : ℝ) + 1 / 2) * shiftLen M m' / (m' : ℝ)) := by
  rw [plateScale, pieceCenter, shiftLen, odOrigin]
  refine congr_arg₂ (plate k) ?_ ?_
  · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    have hm'r : (m' : ℝ) ≠ 0 := by
      have := i.isLt; exact_mod_cast (by omega : m' ≠ 0)
    field_simp
  · have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
    have hm'r : (m' : ℝ) ≠ 0 := by
      have := i.isLt; exact_mod_cast (by omega : m' ≠ 0)
    field_simp
    push_cast
    ring

/-! ## 4. The triangle inequality and the even/odd lift -/

/-- The triangle inequality for the `L^{p_k}` seminorm. -/
lemma lpNorm_add_le {k : ℕ} (hk : 1 ≤ k) {f g : E k → ℂ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    lpNorm k (pE k) (f + g) ≤ lpNorm k (pE k) f + lpNorm k (pE k) g :=
  eLpNorm_add_le (one_le_pE k hk)

set_option maxHeartbeats 16000000 in
/-- **The even/odd lift.**  From the un-enlarged linear decoupling inequality `DecLin` at level
`m'` one gets the enlarged inequality `DecLinScale · 2` at level `M`, provided the even and odd
pieces of the `M`-fold partition fit into the `m'`-fold one (`M ≤ 2m'`).  The proof applies
`DecLin` to the two shifted partitions of origins `∓1/(2M)` (via `decLinOn_of_decLin`) and adds the
two bounds, which costs a factor `2`. -/
theorem decLinScale_two_of_decLin {k M m' : ℕ} (hk : 1 ≤ k) (hm : M ≤ 2 * m')
    {C : ℝ≥0∞} (hD : DecLin k m' C) : DecLinScale k M 2 (2 * C) := by
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    intro F hF
    have h0 : (fun x : E k => ∑ j : Fin 0, F j x) = fun _ => 0 := by
      funext x; simp
    have hl2 : l2Norm (fun j : Fin 0 => lpNorm k (pE k) (F j)) = 0 := by
      rw [l2Norm]
      simp
    rw [h0, lpNorm_zero, hl2]
    simp
  have hm' : 0 < m' := by omega
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hs : 0 < shiftLen M m' := by
    rw [shiftLen]
    exact div_pos (by positivity) hMR
  intro F hF
  -- the two families
  have hfe : ∀ i : Fin m', IsFourierRep k (plate k (shiftLen M m' / (2 * (m' : ℝ)))
      (evOrigin M + (((i : ℕ) : ℝ) + 1 / 2) * shiftLen M m' / (m' : ℝ))) (evenPart F i) := by
    intro i
    by_cases hi : 2 * (i : ℕ) < M
    · rw [evenPart_apply F i hi]
      refine IsFourierRep.mono ?_ (hF ⟨2 * (i : ℕ), hi⟩)
      rw [plate_shift_even (k := k) hM i hi]
    · rw [evenPart_apply_not F i hi]
      exact IsFourierRep.zero k _
  have hfo : ∀ i : Fin m', IsFourierRep k (plate k (shiftLen M m' / (2 * (m' : ℝ)))
      (odOrigin M + (((i : ℕ) : ℝ) + 1 / 2) * shiftLen M m' / (m' : ℝ))) (oddPart F i) := by
    intro i
    by_cases hi : 2 * (i : ℕ) + 1 < M
    · rw [oddPart_apply F i hi]
      refine IsFourierRep.mono ?_ (hF ⟨2 * (i : ℕ) + 1, hi⟩)
      rw [plate_shift_odd (k := k) hM i hi]
    · rw [oddPart_apply_not F i hi]
      exact IsFourierRep.zero k _
  have hmeasE : AEStronglyMeasurable (fun x : E k => ∑ i : Fin m', evenPart F i x)
      (volume : Measure (E k)) :=
    (continuous_finsetSum _ (fun i _ => (hfe i).continuous)).aestronglyMeasurable
  have hmeasO : AEStronglyMeasurable (fun x : E k => ∑ i : Fin m', oddPart F i x)
      (volume : Measure (E k)) :=
    (continuous_finsetSum _ (fun i _ => (hfo i).continuous)).aestronglyMeasurable
  -- the decomposition of the sum
  have hFsum : (∑ j : Fin M, F j)
      = (∑ i : Fin m', evenPart F i) + (∑ i : Fin m', oddPart F i) := by
    rw [(sum_even_add_odd F).symm, sum_evenPart hm F, sum_oddPart hm F]
  have hsum : (fun x : E k => ∑ j : Fin M, F j x)
      = (fun x : E k => ∑ i : Fin m', evenPart F i x)
        + (fun x : E k => ∑ i : Fin m', oddPart F i x) := by
    funext x
    simpa only [Pi.add_apply, Finset.sum_apply] using congrFun hFsum x
  -- the two decoupling bounds
  have hDe := decLinOn_of_decLin (k := k) (M := m') (C := C) hD
    (a := evOrigin M) (s := shiftLen M m') hs
  have hDo := decLinOn_of_decLin (k := k) (M := m') (C := C) hD
    (a := odOrigin M) (s := shiftLen M m') hs
  have hboundE := hDe (evenPart F) hfe
  have hboundO := hDo (oddPart F) hfo
  -- the ℓ²-comparisons
  have hone : (∑ i : Fin m', (lpNorm k (pE k) (evenPart F i)) ^ (2 : ℝ))
      = ∑ i : Fin m', (if 2 * (i : ℕ) < M then
          ((lpNorm k (pE k) (padFin F (2 * (i : ℕ)))) ^ (2 : ℝ)) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 2 * (i : ℕ) < M
    · simp only [evenPart_apply F i hi, if_pos hi, padFin, dif_pos hi]
    · simp only [evenPart_apply_not F i hi, if_neg hi, padFin, dif_neg hi,
        show lpNorm k (pE k) (0 : E k → ℂ) = 0 from lpNorm_zero k,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htwo : (∑ i : Fin m', (lpNorm k (pE k) (oddPart F i)) ^ (2 : ℝ))
      = ∑ i : Fin m', (if 2 * (i : ℕ) + 1 < M then
          ((lpNorm k (pE k) (padFin F (2 * (i : ℕ) + 1))) ^ (2 : ℝ)) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : 2 * (i : ℕ) + 1 < M
    · simp only [oddPart_apply F i hi, if_pos hi, padFin, dif_pos hi]
    · simp only [oddPart_apply_not F i hi, if_neg hi, padFin, dif_neg hi,
        show lpNorm k (pE k) (0 : E k → ℂ) = 0 from lpNorm_zero k,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hsumE : (∑ i : Fin m', (lpNorm k (pE k) (evenPart F i)) ^ (2 : ℝ))
      ≤ ∑ j : Fin M, (lpNorm k (pE k) (F j)) ^ (2 : ℝ) := by
    rw [hone]
    rw [sum_fin_even_eq hm (fun n => (lpNorm k (pE k) (padFin F n)) ^ (2 : ℝ))]
    calc ∑ j : Fin M,
          (if (j : ℕ) % 2 = 0 then (lpNorm k (pE k) (padFin F j)) ^ (2 : ℝ) else 0)
        ≤ ∑ j : Fin M, (lpNorm k (pE k) (padFin F j)) ^ (2 : ℝ) :=
          Finset.sum_le_sum (fun j _ => by
            by_cases hj : (j : ℕ) % 2 = 0 <;> simp [hj])
      _ = ∑ j : Fin M, (lpNorm k (pE k) (F j)) ^ (2 : ℝ) :=
          Finset.sum_congr rfl (fun j _ => by simp)
  have hsumO : (∑ i : Fin m', (lpNorm k (pE k) (oddPart F i)) ^ (2 : ℝ))
      ≤ ∑ j : Fin M, (lpNorm k (pE k) (F j)) ^ (2 : ℝ) := by
    rw [htwo]
    rw [sum_fin_odd_eq hm (fun n => (lpNorm k (pE k) (padFin F n)) ^ (2 : ℝ))]
    calc ∑ j : Fin M,
          (if (j : ℕ) % 2 = 1 then (lpNorm k (pE k) (padFin F j)) ^ (2 : ℝ) else 0)
        ≤ ∑ j : Fin M, (lpNorm k (pE k) (padFin F j)) ^ (2 : ℝ) :=
          Finset.sum_le_sum (fun j _ => by
            by_cases hj : (j : ℕ) % 2 = 1 <;> simp [hj])
      _ = ∑ j : Fin M, (lpNorm k (pE k) (F j)) ^ (2 : ℝ) :=
          Finset.sum_congr rfl (fun j _ => by simp)
  have hnormE : l2Norm (fun i : Fin m' => lpNorm k (pE k) (evenPart F i))
      ≤ l2Norm (fun j : Fin M => lpNorm k (pE k) (F j)) := by
    rw [l2Norm, l2Norm]
    exact ENNReal.rpow_le_rpow hsumE (by norm_num)
  have hnormO : l2Norm (fun i : Fin m' => lpNorm k (pE k) (oddPart F i))
      ≤ l2Norm (fun j : Fin M => lpNorm k (pE k) (F j)) := by
    rw [l2Norm, l2Norm]
    exact ENNReal.rpow_le_rpow hsumO (by norm_num)
  -- assembly
  let L : ℝ≥0∞ := l2Norm (fun j : Fin M => lpNorm k (pE k) (F j))
  calc lpNorm k (pE k) (fun x : E k => ∑ j : Fin M, F j x)
      = lpNorm k (pE k) ((fun x : E k => ∑ i : Fin m', evenPart F i x)
          + (fun x : E k => ∑ i : Fin m', oddPart F i x)) := by rw [hsum]
    _ ≤ lpNorm k (pE k) (fun x : E k => ∑ i : Fin m', evenPart F i x)
          + lpNorm k (pE k) (fun x : E k => ∑ i : Fin m', oddPart F i x) :=
        lpNorm_add_le hk hmeasE hmeasO
    _ ≤ C * L + C * L :=
        add_le_add (hboundE.trans (mul_le_mul' le_rfl hnormE))
          (hboundO.trans (mul_le_mul' le_rfl hnormO))
    _ = (2 * C) * L := by rw [← two_mul, mul_assoc]

/-! ## 5. From the dyadic levels to `linExpSet` membership -/

/-- `2 ^ clog 2 M ≤ 2M` for `M ≥ 1` (the upper bound matching `Nat.le_pow_clog`). -/
lemma pow_clog_two_le (M : ℕ) (hM : 1 ≤ M) : 2 ^ Nat.clog 2 M ≤ 2 * M := by
  rcases eq_or_lt_of_le hM with h | h
  · subst h; simp
  · have hN : 1 ≤ Nat.clog 2 M := Nat.clog_pos (by norm_num) (by omega)
    have hlt : 2 ^ (Nat.clog 2 M - 1) < M := by
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := M) (by omega)
      simpa only [Nat.pred_eq_sub_one] using this
    calc 2 ^ Nat.clog 2 M = 2 ^ (Nat.clog 2 M - 1 + 1) := by rw [Nat.sub_add_cancel hN]
      _ = 2 ^ (Nat.clog 2 M - 1) * 2 := by rw [pow_succ]
      _ ≤ 2 * M := by omega

/-- `2 ^ max 1 (clog 2 M) ≤ 4M` for `M ≥ 1`. -/
lemma two_pow_max_clog_le (M : ℕ) (hM : 1 ≤ M) : 2 ^ max 1 (Nat.clog 2 M) ≤ 4 * M := by
  rcases eq_or_lt_of_le hM with h | h
  · subst h; simp
  · have hc : 1 ≤ Nat.clog 2 M := Nat.clog_pos (by norm_num) (by omega)
    rw [max_eq_right hc]
    have := pow_clog_two_le M hM
    omega

/-- **The lift at a dyadic level gives `linExpSet` membership.**  If the un-enlarged linear
decoupling inequality holds at every dyadic level with a constant `K 2^{NA}`, then the *enlarged*
inequality `DecLinScale · 2` holds at every level `M` with constant `≲ M^A` — i.e. `A` belongs to
the exponent set `linExpSet k` of GLYZ §4.  This is the passage that removes the `λ`-enlargement
blocker of ROADMAP session 79 (B). -/
theorem mem_linExpSet_of_decLin_dyadic {k : ℕ} (hk : 1 ≤ k) {A K : ℝ} (hK : 0 < K) (hA : 0 ≤ A)
    (hD : ∀ N : ℕ, 1 ≤ N →
      DecLin k (2 ^ N) (ENNReal.ofReal (K * ((2 ^ N : ℕ) : ℝ) ^ A))) :
    A ∈ linExpSet k := by
  refine ⟨hA, max 1 (2 * (4 : ℝ) ^ A * K), lt_of_lt_of_le one_pos (le_max_left _ _),
    fun M hM => ?_⟩
  have hN1 : 1 ≤ max 1 (Nat.clog 2 M) := le_max_left _ _
  have hD' := hD (max 1 (Nat.clog 2 M)) hN1
  have hm' : M ≤ 2 * 2 ^ max 1 (Nat.clog 2 M) := by
    have h1 := Nat.le_pow_clog (b := 2) (by norm_num : 1 < 2) M
    have h2 : (2 : ℕ) ^ Nat.clog 2 M ≤ 2 ^ max 1 (Nat.clog 2 M) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  have hlift := decLinScale_two_of_decLin (k := k) (M := M)
    (m' := 2 ^ max 1 (Nat.clog 2 M)) hk hm' hD'
  refine DecLinScale_mono ?_ hlift
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hcast : (((2 ^ max 1 (Nat.clog 2 M) : ℕ) : ℝ)) = (2 : ℝ) ^ max 1 (Nat.clog 2 M) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have hle : (2 : ℝ) ^ max 1 (Nat.clog 2 M) ≤ 4 * M := by
    rw [← hcast]
    exact_mod_cast two_pow_max_clog_le M hM
  have hpow : (((2 ^ max 1 (Nat.clog 2 M) : ℕ) : ℝ)) ^ A ≤ (4 : ℝ) ^ A * (M : ℝ) ^ A := by
    rw [hcast,
      ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    exact Real.rpow_le_rpow (by positivity) hle hA
  have hMA : (0 : ℝ) ≤ (M : ℝ) ^ A := Real.rpow_nonneg (by positivity) A
  have h4A : (0 : ℝ) ≤ (4 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) A
  have hstep : 2 * (K * (((2 ^ max 1 (Nat.clog 2 M) : ℕ) : ℝ)) ^ A)
      ≤ (2 * (4 : ℝ) ^ A * K) * (M : ℝ) ^ A := by
    nlinarith [hpow, hK.le, hMA, h4A]
  calc 2 * (K * (((2 ^ max 1 (Nat.clog 2 M) : ℕ) : ℝ)) ^ A)
      ≤ (2 * (4 : ℝ) ^ A * K) * (M : ℝ) ^ A := hstep
    _ ≤ max 1 (2 * (4 : ℝ) ^ A * K) * (M : ℝ) ^ A :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hMA


/-! ## 6. The generalised lift: `lam` residue classes

The lift `decLinScale_two_of_decLin` is the case `lam = 2` of the following statement: the
`lam`-enlarged plate of the piece `lam·i + r` of the level-`M` partition is the *un-enlarged* plate
of the shifted partition with origin `(r + 1/2 − lam/2)/M` and length `lam·m'/M`.  Summing the
`lam` shifted statements and using the triangle inequality costs the factor `lam`.  The case
`lam = 1` is the level-coarsening `DecLin k m' C → DecLin k M C` (`M ≤ m'`). -/

/-- The origin of the shifted partition realising the residue class `r` mod `lam`. -/
def resOrigin (M lam r : ℕ) : ℝ := ((r : ℝ) + 1 / 2 - (lam : ℝ) / 2) / (M : ℝ)

/-- The length `lam·m'/M` of the shifted partition. -/
def resLen (M m' lam : ℕ) : ℝ := (lam : ℝ) * (m' : ℝ) / (M : ℝ)

/-- The `r`-th residue class of a `Fin M`-family, padded by zeros to a `Fin m`-family. -/
def resPart {M m lam : ℕ} {β : Type*} [Zero β] (r : Fin lam) (F : Fin M → β) : Fin m → β :=
  fun i => if h : lam * (i : ℕ) + (r : ℕ) < M
    then F ⟨lam * (i : ℕ) + (r : ℕ), h⟩ else 0

@[simp] lemma resPart_apply {M m lam : ℕ} {β : Type*} [Zero β] (r : Fin lam)
    (F : Fin M → β) (i : Fin m) (h : lam * (i : ℕ) + (r : ℕ) < M) :
    resPart r F i = F ⟨lam * (i : ℕ) + (r : ℕ), h⟩ := dif_pos h

@[simp] lemma resPart_apply_not {M m lam : ℕ} {β : Type*} [Zero β] (r : Fin lam)
    (F : Fin M → β) (i : Fin m) (h : ¬ lam * (i : ℕ) + (r : ℕ) < M) :
    resPart r F i = 0 := dif_neg h

/-- **The residue-class reindexing.** -/
lemma sum_fin_residue_eq {M m lam : ℕ} (hm : M ≤ lam * m) {α : Type*} [AddCommMonoid α]
    (F : ℕ → α) (r : Fin lam) :
    (∑ i : Fin m, if lam * (i : ℕ) + (r : ℕ) < M then F (lam * (i : ℕ) + (r : ℕ)) else 0)
      = ∑ j : Fin M, (if (j : ℕ) % lam = (r : ℕ) then F (j : ℕ) else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun i hi =>
    (⟨lam * (i : ℕ) + (r : ℕ), (Finset.mem_filter.mp hi).2⟩ : Fin M)) ?_ ?_ ?_ ?_
  · intro a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]
  · intro a₁ ha₁ a₂ ha₂ heq
    have h : lam * (a₁ : ℕ) + (r : ℕ) = lam * (a₂ : ℕ) + (r : ℕ) := by
      have := congrArg Fin.val heq
      simpa only [Fin.val_mk] using this
    have hmul : lam * (a₁ : ℕ) = lam * (a₂ : ℕ) := by omega
    exact Fin.ext (Nat.mul_left_cancel (by omega : 0 < lam) hmul)
  · intro b hb
    have hb2 : (b : ℕ) % lam = (r : ℕ) := (Finset.mem_filter.mp hb).2
    have hk : lam * ((b : ℕ) / lam) + (r : ℕ) = (b : ℕ) := by
      rw [← hb2]; exact Nat.div_add_mod (b : ℕ) lam
    have hlt : (b : ℕ) / lam < m := by
      have h1 : lam * ((b : ℕ) / lam) < M := by omega
      exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le h1 hm)
    refine ⟨⟨(b : ℕ) / lam, hlt⟩, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show lam * ((b : ℕ) / lam) + (r : ℕ) < M
      omega
    · exact Fin.ext hk
  · intro a ha
    rfl

set_option maxHeartbeats 16000000 in
/-- **The generalised lift.**  From the un-enlarged linear decoupling inequality at level `m'` one
gets the `lam`-enlarged inequality at level `M` whenever `M ≤ lam·m'` (`lam ≥ 1`); the price is the
factor `lam` (one shifted partition per residue class mod `lam`).  `lam = 1` is the
level-coarsening, `lam = 2` the even/odd lift `decLinScale_two_of_decLin`. -/
theorem decLinScale_of_decLin_nat {k M m' : ℕ} (hk : 1 ≤ k) (lam : ℕ) (hlam : 1 ≤ lam)
    (hm : M ≤ lam * m') {C : ℝ≥0∞} (hD : DecLin k m' C) :
    DecLinScale k M (lam : ℝ) ((lam : ℝ≥0∞) * C) := by
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    intro F hF
    have h0 : (fun x : E k => ∑ j : Fin 0, F j x) = fun _ => 0 := by
      funext x; simp
    have hl2 : l2Norm (fun j : Fin 0 => lpNorm k (pE k) (F j)) = 0 := by
      rw [l2Norm]; simp
    rw [h0, lpNorm_zero, hl2]
    simp
  have hm' : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hm'R : (0 : ℝ) < (m' : ℝ) := by exact_mod_cast hm'
  have hlamR : (0 : ℝ) < (lam : ℝ) := by exact_mod_cast hlam
  have hlamne : (lam : ℕ) ≠ 0 := by omega
  have hs : 0 < resLen M m' lam := by
    rw [resLen]; exact div_pos (mul_pos hlamR hm'R) hMR
  -- the plate identification
  have hplate : ∀ (r : Fin lam) (i : Fin m') (hi : lam * (i : ℕ) + (r : ℕ) < M),
      plateScale k M (lam : ℝ) (⟨lam * (i : ℕ) + (r : ℕ), hi⟩ : Fin M)
        = plate k (resLen M m' lam / (2 * (m' : ℝ)))
            (resOrigin M lam (r : ℕ) + (((i : ℕ) : ℝ) + 1 / 2) * resLen M m' lam / (m' : ℝ)) := by
    intro r i hi
    have hscale : resLen M m' lam / (2 * (m' : ℝ)) = (lam : ℝ) / (2 * (M : ℝ)) := by
      rw [resLen]
      have hMr : (M : ℝ) ≠ 0 := ne_of_gt hMR
      have hm'r : (m' : ℝ) ≠ 0 := ne_of_gt hm'R
      field_simp
    have hcent : resOrigin M lam (r : ℕ)
          + (((i : ℕ) : ℝ) + 1 / 2) * resLen M m' lam / (m' : ℝ)
        = (((lam * (i : ℕ) + (r : ℕ) : ℕ) : ℝ) + 1 / 2) / (M : ℝ) := by
      rw [resOrigin, resLen]
      have hMr : (M : ℝ) ≠ 0 := ne_of_gt hMR
      have hm'r : (m' : ℝ) ≠ 0 := ne_of_gt hm'R
      push_cast
      field_simp
      ring
    rw [plateScale, pieceCenter, hscale, hcent]
  intro F hF
  -- the class hypotheses
  have hfam : ∀ r : Fin lam, ∀ i : Fin m', IsFourierRep k
      (plate k (resLen M m' lam / (2 * (m' : ℝ)))
        (resOrigin M lam (r : ℕ) + (((i : ℕ) : ℝ) + 1 / 2) * resLen M m' lam / (m' : ℝ)))
      (resPart r F i) := by
    intro r i
    by_cases hi : lam * (i : ℕ) + (r : ℕ) < M
    · rw [resPart_apply r F i hi]
      refine IsFourierRep.mono ?_ (hF ⟨lam * (i : ℕ) + (r : ℕ), hi⟩)
      rw [hplate r i hi]
    · rw [resPart_apply_not r F i hi]
      exact IsFourierRep.zero k _
  -- the decoupling bound for each class
  have hbnd : ∀ r : Fin lam,
      lpNorm k (pE k) (fun x : E k => ∑ i : Fin m', resPart r F i x)
        ≤ C * l2Norm (fun j : Fin M => lpNorm k (pE k) (F j)) := by
    intro r
    have hDe := decLinOn_of_decLin (k := k) (M := m') (C := C) hD
      (a := resOrigin M lam (r : ℕ)) (s := resLen M m' lam) hs
    have hb := hDe (fun i => resPart r F i) (hfam r)
    have hpad : (∑ i : Fin m', (lpNorm k (pE k) (resPart r F i)) ^ (2 : ℝ))
        = ∑ i : Fin m', (if lam * (i : ℕ) + (r : ℕ) < M then
            ((lpNorm k (pE k) (padFin F (lam * (i : ℕ) + (r : ℕ)))) ^ (2 : ℝ)) else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : lam * (i : ℕ) + (r : ℕ) < M
      · simp only [resPart_apply r F i hi, if_pos hi, padFin, dif_pos hi]
      · simp only [resPart_apply_not r F i hi, if_neg hi, padFin, dif_neg hi,
          show lpNorm k (pE k) (0 : E k → ℂ) = 0 from lpNorm_zero k,
          ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hsumr : (∑ i : Fin m', (lpNorm k (pE k) (resPart r F i)) ^ (2 : ℝ))
        ≤ ∑ j : Fin M, (lpNorm k (pE k) (F j)) ^ (2 : ℝ) := by
      rw [hpad]
      rw [sum_fin_residue_eq hm (fun n => (lpNorm k (pE k) (padFin F n)) ^ (2 : ℝ)) r]
      calc ∑ j : Fin M, (if (j : ℕ) % lam = (r : ℕ) then
            (lpNorm k (pE k) (padFin F (j : ℕ))) ^ (2 : ℝ) else 0)
          ≤ ∑ j : Fin M, (lpNorm k (pE k) (padFin F (j : ℕ))) ^ (2 : ℝ) :=
            Finset.sum_le_sum fun j _ => by by_cases hj : (j : ℕ) % lam = (r : ℕ) <;> simp [hj]
        _ = ∑ j : Fin M, (lpNorm k (pE k) (F j)) ^ (2 : ℝ) :=
            Finset.sum_congr rfl fun j _ => by simp
    have hnormr : l2Norm (fun i : Fin m' => lpNorm k (pE k) (resPart r F i))
        ≤ l2Norm (fun j : Fin M => lpNorm k (pE k) (F j)) := by
      rw [l2Norm, l2Norm]
      exact ENNReal.rpow_le_rpow hsumr (by norm_num)
    exact hb.trans (mul_le_mul' le_rfl hnormr)
  -- the ℓ²-norm of each class's summands is measurable
  have hmeas : ∀ r : Fin lam, AEStronglyMeasurable (fun x : E k =>
      ∑ i : Fin m', resPart r F i x) (volume : Measure (E k)) := by
    intro r
    refine (continuous_finsetSum _ (fun i _ => ?_)).aestronglyMeasurable
    by_cases hi : lam * (i : ℕ) + (r : ℕ) < M
    · rw [show resPart r F i = F ⟨lam * (i : ℕ) + (r : ℕ), hi⟩ from resPart_apply r F i hi]
      exact (hF _).continuous
    · rw [show resPart r F i = (0 : E k → ℂ) from resPart_apply_not r F i hi]
      exact continuous_const
  -- the decomposition of the sum
  have hdecomp : (∑ j : Fin M, F j) = ∑ r : Fin lam, ∑ i : Fin m', resPart r F i := by
    have h1 : ∀ r : Fin lam, (∑ i : Fin m', resPart r F i)
        = ∑ j : Fin M, (if (j : ℕ) % lam = (r : ℕ) then F j else 0) := by
      intro r
      have hpad : (∑ i : Fin m', resPart r F i)
          = ∑ i : Fin m', (if lam * (i : ℕ) + (r : ℕ) < M then
              padFin F (lam * (i : ℕ) + (r : ℕ)) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : lam * (i : ℕ) + (r : ℕ) < M <;> simp [resPart, padFin, hi]
      rw [hpad, sum_fin_residue_eq hm (padFin F) r]
      exact Finset.sum_congr rfl fun j _ => by simp
    rw [Finset.sum_congr rfl (fun r _ => h1 r), Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsingle : (∑ r : Fin lam, (if (j : ℕ) % lam = (r : ℕ) then F j else 0)) = F j := by
      refine (Finset.sum_eq_single (⟨(j : ℕ) % lam, Nat.mod_lt _ hlam⟩ : Fin lam) ?_ ?_).trans ?_
      · intro r _ hr
        by_cases h : (j : ℕ) % lam = (r : ℕ)
        · exact absurd (Fin.ext h.symm) hr
        · rw [if_neg h]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
      · simp
    exact hsingle.symm
  have hsumfun : (fun x : E k => ∑ j : Fin M, F j x)
      = fun x : E k => ∑ r : Fin lam, (∑ i : Fin m', resPart r F i x) := by
    funext x
    simpa only [Finset.sum_apply] using congrFun hdecomp x
  have hsumfun2 : (fun x : E k => ∑ r : Fin lam, (∑ i : Fin m', resPart r F i x))
      = ∑ r : Fin lam, (fun x : E k => ∑ i : Fin m', resPart r F i x) := by
    funext x; rw [Finset.sum_apply]
  rw [hsumfun, hsumfun2]
  refine (eLpNorm_sum_le (μ := volume) (p := pE k) (s := Finset.univ)
    (f := fun r : Fin lam => fun x : E k => ∑ i : Fin m', resPart r F i x)
    (one_le_pE k hk)).trans ?_
  calc ∑ r : Fin lam, lpNorm k (pE k) (fun x : E k => ∑ i : Fin m', resPart r F i x)
      ≤ ∑ _r : Fin lam, C * l2Norm (fun j : Fin M => lpNorm k (pE k) (F j)) :=
        Finset.sum_le_sum fun r _ => hbnd r
    _ = (lam : ℝ≥0∞) * (C * l2Norm (fun j : Fin M => lpNorm k (pE k) (F j))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    _ = ((lam : ℝ≥0∞) * C) * l2Norm (fun j : Fin M => lpNorm k (pE k) (F j)) := by
        rw [mul_assoc]

end Submission.Vinogradov
