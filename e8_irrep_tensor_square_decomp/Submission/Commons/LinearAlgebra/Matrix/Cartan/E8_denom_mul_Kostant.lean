import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_small_height_length

set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

/-!
# The Kostant partition function inverts the Weyl denominator (coefficient form)

This file proves the coefficient identity
`(∑_T (-1)^{|T|} e^{-∑_{α ∈ T} α}) · (∑_δ K(δ) e^{-δ}) = 1`,
where `K` is the Kostant partition function of `E₈` truncated at a suitable height bound.

The proof is a single direct computation.  Writing `v` for the list of positive roots and
`f : ι → ℕ` for a multiset of them, the left hand side is the number of pairs `(T, f)` with
`∑_i f_i v_i + ∑_{α ∈ T} α = γ`.  Substituting `g = f + 1_T` turns this into a sum over
`g : ι → ℕ` of the Möbius sums `∑_{Z ⊆ T ⊆ Z ∪ S} (-1)^{|T|}`, where `Z = {i | g i = N + 1}` and
`S = {i | 1 ≤ g i ≤ N}`; these vanish unless `S = ∅`, and a height argument finishes the count.
-/

namespace E8Kostant

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [DecidableEq M]

/-- The vector `∑ i, g i • v i`. -/
def VV (v : ι → M) (g : ι → ℕ) : M := ∑ i, g i • v i

/-- The box of exponents `ι → {0,…,N}`. -/
def box (ι : Type*) [Fintype ι] [DecidableEq ι] (N : ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun _ : ι => Finset.range (N + 1))

lemma mem_box {N : ℕ} {f : ι → ℕ} : f ∈ box ι N ↔ ∀ i, f i ≤ N := by
  rw [box, Fintype.mem_piFinset]
  simp only [Finset.mem_range, Nat.lt_add_one_iff]

lemma sum_indicator (T : Finset ι) (w : ι → M) :
    (∑ i, (if i ∈ T then (1:ℕ) else 0) • w i) = ∑ i ∈ T, w i := by
  have h : ∀ i, (if i ∈ T then (1:ℕ) else 0) • w i = if i ∈ T then w i else 0 := by
    intro i; by_cases hi : i ∈ T <;> simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_ite_mem, Finset.univ_inter]

lemma VV_add_one (v : ι → M) (T : Finset ι) (f : ι → ℕ) :
    VV v (fun i => f i + (if i ∈ T then 1 else 0)) = VV v f + ∑ i ∈ T, v i := by
  rw [VV, VV]
  have h1 : ∀ i, (f i + (if i ∈ T then 1 else 0)) • v i
      = f i • v i + (if i ∈ T then (1:ℕ) else 0) • v i := fun i => by rw [add_smul]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, sum_indicator]

/-- The Kostant-type counting function. -/
def KK (v : ι → M) (N : ℕ) (δ : M) : ℕ :=
  ((box ι N).filter (fun f => VV v f = δ)).card

/-- The Weyl-denominator-times-Kostant sum (type-level version). -/
noncomputable def Srep (v : ι → M) (N : ℕ) (γ : M) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset ι).powerset,
    (-1 : ℤ) ^ T.card * (KK v N (γ - ∑ i ∈ T, v i) : ℤ)

/-- The counting function vanishes below the cone: a solution `f` forces `ht δ ≥ 0`. -/
lemma KK_eq_zero_of_ht_neg (ht : M →+ ℤ) (v : ι → M) (hv : ∀ i, 1 ≤ ht (v i)) (N : ℕ) {δ : M}
    (h : ht δ < 0) : KK v N δ = 0 := by
  rw [KK, Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨f, hf⟩
  rw [Finset.mem_filter, mem_box] at hf
  obtain ⟨-, hV⟩ := hf
  have hht : ht δ = ∑ i, (f i : ℤ) * ht (v i) := by
    rw [← hV, VV, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_nsmul, nsmul_eq_mul]
  have hnn : 0 ≤ ∑ i, (f i : ℤ) * ht (v i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (by linarith [hv i]))
  omega


/-- The "forced" indices `Z(g) = {i | g i = N + 1}`: these have to belong to `T`. -/
def Zset (N : ℕ) (g : ι → ℕ) : Finset ι := Finset.univ.filter (fun i => g i = N + 1)

/-- The "free" indices `S(g) = {i | 1 ≤ g i ≤ N}`; the Möbius sum vanishes unless `S(g) = ∅`. -/
def Sset (N : ℕ) (g : ι → ℕ) : Finset ι := Finset.univ.filter (fun i => 1 ≤ g i ∧ g i ≤ N)

lemma mem_Zset {N : ℕ} {g : ι → ℕ} {i : ι} : i ∈ Zset N g ↔ g i = N + 1 := by
  simp [Zset]

lemma mem_Sset {N : ℕ} {g : ι → ℕ} {i : ι} : i ∈ Sset N g ↔ 1 ≤ g i ∧ g i ≤ N := by
  simp [Sset]

/-- Shifting an exponent function by the indicator of `T` is a bijection from the box
`{0,…,N}^ι` onto the monotone part of the bigger box `{0,…,N+1}^ι`. -/
lemma image_add_indicator (N : ℕ) (T : Finset ι) :
    (box ι N).image (fun f i => f i + (if i ∈ T then 1 else 0)) =
      (box ι (N+1)).filter (fun g => Zset N g ⊆ T ∧ T ⊆ Zset N g ∪ Sset N g) := by
  ext g
  rw [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hf' : ∀ i, f i ≤ N := mem_box.mp hf
    refine ⟨mem_box.mpr (fun i => ?_), ?_, ?_⟩
    · show f i + (if i ∈ T then 1 else 0) ≤ N + 1
      obtain h := hf' i
      by_cases hc : i ∈ T
      · rw [if_pos hc]; omega
      · rw [if_neg hc]; omega
    · intro i hi
      rw [mem_Zset] at hi
      by_cases hc : i ∈ T
      · exact hc
      · have hneq : (fun i => f i + (if i ∈ T then 1 else 0)) i ≠ N + 1 := by
          show f i + (if i ∈ T then 1 else 0) ≠ N + 1
          obtain h := hf' i
          rw [if_neg hc]
          omega
        exact absurd hi hneq
    · intro i hi
      rw [Finset.mem_union, mem_Zset, mem_Sset]
      obtain h := hf' i
      by_cases hc : i ∈ T
      · rw [if_pos hc]
        by_cases hN : f i = N
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, by omega⟩
      · exact absurd hi hc
  · rintro ⟨hg, hZT, hTS⟩
    have hg' : ∀ i, g i ≤ N + 1 := mem_box.mp hg
    have hmem : ∀ i, (fun i => g i - (if i ∈ T then 1 else 0)) i ≤ N := by
      intro i
      obtain h2 := hg' i
      show g i - (if i ∈ T then 1 else 0) ≤ N
      by_cases hc : i ∈ T
      · have hi : i ∈ Zset N g ∪ Sset N g := hTS (by simpa using hc)
        rw [Finset.mem_union, mem_Zset, mem_Sset] at hi
        rw [if_pos hc]
        rcases hi with hi | hi <;> omega
      · have hi : i ∉ Zset N g := fun hh => hc (hZT hh)
        rw [mem_Zset] at hi
        rw [if_neg hc]
        omega
    refine ⟨fun i => g i - (if i ∈ T then 1 else 0), mem_box.mpr hmem, ?_⟩
    funext i
    show (g i - (if i ∈ T then 1 else 0)) + (if i ∈ T then 1 else 0) = g i
    by_cases hc : i ∈ T
    · have hi : i ∈ Zset N g ∪ Sset N g := hTS (by simpa using hc)
      rw [Finset.mem_union, mem_Zset, mem_Sset] at hi
      rw [if_pos hc]
      rcases hi with hi | hi <;> omega
    · rw [if_neg hc]
      simp

/-- Möbius sum over the subfinsets sandwiched between `Z` and `Z ∪ S`. -/
lemma sum_powerset_filter_subset (Z S : Finset ι) (h : Disjoint Z S) :
    (∑ T ∈ ((Finset.univ : Finset ι).powerset).filter (fun T => Z ⊆ T ∧ T ⊆ Z ∪ S),
        (-1 : ℤ) ^ T.card) = if S = ∅ then (-1 : ℤ) ^ Z.card else 0 := by
  have hset : ((Finset.univ : Finset ι).powerset).filter (fun T => Z ⊆ T ∧ T ⊆ Z ∪ S)
      = S.powerset.image (fun T'' => Z ∪ T'') := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, Finset.subset_univ,
      true_and]
    constructor
    · rintro ⟨hZT, hTS⟩
      refine ⟨T \ Z, fun x hx => ?_, Finset.union_sdiff_of_subset hZT⟩
      have hxT : x ∈ T := (Finset.mem_sdiff.mp hx).1
      have hxZ : x ∉ Z := (Finset.mem_sdiff.mp hx).2
      rcases Finset.mem_union.mp (hTS hxT) with h' | h'
      · exact absurd h' hxZ
      · exact h'
    · rintro ⟨T'', hT'', rfl⟩
      refine ⟨Finset.subset_union_left, fun x hx => ?_⟩
      rcases Finset.mem_union.mp hx with h' | h'
      · exact Finset.mem_union_left _ h'
      · exact Finset.mem_union_right _ (hT'' h')
  have hinj : Set.InjOn (fun T'' : Finset ι => Z ∪ T'') ↑(S.powerset) := by
    intro A hA B hB hab
    have hAsub : A ⊆ S := Finset.mem_powerset.mp (by simpa using hA)
    have hBsub : B ⊆ S := Finset.mem_powerset.mp (by simpa using hB)
    have hab' : Z ∪ A = Z ∪ B := hab
    ext x
    have h1 : x ∈ Z ∪ A ↔ x ∈ Z ∪ B := by rw [hab']
    constructor
    · intro hx
      have hxS : x ∈ S := hAsub hx
      rcases Finset.mem_union.mp (h1.mp (Finset.mem_union.mpr (Or.inr hx))) with hh | hh
      · exact absurd hh (Finset.disjoint_right.mp h hxS)
      · exact hh
    · intro hx
      have hxS : x ∈ S := hBsub hx
      rcases Finset.mem_union.mp (h1.mpr (Finset.mem_union.mpr (Or.inr hx))) with hh | hh
      · exact absurd hh (Finset.disjoint_right.mp h hxS)
      · exact hh
  rw [hset, Finset.sum_image hinj]
  have hsplit : ∀ T'' ∈ S.powerset,
      (-1 : ℤ) ^ (Z ∪ T'').card = (-1 : ℤ) ^ Z.card * (-1 : ℤ) ^ T''.card := by
    intro T'' hT''
    rw [Finset.card_union_of_disjoint (h.mono_right (Finset.mem_powerset.mp hT'')), pow_add]
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  rw [Finset.sum_powerset_neg_one_pow_card]
  by_cases hS : S = ∅ <;> simp [hS]

/-- `Z(g)` and `S(g)` are disjoint. -/
lemma disjoint_Zset_Sset (N : ℕ) (g : ι → ℕ) : Disjoint (Zset N g) (Sset N g) := by
  rw [Finset.disjoint_left]
  intro i hi hiS
  rw [mem_Zset] at hi
  rw [mem_Sset] at hiS
  omega

/-- Step 1: rewrite `Srep` as a double sum with the shifted exponent. -/
lemma Srep_eq_double (v : ι → M) (N : ℕ) (γ : M) :
    Srep v N γ = ∑ T ∈ (Finset.univ : Finset ι).powerset, ∑ f ∈ box ι N,
      (-1 : ℤ) ^ T.card *
        (if VV v (fun i => f i + (if i ∈ T then 1 else 0)) = γ then 1 else 0) := by
  rw [Srep]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [KK, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  congr 1
  rw [VV_add_one v T f]
  simp only [eq_sub_iff_add_eq]

/-- Step 2: rewrite the inner sum as a sum over the shifted box. -/
lemma inner_eq (v : ι → M) (N : ℕ) (γ : M) (T : Finset ι) :
    (∑ f ∈ box ι N, (-1 : ℤ) ^ T.card *
        (if VV v (fun i => f i + (if i ∈ T then 1 else 0)) = γ then 1 else 0))
      = ∑ g ∈ (box ι (N+1)).filter
            (fun g => Zset N g ⊆ T ∧ T ⊆ Zset N g ∪ Sset N g),
          (-1 : ℤ) ^ T.card * (if VV v g = γ then 1 else 0) := by
  let F : (ι → ℕ) → ℤ := fun h => (-1 : ℤ) ^ T.card * (if VV v h = γ then 1 else 0)
  have hinj : Set.InjOn (fun f : ι → ℕ => fun i => f i + (if i ∈ T then 1 else 0)) ↑(box ι N) := by
    intro f _ g _ hfg
    funext i
    have := congrFun hfg i
    simp only at this
    omega
  have him : (∑ h ∈ (box ι N).image (fun f : ι → ℕ => fun i => f i + (if i ∈ T then 1 else 0)),
        F h) = ∑ f ∈ box ι N, F (fun i => f i + (if i ∈ T then 1 else 0)) :=
    Finset.sum_image hinj
  have hkey : (∑ f ∈ box ι N, (-1 : ℤ) ^ T.card *
        (if VV v (fun i => f i + (if i ∈ T then 1 else 0)) = γ then 1 else 0))
      = ∑ f ∈ box ι N, F (fun i => f i + (if i ∈ T then 1 else 0)) := rfl
  rw [hkey, ← him, image_add_indicator N T]

lemma Zset_indicator (N : ℕ) (Z : Finset ι) :
    Zset N (fun i => if i ∈ Z then N + 1 else 0) = Z := by
  ext i
  rw [mem_Zset]
  by_cases h : i ∈ Z <;> simp [h]

lemma Sset_indicator (N : ℕ) (Z : Finset ι) :
    Sset N (fun i => if i ∈ Z then N + 1 else 0) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨i, hi⟩
  rw [mem_Sset] at hi
  by_cases h : i ∈ Z <;> simp [h] at hi

lemma VV_indicator (v : ι → M) (N : ℕ) (Z : Finset ι) :
    VV v (fun i => if i ∈ Z then N + 1 else 0) = (N + 1) • ∑ i ∈ Z, v i := by
  rw [VV]
  have h : ∀ i, (if i ∈ Z then N + 1 else 0) • v i
      = if i ∈ Z then (N + 1) • v i else (0 : M) := by
    intro i; by_cases hi : i ∈ Z <;> simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.smul_sum]

/-- The map `Z ↦ (i ↦ if i ∈ Z then N+1 else 0)` is injective. -/
lemma injOn_indicator (N : ℕ) :
    Set.InjOn (fun Z : Finset ι => fun i => if i ∈ Z then N + 1 else 0) ↑(Finset.univ : Finset ι).powerset := by
  intro A _ B _ hAB
  ext i
  have h : (if i ∈ A then N + 1 else 0) = (if i ∈ B then N + 1 else 0) := congrFun hAB i
  by_cases hA : i ∈ A
  · have hB : i ∈ B := by
      by_contra hB
      rw [if_pos hA, if_neg hB] at h
      omega
    simp [hA, hB]
  · have hB : i ∉ B := by
      intro hB
      rw [if_neg hA, if_pos hB] at h
      omega
    simp [hA, hB]

/-- The functions in the big box with `S(g) = ∅` are exactly the dilated indicators. -/
lemma image_indicator (N : ℕ) :
    (box ι (N+1)).filter (fun g => Sset N g = ∅)
      = (Finset.univ : Finset ι).powerset.image (fun Z => fun i => if i ∈ Z then N + 1 else 0) := by
  ext g
  rw [Finset.mem_filter, mem_box, Finset.mem_image]
  constructor
  · intro ⟨hg, hS⟩
    refine ⟨Zset N g, Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    funext i
    have h2 : ¬ (1 ≤ g i ∧ g i ≤ N) := by
      intro hh
      have hmem : i ∈ Sset N g := by rw [mem_Sset]; exact hh
      rw [hS] at hmem
      exact Finset.notMem_empty i hmem
    show (if i ∈ Zset N g then N + 1 else 0) = g i
    by_cases hi : i ∈ Zset N g
    · rw [if_pos hi, mem_Zset.mp hi]
    · rw [if_neg hi]
      have hi' : g i ≠ N + 1 := fun h => hi (mem_Zset.mpr h)
      have hle : g i ≤ N + 1 := hg i
      have h3 : g i < 1 ∨ N < g i := by
        by_contra hc
        push Not at hc
        exact h2 hc
      rcases h3 with h3 | h3 <;> omega
  · rintro ⟨Z, _, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · show (if i ∈ Z then N + 1 else 0) ≤ N + 1
      by_cases hi : i ∈ Z
      · rw [if_pos hi]
      · rw [if_neg hi]; omega
    · rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨i, hi⟩
      rw [mem_Sset] at hi
      by_cases hZ : i ∈ Z <;> simp [hZ] at hi

/-- **The general coefficient identity.**  For any finite family of vectors whose heights are
at least one, the Weyl-denominator sum times the (bounded) Kostant partition function is the
delta function at the origin. -/
theorem Srep_main (ht : M →+ ℤ) (v : ι → M) (hv : ∀ i, 1 ≤ ht (v i)) (N : ℕ) (γ : M)
    (hγ : ht γ ≤ (N : ℤ)) : Srep v N γ = if γ = 0 then 1 else 0 := by
  rw [Srep_eq_double]
  rw [Finset.sum_congr rfl (fun T _ => inner_eq v N γ T)]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  have stepC : ∀ g : ι → ℕ,
      (∑ T ∈ (Finset.univ : Finset ι).powerset,
          (if Zset N g ⊆ T ∧ T ⊆ Zset N g ∪ Sset N g then
            (-1 : ℤ) ^ T.card * (if VV v g = γ then 1 else 0) else 0))
        = (if Sset N g = ∅ then (-1 : ℤ) ^ (Zset N g).card else 0) *
            (if VV v g = γ then 1 else 0) := by
    intro g
    have h1 : ∀ T : Finset ι,
        (if Zset N g ⊆ T ∧ T ⊆ Zset N g ∪ Sset N g then
          (-1 : ℤ) ^ T.card * (if VV v g = γ then 1 else 0) else 0)
          = (if Zset N g ⊆ T ∧ T ⊆ Zset N g ∪ Sset N g then (-1 : ℤ) ^ T.card else 0) *
              (if VV v g = γ then 1 else 0) := by
      intro T
      by_cases h : Zset N g ⊆ T ∧ T ⊆ Zset N g ∪ Sset N g <;> simp [h]
    rw [Finset.sum_congr rfl (fun T _ => h1 T), ← Finset.sum_mul, ← Finset.sum_filter,
      sum_powerset_filter_subset (Zset N g) (Sset N g) (disjoint_Zset_Sset N g)]
  rw [Finset.sum_congr rfl (fun g _ => stepC g)]
  have stepD : (∑ g ∈ box ι (N+1),
        (if Sset N g = ∅ then (-1 : ℤ) ^ (Zset N g).card else 0) *
          (if VV v g = γ then 1 else 0))
      = ∑ Z ∈ (Finset.univ : Finset ι).powerset,
          (-1 : ℤ) ^ Z.card * (if (N + 1) • (∑ i ∈ Z, v i) = γ then 1 else 0) := by
    have h1 : ∀ g ∈ box ι (N+1),
        (if Sset N g = ∅ then (-1 : ℤ) ^ (Zset N g).card else 0) *
            (if VV v g = γ then 1 else 0)
          = if Sset N g = ∅ then
              (-1 : ℤ) ^ (Zset N g).card * (if VV v g = γ then 1 else 0) else 0 := by
      intro g _
      by_cases h : Sset N g = ∅ <;> simp [h]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, image_indicator N,
      Finset.sum_image (injOn_indicator N)]
    refine Finset.sum_congr rfl (fun Z _ => ?_)
    show (-1 : ℤ) ^ (Zset N (fun i => if i ∈ Z then N + 1 else 0)).card *
          (if VV v (fun i => if i ∈ Z then N + 1 else 0) = γ then 1 else 0)
      = (-1 : ℤ) ^ Z.card * (if (N + 1) • (∑ i ∈ Z, v i) = γ then 1 else 0)
    rw [Zset_indicator N Z, VV_indicator v N Z]
  rw [stepD]
  have hsum := Finset.sum_eq_single (s := (Finset.univ : Finset ι).powerset)
    (f := fun Z => (-1 : ℤ) ^ Z.card * (if (N + 1) • (∑ i ∈ Z, v i) = γ then 1 else 0)) ∅
    ?_ ?_
  · rw [hsum]
    simp only [Finset.card_empty, pow_zero, one_mul, Finset.sum_empty, nsmul_zero]
    exact if_congr eq_comm rfl rfl
  · intro Z _ hne
    have hC : ¬ ((N + 1) • (∑ i ∈ Z, v i) = γ) := by
      intro hc
      have hσ : (1 : ℤ) ≤ ∑ i ∈ Z, ht (v i) := by
        have hcard : 1 ≤ Z.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
        calc (1 : ℤ) ≤ (Z.card : ℤ) := by exact_mod_cast hcard
          _ = ∑ i ∈ Z, (1 : ℤ) := by simp
          _ ≤ ∑ i ∈ Z, ht (v i) := Finset.sum_le_sum (fun i _ => hv i)
      have h1 : ht γ = (N + 1) * (∑ i ∈ Z, ht (v i)) := by
        rw [← hc, map_nsmul, map_sum, nsmul_eq_mul]
        push_cast
        ring
      have h2 : ((N : ℤ) + 1) ≤ ht γ := by
        rw [h1]
        nlinarith [hσ, Nat.cast_nonneg (α := ℤ) N]
      omega
    rw [if_neg hC, mul_zero]
  · intro h
    exact absurd (Finset.mem_powerset.mpr (Finset.empty_subset _)) h

/-! ## The finset form: the positive roots as a finset of vectors -/

section FinsetForm

variable {M : Type*} [AddCommGroup M] [DecidableEq M]

/-- The subset of `M` underlying a subset `A` of a subtype `↥L`. -/
def tr (L : Finset M) (A : Finset ↥L) : Finset M := A.image Subtype.val

lemma mem_tr' {L : Finset M} {A : Finset ↥L} {x : M} :
    x ∈ tr L A ↔ ∃ a : ↥L, (a : M) = x ∧ a ∈ A := by
  rw [tr, Finset.mem_image]
  exact ⟨fun h => h.elim fun b hb => ⟨b, hb.2, hb.1⟩,
    fun h => h.elim fun b hb => ⟨b, hb.2, hb.1⟩⟩

lemma mem_tr {L : Finset M} {A : Finset ↥L} {a : ↥L} : (a : M) ∈ tr L A ↔ a ∈ A := by
  rw [mem_tr']
  exact ⟨fun h => h.elim fun b hb => (Subtype.ext hb.1) ▸ hb.2,
    fun ha => ⟨a, rfl, ha⟩⟩

/-- **The identity for a general finset of vectors.**  This is the form in which the theorem is
applied to the finset `E8posRoots.P` of positive roots. -/
theorem Srep_finset (L : Finset M)
    (ht : M →+ ℤ) (hht : ∀ a ∈ L, 1 ≤ ht a) (N : ℕ) (γ : M) (hγ : ht γ ≤ (N : ℤ)) :
    (∑ T ∈ L.powerset, (-1 : ℤ) ^ T.card *
      ((Fintype.piFinset (fun _ : ↥L => Finset.range (N + 1))).filter
        (fun f => ∑ a : ↥L, f a • (a : M) = γ - ∑ a ∈ T, a)).card)
      = if γ = 0 then 1 else 0 := by
  have him : ((Finset.univ : Finset ↥L).powerset).image (tr L) = L.powerset := by
    ext T
    rw [Finset.mem_image, Finset.mem_powerset]
    constructor
    · rintro ⟨A, -, rfl⟩
      exact Finset.image_subset_iff.mpr (fun a _ => a.2)
    · intro hT
      refine ⟨L.attach.filter (fun a => (a : M) ∈ T),
        Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      ext x
      rw [mem_tr']
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨a, hax, -, haT⟩
        rwa [← hax]
      · intro hx
        exact ⟨⟨x, hT hx⟩, rfl, by simp, by simpa using hx⟩
  have hinj : Set.InjOn (tr L) ↑(Finset.univ : Finset ↥L).powerset := by
    intro A _ B _ hAB
    ext a
    have h : (a : M) ∈ tr L A ↔ (a : M) ∈ tr L B := by rw [hAB]
    simpa only [mem_tr] using h
  have hmain : Srep (fun a : ↥L => (a : M)) N γ = if γ = 0 then 1 else 0 :=
    Srep_main ht (fun a : ↥L => (a : M)) (fun a => hht a a.2) N γ hγ
  rw [← hmain, Srep]
  rw [← him, Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  have h1 : (tr L A).card = A.card := by
    rw [tr]
    exact Finset.card_image_of_injOn (fun a _ b _ h => Subtype.ext h)
  have h2 : (∑ a ∈ tr L A, (a : M)) = ∑ a ∈ A, (a : M) := by
    rw [tr]
    exact Finset.sum_image (f := fun x : M => x) (s := A) (g := Subtype.val)
      (fun a _ b _ h => Subtype.ext h)
  rw [h1, h2]
  rfl

end FinsetForm

end E8Kostant

/-- The height of `E₈` as an additive homomorphism. -/
def e8htHom : (Fin 8 → ℤ) →+ ℤ where
  toFun := E8NormTwo.e8ht
  map_zero' := by
    have h := e8ht_add (0 : Fin 8 → ℤ) 0
    simp only [add_zero] at h
    omega
  map_add' := fun a b => e8ht_add a b

/-- **The Kostant partition function is the inverse of the Weyl denominator** — the coefficient
form of the identity `(∏_{α>0}(1 - e^{-α})) · (∏_{α>0}(1 - e^{-α})^{-1}) = 1`.

Context.  `Commons.LinearAlgebra.Matrix.Cartan.E8posRoots.P` is the finset of the `120` positive
roots of `E₈` (file `Submission/Commons/LinearAlgebra/Matrix/Cartan/E8_posRoots_finset.lean`);
`Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.e8ht` is the height `∑ᵢ (A⁻¹γ)ᵢ`
(file `Submission/Commons/LinearAlgebra/Matrix/Cartan/E8_norm_two_conj_simple.lean`).
`K δ` below is the number of *multisets* of positive roots with sum `δ`, encoded as the number of
`f : ↥P → ℕ` with all values `≤ (e8ht γ).toNat` and `∑ α, f α • α = δ`.  The height bound is
harmless: any multiset summing to a cone element `δ` satisfies `∑ f α ≤ e8ht δ`, and for every
`T` for which `γ - ∑_{α∈T} α ∈ ℕΦ⁺` one has `e8ht (γ - ∑_{α∈T} α) ≤ e8ht γ` (heights add on the
cone); for `δ ∉ ℕΦ⁺` there are no solutions at all.

Proof ingredients (recorded so the telescoping argument is not rediscovered).  Order the positive
roots `α₁,…,α₁₂₀` and let `K_n(γ) := #{f : Fin n → ℕ | ∑ i, f i • α_i = γ}`.  Splitting off the
last root gives, for every `k`,
`K_{n+1}(γ - k·α_{n+1}) = ∑_{j ≥ k} K_n(γ - j·α_{n+1})`, hence the telescoping relation
`K_{n+1}(γ) - K_{n+1}(γ - α_{n+1}) = K_n(γ)`, i.e. `(1 - e^{-α_{n+1}})·K_{n+1} = K_n`, and the
product `∏ (1 - e^{-α}) · K` telescopes from `K_0 = δ_0` to `1`.  (A bounded version of the
telescoping relation, formulated with `f : ↥P → Fin (N+1)`, is what has to be formalized; the
bound `N = (e8ht γ).toNat` must be chosen large enough for the induction.) -/
theorem E8_denom_mul_Kostant (γ : Fin 8 → ℤ) :
    (∑ T ∈ E8posRoots.P.powerset, (-1 : ℤ) ^ T.card *
      ((Fintype.piFinset
          (fun _ : ↥E8posRoots.P => Finset.range ((E8NormTwo.e8ht γ).toNat + 1))).filter
        (fun f => ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = γ - ∑ α ∈ T, α)).card)
      = if γ = 0 then 1 else 0 := by
  by_cases hpos : 0 ≤ E8NormTwo.e8ht γ
  · have hγ : E8NormTwo.e8ht γ ≤ (((E8NormTwo.e8ht γ).toNat : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hpos]
    exact E8Kostant.Srep_finset E8posRoots.P e8htHom (fun a ha => one_le_e8ht_of_mem_P ha)
      ((E8NormTwo.e8ht γ).toNat) γ hγ
  · push Not at hpos
    have hne : γ ≠ 0 := by
      intro h
      rw [h] at hpos
      have h0 : E8NormTwo.e8ht (0 : Fin 8 → ℤ) = 0 := e8htHom.map_zero
      rw [h0] at hpos
      exact absurd hpos (lt_irrefl 0)
    rw [if_neg hne]
    refine Finset.sum_eq_zero (fun T hT => ?_)
    rw [mul_eq_zero]
    right
    have hσ : 0 ≤ E8NormTwo.e8ht (∑ α ∈ T, α) := by
      rw [e8ht_sum]
      exact Finset.sum_nonneg (fun a ha => by
        have := one_le_e8ht_of_mem_P (Finset.mem_powerset.mp hT ha)
        omega)
    have hneg : E8NormTwo.e8ht (γ - ∑ α ∈ T, α) < 0 := by
      rw [e8ht_sub]; omega
    have hz := E8Kostant.KK_eq_zero_of_ht_neg e8htHom (fun a : ↥E8posRoots.P => (a : Fin 8 → ℤ))
      (fun a => one_le_e8ht_of_mem_P a.2) ((E8NormTwo.e8ht γ).toNat) hneg
    change (((E8Kostant.KK (fun a : ↥E8posRoots.P => (a : Fin 8 → ℤ))
      ((E8NormTwo.e8ht γ).toNat) (γ - ∑ α ∈ T, α) : ℕ)) : ℤ) = 0
    exact_mod_cast hz

end Commons.LinearAlgebra.Matrix.Cartan
