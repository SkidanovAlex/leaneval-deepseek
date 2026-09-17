import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_norm_two_conj_simple

/-!
# The `E₈` lattice points of squared length at most `10`

This file proves the existence of an explicit list of the lattice points `v : Fin 8 → ℤ` with
`qZ v ≤ 10` (where `qZ` is the squared length in the fundamental-weight coordinates, see
`Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ`) together with the norm distribution
`1, 240, 2160, 6720, 17520, 30240`.

The proof proceeds by exhibiting an explicit isometry `Phi` between `ℤ^8` with the form `qZ` and
the standard model `2Λ(E₈) = {y : all coordinates even or all odd, 4 ∣ ∑ y}` of the doubled `E₈`
lattice, where the squared length is the ordinary dot product.  The counts in the standard model
are then evaluated by a computable dynamic program.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

namespace E8Lat


/-- Number of `f : Fin k → ℤ` with `∑ i, (f i)^2 = s`. -/
noncomputable def SqC (k : ℕ) (s : ℤ) : ℕ :=
  Set.ncard {f : Fin k → ℤ | ∑ i, (f i)^2 = s}

/-- Number of `f : Fin k → ℤ` with `∑ i, ((f i)^2 + f i) = s`. -/
noncomputable def WqT (k : ℕ) (s : ℤ) : ℕ :=
  Set.ncard {f : Fin k → ℤ | ∑ i, ((f i)^2 + f i) = s}

lemma wq_term_nonneg (a : ℤ) : (0:ℤ) ≤ a^2 + a := by nlinarith [sq_nonneg (a + 1/2)]

lemma wq_term_le {a s : ℤ} (h : a^2 + a ≤ s) : -(s+1) ≤ a ∧ a ≤ s := by
  constructor <;> nlinarith [h, wq_term_nonneg a, sq_nonneg (a + 1)]

lemma wq_term_le' {a s : ℤ} (h : a^2 + a ≤ s) : -s - 1 ≤ a ∧ a ≤ s := by
  have h1 := wq_term_le h
  constructor <;> omega

lemma sqSol_finite (k : ℕ) (s : ℤ) : ({f : Fin k → ℤ | ∑ i, (f i)^2 = s}).Finite := by
  rcases lt_or_ge s 0 with hs | hs
  · have hempty : {f : Fin k → ℤ | ∑ i, (f i)^2 = s} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hf
      have h1 : (0:ℤ) ≤ ∑ i, (f i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
      omega
    rw [hempty]; exact Set.finite_empty
  · refine (Set.Finite.pi (fun _ : Fin k => (Finset.finite_toSet (Finset.Icc (-s) s)))).subset ?_
    intro f hf
    simp only [Set.mem_setOf_eq] at hf
    rw [Set.mem_pi]
    intro i _
    simp only [Finset.mem_coe, Finset.mem_Icc]
    have h1 : (f i)^2 ≤ s := by
      have := Finset.single_le_sum (f := fun i => (f i)^2) (fun i _ => sq_nonneg (f i))
        (Finset.mem_univ i)
      omega
    constructor <;> nlinarith [h1]

lemma wqSol_finite (k : ℕ) (s : ℤ) : ({f : Fin k → ℤ | ∑ i, ((f i)^2 + f i) = s}).Finite := by
  rcases lt_or_ge s 0 with hs | hs
  · have hempty : {f : Fin k → ℤ | ∑ i, ((f i)^2 + f i) = s} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hf
      have h1 : (0:ℤ) ≤ ∑ i, ((f i)^2 + f i) := Finset.sum_nonneg (fun i _ => wq_term_nonneg _)
      omega
    rw [hempty]; exact Set.finite_empty
  · refine (Set.Finite.pi (fun _ : Fin k => (Finset.finite_toSet (Finset.Icc (-(s+1)) s)))).subset ?_
    intro f hf
    simp only [Set.mem_setOf_eq] at hf
    rw [Set.mem_pi]
    intro i _
    simp only [Finset.mem_coe, Finset.mem_Icc]
    have h1 : (f i)^2 + f i ≤ s := by
      have := Finset.single_le_sum (f := fun i => ((f i)^2 + f i))
        (fun i _ => wq_term_nonneg _) (Finset.mem_univ i)
      omega
    exact wq_term_le h1

/-- `snocZ g a` appends `a` to the vector `g`. -/
def snocZ {k : ℕ} (g : Fin k → ℤ) (a : ℤ) : Fin (k+1) → ℤ := Fin.lastCases a g

@[simp] lemma snocZ_last {k : ℕ} (g : Fin k → ℤ) (a : ℤ) : snocZ g a (Fin.last k) = a :=
  Fin.lastCases_last

@[simp] lemma snocZ_castSucc {k : ℕ} (g : Fin k → ℤ) (a : ℤ) (i : Fin k) :
    snocZ g a (Fin.castSucc i) = g i := Fin.lastCases_castSucc i

lemma snocZ_inj {k : ℕ} {g₁ g₂ : Fin k → ℤ} {a b : ℤ} (h : snocZ g₁ a = snocZ g₂ b) :
    g₁ = g₂ ∧ a = b := by
  constructor
  · funext i
    have := congr_fun h (Fin.castSucc i)
    simpa using this
  · have := congr_fun h (Fin.last k)
    simpa using this

lemma snocZ_surj {k : ℕ} (f : Fin (k+1) → ℤ) :
    snocZ (fun i => f (Fin.castSucc i)) (f (Fin.last k)) = f := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j; simp

lemma ncard_biUnion_finset {ι α : Type*} (t : Finset ι) (S : ι → Set α)
    (hfin : ∀ i ∈ t, (S i).Finite) (hdisj : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (S i) (S j)) :
    (⋃ i ∈ t, S i).ncard = ∑ i ∈ t, (S i).ncard := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      have hdisj' : Disjoint (S a) (⋃ i ∈ t, S i) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        rw [Set.mem_iUnion₂] at hx'
        obtain ⟨i, hi, hxi⟩ := hx'
        have hne : a ≠ i := fun h => ha (h ▸ hi)
        have hd := hdisj a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi) hne
        exact Set.notMem_empty x (hd.le_bot ⟨hx, hxi⟩)
      rw [Finset.set_biUnion_insert,
        Set.ncard_union_eq hdisj' (hfin a (Finset.mem_insert_self a t))
          (Set.Finite.biUnion t.finite_toSet (fun i hi => hfin i (Finset.mem_insert_of_mem hi))),
        ih (fun i hi => hfin i (Finset.mem_insert_of_mem hi))
           (fun i hi j hj hij => hdisj i (Finset.mem_insert_of_mem hi) j
              (Finset.mem_insert_of_mem hj) hij),
        Finset.sum_insert ha]

/-- The embedding `j ↦ j - s` of `ℕ` into `ℤ`. -/
def shiftEmb (s : ℕ) : ℕ ↪ ℤ :=
  ⟨fun j : ℕ => (j:ℤ) - (s:ℤ), by intro a b h; simp only at h; omega⟩

@[simp] lemma shiftEmb_apply (s j : ℕ) : shiftEmb s j = (j:ℤ) - (s:ℤ) := rfl

/-- The embedding `j ↦ j - s - 1` of `ℕ` into `ℤ`. -/
def shiftEmb' (s : ℕ) : ℕ ↪ ℤ :=
  ⟨fun j : ℕ => (j:ℤ) - (s:ℤ) - 1, by intro a b h; simp only at h; omega⟩

@[simp] lemma shiftEmb'_apply (s j : ℕ) : shiftEmb' s j = (j:ℤ) - (s:ℤ) - 1 := rfl

lemma Icc_eq_map_range (s : ℕ) :
    Finset.Icc (-(s:ℤ)) (s:ℤ) = (Finset.range (2*s+1)).map (shiftEmb s) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, shiftEmb_apply]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨(a + (s:ℤ)).toNat, ?_, ?_⟩
    · have : a + (s:ℤ) < 2*s+1 := by omega
      omega
    · have h3 : (0:ℤ) ≤ a + (s:ℤ) := by omega
      rw [Int.toNat_of_nonneg h3]; ring
  · rintro ⟨j, hj, hja⟩
    rw [← hja]
    constructor <;> omega

lemma sum_Icc_eq_sum_range (s : ℕ) (f : ℤ → ℕ) :
    ∑ a ∈ Finset.Icc (-(s:ℤ)) (s:ℤ), f a
      = ∑ j ∈ Finset.range (2*s+1), f (shiftEmb s j) := by
  rw [Icc_eq_map_range, Finset.sum_map]

lemma Icc_eq_map_range' (s : ℕ) :
    Finset.Icc (-(s:ℤ)-1) (s:ℤ) = (Finset.range (2*s+2)).map (shiftEmb' s) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, shiftEmb'_apply]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨(a + (s:ℤ) + 1).toNat, ?_, ?_⟩
    · have : a + (s:ℤ) + 1 < 2*s+2 := by omega
      omega
    · have h3 : (0:ℤ) ≤ a + (s:ℤ) + 1 := by omega
      rw [Int.toNat_of_nonneg h3]; ring
  · rintro ⟨j, hj, hja⟩
    rw [← hja]
    have hj' : (j:ℤ) < 2*(s:ℤ)+2 := by exact_mod_cast hj
    constructor
    · linarith [Int.natCast_nonneg j]
    · linarith

lemma sum_Icc_eq_sum_range' (s : ℕ) (f : ℤ → ℕ) :
    ∑ a ∈ Finset.Icc (-(s:ℤ)-1) (s:ℤ), f a
      = ∑ j ∈ Finset.range (2*s+2), f (shiftEmb' s j) := by
  rw [Icc_eq_map_range', Finset.sum_map]

lemma SqC_succZ (k : ℕ) (s : ℤ) :
    SqC (k+1) s = ∑ a ∈ Finset.Icc (-s) s, SqC k (s - a^2) := by
  classical
  have hset : {f : Fin (k+1) → ℤ | ∑ i, (f i)^2 = s}
      = ⋃ a ∈ (Finset.Icc (-s) s),
          (fun g : Fin k → ℤ => snocZ g a) '' {g : Fin k → ℤ | ∑ i, (g i)^2 = s - a^2} := by
    ext f
    rw [Set.mem_setOf_eq, Set.mem_iUnion₂]
    constructor
    · intro hf
      refine ⟨f (Fin.last k), ?_, fun i => f (Fin.castSucc i), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        have h1 : (f (Fin.last k))^2 ≤ s := by
          have := Finset.single_le_sum (f := fun i : Fin (k+1) => (f i)^2)
            (fun i _ => sq_nonneg (f i)) (Finset.mem_univ (Fin.last k))
          omega
        constructor <;> nlinarith [h1]
      · rw [Set.mem_setOf_eq, ← hf, Fin.sum_univ_castSucc]; ring
      · simp only [snocZ_surj]
    · rintro ⟨a, ha, g, hg, hreal⟩
      rw [Set.mem_setOf_eq] at hg
      rw [← hreal, Fin.sum_univ_castSucc]
      simp only [snocZ_castSucc, snocZ_last]
      omega
  rw [SqC, hset, ncard_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Set.ncard_image_of_injective, SqC]
    intro x y hxy
    exact (snocZ_inj hxy).1
  · intro a _; exact Set.Finite.image _ (sqSol_finite k (s - a^2))
  · intro a ha b hb hab
    rw [Set.disjoint_left]
    intro x hx hy
    rw [Set.mem_image] at hx hy
    obtain ⟨g1, -, hg1⟩ := hx
    obtain ⟨g2, -, hg2⟩ := hy
    have h2 : snocZ g1 a (Fin.last k) = snocZ g2 b (Fin.last k) := by rw [hg1, hg2]
    simp only [snocZ_last] at h2
    exact hab h2

lemma WqT_succZ (k : ℕ) (s : ℤ) :
    WqT (k+1) s = ∑ a ∈ Finset.Icc (-s-1) s, WqT k (s - (a^2 + a)) := by
  classical
  have hset : {f : Fin (k+1) → ℤ | ∑ i, ((f i)^2 + f i) = s}
      = ⋃ a ∈ (Finset.Icc (-s-1) s),
          (fun g : Fin k → ℤ => snocZ g a) '' {g : Fin k → ℤ | ∑ i, ((g i)^2 + g i) = s - (a^2+a)} := by
    ext f
    rw [Set.mem_setOf_eq, Set.mem_iUnion₂]
    constructor
    · intro hf
      refine ⟨f (Fin.last k), ?_, fun i => f (Fin.castSucc i), ?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact wq_term_le' (by
          have := Finset.single_le_sum (f := fun i : Fin (k+1) => ((f i)^2 + f i))
            (fun i _ => wq_term_nonneg _) (Finset.mem_univ (Fin.last k))
          omega)
      · rw [Set.mem_setOf_eq, ← hf, Fin.sum_univ_castSucc]; ring
      · simp only [snocZ_surj]
    · rintro ⟨a, ha, g, hg, hreal⟩
      rw [Set.mem_setOf_eq] at hg
      rw [← hreal, Fin.sum_univ_castSucc]
      simp only [snocZ_castSucc, snocZ_last]
      omega
  rw [WqT, hset, ncard_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Set.ncard_image_of_injective, WqT]
    intro x y hxy
    exact (snocZ_inj hxy).1
  · intro a _; exact Set.Finite.image _ (wqSol_finite k (s - (a^2+a)))
  · intro a ha b hb hab
    rw [Set.disjoint_left]
    intro x hx hy
    rw [Set.mem_image] at hx hy
    obtain ⟨g1, -, hg1⟩ := hx
    obtain ⟨g2, -, hg2⟩ := hy
    have h2 : snocZ g1 a (Fin.last k) = snocZ g2 b (Fin.last k) := by rw [hg1, hg2]
    simp only [snocZ_last] at h2
    exact hab h2

lemma SqC_succ (k s : ℕ) :
    SqC (k+1) (s:ℤ) = ∑ j ∈ Finset.range (2*s+1), SqC k ((s:ℤ) - ((j:ℤ) - (s:ℤ))^2) := by
  rw [SqC_succZ k (s:ℤ), sum_Icc_eq_sum_range]
  simp only [shiftEmb_apply]

lemma WqT_succ (k s : ℕ) :
    WqT (k+1) (s:ℤ)
      = ∑ j ∈ Finset.range (2*s+2),
          WqT k ((s:ℤ) - (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1))) := by
  rw [WqT_succZ k (s:ℤ), sum_Icc_eq_sum_range']
  simp only [shiftEmb'_apply]

/-! ## The computable dynamic programs -/

def zbase (N : ℕ) : List ℕ := (List.range (N+1)).map (fun s => if s = 0 then 1 else 0)

def zstep (N : ℕ) (v : List ℕ) : List ℕ :=
  (List.range (N+1)).map (fun s =>
    ∑ j ∈ Finset.range (2*s+1),
      (if ((j:ℤ) - (s:ℤ))^2 ≤ (s:ℤ)
       then v.getD (s - (((j:ℤ) - (s:ℤ))^2).toNat) 0 else 0))

def zfin (N k : ℕ) : List ℕ := (List.range k).foldl (fun v _ => zstep N v) (zbase N)

def zcnt (N : ℕ) : ℕ := (zfin N 8).getD N 0

def wbase (N : ℕ) : List ℕ := (List.range (N+1)).map (fun s => if s = 0 then 1 else 0)

def wstep (N : ℕ) (v : List ℕ) : List ℕ :=
  (List.range (N+1)).map (fun s =>
    ∑ j ∈ Finset.range (2*s+2),
      (if (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat ≤ s
       then v.getD (s - (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat) 0 else 0))

def wfin (N k : ℕ) : List ℕ := (List.range k).foldl (fun v _ => wstep N v) (wbase N)

def wcnt (N : ℕ) : ℕ := (wfin N 8).getD N 0

lemma zfin_succ (N k : ℕ) : zfin N (k+1) = zstep N (zfin N k) := by
  simp [zfin, List.range_succ, List.foldl_append]

lemma wfin_succ (N k : ℕ) : wfin N (k+1) = wstep N (wfin N k) := by
  simp [wfin, List.range_succ, List.foldl_append]

lemma zbase_getD (N s : ℕ) (hs : s ≤ N) : (zbase N).getD s 0 = (if s = 0 then 1 else 0) := by
  rw [zbase, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

lemma wbase_getD (N s : ℕ) (hs : s ≤ N) : (wbase N).getD s 0 = (if s = 0 then 1 else 0) := by
  rw [wbase, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

lemma zstep_getD (N s : ℕ) (hs : s ≤ N) (v : List ℕ) :
    (zstep N v).getD s 0 =
      ∑ j ∈ Finset.range (2*s+1),
        (if ((j:ℤ) - (s:ℤ))^2 ≤ (s:ℤ)
         then v.getD (s - (((j:ℤ) - (s:ℤ))^2).toNat) 0 else 0) := by
  rw [zstep, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

lemma wstep_getD (N s : ℕ) (hs : s ≤ N) (v : List ℕ) :
    (wstep N v).getD s 0 =
      ∑ j ∈ Finset.range (2*s+2),
        (if (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat ≤ s
         then v.getD (s - (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat) 0 else 0) := by
  rw [wstep, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

lemma SqC_eq_zero_of_neg {k : ℕ} {s : ℤ} (h : s < 0) : SqC k s = 0 := by
  rw [SqC, Set.ncard_eq_zero (sqSol_finite k s)]
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hf
  have h1 : (0:ℤ) ≤ ∑ i : Fin k, (f i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  omega

lemma WqT_eq_zero_of_neg {k : ℕ} {s : ℤ} (h : s < 0) : WqT k s = 0 := by
  rw [WqT, Set.ncard_eq_zero (wqSol_finite k s)]
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hf
  have h1 : (0:ℤ) ≤ ∑ i : Fin k, ((f i)^2 + f i) := Finset.sum_nonneg (fun i _ => wq_term_nonneg _)
  omega

lemma SqC_zero (s : ℤ) : SqC 0 s = if s = 0 then 1 else 0 := by
  rw [SqC]
  by_cases hs : s = 0
  · have hset : {f : Fin 0 → ℤ | ∑ i, (f i)^2 = s} = {fun i => i.elim0} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro _; funext i; exact i.elim0
      · intro _; simp [Fin.sum_univ_zero, hs]
    rw [hset, Set.ncard_singleton, if_pos hs]
  · have hset : {f : Fin 0 → ℤ | ∑ i, (f i)^2 = s} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hf
      rw [Fin.sum_univ_zero] at hf
      exact hs hf.symm
    rw [hset, Set.ncard_empty, if_neg hs]

lemma WqT_zero (s : ℤ) : WqT 0 s = if s = 0 then 1 else 0 := by
  rw [WqT]
  by_cases hs : s = 0
  · have hset : {f : Fin 0 → ℤ | ∑ i, ((f i)^2 + f i) = s} = {fun i => i.elim0} := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro _; funext i; exact i.elim0
      · intro _; simp [Fin.sum_univ_zero, hs]
    rw [hset, Set.ncard_singleton, if_pos hs]
  · have hset : {f : Fin 0 → ℤ | ∑ i, ((f i)^2 + f i) = s} = ∅ := by
      ext f
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hf
      rw [Fin.sum_univ_zero] at hf
      exact hs hf.symm
    rw [hset, Set.ncard_empty, if_neg hs]

lemma zfin_spec (N k : ℕ) : ∀ s ≤ N, (zfin N k).getD s 0 = SqC k (s : ℤ) := by
  induction k with
  | zero =>
      intro s hs
      rw [zfin, List.range_zero, List.foldl_nil, zbase_getD N s hs, SqC_zero]
      by_cases h : s = 0 <;> simp [h]
  | succ k ih =>
      intro s hs
      rw [zfin_succ, zstep_getD N s hs]
      have h1 : ∀ j ∈ Finset.range (2*s+1),
          (if ((j:ℤ) - (s:ℤ))^2 ≤ (s:ℤ)
           then (zfin N k).getD (s - (((j:ℤ) - (s:ℤ))^2).toNat) 0
           else 0) = SqC k ((s:ℤ) - ((j:ℤ) - (s:ℤ))^2) := by
        intro j hj
        rw [Finset.mem_range] at hj
        by_cases h2 : ((j:ℤ) - (s:ℤ))^2 ≤ (s:ℤ)
        · rw [if_pos h2, ih _ (by omega)]
          congr 1
          have hsub : (((j:ℤ) - (s:ℤ))^2).toNat ≤ s := Int.toNat_le_toNat h2
          rw [Nat.cast_sub hsub, Int.toNat_of_nonneg (sq_nonneg ((j:ℤ) - (s:ℤ)))]
        · rw [if_neg h2]
          have h5 : (s:ℤ) - ((j:ℤ) - (s:ℤ))^2 < 0 := by omega
          rw [SqC_eq_zero_of_neg h5]
      rw [Finset.sum_congr rfl h1, ← SqC_succ]

lemma wfin_spec (N k : ℕ) : ∀ s ≤ N, (wfin N k).getD s 0 = WqT k (s : ℤ) := by
  induction k with
  | zero =>
      intro s hs
      rw [wfin, List.range_zero, List.foldl_nil, wbase_getD N s hs, WqT_zero]
      by_cases h : s = 0 <;> simp [h]
  | succ k ih =>
      intro s hs
      rw [wfin_succ, wstep_getD N s hs]
      have h1 : ∀ j ∈ Finset.range (2*s+2),
          (if (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat ≤ s
           then (wfin N k).getD (s - (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat) 0
           else 0) = WqT k ((s:ℤ) - (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1))) := by
        intro j hj
        rw [Finset.mem_range] at hj
        by_cases h2 : (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat ≤ s
        · rw [if_pos h2, ih _ (by omega)]
          congr 1
          have hsub : (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat ≤ s := h2
          rw [Nat.cast_sub hsub, Int.toNat_of_nonneg (wq_term_nonneg _)]
        · rw [if_neg h2]
          have h5 : (s:ℤ) - (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)) < 0 := by
            have h6 : (((j:ℤ) - (s:ℤ) - 1)^2 + ((j:ℤ) - (s:ℤ) - 1)).toNat > s := by omega
            have h7 := Int.toNat_of_nonneg (wq_term_nonneg ((j:ℤ) - (s:ℤ) - 1))
            omega
          rw [WqT_eq_zero_of_neg h5]
      rw [Finset.sum_congr rfl h1, ← WqT_succ]

theorem zcnt_eq (N : ℕ) : zcnt N = SqC 8 (N : ℤ) := by
  rw [zcnt]
  exact zfin_spec N 8 N le_rfl

theorem wcnt_eq (N : ℕ) : wcnt N = WqT 8 (N : ℤ) := by
  rw [wcnt]
  exact wfin_spec N 8 N le_rfl

/-- The parity-flipping involution on `Fin (k+1) → ℤ`. -/
def tau {k : ℕ} (f : Fin (k+1) → ℤ) : Fin (k+1) → ℤ := Fin.cons (- f 0 - 1) (Fin.tail f)

@[simp] lemma tau_zero {k : ℕ} (f : Fin (k+1) → ℤ) : tau f 0 = - f 0 - 1 := Fin.cons_zero _ _

@[simp] lemma tau_succ {k : ℕ} (f : Fin (k+1) → ℤ) (i : Fin k) :
    tau f i.succ = f i.succ := Fin.cons_succ _ _ _

lemma tau_invol {k : ℕ} (f : Fin (k+1) → ℤ) : tau (tau f) = f := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp only [tau_zero]; ring
  · intro j; simp only [tau_succ]

lemma tau_sum {k : ℕ} (f : Fin (k+1) → ℤ) :
    ∑ i, ((tau f i)^2 + tau f i)
      = ((f 0)^2 + f 0) + ∑ i : Fin k, ((f i.succ)^2 + f i.succ) := by
  rw [Fin.sum_univ_succ]
  simp only [tau_zero, tau_succ]
  ring

lemma tau_sum_coord {k : ℕ} (f : Fin (k+1) → ℤ) :
    ∑ i, tau f i = - f 0 - 1 + ∑ i : Fin k, f i.succ := by
  rw [Fin.sum_univ_succ]
  simp only [tau_zero, tau_succ]

lemma WqT_split (k : ℕ) (s : ℤ) :
    WqT (k+1) s
      = Set.ncard {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ 2 ∣ ∑ i, f i}
      + Set.ncard {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ ¬ 2 ∣ ∑ i, f i} := by
  classical
  have hset : {f : Fin (k+1) → ℤ | ∑ i, ((f i)^2 + f i) = s}
      = {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ 2 ∣ ∑ i, f i}
        ∪ {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ ¬ 2 ∣ ∑ i, f i} := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_union]
    tauto
  have hdisj : Disjoint {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ 2 ∣ ∑ i, f i}
      {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ ¬ 2 ∣ ∑ i, f i} := by
    rw [Set.disjoint_left]
    intro f hf hg
    exact hg.2 hf.2
  rw [WqT, hset, Set.ncard_union_eq hdisj
      ((wqSol_finite (k+1) s).subset (fun f hf => hf.1))
      ((wqSol_finite (k+1) s).subset (fun f hf => hf.1))]

lemma WqT_halves (k : ℕ) (s : ℤ) :
    Set.ncard {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ 2 ∣ ∑ i, f i}
      = Set.ncard {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ ¬ 2 ∣ ∑ i, f i} := by
  classical
  refine Set.ncard_congr (fun f _ => tau f) ?_ ?_ ?_
  · intro f hf
    rw [Set.mem_setOf_eq] at hf ⊢
    obtain ⟨hf1, m, hm⟩ := hf
    refine ⟨?_, ?_⟩
    · rw [tau_sum, ← hf1, Fin.sum_univ_succ]
    · intro ⟨n, hn⟩
      rw [tau_sum_coord] at hn
      rw [Fin.sum_univ_succ] at hm
      omega
  · intro f g hf hg h
    exact Function.LeftInverse.injective (g := tau) (fun x => tau_invol x) h
  · intro g hg
    rw [Set.mem_setOf_eq] at hg
    obtain ⟨hg1, hg2⟩ := hg
    refine ⟨tau g, ?_, tau_invol g⟩
    rw [Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [tau_sum, ← hg1, Fin.sum_univ_succ]
    · rcases Int.even_or_odd (∑ i, g i) with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact absurd ⟨m, by omega⟩ hg2
      · refine ⟨m - g 0, ?_⟩
        rw [tau_sum_coord, Fin.sum_univ_succ] at *
        omega

theorem two_mul_evenpart (k : ℕ) (s : ℤ) :
    2 * Set.ncard {f : Fin (k+1) → ℤ | (∑ i, ((f i)^2 + f i) = s) ∧ 2 ∣ ∑ i, f i}
      = WqT (k+1) s := by
  rw [WqT_split, WqT_halves]
  ring


end E8Lat

namespace E8Iso


abbrev Vec := Fin 8 → ℤ

/-- The standard bilinear form (dot product) on `Fin 8 → ℤ`. -/
def dotZ (x y : Vec) : ℤ := ∑ i, x i * y i

/-- The eight simple roots of `E₈` in the standard realization, scaled by `2`. -/
def srt : Fin 8 → Vec :=
  ![ ![1, -1, -1, -1, -1, -1, -1, 1],
     ![2, 2, 0, 0, 0, 0, 0, 0],
     ![-2, 2, 0, 0, 0, 0, 0, 0],
     ![0, -2, 2, 0, 0, 0, 0, 0],
     ![0, 0, -2, 2, 0, 0, 0, 0],
     ![0, 0, 0, -2, 2, 0, 0, 0],
     ![0, 0, 0, 0, -2, 2, 0, 0],
     ![0, 0, 0, 0, 0, -2, 2, 0] ]

/-- The Gram matrix of the scaled simple roots is `4` times the `E₈` Cartan matrix. -/
theorem gram (i j : Fin 8) : dotZ (srt i) (srt j) = 4 * E8NormTwo.E8 i j := by
  fin_cases i <;> fin_cases j <;> decide

lemma dotZ_add_left (x y z : Vec) : dotZ (x + y) z = dotZ x z + dotZ y z := by
  simp only [dotZ, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotZ_add_right (x y z : Vec) : dotZ x (y + z) = dotZ x y + dotZ x z := by
  simp only [dotZ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotZ_smul_left (c : ℤ) (x y : Vec) : dotZ (c • x) y = c * dotZ x y := by
  simp only [dotZ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma dotZ_zero_left (y : Vec) : dotZ 0 y = 0 := by simp [dotZ]

lemma dotZ_sum_left (s : Finset (Fin 8)) (c : Fin 8 → ℤ) (y : Vec) :
    dotZ (∑ i ∈ s, c i • srt i) y = ∑ i ∈ s, c i * dotZ (srt i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [dotZ_zero_left]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, dotZ_add_left, ih, dotZ_smul_left]

lemma dotZ_smul_right (c : ℤ) (x y : Vec) : dotZ x (c • y) = c * dotZ x y := by
  simp only [dotZ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma dotZ_sum_right (s : Finset (Fin 8)) (d : Fin 8 → ℤ) (x : Vec) :
    dotZ x (∑ j ∈ s, d j • srt j) = ∑ j ∈ s, d j * dotZ x (srt j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [dotZ]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, dotZ_add_right, ih, dotZ_smul_right]

lemma dotZ_sum_sum (c d : Fin 8 → ℤ) :
    dotZ (∑ i, c i • srt i) (∑ j, d j • srt j)
      = ∑ i, ∑ j, c i * (d j * dotZ (srt i) (srt j)) := by
  rw [dotZ_sum_left]
  apply Finset.sum_congr rfl; intro i _
  rw [dotZ_sum_right, Finset.mul_sum]

/-- The isometry `Z^8 → 2Λ(E₈)` given by `v ↦ ∑ᵢ (A⁻¹v)ᵢ • srtᵢ`. -/
def Phi (v : Vec) : Vec := ∑ i, (E8NormTwo.E8inv.mulVec v) i • srt i

lemma E8_mul_E8inv : E8NormTwo.E8 * E8NormTwo.E8inv = 1 := by
  rw [mul_eq_one_comm]; exact E8NormTwo.E8inv_mul_E8

lemma E8_mulVec_inv (v : Vec) : E8NormTwo.E8.mulVec (E8NormTwo.E8inv.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, E8_mul_E8inv, Matrix.one_mulVec]

lemma qZ_eq_dot_inv (v : Vec) : E8NormTwo.qZ v = dotZ v (E8NormTwo.E8inv.mulVec v) := by
  simp only [dotZ, E8NormTwo.qZ, Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

theorem Phi_norm (v : Vec) : dotZ (Phi v) (Phi v) = 4 * E8NormTwo.qZ v := by
  set w : Vec := E8NormTwo.E8inv.mulVec v with hw
  have hgram : ∀ i j : Fin 8, dotZ (srt i) (srt j) = 4 * E8NormTwo.E8 i j := gram
  have hwv : E8NormTwo.E8.mulVec w = v := by rw [hw]; exact E8_mulVec_inv v
  have hq : E8NormTwo.qZ v = dotZ v w := by rw [hw]; exact qZ_eq_dot_inv v
  have hPhi : Phi v = ∑ i, w i • srt i := by rw [Phi, hw]
  rw [hPhi, dotZ_sum_sum]
  calc ∑ i, ∑ j, w i * (w j * dotZ (srt i) (srt j))
      = 4 * (∑ i, ∑ j, w i * E8NormTwo.E8 i j * w j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [hgram]; ring
    _ = 4 * (∑ i, w i * (E8NormTwo.E8.mulVec w) i) := by
        congr 1
        apply Finset.sum_congr rfl; intro i _
        rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        ring
    _ = 4 * (∑ i, v i * w i) := by
        rw [hwv]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = 4 * E8NormTwo.qZ v := by rw [hq, dotZ]

/-! ## The standard model `2Λ(E₈)` -/

/-- All coordinates even. -/
abbrev AllEven (y : Vec) : Prop := ∀ i, 2 ∣ y i

/-- All coordinates odd. -/
abbrev AllOdd (y : Vec) : Prop := ∀ i, ¬ 2 ∣ y i

/-- An element of `2Λ(E₈)`: all coordinates even or all odd, and the coordinate sum divisible by `4`. -/
abbrev Std (y : Vec) : Prop := (AllEven y ∨ AllOdd y) ∧ (4 ∣ ∑ i, y i)

lemma AllEven.add {y z : Vec} (hy : AllEven y) (hz : AllEven z) : AllEven (y + z) :=
  fun i => by simpa [Pi.add_apply] using dvd_add (hy i) (hz i)

lemma AllEven.add_odd {y z : Vec} (hy : AllEven y) (hz : AllOdd z) : AllOdd (y + z) := by
  intro i
  simp only [Pi.add_apply]
  intro h
  exact hz i (by simpa using dvd_sub h (hy i))

lemma two_dvd_add_of_not {a b : ℤ} (ha : ¬ 2 ∣ a) (hb : ¬ 2 ∣ b) : 2 ∣ a + b := by
  rcases Int.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact absurd ⟨m, by omega⟩ ha
  · rcases Int.even_or_odd b with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact absurd ⟨n, by omega⟩ hb
    · exact ⟨m + n + 1, by omega⟩

lemma AllOdd.add_odd {y z : Vec} (hy : AllOdd y) (hz : AllOdd z) : AllEven (y + z) := by
  intro i
  simp only [Pi.add_apply]
  exact two_dvd_add_of_not (hy i) (hz i)

lemma AllEven.neg {y : Vec} (hy : AllEven y) : AllEven (-y) := fun i => by
  simpa using dvd_neg.mpr (hy i)

lemma AllOdd.neg {y : Vec} (hy : AllOdd y) : AllOdd (-y) := by
  intro i h
  exact hy i (dvd_neg.mp (by simpa only [Pi.neg_apply] using h))

lemma AllEven.smul (c : ℤ) {y : Vec} (hy : AllEven y) : AllEven (c • y) := by
  intro i
  simp only [Pi.smul_apply, smul_eq_mul]
  exact Dvd.dvd.mul_left (hy i) c

lemma Std.add {y z : Vec} (hy : Std y) (hz : Std z) : Std (y + z) := by
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨?_, ?_⟩
  · rcases hy1 with h | h <;> rcases hz1 with h' | h'
    · exact Or.inl (h.add h')
    · exact Or.inr (h.add_odd h')
    · exact Or.inr (by rw [add_comm]; exact h'.add_odd h)
    · exact Or.inl (h.add_odd h')
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib]
    exact dvd_add hy2 hz2

lemma Std.neg {y : Vec} (hy : Std y) : Std (-y) := by
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · rcases hy1 with h | h
    · exact Or.inl h.neg
    · exact Or.inr h.neg
  · simp only [Pi.neg_apply]
    rw [Finset.sum_neg_distrib]
    exact dvd_neg.mpr hy2

lemma not_dvd_odd_mul {m y : ℤ} (h : ¬ 2 ∣ y) : ¬ 2 ∣ (2*m + 1) * y := by
  intro hcon
  obtain ⟨k, hk⟩ := hcon
  exact h ⟨k - m*y, by nlinarith [hk]⟩

lemma dvd_odd_mul_even {m y : ℤ} (h : 2 ∣ y) : 2 ∣ (2*m + 1) * y := by
  obtain ⟨k, hk⟩ := h
  exact ⟨(2*m+1)*k, by rw [hk]; ring⟩

lemma Std.smul (c : ℤ) {y : Vec} (hy : Std y) : Std (c • y) := by
  obtain ⟨hy1, hy2⟩ := hy
  have hsum : ∑ i, (c • y) i = c * ∑ i, y i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by simp [Pi.smul_apply, smul_eq_mul])
  rcases Int.even_or_odd c with ⟨m, hm⟩ | ⟨m, hm⟩
  · refine ⟨Or.inl ?_, ?_⟩
    · intro i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact ⟨m * y i, by rw [show c = m + m by omega]; ring⟩
    · rw [hsum]
      obtain ⟨t, ht⟩ := hy2
      exact ⟨c * t, by rw [ht]; ring⟩
  · have hc : c = 2*m + 1 := by omega
    refine ⟨?_, ?_⟩
    · rcases hy1 with h | h
      · left
        intro i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hc]; exact dvd_odd_mul_even (m := m) (h i)
      · right
        intro i
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hc]; exact not_dvd_odd_mul (m := m) (h i)
    · rw [hsum]
      obtain ⟨t, ht⟩ := hy2
      exact ⟨c * t, by rw [ht]; ring⟩

lemma Std_srt (i : Fin 8) : Std (srt i) := by
  fin_cases i <;> decide

lemma Std_zero : Std (0 : Vec) := by
  refine ⟨Or.inl (fun i => ⟨0, by simp⟩), ⟨0, by simp⟩⟩

lemma Std_sum {n : ℕ} (c : Fin n → ℤ) (g : Fin n → Vec) (h : ∀ i, Std (g i)) :
    Std (∑ i : Fin n, c i • g i) := by
  classical
  have key : ∀ s : Finset (Fin n), (∀ i ∈ s, Std (g i)) → Std (∑ i ∈ s, c i • g i) := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; simpa using Std_zero
    | insert a s ha ih =>
        intro hs
        rw [Finset.sum_insert ha]
        exact Std.add ((h a).smul (c a))
          (ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)))
  exact key Finset.univ (fun i _ => h i)

/-! ## The span of the simple roots and the standard model -/

/-- `spanZ g y` means that `y` is an integral linear combination of the vectors `g i`. -/
def spanZ {n : ℕ} (g : Fin n → Vec) (y : Vec) : Prop :=
  ∃ c : Fin n → ℤ, y = ∑ i, c i • g i

lemma spanZ.zero {n : ℕ} (g : Fin n → Vec) : spanZ g 0 :=
  ⟨0, by simp⟩

lemma spanZ.smul {n : ℕ} {g : Fin n → Vec} (c : ℤ) {y : Vec} (hy : spanZ g y) :
    spanZ g (c • y) := by
  obtain ⟨d, hd⟩ := hy
  refine ⟨fun i => c * d i, ?_⟩
  rw [hd, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma spanZ.add {n : ℕ} {g : Fin n → Vec} {y z : Vec} (hy : spanZ g y) (hz : spanZ g z) :
    spanZ g (y + z) := by
  obtain ⟨c, hc⟩ := hy
  obtain ⟨d, hd⟩ := hz
  exact ⟨fun i => c i + d i, by rw [hc, hd, ← Finset.sum_add_distrib]; simp [add_smul]⟩

/-- The unit vectors. -/
def eVec (i : Fin 8) : Vec := Pi.single i 1

/-- The nine generators of `2Λ(E₈)` inside `ℤ^8`. -/
def gen : Fin 9 → Vec :=
  ![ ![2, -2, 0, 0, 0, 0, 0, 0],
     ![0, 2, -2, 0, 0, 0, 0, 0],
     ![0, 0, 2, -2, 0, 0, 0, 0],
     ![0, 0, 0, 2, -2, 0, 0, 0],
     ![0, 0, 0, 0, 2, -2, 0, 0],
     ![0, 0, 0, 0, 0, 2, -2, 0],
     ![0, 0, 0, 0, 0, 0, 2, -2],
     ![0, 0, 0, 0, 0, 0, 2, 2],
     ![1, 1, 1, 1, 1, 1, 1, 1] ]

@[simp] lemma eVec_apply (i j : Fin 8) : eVec i j = if j = i then 1 else 0 := by
  simp [eVec, Pi.single_apply, eq_comm]

lemma mem_two_diff : ∀ i : Fin 7, spanZ gen (2 • (eVec i.castSucc - eVec 7)) := by
  intro i
  fin_cases i
  · exact ⟨![1, 1, 1, 1, 1, 1, 1, 0, 0], by decide⟩
  · exact ⟨![0, 1, 1, 1, 1, 1, 1, 0, 0], by decide⟩
  · exact ⟨![0, 0, 1, 1, 1, 1, 1, 0, 0], by decide⟩
  · exact ⟨![0, 0, 0, 1, 1, 1, 1, 0, 0], by decide⟩
  · exact ⟨![0, 0, 0, 0, 1, 1, 1, 0, 0], by decide⟩
  · exact ⟨![0, 0, 0, 0, 0, 1, 1, 0, 0], by decide⟩
  · exact ⟨![0, 0, 0, 0, 0, 0, 1, 0, 0], by decide⟩

lemma mem_four_e7 : spanZ gen (4 • eVec 7) :=
  ⟨![0, 0, 0, 0, 0, 0, -1, 1, 0], by decide⟩

lemma mem_ones : spanZ gen (1 : Vec) :=
  ⟨![0, 0, 0, 0, 0, 0, 0, 0, 1], by decide⟩

lemma sum_univ_split8 (z : Vec) : ∑ i, z i = z 0 + z 1 + z 2 + z 3 + z 4 + z 5 + z 6 + z 7 := by
  simp [Fin.sum_univ_eight]

lemma even_decomp (z : Vec) (t : ℤ) (ht : ∑ i, z i = 2 * t) :
    2 • z = z 0 • (2 • (eVec 0 - eVec 7)) + z 1 • (2 • (eVec 1 - eVec 7))
      + z 2 • (2 • (eVec 2 - eVec 7)) + z 3 • (2 • (eVec 3 - eVec 7))
      + z 4 • (2 • (eVec 4 - eVec 7)) + z 5 • (2 • (eVec 5 - eVec 7))
      + z 6 • (2 • (eVec 6 - eVec 7)) + t • (4 • eVec 7) := by
  funext k
  fin_cases k <;> simp [eVec, Fin.sum_univ_eight] at ht ⊢ <;> omega

lemma spanZ_even {y : Vec} (hy : AllEven y) (h4 : 4 ∣ ∑ i, y i) : spanZ gen y := by
  choose z hz using hy
  have hyz : y = 2 • z := by funext i; simp [Pi.smul_apply, hz i]
  have hsum : ∑ i, y i = 2 * (∑ i, z i) := by
    rw [hyz]
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have h2 : 2 ∣ ∑ i, z i := by
    obtain ⟨t, ht⟩ := h4
    refine ⟨t, ?_⟩
    rw [hsum] at ht
    omega
  obtain ⟨t, ht⟩ := h2
  rw [hyz, even_decomp z t ht]
  have h0 : spanZ gen (z 0 • (2 • (eVec 0 - eVec 7))) :=
    spanZ.smul (z 0) (mem_two_diff 0)
  have h1 : spanZ gen (z 1 • (2 • (eVec 1 - eVec 7))) :=
    spanZ.smul (z 1) (mem_two_diff 1)
  have h2' : spanZ gen (z 2 • (2 • (eVec 2 - eVec 7))) :=
    spanZ.smul (z 2) (mem_two_diff 2)
  have h3 : spanZ gen (z 3 • (2 • (eVec 3 - eVec 7))) :=
    spanZ.smul (z 3) (mem_two_diff 3)
  have h4' : spanZ gen (z 4 • (2 • (eVec 4 - eVec 7))) :=
    spanZ.smul (z 4) (mem_two_diff 4)
  have h5 : spanZ gen (z 5 • (2 • (eVec 5 - eVec 7))) :=
    spanZ.smul (z 5) (mem_two_diff 5)
  have h6 : spanZ gen (z 6 • (2 • (eVec 6 - eVec 7))) :=
    spanZ.smul (z 6) (mem_two_diff 6)
  have h7 : spanZ gen (t • (4 • eVec 7)) := spanZ.smul t mem_four_e7
  exact spanZ.add (spanZ.add (spanZ.add (spanZ.add (spanZ.add (spanZ.add (spanZ.add h0 h1) h2') h3) h4') h5) h6) h7

lemma two_dvd_sub_one_of_not {a : ℤ} (h : ¬ 2 ∣ a) : 2 ∣ a - 1 := by
  rcases Int.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact absurd ⟨m, by omega⟩ h
  · exact ⟨m, by omega⟩

lemma sub_one_even {y : Vec} (h : AllOdd y) : AllEven (y - 1) := by
  intro i
  simp only [Pi.sub_apply, Pi.one_apply]
  exact two_dvd_sub_one_of_not (h i)

lemma Std_mem_span {y : Vec} (hy : Std y) : spanZ gen y := by
  obtain ⟨hy1, hy2⟩ := hy
  rcases hy1 with h | h
  · exact spanZ_even h hy2
  · have hsub : AllEven (y - 1) := sub_one_even h
    have h4 : 4 ∣ ∑ i, (y - 1) i := by
      have hsum : ∑ i, (y - 1) i = (∑ i, y i) - 8 := by
        simp only [Pi.sub_apply, Pi.one_apply]
        rw [Finset.sum_sub_distrib]
        norm_num
      rw [hsum]
      obtain ⟨t, ht⟩ := hy2
      exact ⟨t - 2, by omega⟩
    have := spanZ_even hsub h4
    have hsum2 : (y - 1) + (1 : Vec) = y := by
      funext i; simp
    rw [← hsum2]
    exact spanZ.add this mem_ones

/-! ## The generators as combinations of the simple roots -/

lemma spanZ_trans {m n : ℕ} {g : Fin m → Vec} {h : Fin n → Vec} {y : Vec}
    (hy : spanZ g y) (hgh : ∀ i, spanZ h (g i)) : spanZ h y := by
  obtain ⟨c, hc⟩ := hy
  choose d hd using hgh
  refine ⟨fun j => ∑ i, c i * d i j, ?_⟩
  rw [hc]
  calc ∑ i, c i • g i = ∑ i, c i • (∑ j, d i j • h j) := by
        apply Finset.sum_congr rfl; intro i _; rw [hd i]
    _ = ∑ j, (∑ i, c i * d i j) • h j := by
        have h1 : ∀ i, c i • (∑ j, d i j • h j) = ∑ j, (c i * d i j) • h j := by
          intro i
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl; intro j _
          rw [smul_smul]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_smul]

lemma gen_mem_span_srt : ∀ i : Fin 9, spanZ srt (gen i) := by
  intro i
  fin_cases i
  · exact ⟨![0, 0, -1, 0, 0, 0, 0, 0], by decide⟩
  · exact ⟨![0, 0, 0, -1, 0, 0, 0, 0], by decide⟩
  · exact ⟨![0, 0, 0, 0, -1, 0, 0, 0], by decide⟩
  · exact ⟨![0, 0, 0, 0, 0, -1, 0, 0], by decide⟩
  · exact ⟨![0, 0, 0, 0, 0, 0, -1, 0], by decide⟩
  · exact ⟨![0, 0, 0, 0, 0, 0, 0, -1], by decide⟩
  · exact ⟨![-2, -2, -3, -4, -3, -2, -1, 0], by decide⟩
  · exact ⟨![2, 3, 4, 6, 5, 4, 3, 2], by decide⟩
  · exact ⟨![1, 3, 3, 5, 4, 3, 2, 1], by decide⟩

theorem Std_mem_span_srt {y : Vec} (hy : Std y) : spanZ srt y :=
  spanZ_trans (Std_mem_span hy) gen_mem_span_srt

/-! ## Injectivity and surjectivity of `Phi` -/

lemma srt_indep {c : Fin 8 → ℤ} (h : ∑ i, c i • srt i = 0) : c = 0 := by
  have h1 : ∀ j : Fin 8, ∑ i, c i * (4 * E8NormTwo.E8 i j) = 0 := by
    intro j
    have h0 : ∑ i, c i * dotZ (srt i) (srt j) = 0 := by
      have hh := congrArg (fun y : Vec => dotZ y (srt j)) h
      rw [dotZ_sum_left, dotZ_zero_left] at hh
      exact hh
    have key : (∑ i, c i * dotZ (srt i) (srt j)) = ∑ i, c i * (4 * E8NormTwo.E8 i j) := by
      apply Finset.sum_congr rfl; intro i _
      rw [gram i j]
    rw [key] at h0
    exact h0
  have h2 : ∀ j : Fin 8, ∑ i, E8NormTwo.E8 i j * c i = 0 := by
    intro j
    have h4 : 4 * (∑ i, E8NormTwo.E8 i j * c i) = 0 := by
      rw [Finset.mul_sum, ← h1 j]
      apply Finset.sum_congr rfl; intro i _
      ring
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
  have h3 : E8NormTwo.E8.mulVec c = 0 := by
    funext j
    rw [Matrix.mulVec_apply_eq_sum]
    rw [show (∑ x, E8NormTwo.E8 j x * c x) = ∑ x, E8NormTwo.E8 x j * c x from
      Finset.sum_congr rfl (fun x _ => by rw [E8NormTwo.E8_symm])]
    exact h2 j
  have h4 : E8NormTwo.E8inv.mulVec (E8NormTwo.E8.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, E8NormTwo.E8inv_mul_E8, Matrix.one_mulVec]
  rw [h3, Matrix.mulVec_zero] at h4
  exact h4.symm

lemma Phi_sub (v w : Vec) : Phi (v - w) = Phi v - Phi w := by
  have key : (∑ x, (E8NormTwo.E8inv.mulVec (v - w)) x • srt x)
      = ∑ x, ((E8NormTwo.E8inv.mulVec v) x • srt x - (E8NormTwo.E8inv.mulVec w) x • srt x) := by
    apply Finset.sum_congr rfl; intro x _
    rw [Matrix.mulVec_sub, Pi.sub_apply, sub_smul]
  rw [Phi, Phi, Phi]
  rw [key, Finset.sum_sub_distrib]

theorem Phi_inj {v w : Vec} (h : Phi v = Phi w) : v = w := by
  have h0 : Phi (v - w) = 0 := by
    rw [Phi_sub, h, sub_self]
  have h1 : ∑ i, (E8NormTwo.E8inv.mulVec (v - w)) i • srt i = 0 := by
    rw [← h0, Phi]
  have h2 := srt_indep h1
  have h3 : E8NormTwo.E8.mulVec (E8NormTwo.E8inv.mulVec (v - w)) = v - w := E8_mulVec_inv _
  rw [h2, Matrix.mulVec_zero] at h3
  exact sub_eq_zero.mp h3.symm

theorem Phi_surj {y : Vec} (hy : Std y) : ∃ v : Vec, Phi v = y := by
  obtain ⟨c, hc⟩ := Std_mem_span_srt hy
  refine ⟨E8NormTwo.E8.mulVec c, ?_⟩
  rw [Phi]
  have h1 : E8NormTwo.E8inv.mulVec (E8NormTwo.E8.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, E8NormTwo.E8inv_mul_E8, Matrix.one_mulVec]
  rw [h1]
  exact hc.symm

lemma Phi_mem_std (v : Vec) : Std (Phi v) := by
  rw [Phi]
  exact Std_sum _ _ (fun i => Std_srt i)


/-! ## The counting transfer -/

lemma filter_toList_length {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.toList.filter p).length = (s.filter p).card := by
  have h1 : (s.toList.filter p).toFinset = s.filter p := by
    ext a
    rw [List.mem_toFinset, List.mem_filter, Finset.mem_filter, Finset.mem_toList, decide_eq_true_eq]
  rw [← h1, List.toFinset_card_of_nodup]
  exact List.Nodup.filter _ s.nodup_toList

lemma two_dvd_sq_sub (a : ℤ) : 2 ∣ a^2 - a := by
  rcases Int.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨2*m*m - m, by rw [hm]; ring⟩
  · exact ⟨2*m*m + m, by rw [hm]; ring⟩

lemma two_dvd_sum_of_sq (z : Vec) : 2 ∣ (∑ i, (z i)^2) - ∑ i, z i := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.dvd_sum (fun i _ => two_dvd_sq_sub (z i))

lemma dotZ_self (z : Vec) : E8Iso.dotZ z z = ∑ i, (z i)^2 := by
  simp only [E8Iso.dotZ]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma sum_smul_coord (c : ℤ) (z : Vec) : ∑ i, (c • z) i = c * ∑ i, z i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp [Pi.smul_apply, smul_eq_mul])

lemma two_smul_sqsum (z : Vec) : ∑ i, (((2:ℤ) • z) i)^2 = 4 * ∑ i, (z i)^2 := by
  have h1 : ∀ i : Fin 8, (((2:ℤ) • z) i)^2 = 4 * (z i)^2 := by
    intro i; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.mul_sum]

lemma even_add_one_sum (z : Vec) :
    ∑ i, ((2:ℤ) • z + 1) i = 2 * (∑ i, z i) + 8 := by
  have h1 : ∀ i : Fin 8, ((2:ℤ) • z + 1) i = 2 * z i + 1 := by
    intro i; simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

lemma even_add_one_sqsum (z : Vec) :
    ∑ i, (((2:ℤ) • z + 1) i)^2 = 4 * (∑ i, ((z i)^2 + z i)) + 8 := by
  have h1 : ∀ i : Fin 8, (((2:ℤ) • z + 1) i)^2 = 4 * ((z i)^2 + z i) + 1 := by
    intro i; simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]; ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

lemma smul_two_inj : Function.Injective (fun z : Vec => (2:ℤ) • z) := by
  intro z w h
  funext i
  have h1 : (2:ℤ) * z i = 2 * w i := by
    simpa [Pi.smul_apply, smul_eq_mul] using congr_fun h i
  omega

lemma add_one_two_inj : Function.Injective (fun z : Vec => (2:ℤ) • z + 1) := by
  intro z w h
  funext i
  have h1 : (2:ℤ) * z i + 1 = 2 * w i + 1 := by
    simpa [Pi.smul_apply, Pi.add_apply, smul_eq_mul] using congr_fun h i
  omega

/-! ## The list of lattice points and its statistics -/

lemma sq_le_two_qZ (v : Vec) (j : Fin 8) : (v j)^2 ≤ 2 * E8NormTwo.qZ v := by
  have hcf : E8NormTwo.form2 (E8NormTwo.xc v) (E8NormTwo.xc v) = (E8NormTwo.qZ v : ℚ) :=
    E8NormTwo.form2_xc_self v
  have hAx : E8NormTwo.form2 (E8NormTwo.xc v) (Pi.single j (1:ℚ)) = ((v j : ℤ) : ℚ) := by
    rw [E8NormTwo.form2_single, E8NormTwo.E8q_mul_xc]
  have hpsd : 0 ≤ E8NormTwo.form2
      (E8NormTwo.xc v - (((v j : ℤ):ℚ)/2) • Pi.single j (1:ℚ))
      (E8NormTwo.xc v - (((v j : ℤ):ℚ)/2) • Pi.single j (1:ℚ)) := E8NormTwo.form2_nonneg _
  rw [E8NormTwo.form2_bilin, hcf, hAx, E8NormTwo.form2_single_self] at hpsd
  have : ((v j : ℤ) : ℚ)^2 ≤ 2 * (E8NormTwo.qZ v : ℚ) := by nlinarith [hpsd]
  exact_mod_cast this

lemma abs_coord_le_four {v : Vec} (hv : E8NormTwo.qZ v ≤ 10) (j : Fin 8) :
    -4 ≤ v j ∧ v j ≤ 4 := by
  have h1 : (v j)^2 ≤ 2 * E8NormTwo.qZ v := sq_le_two_qZ v j
  have h2 : (v j)^2 ≤ 20 := by omega
  constructor <;> nlinarith [h2, sq_nonneg (v j)]

lemma qZSol_finite : ({v : Vec | E8NormTwo.qZ v ≤ 10}).Finite := by
  refine (Set.Finite.pi (fun _ : Fin 8 => Finset.finite_toSet (Finset.Icc (-4) 4))).subset ?_
  intro v hv
  rw [Set.mem_pi]
  intro j _
  simp only [Finset.mem_coe, Finset.mem_Icc]
  exact abs_coord_le_four hv j

/-- The explicit list of lattice points of squared length at most `10`. -/
noncomputable def L : List Vec := qZSol_finite.toFinset.toList

lemma L_nodup : L.Nodup := Finset.nodup_toList _

lemma L_mem {v : Vec} (hv : E8NormTwo.qZ v ≤ 10) : v ∈ L := by
  rw [L, Finset.mem_toList]
  exact (Set.Finite.mem_toFinset qZSol_finite).mpr hv

/-- The isometry transfers the counting problem to the standard model. -/
theorem ncard_qZ_eq_std (m : ℕ) :
    {v : Vec | E8NormTwo.qZ v = (2*m:ℤ)}.ncard
      = {y : Vec | E8Iso.Std y ∧ ∑ i, (y i)^2 = (8*m:ℤ)}.ncard := by
  refine Set.ncard_congr (fun v _ => E8Iso.Phi v) ?_ ?_ ?_
  · intro v hv
    rw [Set.mem_setOf_eq] at hv ⊢
    refine ⟨E8Iso.Phi_mem_std v, ?_⟩
    rw [← dotZ_self (E8Iso.Phi v), E8Iso.Phi_norm, hv]
    ring
  · intro v w hv hw h
    exact E8Iso.Phi_inj h
  · intro y hy
    rw [Set.mem_setOf_eq] at hy
    obtain ⟨v, hv⟩ := E8Iso.Phi_surj hy.1
    refine ⟨v, ?_, hv⟩
    rw [Set.mem_setOf_eq]
    have h4 : 4 * E8NormTwo.qZ v = (8*m:ℤ) := by
      rw [← E8Iso.Phi_norm v, hv, dotZ_self y]
      exact hy.2
    omega

/-- The even part of the standard model has `SqC` many points. -/
theorem ncard_even (m : ℕ) :
    {y : Vec | E8Iso.AllEven y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}.ncard
      = E8Lat.SqC 8 (2*m:ℤ) := by
  have hset : {y : Vec | E8Iso.AllEven y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}
      = (fun z : Vec => (2:ℤ) • z) '' {z : Vec | ∑ i, (z i)^2 = (2*m:ℤ)} := by
    ext y
    constructor
    · intro hy
      obtain ⟨h1, h2, h3⟩ := hy
      set k : Vec := fun i => Classical.choose (h1 i) with hkdef
      have hk : ∀ i, y i = 2 * k i := fun i => Classical.choose_spec (h1 i)
      have hy2 : y = (2:ℤ) • k := by funext i; simp [Pi.smul_apply, smul_eq_mul, hk i]
      refine ⟨k, ?_, ?_⟩
      · rw [hy2, two_smul_sqsum] at h3
        have h3' : (4:ℤ) * (∑ i, (k i)^2) = 4 * (2*m:ℤ) := by rw [h3]; ring
        exact mul_left_cancel₀ (by norm_num) h3'
      · funext i
        simp only [Pi.smul_apply, smul_eq_mul]
        have := hk i; omega
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i; exact ⟨z i, rfl⟩
      · rw [sum_smul_coord]
        obtain ⟨t, ht⟩ := two_dvd_sum_of_sq z
        rw [hz] at ht
        exact ⟨m - t, by omega⟩
      · rw [two_smul_sqsum, hz]; ring
  rw [hset, Set.ncard_image_of_injective _ smul_two_inj, E8Lat.SqC]

/-- The odd part of the standard model is the `WqT`-count cut in half. -/
theorem two_mul_ncard_odd (m : ℕ) :
    2 * {y : Vec | E8Iso.AllOdd y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}.ncard
      = E8Lat.WqT 8 (2*m - 2:ℤ) := by
  have hset : {y : Vec | E8Iso.AllOdd y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}
      = (fun w : Vec => (2:ℤ) • w + 1) ''
          {w : Vec | (∑ i, ((w i)^2 + w i)) = (2*m - 2:ℤ) ∧ 2 ∣ ∑ i, w i} := by
    ext y
    constructor
    · intro hy
      obtain ⟨h1, h2, h3⟩ := hy
      have hodd : ∀ i, ∃ k, y i = 2*k + 1 := by
        intro i
        rcases Int.even_or_odd (y i) with ⟨c, hc⟩ | ⟨c, hc⟩
        · exact absurd ⟨c, by omega⟩ (h1 i)
        · exact ⟨c, hc⟩
      set k : Vec := fun i => Classical.choose (hodd i) with hkdef
      have hk : ∀ i, y i = 2 * k i + 1 := fun i => Classical.choose_spec (hodd i)
      have hy2 : y = (2:ℤ) • k + 1 := by
        funext i; simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hk i]
      refine ⟨k, ⟨?_, ?_⟩, ?_⟩
      · rw [hy2, even_add_one_sqsum] at h3
        have h3' : 4 * (∑ i, ((k i)^2 + k i)) + 8 = 4 * ((2*m - 2:ℤ) + 2) := by rw [h3]; ring
        have : (∑ i, ((k i)^2 + k i)) + 2 = (2*m - 2:ℤ) + 2 := by
          apply mul_left_cancel₀ (show (4:ℤ) ≠ 0 by norm_num)
          linarith [h3']
        omega
      · rw [hy2, even_add_one_sum] at h2
        obtain ⟨t, ht⟩ := h2
        exact ⟨t - 2, by omega⟩
      · funext i
        simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
        have := hk i; omega
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro i
        simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
        intro ⟨t, ht⟩
        omega
      · rw [even_add_one_sum]
        obtain ⟨t, ht⟩ := hw2
        exact ⟨t + 2, by omega⟩
      · rw [even_add_one_sqsum, hw1]
        ring
  rw [hset, Set.ncard_image_of_injective _ add_one_two_inj, E8Lat.two_mul_evenpart]

lemma sqsum_finite (m : ℕ) (hm : m ≤ 5) : ({y : Vec | ∑ i, (y i)^2 = (8*m:ℤ)}).Finite := by
  refine (Set.Finite.pi (fun _ : Fin 8 => Finset.finite_toSet (Finset.Icc (-6) 6))).subset ?_
  intro y hy
  rw [Set.mem_pi]
  intro j _
  simp only [Finset.mem_coe, Finset.mem_Icc]
  have h1 : (y j)^2 ≤ (8*m:ℤ) := by
    calc (y j)^2 ≤ ∑ i, (y i)^2 :=
          Finset.single_le_sum (fun i _ => sq_nonneg (y i)) (Finset.mem_univ j)
      _ = (8*m:ℤ) := hy
  have h2 : (y j)^2 ≤ 40 := by omega
  constructor <;> nlinarith [h2, sq_nonneg (y j + 7), sq_nonneg (y j - 7)]

/-- The standard-model count in terms of the two dynamic programs. -/
theorem std_count (m : ℕ) (hm : m ≤ 5) :
    {y : Vec | E8Iso.Std y ∧ ∑ i, (y i)^2 = (8*m:ℤ)}.ncard
      = E8Lat.SqC 8 (2*m:ℤ) + E8Lat.WqT 8 (2*m - 2:ℤ) / 2 := by
  rw [show {y : Vec | E8Iso.Std y ∧ ∑ i, (y i)^2 = (8*m:ℤ)}
      = {y : Vec | E8Iso.AllEven y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}
        ∪ {y : Vec | E8Iso.AllOdd y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)} from by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_union, E8Iso.Std]
    tauto]
  have hdisj : Disjoint {y : Vec | E8Iso.AllEven y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}
      {y : Vec | E8Iso.AllOdd y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)} := by
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hy'.1 0 (hy.1 0)
  have hfin1 : ({y : Vec | E8Iso.AllEven y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}).Finite :=
    (sqsum_finite m hm).subset (fun y hy => hy.2.2)
  have hfin2 : ({y : Vec | E8Iso.AllOdd y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}).Finite :=
    (sqsum_finite m hm).subset (fun y hy => hy.2.2)
  rw [Set.ncard_union_eq hdisj hfin1 hfin2]
  · rw [ncard_even]
    have hodd : {y : Vec | E8Iso.AllOdd y ∧ 4 ∣ ∑ i, y i ∧ ∑ i, (y i)^2 = (8*m:ℤ)}.ncard
        = E8Lat.WqT 8 (2*m - 2:ℤ) / 2 := by
      have h2 := two_mul_ncard_odd m
      omega
    rw [hodd]

lemma L_count (m : ℕ) (hm : m ≤ 5) :
    (L.filter (fun v => E8NormTwo.qZ v = (2*m:ℤ))).length
      = E8Lat.SqC 8 (2*m:ℤ) + E8Lat.WqT 8 (2*m - 2:ℤ) / 2 := by
  rw [L, filter_toList_length]
  have h1 : (qZSol_finite.toFinset.filter (fun v => E8NormTwo.qZ v = (2*m:ℤ))).card
      = {v : Vec | E8NormTwo.qZ v ≤ 10 ∧ E8NormTwo.qZ v = (2*m:ℤ)}.ncard := by
    rw [Set.ncard_eq_toFinset_card _ (qZSol_finite.subset (fun v hv => hv.1))]
    congr 1
    ext v
    simp [Finset.mem_filter]
  rw [h1]
  have h2 : {v : Vec | E8NormTwo.qZ v ≤ 10 ∧ E8NormTwo.qZ v = (2*m:ℤ)}
      = {v : Vec | E8NormTwo.qZ v = (2*m:ℤ)} := by
    ext v
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact show (2:ℤ) * m ≤ 10 by omega
  rw [h2, ncard_qZ_eq_std, std_count m hm]

end E8Iso

open E8Iso

/-- **The `E₈` lattice points of squared length at most `10`, with their norm distribution.**

The quadratic form is `qZ v = ∑ᵢ ∑ⱼ vᵢ * E8inv i j * vⱼ` where `E8inv` is the inverse Cartan
matrix of `E₈`, i.e. the squared length in the normalization where the roots have squared length
`2`.  The statement asks for an explicit *computably enumerable* list `L` of the lattice points
`v : Fin 8 → ℤ` with `qZ v ≤ 10`, together with the norm distribution
`1, 240, 2160, 6720, 17520, 30240` at the norms `0, 2, 4, 6, 8, 10`.

## Recipe for the intended proof

`E8inv = L * D * Lᵀ` with `D = diag(4, 7/4, 6/7, 5/6, 4/5, 3/4, 2/3, 1/2)` and `L` unit lower
triangular with rows
`[1,0,0,0,0,0,0,0]`, `[5/4,1,0,0,0,0,0,0]`, `[7/4,5/7,1,0,0,0,0,0]`, `[5/2,10/7,5/6,1,0,0,0,0]`,
`[2,8/7,2/3,4/5,1,0,0,0]`, `[3/2,6/7,1/2,3/5,3/4,1,0,0]`, `[1,4/7,1/3,2/5,1/2,2/3,1,0]`,
`[1/2,2/7,1/6,1/5,1/4,1/3,1/2,1]`.  Writing `y k = v k + ∑_{i>k} L i k * v i` one has

  `420^3 * qZ v = ∑ k, e k * Y k ^ 2`,  `Y k = 420 * y k` (integer),  `e = [105,240,490,504,525,560,630,840]`,

i.e. explicitly `Y k = 420 * v k + ∑_{i>k} B i k * v i` with the column `k` of `B = 420 * L` given by
the entries `i > k`: `k=0`: `525,735,1050,840,630,420,210`; `k=1`: `300,600,480,360,240,120`;
`k=2`: `350,280,210,140,70`; `k=3`: `336,252,168,84`; `k=4`: `315,210,105`; `k=5`: `280,140`;
`k=6`: `210`; `k=7`: none (so `Y 7 = 420 * v 7`).

Since all `e k > 0`, for every `v` with `qZ v ≤ 10` the partial sums `∑_{i≥k} e i * Y i ^ 2` are
`≤ 420^3 * 10`, so enumerating `v 7, v 6, …, v 0` with the pruning "the partial sum stays below
`420^3 * 10`" (each coordinate ranging in a short interval determined by the remaining budget)
visits about `114000` nodes and yields exactly the `56881` points.  The identity above is a finite
polynomial identity (`decide`/`ring`); completeness follows because the terms are non-negative, so
every partial bound used in the enumeration is satisfied with room to spare. -/
theorem e8_lattice_count :
    ∃ L : List (Fin 8 → ℤ), L.Nodup ∧
      (∀ v : Fin 8 → ℤ, Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v ≤ 10 → v ∈ L) ∧
      (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 0)).length = 1 ∧
      (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 2)).length = 240 ∧
      (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 4)).length = 2160 ∧
      (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 6)).length = 6720 ∧
      (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 8)).length = 17520 ∧
      (L.filter (fun v => Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 10)).length = 30240 := by
  refine ⟨E8Iso.L, E8Iso.L_nodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact E8Iso.L_mem hv
  · have hL : (List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = 0)) E8Iso.L)
        = List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = (2*(0:ℕ):ℤ))) E8Iso.L := rfl
    rw [hL, E8Iso.L_count 0 (by norm_num)]
    have hz : E8Lat.SqC 8 ((2*(0:ℕ):ℤ)) = 1 := by
      have hmv : ((2*(0:ℕ):ℤ)) = ((0:ℕ) : ℤ) := by norm_num
      rw [hmv, ← E8Lat.zcnt_eq 0]
      decide
    have hw : E8Lat.WqT 8 ((2*(0:ℕ):ℤ) - 2) / 2 = 0 := by
      have hneg : ((2*(0:ℕ):ℤ) - 2) = -2 := by norm_num
      rw [hneg, E8Lat.WqT_eq_zero_of_neg (by norm_num)]
    rw [hz, hw]
  · have hL : (List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = 2)) E8Iso.L)
        = List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = (2*(1:ℕ):ℤ))) E8Iso.L := rfl
    rw [hL, E8Iso.L_count 1 (by norm_num)]
    have hz : E8Lat.SqC 8 ((2*(1:ℕ):ℤ)) = 112 := by
      have hmv : ((2*(1:ℕ):ℤ)) = ((2:ℕ) : ℤ) := by norm_num
      rw [hmv, ← E8Lat.zcnt_eq 2]
      decide
    have hw : E8Lat.WqT 8 ((2*(1:ℕ):ℤ) - 2) / 2 = 128 := by
      have hval : ((2*(1:ℕ):ℤ) - 2) = ((0:ℕ) : ℤ) := by norm_num
      rw [hval, ← E8Lat.wcnt_eq 0]
      decide
    rw [hz, hw]
  · have hL : (List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = 4)) E8Iso.L)
        = List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = (2*(2:ℕ):ℤ))) E8Iso.L := rfl
    rw [hL, E8Iso.L_count 2 (by norm_num)]
    have hz : E8Lat.SqC 8 ((2*(2:ℕ):ℤ)) = 1136 := by
      have hmv : ((2*(2:ℕ):ℤ)) = ((4:ℕ) : ℤ) := by norm_num
      rw [hmv, ← E8Lat.zcnt_eq 4]
      decide
    have hw : E8Lat.WqT 8 ((2*(2:ℕ):ℤ) - 2) / 2 = 1024 := by
      have hval : ((2*(2:ℕ):ℤ) - 2) = ((2:ℕ) : ℤ) := by norm_num
      rw [hval, ← E8Lat.wcnt_eq 2]
      decide
    rw [hz, hw]
  · have hL : (List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = 6)) E8Iso.L)
        = List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = (2*(3:ℕ):ℤ))) E8Iso.L := rfl
    rw [hL, E8Iso.L_count 3 (by norm_num)]
    have hz : E8Lat.SqC 8 ((2*(3:ℕ):ℤ)) = 3136 := by
      have hmv : ((2*(3:ℕ):ℤ)) = ((6:ℕ) : ℤ) := by norm_num
      rw [hmv, ← E8Lat.zcnt_eq 6]
      decide
    have hw : E8Lat.WqT 8 ((2*(3:ℕ):ℤ) - 2) / 2 = 3584 := by
      have hval : ((2*(3:ℕ):ℤ) - 2) = ((4:ℕ) : ℤ) := by norm_num
      rw [hval, ← E8Lat.wcnt_eq 4]
      decide
    rw [hz, hw]
  · have hL : (List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = 8)) E8Iso.L)
        = List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = (2*(4:ℕ):ℤ))) E8Iso.L := rfl
    rw [hL, E8Iso.L_count 4 (by norm_num)]
    have hz : E8Lat.SqC 8 ((2*(4:ℕ):ℤ)) = 9328 := by
      have hmv : ((2*(4:ℕ):ℤ)) = ((8:ℕ) : ℤ) := by norm_num
      rw [hmv, ← E8Lat.zcnt_eq 8]
      decide
    have hw : E8Lat.WqT 8 ((2*(4:ℕ):ℤ) - 2) / 2 = 8192 := by
      have hval : ((2*(4:ℕ):ℤ) - 2) = ((6:ℕ) : ℤ) := by norm_num
      rw [hval, ← E8Lat.wcnt_eq 6]
      decide
    rw [hz, hw]
  · have hL : (List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = 10)) E8Iso.L)
        = List.filter (fun v : Fin 8 → ℤ => decide (E8NormTwo.qZ v = (2*(5:ℕ):ℤ))) E8Iso.L := rfl
    rw [hL, E8Iso.L_count 5 (by norm_num)]
    have hz : E8Lat.SqC 8 ((2*(5:ℕ):ℤ)) = 14112 := by
      have hmv : ((2*(5:ℕ):ℤ)) = ((10:ℕ) : ℤ) := by norm_num
      rw [hmv, ← E8Lat.zcnt_eq 10]
      decide
    have hw : E8Lat.WqT 8 ((2*(5:ℕ):ℤ) - 2) / 2 = 16128 := by
      have hval : ((2*(5:ℕ):ℤ) - 2) = ((8:ℕ) : ℤ) := by norm_num
      rw [hval, ← E8Lat.wcnt_eq 8]
      decide
    rw [hz, hw]

end Commons.LinearAlgebra.Matrix.Cartan
