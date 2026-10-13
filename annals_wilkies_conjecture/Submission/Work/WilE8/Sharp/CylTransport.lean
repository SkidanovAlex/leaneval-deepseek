/-
  WilE8 — transporting a sharp cell decomposition of the cube to `ℝⁿ`.

  Given `B` an `IsCylDecompOn n (cubeC n)` decomposition, `B.filter (· ⊆ ocube n)` is a
  cylindrical decomposition of the open cube, and its image under `ψV ⁻¹'` is an
  `IsCylDecomp n`.  The bridge is the projection `keep h` to the first `m ≤ n` coordinates:
  `B.filter`'s image under `keep h` is a cylindrical decomposition of `ocube m`, and the
  induction on `m` transports it.
-/
import Mathlib
import Submission.Work.WilE8.Sharp.CellTransport

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE8.Sharp

open WilkiesDesign WilkiesDesign.E

/-! ## API for `IsCylDecompOn` -/

theorem zero_mem_ocube (n : ℕ) : (0 : Fin n → ℝ) ∈ ocube n := fun i => by simp

theorem init_image_cubeC (n : ℕ) :
    Fin.init '' WilkiesDesign.E.cubeC (n+1) = WilkiesDesign.E.cubeC n := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact fun i => hz (Fin.castSucc i)
  · intro hx
    refine ⟨snocR x 0, ?_, init_snocR x 0⟩
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [snocR_last]; norm_num
    · intro j; rw [snocR_castSucc]; exact hx j

theorem IsCylDecompOn.sUnion_eq {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))}
    (h : IsCylDecompOn n A C) : ⋃₀ (C : Set (Set (Fin n → ℝ))) = A := by
  cases n with
  | zero => rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  | succ n => exact h.2.2.1

theorem IsCylDecompOn.isCell {n : ℕ} {A : Set (Fin n → ℝ)} {C : Finset (Set (Fin n → ℝ))}
    (h : IsCylDecompOn n A C) : ∀ c ∈ C, IsCell n c ∧ c.Nonempty := by
  cases n with
  | zero =>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · intro c hc
        rw [Finset.mem_singleton] at hc
        subst hc
        exact ⟨IsCell.zero, Set.univ_nonempty⟩
      · intro c hc
        exact absurd hc (Finset.notMem_empty c)
  | succ n => exact h.1

theorem IsCylDecompOn.pairwiseDisjoint {n : ℕ} {A : Set (Fin n → ℝ)}
    {C : Finset (Set (Fin n → ℝ))} (h : IsCylDecompOn n A C) :
    (C : Set (Set (Fin n → ℝ))).PairwiseDisjoint id := by
  cases n with
  | zero =>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · intro a ha b hb hab
        rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
        exact absurd (ha.trans hb.symm) hab
      · intro a ha
        simp at ha
  | succ n => exact h.2.1

theorem IsCylDecompOn.rec' {n : ℕ} {A : Set (Fin (n+1) → ℝ)}
    {C : Finset (Set (Fin (n+1) → ℝ))} (h : IsCylDecompOn (n+1) A C) :
    IsCylDecompOn n (Fin.init '' A) (C.image (fun c => Fin.init '' c)) :=
  h.2.2.2

/-! ## The first-`m`-coordinates projection -/

/-- The projection of `A ⊆ ℝⁿ` to its first `m` coordinates (`m ≤ n`). -/
def keep {m n : ℕ} (h : m ≤ n) (A : Set (Fin n → ℝ)) : Set (Fin m → ℝ) :=
  {x | ∃ y ∈ A, x = fun i => y (Fin.castLE h i)}

/-- The extension of `y ∈ ℝᵐ` by zeros to `ℝⁿ` (`m ≤ n`). -/
def extend {m n : ℕ} (h : m ≤ n) (y : Fin m → ℝ) : Fin n → ℝ :=
  fun j => if hj : (j : ℕ) < m then y ⟨j, hj⟩ else 0

theorem extend_castLE {m n : ℕ} (h : m ≤ n) (y : Fin m → ℝ) (i : Fin m) :
    extend h y (Fin.castLE h i) = y i := by
  unfold extend
  rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
  exact congrArg y (Fin.ext (by rw [Fin.val_castLE]))

theorem extend_mem_ocube {m n : ℕ} (h : m ≤ n) {y : Fin m → ℝ} (hy : y ∈ ocube m) :
    extend h y ∈ ocube n := by
  intro j
  unfold extend
  split_ifs with hj
  · exact hy _
  · simp

theorem keep_subset_ocube {m n : ℕ} {h : m ≤ n} {A : Set (Fin n → ℝ)} (hA : A ⊆ ocube n) :
    keep h A ⊆ ocube m := by
  rintro x ⟨y, hy, rfl⟩ i
  exact hA hy (Fin.castLE h i)

theorem keep_nonempty {m n : ℕ} {h : m ≤ n} {A : Set (Fin n → ℝ)} (hA : A.Nonempty) :
    (keep h A).Nonempty := by
  obtain ⟨y, hy⟩ := hA
  exact ⟨fun i => y (Fin.castLE h i), y, hy, rfl⟩

theorem keep_self {m : ℕ} (h : m ≤ m) (A : Set (Fin m → ℝ)) : keep h A = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [show (fun i : Fin m => y (Fin.castLE h i)) = y from
      funext fun i => congrArg y (Fin.ext (by rw [Fin.val_castLE]))]
  · intro hx
    exact ⟨x, hx, funext fun i => congrArg x (Fin.ext (by rw [Fin.val_castLE]))⟩

theorem keep_zero_eq_univ {n : ℕ} (h : 0 ≤ n) {A : Set (Fin n → ℝ)} (hA : A.Nonempty) :
    keep (m := 0) h A = Set.univ := by
  obtain ⟨y, hy⟩ := keep_nonempty hA
  rw [Set.eq_univ_iff_forall]
  intro x
  rwa [Subsingleton.elim x y]

theorem keep_projLast {m n : ℕ} (h : m ≤ n + 1) (h' : m ≤ n) (A : Set (Fin (n+1) → ℝ)) :
    keep h A = keep h' (projLast A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Fin.init y, ?_, ?_⟩
    · rw [projLast_eq_init]; exact ⟨y, hy, rfl⟩
    · funext i
      exact congrArg y (Fin.ext (by rw [Fin.val_castSucc, Fin.val_castLE, Fin.val_castLE]))
  · rintro ⟨z, hz, rfl⟩
    rw [projLast_eq_init] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, hy, funext fun i => congrArg y (Fin.ext (by
      rw [Fin.val_castLE, Fin.val_castSucc, Fin.val_castLE]))⟩

theorem keep_init {m n : ℕ} (h : m + 1 ≤ n) (h' : m ≤ n) (A : Set (Fin n → ℝ)) :
    Fin.init '' (keep h A) = keep h' A := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, funext fun i => congrArg y (Fin.ext (by
      rw [Fin.val_castLE, Fin.val_castSucc, Fin.val_castLE]))⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun i => y (Fin.castLE h i), ⟨y, hy, rfl⟩, funext fun i => congrArg y (Fin.ext (by
      rw [Fin.val_castLE, Fin.val_castSucc, Fin.val_castLE]))⟩

theorem keep_isCell (n : ℕ) : ∀ (m : ℕ) (h : m ≤ n) (A : Set (Fin n → ℝ)),
    IsCell n A → IsCell m (keep h A) := by
  induction n with
  | zero =>
      intro m h A hA
      have hm : m = 0 := Nat.le_zero.mp h
      subst m
      rw [keep_self h A]; exact hA
  | succ n ih =>
      intro m h A hA
      rcases eq_or_lt_of_le h with heq | hlt
      · subst m
        rw [keep_self h A]; exact hA
      · have h' : m ≤ n := Nat.lt_succ_iff.mp hlt
        rw [keep_projLast h h' A]
        exact ih m h' (projLast A) (isCell_projLast hA)

/-! ## Pairwise disjointness -/

theorem keep_pairwiseDisjoint (n : ℕ) (B : Finset (Set (Fin n → ℝ)))
    (hB : IsCylDecompOn n (WilkiesDesign.E.cubeC n) B) :
    ∀ (m : ℕ) (h : m ≤ n),
      (B.image (keep h) : Set (Set (Fin m → ℝ))).PairwiseDisjoint id := by
  induction n with
  | zero =>
      intro m h
      have hm : m = 0 := Nat.le_zero.mp h
      subst m
      have hf : B.image (keep (m := 0) h) = B := by
        rw [Finset.image_congr (fun c _ => keep_self h c), Finset.image_id']
      rw [hf]
      exact IsCylDecompOn.pairwiseDisjoint hB
  | succ n ih =>
      intro m h
      rcases eq_or_lt_of_le h with heq | hlt
      · subst m
        have hf : B.image (keep h) = B := by
          rw [Finset.image_congr (fun c _ => keep_self h c), Finset.image_id']
        rw [hf]
        exact IsCylDecompOn.pairwiseDisjoint hB
      · have h' : m ≤ n := Nat.lt_succ_iff.mp hlt
        have hB₁ : IsCylDecompOn n (WilkiesDesign.E.cubeC n)
            (B.image (fun c => Fin.init '' c)) := by
          have h2 := IsCylDecompOn.rec' hB
          rwa [init_image_cubeC n] at h2
        have hset : B.image (fun c => keep h' (projLast c))
            = (B.image (fun c => Fin.init '' c)).image (keep h') := by
          rw [Finset.image_image]
          exact Finset.image_congr (fun c _ => congrArg (keep h') (projLast_eq_init c))
        rw [show B.image (keep h) = B.image (fun c => keep h' (projLast c)) from
          Finset.image_congr (fun c _ => keep_projLast h h' c), hset]
        exact ih (B.image (fun c => Fin.init '' c)) hB₁ m h'

/-! ## Coverage -/

theorem keep_cover (n : ℕ) (B : Finset (Set (Fin n → ℝ)))
    (hB : IsCylDecompOn n (WilkiesDesign.E.cubeC n) B)
    (hcut : ∀ c ∈ B, c ⊆ ocube n ∨ Disjoint c (ocube n)) :
    ∀ (m : ℕ) (h : m ≤ n),
      ⋃₀ (((B.filter fun c => c ⊆ ocube n).image (keep h)) : Set (Set (Fin m → ℝ)))
        = ocube m := by
  intro m h
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [Set.mem_sUnion] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    exact keep_subset_ocube (Finset.mem_filter.mp hc').2 hxc
  · intro y hy
    have hz : extend h y ∈ WilkiesDesign.E.cubeC n :=
      ocube_subset_cube n (extend_mem_ocube h hy)
    rw [← IsCylDecompOn.sUnion_eq hB, Set.mem_sUnion] at hz
    obtain ⟨c, hcB, hzc⟩ := hz
    have hzoc : extend h y ∈ ocube n := extend_mem_ocube h hy
    have hcsub : c ⊆ ocube n := by
      rcases hcut c hcB with hsub | hdisj
      · exact hsub
      · exact absurd hzoc (Set.disjoint_left.mp hdisj hzc)
    exact ⟨keep h c, Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hcB, hcsub⟩, rfl⟩,
      extend h y, hzc, funext fun i => (extend_castLE h y i).symm⟩

/-! ## Auxiliary -/

theorem preimage_nonempty_of_subset_ocube {m : ℕ} {κ : Set (Fin m → ℝ)}
    (hκ : κ.Nonempty) (hoc : κ ⊆ ocube m) : (psiV ⁻¹' κ).Nonempty := by
  obtain ⟨w, hw⟩ := hκ
  refine ⟨fun i => Work.WilE8.psiInv (w i), ?_⟩
  have h1 : psiV (fun i => Work.WilE8.psiInv (w i)) = w :=
    funext fun i => Work.WilE8.StarR.psi_psiInv (hoc hw i)
  rw [Set.mem_preimage, h1]
  exact hw

theorem image_preimage_pairwiseDisjoint {m : ℕ} {D : Finset (Set (Fin m → ℝ))}
    (h : (D : Set (Set (Fin m → ℝ))).PairwiseDisjoint id) :
    (D.image (fun κ => psiV ⁻¹' κ) : Set (Set (Fin m → ℝ))).PairwiseDisjoint id := by
  intro a ha b hb hab
  obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
  obtain ⟨κ', hκ', rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
  exact (h.disjoint_of_ne (Finset.mem_coe.mpr hκ) (Finset.mem_coe.mpr hκ')
    (fun hκκ => hab (by rw [hκκ]))).preimage psiV

/-! ## Main transport -/

theorem transport_aux (m : ℕ) : ∀ (n : ℕ) (h : m ≤ n) (B : Finset (Set (Fin n → ℝ))),
    IsCylDecompOn n (WilkiesDesign.E.cubeC n) B →
    (∀ c ∈ B, c ⊆ ocube n ∨ Disjoint c (ocube n)) →
    IsCylDecomp m (((B.filter fun c => c ⊆ ocube n).image (keep h)).image
      (fun κ => psiV ⁻¹' κ)) := by
  induction m with
  | zero =>
      intro n h B hB hcut
      have hBne : (B.filter fun c => c ⊆ ocube n).Nonempty := by
        have h0c : (0 : Fin n → ℝ) ∈ WilkiesDesign.E.cubeC n := zero_mem_cubeC n
        rw [← IsCylDecompOn.sUnion_eq hB, Set.mem_sUnion] at h0c
        obtain ⟨c, hcB, h0c⟩ := h0c
        refine ⟨c, Finset.mem_filter.mpr ⟨hcB, ?_⟩⟩
        rcases hcut c hcB with hsub | hdisj
        · exact hsub
        · exact absurd (zero_mem_ocube n) (Set.disjoint_left.mp hdisj h0c)
      change (((B.filter fun c => c ⊆ ocube n).image (keep h)).image
        (fun κ => psiV ⁻¹' κ)) = {Set.univ}
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · obtain ⟨c, hc⟩ := hBne
        refine Finset.mem_image.mpr ⟨keep h c, Finset.mem_image.mpr ⟨c, hc, rfl⟩, ?_⟩
        rw [keep_zero_eq_univ h (IsCylDecompOn.isCell hB c (Finset.mem_filter.mp hc).1).2]
        exact Set.preimage_univ
      · intro x hx
        obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ
        rw [keep_zero_eq_univ h (IsCylDecompOn.isCell hB c (Finset.mem_filter.mp hc).1).2]
        exact Set.preimage_univ
  | succ m ih =>
      intro n h B hB hcut
      have h' : m ≤ n := Nat.le_of_succ_le h
      have hcomm : ∀ κ ∈ (B.filter fun c => c ⊆ ocube n).image (keep h),
          Fin.init '' (psiV ⁻¹' κ) = psiV ⁻¹' (Fin.init '' κ) := by
        intro κ hκ
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ
        rw [← projLast_eq_init (psiV ⁻¹' keep h c),
          ← psiV_preimage_projLast (keep_subset_ocube (Finset.mem_filter.mp hc).2),
          projLast_eq_init (keep h c)]
      have hrec : (((B.filter fun c => c ⊆ ocube n).image (keep h)).image
            (fun κ => psiV ⁻¹' κ)).image (fun c => Fin.init '' c)
          = ((B.filter fun c => c ⊆ ocube n).image (keep h')).image
            (fun κ => psiV ⁻¹' κ) := by
        ext z
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨y, hy, hyz⟩
          obtain ⟨κ, hκ, hκy⟩ := hy
          obtain ⟨c, hc, hcκ⟩ := hκ
          refine ⟨keep h' c, ⟨c, hc, rfl⟩, ?_⟩
          rw [← hyz, ← hκy, ← hcκ, ← keep_init h h' c,
            ← hcomm (keep h c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)]
        · rintro ⟨a, ha, haz⟩
          obtain ⟨c, hc, hca⟩ := ha
          refine ⟨psiV ⁻¹' keep h c, ⟨keep h c, ⟨c, hc, rfl⟩, rfl⟩, ?_⟩
          rw [← haz, ← hca, ← keep_init h h' c,
            hcomm (keep h c) (Finset.mem_image.mpr ⟨c, hc, rfl⟩)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨κ, hκ, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hκ
        have hcB : c ∈ B := (Finset.mem_filter.mp hc).1
        have hcsub : c ⊆ ocube n := (Finset.mem_filter.mp hc).2
        exact ⟨psiV_preimage_isCell (m+1) (keep_isCell n (m+1) h c
              (IsCylDecompOn.isCell hB c hcB).1)
            (keep_nonempty (IsCylDecompOn.isCell hB c hcB).2) (keep_subset_ocube hcsub),
          preimage_nonempty_of_subset_ocube (keep_nonempty (IsCylDecompOn.isCell hB c hcB).2)
            (keep_subset_ocube hcsub)⟩
      · refine image_preimage_pairwiseDisjoint (Set.PairwiseDisjoint.subset
          (keep_pairwiseDisjoint n B hB (m+1) h) ?_)
        intro x hx
        rw [Finset.mem_coe] at hx ⊢
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_image.mpr ⟨c, (Finset.mem_filter.mp hc).1, rfl⟩
      · intro z
        have hz : psiV z ∈ ⋃₀ (((B.filter fun c => c ⊆ ocube n).image (keep h)) :
            Set (Set (Fin (m+1) → ℝ))) := by
          rw [keep_cover n B hB hcut (m+1) h]
          exact fun i => Work.WilE10.psi_abs_lt_one (z i)
        rw [Set.mem_sUnion] at hz
        obtain ⟨κ, hκ, hzκ⟩ := hz
        exact ⟨psiV ⁻¹' κ, Finset.mem_image.mpr ⟨κ, hκ, rfl⟩, hzκ⟩
      · rw [hrec]
        exact ih n h' B hB hcut

end Work.WilE8.Sharp
