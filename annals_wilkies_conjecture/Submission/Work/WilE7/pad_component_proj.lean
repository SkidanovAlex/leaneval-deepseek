/-
  Area E7: the `pad` operation (viewing a semi-Pfaffian set in `ℝ^{n+m}` as one in `ℝ^{n+M}`,
  `m ≤ M`) commutes with connected components of points and with the projection onto the
  first `n` coordinates.
-/
import Mathlib
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section

namespace Work.WilE7

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The closed cube -/

theorem cubeC_eq_pi (n : ℕ) : cubeC n = Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp only [cubeC, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]

theorem cubeC_preconnected (n : ℕ) : IsPreconnected (cubeC n) := by
  rw [cubeC_eq_pi]
  refine (convex_pi (s := Set.univ) (t := fun _ : Fin n => Set.Icc (-1 : ℝ) 1) ?_).isPreconnected
  intro i _
  exact convex_Icc _ _

/-! ## `takeZ` / `padZ` -/

/-- `takeZ` in terms of `Fin.castLE`. -/
theorem takeZ_eq_castLE {k K : ℕ} (hm : k ≤ K) (y : Fin K → ℝ) :
    takeZ hm y = fun i => y (Fin.castLE hm i) := rfl

theorem takeZ_mem_cubeC {k K : ℕ} (hm : k ≤ K) {y : Fin K → ℝ} (hy : y ∈ cubeC K) :
    takeZ hm y ∈ cubeC k := by
  intro i
  simpa only [takeZ_eq_castLE] using hy (Fin.castLE hm i)

theorem continuous_takeZ {k K : ℕ} (hm : k ≤ K) :
    Continuous (fun y : Fin K → ℝ => takeZ hm y) := by
  apply continuous_pi
  intro i
  simpa only [takeZ_eq_castLE] using continuous_apply (Fin.castLE hm i)

theorem takeZ_padZ {k K : ℕ} (hm : k ≤ K) (x : Fin k → ℝ) : takeZ hm (padZ K x) = x := by
  funext i
  rw [takeZ_eq_castLE]
  show (if h : ((Fin.castLE hm i : Fin K) : ℕ) < k then
      x ⟨((Fin.castLE hm i : Fin K) : ℕ), h⟩ else 0) = x i
  rw [dif_pos (by rw [Fin.val_castLE]; exact i.isLt)]
  exact congrArg x (Fin.ext (by rw [Fin.val_castLE]))

theorem padZ_mem_cubeC {k K : ℕ} {x : Fin k → ℝ} (hx : x ∈ cubeC k) :
    padZ K x ∈ cubeC K := by
  intro i
  show |(if h : (i : ℕ) < k then x ⟨(i : ℕ), h⟩ else 0)| ≤ 1
  split_ifs with h
  · exact hx ⟨(i : ℕ), h⟩
  · simp

theorem projFirst_padZ {n m M : ℕ} (hm : m ≤ M) (x : Fin (n + m) → ℝ) :
    projFirst n M (padZ (n + M) x) = projFirst n m x := by
  funext i
  show padZ (n + M) x (Fin.castAdd M i) = x (Fin.castAdd m i)
  show (if h : ((Fin.castAdd M i : Fin (n + M)) : ℕ) < n + m then
      x ⟨((Fin.castAdd M i : Fin (n + M)) : ℕ), h⟩ else 0) = x (Fin.castAdd m i)
  rw [dif_pos (by rw [Fin.val_castAdd]; omega)]
  exact congrArg x (Fin.ext (by rw [Fin.val_castAdd, Fin.val_castAdd]))

theorem projFirst_takeZ {n m M : ℕ} (hm : m ≤ M) (y : Fin (n + M) → ℝ) :
    projFirst n M y = projFirst n m (takeZ (Nat.add_le_add_left hm n) y) := by
  funext i
  show y (Fin.castAdd M i) = y (Fin.castLE (Nat.add_le_add_left hm n) (Fin.castAdd m i))
  exact congrArg y (Fin.ext (by rw [Fin.val_castAdd, Fin.val_castLE, Fin.val_castAdd]))

/-! ## Splitting `ℝ^{n+M}` into its first `n+m` and last `M-m` coordinates -/

/-- The point of `ℝ^{n+M}` with first part `a` and last part `z`. -/
def glue {n m M : ℕ} (hm : m ≤ M) :
    (Fin (n + m) → ℝ) × (Fin (M - m) → ℝ) → (Fin (n + M) → ℝ) :=
  fun q i => if h : (i : ℕ) < n + m then q.1 ⟨(i : ℕ), h⟩
    else q.2 ⟨(i : ℕ) - (n + m), by omega⟩

/-- The last `M-m` coordinates of a point of `ℝ^{n+M}`. -/
def suffix {n m M : ℕ} (hm : m ≤ M) (y : Fin (n + M) → ℝ) : Fin (M - m) → ℝ :=
  fun j => y ⟨n + m + (j : ℕ), by omega⟩

theorem glue_pos {n m M : ℕ} (hm : m ≤ M) {q : (Fin (n + m) → ℝ) × (Fin (M - m) → ℝ)}
    {i : Fin (n + M)} (h : (i : ℕ) < n + m) : glue hm q i = q.1 ⟨(i : ℕ), h⟩ := by
  simp only [glue, dif_pos h]

theorem glue_neg {n m M : ℕ} (hm : m ≤ M) {q : (Fin (n + m) → ℝ) × (Fin (M - m) → ℝ)}
    {i : Fin (n + M)} (h : ¬ (i : ℕ) < n + m) :
    glue hm q i = q.2 ⟨(i : ℕ) - (n + m), by omega⟩ := by
  simp only [glue, dif_neg h]

theorem takeZ_glue {n m M : ℕ} (hm : m ≤ M) (a : Fin (n + m) → ℝ) (z : Fin (M - m) → ℝ) :
    takeZ (Nat.add_le_add_left hm n) (glue hm (a, z)) = a := by
  funext i
  rw [takeZ_eq_castLE]
  show glue hm (a, z) (Fin.castLE (Nat.add_le_add_left hm n) i) = a i
  rw [glue_pos hm (by rw [Fin.val_castLE]; exact i.isLt)]
  exact congrArg a (Fin.ext (by rw [Fin.val_castLE]))

theorem glue_takeZ_suffix {n m M : ℕ} (hm : m ≤ M) (y : Fin (n + M) → ℝ) :
    glue hm (takeZ (Nat.add_le_add_left hm n) y, suffix hm y) = y := by
  funext i
  by_cases h : (i : ℕ) < n + m
  · rw [glue_pos hm h]
    show takeZ (Nat.add_le_add_left hm n) y ⟨(i : ℕ), h⟩ = y i
    rw [takeZ_eq_castLE]
    exact congrArg y (Fin.ext (by rw [Fin.val_castLE]))
  · rw [glue_neg hm h]
    show suffix hm y ⟨(i : ℕ) - (n + m), by omega⟩ = y i
    rw [suffix]
    exact congrArg y (Fin.ext (by
      show n + m + ((⟨(i : ℕ) - (n + m), by omega⟩ : Fin (M - m)) : ℕ) = (i : ℕ)
      rw [show ((⟨(i : ℕ) - (n + m), by omega⟩ : Fin (M - m)) : ℕ) = (i : ℕ) - (n + m) from rfl]
      omega))

theorem glue_mem_cubeC {n m M : ℕ} (hm : m ≤ M) {a : Fin (n + m) → ℝ} {z : Fin (M - m) → ℝ}
    (ha : a ∈ cubeC (n + m)) (hz : z ∈ cubeC (M - m)) :
    glue hm (a, z) ∈ cubeC (n + M) := by
  intro i
  by_cases h : (i : ℕ) < n + m
  · rw [glue_pos hm h]
    exact ha ⟨(i : ℕ), h⟩
  · rw [glue_neg hm h]
    exact hz ⟨(i : ℕ) - (n + m), by omega⟩

theorem suffix_mem_cubeC {n m M : ℕ} (hm : m ≤ M) {y : Fin (n + M) → ℝ}
    (hy : y ∈ cubeC (n + M)) : suffix hm y ∈ cubeC (M - m) := by
  intro j
  exact hy ⟨n + m + (j : ℕ), by omega⟩

theorem continuous_glue {n m M : ℕ} (hm : m ≤ M) :
    Continuous (glue (n := n) (M := M) hm) := by
  apply continuous_pi
  intro i
  by_cases h : (i : ℕ) < n + m
  · have hfun : (fun q : (Fin (n + m) → ℝ) × (Fin (M - m) → ℝ) => glue hm q i)
        = fun q => q.1 ⟨(i : ℕ), h⟩ := by
      funext q
      rw [glue_pos hm h]
    rw [hfun]
    exact (continuous_apply _).comp continuous_fst
  · have hfun : (fun q : (Fin (n + m) → ℝ) × (Fin (M - m) → ℝ) => glue hm q i)
        = fun q => q.2 ⟨(i : ℕ) - (n + m), by omega⟩ := by
      funext q
      rw [glue_neg hm h]
    rw [hfun]
    exact (continuous_apply _).comp continuous_snd

/-! ## Evaluation commutes with `pad` -/

theorem EAChain.pad_ell {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (j : Fin r)
    (y : Fin K → ℝ) :
    (EAChain.pad hm c).ell j y = c.ell j (takeZ hm y) := by
  have hsum : (∑ i : Fin K, (if h : (i : ℕ) < k then c.a j ⟨(i : ℕ), h⟩ else 0) * y i)
      = ∑ i : Fin k, c.a j i * y (Fin.castLE hm i) := by
    have hvan : ∀ x ∈ (Finset.univ : Finset (Fin K)),
        x ∉ Finset.univ.map ⟨Fin.castLE hm, Fin.castLE_injective hm⟩ →
        (if h : (x : ℕ) < k then c.a j ⟨(x : ℕ), h⟩ else 0) * y x = 0 := by
      intro x _ hx
      have hxk : ¬ (x : ℕ) < k := by
        intro hlt
        apply hx
        rw [Finset.mem_map]
        exact ⟨⟨(x : ℕ), hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
      rw [dif_neg hxk, zero_mul]
    calc (∑ i : Fin K, (if h : (i : ℕ) < k then c.a j ⟨(i : ℕ), h⟩ else 0) * y i)
        = ∑ i ∈ Finset.univ.map ⟨Fin.castLE hm, Fin.castLE_injective hm⟩,
            (if h : (i : ℕ) < k then c.a j ⟨(i : ℕ), h⟩ else 0) * y i :=
          (Finset.sum_subset (Finset.subset_univ _) hvan).symm
      _ = ∑ i : Fin k, (if h : (↑(Fin.castLE hm i) : ℕ) < k then
              c.a j ⟨(↑(Fin.castLE hm i) : ℕ), h⟩ else 0) * y (Fin.castLE hm i) :=
          Finset.sum_map _ _ _
      _ = ∑ i : Fin k, c.a j i * y (Fin.castLE hm i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Fin.val_castLE, dif_pos i.isLt]
  simp only [EAChain.ell, EAChain.pad]
  rw [hsum, takeZ_eq_castLE]

theorem EAPoly.pad_eaEval {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (Q : EAPoly k r)
    (y : Fin K → ℝ) :
    eaEval (EAChain.pad hm c) (EAPoly.pad hm Q) y = eaEval c Q (takeZ hm y) := by
  have hfun : (Sum.elim y fun j => Real.exp ((EAChain.pad hm c).ell j y)) ∘
        (Sum.map (Fin.castLE hm) id) =
      (Sum.elim (takeZ hm y) fun j => Real.exp (c.ell j (takeZ hm y))) := by
    funext s
    rcases s with i | j
    · show y (Fin.castLE hm i) = takeZ hm y i
      rfl
    · show Real.exp ((EAChain.pad hm c).ell j y) = Real.exp (c.ell j (takeZ hm y))
      rw [EAChain.pad_ell hm c j y]
  simp only [eaEval, EAPoly.pad]
  rw [MvPolynomial.eval_rename, hfun]

theorem Basic.pad_holds {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (B : Basic k r)
    (y : Fin K → ℝ) :
    (Basic.pad hm B).holds (EAChain.pad hm c) y ↔ B.holds c (takeZ hm y) := by
  simp only [Basic.holds, Basic.pad]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · have h := h1 (EAPoly.pad hm f) (List.mem_map_of_mem (f := EAPoly.pad hm) hf)
      rwa [EAPoly.pad_eaEval] at h
    · have h := h2 (EAPoly.pad hm g) (List.mem_map_of_mem (f := EAPoly.pad hm) hg)
      rwa [EAPoly.pad_eaEval] at h
  · rintro ⟨h1, h2⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨f', hf', rfl⟩ := List.mem_map.mp hf
      rw [EAPoly.pad_eaEval]
      exact h1 f' hf'
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      rw [EAPoly.pad_eaEval]
      exact h2 g' hg'

theorem SemiPf.pad_set {k K : ℕ} (hm : k ≤ K) (X : WilkiesDesign.E.SemiPf k) :
    (SemiPf.pad hm X).set = {y | y ∈ cubeC K ∧ takeZ hm y ∈ X.set} := by
  ext y
  have hb : (∃ B ∈ (SemiPf.pad hm X).basics, B.holds (SemiPf.pad hm X).c y) ↔
      ∃ B ∈ X.basics, B.holds X.c (takeZ hm y) := by
    constructor
    · rintro ⟨B, hB, hh⟩
      obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
      exact ⟨B', hB', (Basic.pad_holds hm X.c B' y).mp hh⟩
    · rintro ⟨B, hB, hh⟩
      exact ⟨Basic.pad hm B, List.mem_map_of_mem (f := Basic.pad hm) hB,
        (Basic.pad_holds hm X.c B y).mpr hh⟩
  constructor
  · intro hy
    obtain ⟨h1, h2⟩ := hy
    exact ⟨h1, takeZ_mem_cubeC hm h1, hb.mp h2⟩
  · rintro ⟨h1, _, h2⟩
    exact ⟨h1, hb.mpr h2⟩

/-! ## The main statement -/

theorem pad_component_proj {n m M : ℕ} (hm : m ≤ M) (X : WilkiesDesign.E.SemiPf (n + m))
    (p : Fin (n + m) → ℝ) :
    (connectedComponentIn (Work.WilE7.SemiPf.pad (Nat.add_le_add_left hm n) X).set
        (Work.WilE7.padZ (n + M) p)
        = {y | y ∈ (Work.WilE7.SemiPf.pad (Nat.add_le_add_left hm n) X).set ∧
            Work.WilE7.takeZ (Nat.add_le_add_left hm n) y ∈ connectedComponentIn X.set p}) ∧
      WilkiesDesign.E.projFirst n M ''
          connectedComponentIn (Work.WilE7.SemiPf.pad (Nat.add_le_add_left hm n) X).set
            (Work.WilE7.padZ (n + M) p)
        = WilkiesDesign.E.projFirst n m '' connectedComponentIn X.set p := by
  have hYcube : ∀ y : Fin (n + M) → ℝ,
      y ∈ (SemiPf.pad (Nat.add_le_add_left hm n) X).set → y ∈ cubeC (n + M) := by
    intro y hy
    rw [SemiPf.pad_set (Nat.add_le_add_left hm n) X, Set.mem_setOf_eq] at hy
    exact hy.1
  have hYtake : ∀ y : Fin (n + M) → ℝ,
      y ∈ (SemiPf.pad (Nat.add_le_add_left hm n) X).set →
        takeZ (Nat.add_le_add_left hm n) y ∈ X.set := by
    intro y hy
    rw [SemiPf.pad_set (Nat.add_le_add_left hm n) X, Set.mem_setOf_eq] at hy
    exact hy.2
  have hYmem : ∀ y : Fin (n + M) → ℝ, y ∈ cubeC (n + M) →
      takeZ (Nat.add_le_add_left hm n) y ∈ X.set →
        y ∈ (SemiPf.pad (Nat.add_le_add_left hm n) X).set := by
    intro y h1 h2
    rw [SemiPf.pad_set (Nat.add_le_add_left hm n) X, Set.mem_setOf_eq]
    exact ⟨h1, h2⟩
  have hXsub : X.set ⊆ cubeC (n + m) := fun x hx => hx.1
  have hZeq : {y : Fin (n + M) → ℝ |
        y ∈ (SemiPf.pad (Nat.add_le_add_left hm n) X).set ∧
          takeZ (Nat.add_le_add_left hm n) y ∈ connectedComponentIn X.set p}
      = glue hm '' (connectedComponentIn X.set p ×ˢ cubeC (M - m)) := by
    ext y
    constructor
    · rintro ⟨hy, hyC⟩
      refine ⟨(takeZ (Nat.add_le_add_left hm n) y, suffix hm y), ⟨hyC, ?_⟩, ?_⟩
      · exact suffix_mem_cubeC hm (hYcube y hy)
      · exact glue_takeZ_suffix hm y
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨a, z⟩ := q
      obtain ⟨haC, hz⟩ := hq
      refine ⟨hYmem _ ?_ ?_, ?_⟩
      · exact glue_mem_cubeC hm (hXsub (connectedComponentIn_subset X.set p haC)) hz
      · rw [takeZ_glue hm a z]
        exact connectedComponentIn_subset X.set p haC
      · rw [takeZ_glue hm a z]
        exact haC
  have hZpre : IsPreconnected {y : Fin (n + M) → ℝ |
        y ∈ (SemiPf.pad (Nat.add_le_add_left hm n) X).set ∧
          takeZ (Nat.add_le_add_left hm n) y ∈ connectedComponentIn X.set p} := by
    rw [hZeq]
    have h1 : IsPreconnected (connectedComponentIn X.set p : Set (Fin (n + m) → ℝ)) :=
      isPreconnected_connectedComponentIn
    have h2 : IsPreconnected (cubeC (M - m)) := cubeC_preconnected (M - m)
    exact (h1.prod h2).image (glue hm) (continuous_glue hm).continuousOn
  have key : connectedComponentIn (SemiPf.pad (Nat.add_le_add_left hm n) X).set
        (padZ (n + M) p)
      = {y : Fin (n + M) → ℝ |
          y ∈ (SemiPf.pad (Nat.add_le_add_left hm n) X).set ∧
            takeZ (Nat.add_le_add_left hm n) y ∈ connectedComponentIn X.set p} := by
    by_cases hp : p ∈ X.set
    · have hqY : padZ (n + M) p ∈ (SemiPf.pad (Nat.add_le_add_left hm n) X).set := by
        refine hYmem _ (padZ_mem_cubeC hp.1) ?_
        rw [takeZ_padZ]
        exact hp
      have hqZ : padZ (n + M) p ∈ {y : Fin (n + M) → ℝ |
          y ∈ (SemiPf.pad (Nat.add_le_add_left hm n) X).set ∧
            takeZ (Nat.add_le_add_left hm n) y ∈ connectedComponentIn X.set p} :=
        ⟨hqY, by rw [takeZ_padZ]; exact mem_connectedComponentIn hp⟩
      refine Set.Subset.antisymm ?_
        (IsPreconnected.subset_connectedComponentIn hZpre hqZ (fun y hy => hy.1))
      intro y hy
      refine ⟨connectedComponentIn_subset _ _ hy, ?_⟩
      have hq_comp := mem_connectedComponentIn hqY
      have hpre : IsPreconnected (takeZ (Nat.add_le_add_left hm n) ''
          connectedComponentIn (SemiPf.pad (Nat.add_le_add_left hm n) X).set
            (padZ (n + M) p)) :=
        isPreconnected_connectedComponentIn.image _ (continuous_takeZ _).continuousOn
      have hpmem : p ∈ takeZ (Nat.add_le_add_left hm n) ''
          connectedComponentIn (SemiPf.pad (Nat.add_le_add_left hm n) X).set
            (padZ (n + M) p) :=
        ⟨padZ (n + M) p, hq_comp, takeZ_padZ _ _⟩
      have hsub : takeZ (Nat.add_le_add_left hm n) ''
          connectedComponentIn (SemiPf.pad (Nat.add_le_add_left hm n) X).set
            (padZ (n + M) p) ⊆ X.set := by
        rintro x ⟨w, hw, rfl⟩
        exact hYtake w (connectedComponentIn_subset _ _ hw)
      exact hpre.subset_connectedComponentIn hpmem hsub ⟨y, hy, rfl⟩
    · have hqY : padZ (n + M) p ∉ (SemiPf.pad (Nat.add_le_add_left hm n) X).set := by
        intro h
        have h' := hYtake _ h
        rw [takeZ_padZ] at h'
        exact hp h'
      rw [connectedComponentIn_eq_empty hqY]
      ext y
      constructor
      · intro hy
        exact (Set.notMem_empty y hy).elim
      · rintro ⟨hy, hyC⟩
        rw [connectedComponentIn_eq_empty hp] at hyC
        exact hyC
  refine ⟨key, ?_⟩
  rw [key]
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨takeZ (Nat.add_le_add_left hm n) y, hy.2, (projFirst_takeZ hm y).symm⟩
  · rintro x ⟨c, hc, rfl⟩
    have hcX : c ∈ X.set := connectedComponentIn_subset X.set p hc
    refine ⟨padZ (n + M) c,
      ⟨hYmem _ (padZ_mem_cubeC hcX.1) (by rw [takeZ_padZ]; exact hcX),
        by rw [takeZ_padZ]; exact hc⟩, ?_⟩
    exact projFirst_padZ hm c

end Work.WilE7
