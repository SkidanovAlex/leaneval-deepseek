import Mathlib
import Submission.Work.BW.Minkowski2.adapted_defs
import Submission.Work.BW.Minkowski2.finrank_comap_castQ
import Submission.Work.BW.Minkowski2.exists_split_step
import Submission.Work.BW.Minkowski2.span_castR_Ksat
import Submission.Work.BW.Minkowski2.linearIndependent_rat_of_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A pure flag of `ℤⁿ` admits an adapted `ℤ`-basis

Given `ℝ`-linearly independent `z 0, …, z (n-1) ∈ ℤⁿ`, we construct a `ℤ`-basis `w 0, …, w (n-1)`
of `ℤⁿ` with `span_ℝ (w 0, …, w j) = span_ℝ (z 0, …, z j)` for every `j`.

The construction uses the saturated (pure) flag `Ksat z j = ℤⁿ ∩ 〈z 0, …, z j〉_ℚ`:
each `Ksat z j` is a pure sublattice of `ℤⁿ` of rank `j+1`, and we split off one primitive
vector at a time (`exists_split_step`) to build a basis `w 0, …, w (n-1)` of `ℤⁿ` with
`span_ℤ (w 0, …, w j) = Ksat z j`.
-/

namespace Work.BW.Minkowski2

open Module

variable {n : ℕ}

/-- Cardinality of the initial segment `{k : Fin n // k ≤ j}`. -/
theorem card_fin_subtype_le (n j : ℕ) :
    Fintype.card {k : Fin n // k.1 ≤ j} = min (j + 1) n := by
  have e : {k : Fin n // k.1 ≤ j} ≃ Fin (min (j + 1) n) :=
  { toFun := fun k => ⟨k.1.1, Nat.lt_min.mpr ⟨Nat.lt_succ_of_le k.2, k.1.2⟩⟩
    invFun := fun i =>
      ⟨⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.min_le_right _ _)⟩,
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le i.2 (Nat.min_le_left _ _))⟩
    left_inv := fun k => by ext; rfl
    right_inv := fun i => by ext; rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

/-- The saturated flag has the expected rank: `Ksat z j` has `ℤ`-rank `j+1`. -/
theorem Ksat_finrank (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    (j : ℕ) (hj : j + 1 ≤ n) : Module.finrank ℤ (Ksat z j) = j + 1 := by
  have hli : LinearIndependent ℚ
      (fun k : {k : Fin n // k.1 ≤ j} => (fun i => (z k.1 i : ℚ))) :=
    hind.comp Subtype.val Subtype.val_injective
  have h1 : Module.finrank ℤ (Ksat z j) = Module.finrank ℚ (Wq z j) :=
    finrank_comap_castQ (Wq z j)
  rw [h1, Wq, finrank_span_eq_card hli]
  rw [card_fin_subtype_le, Nat.min_eq_left hj]

/-- The first splitting step: `Ksat z 0` is free of rank `1`. -/
theorem exists_step_bot (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    (h : 0 + 1 ≤ n) :
    ∃ y : Fin n → ℤ, y ∈ Ksat z 0 ∧
      (∀ (c : ℤ) (x : Fin n → ℤ),
        x ∈ (⊥ : Submodule ℤ (Fin n → ℤ)) → c • y + x = 0 → c = 0) ∧
      (∀ w ∈ Ksat z 0, ∃ c : ℤ, w + c • y ∈ (⊥ : Submodule ℤ (Fin n → ℤ))) := by
  refine exists_split_step ⊥ (Ksat z 0) bot_le (fun c x hc hx => ?_) ?_
  · rw [Submodule.mem_bot] at hx ⊢
    rcases smul_eq_zero.mp hx with h | h
    · exact absurd h hc
    · exact h
  · rw [finrank_bot, Ksat_finrank z hind 0 h]

/-- The general splitting step, from `Ksat z j` to `Ksat z (j+1)`. -/
theorem exists_step_succ (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    (j : ℕ) (h : j + 1 + 1 ≤ n) :
    ∃ y : Fin n → ℤ, y ∈ Ksat z (j + 1) ∧
      (∀ (c : ℤ) (x : Fin n → ℤ), x ∈ Ksat z j → c • y + x = 0 → c = 0) ∧
      (∀ w ∈ Ksat z (j + 1), ∃ c : ℤ, w + c • y ∈ Ksat z j) := by
  have hr : Module.finrank ℤ (Ksat z (j + 1)) = Module.finrank ℤ (Ksat z j) + 1 := by
    rw [Ksat_finrank z hind (j + 1) h, Ksat_finrank z hind j (by omega)]
  exact exists_split_step (Ksat z j) (Ksat z (j + 1)) (Ksat_mono z (Nat.le_succ j))
    (fun c x hc hx => Ksat_pure z j hc hx) hr

/-- The vectors `y j` splitting off one rank at each level: `y j` is primitive modulo
`Ksat z (j-1)` and `Ksat z j = Ksat z (j-1) ⊕ ℤ·y j`. -/
noncomputable def yvec (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ)))) :
    (j : ℕ) → (j + 1 ≤ n) → (Fin n → ℤ) :=
  fun j => Nat.rec
    (fun (h : 0 + 1 ≤ n) => (exists_step_bot z hind h).choose)
    (fun k (_ : (k + 1 ≤ n) → (Fin n → ℤ)) (h : k + 1 + 1 ≤ n) =>
      (exists_step_succ z hind k h).choose) j

/-- The associated `ℤ`-basis candidate: `wfun z hind k = yvec z hind k.1`. -/
noncomputable def wfun (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ)))) (k : Fin n) :
    Fin n → ℤ :=
  yvec z hind k.1 k.2

theorem yvec_zero (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    (h : 0 + 1 ≤ n) : yvec z hind 0 h = (exists_step_bot z hind h).choose := rfl

theorem yvec_succ (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    (k : ℕ) (h : k + 1 + 1 ≤ n) :
    yvec z hind (k + 1) h = (exists_step_succ z hind k h).choose := rfl

/-- `Wq z j = ⊤` once `j` reaches `n-1`. -/
theorem Wq_top (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    {j : ℕ} (hj : n ≤ j + 1) : Wq z j = ⊤ := by
  have hset : Set.range (fun k : {k : Fin n // k.1 ≤ j} => (fun i => (z k.1 i : ℚ)))
      = Set.range (fun k : Fin n => (fun i => (z k i : ℚ))) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨k, rfl⟩; exact ⟨k.1, rfl⟩
    · rintro _ ⟨k, rfl⟩; exact ⟨⟨k, by omega⟩, rfl⟩
  rw [Wq, hset]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [finrank_span_eq_card hind, Fintype.card_fin, Module.finrank_fin_fun]

/-- `Ksat z (n-1) = ℤⁿ`. -/
theorem Ksat_top (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    (hn : 1 ≤ n) : Ksat z (n - 1) = ⊤ := by
  have h : Wq z (n - 1) = ⊤ := Wq_top z hind (by omega)
  rw [Ksat, h]
  ext x
  simp

/-- **Main structural induction.** The first `j+1` vectors `w 0, …, w j` span exactly the
saturated lattice `Ksat z j`. -/
theorem wfun_span (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ)))) :
    ∀ (j : ℕ), j + 1 ≤ n →
      Submodule.span ℤ (wfun z hind '' {k : Fin n | k.1 ≤ j}) = Ksat z j := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hset : ({k : Fin n | k.1 ≤ 0} : Set (Fin n)) = {⟨0, hj⟩} := by
      ext k
      constructor
      · intro hk; exact Fin.ext (Nat.le_zero.mp hk)
      · intro hk
        rw [Set.mem_singleton_iff] at hk
        rw [hk]
        exact Nat.zero_le 0
    rw [hset, Set.image_singleton]
    have hmem : wfun z hind ⟨0, hj⟩ = (exists_step_bot z hind hj).choose := rfl
    rw [hmem]
    obtain ⟨hyO, -, hsp⟩ := (exists_step_bot z hind hj).choose_spec
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hyO
    · intro x hx
      obtain ⟨c, hc⟩ := hsp x hx
      rw [Submodule.mem_bot] at hc
      have hx' : x = (-c) • (exists_step_bot z hind hj).choose := by
        rw [neg_smul, eq_neg_iff_add_eq_zero]; exact hc
      rw [hx']
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  | succ j ih =>
    intro hj
    have hlt : j + 1 < n := hj
    have hset : ({k : Fin n | k.1 ≤ j + 1} : Set (Fin n))
        = insert ⟨j + 1, hlt⟩ {k : Fin n | k.1 ≤ j} := by
      ext k
      constructor
      · intro hk
        rcases Nat.lt_or_ge k.1 (j + 1) with h | h
        · exact Or.inr (Nat.lt_succ_iff.mp h)
        · exact Or.inl (Fin.ext (le_antisymm hk h))
      · rintro (h | hk)
        · rw [h]; exact Nat.le_refl (j + 1)
        · exact le_trans hk (Nat.le_succ j)
    have ih' := ih (by omega : j + 1 ≤ n)
    rw [hset, Set.image_insert_eq, Submodule.span_insert, ih']
    have hmem : wfun z hind ⟨j + 1, hlt⟩ = (exists_step_succ z hind j hj).choose := by
      show yvec z hind (j + 1) hlt = _
      rw [yvec_succ z hind j hlt]
    obtain ⟨hyO, hli, hsp⟩ := (exists_step_succ z hind j hj).choose_spec
    refine le_antisymm ?_ ?_
    · rw [sup_le_iff]
      constructor
      · rw [Submodule.span_le]
        rintro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx, hmem]; exact hyO
      · exact Ksat_mono z (Nat.le_succ j)
    · intro x hx
      obtain ⟨c, hc⟩ := hsp x hx
      have hx' : x = (x + c • (exists_step_succ z hind j hj).choose) +
          (-c) • (exists_step_succ z hind j hj).choose := by
        rw [add_assoc, neg_smul, add_neg_cancel, add_zero]
      rw [hx', hmem]
      refine Submodule.add_mem _ (Submodule.mem_sup_right hc) ?_
      exact Submodule.mem_sup_left (Submodule.smul_mem _ (-c)
        (Submodule.subset_span (Set.mem_singleton _)))

/-- The `wfun` vectors form a `ℤ`-basis of `ℤⁿ`: their columns matrix is unimodular. -/
theorem wfun_det (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    (hn : 1 ≤ n) : IsUnit (Matrix.of (fun i j => wfun z hind j i)).det := by
  have hspan : Submodule.span ℤ (Set.range (wfun z hind)) = ⊤ := by
    have h1 : Submodule.span ℤ (wfun z hind '' {k : Fin n | k.1 ≤ n - 1}) = Ksat z (n - 1) :=
      wfun_span z hind (n - 1) (by omega)
    have h3 : ({k : Fin n | k.1 ≤ n - 1} : Set (Fin n)) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro k
      exact Order.le_sub_one_of_lt k.2
    rw [h3, Set.image_univ] at h1
    rw [h1, Ksat_top z hind hn]
  have key : ∀ i : Fin n, ∃ c : Fin n → ℤ,
      ∑ k, c k • wfun z hind k = Pi.single i 1 := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (by
      have hmem : Pi.single i (1 : ℤ) ∈ (⊤ : Submodule ℤ (Fin n → ℤ)) := Submodule.mem_top
      rwa [← hspan] at hmem)
  choose c hc using key
  have hP : Matrix.of c * Matrix.transpose (Matrix.of (fun i j => wfun z hind j i)) = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hsum : (∑ k : Fin n, Matrix.of c i k *
          Matrix.transpose (Matrix.of (fun i j => wfun z hind j i)) k j)
        = ∑ k : Fin n, (c i k • wfun z hind k) j := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
      simp [Pi.smul_apply]
    rw [hsum, ← Finset.sum_apply, hc i]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hunit := Matrix.isUnit_det_of_left_inverse hP
  rwa [Matrix.det_transpose] at hunit

/-- The first `j+1` vectors `w 0, …, w j` have the same `ℝ`-span as `z 0, …, z j`. -/
theorem wfun_flag (z : Fin n → (Fin n → ℤ))
    (hindq : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))))
    (j : ℕ) (hj : j < n) :
    Submodule.span ℝ {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ j ∧ x = (fun i => (wfun z hindq k i : ℝ))}
      = Submodule.span ℝ {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ j ∧ x = (fun i => (z k i : ℝ))} := by
  have hj1 : j + 1 ≤ n := hj
  have hL : Submodule.span ℝ {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ j ∧
      x = (fun i => (wfun z hindq k i : ℝ))} = Wr z j := by
    have e1 : {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ j ∧ x = (fun i => (wfun z hindq k i : ℝ))}
        = (fun k : Fin n => castR n (wfun z hindq k)) '' {k : Fin n | k.1 ≤ j} := by
      ext x; constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    rw [e1]
    have hmap : Submodule.map (castR n) (Ksat z j)
        = Submodule.span ℤ ((fun k : Fin n => castR n (wfun z hindq k)) '' {k : Fin n | k.1 ≤ j}) := by
      rw [← wfun_span z hindq j hj1, Submodule.map_span]
      congr 1
      ext y; constructor
      · rintro ⟨v, ⟨k, hk, rfl⟩, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨wfun z hindq k, ⟨k, hk, rfl⟩, rfl⟩
    rw [← Submodule.span_span_of_tower (R := ℤ) (S := ℝ), ← hmap]
    have hset2 : (↑(Submodule.map (castR n) (Ksat z j)) : Set (Fin n → ℝ))
        = Set.range (fun x : Ksat z j => castR n x.1) := by
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    rw [hset2]
    exact span_castR_Ksat z j
  have hz : Submodule.span ℝ {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ j ∧
      x = (fun i => (z k i : ℝ))} = Wr z j := by
    rw [Wr]
    congr 1
    ext x; constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩; exact ⟨k, hk, rfl⟩
  rw [hL, hz]

/-- Given `n` `ℝ`-linearly independent lattice vectors `z 0, …, z (n-1)`, there is a `ℤ`-basis
`w 0, …, w (n-1)` of `ℤⁿ` whose partial spans agree with those of the `z`s:
`span (w 0, …, w j) = span (z 0, …, z j)` for every `j`.  (Equivalently: a pure flag of
`ℤⁿ` admits a compatible `ℤ`-basis.) -/
theorem exists_zbasis_adapted {n : ℕ} (z : Fin n → (Fin n → ℤ))
    (hind : LinearIndependent ℝ (fun k : Fin n => (fun i => ((z k) i : ℝ)))) :
    ∃ w : Fin n → (Fin n → ℤ), IsUnit (Matrix.of (fun i j => w j i)).det ∧
      ∀ j : ℕ, j < n →
        Submodule.span ℝ {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ j ∧ x = (fun i => ((w k) i : ℝ))} =
          Submodule.span ℝ {x : Fin n → ℝ | ∃ k : Fin n, k.1 ≤ j ∧ x = (fun i => ((z k) i : ℝ))} := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    exact ⟨fun i => i.elim0, by simp, fun j hj => absurd hj (by omega)⟩
  · have hindq : LinearIndependent ℚ (fun k : Fin n => (fun i => (z k i : ℚ))) :=
      linearIndependent_rat_of_real z hind
    exact ⟨wfun z hindq, wfun_det z hindq hn, fun j hj => wfun_flag z hindq j hj⟩

end Work.BW.Minkowski2
