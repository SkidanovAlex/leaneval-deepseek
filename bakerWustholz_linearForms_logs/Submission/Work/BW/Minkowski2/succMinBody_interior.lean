import Mathlib
import Submission.Work.BW.Minkowski2.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lattice points in the interior of the `j`-th successive-minimum body

For a lattice `Λ ⊆ ℝᵈ`, a convex symmetric body `K` and `1 ≤ j ≤ d`, the lattice points of `Λ`
lying in the interior of `Work.BW.succMinBody Λ K j • K` may only have their first `j - 1`
coordinates non-zero, provided the standard basis vectors are lattice vectors realising the
successive minima (`eᵢ ∈ succMinBody Λ K (i+1) • K`).

The proof rests on a single structural fact: with `a := succMinBody Λ K j` and `j₀` the first index
`m` with `a ≤ succMinBody Λ K m`, every `λ < a` satisfies
`finrank ℝ (span ℝ (Λ ∩ λ • K)) < j₀`.  On the other hand the `j₀ - 1` standard basis vectors
`e₀, …, e_{j₀-2}` lie in `Λ ∩ λ • K` for a suitable `λ < a`, so `Λ ∩ λ • K` has a subspace of
dimension `j₀ - 1`; combined with the rank bound this forces every lattice point of `Λ ∩ λ • K`
into `span {e₀, …, e_{j₀-2}} ⊆ span {e₀, …, e_{j-1}}`.
-/

namespace Work.BW.Minkowski2

open scoped Pointwise Topology

open Work.BW

/-- A convex symmetric nonempty subset of `ℝᵈ` contains `0` (as the midpoint of `x` and `-x`). -/
theorem zero_mem_of_convex_symm {d : ℕ} {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hne : K.Nonempty) : (0 : Fin d → ℝ) ∈ K := by
  obtain ⟨x, hx⟩ := hne
  have h := hKc hx (hsym x hx) (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  simpa using h

/-- Dilation `c • K ⊆ c' • K` of a convex set containing `0`, for `0 ≤ c ≤ c'`. -/
theorem smul_set_subset_smul_of_le {d : ℕ} {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (h0 : (0 : Fin d → ℝ) ∈ K) {c c' : ℝ} (hc : 0 ≤ c) (hcc' : c ≤ c') :
    c • K ⊆ c' • K := by
  intro x hx
  rw [Set.mem_smul_set] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  rcases eq_or_lt_of_le hcc' with h | h
  · subst h; exact ⟨y, hy, rfl⟩
  · have hc'pos : 0 < c' := lt_of_le_of_lt hc h
    refine ⟨(c / c') • y, ?_, ?_⟩
    · have hle1 : c / c' ≤ 1 := by rw [div_le_one hc'pos]; exact hcc'
      have hratio : c / c' + (1 - c / c') = 1 := by ring
      have := hKc hy h0 (by positivity) (by linarith) hratio
      simpa using this
    · rw [smul_smul, mul_comm, div_mul_cancel₀ _ (ne_of_gt hc'pos)]

/-- A point of the interior of `a • K` (`a > 0`) lies in `μ • K` for some `0 < μ < a`. -/
theorem exists_smul_lt_of_mem_interior {d : ℕ} {K : Set (Fin d → ℝ)} {a : ℝ} (ha : 0 < a)
    {w : Fin d → ℝ} (hwint : w ∈ interior (a • K)) :
    ∃ μ : ℝ, 0 < μ ∧ μ < a ∧ w ∈ μ • K := by
  have hmem : (a • K) ∈ 𝓝 w :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hwint) interior_subset
  have hcont : ContinuousAt (fun t : ℝ => (1 + t) • w) 0 := by fun_prop
  have hpre : (fun t : ℝ => (1 + t) • w) ⁻¹' (a • K) ∈ 𝓝 (0:ℝ) := by
    apply hcont; simpa using hmem
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨δ, hδpos, hδ⟩ := hpre
  refine ⟨a / (1 + δ/2), by positivity, ?_, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]; nlinarith [hδpos]
  · have htw : (1 + δ/2) • w ∈ a • K := by
      apply hδ
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
    rw [Set.mem_smul_set] at htw ⊢
    obtain ⟨k, hk, hk_eq⟩ := htw
    refine ⟨k, hk, ?_⟩
    rw [div_eq_inv_mul, ← smul_smul, hk_eq, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

theorem succMinBody_nonneg {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ)) (K : Set (Fin d → ℝ))
    (m : ℕ) : 0 ≤ succMinBody Λ K m :=
  Real.sInf_nonneg (fun _ hx => le_of_lt hx.1)

/-- If `lam < succMinBody Λ K m` then `Λ ∩ lam • K` spans a subspace of dimension `< m`. -/
theorem not_le_finrank_of_lt_succMinBody {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ))
    (K : Set (Fin d → ℝ)) {m : ℕ} {lam : ℝ} (h : lam < succMinBody Λ K m) :
    ¬ (0 < lam ∧ m ≤ Module.finrank ℝ
        (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)))) := by
  intro hmem
  have hbdd : BddBelow {l : ℝ | 0 < l ∧ m ≤ Module.finrank ℝ
      (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (l • K)))} :=
    ⟨0, fun l hl => le_of_lt hl.1⟩
  have hle : succMinBody Λ K m ≤ lam := csInf_le hbdd hmem
  linarith

/-- The standard basis vectors of `ℝᵈ` are linearly independent. -/
theorem stdVec_linearIndependent (d : ℕ) :
    LinearIndependent ℝ (stdVec : Fin d → (Fin d → ℝ)) := by
  have h : (stdVec : Fin d → (Fin d → ℝ)) = ⇑(Pi.basisFun ℝ (Fin d)) := by
    funext i; rw [Pi.basisFun_apply]; rfl
  rw [h]
  exact (Pi.basisFun ℝ (Fin d)).linearIndependent

theorem succMinBody_interior {d : ℕ} (Λ : Submodule ℤ (Fin d → ℝ)) (K : Set (Fin d → ℝ))
    (hKconv : Convex ℝ K) (hKsym : ∀ x ∈ K, -x ∈ K)
    (hstd : ∀ i : Fin d, Work.BW.stdVec i ∈ Λ)
    (hreal : ∀ i : Fin d,
      Work.BW.stdVec i ∈ Work.BW.smulSet (Work.BW.succMinBody Λ K (i.1 + 1)) K)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ d) (w : Fin d → ℝ) (hw : w ∈ Λ)
    (hwint : w ∈ interior (Work.BW.smulSet (Work.BW.succMinBody Λ K j) K)) :
    ∀ i : Fin d, j ≤ (i : ℕ) → w i = 0 := by
  classical
  -- `K` is nonempty
  have hKne : K.Nonempty := by
    rcases K.eq_empty_or_nonempty with h | h
    · rw [h] at hwint; simp [Work.BW.smulSet] at hwint
    · exact h
  have h0K : (0 : Fin d → ℝ) ∈ K := zero_mem_of_convex_symm hKconv hKsym hKne
  set a : ℝ := Work.BW.succMinBody Λ K j with ha
  have ha_nonneg : 0 ≤ a := by rw [ha]; exact succMinBody_nonneg Λ K j
  by_cases ha0 : a = 0
  · -- then `w = 0` and there is nothing to prove
    have hw0 : w = 0 := by
      have h1 : w ∈ Work.BW.smulSet a K := interior_subset hwint
      rw [Work.BW.mem_smulSet] at h1
      obtain ⟨k, hk, hk0⟩ := h1
      rw [hk0, ha0, zero_smul]
    intro i _
    rw [hw0]; rfl
  · have ha_pos : 0 < a := lt_of_le_of_ne' ha_nonneg ha0
    -- a point `w ∈ interior (a • K)` lies in `μ • K` for some `0 < μ < a`
    have hwint' : w ∈ interior (a • K) := by
      have h := hwint; rw [Work.BW.smulSet_eq] at h; exact h
    obtain ⟨μ, hμpos, hμlt, hwμ⟩ := exists_smul_lt_of_mem_interior ha_pos hwint'
    -- the first index `j0` with `a ≤ succMinBody Λ K j0`
    have hfind : ∃ m : ℕ, a ≤ Work.BW.succMinBody Λ K m := ⟨j, ha.le⟩
    obtain ⟨j0, hj0spec, hj0le, hj0min⟩ :
        ∃ j0 : ℕ, a ≤ Work.BW.succMinBody Λ K j0 ∧ j0 ≤ j ∧
          ∀ m : ℕ, m < j0 → Work.BW.succMinBody Λ K m < a :=
      ⟨Nat.find hfind, Nat.find_spec hfind, Nat.find_min' hfind ha.le,
        fun m hm => not_le.mp (Nat.find_min hfind hm)⟩
    -- the subspace spanned by `e₀, …, e_{j0-2}`
    let e : Fin (j0 - 1) → Fin d := fun m => ⟨m.val, by omega⟩
    -- all standard basis vectors of index `< j0 - 1` are lattice points of `λ • K` for a common
    -- `λ < a`; choose `λ` dominating `μ` and all these levels
    set T : Finset ℝ := insert μ ((Finset.range (j0 - 1)).image
        (fun m : ℕ => Work.BW.succMinBody Λ K (m + 1))) with hTdef
    have hTne : T.Nonempty := by rw [hTdef]; exact Finset.insert_nonempty _ _
    set M : ℝ := T.max' hTne with hMdef
    have hMlt : M < a := by
      rw [hMdef]
      refine (Finset.max'_lt_iff T hTne).mpr ?_
      intro y hy
      rw [hTdef] at hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hμlt
      · rw [Finset.mem_image] at hy
        obtain ⟨n, hn, hny⟩ := hy
        rw [Finset.mem_range] at hn
        rw [← hny]
        exact hj0min (n+1) (by omega)
    have hμM : μ ≤ M := by
      rw [hMdef]
      exact Finset.le_max' T μ (by rw [hTdef]; exact Finset.mem_insert_self μ _)
    set lam : ℝ := (M + a) / 2 with hlamdef
    have hMlam : M < lam := by rw [hlamdef]; linarith
    have hlamlt : lam < a := by rw [hlamdef]; linarith
    have hlampos : 0 < lam := by linarith
    -- rank bound at level `lam`
    have hrank : Module.finrank ℝ (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K))) < j0 :=
      Nat.lt_of_not_le (fun hle =>
        not_le_finrank_of_lt_succMinBody Λ K (lt_of_lt_of_le hlamlt hj0spec) ⟨hlampos, hle⟩)
    let f : Fin (j0 - 1) → (Fin d → ℝ) := fun m => Work.BW.stdVec (e m)
    have heinj : Function.Injective e := by
      intro x y h
      exact Fin.ext (by have := congrArg Fin.val h; simpa [e] using this)
    have hfli : LinearIndependent ℝ f := by
      have : f = Work.BW.stdVec ∘ e := rfl
      rw [this]
      exact (stdVec_linearIndependent d).comp e heinj
    have hUfin : Module.finrank ℝ (Submodule.span ℝ (Set.range f)) = j0 - 1 := by
      rw [finrank_span_eq_card hfli, Fintype.card_fin]
    have hmemUV : Set.range f ⊆ (Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)) :
        Set (Fin d → ℝ)) := by
      rintro _ ⟨m, rfl⟩
      have hm : ((e m : Fin d) : ℕ) + 1 < j0 := by
        have := m.isLt; simp only [e] at this ⊢; omega
      refine Submodule.subset_span ⟨hstd (e m), ?_⟩
      have hreal' := hreal (e m)
      rw [Work.BW.smulSet_eq] at hreal'
      refine smul_set_subset_smul_of_le hKconv h0K (succMinBody_nonneg Λ K _) ?_ hreal'
      have hmemT : Work.BW.succMinBody Λ K (((e m : Fin d) : ℕ) + 1) ∈ T := by
        rw [hTdef, Finset.mem_insert]
        right
        rw [Finset.mem_image]
        exact ⟨m.val, Finset.mem_range.mpr m.isLt, rfl⟩
      have hleM : Work.BW.succMinBody Λ K (((e m : Fin d) : ℕ) + 1) ≤ M := by
        rw [hMdef]; exact Finset.le_max' T _ hmemT
      linarith
    have hUV : Submodule.span ℝ (Set.range f) ≤
        Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)) := Submodule.span_le.mpr hmemUV
    have hUeqV : Submodule.span ℝ (Set.range f) =
        Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)) := by
      refine Submodule.eq_of_le_of_finrank_le hUV ?_
      rw [hUfin]; exact Nat.le_sub_one_of_lt hrank
    have hwV : w ∈ Submodule.span ℝ ((Λ : Set (Fin d → ℝ)) ∩ (lam • K)) :=
      Submodule.subset_span ⟨hw, smul_set_subset_smul_of_le hKconv h0K (le_of_lt hμpos)
        (le_trans hμM (le_of_lt hMlam)) hwμ⟩
    have hwU : w ∈ Submodule.span ℝ (Set.range f) := by rw [hUeqV]; exact hwV
    -- every element of `span (range f)` has vanishing `i`-th coordinate for `j ≤ i`
    intro i hi
    refine Submodule.span_induction (p := fun x (_ : x ∈ Submodule.span ℝ (Set.range f)) =>
      x i = 0) ?_ ?_ ?_ ?_ hwU
    · rintro _ ⟨m, rfl⟩
      show Work.BW.stdVec (e m) i = 0
      have hne : i ≠ e m := by
        intro hcon
        have hval : (e m : Fin d).val < (i : ℕ) := by
          have := m.isLt; simp only [e] at this ⊢; omega
        rw [hcon] at hval
        exact absurd hval (lt_irrefl _)
      simp [Work.BW.stdVec, hne]
    · simp
    · intro x y hx hy hpx hpy; simp [hpx, hpy]
    · intro c x hx hpx; simp [hpx]

end Work.BW.Minkowski2
