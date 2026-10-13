/-
  `HmaxAux` — auxiliary lemmas for `Work.WilkG4c.hmax_of_choice_lists`.

  This is a *fresh* module: it only imports `Mathlib` and
  `Submission.Work.WilG4c.Engine`, both of which load correctly in this workspace.  The
  lemmas below are the standard tools of the `WilG4c` area — the count-vector listing of a
  multiset, smoothness of the iterated directional derivative `iterDir`, Clairaut/Schwarz for
  adjacent directions, permutation invariance of `iterDir`, the identification of `iterDir`
  with `iteratedFDeriv` on a direction tuple, and the `2`-approximate maximiser of a bounded
  family of values.

  The same lemmas already exist in sibling modules of the area
  (`countvec_perm.lean`, `IterDirAux.lean`, `iterDir_swap.lean`, `iterDir_perm.lean`,
  `iterDir_eq_iteratedFDeriv.lean`, `exists_nearmax_of_bdd.lean`), with the same proofs.
  They are restated here because the compiled artifacts of those modules currently do not
  expose their declarations to importers: `import`ing them succeeds, yet `#check` on their
  source-declared names reports "unknown identifier".
-/
import Mathlib
import Submission.Work.WilG4c.Engine

open scoped Topology

set_option autoImplicit false
noncomputable section

namespace Work.WilkG4c

open Work.WilkG4c

/-! ## 1. The count-vector listing of a multiset -/

/-- The multiset of a list `M` is the sum, over all `i : Fin n`, of `count i M` copies of
`{i}`: the "count vector" expansion of `M`. -/
theorem hmax_countvec_sum {n : ℕ} (M : List (Fin n)) :
    (Finset.univ.sum (fun i : Fin n =>
        (Multiset.ofList M).count i • ({i} : Multiset (Fin n)))) = (Multiset.ofList M) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Multiset.ofList M).toFinset)
    (fun x _ hx => by
      rw [Multiset.mem_toFinset] at hx
      rw [Multiset.count_eq_zero.mpr hx, zero_nsmul])]
  exact Multiset.toFinset_sum_count_nsmul_eq _

/-- The "count vector" listing of `M` is a permutation of `M`. -/
theorem hmax_countvec_perm {n r : ℕ} (M : List (Fin n)) (hM : M.length ≤ r) :
    M.Perm ((Finset.univ.sum (fun i : Fin n =>
        (Multiset.ofList M).count i • ({i} : Multiset (Fin n)))).toList) := by
  rw [hmax_countvec_sum M]
  exact Multiset.coe_eq_coe.mp (by rw [Multiset.coe_toList])

/-! ## 2. Smoothness of the iterated directional derivative -/

/-- **Smoothness of the iterated directional derivative.**  If `G` is `C^{|L| + k}` at `z`,
then its iterated directional derivative `iterDir L G` is `C^k` at `z`. -/
theorem hmax_iterDir_contDiffAt {m : ℕ} (G : (Fin m → ℝ) → ℝ) :
    ∀ (L : List (Fin m)) (k : ℕ) (z : Fin m → ℝ),
      ContDiffAt ℝ (L.length + k) G z → ContDiffAt ℝ k (iterDir L G) z := by
  intro L
  induction L with
  | nil => intro k z hG; simpa using hG
  | cons i M ih =>
    intro k z hG
    rw [iterDir_cons]
    apply ContDiffAt.clm_apply
    · apply ContDiffAt.fderiv_right
      · exact ih (k + 1) z (by
          have e : (↑M.length + ↑(k + 1) : WithTop ℕ∞) = ↑(i :: M).length + ↑k := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm]
          rw [e]; exact hG)
      · exact le_refl _
    · exact contDiffAt_const

/-! ## 3. Clairaut/Schwarz for the two outermost directions -/

/-- **Two outermost derivatives commute.** If `H` is `C²` at `z`, then the iterated directional
derivative along `[a, b]` agrees with the one along `[b, a]`. -/
theorem hmax_iterDir_pair_swap {m : ℕ} (H : (Fin m → ℝ) → ℝ) (a b : Fin m) (z : Fin m → ℝ)
    (hH : ContDiffAt ℝ 2 H z) :
    iterDir [a, b] H z = iterDir [b, a] H z := by
  simp only [iterDir_cons, iterDir_nil]
  have hdiff : DifferentiableAt ℝ (fderiv ℝ H) z :=
    (hH.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)).differentiableAt one_ne_zero
  have key : ∀ (v w : Fin m → ℝ),
      fderiv ℝ (fun y => (fderiv ℝ H y) v) z w = (fderiv ℝ (fderiv ℝ H) z w) v := by
    intro v w
    rw [fderiv_clm_apply (c := fderiv ℝ H) (u := fun _ : Fin m → ℝ => v) hdiff
      (differentiableAt_const v)]
    simp [ContinuousLinearMap.flip_apply]
  rw [key (Pi.single b 1) (Pi.single a 1), key (Pi.single a 1) (Pi.single b 1)]
  exact (hH.isSymmSndFDerivAt (by norm_num)).eq (Pi.single a 1) (Pi.single b 1)

/-- **Adjacent transposition.** For a function `G` that is `C^{|M|+2}` at `z`, the iterated
directional derivative along `a :: b :: M` equals that along `b :: a :: M`. -/
theorem hmax_iterDir_swap {m : ℕ} (G : (Fin m → ℝ) → ℝ) (a b : Fin m) (M : List (Fin m))
    (z : Fin m → ℝ) (hG : ContDiffAt ℝ (M.length + 2) G z) :
    iterDir (a :: b :: M) G z = iterDir (b :: a :: M) G z := by
  have hH : ContDiffAt ℝ 2 (iterDir M G) z :=
    hmax_iterDir_contDiffAt G M 2 z (by simpa using hG)
  have e₁ : iterDir (a :: b :: M) G z = iterDir [a, b] (iterDir M G) z := by
    simp only [iterDir_cons, iterDir_nil]
  have e₂ : iterDir (b :: a :: M) G z = iterDir [b, a] (iterDir M G) z := by
    simp only [iterDir_cons, iterDir_nil]
  rw [e₁, e₂]
  exact hmax_iterDir_pair_swap (iterDir M G) a b z hH

/-! ## 4. Permutation invariance of `iterDir` -/

/-- The iterated directional derivative `iterDir L G` is invariant under permuting the list,
for `C^{|L|}` functions: the mixed partial derivatives commute. -/
theorem hmax_iterDir_perm {m : ℕ} (G : (Fin m → ℝ) → ℝ) {L L' : List (Fin m)} (h : L.Perm L')
    (z : Fin m → ℝ) (hG : ContDiffAt ℝ L.length G z) : iterDir L G z = iterDir L' G z := by
  have key : ∀ (L L' : List (Fin m)), L.Perm L' → ∀ z, ContDiffAt ℝ L.length G z →
      iterDir L G z = iterDir L' G z := by
    intro L L' h
    induction h with
    | nil => intro z _; rfl
    | cons x _ ih =>
      intro z hG
      simp only [iterDir_cons]
      congr 1
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hG.eventually (by simp)] with y hy
      exact ih y (hy.of_le (by simp [List.length_cons]))
    | swap x y l =>
      intro z hG
      have he : (↑((y :: x :: l).length) : WithTop ℕ∞) = ↑l.length + 2 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring
      exact hmax_iterDir_swap G y x l z (he ▸ hG)
    | trans h₁ _ ih₁ ih₂ =>
      intro z hG
      exact (ih₁ z hG).trans (ih₂ z (by rwa [← h₁.length_eq]))
  exact key L L' h z hG

/-! ## 5. `iterDir` as an `iteratedFDeriv` -/

/-- `iterDir L G z` is the iterated Fréchet derivative of `G` at `z` evaluated on the list of
direction vectors `Pi.single (L.get k) 1`. -/
theorem hmax_iterDir_eq_iteratedFDeriv {m : ℕ} (L : List (Fin m)) (G : (Fin m → ℝ) → ℝ)
    (z : Fin m → ℝ) (hG : ContDiffAt ℝ L.length G z) :
    iterDir L G z =
      iteratedFDeriv ℝ L.length G z (fun k => Pi.single (L.get k) 1) := by
  revert G z
  induction L with
  | nil =>
    intro G z _
    simp [iterDir_nil, iteratedFDeriv_zero_apply]
  | cons i L' ih =>
    intro G z hG
    simp only [iterDir_cons]
    have hev : ∀ᶠ w in 𝓝 z, ContDiffAt ℝ (L'.length) G w := by
      have hne : ((L'.length + 1 : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
      have h1 := hG.eventually hne
      filter_upwards [show ∀ᶠ y in 𝓝 z, ContDiffAt ℝ (L'.length + 1) G y from by
        simpa using h1] with w hw
      exact hw.of_le (by exact_mod_cast Nat.le_succ L'.length :
        (L'.length : WithTop ℕ∞) ≤ ((L'.length + 1 : ℕ) : WithTop ℕ∞))
    have heq : iterDir L' G =ᶠ[𝓝 z]
        (fun w => iteratedFDeriv ℝ (L'.length) G w (fun k => Pi.single (L'.get k) 1)) := by
      filter_upwards [hev] with w hw
      exact ih G w hw
    rw [heq.fderiv_eq]
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ (L'.length) G) z :=
      hG.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self L'.length)
    rw [fderiv_continuousMultilinear_apply_const_apply (c := iteratedFDeriv ℝ (L'.length) G)
          hdiff (fun k => Pi.single (L'.get k) 1) (Pi.single i 1)]
    change (((fderiv ℝ (iteratedFDeriv ℝ L'.length G) z) (Pi.single i 1))
        (fun k => Pi.single (L'.get k) 1)) =
      (iteratedFDeriv ℝ (L'.length + 1) G z) (fun k => Pi.single ((i :: L').get k) 1)
    rw [iteratedFDeriv_succ_apply_left (f := G) (x := z) (n := L'.length)]
    rfl

/-! ## 6. A `2`-approximate maximiser -/

/-- If a non-empty set of points `S` carries a bounded set of values `|g|`, then it contains a
point whose value is within a factor `2` of the supremum (a `2`-approximate maximiser). -/
theorem hmax_nearmax_of_bdd {n : ℕ} {S : Set (Fin n → ℝ)} (hS : S.Nonempty)
    (g : (Fin n → ℝ) → ℝ) (hbdd : BddAbove ((fun y => |g y|) '' S)) :
    ∃ y ∈ S, ∀ y' ∈ S, |g y'| ≤ 2 * |g y| := by
  have hne : ((fun y => |g y|) '' S).Nonempty := hS.image (fun y => |g y|)
  have hmem : ∀ y ∈ S, |g y| ≤ sSup ((fun y => |g y|) '' S) := fun y hy =>
    le_csSup hbdd ⟨y, hy, rfl⟩
  by_cases ht : sSup ((fun y => |g y|) '' S) ≤ 0
  · obtain ⟨y, hy⟩ := hS
    refine ⟨y, hy, ?_⟩
    have h0 : sSup ((fun y => |g y|) '' S) = 0 :=
      le_antisymm ht (le_trans (abs_nonneg (g y)) (hmem y hy))
    have hyg : |g y| = 0 := le_antisymm (h0 ▸ hmem y hy) (abs_nonneg (g y))
    intro y' hy'
    have h1 : |g y'| ≤ 0 := h0 ▸ hmem y' hy'
    rw [hyg]
    linarith
  · have hlt : sSup ((fun y => |g y|) '' S) / 2 < sSup ((fun y => |g y|) '' S) := by linarith
    obtain ⟨b, hbT, hb⟩ := (lt_csSup_iff hbdd hne).mp hlt
    obtain ⟨y, hy, hyb⟩ := hbT
    refine ⟨y, hy, ?_⟩
    rw [← hyb] at hb
    intro y' hy'
    have h1 : |g y'| ≤ sSup ((fun y => |g y|) '' S) := hmem y' hy'
    linarith

end Work.WilkG4c
