import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.DimAPI.stratum_nullDimLE
import Submission.Work.WilE7.DimAPI.nullDimLE_mono_dim
import Submission.Work.WilE7.DimAPI.nullDimLT_basics

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep

/-! ## Helper lemmas for `sigmaLevelOfPair`

The level-pair Σ is assembled from the `hE5`-decomposition of the level-agreeing pair set and the
`hE6`-frontier sets of its top-dimensional members.  The measure bookkeeping needs only three
elementary facts (monotonicity of `Polynomial.eval` over `ℕ`, nullity of the empty set, and
finite unions of null-dimensional sets) plus the one geometric point of the construction, namely
that *the first vertex of a point of the level-agreeing pair set lies in the first stratum* — which
is what lets the measure of the whole Σ be read off from `stratum_nullDimLE` of `T`. -/

/-- Monotonicity of `Polynomial.eval` for `ℕ`-valued polynomials (all coefficients are
nonnegative). -/
theorem slp_eval_mono_nat {p : Polynomial ℕ} {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- The empty set has null dimension at every index. -/
theorem slp_nullDimLE_empty {N μ : ℕ} :
    NullDimLE (∅ : Set (Fin N → ℝ)) μ := by
  intro e
  rw [Set.image_empty]
  simp

/-- Finite unions (over a list) of `NullDimLE` sets are `NullDimLE`. -/
theorem slp_nullDimLE_list_iUnion {N μ : ℕ} {α : Type*} (L : List α)
    (f : α → Set (Fin N → ℝ)) (h : ∀ A ∈ L, NullDimLE (f A) μ) :
    NullDimLE (⋃ A ∈ L, f A) μ := by
  induction L with
  | nil =>
    have hnil : (⋃ A ∈ ([] : List α), f A) = (∅ : Set (Fin N → ℝ)) := by simp
    rw [hnil]
    exact slp_nullDimLE_empty
  | cons a t ih =>
    have hsplit : (⋃ A ∈ (a :: t), f A) = f a ∪ (⋃ A ∈ t, f A) := by
      ext x
      simp only [Set.mem_iUnion, List.mem_cons, Set.mem_union]
      constructor
      · rintro ⟨A, hA | hA, hx⟩
        · exact Or.inl (hA ▸ hx)
        · exact Or.inr ⟨A, hA, hx⟩
      · rintro (hx | ⟨A, hA, hx⟩)
        · exact ⟨a, Or.inl rfl, hx⟩
        · exact ⟨A, Or.inr hA, hx⟩
    rw [hsplit]
    exact NullDimLE.union (h a List.mem_cons_self)
      (ih fun A hA => h A (List.mem_cons_of_mem a hA))

/-- **The first vertex of a level-agreeing pair lies in the first stratum.**  If `z` lies in
`absLevelPairSet T T'`, i.e. its two vertices are a pair `(u,v)` with `u ∈ T.X.set`,
`v ∈ T'.X.set`, the same base point `π_n u = π_n v` *and* the same last coordinate, then the
first vertex `u` (read in the `Fin (0 + ·)` bookkeeping) is a point of `T.X.set`. -/
theorem slp_firstVertex_mem {n m : ℕ} (T T' : Stratum 0 (n + (m + 1)))
    {z : Fin (0 + pPair n m) → ℝ} (hz : z ∈ (absLevelPairSet T T').set) :
    absPtUp (n := n) (m := m)
      (projFirst (n + (m + 1)) (n + (m + 1)) (absPt z)) ∈ T.X.set := by
  set e : Fin (pPair n m) ≃ Fin (0 + pPair n m) :=
    (Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm with he
  have hmem : (fun i : Fin (pPair n m) => z (e i))
      ∈ (Work.WilE7.levelGlue (absReindex T) (absReindex T')).set := by
    have h := hz
    rw [absLevelPairSet, Work.WilE7.sp_reindex_set] at h
    simpa only [Set.mem_ofPred_eq] using h
  rw [Work.WilE7.levelGlue_set] at hmem
  simp only [Set.mem_ofPred_eq] at hmem
  have h2 : absPtUp (n := n) (m := m)
      (projFirst (n + (m + 1)) (n + (m + 1))
        (fun i : Fin (pPair n m) => z (e i))) ∈ T.X.set := by
    rw [← mem_absReindex]
    exact hmem.1
  convert h2 using 2
  funext j
  congr 1

theorem sigmaLevelOfPair
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
      (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (n m : ℕ) (T T' : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good) (hT' : T'.Good)
    (F : ℕ) (hF : (Work.WilE7.CoreStep.absLevelPairSet T T').fmt ≤ F) :
    ∃ (a a' : ℕ) (b b' : Polynomial ℕ)
      (Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
      (Fl : List (WilkiesDesign.E.SemiPf (0 + Work.WilE7.CoreStep.pPair n m))),
      (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet T T').set ∧
          W.X.fmt ≤ a ∧ W.deg ≤ b.eval (Work.WilE7.CoreStep.absLevelPairSet T T').deg) ∧
      ((Work.WilE7.CoreStep.absLevelPairSet T T').set = ⋃ W ∈ Wl, W.X.set) ∧
      (∀ S ∈ Fl, S.fmt ≤ a' ∧
          S.deg ≤ b'.eval (Work.WilE7.CoreStep.absLevelPairSet T T').deg) ∧
      (∀ W ∈ Wl, Work.WilE7.MainDesign.NullDimLT
          (WilkiesDesign.E.projFirst n (m + 1) ''
            (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) ''
              (Work.WilE7.MainDesign.absPt '' W.X.set)))
          (n + (m + 1) - T.j + 1)) ∧
      (∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j = n + (m + 1) - T.j →
        ∃ S ∈ Fl, S.set = closure W.X.set \ W.X.set) ∧
      (∀ S ∈ Fl, Work.WilE7.MainDesign.NullDimLT
          (WilkiesDesign.E.projFirst n (m + 1) ''
            (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1)) ''
              (Work.WilE7.MainDesign.absPt '' S.set)))
          (n + (m + 1) - T.j + 1)) := by
  classical
  -- (0) `hE5` on the level-agreeing pair set: the list `Sl` of all its `Good` strata.
  obtain ⟨a, b, hE5'⟩ := hE5 F
  obtain ⟨Sl, hSllen, hSlgood, hSlcover, hSldisj⟩ :=
    hE5' 0 (pPair n m) (absLevelPairSet T T') hF
  -- (0') `hE6` at a format bound large enough for every member of `Sl`: the frontier sets.
  obtain ⟨a6, b6, hE6'⟩ := hE6 (max F a)
  have hsubL : ∀ W ∈ Sl, W.X.set ⊆ (absLevelPairSet T T').set := by
    intro W hW z hz
    rw [hSlcover]
    exact Set.mem_iUnion.mpr ⟨W, Set.mem_iUnion.mpr ⟨hW, hz⟩⟩
  have hchoice : ∀ W ∈ Sl, ∃ Y : SemiPf (0 + pPair n m),
      Y.fmt ≤ a6 ∧ Y.deg ≤ b6.eval W.X.deg ∧ Y.set = closure W.X.set \ W.X.set := by
    intro W hW
    obtain ⟨Y, Y', h1, h2, h3, h4, h5, h6⟩ :=
      hE6' 0 (pPair n m) W.X (le_trans (hSlgood W hW).1 (le_max_right F a))
    exact ⟨Y', h3, h4, by rw [h6, fiberClosure_zero]⟩
  -- the list of frontier sets of the top-dimensional members of `Sl`
  let Fl : List (SemiPf (0 + pPair n m)) :=
    (Sl.attach.filter (fun W => decide (pPair n m - W.1.j = n + (m + 1) - T.j))).map
      (fun W => (hchoice W.1 W.2).choose)
  have hFlmem : ∀ (W : Stratum 0 (pPair n m)) (hW : W ∈ Sl),
      pPair n m - W.j = n + (m + 1) - T.j → (hchoice W hW).choose ∈ Fl := by
    intro W hW hc
    rw [List.mem_map]
    refine ⟨⟨W, hW⟩, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨List.mem_attach _ _, by simpa only [decide_eq_true_eq] using hc⟩
  have hFlmem' : ∀ S ∈ Fl, ∃ (W : Stratum 0 (pPair n m)) (hW : W ∈ Sl),
      pPair n m - W.j = n + (m + 1) - T.j ∧ S = (hchoice W hW).choose := by
    intro S hS
    rw [List.mem_map] at hS
    obtain ⟨W, hW, hSeq⟩ := hS
    rw [List.mem_filter] at hW
    obtain ⟨hWL, hc⟩ := hW
    exact ⟨W.1, W.2, by simpa only [decide_eq_true_eq] using hc, hSeq.symm⟩
  refine ⟨a, a6, b, b6.comp b, Sl, Fl, ?_, hSlcover, ?_, ?_, ?_, ?_⟩
  · -- (1) the members of `Sl`: `Good`, contained, format and degree
    intro W hW
    exact ⟨(hSlgood W hW).2.2, hsubL W hW, (hSlgood W hW).1, (hSlgood W hW).2.1⟩
  · -- (3) the members of `Fl`: format and degree
    intro S hS
    obtain ⟨W, hW, hc, hSeq⟩ := hFlmem' S hS
    obtain ⟨h1, h2, h3⟩ := (hchoice W hW).choose_spec
    rw [hSeq]
    refine ⟨h1, ?_⟩
    rw [Polynomial.eval_comp]
    refine le_trans h2 (slp_eval_mono_nat ?_)
    refine le_trans ?_ (hSlgood W hW).2.1
    rw [Stratum.deg]
    exact Nat.le_add_right _ _
  · -- (4) the measure condition for the members of `Sl`: the first vertex sits in `T`, and
    -- `T` has `NullDimLE` its dimension (`stratum_nullDimLE`)
    intro W hW
    refine NullDimLT.mono (Work.WilE7.DimAPI.stratum_nullDimLE T hT) ?_
    rintro y ⟨v, ⟨w, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    have hzL : z ∈ (absLevelPairSet T T').set := hsubL W hW hz
    refine ⟨absPt (absPtUp (n := n) (m := m)
        (projFirst (n + (m + 1)) (n + (m + 1)) (absPt z))),
      ⟨_, slp_firstVertex_mem T T' hzL, rfl⟩, ?_⟩
    exact congrArg (projFirst n (m + 1))
      (absPtInv_absPtUp (n := n) (m := m)
        (projFirst (n + (m + 1)) (n + (m + 1)) (absPt z)))
  · -- (5) the frontier of a top-dimensional member is in `Fl`
    intro W hW hc
    exact ⟨(hchoice W hW).choose, hFlmem W hW hc, (hchoice W hW).choose_spec.2.2⟩
  · -- (6) the measure condition for the members of `Fl`: decompose the frontier by `hE5`; every
    -- nonempty piece of the decomposition is a `Good` stratum in the frontier of the
    -- top-dimensional `Good` stratum `W`, so it has *more* equations (`frontierDrop_abs`), i.e.
    -- strictly smaller dimension, and `stratum_nullDimLE` bounds its projection
    intro S hS
    obtain ⟨W, hW, hc, hSeq⟩ := hFlmem' S hS
    rw [hSeq]
    set S' := (hchoice W hW).choose with hS'def
    have hS'set : S'.set = closure W.X.set \ W.X.set := (hchoice W hW).choose_spec.2.2
    have hS'fmt : S'.fmt ≤ max (max F a) a6 :=
      le_trans (hchoice W hW).choose_spec.1 (le_max_right (max F a) a6)
    obtain ⟨a2, b2, hE5''⟩ := hE5 (max (max F a) a6)
    obtain ⟨Tl, -, hTlgood, hTlcover, -⟩ := hE5'' 0 (pPair n m) S' hS'fmt
    have hpoint : ∀ V ∈ Tl, NullDimLE (projFirst n (m + 1) ''
        (projFirst (n + (m + 1)) (n + (m + 1)) '' (absPt '' V.X.set)))
        (n + (m + 1) - T.j) := by
      intro V hV
      have hVgood : V.Good := (hTlgood V hV).2.2
      have hVsub : V.X.set ⊆ closure W.X.set \ W.X.set := by
        rw [← hS'set, hTlcover]
        intro z hz
        exact Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hV, hz⟩⟩
      by_cases hne : V.X.set.Nonempty
      · have hlt : W.j < V.j := frontierDrop_abs W V (hSlgood W hW).2.2 hVgood hVsub hne
        have hVj : V.j ≤ (n + (m + 1)) + (n + (m + 1)) := by
          obtain ⟨z, hz⟩ := hne
          have hrank := (hVgood z hz).2.1
          have hle := Matrix.rank_le_card_width (Matrix.of fun (a : Fin V.j)
            (l : Fin (pPair n m)) => eaEval V.X.c (eaD V.X.c (Fin.natAdd 0 l) (V.h a)) z)
          rw [hrank] at hle
          simpa using hle
        have h2 : (n + (m + 1)) + (n + (m + 1)) - V.j
            < (n + (m + 1)) + (n + (m + 1)) - W.j := by omega
        rw [hc] at h2
        exact Work.WilE7.DimAPI.nullDimLE_mono_dim
          (NullDimLE.projFirst (n := n) (m := m + 1)
            (Work.WilE7.DimAPI.stratum_nullDimLE V hVgood)) (le_of_lt h2)
      · have hempty : V.X.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        rw [hempty]
        simp only [Set.image_empty]
        exact slp_nullDimLE_empty
    have hunion := slp_nullDimLE_list_iUnion Tl (fun V => projFirst n (m + 1) ''
        (projFirst (n + (m + 1)) (n + (m + 1)) '' (absPt '' V.X.set))) hpoint
    have hconv : projFirst n (m + 1) '' (projFirst (n + (m + 1)) (n + (m + 1)) ''
        (absPt '' S'.set))
        = ⋃ V ∈ Tl, projFirst n (m + 1) '' (projFirst (n + (m + 1)) (n + (m + 1)) ''
            (absPt '' V.X.set)) := by
      rw [hTlcover]
      simp only [Set.image_iUnion]
    rw [hconv]
    exact hunion

end Work.CoreStep
