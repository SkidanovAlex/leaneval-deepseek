/-
  `pairAvoid_witness_limit` — the **closedness half** of the per-level attainment dichotomy for
  the vertical row of `CoreLT_succ` (node `G1`, `Work.WilE7.Endgame.attain_dichotomy_of_pairAvoid`).

  Setting.  `S`, `T` are absolute pieces of `ℝ^{n+(m+1)}`; `C ⊆ ℝⁿ` carries continuous sheets
  `s j` of `S` (`hsub`); `Vl` stratifies the *level-pair set*
  `absLevelPairSet S T = {(u,v) ∈ S × T : projTop u = projTop v}` (`hVcov`), its strata are
  `Good` and lie in the pair set (`hVsub`); the base projections of the low strata
  (`hbound` + `hlow`) and of the frontiers of the top strata (`htop`) avoid `C`.

  Claim.  The set of base points of `C` at which the level `ℓ x = (s j x) (Fin.last m)` is
  *attained* on the fibre of `T` is relatively closed: if `x t → x₀` in `C` and `ℓ` is attained at
  every `x t`, it is attained at `x₀`.

  Proof (contradiction).  Choose witnesses `z t ∈ T.X.set` over `(x t, ℓ (x t))`; pass to a
  subsequence with `absPt (z t) → w` (the cube is compact).  The pair points
  `P t = (absPtUp (x t ++ s j (x t)), absPtUp (absPt (z t)))` are points of `absLevelPairSet S T`
  (`mem_absLevelPairSet`) and converge to `p⋆ = (u₀, absPtUp w)`.
  * A stratum of `Vl` containing `P t` cannot be low: its base projection would hit the base point
    `x t ∈ C`, contradicting `hlow`.  Hence every `P t` lies in a *top* stratum, and since the
    top strata form a finite family, `p⋆` lies in the closure of one of them
    (`witness_mem_iUnion_closure`).
  * `p⋆` lies in no stratum of `Vl`: otherwise `hVsub` puts it in the pair set and
    `mem_absLevelPairSet_elim` exhibits `w` as a point of `absSet T` over `(x₀, ℓ x₀)`, i.e. an
    attainment at `x₀`, contradicting the assumption.
  * So `p⋆` lies in the *frontier* of a top stratum `V`, and the base of `p⋆` is `x₀`; hence
    `x₀ ∈ pairFrontierBaseFst V` (`witness_mem_pairFrontierBaseFst`), contradicting `htop`.

  The three helper lemmas above the theorem (`witness_pairPtUp_tendsto`, `witness_projTop_eq`,
  `witness_mem_pairFrontierBaseFst`, `witness_mem_iUnion_closure`) are the four elementary
  analytic/topological inputs of this argument; they live in the sibling modules
  `WilE7/Endgame/witness_*.lean`.

  Note: `hS`, `hT`, `himm`, `hVgood` are carried along for uniformity with the calling context
  (they are used by the *openness* half `G2`), and are not needed here.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.CoreStep.mem_absLevelPairSet_elim
import Submission.Work.CoreStep.persist_aux_pairPtUp_mem
import Submission.Work.CoreStep.CrossDefs
import Submission.Work.CoreStep.havoid_of_sigma
import Submission.Work.WilE7.Endgame.witness_pairPtUp_tendsto
import Submission.Work.WilE7.Endgame.witness_mem_iUnion_closure
import Submission.Work.WilE7.Endgame.witness_mem_pairFrontierBaseFst
import Submission.Work.WilE7.Endgame.witness_projTop_eq

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep
open Work.CoreStep

theorem pairAvoid_witness_limit {n m k : ℕ}
    (S T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hS : S.Good) (hT : T.Good) (himm : Work.WilE7.CoreLTSuccPlan.HImm T)
    (C : Set (Fin n → ℝ))
    (s : Fin k → (Fin n → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ (j : Fin k) (x : Fin n → ℝ), x ∈ C →
      Work.WilE7.CoreStep.absPtUp (n := n) (m := m) (Fin.append x (s j x)) ∈ S.X.set)
    (Vl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)))
    (hVgood : ∀ V ∈ Vl, V.Good)
    (hVsub : ∀ V ∈ Vl, V.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet S T).set)
    (hVcov : (Work.WilE7.CoreStep.absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set)
    (hbound : ∀ V ∈ Vl, ∀ z ∈ V.X.set,
      Work.WilE7.CoreStep.pPair n m - V.j ≤ n + (m + 1) - S.j)
    (hlow : ∀ V ∈ Vl, Work.WilE7.CoreStep.pPair n m - V.j < n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairSubBaseFst n m V) C)
    (htop : ∀ V ∈ Vl, Work.WilE7.CoreStep.pPair n m - V.j = n + (m + 1) - S.j →
      Disjoint (Work.CoreStep.pairFrontierBaseFst n m V) C)
    (j : Fin k)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ C)
    (x : ℕ → Fin n → ℝ) (hxC : ∀ t, x t ∈ C) (hxtend : Filter.Tendsto x Filter.atTop (nhds x₀))
    (hAtt : ∀ t, Work.WilE7.CoreStep.AttainAt T (fun y => (s j y) (Fin.last m)) (x t)) :
    Work.WilE7.CoreStep.AttainAt T (fun y => (s j y) (Fin.last m)) x₀ := by
  classical
  let ℓ : (Fin n → ℝ) → ℝ := fun y => (s j y) (Fin.last m)
  change Work.WilE7.CoreStep.AttainAt T ℓ x₀
  have hℓcont : ContinuousOn ℓ C :=
    (continuous_apply (Fin.last m)).comp_continuousOn (hcont j)
  by_contra hnot
  -- witnesses over the sequence
  have hAtt' : ∀ t, ∃ z ∈ T.X.set,
      Work.WilE7.CoreStep.projTop n m (absPt z) = Fin.snoc (x t) (ℓ (x t)) := fun t => hAtt t
  choose z hzT hzproj using hAtt'
  -- compactness
  have hzcube : ∀ t, absPt (z t) ∈ cubeC (n + (m + 1)) :=
    fun t => Work.CoreStep.absSet_subset_cubeC' T ⟨z t, hzT t, rfl⟩
  obtain ⟨w, _hwcube, φ, hφmono, hφtend⟩ :=
    (Work.CoreStep.cubeC_isCompact' (n + (m + 1))).tendsto_subseq hzcube
  set xk : ℕ → Fin n → ℝ := fun t => x (φ t) with hxk
  set zk : ℕ → Fin (0 + (n + (m + 1))) → ℝ := fun t => z (φ t) with hzk
  have hxkmem : ∀ t, xk t ∈ C := fun t => hxC (φ t)
  have hxktend : Filter.Tendsto xk Filter.atTop (nhds x₀) := hxtend.comp hφmono.tendsto_atTop
  have hxkw : Filter.Tendsto xk Filter.atTop (nhdsWithin x₀ C) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxktend, Filter.Eventually.of_forall hxkmem⟩
  have hzwtend : Filter.Tendsto (fun t => absPt (zk t)) Filter.atTop (nhds w) := by
    simpa only [hzk, Function.comp_def] using hφtend
  set u₀ : Fin (pDim n m) → ℝ := absPtUp (n := n) (m := m) (Fin.append x₀ (s j x₀)) with hu₀
  set W : Fin (pDim n m) → ℝ := absPtUp (n := n) (m := m) w with hW
  set pstar : Fin (0 + pPair n m) → ℝ := pairPtUp u₀ W with hpstar
  -- elementary facts about the reindexing maps
  have hWup : absPt W = w := by
    rw [hW]
    exact Work.WilE7.CoreStep.absPtInv_absPtUp w
  have hdown : ∀ y : Fin (0 + (n + (m + 1))) → ℝ, absPtUp (n := n) (m := m) (absPt y) = y :=
    fun y => (Work.CoreStep.absPtUp_eq_absPtInv (n := n) (m := m) (absPt y)).trans
      (Work.WilE7.DimAPI.absPtInv_absPt (n + (m + 1)) y)
  have hcontUp : Continuous (fun y : Fin (n + (m + 1)) → ℝ => absPtUp (n := n) (m := m) y) := by
    have h1 : (fun y : Fin (n + (m + 1)) → ℝ => absPtUp (n := n) (m := m) y)
        = ⇑(Work.CoreStep.absPtInvCLM (n + (m + 1))) := by
      funext y
      rw [Work.CoreStep.absPtInvCLM_apply, Work.CoreStep.absPtUp_eq_absPtInv]
    rw [h1]
    exact (Work.CoreStep.absPtInvCLM (n + (m + 1))).continuous
  -- the second coordinate converges
  have hzktend : Filter.Tendsto zk Filter.atTop (nhds W) := by
    have h2 : Filter.Tendsto (fun t => absPtUp (n := n) (m := m) (absPt (zk t)))
        Filter.atTop (nhds (absPtUp (n := n) (m := m) w)) :=
      (hcontUp.tendsto w).comp hzwtend
    have h3 : (fun t => absPtUp (n := n) (m := m) (absPt (zk t))) = zk := by
      funext t
      exact hdown (zk t)
    rw [h3] at h2
    rwa [← hW] at h2
  -- the first coordinate converges
  have hsheetcont : ContinuousOn
      (fun y : Fin n → ℝ => absPtUp (n := n) (m := m) (Fin.append y (s j y))) C := by
    have h1 : ContinuousOn (fun y : Fin n → ℝ => (y, s j y)) C :=
      ContinuousOn.prodMk (f := fun y : Fin n → ℝ => y) (g := s j)
        continuousOn_id (hcont j)
    have h2 : Continuous (fun p : (Fin n → ℝ) × (Fin (m + 1) → ℝ) => Fin.append p.1 p.2) :=
      Fin.continuous_append n (m + 1)
    exact hcontUp.comp_continuousOn (h2.comp_continuousOn h1)
  have huktend : Filter.Tendsto
      (fun t => absPtUp (n := n) (m := m) (Fin.append (xk t) (s j (xk t))))
      Filter.atTop (nhds u₀) := by
    have h := (hsheetcont.continuousWithinAt hx₀).tendsto.comp hxkw
    rwa [← hu₀] at h
  -- the pair points converge
  set P : ℕ → (Fin (0 + pPair n m) → ℝ) :=
    fun t => pairPtUp (absPtUp (n := n) (m := m) (Fin.append (xk t) (s j (xk t)))) (zk t)
    with hP
  have hpktend : Filter.Tendsto P Filter.atTop (nhds pstar) := by
    have h := witness_pairPtUp_tendsto (x := xk) (z := zk) (w := w) s hcont j hxkmem
      hxktend hx₀ hzwtend
    simpa only [hP, hpstar, hu₀, hW] using h
  -- the pair points lie in the level-pair set
  have hpkmem : ∀ t, P t ∈ (absLevelPairSet S T).set := by
    intro t
    refine mem_absLevelPairSet S T
      (absPtUp (n := n) (m := m) (Fin.append (xk t) (s j (xk t)))) (zk t)
      (hsub j (xk t) (hxkmem t)) (hzT (φ t)) ?_ ?_
    · rw [Work.CoreStep.projFirst_absPtInv_absPtUp_append]
      rw [← Work.WilE7.CoreStep.projTop_init]
      rw [show Work.WilE7.CoreStep.projTop n m (absPt (zk t)) = Fin.snoc (xk t) (ℓ (xk t)) from by
        rw [hzk]; exact hzproj (φ t)]
      simp
    · have hL : (WilkiesDesign.E.projSnd n (m + 1)
            (Work.WilE7.CoreStep.absPtInv (n := n) (m := m)
              (absPtUp (n := n) (m := m) (Fin.append (xk t) (s j (xk t))))) (Fin.last m))
          = (s j (xk t)) (Fin.last m) := by
        simpa only [Fin.last] using
          (Work.CoreStep.projSnd_absPtInv_absPtUp_append (n := n) (m := m) (xk t) (s j (xk t)))
      have hR : (WilkiesDesign.E.projSnd n (m + 1)
            (Work.WilE7.CoreStep.absPtInv (n := n) (m := m) (zk t)) (Fin.last m)) = ℓ (xk t) := by
        rw [← Work.WilE7.CoreStep.projTop_last (n := n) (m := m) (absPt (zk t))]
        rw [show Work.WilE7.CoreStep.projTop n m (absPt (zk t)) = Fin.snoc (xk t) (ℓ (xk t)) from by
          rw [hzk]; exact hzproj (φ t)]
        rw [Fin.snoc_last]
      show (WilkiesDesign.E.projSnd n (m + 1)
          (Work.WilE7.CoreStep.absPtInv (n := n) (m := m)
            (absPtUp (n := n) (m := m) (Fin.append (xk t) (s j (xk t))))) (Fin.last m))
        = (WilkiesDesign.E.projSnd n (m + 1)
            (Work.WilE7.CoreStep.absPtInv (n := n) (m := m) (zk t)) (Fin.last m))
      exact hL.trans hR.symm
  -- every pair point lies in a *top* stratum over C
  have htopV : ∀ t, ∃ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j ∧ P t ∈ V.X.set := by
    intro t
    have hpk : P t ∈ (absLevelPairSet S T).set := hpkmem t
    rw [hVcov] at hpk
    obtain ⟨V, hVmem, hVX⟩ := Set.mem_iUnion₂.mp hpk
    rcases lt_or_eq_of_le (hbound V hVmem (P t) hVX) with hlt | heq
    · exfalso
      have hxV : xk t ∈ Work.CoreStep.pairSubBaseFst n m V := by
        refine ⟨absPt (P t), ⟨P t, hVX, rfl⟩, ?_⟩
        rw [Work.CoreStep.pairBaseFst_absPt_pairPtUp]
        exact Work.CoreStep.projFirst_absPtInv_absPtUp_append (xk t) (s j (xk t))
      exact (Set.disjoint_left.mp (hlow V hVmem hlt)) hxV (hxkmem t)
    · exact ⟨V, hVmem, heq, hVX⟩
  let Lf : List (WilkiesDesign.E.Stratum 0 (pPair n m)) :=
    Vl.filter (fun V => decide (pPair n m - V.j = n + (m + 1) - S.j))
  have hLf_mem : ∀ V, V ∈ Lf ↔ V ∈ Vl ∧ pPair n m - V.j = n + (m + 1) - S.j := by
    intro V
    show V ∈ Vl.filter (fun V => decide (pPair n m - V.j = n + (m + 1) - S.j)) ↔ _
    rw [List.mem_filter]
    exact ⟨fun h => ⟨h.1, of_decide_eq_true h.2⟩,
      fun h => ⟨h.1, by rw [decide_eq_true_eq]; exact h.2⟩⟩
  have hfilt : ∀ t, P t ∈ ⋃ V ∈ Lf, V.X.set := by
    intro t
    obtain ⟨V, hVmem, hVtop, hVX⟩ := htopV t
    exact Set.mem_iUnion₂.mpr ⟨V, (hLf_mem V).mpr ⟨hVmem, hVtop⟩, hVX⟩
  have hstar : pstar ∈ ⋃ V ∈ Lf, closure V.X.set :=
    witness_mem_iUnion_closure (f := P) (a := pstar) (g := fun V => V.X.set) (L := Lf)
      hpktend hfilt
  obtain ⟨V, hVfilt, hVcl⟩ := Set.mem_iUnion₂.mp hstar
  obtain ⟨hVmem, hVtop⟩ := (hLf_mem V).mp hVfilt
  have hVnotin : pstar ∉ V.X.set := by
    intro hVX
    have hpair : pstar ∈ (absLevelPairSet S T).set := hVsub V hVmem hVX
    obtain ⟨-, hSnd, -, -, -⟩ := Work.CoreStep.mem_absLevelPairSet_elim S T hpair
    have hpt : absPt pstar = Fin.append (absPt u₀) (absPt W) := by
      rw [hpstar]; exact Work.CoreStep.Cross_absPt_pairPtUp u₀ W
    have hbase : projSnd (n + (m + 1)) (n + (m + 1)) (absPt pstar) = w := by
      have h1 : projSnd (n + (m + 1)) (n + (m + 1)) (absPt pstar) = absPt W := by
        rw [hpt]
        funext i
        exact Fin.append_right _ _ _
      rw [h1, hWup]
    have hwd : w ∈ absSet T := by rwa [hbase] at hSnd
    have hWT : Work.WilE7.DimAPI.absPtInv (n + (m + 1)) w ∈ T.X.set :=
      (Work.CoreStep.mem_absSet_iff T w).mp hwd
    have hproj : Work.WilE7.CoreStep.projTop n m w = Fin.snoc x₀ (ℓ x₀) :=
      witness_projTop_eq ℓ hℓcont hxkmem hxktend hx₀ hzwtend (fun t => by
        rw [hzk]; exact hzproj (φ t))
    exact hnot ⟨Work.WilE7.DimAPI.absPtInv (n + (m + 1)) w, hWT, by
      rw [Work.WilE7.DimAPI.absPt_absPtInv]; exact hproj⟩
  -- the base of the pair limit is `x₀`
  have hbase_pstar : Work.CoreStep.pairBaseFst n m (absPt pstar) = x₀ := by
    have h1 : Work.CoreStep.pairBaseFst n m (absPt pstar) =
        WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u₀) := by
      rw [hpstar]; exact Work.CoreStep.pairBaseFst_absPt_pairPtUp u₀ W
    rw [h1, hu₀]
    exact Work.CoreStep.projFirst_absPtInv_absPtUp_append x₀ (s j x₀)
  have hx₀front : x₀ ∈ Work.CoreStep.pairFrontierBaseFst n m V := by
    rw [← hbase_pstar]
    exact witness_mem_pairFrontierBaseFst V hVcl hVnotin
  exact (Set.disjoint_left.mp (htop V hVmem hVtop)) hx₀front hx₀


end Work.WilE7.Endgame
