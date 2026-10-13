import Mathlib
import Submission.Work.CoreStep.sigmaFamily_len
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.Endgame.sigmaFamily_len_unif_helpers

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)
open Work.CoreStep

theorem sigmaFamily_len_unif
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
    (n m K Fp : ℕ) :
    ∃ (Q : MvPolynomial (Fin 2) ℕ) (A : ℕ) (B : Polynomial ℕ),
      ∀ (D : ℕ) (Pi : List (WilkiesDesign.E.Stratum 0 (n + (m + 1)))),
        (∀ T ∈ Pi, T.Good) → (∀ T ∈ Pi, T.X.fmt ≤ Fp) → (∀ T ∈ Pi, T.deg ≤ D) →
        (∀ T ∈ Pi, n + (m + 1) - T.j ≤ K) →
        (∀ T ∈ Pi, (Work.WilE7.CoreStep.absPairSet T).fmt ≤ Fp) →
        (∀ T ∈ Pi, ∀ T' ∈ Pi, (Work.WilE7.CoreStep.absLevelPairSet T T').fmt ≤ Fp) →
        ∃ (Sig : List (WilkiesDesign.E.SemiPf (n + Work.WilE7.CoreStep.pPair n m))),
          Sig.length ≤ MvPolynomial.eval ![D, Pi.length] Q ∧
          (∀ S ∈ Sig, S.fmt ≤ A ∧ S.deg ≤ B.eval D ∧
            Work.WilE7.MainDesign.NullDimLT
              (WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set) K) ∧
          (∀ T ∈ Pi, n + (m + 1) - T.j < K →
            WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T) ⊆
              ⋃ S ∈ Sig,
                WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set) ∧
          (∀ T ∈ Pi, Work.CoreStep.frontierSet n m T ⊆
            ⋃ S ∈ Sig,
              WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set) ∧
          (∀ T ∈ Pi,
            ∃ Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
              (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set) ∧
              ((Work.WilE7.CoreStep.absPairSet T).set = ⋃ W ∈ Wl, W.X.set) ∧
              (∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - T.j →
                Work.CoreStep.pairSubBaseFst n m W ⊆
                  ⋃ S ∈ Sig,
                    WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set)) ∧
          (∀ T ∈ Pi, ∀ T' ∈ Pi,
            ∃ Vl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
              (∀ V ∈ Vl, V.Good ∧
                V.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet T T').set) ∧
              ((Work.WilE7.CoreStep.absLevelPairSet T T').set = ⋃ V ∈ Vl, V.X.set) ∧
              (∀ V ∈ Vl, Work.WilE7.CoreStep.pPair n m - V.j < n + (m + 1) - T.j →
                Work.CoreStep.pairSubBaseFst n m V ⊆
                  ⋃ S ∈ Sig,
                    WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set) ∧
              (∀ V ∈ Vl, Work.WilE7.CoreStep.pPair n m - V.j = n + (m + 1) - T.j →
                Work.CoreStep.pairFrontierBaseFst n m V ⊆
                  ⋃ S ∈ Sig,
                    WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set)) := by
  classical
  -- ## The bounds
  obtain ⟨a5, b5, hE5p⟩ := hE5 Fp
  obtain ⟨a6, b6, hE6p⟩ := hE6 Fp
  obtain ⟨a5', b5', hE5f⟩ := hE5 a6
  obtain ⟨a6', b6', hE6q⟩ := hE6 a5
  obtain ⟨a5'', b5'', hE5g⟩ := hE5 a6'
  obtain ⟨B, hB⟩ := sigmaDegBound Fp b5 b5' b5'' b6 b6'
  have hB1 : ∀ D' : ℕ, D' ≤ B.eval D' := fun D' => (hB D').1
  have hB2 : ∀ D' : ℕ, b5'.eval (b6.eval D') ≤ B.eval D' := fun D' => (hB D').2.2.1
  have hB3 : ∀ D' : ℕ, b5.eval (2 * (1 + Fp) * (1 + 2 * D') ^ 2) ≤ B.eval D' :=
    fun D' => (hB D').2.2.2.1
  have hB4 : ∀ D' : ℕ, b5.eval (2 * (Fp + 2) * (1 + 2 * D') ^ 2) ≤ B.eval D' :=
    fun D' => (hB D').2.2.2.2.1
  have hB5 : ∀ D' : ℕ, b5''.eval (b6'.eval (b5.eval (2 * (Fp + 2) * (1 + 2 * D') ^ 2))) ≤
      B.eval D' := fun D' => (hB D').2.2.2.2.2
  -- ## The length polynomial `Q`
  let p3 : Polynomial ℕ := Polynomial.C (2 * (1 + Fp)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2
  let p4 : Polynomial ℕ := Polynomial.C (2 * (Fp + 2)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2
  let Q : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.X 1 * (1 + Polynomial.aeval (MvPolynomial.X 0) (b5'.comp b6) +
        Polynomial.aeval (MvPolynomial.X 0) (b5.comp p3)) +
      MvPolynomial.X 1 ^ 2 * Polynomial.aeval (MvPolynomial.X 0) (b5.comp p4) *
        (1 + Polynomial.aeval (MvPolynomial.X 0) (b5''.comp (b6'.comp (b5.comp p4))))
  let Amax : ℕ := Fp + a5 + a5' + a5'' + a6'
  let A : ℕ := (n + pPair n m) + Amax
  have hA5 : a5 ≤ Amax := by dsimp only [Amax]; omega
  have hA5' : a5' ≤ Amax := by dsimp only [Amax]; omega
  have hA5'' : a5'' ≤ Amax := by dsimp only [Amax]; omega
  have hAFp : Fp ≤ Amax := by dsimp only [Amax]; omega
  have hA6' : a6' ≤ Amax := by dsimp only [Amax]; omega
  refine ⟨Q, A, B, fun D Pi hPigood hPifmt hPideg hPiK hPpair hPlev => ?_⟩
  -- ## The numerical length bounds (as functions of `D`)
  let B2 : ℕ := b5'.eval (b6.eval D)
  let B3 : ℕ := b5.eval (2 * (1 + Fp) * (1 + 2 * D) ^ 2)
  let B4 : ℕ := b5.eval (2 * (Fp + 2) * (1 + 2 * D) ^ 2)
  let B5 : ℕ := b5''.eval (b6'.eval (b5.eval (2 * (Fp + 2) * (1 + 2 * D) ^ 2)))
  -- ## The per-piece data
  -- (a) the frontier of an absolute stratum of `Pi`
  have hFrontSpec : ∀ T : WilkiesDesign.E.Stratum 0 (n + (m + 1)), T.X.fmt ≤ Fp →
      ∃ Y' : WilkiesDesign.E.SemiPf (0 + (n + (m + 1))), Y'.fmt ≤ a6 ∧
        Y'.deg ≤ b6.eval T.X.deg ∧ Y'.set = closure T.X.set \ T.X.set := by
    intro T hfmt
    obtain ⟨Y, Y', -, -, h3, h4, -, h6⟩ := hE6p 0 (n + (m + 1)) T.X hfmt
    exact ⟨Y', h3, h4, by rw [h6, fiberClosure_zero]⟩
  let Yf : (T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi}) →
      WilkiesDesign.E.SemiPf (0 + (n + (m + 1))) :=
    fun T => (hFrontSpec T.1 (hPifmt T.1 T.2)).choose
  have hYf : ∀ T, (Yf T).fmt ≤ a6 ∧ (Yf T).deg ≤ b6.eval T.1.X.deg ∧
      (Yf T).set = closure T.1.X.set \ T.1.X.set :=
    fun T => (hFrontSpec T.1 (hPifmt T.1 T.2)).choose_spec
  have hFS : ∀ T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi},
      ∃ TL : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))),
        (∀ V ∈ TL, V.Good ∧ V.X.set ⊆ (Yf T).set ∧ V.X.fmt ≤ a5' ∧
          V.deg ≤ b5'.eval (Yf T).deg) ∧
        ((Yf T).set = ⋃ V ∈ TL, V.X.set) ∧
        TL.length ≤ b5'.eval (Yf T).deg := by
    intro T
    obtain ⟨TL, hTLlen, hgood, hcov, -⟩ := hE5f 0 (n + (m + 1)) (Yf T) (hYf T).1
    exact ⟨TL, fun V hV =>
      ⟨(hgood V hV).2.2, (by rw [hcov]; intro z hz; exact Set.mem_iUnion₂.mpr ⟨V, hV, hz⟩),
        (hgood V hV).1, (hgood V hV).2.1⟩, hcov, hTLlen⟩
  let FL : (T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi}) →
      List (WilkiesDesign.E.Stratum 0 (n + (m + 1))) := fun T => (hFS T).choose
  have hFL : ∀ T, (∀ V ∈ FL T, V.Good ∧ V.X.set ⊆ (Yf T).set ∧ V.X.fmt ≤ a5' ∧
        V.deg ≤ b5'.eval (Yf T).deg) ∧ ((Yf T).set = ⋃ V ∈ FL T, V.X.set) ∧
        (FL T).length ≤ b5'.eval (Yf T).deg :=
    fun T => (hFS T).choose_spec
  -- (b) the pair-set decomposition of a piece of `Pi`
  have hPairSpec : ∀ T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi},
      ∃ Wl : List (WilkiesDesign.E.Stratum 0 (pPair n m)),
        (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet T.1).set ∧ W.X.fmt ≤ a5 ∧
          W.deg ≤ b5.eval (absPairSet T.1).deg) ∧
        ((absPairSet T.1).set = ⋃ W ∈ Wl, W.X.set) ∧
        Wl.length ≤ b5.eval (absPairSet T.1).deg := by
    intro T
    obtain ⟨Wl, hWllen, hgood, hcov, -⟩ := hE5p 0 (pPair n m) (absPairSet T.1) (hPpair T.1 T.2)
    exact ⟨Wl, fun W hW =>
      ⟨(hgood W hW).2.2, (by rw [hcov]; intro z hz; exact Set.mem_iUnion₂.mpr ⟨W, hW, hz⟩),
        (hgood W hW).1, (hgood W hW).2.1⟩, hcov, hWllen⟩
  let WL : (T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi}) →
      List (WilkiesDesign.E.Stratum 0 (pPair n m)) := fun T => (hPairSpec T).choose
  have hWL : ∀ T, (∀ W ∈ WL T, W.Good ∧ W.X.set ⊆ (absPairSet T.1).set ∧ W.X.fmt ≤ a5 ∧
        W.deg ≤ b5.eval (absPairSet T.1).deg) ∧
      ((absPairSet T.1).set = ⋃ W ∈ WL T, W.X.set) ∧
      (WL T).length ≤ b5.eval (absPairSet T.1).deg := fun T => (hPairSpec T).choose_spec
  -- (c) the level-pair decomposition of a pair of pieces of `Pi`
  have hLevSpec : ∀ p : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi} ×
      {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi},
      ∃ Vl : List (WilkiesDesign.E.Stratum 0 (pPair n m)),
        (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet p.1.1 p.2.1).set ∧ V.X.fmt ≤ a5 ∧
          V.deg ≤ b5.eval (absLevelPairSet p.1.1 p.2.1).deg) ∧
        ((absLevelPairSet p.1.1 p.2.1).set = ⋃ V ∈ Vl, V.X.set) ∧
        Vl.length ≤ b5.eval (absLevelPairSet p.1.1 p.2.1).deg := by
    intro p
    obtain ⟨Vl, hVllen, hgood, hcov, -⟩ :=
      hE5p 0 (pPair n m) (absLevelPairSet p.1.1 p.2.1) (hPlev p.1.1 p.1.2 p.2.1 p.2.2)
    exact ⟨Vl, fun V hV =>
      ⟨(hgood V hV).2.2, (by rw [hcov]; intro z hz; exact Set.mem_iUnion₂.mpr ⟨V, hV, hz⟩),
        (hgood V hV).1, (hgood V hV).2.1⟩, hcov, hVllen⟩
  let VL : (T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi}) →
      {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi} →
      List (WilkiesDesign.E.Stratum 0 (pPair n m)) :=
    fun T T' => (hLevSpec (T, T')).choose
  have hVL : ∀ T T', (∀ V ∈ VL T T', V.Good ∧ V.X.set ⊆ (absLevelPairSet T.1 T'.1).set ∧
        V.X.fmt ≤ a5 ∧ V.deg ≤ b5.eval (absLevelPairSet T.1 T'.1).deg) ∧
      ((absLevelPairSet T.1 T'.1).set = ⋃ V ∈ VL T T', V.X.set) ∧
      (VL T T').length ≤ b5.eval (absLevelPairSet T.1 T'.1).deg :=
    fun T T' => (hLevSpec (T, T')).choose_spec
  -- (d) the frontier decomposition of a pair stratum (`hE6` at `a5`, `hE5` at `a6'`)
  have hPFS : ∀ V : WilkiesDesign.E.Stratum 0 (pPair n m), V.X.fmt ≤ a5 →
      ∃ UL : List (WilkiesDesign.E.Stratum 0 (pPair n m)),
        (∀ U ∈ UL, U.Good ∧ U.X.set ⊆ closure V.X.set \ V.X.set ∧ U.X.fmt ≤ a5'' ∧
          U.deg ≤ b5''.eval (b6'.eval V.deg)) ∧
        (closure V.X.set \ V.X.set = ⋃ U ∈ UL, U.X.set) ∧
        UL.length ≤ b5''.eval (b6'.eval V.deg) := by
    intro V hfmt
    obtain ⟨Y, Y', -, -, h3, h4, -, h6⟩ := hE6q 0 (pPair n m) V.X hfmt
    have hset : Y'.set = closure V.X.set \ V.X.set := by rw [h6, fiberClosure_zero]
    obtain ⟨UL, hULlen, hgood, hcov, -⟩ := hE5g 0 (pPair n m) Y' h3
    refine ⟨UL, fun U hU => ?_, ?_, ?_⟩
    · refine ⟨(hgood U hU).2.2, ?_, (hgood U hU).1, ?_⟩
      · have h1 : U.X.set ⊆ (⋃ S ∈ UL, S.X.set) :=
          fun z hz => Set.mem_iUnion₂.mpr ⟨U, hU, hz⟩
        rw [← hcov, hset] at h1
        exact h1
      · refine le_trans (hgood U hU).2.1 ?_
        refine pol_eval_mono_nat ?_
        refine le_trans h4 ?_
        exact pol_eval_mono_nat (Nat.le_add_right _ _)
    · rw [← hset]
      exact hcov
    · refine le_trans hULlen ?_
      refine pol_eval_mono_nat ?_
      refine le_trans h4 ?_
      exact pol_eval_mono_nat (Nat.le_add_right _ _)
  let PF : (V : WilkiesDesign.E.Stratum 0 (pPair n m)) →
      List (WilkiesDesign.E.Stratum 0 (pPair n m)) :=
    fun V => if h : V.X.fmt ≤ a5 then (hPFS V h).choose else []
  have hPF : ∀ (V : WilkiesDesign.E.Stratum 0 (pPair n m)) (h : V.X.fmt ≤ a5),
      (∀ U ∈ PF V, U.Good ∧ U.X.set ⊆ closure V.X.set \ V.X.set ∧ U.X.fmt ≤ a5'' ∧
        U.deg ≤ b5''.eval (b6'.eval V.deg)) ∧
      (closure V.X.set \ V.X.set = ⋃ U ∈ PF V, U.X.set) ∧
      (PF V).length ≤ b5''.eval (b6'.eval V.deg) := by
    intro V h
    have hspec := (hPFS V h).choose_spec
    dsimp only [PF]
    rw [dif_pos h]
    exact hspec
  -- ## The length bounds of the per-piece data, as functions of `D`
  have hFLlen : ∀ T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi},
      (FL T).length ≤ B2 := by
    intro T
    refine le_trans (hFL T).2.2 ?_
    refine le_trans (pol_eval_mono_nat (hYf T).2.1) ?_
    exact pol_eval_mono_nat (pol_eval_mono_nat (le_trans (Nat.le_add_right _ _) (hPideg T.1 T.2)))
  -- ## The Σ-list
  let PT : List {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi} := Pi.attach
  let PTP : List ({T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi} ×
      {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi}) := PT.product PT
  let L1 : List (WilkiesDesign.E.SemiPf (n + pPair n m)) :=
    (Pi.filter (fun T => decide (n + (m + 1) - T.j < K))).map (sigAbs n m)
  let L2 : List (WilkiesDesign.E.SemiPf (n + pPair n m)) := (PT.flatMap FL).map (sigAbs n m)
  let L3 : List (WilkiesDesign.E.SemiPf (n + pPair n m)) :=
    (PT.flatMap (fun T =>
      (WL T).filter (fun W => decide (pPair n m - W.j < n + (m + 1) - T.1.j)))).map
      (sigPair n m)
  let L4 : List (WilkiesDesign.E.SemiPf (n + pPair n m)) :=
    (PTP.flatMap (fun p =>
      (VL p.1 p.2).filter (fun V => decide (pPair n m - V.j < n + (m + 1) - p.1.1.j)))).map
      (sigPair n m)
  let L5 : List (WilkiesDesign.E.SemiPf (n + pPair n m)) :=
    (PTP.flatMap (fun p =>
      ((VL p.1 p.2).filter (fun V => decide (pPair n m - V.j = n + (m + 1) - p.1.1.j))).flatMap
        PF)).map (sigPair n m)
  let Sig : List (WilkiesDesign.E.SemiPf (n + pPair n m)) := L1 ++ L2 ++ L3 ++ L4 ++ L5
  -- ## Memberships
  have memL1 : ∀ T ∈ Pi, n + (m + 1) - T.j < K → sigAbs n m T ∈ L1 := by
    intro T hT hK
    refine List.mem_map.mpr ⟨T, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨hT, decide_eq_true_eq.mpr hK⟩
  have memL2 : ∀ (T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi})
      (V : WilkiesDesign.E.Stratum 0 (n + (m + 1))), V ∈ FL T → sigAbs n m V ∈ L2 := by
    intro T V hV
    exact List.mem_map.mpr ⟨V, List.mem_flatMap.mpr ⟨T, List.mem_attach _ _, hV⟩, rfl⟩
  have memL3 : ∀ (T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi})
      (W : WilkiesDesign.E.Stratum 0 (pPair n m)), W ∈ WL T →
      pPair n m - W.j < n + (m + 1) - T.1.j → sigPair n m W ∈ L3 := by
    intro T W hW hdim
    refine List.mem_map.mpr ⟨W, List.mem_flatMap.mpr ⟨T, List.mem_attach _ _, ?_⟩, rfl⟩
    exact List.mem_filter.mpr ⟨hW, decide_eq_true_eq.mpr hdim⟩
  have memL4 : ∀ (p : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi} ×
        {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi})
      (V : WilkiesDesign.E.Stratum 0 (pPair n m)), V ∈ VL p.1 p.2 →
      pPair n m - V.j < n + (m + 1) - p.1.1.j → sigPair n m V ∈ L4 := by
    intro p V hV hdim
    refine List.mem_map.mpr ⟨V, List.mem_flatMap.mpr ⟨p, ?_, ?_⟩, rfl⟩
    · exact List.mem_product.mpr ⟨List.mem_attach _ _, List.mem_attach _ _⟩
    · exact List.mem_filter.mpr ⟨hV, decide_eq_true_eq.mpr hdim⟩
  have memL5 : ∀ (p : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi} ×
        {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi})
      (V : WilkiesDesign.E.Stratum 0 (pPair n m)), V ∈ VL p.1 p.2 →
      pPair n m - V.j = n + (m + 1) - p.1.1.j →
      (U : WilkiesDesign.E.Stratum 0 (pPair n m)) → U ∈ PF V → sigPair n m U ∈ L5 := by
    intro p V hV hdim U hU
    refine List.mem_map.mpr ⟨U, List.mem_flatMap.mpr ⟨p, ?_, ?_⟩, rfl⟩
    · exact List.mem_product.mpr ⟨List.mem_attach _ _, List.mem_attach _ _⟩
    · refine List.mem_flatMap.mpr ⟨V, ?_, hU⟩
      exact List.mem_filter.mpr ⟨hV, decide_eq_true_eq.mpr hdim⟩
  have memSig1 : ∀ S, S ∈ L1 → S ∈ Sig := by
    intro S h; simp only [Sig, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  have memSig2 : ∀ S, S ∈ L2 → S ∈ Sig := by
    intro S h; simp only [Sig, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  have memSig3 : ∀ S, S ∈ L3 → S ∈ Sig := by
    intro S h; simp only [Sig, List.mem_append]
    exact Or.inl (Or.inl (Or.inr h))
  have memSig4 : ∀ S, S ∈ L4 → S ∈ Sig := by
    intro S h; simp only [Sig, List.mem_append]
    exact Or.inl (Or.inr h)
  have memSig5 : ∀ S, S ∈ L5 → S ∈ Sig := by
    intro S h; simp only [Sig, List.mem_append]
    exact Or.inr h
  -- ## The format bounds
  have fmt_of : ∀ {amb : ℕ} (X : WilkiesDesign.E.SemiPf amb) {c : ℕ}, X.fmt ≤ c → c ≤ Amax →
      X.r ≤ Amax := by
    intro amb X c h1 h2
    simp only [WilkiesDesign.E.SemiPf.fmt] at h1
    omega
  -- ## The degree bounds of the pair sets
  have hPairDeg : ∀ T ∈ Pi, (absPairSet T).deg ≤ 2 * (1 + Fp) * (1 + 2 * D) ^ 2 := by
    intro T hT
    have hfmt : (n + (m + 1)) + T.X.r ≤ Fp := by
      have h := hPifmt T hT
      simp only [WilkiesDesign.E.SemiPf.fmt] at h
      omega
    refine le_trans (absPairSet_deg_le T hfmt) ?_
    have h3 : T.X.deg ≤ D := le_trans (Nat.le_add_right _ _) (hPideg T hT)
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2)
    omega
  have hLevDeg : ∀ T ∈ Pi, ∀ T' ∈ Pi,
      (absLevelPairSet T T').deg ≤ 2 * (Fp + 2) * (1 + 2 * D) ^ 2 := by
    intro T hT T' hT'
    have hfmt : (n + (m + 1)) + T.X.r ≤ Fp := by
      have h := hPifmt T hT
      simp only [WilkiesDesign.E.SemiPf.fmt] at h
      omega
    refine le_trans (absLevelPairSet_deg_le T T' hfmt) ?_
    have h3 : T.X.deg ≤ D := le_trans (Nat.le_add_right _ _) (hPideg T hT)
    have h4 : T'.X.deg ≤ D := le_trans (Nat.le_add_right _ _) (hPideg T' hT')
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ 2)
    omega
  -- ## The length bounds of the pieces, in terms of `B2`, …, `B5`
  have hWLlen : ∀ T : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi},
      (WL T).length ≤ B3 := by
    intro T
    refine le_trans (hWL T).2.2 ?_
    exact pol_eval_mono_nat (hPairDeg T.1 T.2)
  have hVLlen : ∀ T T' : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi},
      (VL T T').length ≤ B4 := by
    intro T T'
    refine le_trans (hVL T T').2.2 ?_
    exact pol_eval_mono_nat (hLevDeg T.1 T.2 T'.1 T'.2)
  have hPFlen : ∀ (T T' : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi})
      (V : WilkiesDesign.E.Stratum 0 (pPair n m)), V ∈ VL T T' → (PF V).length ≤ B5 := by
    intro T T' V hV
    have hfmtV : V.X.fmt ≤ a5 := ((hVL T T').1 V hV).2.2.1
    have hdegV : V.deg ≤ b5.eval (2 * (Fp + 2) * (1 + 2 * D) ^ 2) :=
      le_trans ((hVL T T').1 V hV).2.2.2 (pol_eval_mono_nat (hLevDeg T.1 T.2 T'.1 T'.2))
    exact le_trans (hPF V hfmtV).2.2 (pol_eval_mono_nat (pol_eval_mono_nat hdegV))
  have hPTlen : PT.length = Pi.length := by simp only [PT, List.length_attach]
  have hPTPlen : PTP.length = Pi.length * Pi.length := by
    rw [show PTP = PT ×ˢ PT from rfl, List.length_product, hPTlen]
  -- ## The length of `Sig`
  have hL1len : L1.length ≤ Pi.length := by
    dsimp only [L1]
    rw [List.length_map]
    exact List.length_filter_le _ _
  have hL2len : L2.length ≤ Pi.length * B2 := by
    dsimp only [L2]
    rw [List.length_map]
    refine le_trans (length_flatMap_le PT FL B2 (fun T _ => hFLlen T)) ?_
    simp only [hPTlen, le_refl]
  have hL3len : L3.length ≤ Pi.length * B3 := by
    dsimp only [L3]
    rw [List.length_map]
    refine le_trans (length_flatMap_le PT _ B3 ?_) ?_
    · intro T _
      exact le_trans (List.length_filter_le _ _) (hWLlen T)
    · simp only [hPTlen, le_refl]
  have hL4len : L4.length ≤ Pi.length * Pi.length * B4 := by
    dsimp only [L4]
    rw [List.length_map]
    refine le_trans (length_flatMap_le PTP _ B4 ?_) ?_
    · intro p _
      exact le_trans (List.length_filter_le _ _) (hVLlen p.1 p.2)
    · rw [hPTPlen]
  have hInnerLen : ∀ p : {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi} ×
      {T : WilkiesDesign.E.Stratum 0 (n + (m + 1)) // T ∈ Pi},
      (((VL p.1 p.2).filter (fun V => decide (pPair n m - V.j = n + (m + 1) - p.1.1.j))).flatMap
        PF).length ≤ B4 * B5 := by
    intro p
    refine le_trans (length_flatMap_le _ PF B5 ?_) ?_
    · intro V hV
      exact hPFlen p.1 p.2 V (List.mem_filter.mp hV).1
    · refine Nat.mul_le_mul_right B5 ?_
      exact le_trans (List.length_filter_le _ _) (hVLlen p.1 p.2)
  have hL5len : L5.length ≤ Pi.length * Pi.length * (B4 * B5) := by
    dsimp only [L5]
    rw [List.length_map]
    refine le_trans (length_flatMap_le PTP _ (B4 * B5) (fun p _ => hInnerLen p)) ?_
    rw [hPTPlen]
  -- ## The evaluation of `Q`
  have hQeval : MvPolynomial.eval ![D, Pi.length] Q =
      Pi.length * (1 + B2 + B3) + Pi.length ^ 2 * B4 * (1 + B5) := by
    simp only [Q, p3, p4, B2, B3, B4, B5, MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one,
      MvPolynomial.eval_pow, MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      mv_eval_aeval_X0, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  refine ⟨Sig, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (0) the length of `Sig`
    have hSigLen : Sig.length ≤ Pi.length + Pi.length * B2 + Pi.length * B3 +
        Pi.length * Pi.length * B4 + Pi.length * Pi.length * (B4 * B5) := by
      simp only [Sig, List.length_append]
      omega
    rw [hQeval]
    have key : Pi.length * (1 + B2 + B3) + Pi.length ^ 2 * B4 * (1 + B5) =
        Pi.length + Pi.length * B2 + Pi.length * B3 + Pi.length * Pi.length * B4 +
          Pi.length * Pi.length * (B4 * B5) := by ring
    rw [key]
    exact hSigLen
  · -- (1) the members of `Sig`
    intro S hS
    rcases List.mem_append.mp hS with hS | hS
    · rcases List.mem_append.mp hS with hS | hS
      · rcases List.mem_append.mp hS with hS | hS
        · rcases List.mem_append.mp hS with hS | hS
          · -- `L1`
            obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hS
            obtain ⟨hTpi, hTdec⟩ := List.mem_filter.mp hT
            have hTK : n + (m + 1) - T.j < K := decide_eq_true_eq.mp hTdec
            refine ⟨?_, ?_, sigAbs_nullDimLT T (hPigood T hTpi) (fun _ => hTK)⟩
            · rw [sigAbs_fmt]
              exact Nat.add_le_add_left (fmt_of T.X (hPifmt T hTpi) hAFp) _
            · refine le_trans (sigAbs_deg n m T) ?_
              exact le_trans (le_trans (Nat.le_add_right _ _) (hPideg T hTpi)) (hB1 D)
          · -- `L2`
            obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hS
            obtain ⟨T, hT, hVT⟩ := List.mem_flatMap.mp hV
            obtain ⟨hFLgood, hFLsub, hFLfmt, hFLdeg⟩ := (hFL T).1 V hVT
            refine ⟨?_, ?_, sigAbs_nullDimLT V hFLgood (fun hne => ?_)⟩
            · rw [sigAbs_fmt]
              exact Nat.add_le_add_left (fmt_of V.X hFLfmt hA5') _
            · refine le_trans (sigAbs_deg n m V) ?_
              refine le_trans (le_trans (Nat.le_add_right _ _) hFLdeg) ?_
              refine le_trans (pol_eval_mono_nat ((hYf T).2.1)) ?_
              refine le_trans (pol_eval_mono_nat (pol_eval_mono_nat ?_)) (hB2 D)
              exact le_trans (Nat.le_add_right _ _) (hPideg T.1 T.2)
            · have hdrop := frontierDrop_abs T.1 V (hPigood T.1 T.2) hFLgood
                (fun z hz => by
                  have h1 := hFLsub hz
                  rwa [(hYf T).2.2] at h1) hne
              have hK := hPiK T.1 T.2
              have hjl : V.j ≤ n + (m + 1) := Stratum.j_le_card_of_good V hFLgood hne
              omega
        · -- `L3`
          obtain ⟨W, hW, rfl⟩ := List.mem_map.mp hS
          obtain ⟨T, hT, hWT⟩ := List.mem_flatMap.mp hW
          obtain ⟨hWl, hWdec⟩ := List.mem_filter.mp hWT
          have hdim : pPair n m - W.j < n + (m + 1) - T.1.j := decide_eq_true_eq.mp hWdec
          obtain ⟨hWLgood, -, hWLfmt, hWLdeg⟩ := (hWL T).1 W hWl
          refine ⟨?_, ?_, sigPair_nullDimLT W hWLgood
            (fun _ => lt_of_lt_of_le hdim (hPiK T.1 T.2))⟩
          · rw [sigPair_fmt]
            exact Nat.add_le_add_left (fmt_of W.X hWLfmt hA5) _
          · refine le_trans (sigPair_deg n m W) ?_
            refine le_trans (le_trans (Nat.le_add_right _ _) hWLdeg) ?_
            exact le_trans (pol_eval_mono_nat (hPairDeg T.1 T.2)) (hB3 D)
      · -- `L4`
        obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hS
        obtain ⟨p, hp, hVp⟩ := List.mem_flatMap.mp hV
        obtain ⟨hVl, hVdec⟩ := List.mem_filter.mp hVp
        have hdim : pPair n m - V.j < n + (m + 1) - p.1.1.j := decide_eq_true_eq.mp hVdec
        obtain ⟨hVLgood, -, hVLfmt, hVLdeg⟩ := (hVL p.1 p.2).1 V hVl
        refine ⟨?_, ?_, sigPair_nullDimLT V hVLgood
          (fun _ => lt_of_lt_of_le hdim (hPiK p.1.1 p.1.2))⟩
        · rw [sigPair_fmt]
          exact Nat.add_le_add_left (fmt_of V.X hVLfmt hA5) _
        · refine le_trans (sigPair_deg n m V) ?_
          refine le_trans (le_trans (Nat.le_add_right _ _) hVLdeg) ?_
          exact le_trans (pol_eval_mono_nat (hLevDeg p.1.1 p.1.2 p.2.1 p.2.2)) (hB4 D)
    · -- `L5`
      obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hS
      obtain ⟨p, hp, hUp⟩ := List.mem_flatMap.mp hU
      obtain ⟨V, hVp, hUV⟩ := List.mem_flatMap.mp hUp
      obtain ⟨hVl, hVdec⟩ := List.mem_filter.mp hVp
      have hdim : pPair n m - V.j = n + (m + 1) - p.1.1.j := decide_eq_true_eq.mp hVdec
      obtain ⟨hVLgood, -, hVLfmt, hVLdeg⟩ := (hVL p.1 p.2).1 V hVl
      obtain ⟨hPFgood, hPFcov, -⟩ := hPF V hVLfmt
      obtain ⟨hPFn, hPFsub, hPFfmt, hPFdeg⟩ := hPFgood U hUV
      refine ⟨?_, ?_, sigPair_nullDimLT U hPFn (fun hne => ?_)⟩
      · rw [sigPair_fmt]
        exact Nat.add_le_add_left (fmt_of U.X hPFfmt hA5'') _
      · refine le_trans (sigPair_deg n m U) ?_
        refine le_trans (le_trans (Nat.le_add_right _ _) hPFdeg) ?_
        refine le_trans (pol_eval_mono_nat (pol_eval_mono_nat hVLdeg)) ?_
        refine le_trans (pol_eval_mono_nat (pol_eval_mono_nat (pol_eval_mono_nat
          (hLevDeg p.1.1 p.1.2 p.2.1 p.2.2)))) (hB5 D)
      · have hdrop := frontierDrop_abs V U hVLgood hPFn hPFsub hne
        have hK := hPiK p.1.1 p.1.2
        have hjl : U.j ≤ pPair n m := Stratum.j_le_card_of_good U hPFn hne
        omega
  · -- (2) the low-dimensional pieces
    intro T hT hTK z hz
    rw [← sigAbs_proj n m T] at hz
    exact Set.mem_iUnion₂.mpr ⟨sigAbs n m T, memSig1 _ (memL1 T hT hTK), hz⟩
  · -- (3) the frontiers
    intro T hT
    have hcover : closure T.X.set \ T.X.set = ⋃ V ∈ FL ⟨T, hT⟩, V.X.set := by
      rw [← (hYf ⟨T, hT⟩).2.2]
      exact (hFL ⟨T, hT⟩).2.1
    rw [sigmaFrontierCover T (FL ⟨T, hT⟩) hcover]
    intro z hz
    obtain ⟨V, hV, hzV⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion₂.mpr ⟨sigAbs n m V, memSig2 _ (memL2 ⟨T, hT⟩ V hV), hzV⟩
  · -- (4) the pair-set decompositions
    intro T hT
    refine ⟨WL ⟨T, hT⟩, ?_, ?_, ?_⟩
    · intro W hW
      exact ⟨((hWL ⟨T, hT⟩).1 W hW).1, ((hWL ⟨T, hT⟩).1 W hW).2.1⟩
    · exact (hWL ⟨T, hT⟩).2.1
    · intro W hW hdim z hz
      rw [← sigPair_proj n m W] at hz
      exact Set.mem_iUnion₂.mpr ⟨sigPair n m W, memSig3 _ (memL3 ⟨T, hT⟩ W hW hdim), hz⟩
  · -- (5) the level-pair decompositions
    intro T hT T' hT'
    refine ⟨VL ⟨T, hT⟩ ⟨T', hT'⟩, ?_, ?_, ?_, ?_⟩
    · intro V hV
      exact ⟨((hVL ⟨T, hT⟩ ⟨T', hT'⟩).1 V hV).1, ((hVL ⟨T, hT⟩ ⟨T', hT'⟩).1 V hV).2.1⟩
    · exact (hVL ⟨T, hT⟩ ⟨T', hT'⟩).2.1
    · intro V hV hdim z hz
      rw [← sigPair_proj n m V] at hz
      exact Set.mem_iUnion₂.mpr
        ⟨sigPair n m V, memSig4 _ (memL4 (⟨T, hT⟩, ⟨T', hT'⟩) V hV hdim), hz⟩
    · intro V hV hdim
      have hcov := (hPF V ((hVL ⟨T, hT⟩ ⟨T', hT'⟩).1 V hV).2.2.1).2.1
      rw [sigmaPairFrontierCover V (PF V) hcov]
      intro z hz
      obtain ⟨U, hU, hzU⟩ := Set.mem_iUnion₂.mp hz
      exact Set.mem_iUnion₂.mpr
        ⟨sigPair n m U, memSig5 _ (memL5 (⟨T, hT⟩, ⟨T', hT'⟩) V hV hdim U hU), hzU⟩


end Work.WilE7.Endgame
