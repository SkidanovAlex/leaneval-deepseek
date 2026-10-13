import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.CoreStep.SigmaFamDefs
import Submission.Work.CoreStep.sigmaFamilyAux
import Submission.Work.CoreStep.sigmaFamily_len

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair absPairSet absLevelPairSet)
open Work.CoreStep (pairBase sigPair pairSubBaseFst pairFrontierBaseFst)
open Work.WilE7.CoreLTSuccPlan (pairBaseRank pairBaseLin absPairSet2 HypE5 HypE6)

/-- The `Σ`-family cooking of a *single* level-agreeing pair set `absLevelPairSet S T`:
`hE5` stratifies the level-pair set, the low strata (`dim < dim S`) enter `Σ` directly, and the
frontier of every top stratum (`dim = dim S`) is decomposed by `hE6` + `hE5` and its pieces enter
`Σ`.  This is the `(T,T')`-clause of `Work.CoreStep.sigmaFamily_len` extracted for the pair
`(S,T)`, with the length/format/degree bounds collapsed into a single pair `(A,B)`. -/
theorem levelPairFamily (hE5 : HypE5) (hE6 : HypE6) (n m K Fp : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (D : ℕ) (S T : Stratum 0 (n + (m + 1))),
        S.Good → S.X.fmt ≤ Fp → S.deg ≤ D → n + (m + 1) - S.j ≤ K →
        T.Good → T.X.fmt ≤ Fp → T.deg ≤ D →
        (absLevelPairSet S T).fmt ≤ Fp →
        ∃ Sig : List (SemiPf (n + pPair n m)),
          Sig.length ≤ B.eval D ∧
          (∀ Z ∈ Sig, Z.fmt ≤ A ∧ Z.deg ≤ B.eval D ∧
            NullDimLT (projFirst n (pPair n m) '' Z.set) K) ∧
          ∃ Vl : List (Stratum 0 (pPair n m)),
            (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet S T).set) ∧
            (absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set ∧
            (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
              pairSubBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
            (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j →
              pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) := by
  classical
  -- The format parameters of the two applications of `E5` and one of `E6` that we need.
  obtain ⟨a5, b5, hE5p⟩ := hE5 Fp
  obtain ⟨a6', b6', hE6q⟩ := hE6 a5
  obtain ⟨a5'', b5'', hE5g⟩ := hE5 a6'
  -- The answer: `A` is the format bound, `B` the degree/length bound.
  let Amax : ℕ := Fp + a5 + a5''
  let A0 : ℕ := (n + pPair n m) + Amax
  let P4 : Polynomial ℕ :=
    Polynomial.C (2 * (Fp + 2)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2
  let B0 : Polynomial ℕ :=
    Polynomial.X + (b5.comp P4) + (b5''.comp (b6'.comp (b5.comp P4))) +
      (b5.comp P4) * (b5''.comp (b6'.comp (b5.comp P4)))
  have hAmax5 : a5 ≤ Amax := by dsimp only [Amax]; omega
  have hAmax5'' : a5'' ≤ Amax := by dsimp only [Amax]; omega
  have fmt_of : ∀ {amb : ℕ} (X : SemiPf amb) {c : ℕ}, X.fmt ≤ c → c ≤ Amax → X.r ≤ Amax := by
    intro amb X c h1 h2
    simp only [SemiPf.fmt] at h1
    omega
  -- ## The frontier decomposition of a pair stratum: `E6` at `a5`, then `E5` at `a6'`
  have hPFS : ∀ V : Stratum 0 (pPair n m), V.X.fmt ≤ a5 →
      ∃ UL : List (Stratum 0 (pPair n m)),
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
        refine Work.CoreStep.pol_eval_mono_nat ?_
        refine le_trans h4 ?_
        exact Work.CoreStep.pol_eval_mono_nat (Nat.le_add_right _ _)
    · rw [← hset]
      exact hcov
    · refine le_trans hULlen ?_
      refine Work.CoreStep.pol_eval_mono_nat ?_
      refine le_trans h4 ?_
      exact Work.CoreStep.pol_eval_mono_nat (Nat.le_add_right _ _)
  let PFl : (V : Stratum 0 (pPair n m)) → List (Stratum 0 (pPair n m)) :=
    fun V => if h : V.X.fmt ≤ a5 then (hPFS V h).choose else []
  have hPFl : ∀ (V : Stratum 0 (pPair n m)) (h : V.X.fmt ≤ a5),
      (∀ U ∈ PFl V, U.Good ∧ U.X.set ⊆ closure V.X.set \ V.X.set ∧ U.X.fmt ≤ a5'' ∧
        U.deg ≤ b5''.eval (b6'.eval V.deg)) ∧
      (closure V.X.set \ V.X.set = ⋃ U ∈ PFl V, U.X.set) ∧
      (PFl V).length ≤ b5''.eval (b6'.eval V.deg) := by
    intro V h
    have hspec := (hPFS V h).choose_spec
    dsimp only [PFl]
    rw [dif_pos h]
    exact hspec
  refine ⟨A0, B0, ?_⟩
  intro D S T hSg hSfmt hSdeg hSK hTg hTfmt hTdeg hpair
  -- ## The degree bound for the level-pair set
  have hLF : (n + (m + 1)) + S.X.r ≤ Fp := by
    have h := hSfmt
    simp only [SemiPf.fmt] at h
    omega
  have hP4eval : P4.eval D = 2 * (Fp + 2) * (1 + 2 * D) ^ 2 := by
    simp only [P4, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_X]
  have hLdeg : (absLevelPairSet S T).deg ≤ P4.eval D := by
    rw [hP4eval]
    refine le_trans (Work.CoreStep.absLevelPairSet_deg_le S T hLF) ?_
    have hsd : S.X.deg ≤ D := le_trans (Nat.le_add_right _ _) hSdeg
    have htd : T.X.deg ≤ D := le_trans (Nat.le_add_right _ _) hTdeg
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  -- ## The stratification of the level-pair set
  obtain ⟨Vl, hVllen, hVlgood, hVlcov, -⟩ :=
    hE5p 0 (pPair n m) (absLevelPairSet S T) hpair
  have hVlSub : ∀ V ∈ Vl, V.X.set ⊆ (absLevelPairSet S T).set := by
    intro V hV z hz
    rw [hVlcov]
    exact Set.mem_iUnion₂.mpr ⟨V, hV, hz⟩
  -- ## The Σ-list
  let FLt : List (Stratum 0 (pPair n m)) :=
    Vl.filter (fun V => decide (pPair n m - V.j < n + (m + 1) - S.j))
  let FTt : List (Stratum 0 (pPair n m)) :=
    Vl.filter (fun V => decide (pPair n m - V.j = n + (m + 1) - S.j))
  let Sig : List (SemiPf (n + pPair n m)) :=
    (FLt.map (sigPair n m)) ++ ((FTt.flatMap PFl).map (sigPair n m))
  have memLow : ∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j → sigPair n m V ∈ Sig := by
    intro V hV hdim
    refine List.mem_append.mpr (Or.inl ?_)
    exact List.mem_map.mpr
      ⟨V, List.mem_filter.mpr ⟨hV, decide_eq_true_eq.mpr hdim⟩, rfl⟩
  have memTop : ∀ (V : Stratum 0 (pPair n m)), V ∈ Vl →
      pPair n m - V.j = n + (m + 1) - S.j → ∀ U ∈ PFl V, sigPair n m U ∈ Sig := by
    intro V hV hdim U hU
    refine List.mem_append.mpr (Or.inr ?_)
    exact List.mem_map.mpr
      ⟨U, List.mem_flatMap.mpr
        ⟨V, List.mem_filter.mpr ⟨hV, decide_eq_true_eq.mpr hdim⟩, hU⟩, rfl⟩
  refine ⟨Sig, ?_, ?_, Vl, ?_, hVlcov, ?_, ?_⟩
  · -- (0) the length bound
    have hVlLen : Vl.length ≤ b5.eval (P4.eval D) :=
      le_trans hVllen (Work.CoreStep.pol_eval_mono_nat hLdeg)
    have hPFlen : ∀ V ∈ Vl, (PFl V).length ≤
        b5''.eval (b6'.eval (b5.eval (P4.eval D))) := by
      intro V hV
      have hfmtV : V.X.fmt ≤ a5 := (hVlgood V hV).1
      refine le_trans (hPFl V hfmtV).2.2 ?_
      refine Work.CoreStep.pol_eval_mono_nat (Work.CoreStep.pol_eval_mono_nat ?_)
      exact le_trans (hVlgood V hV).2.1 (Work.CoreStep.pol_eval_mono_nat hLdeg)
    have h1 : FLt.length ≤ b5.eval (P4.eval D) :=
      le_trans (List.length_filter_le _ _) hVlLen
    have h1' : FTt.length ≤ b5.eval (P4.eval D) :=
      le_trans (List.length_filter_le _ _) hVlLen
    have h2 : (FTt.flatMap PFl).length ≤
        b5.eval (P4.eval D) * b5''.eval (b6'.eval (b5.eval (P4.eval D))) :=
      le_trans
        (Work.CoreStep.length_flatMap_le FTt PFl
          (b5''.eval (b6'.eval (b5.eval (P4.eval D))))
          (fun V hV => hPFlen V (List.mem_filter.mp hV).1))
        (Nat.mul_le_mul_right (b5''.eval (b6'.eval (b5.eval (P4.eval D)))) h1')
    have hmain : FLt.length + (FTt.flatMap PFl).length ≤
        D + b5.eval (P4.eval D) + b5''.eval (b6'.eval (b5.eval (P4.eval D))) +
          b5.eval (P4.eval D) * b5''.eval (b6'.eval (b5.eval (P4.eval D))) :=
      le_trans (Nat.add_le_add h1 h2) (by omega)
    simpa only [Sig, B0, List.length_append, List.length_map, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp] using hmain
  · -- (1) the members of `Sig`
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · -- low stratum of the level-pair set
      obtain ⟨V, hVf, rfl⟩ := List.mem_map.mp hZ
      obtain ⟨hV, hVdec⟩ := List.mem_filter.mp hVf
      have hdim : pPair n m - V.j < n + (m + 1) - S.j := decide_eq_true_eq.mp hVdec
      obtain ⟨hVfmt, hVdeg, hVgood⟩ := hVlgood V hV
      refine ⟨?_, ?_,
        Work.CoreStep.sigPair_nullDimLT V hVgood (fun _ => lt_of_lt_of_le hdim hSK)⟩
      · have h1 := fmt_of V.X hVfmt hAmax5
        simp only [Work.CoreStep.sigPair_fmt, A0]
        omega
      · have h2 : V.X.deg ≤ b5.eval (P4.eval D) :=
          le_trans (Nat.le_add_right _ _)
            (le_trans hVdeg (Work.CoreStep.pol_eval_mono_nat hLdeg))
        refine le_trans (Work.CoreStep.sigPair_deg n m V) ?_
        simp only [B0, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_comp]
        omega
    · -- frontier of a top stratum of the level-pair set
      obtain ⟨U, hUf, rfl⟩ := List.mem_map.mp hZ
      obtain ⟨V, hVf, hUV⟩ := List.mem_flatMap.mp hUf
      obtain ⟨hV, hVdec⟩ := List.mem_filter.mp hVf
      have hdim : pPair n m - V.j = n + (m + 1) - S.j := decide_eq_true_eq.mp hVdec
      obtain ⟨hVfmt, hVdeg, hVgood⟩ := hVlgood V hV
      obtain ⟨hPFlgood, -, -⟩ := hPFl V hVfmt
      obtain ⟨hUgood, hUsub, hUfmt, hUdeg⟩ := hPFlgood U hUV
      refine ⟨?_, ?_, Work.CoreStep.sigPair_nullDimLT U hUgood (fun hne => ?_)⟩
      · have h1 := fmt_of U.X hUfmt hAmax5''
        simp only [Work.CoreStep.sigPair_fmt, A0]
        omega
      · have hVd : V.deg ≤ b5.eval (P4.eval D) :=
          le_trans hVdeg (Work.CoreStep.pol_eval_mono_nat hLdeg)
        have h3 : U.X.deg ≤ b5''.eval (b6'.eval (b5.eval (P4.eval D))) :=
          le_trans (le_trans (Nat.le_add_right _ _) hUdeg)
            (Work.CoreStep.pol_eval_mono_nat (Work.CoreStep.pol_eval_mono_nat hVd))
        refine le_trans (Work.CoreStep.sigPair_deg n m U) ?_
        simp only [B0, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_comp]
        omega
      · have hdrop := frontierDrop_abs V U hVgood hUgood hUsub hne
        have hjl : U.j ≤ pPair n m := Work.CoreStep.Stratum.j_le_card_of_good U hUgood hne
        omega
  · -- (2) `Vl` stratifies the level-pair set
    intro V hV
    exact ⟨(hVlgood V hV).2.2, hVlSub V hV⟩
  · -- (3) the low strata
    intro V hV hdim
    rw [← Work.CoreStep.sigPair_proj n m V]
    intro z hz
    exact Set.mem_iUnion₂.mpr ⟨sigPair n m V, memLow V hV hdim, hz⟩
  · -- (4) the frontiers of the top strata
    intro V hV hdim
    have hcf := (hPFl V ((hVlgood V hV).1)).2.1
    rw [Work.CoreStep.sigmaPairFrontierCover V (PFl V) hcf]
    intro z hz
    obtain ⟨U, hU, hzU⟩ := Set.mem_iUnion₂.mp hz
    exact Set.mem_iUnion₂.mpr ⟨sigPair n m U, memTop V hV hdim U hU, hzU⟩

end Work.WilE7.Endgame
