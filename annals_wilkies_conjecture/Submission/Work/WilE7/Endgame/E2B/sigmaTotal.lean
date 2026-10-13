import Mathlib
import Submission.Work.WilE7.Endgame.sigmaFamily_len_unif
import Submission.Work.WilE7.Endgame.PairSet2Bounds
import Submission.Work.WilE7.Endgame.E2Aux

namespace Work.WilE7.Endgame.E2B

open Classical
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

theorem sigmaTotal (hE5 : Work.WilE7.CoreLTSuccPlan.HypE5)
    (hE6 : Work.WilE7.CoreLTSuccPlan.HypE6)
    (h1 : Work.WilE7.CoreLTSuccPlan.SigmaVPairs) (n K Fp F : ℕ) :
    ∃ (Q : MvPolynomial (Fin 3) ℕ) (A : ℕ) (B : Polynomial ℕ),
      ∀ (m : ℕ) (hm : m ≤ F) (D : ℕ)
        (Pi Pv : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))))
        (hPi : ∀ T ∈ Pi, T.Good ∧ T.X.fmt ≤ Fp ∧ T.deg ≤ D)
        (hPv : ∀ T ∈ Pv, T.Good ∧ T.X.fmt ≤ Fp ∧ T.deg ≤ D)
        (hPidim : ∀ S ∈ Pi, n + (m + 1) - S.j ≤ K)
        (hPiF : ∀ S ∈ Pi, (Work.WilE7.CoreStep.absPairSet S).fmt ≤ Fp)
        (hPiL : ∀ S ∈ Pi, ∀ T ∈ Pi, (Work.WilE7.CoreStep.absLevelPairSet S T).fmt ≤ Fp)
        (hVpF : ∀ S ∈ Pi, ∀ T ∈ Pv, (Work.WilE7.CoreLTSuccPlan.absPairSet2 S T).fmt ≤ Fp)
        (hVpL : ∀ S ∈ Pi, ∀ T ∈ Pv, (Work.WilE7.CoreStep.absLevelPairSet S T).fmt ≤ Fp),
        ∃ Sig : List (WilkiesDesign.E.SemiPf (n + Work.WilE7.CoreStep.pPair n m)),
          Sig.length ≤ MvPolynomial.eval ![D, Pi.length, Pv.length] Q ∧
          (∀ Z ∈ Sig, Z.fmt ≤ A ∧ Z.deg ≤ B.eval D ∧
            Work.WilE7.MainDesign.NullDimLT
              (WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set) K) ∧
          (∀ T ∈ Pi, n + (m + 1) - T.j < K →
            WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet T ⊆
              ⋃ Z ∈ Sig, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set) ∧
          (∀ T ∈ Pi, Work.CoreStep.frontierSet n m T ⊆
              ⋃ Z ∈ Sig, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set) ∧
          (∀ T ∈ Pi, ∃ Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
            (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (Work.WilE7.CoreStep.absPairSet T).set) ∧
            ((Work.WilE7.CoreStep.absPairSet T).set = ⋃ W ∈ Wl, W.X.set) ∧
            (∀ W ∈ Wl, Work.WilE7.CoreStep.pPair n m - W.j < n + (m + 1) - T.j →
              Work.CoreStep.pairSubBaseFst n m W ⊆
                ⋃ Z ∈ Sig, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set)) ∧
          (∀ T ∈ Pi, ∀ T' ∈ Pi, ∃ Vl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
            (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet T T').set) ∧
            ((Work.WilE7.CoreStep.absLevelPairSet T T').set = ⋃ V ∈ Vl, V.X.set) ∧
            (∀ V ∈ Vl, Work.WilE7.CoreStep.pPair n m - V.j < n + (m + 1) - T.j →
              Work.CoreStep.pairSubBaseFst n m V ⊆
                ⋃ Z ∈ Sig, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set) ∧
            (∀ V ∈ Vl, Work.WilE7.CoreStep.pPair n m - V.j = n + (m + 1) - T.j →
              Work.CoreStep.pairFrontierBaseFst n m V ⊆
                ⋃ Z ∈ Sig, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set)) ∧
          (∀ S ∈ Pi, ∀ T ∈ Pv, ∃ Vl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
            (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (Work.WilE7.CoreStep.absLevelPairSet S T).set) ∧
            ((Work.WilE7.CoreStep.absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set) ∧
            (∀ V ∈ Vl, Work.WilE7.CoreStep.pPair n m - V.j < n + (m + 1) - S.j →
              Work.CoreStep.pairSubBaseFst n m V ⊆
                ⋃ Z ∈ Sig, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set) ∧
            (∀ V ∈ Vl, Work.WilE7.CoreStep.pPair n m - V.j = n + (m + 1) - S.j →
              Work.CoreStep.pairFrontierBaseFst n m V ⊆
                ⋃ Z ∈ Sig, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set)) ∧
          (∀ S ∈ Pi, ∀ T ∈ Pv, ∃ Wl : List (WilkiesDesign.E.Stratum 0 (Work.WilE7.CoreStep.pPair n m)),
            (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (Work.WilE7.CoreLTSuccPlan.absPairSet2 S T).set) ∧
            ((Work.WilE7.CoreLTSuccPlan.absPairSet2 S T).set = ⋃ W ∈ Wl, W.X.set) ∧
            (∀ W ∈ Wl, ∀ w ∈ W.X.set,
              Work.WilE7.CoreLTSuccPlan.pairBaseRank W w < n + (m + 1) - S.j →
              Work.CoreStep.pairBase n m w ∈
                ⋃ Z ∈ Sig, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set)) := by
  classical
  -- The two producers (the `Pi`-only Σ-family and the `Pi × Pv` Σ-family), chosen for every fibre
  -- dimension `m₀`, with their hoisted bounds.
  let QS : ℕ → MvPolynomial (Fin 2) ℕ :=
    fun m₀ => (Work.WilE7.Endgame.sigmaFamily_len_unif hE5 hE6 n m₀ K Fp).choose
  let AS : ℕ → ℕ :=
    fun m₀ => (Work.WilE7.Endgame.sigmaFamily_len_unif hE5 hE6 n m₀ K Fp).choose_spec.choose
  let BS : ℕ → Polynomial ℕ :=
    fun m₀ =>
      (Work.WilE7.Endgame.sigmaFamily_len_unif hE5 hE6 n m₀ K Fp).choose_spec.choose_spec.choose
  let QV : ℕ → MvPolynomial (Fin 3) ℕ := fun m₀ => (h1 n m₀ K Fp).choose
  let AV : ℕ → ℕ := fun m₀ => (h1 n m₀ K Fp).choose_spec.choose
  let BV : ℕ → Polynomial ℕ := fun m₀ => (h1 n m₀ K Fp).choose_spec.choose_spec.choose
  -- `QS` lives in two variables; view it in three (`l` unused).
  let L2 : ℕ → MvPolynomial (Fin 3) ℕ := fun m₀ => (Work.WilE7.Endgame.mvpoly2_to_3 (QS m₀)).choose
  have hL2 : ∀ (m₀ D a b : ℕ), MvPolynomial.eval ![D, a, b] (L2 m₀) =
      MvPolynomial.eval ![D, a] (QS m₀) :=
    fun m₀ D a b => (Work.WilE7.Endgame.mvpoly2_to_3 (QS m₀)).choose_spec D a b
  let R : Finset ℕ := Finset.range (F + 1)
  -- The four bounds, obtained by summing over the (finitely many) fibre dimensions `m₀ ≤ F`.
  let QQ : MvPolynomial (Fin 3) ℕ := (∑ m₀ ∈ R, L2 m₀) + (∑ m₀ ∈ R, QV m₀)
  let UA : ℕ := ∑ m₀ ∈ R, AS m₀
  let UB : ℕ := ∑ m₀ ∈ R, AV m₀
  let AA : ℕ := UA + UB
  let BB : Polynomial ℕ := ∑ m₀ ∈ R, (BS m₀ + BV m₀)
  refine ⟨QQ, AA, BB, ?_⟩
  intro m hm D Pi Pv hPi hPv hPidim hPiF hPiL hVpF hVpL
  have hmR : m ∈ R := by
    simp only [R]; exact Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  -- The Σ-family of the `Pi`-part: clauses (2)–(6).
  obtain ⟨SigS, hSlen, hSbd, hS3, hS4, hS5, hS6⟩ :=
    (Work.WilE7.Endgame.sigmaFamily_len_unif hE5 hE6 n m K Fp).choose_spec.choose_spec.choose_spec
      D Pi (fun T hT => (hPi T hT).1) (fun T hT => (hPi T hT).2.1)
      (fun T hT => (hPi T hT).2.2) hPidim hPiF hPiL
  -- The Σ-family of the `Pi × Pv`-part: clauses (7)–(8).
  obtain ⟨SigV, hVlen, hVbd, hV7, hV8⟩ :=
    (h1 n m K Fp).choose_spec.choose_spec.choose_spec D Pi Pv
      (fun T hT => by
        rcases List.mem_append.mp hT with h | h
        · exact hPi T h
        · exact hPv T h)
      hPidim
      (fun S hS T hT => ⟨hVpL S hS T hT, hVpF S hS T hT⟩)
  -- Monotonicity of the union in the list of presentations.
  have mono : ∀ {L₁ L₂ : List (WilkiesDesign.E.SemiPf (n + Work.WilE7.CoreStep.pPair n m))},
      (∀ Z ∈ L₁, Z ∈ L₂) →
      (⋃ Z ∈ L₁, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set) ⊆
        (⋃ Z ∈ L₂, WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' Z.set) := by
    intro L₁ L₂ h x hx
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨Z, h Z hZ, hxZ⟩
  have hSV : ∀ Z ∈ SigS, Z ∈ SigS ++ SigV := fun Z hZ => List.mem_append.mpr (Or.inl hZ)
  have hVS : ∀ Z ∈ SigV, Z ∈ SigS ++ SigV := fun Z hZ => List.mem_append.mpr (Or.inr hZ)
  -- The numeric bounds at the fixed `D`, as sums over `R`.
  let SS : ℕ := ∑ m₀ ∈ R, MvPolynomial.eval ![D, Pi.length] (QS m₀)
  let SV : ℕ := ∑ m₀ ∈ R, MvPolynomial.eval ![D, Pi.length, Pv.length] (QV m₀)
  let dB : ℕ → ℕ := fun m₀ => (BS m₀).eval D + (BV m₀).eval D
  let DB : ℕ := ∑ m₀ ∈ R, dB m₀
  have hBeval : BB.eval D = DB := by
    rw [show BB = ∑ m₀ ∈ R, (BS m₀ + BV m₀) from rfl, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl (fun m₀ _ => Polynomial.eval_add)
  have hQ2 : MvPolynomial.eval ![D, Pi.length, Pv.length] (∑ m₀ ∈ R, L2 m₀) = SS := by
    rw [MvPolynomial.eval_sum]
    exact Finset.sum_congr rfl (fun m₀ _ => hL2 m₀ D Pi.length Pv.length)
  have hQ3 : MvPolynomial.eval ![D, Pi.length, Pv.length] (∑ m₀ ∈ R, QV m₀) = SV := by
    rw [MvPolynomial.eval_sum]
  have hQeval : MvPolynomial.eval ![D, Pi.length, Pv.length] QQ = SS + SV := by
    rw [show QQ = (∑ m₀ ∈ R, L2 m₀) + (∑ m₀ ∈ R, QV m₀) from rfl, MvPolynomial.eval_add,
      hQ2, hQ3]
  refine ⟨SigS ++ SigV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (0) the length bound
    rw [List.length_append, hQeval]
    have e1 : SigS.length ≤ MvPolynomial.eval ![D, Pi.length] (QS m) := hSlen
    have e2 : SigV.length ≤ MvPolynomial.eval ![D, Pi.length, Pv.length] (QV m) := hVlen
    have hs1 : MvPolynomial.eval ![D, Pi.length] (QS m) ≤ SS :=
      Finset.single_le_sum (f := fun m₀ => MvPolynomial.eval ![D, Pi.length] (QS m₀))
        (fun i _ => Nat.zero_le _) hmR
    have hs2 : MvPolynomial.eval ![D, Pi.length, Pv.length] (QV m) ≤ SV :=
      Finset.single_le_sum (f := fun m₀ => MvPolynomial.eval ![D, Pi.length, Pv.length] (QV m₀))
        (fun i _ => Nat.zero_le _) hmR
    omega
  · -- (2) the format, degree and dimension bounds of the members of `Sig`
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · obtain ⟨hf, hd, hn⟩ := hSbd Z hZ
      refine ⟨?_, ?_, hn⟩
      · refine le_trans hf ?_
        refine le_trans (Finset.single_le_sum (f := AS) (fun i _ => Nat.zero_le _) hmR) ?_
        exact Nat.le_add_right UA UB
      · have h1 : Z.deg ≤ dB m :=
          le_trans hd (Nat.le_add_right ((BS m).eval D) ((BV m).eval D))
        refine le_trans h1 ?_
        rw [hBeval]
        exact Finset.single_le_sum (f := dB) (fun i _ => Nat.zero_le _) hmR
    · obtain ⟨hf, hd, hn⟩ := hVbd Z hZ
      refine ⟨?_, ?_, hn⟩
      · refine le_trans hf ?_
        refine le_trans (Finset.single_le_sum (f := AV) (fun i _ => Nat.zero_le _) hmR) ?_
        exact Nat.le_add_left UB UA
      · have h1 : Z.deg ≤ dB m :=
          le_trans hd (Nat.le_add_left ((BV m).eval D) ((BS m).eval D))
        refine le_trans h1 ?_
        rw [hBeval]
        exact Finset.single_le_sum (f := dB) (fun i _ => Nat.zero_le _) hmR
  · -- (3) the `π_n`-images of the low pieces
    intro T hT hK
    exact subset_trans (hS3 T hT hK) (mono hSV)
  · -- (4) the frontiers of the pieces
    intro T hT
    exact subset_trans (hS4 T hT) (mono hSV)
  · -- (5) the base-pair strata of a piece
    intro T hT
    obtain ⟨Wl, hg, hc, hcond⟩ := hS5 T hT
    exact ⟨Wl, hg, hc, fun W hW hd => subset_trans (hcond W hW hd) (mono hSV)⟩
  · -- (6) the level-pair strata of a pair of pieces
    intro T hT T' hT'
    obtain ⟨Vl, hg, hc, hc1, hc2⟩ := hS6 T hT T' hT'
    exact ⟨Vl, hg, hc, (fun V hV hd => subset_trans (hc1 V hV hd) (mono hSV)),
      (fun V hV hd => subset_trans (hc2 V hV hd) (mono hSV))⟩
  · -- (7) the level-pair strata of a vertical pair
    intro S hS T hT
    obtain ⟨Vl, hg, hc, hc1, hc2⟩ := hV7 S hS T hT
    exact ⟨Vl, hg, hc, (fun V hV hd => subset_trans (hc1 V hV hd) (mono hVS)),
      (fun V hV hd => subset_trans (hc2 V hV hd) (mono hVS))⟩
  · -- (8) the base-pair strata of a vertical pair
    intro S hS T hT
    obtain ⟨Wl, hg, hc, hcond⟩ := hV8 S hS T hT
    exact ⟨Wl, hg, hc, fun W hW w hw hr => mono hVS (hcond W hW w hw hr)⟩

end Work.WilE7.Endgame.E2B
