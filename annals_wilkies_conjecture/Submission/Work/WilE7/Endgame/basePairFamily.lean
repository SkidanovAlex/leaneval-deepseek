import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.CoreStep.SigmaFamDefs
import Submission.Work.WilE7.Endgame.PairSet2Bounds
import Submission.Work.CoreStep.sigmaFamilyAux

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair absPairSet absLevelPairSet)
open Work.CoreStep (pairBase sigPair pairSubBaseFst pairFrontierBaseFst)
open Work.WilE7.CoreLTSuccPlan (pairBaseRank pairBaseLin absPairSet2 HypE5 HypE6)

/-! ## Elementary bookkeeping

The three lemmas below are the "mechanical" ingredients of `basePairFamily`:
* the length of a `flatMap` is bounded by `(length of the index list) · (uniform fibre bound)`;
* one polynomial dominates two composed polynomial expressions (the length bound `K · b₅(D)` and
  the degree bound `B_hRank(b₅(D))`);
* the uniform degree bound of the two-piece pair set `absPairSet2 S T`, obtained from
  `absPairSet2_deg_le` and the format hypothesis `(absPairSet2 S T).fmt ≤ Fp`. -/

/-- Length of a `flatMap`: if all the fibres are bounded by `B`, the total length is at most
`l.length * B`. -/
theorem bp_flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have ha : (f a).length ≤ B := h a (by simp)
      have ht : (t.flatMap f).length ≤ t.length * B := ih (fun b hb => h b (by simp [hb]))
      calc (f a).length + (t.flatMap f).length ≤ B + t.length * B := Nat.add_le_add ha ht
        _ = (t.length + 1) * B := by ring

/-- A polynomial `B` dominating both `K * b.eval (C.eval D)` and `Br.eval (b.eval (C.eval D))`
for every `D`. -/
theorem bp_exists_poly_bound (K : ℕ) (b Br C : Polynomial ℕ) :
    ∃ B : Polynomial ℕ, ∀ D : ℕ,
      K * b.eval (C.eval D) ≤ B.eval D ∧ Br.eval (b.eval (C.eval D)) ≤ B.eval D := by
  refine ⟨Polynomial.C K * (b.comp C) + Br.comp (b.comp C), fun D => ?_⟩
  have h1 : (Polynomial.C K * (b.comp C)).eval D = K * b.eval (C.eval D) := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp]
  have h2 : (Br.comp (b.comp C)).eval D = Br.eval (b.eval (C.eval D)) := by
    rw [Polynomial.eval_comp, Polynomial.eval_comp]
  constructor
  · rw [Polynomial.eval_add, h1]
    exact Nat.le_add_right _ _
  · rw [Polynomial.eval_add, h2]
    exact Nat.le_add_left _ _

/-- **Uniform degree bound of the two-piece pair set.**  If `(absPairSet2 S T).fmt ≤ Fp` and
`S.deg, T.deg ≤ D`, then `(absPairSet2 S T).deg ≤ 2*(1+Fp)*(1+2D)^2`. -/
theorem bp_absPairSet2_deg_le {n m Fp D : ℕ} (S T : Stratum 0 (n + (m + 1)))
    (hf : (absPairSet2 S T).fmt ≤ Fp) (hS : S.deg ≤ D) (hT : T.deg ≤ D) :
    (absPairSet2 S T).deg ≤ 2 * (1 + Fp) * (1 + 2 * D) ^ 2 := by
  have hfmt : (absPairSet2 S T).fmt = pPair n m + (S.X.r + T.X.r) := by
    show (0 + pPair n m) + (S.X.r + T.X.r) = pPair n m + (S.X.r + T.X.r)
    rw [Nat.zero_add]
  have hle : n + (m + 1) ≤ pPair n m := by
    show n + (m + 1) ≤ (n + (m + 1)) + (n + (m + 1)); omega
  have hR : (n + (m + 1)) + S.X.r ≤ Fp := by
    have h := hf; rw [hfmt] at h; omega
  have hmain := absPairSet2_deg_le S T hR
  refine le_trans hmain ?_
  have hSd : S.X.deg ≤ D := le_trans (Nat.le_add_right _ _) hS
  have hTd : T.X.deg ≤ D := le_trans (Nat.le_add_right _ _) hT
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-! ## The base-pair family -/

/-- **`basePairFamily` (the `(4′)` clause of `SigmaVPairs` for the base pair set).**

`hRank` is the pair analogue of the rank-slice node `rankSlice_projRank` (the witness is
`Work.WilE7.Endgame.pairRankSlice_nullDimLT`): for every `F` there are bounds `A, B` such that the
base-rank-`r` locus of a `Good` pair stratum `W` of format `≤ F` and rank `r+1 ≤ K` projects into
the `π_n`-image of a semi-Pfaffian set of format `≤ A`, degree `≤ B.eval W.deg`, and measure
`NullDimLT · K`.

Given such a `hRank` and `HypE5`, for every `(S,T)` whose two-piece pair set is of bounded format
we produce a single list `Sig` (all members `NullDimLT · K` and of format/degree bounded uniformly
in `D`) whose `π_n`-images cover the *whole* base-rank-deficient locus (`pairBaseRank < dim S`) of
every stratum `W` of an `hE5`-decomposition `Wl` of `absPairSet2 S T`. -/
theorem basePairFamily
    (hRank : ∀ (F : ℕ), ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m r K : ℕ) (W : Stratum 0 (pPair n m)),
        W.Good → W.X.fmt ≤ F → r + 1 ≤ K →
        ∃ Z : SemiPf (n + pPair n m),
          Z.fmt ≤ A ∧ Z.deg ≤ B.eval W.deg ∧
          NullDimLT (projFirst n (pPair n m) '' Z.set) K ∧
          pairBase n m '' {w : Fin (0 + pPair n m) → ℝ | w ∈ W.X.set ∧
            pairBaseRank W w = r} ⊆ projFirst n (pPair n m) '' Z.set)
    (hE5 : HypE5) (n m K Fp : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (D : ℕ) (S T : Stratum 0 (n + (m + 1))),
        S.Good → S.X.fmt ≤ Fp → S.deg ≤ D → n + (m + 1) - S.j ≤ K →
        T.Good → T.X.fmt ≤ Fp → T.deg ≤ D →
        (absPairSet2 S T).fmt ≤ Fp →
        ∃ Sig : List (SemiPf (n + pPair n m)),
          Sig.length ≤ B.eval D ∧
          (∀ Z ∈ Sig, Z.fmt ≤ A ∧ Z.deg ≤ B.eval D ∧
            NullDimLT (projFirst n (pPair n m) '' Z.set) K) ∧
          ∃ Wl : List (Stratum 0 (pPair n m)),
            (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet2 S T).set) ∧
            (absPairSet2 S T).set = ⋃ W ∈ Wl, W.X.set ∧
            (∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - S.j →
              pairBase n m w ∈ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) := by
  classical
  -- the format bound of the pair strata, and the two polynomial bounds
  obtain ⟨a5, b5, hE5p⟩ := hE5 Fp
  obtain ⟨Ar, Br, hRankp⟩ := hRank a5
  let Cpoly : Polynomial ℕ :=
    Polynomial.C (2 * (1 + Fp)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2
  have hCpoly : ∀ D : ℕ, Cpoly.eval D = 2 * (1 + Fp) * (1 + 2 * D) ^ 2 := by
    intro D
    simp [Cpoly]
  obtain ⟨B, hB⟩ := bp_exists_poly_bound K b5 Br Cpoly
  refine ⟨Ar, B, ?_⟩
  intro D S T hSg hSf hSd hSK hTg hTf hTd hPfmt
  -- the `hE5`-decomposition of the two-piece pair set
  obtain ⟨Wl, hWllen, hWgood, hWcov, -⟩ := hE5p 0 (pPair n m) (absPairSet2 S T) hPfmt
  have hWfmt : ∀ W ∈ Wl, W.X.fmt ≤ a5 := fun W hW => (hWgood W hW).1
  have hWdeg : ∀ W ∈ Wl, W.deg ≤ b5.eval (absPairSet2 S T).deg :=
    fun W hW => (hWgood W hW).2.1
  have hWGood : ∀ W ∈ Wl, W.Good := fun W hW => (hWgood W hW).2.2
  have hPdeg : (absPairSet2 S T).deg ≤ Cpoly.eval D := by
    rw [hCpoly D]
    exact bp_absPairSet2_deg_le S T hPfmt hSd hTd
  -- the rank-slice set attached to a stratum `W ∈ Wl` and a rank `r < K`
  let Zf : {W // W ∈ Wl} → Fin K → SemiPf (n + pPair n m) :=
    fun W r => (hRankp n m r.1 K W.1 (hWGood W.1 W.2) (hWfmt W.1 W.2)
      (Nat.succ_le_of_lt r.2)).choose
  have hZspec : ∀ (W : {W // W ∈ Wl}) (r : Fin K),
      (Zf W r).fmt ≤ Ar ∧ (Zf W r).deg ≤ Br.eval W.1.deg ∧
      NullDimLT (projFirst n (pPair n m) '' (Zf W r).set) K ∧
      pairBase n m '' {w : Fin (0 + pPair n m) → ℝ | w ∈ W.1.X.set ∧
        pairBaseRank W.1 w = r.1} ⊆ projFirst n (pPair n m) '' (Zf W r).set :=
    fun W r => (hRankp n m r.1 K W.1 (hWGood W.1 W.2) (hWfmt W.1 W.2)
      (Nat.succ_le_of_lt r.2)).choose_spec
  let Sig : List (SemiPf (n + pPair n m)) :=
    Wl.attach.flatMap (fun W => (List.finRange K).map (Zf W))
  refine ⟨Sig, ?_, ?_, Wl, ?_, hWcov, ?_⟩
  · -- the length of `Sig`
    have h1 : Sig.length ≤ Wl.length * K := by
      simp only [Sig]
      refine le_trans (bp_flatMap_length_le Wl.attach
        (fun W => (List.finRange K).map (Zf W)) K ?_) ?_
      · intro W _
        simp
      · rw [List.length_attach]
    have h2 : Wl.length * K ≤ K * b5.eval (Cpoly.eval D) := by
      have h3 : Wl.length ≤ b5.eval (Cpoly.eval D) :=
        le_trans hWllen (Work.CoreStep.pol_eval_mono_nat hPdeg)
      calc Wl.length * K ≤ b5.eval (Cpoly.eval D) * K := Nat.mul_le_mul_right K h3
        _ = K * b5.eval (Cpoly.eval D) := by ring
    exact le_trans (le_trans h1 h2) (hB D).1
  · -- the members of `Sig`
    intro Z hZ
    simp only [Sig] at hZ
    obtain ⟨W, -, hZW⟩ := List.mem_flatMap.mp hZ
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hZW
    refine ⟨(hZspec W r).1, ?_, (hZspec W r).2.2.1⟩
    refine le_trans (hZspec W r).2.1 ?_
    refine le_trans (Work.CoreStep.pol_eval_mono_nat ?_) (hB D).2
    exact le_trans (hWdeg W.1 W.2) (Work.CoreStep.pol_eval_mono_nat hPdeg)
  · -- the decomposition of the pair set
    intro W hW
    refine ⟨hWGood W hW, ?_⟩
    intro z hz
    rw [hWcov]
    exact Set.mem_iUnion₂.mpr ⟨W, hW, hz⟩
  · -- the rank-deficient locus is covered
    intro W hW w hwW hrank
    have hr0 : pairBaseRank W w < K := lt_of_lt_of_le hrank hSK
    refine Set.mem_iUnion₂.mpr ⟨Zf ⟨W, hW⟩ ⟨pairBaseRank W w, hr0⟩, ?_, ?_⟩
    · simp only [Sig]
      refine List.mem_flatMap.mpr ⟨⟨W, hW⟩, List.mem_attach _ _, ?_⟩
      exact List.mem_map.mpr ⟨⟨pairBaseRank W w, hr0⟩, List.mem_finRange _, rfl⟩
    · exact (hZspec ⟨W, hW⟩ ⟨pairBaseRank W w, hr0⟩).2.2.2 ⟨w, ⟨hwW, rfl⟩, rfl⟩

end Work.WilE7.Endgame
