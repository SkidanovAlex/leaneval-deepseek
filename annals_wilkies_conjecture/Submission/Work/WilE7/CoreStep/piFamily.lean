import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.pieces_of_family
import Submission.Work.WilE7.strata_of_piece
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.WilE7.absGood_locality
import Submission.Work.WilE7.VertSwap
import Submission.Work.WilE7.poly_dominate
import Submission.Work.WilE9G.Assembly.poly_eval_mono
import Submission.Work.WilE7.CoreStep.piPiece
import Submission.Work.WilE7.CoreStep.polyOuterN

/-!
  `Work.WilE7.CoreStep.piFamily`: the family step of the `CoreLT_succ` assembly
  (`NOTES_S32_CoreLT_succ_design.md` §2, steps 1–5).  Given the fibre-cutting hypothesis `hFC`
  and the weak stratification `hE5`, every finite family `X : Fin k → SemiPf (n + (m+1))` of
  format `≤ F` and degree `≤ D` has a list `Pi` of `poly_F(D, k)` strata `T : Stratum 0 (n+(m+1))`
  which are `Good` at the *absolute* split, have finite fibres over `ℝⁿ`, satisfy the immersion
  condition `projRank T z = n + (m+1) - T.j`, each sits (in projection) inside some `X i`, and
  whose projections are exactly `⋃ i, π_n (X i).set`.

  The per-piece work (fibrewise stratification → absolute stratification → rank condition) is
  `Work.WilE7.CoreStep.piPiece`; this file adds the `k`-family bookkeeping: flattening the pieces
  of all `k` members of the family, keeping the provenance, and counting.  Bounds: the pieces of
  `X i` number `≤ bfc.eval D` each (`hFC`), each of them contributes `≤ Bper.eval (bfc.eval D)`
  strata (`piPiece`), so `|Pi| ≤ k * bfc.eval D * Bper.eval (bfc.eval D)`, which is
  `N.eval ![D,k]` for the bivariate `N` of `Work.WilE7.CoreStep.polyOuterN`; the degree bound is
  `(Bper.comp bfc).eval D = Bper.eval (bfc.eval D)`, and the format bound `A` is `piPiece`'s.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilE7.CoreStep
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- The `flatMap` length bound (used twice in `piFamily`): if every member of the list `l` maps to
a list of length `≤ M`, then the flattened list has length `≤ l.length * M`. -/
lemma length_flatMap_le_mul {α β : Type*} (l : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ M) : (l.flatMap f).length ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 : (f a).length ≤ M := h a (by simp)
      have h2 : (t.flatMap f).length ≤ t.length * M := ih (fun b hb => h b (by simp [hb]))
      calc (f a).length + (t.flatMap f).length ≤ M + t.length * M := Nat.add_le_add h1 h2
        _ = (t.length + 1) * M := by ring

theorem piFamily
    (hFC : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
          (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
            ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
          WilkiesDesign.E.projFirst n m '' X.set =
            ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ) (N : MvPolynomial (Fin 2) ℕ),
      ∀ (D k n m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (n + (m + 1))),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ Pi : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))),
          Pi.length ≤ MvPolynomial.eval ![D, k] N ∧
          (∀ T ∈ Pi, T.Good ∧ T.X.fmt ≤ A ∧ T.deg ≤ B.eval D ∧
            (∀ x : Fin n → ℝ, (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite) ∧
            (∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j) ∧
            (∃ i : Fin k, WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet T ⊆
              WilkiesDesign.E.projFirst n (m + 1) '' (X i).set)) ∧
          (⋃ i, WilkiesDesign.E.projFirst n (m + 1) '' (X i).set =
            ⋃ T ∈ Pi, WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet T) := by
  classical
  obtain ⟨afc, bfc, hfc⟩ := hFC F
  obtain ⟨A, Bper, hpiece⟩ := piPiece hE5 afc
  obtain ⟨N, hN⟩ := polyOuterN bfc Bper
  refine ⟨A, Bper.comp bfc, N, ?_⟩
  intro D k n m X hX
  choose L hL using fun i : Fin k => hfc n (m + 1) (X i) (hX i).1
  -- the flat list of pieces, with provenance `Fin k`
  let LP : List (Fin k × SemiPf (n + (m + 1))) :=
    (List.finRange k).flatMap (fun i => (L i).map (fun P => (i, P)))
  have memLP : ∀ q ∈ LP, q.2 ∈ L q.1 := by
    intro q hq
    simp only [LP, List.mem_flatMap, List.mem_map] at hq
    obtain ⟨i, -, P, hP, hPeq⟩ := hq
    rw [← hPeq]
    exact hP
  have memLP_fmt : ∀ q ∈ LP, q.2.fmt ≤ afc :=
    fun q hq => ((hL q.1).2.1 q.2 (memLP q hq)).1
  have memLP_deg : ∀ q ∈ LP, q.2.deg ≤ bfc.eval D :=
    fun q hq => le_trans ((hL q.1).2.1 q.2 (memLP q hq)).2.1
      (Work.WilE9G.Assembly.poly_eval_mono bfc (hX q.1).2)
  have memLP_fin : ∀ q ∈ LP, ∀ x, (fiber q.2.set x).Finite :=
    fun q hq => ((hL q.1).2.1 q.2 (memLP q hq)).2.2
  -- the per-piece stratum list
  let TL : (q : {q : Fin k × SemiPf (n + (m + 1)) // q ∈ LP}) →
      List (Stratum 0 (n + (m + 1))) := fun q =>
    (hpiece (bfc.eval D) n m q.1.2 (memLP_fmt q.1 q.2) (memLP_deg q.1 q.2)
      (memLP_fin q.1 q.2)).choose
  have hTLspec : ∀ q : {q : Fin k × SemiPf (n + (m + 1)) // q ∈ LP},
      TL q = (hpiece (bfc.eval D) n m q.1.2 (memLP_fmt q.1 q.2) (memLP_deg q.1 q.2)
        (memLP_fin q.1 q.2)).choose := fun q => rfl
  have hTLlen : ∀ q : {q : Fin k × SemiPf (n + (m + 1)) // q ∈ LP},
      (TL q).length ≤ Bper.eval (bfc.eval D) := fun q =>
    (Classical.choose_spec (hpiece (bfc.eval D) n m q.1.2 (memLP_fmt q.1 q.2)
      (memLP_deg q.1 q.2) (memLP_fin q.1 q.2))).1
  have hTLcov : ∀ q : {q : Fin k × SemiPf (n + (m + 1)) // q ∈ LP},
      projFirst n (m + 1) '' q.1.2.set =
        ⋃ T' ∈ TL q, projFirst n (m + 1) '' absSet T' := by
    intro q
    have h := (Classical.choose_spec (hpiece (bfc.eval D) n m q.1.2 (memLP_fmt q.1 q.2)
      (memLP_deg q.1 q.2) (memLP_fin q.1 q.2))).2.2
    rw [hTLspec q]
    exact h
  have hTP : ∀ (q : {q : Fin k × SemiPf (n + (m + 1)) // q ∈ LP})
      (T : Stratum 0 (n + (m + 1))),
      T ∈ TL q →
      T.Good ∧ T.X.fmt ≤ A ∧ T.deg ≤ Bper.eval (bfc.eval D) ∧
        absSet T ⊆ q.1.2.set ∧
        (∀ x : Fin n → ℝ, (fiber (absSet T) x).Finite) ∧
        (∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j) ∧
        projFirst n (m + 1) '' q.1.2.set =
          ⋃ T' ∈ TL q, projFirst n (m + 1) '' absSet T' := by
    intro q T hT
    have hspec := Classical.choose_spec (hpiece (bfc.eval D) n m q.1.2 (memLP_fmt q.1 q.2)
      (memLP_deg q.1 q.2) (memLP_fin q.1 q.2))
    rw [hTLspec q] at hT
    exact ⟨(hspec.2.1 T hT).1, (hspec.2.1 T hT).2.1, (hspec.2.1 T hT).2.2.1,
      (hspec.2.1 T hT).2.2.2.1, (hspec.2.1 T hT).2.2.2.2.1, (hspec.2.1 T hT).2.2.2.2.2,
      hspec.2.2⟩
  -- the length bound
  have hPilen : (LP.attach.flatMap TL).length ≤ MvPolynomial.eval ![D, k] N := by
    have h1 := length_flatMap_le_mul LP.attach TL (Bper.eval (bfc.eval D)) (fun a _ => hTLlen a)
    rw [List.length_attach] at h1
    have hLPlen : LP.length ≤ k * bfc.eval D := by
      have h := length_flatMap_le_mul (List.finRange k)
        (fun i : Fin k => (L i).map (fun P => (i, P))) (bfc.eval D)
        (fun i _ => by
          rw [List.length_map]
          exact le_trans (hL i).1 (Work.WilE9G.Assembly.poly_eval_mono bfc (hX i).2))
      simpa only [LP, List.length_finRange] using h
    calc (LP.attach.flatMap TL).length ≤ LP.length * Bper.eval (bfc.eval D) := h1
      _ ≤ (k * bfc.eval D) * Bper.eval (bfc.eval D) := Nat.mul_le_mul_right _ hLPlen
      _ = MvPolynomial.eval ![D, k] N := (hN D k).symm
  refine ⟨LP.attach.flatMap TL, hPilen, ?_, ?_⟩
  · -- the properties of the members of the list
    intro T hT
    obtain ⟨q, -, hTq⟩ := List.mem_flatMap.mp hT
    obtain ⟨hgood, hfmt, hdeg, hsub, hfinT, hrank, -⟩ := hTP q T hTq
    refine ⟨hgood, hfmt, ?_, hfinT, hrank, ?_⟩
    · -- the degree bound: `Bper.eval (bfc.eval D) = (Bper.comp bfc).eval D`
      have heq : (Bper.comp bfc).eval D = Bper.eval (bfc.eval D) := Polynomial.eval_comp
      rw [heq]
      exact hdeg
    · -- the provenance: the projection of `absSet T` lies in that of the piece, hence of `X i`
      refine ⟨q.1.1, ?_⟩
      have hpiece_mem : q.1.2 ∈ L q.1.1 := memLP q.1 q.2
      have hcov := (hL q.1.1).2.2
      calc projFirst n (m + 1) '' absSet T
          ⊆ projFirst n (m + 1) '' q.1.2.set := Set.image_mono hsub
        _ ⊆ projFirst n (m + 1) '' (X q.1.1).set := by
            rw [hcov]
            intro z hz
            simp only [Set.mem_iUnion, exists_prop] at hz ⊢
            obtain ⟨z0, hz0, rfl⟩ := hz
            exact ⟨q.1.2, hpiece_mem, z0, hz0, rfl⟩
  · -- the union identity
    apply Set.Subset.antisymm
    · intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨i, hz⟩ := hz
      rw [(hL i).2.2] at hz
      simp only [Set.mem_iUnion, exists_prop] at hz
      obtain ⟨P, hP, hzP⟩ := hz
      obtain ⟨z0, hz0, rfl⟩ := hzP
      have hq : (i, P) ∈ LP := by
        simp only [LP, List.mem_flatMap, List.mem_map]
        exact ⟨i, List.mem_finRange i, P, hP, rfl⟩
      have hmem : projFirst n (m + 1) z0 ∈ projFirst n (m + 1) '' P.set := ⟨z0, hz0, rfl⟩
      have hcov := hTLcov ⟨(i, P), hq⟩
      rw [hcov] at hmem
      simp only [Set.mem_iUnion, exists_prop] at hmem ⊢
      obtain ⟨T, hT, hzT⟩ := hmem
      refine ⟨T, ?_, hzT⟩
      refine List.mem_flatMap.mpr ⟨⟨(i, P), hq⟩, ?_, ?_⟩
      · exact List.mem_attach LP ⟨(i, P), hq⟩
      · rw [hTLspec ⟨(i, P), hq⟩]
        exact hT
    · intro z hz
      simp only [Set.mem_iUnion, exists_prop] at hz ⊢
      obtain ⟨T, hT, hzT⟩ := hz
      obtain ⟨q, -, hTq⟩ := List.mem_flatMap.mp hT
      obtain ⟨-, -, -, hsub, -, -, -⟩ := hTP q T hTq
      refine ⟨q.1.1, ?_⟩
      have hpiece_mem : q.1.2 ∈ L q.1.1 := memLP q.1 q.2
      have hcov := (hL q.1.1).2.2
      have h2 : projFirst n (m + 1) '' q.1.2.set ⊆ projFirst n (m + 1) '' (X q.1.1).set := by
        rw [hcov]
        intro z' hz'
        simp only [Set.mem_iUnion, exists_prop] at hz' ⊢
        obtain ⟨z0, hz0, rfl⟩ := hz'
        exact ⟨q.1.2, hpiece_mem, z0, hz0, rfl⟩
      exact h2 (Set.image_mono hsub hzT)

end Work.WilE7.CoreStep
