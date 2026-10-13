import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.strata_of_piece
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
noncomputable section
namespace Work.WilE7.CoreStep
open Classical
open WilkiesDesign WilkiesDesign.E

/-- The `absPt`-image of a semi-Pfaffian set, reindexed along the value-preserving equivalence
`Fin N ≃ Fin (0 + N)`, is the set itself: `absPt` is only a change of bookkeeping between the
coordinate types `Fin (0 + N)` and `Fin N`. -/
theorem absPt_image_reindex {N : ℕ} (X : SemiPf N) :
    Work.WilE7.MainDesign.absPt ''
      (Work.WilE7.SemiPf.reindex (Work.WilE7.finEquiv (Nat.zero_add N)).symm X).set = X.set := by
  rw [Work.WilE7.sp_reindex_set]
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact hy
  · intro x hx
    refine ⟨fun j : Fin (0 + N) => x (Fin.cast (Nat.zero_add N) j), ?_, ?_⟩
    · have hfun : (fun i : Fin N =>
          (fun j : Fin (0 + N) => x (Fin.cast (Nat.zero_add N) j))
            ((Work.WilE7.finEquiv (Nat.zero_add N)).symm i)) = x := by
        funext i
        show x (Fin.cast (Nat.zero_add N) ((Work.WilE7.finEquiv (Nat.zero_add N)).symm i)) = x i
        congr 1
      show (fun i : Fin N =>
          (fun j : Fin (0 + N) => x (Fin.cast (Nat.zero_add N) j))
            ((Work.WilE7.finEquiv (Nat.zero_add N)).symm i)) ∈ X.set
      rw [hfun]
      exact hx
    · funext i
      show x (Fin.cast (Nat.zero_add N) ((Work.WilE7.finEquiv (Nat.zero_add N)).symm i)) = x i
      congr 1

/-- The per-piece step of `CoreStep.piFamily`: given the frozen weak stratification `hE5`, every semi-Pfaffian piece `P : SemiPf (n + (m+1))` of format `≤ F`, degree `≤ D` and with *finite fibres* over `ℝⁿ` can be covered by `poly_F(D)` strata `T : Stratum 0 (n + (m+1))` which are `Good` at the *absolute* split `(0, n+(m+1))`, such that (i) `absSet T ⊆ P.set`, (ii) `absSet T` still has finite fibres over `ℝⁿ`, (iii) the immersion/rank condition `projRank T z = n + (m+1) - T.j` holds on `T.X.set`, and (iv) the projections to `ℝⁿ` agree exactly: `projFirst n (m+1) '' P.set = ⋃ T ∈ L, projFirst n (m+1) '' absSet T`.

PROOF SKETCH (all machinery is already proved in this workspace).

1. `obtain ⟨A1, q, hs⟩ := Work.WilE7.strata_of_piece hE5 F`.  For `P` with `P.fmt ≤ F`, `P.deg ≤ D` and finite fibres, `hs` gives `SL : List (Stratum n (m+1))` with `SL.length ≤ q.eval D`, every `Sf ∈ SL` satisfying `Sf.X.fmt ≤ A1`, `Sf.deg ≤ q.eval D`, `Sf.Good`, `Sf.j = m+1`, finite fibres, `Sf.X.set.Nonempty`, plus `P.set = ⋃ Sf ∈ SL, Sf.X.set`.
2. `obtain ⟨aT, bT, hT⟩ := hE5 A1`.  For each `Sf ∈ SL`, apply `hT 0 (0 + (n+(m+1))) (SemiPf.reindex (finEquiv (Nat.zero_add (n+(m+1)))).symm Sf.X)`; the format bound is `(0 + (n+(m+1))) + Sf.X.r ≤ A1` (from `Sf.X.fmt ≤ A1` by `omega`).  This gives `TL : List (Stratum 0 (n+(m+1)))` with `TL.length ≤ bT.eval Sf.X.deg`, each `T` `Good`, `T.X.fmt ≤ aT`, `T.deg ≤ bT.eval Sf.X.deg`, and `(reindex Sf.X).set = ⋃ T ∈ TL, T.X.set`.
3. Take `L := SL.flatMap TL` (the list of all `T`), `A := aT`, `B := (bT.comp q) * (q + 1)`.  Then `B.eval D = bT.eval (q.eval D) * (q.eval D + 1)` dominates both `bT.eval (q.eval D)` (degree bound of the `T`) and `q.eval D * bT.eval (q.eval D)` (the number of the `T`).
4. Casts: `Work.WilE7.sp_reindex_set (finEquiv (Nat.zero_add N)).symm X` says membership in `(reindex ...).set` is `absPt y ∈ X.set` (both sides are functions `Fin N → ℝ` with equal values, `Fin.ext rfl`), hence `absPt '' (SemiPf.reindex (finEquiv (Nat.zero_add N)).symm X).set = X.set`; this gives `absSet T ⊆ Sf.X.set ⊆ P.set` and (with `Sf.X.set = absPt '' (reindex Sf.X).set`) also (iv) via `Set.image_iUnion`/`Set.image_mono`.
5. (ii) is `(fiber P.set x).Finite.subset` along `absSet T ⊆ P.set`; (iii) is `Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood T hT T.Good Sf hSf (hj : Sf.j = m+1) (hsub : absSet T ⊆ Sf.X.set)`. -/
theorem piPiece
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (D n m : ℕ) (P : WilkiesDesign.E.SemiPf (n + (m + 1))),
        P.fmt ≤ F → P.deg ≤ D →
        (∀ x : Fin n → ℝ, (WilkiesDesign.E.fiber P.set x).Finite) →
        ∃ L : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))),
          L.length ≤ B.eval D ∧
          (∀ T ∈ L, T.Good ∧ T.X.fmt ≤ A ∧ T.deg ≤ B.eval D ∧
            Work.WilE7.MainDesign.absSet T ⊆ P.set ∧
            (∀ x : Fin n → ℝ,
              (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite) ∧
            (∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j)) ∧
          WilkiesDesign.E.projFirst n (m + 1) '' P.set =
            ⋃ T ∈ L, WilkiesDesign.E.projFirst n (m + 1) '' Work.WilE7.MainDesign.absSet T := by
  obtain ⟨A1, q, hs⟩ := Work.WilE7.strata_of_piece hE5 F
  obtain ⟨aT, bT, hT⟩ := hE5 A1
  refine ⟨aT, (bT.comp q) * (q + 1), ?_⟩
  intro D n m P hfmt hdeg hfin
  obtain ⟨SL, hSLlen, hSLmem, hSLcov, _hSLdisj⟩ := hs D n m P hfmt hdeg hfin
  -- the absolute reindexing `Fin (n + (m+1)) ≃ Fin (0 + (n + (m+1)))`
  let e : Fin (n + (m + 1)) ≃ Fin (0 + (n + (m + 1))) :=
    (Work.WilE7.finEquiv (Nat.zero_add (n + (m + 1)))).symm
  have hfmtmem : ∀ Sf ∈ SL, (Work.WilE7.SemiPf.reindex e Sf.X).fmt ≤ A1 := by
    intro Sf hSf
    have h : (n + (m + 1)) + Sf.X.r ≤ A1 := (hSLmem Sf hSf).1
    have h2 : (Work.WilE7.SemiPf.reindex e Sf.X).fmt = (0 + (n + (m + 1))) + Sf.X.r := rfl
    rw [h2]
    simpa only [Nat.zero_add] using h
  have hTLspec : ∀ Sf ∈ SL, ∃ TL : List (WilkiesDesign.E.Stratum 0 (n + (m + 1))),
      TL.length ≤ bT.eval (Work.WilE7.SemiPf.reindex e Sf.X).deg ∧
      (∀ T ∈ TL, T.X.fmt ≤ aT ∧ T.deg ≤ bT.eval (Work.WilE7.SemiPf.reindex e Sf.X).deg ∧
        T.Good) ∧
      (Work.WilE7.SemiPf.reindex e Sf.X).set = (⋃ T ∈ TL, T.X.set) ∧
      TL.Pairwise (fun S T => Disjoint S.X.set T.X.set) :=
    fun Sf hSf => hT 0 (n + (m + 1)) (Work.WilE7.SemiPf.reindex e Sf.X) (hfmtmem Sf hSf)
  let TLall : WilkiesDesign.E.Stratum n (m + 1) →
      List (WilkiesDesign.E.Stratum 0 (n + (m + 1))) :=
    fun Sf => if h : Sf ∈ SL then (hTLspec Sf h).choose else []
  have hTLall_eq : ∀ Sf (h : Sf ∈ SL), TLall Sf = (hTLspec Sf h).choose := by
    intro Sf h
    show (if h' : Sf ∈ SL then (hTLspec Sf h').choose else []) = (hTLspec Sf h).choose
    rw [dite_eq_left h]
  -- the degree of `Sf.X` is bounded by `q.eval D`
  have hdegSf : ∀ Sf ∈ SL, Sf.X.deg ≤ q.eval D := by
    intro Sf hSf
    refine le_trans ?_ (hSLmem Sf hSf).2.1
    show Sf.X.deg ≤ Sf.deg
    simp only [WilkiesDesign.E.Stratum.deg]
    exact Nat.le_add_right _ _
  -- `absPt` undoes the reindexing
  have hAbsReindexOf : ∀ Sf ∈ SL,
      Work.WilE7.MainDesign.absPt '' (Work.WilE7.SemiPf.reindex e Sf.X).set = Sf.X.set :=
    fun Sf _ => absPt_image_reindex Sf.X
  have hcovOf : ∀ Sf ∈ SL,
      (Work.WilE7.SemiPf.reindex e Sf.X).set = ⋃ T ∈ TLall Sf, T.X.set := by
    intro Sf hSf
    rw [hTLall_eq Sf hSf]
    exact (hTLspec Sf hSf).choose_spec.2.2.1
  have hsubAbsOf : ∀ Sf (hSf : Sf ∈ SL) (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
      (hT : T ∈ TLall Sf), Work.WilE7.MainDesign.absSet T ⊆ Sf.X.set := by
    intro Sf hSf T hT
    have h1 : Work.WilE7.MainDesign.absSet T ⊆
        Work.WilE7.MainDesign.absPt '' (Work.WilE7.SemiPf.reindex e Sf.X).set := by
      apply Set.image_mono
      rw [hcovOf Sf hSf]
      intro z hz
      exact Set.mem_iUnion₂.mpr ⟨T, hT, hz⟩
    rwa [hAbsReindexOf Sf hSf] at h1
  have hB : ((bT.comp q) * (q + 1)).eval D = bT.eval (q.eval D) * (q.eval D + 1) := by
    rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one]
  refine ⟨SL.flatMap TLall, ?_, ?_, ?_⟩
  · -- the length bound
    rw [List.length_flatMap]
    have hc : ∀ Sf ∈ SL, (TLall Sf).length ≤ bT.eval (q.eval D) := by
      intro Sf hSf
      rw [hTLall_eq Sf hSf]
      refine le_trans (hTLspec Sf hSf).choose_spec.1 ?_
      rw [Work.WilE7.sp_reindex_deg]
      exact Work.WilE7.poly_eval_mono_nat bT (hdegSf Sf hSf)
    have hsum : (SL.map (fun Sf => (TLall Sf).length)).sum
        ≤ ((SL.map fun _ => bT.eval (q.eval D))).sum :=
      List.sum_le_sum fun Sf hSf => hc Sf hSf
    have hconst : ((SL.map fun _ => bT.eval (q.eval D))).sum
        = SL.length * bT.eval (q.eval D) := by
      rw [List.map_const', List.sum_replicate]
      simp
    rw [hconst] at hsum
    rw [hB]
    refine le_trans hsum ?_
    refine le_trans (Nat.mul_le_mul_right _ hSLlen) ?_
    rw [Nat.mul_comm (q.eval D) (bT.eval (q.eval D))]
    exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  · -- the members of the flattened list
    intro T hT
    obtain ⟨Sf, hSf, hTSf⟩ := List.mem_flatMap.mp hT
    have hsubAbs : Work.WilE7.MainDesign.absSet T ⊆ Sf.X.set := hsubAbsOf Sf hSf T hTSf
    rw [hTLall_eq Sf hSf] at hTSf
    obtain ⟨hTfmt, hTdeg, hTgood⟩ := (hTLspec Sf hSf).choose_spec.2.1 T hTSf
    have hsubP : Work.WilE7.MainDesign.absSet T ⊆ P.set := by
      intro z hz
      rw [hSLcov]
      exact Set.mem_iUnion₂.mpr ⟨Sf, hSf, hsubAbs hz⟩
    have hfinAbs : ∀ x : Fin n → ℝ,
        (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite :=
      fun x => (hfin x).subset fun y hy => hsubP hy
    have hrank : ∀ z ∈ T.X.set,
        Work.WilE7.MainDesign.projRank T z = n + (m + 1) - T.j :=
      fun z hz => Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood (n := n) (m := m + 1) T
        hTgood Sf (hSLmem Sf hSf).2.2.1 (hSLmem Sf hSf).2.2.2.1 hsubAbs hz
    have hTdegB : T.deg ≤ ((bT.comp q) * (q + 1)).eval D := by
      rw [hB]
      refine le_trans (le_trans hTdeg ?_) (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      rw [Work.WilE7.sp_reindex_deg]
      exact Work.WilE7.poly_eval_mono_nat bT (hdegSf Sf hSf)
    exact ⟨hTgood, hTfmt, hTdegB, hsubP, hfinAbs, hrank⟩
  · -- the projections agree
    rw [hSLcov]
    apply Set.Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨Sf, hSf, hzSf⟩ := Set.mem_iUnion₂.mp hz
      have hmem : z ∈ Work.WilE7.MainDesign.absPt '' (⋃ T ∈ TLall Sf, T.X.set) := by
        have h2 : z ∈ Work.WilE7.MainDesign.absPt ''
            (Work.WilE7.SemiPf.reindex e Sf.X).set := by
          rw [hAbsReindexOf Sf hSf]
          exact hzSf
        rwa [hcovOf Sf hSf] at h2
      obtain ⟨w, hw, hzw⟩ := hmem
      obtain ⟨T, hT, hwT⟩ := Set.mem_iUnion₂.mp hw
      rw [Set.mem_iUnion₂]
      refine ⟨T, List.mem_flatMap.mpr ⟨Sf, hSf, hT⟩, ?_⟩
      exact ⟨Work.WilE7.MainDesign.absPt w, ⟨w, hwT, rfl⟩, by rw [hzw]⟩
    · intro y hy
      obtain ⟨T, hT, hy⟩ := Set.mem_iUnion₂.mp hy
      obtain ⟨Sf, hSf, hTSf⟩ := List.mem_flatMap.mp hT
      obtain ⟨w, hw, rfl⟩ := hy
      refine ⟨w, ?_, rfl⟩
      rw [Set.mem_iUnion₂]
      exact ⟨Sf, hSf, hsubAbsOf Sf hSf T hTSf hw⟩

end Work.WilE7.CoreStep
