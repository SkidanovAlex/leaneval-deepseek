import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.Endgame.rankLeSlice_projRank
import Submission.Work.WilE7.Endgame.gcase_strata_uniform
import Submission.Work.WilE7.yFamily_withCutters
import Submission.Work.WilE7.coreLT_succ.RankBounds
import Submission.Work.WilE7.coreLT_succ.SubStratum
import Submission.Work.WilE7.coreLT_succ.Classification
import Submission.Work.CoreStep.SigmaFamDefs
import Submission.Work.WilE7.DimAPI.nullDimLT_basics
import Submission.Work.WilE7.Endgame.sigmaFamily_len_unif_helpers

namespace Work.WilE7.Endgame

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)

/-! ## 0. Elementary helpers for the re-stratification

The endgame node `frontier_restrat` splits the frontier of a `Good` absolute stratum `T` into

* graph-like pieces, on which the base projection `π_n` has rank equal to the dimension
  (`gcase_strata_uniform`), and
* "low-rank" pieces, whose `π_n`-projection has dimension `< K`
  (`rankLeSlice_nullDim`, `rankLeSlice_lowPiece` below).

Everything is measured against the bound `K` of the interface, not against the dimension of the
individual frontier stratum, so that the counting stays uniform in `K`.
-/

/-- The empty semi-Pfaffian set. -/
def emptySemiPf (k : ℕ) : SemiPf k := ⟨0, EAChain.nil k, []⟩

theorem emptySemiPf_set (k : ℕ) : (emptySemiPf k).set = ∅ := by
  ext x
  constructor
  · rintro ⟨-, B, hB, -⟩
    exact absurd hB (List.not_mem_nil)
  · rintro h
    exact absurd h (by simp)

@[simp] theorem emptySemiPf_fmt (k : ℕ) : (emptySemiPf k).fmt = k := rfl

@[simp] theorem emptySemiPf_deg (k : ℕ) : (emptySemiPf k).deg = 0 := rfl

/-- Elementary bound: for `m ≥ max a b c + 1` the polynomial `(D+1) * m * m` dominates `a`, `b`,
`c` and `a * b`.  This is the degree bookkeeping of the two lists of `FrontierRestrat`. -/
theorem poly_arith {a b c D : ℕ} :
    a * b ≤ (D + 1) * (a + b + c + 1) * (a + b + c + 1) ∧
    a ≤ (D + 1) * (a + b + c + 1) * (a + b + c + 1) ∧
    b ≤ (D + 1) * (a + b + c + 1) * (a + b + c + 1) ∧
    c ≤ (D + 1) * (a + b + c + 1) * (a + b + c + 1) := by
  set m : ℕ := a + b + c + 1 with hm
  have hm1 : 1 ≤ m := by omega
  have hD1 : 1 ≤ D + 1 := by omega
  have ha : a ≤ m := by omega
  have hb : b ≤ m := by omega
  have hc : c ≤ m := by omega
  have hmm : m ≤ (D + 1) * m * m := by
    calc m ≤ (D + 1) * m := Nat.le_mul_of_pos_left m (by omega)
      _ ≤ (D + 1) * m * m := Nat.le_mul_of_pos_right _ hm1
  have hab : a * b ≤ (D + 1) * m * m := by
    calc a * b ≤ m * m := Nat.mul_le_mul ha hb
      _ = 1 * (m * m) := by ring
      _ ≤ (D + 1) * (m * m) := Nat.mul_le_mul_right _ hD1
      _ = (D + 1) * m * m := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm]; exact hab
  · rw [hm]; exact le_trans ha hmm
  · rw [hm]; exact le_trans hb hmm
  · rw [hm]; exact le_trans hc hmm

/-! ## 1. The low-rank locus of a `Good` stratum, with the `NullDimLT` bound -/

/-- **The rank-`≤ r` locus in the ambient space.**  Combining `rankLeSlice_projRank` with the
`absPt`-reindexing (`absSlice`) and the Sard node `rankLocus_nullDimLE` (which bounds the measure
of the base projection of the rank-`≤ r` locus by `r`) gives, for `r + 1 ≤ K`, a `SemiPf` set of
format `≤ A` and degree `≤ B.eval S.deg` whose base projection has dimension `< K`. -/
theorem rankLeSlice_nullDim (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m r K : ℕ) (S : Stratum 0 (n + m)), S.Good → S.X.fmt ≤ F → r + 1 ≤ K →
        ∃ Y : SemiPf (n + m),
          Y.set = absPt '' {z | z ∈ S.X.set ∧ projRank S z ≤ r} ∧
          Y.fmt ≤ A ∧ Y.deg ≤ B.eval S.deg ∧
          NullDimLT (projFirst n m '' Y.set) K := by
  obtain ⟨A, B, h⟩ := rankLeSlice_projRank F
  refine ⟨A, B, ?_⟩
  intro n m r K S hS hSf hK
  obtain ⟨Y₀, hY₀set, hY₀fmt, hY₀deg⟩ := h n m r S hS hSf
  refine ⟨Work.WilE7.coreLT_succ.absSlice Y₀, ?_, ?_, ?_, ?_⟩
  · rw [Work.WilE7.coreLT_succ.absSlice_set, hY₀set]
  · rw [Work.WilE7.coreLT_succ.absSlice_fmt]
    have hfmt : Y₀.fmt = n + m + Y₀.r := by simp only [SemiPf.fmt, Nat.zero_add]
    rw [← hfmt]
    exact hY₀fmt
  · rw [Work.WilE7.coreLT_succ.absSlice_deg]
    exact hY₀deg
  · rw [Work.WilE7.coreLT_succ.absSlice_set, hY₀set]
    cases K with
    | zero => omega
    | succ K' =>
        refine Work.WilE7.DimAPI.nullDimLE_mono_dim
          (Work.WilE7.DimAPI.rankLocus_nullDimLE S hS r) ?_
        omega

/-- **The low-rank piece of a `Good` stratum.**  With `dS = n + m - S.j` and
`dS ≤ K` (the hypothesis is vacuous when `S.X.set = ∅`), there is a `SemiPf` set `Y` containing
the image of the locus `{projRank S < dS}` (the complement of the full-rank locus of `S` inside
`S`), of format `≤ A` and degree `≤ B.eval S.deg`, whose base projection has dimension `< K`.

The two degenerate situations are absorbed here once and for all: if `S.X.set = ∅` or `K = 0`
the low-rank locus is empty and the empty semi-Pfaffian set is used. -/
theorem rankLeSlice_lowPiece (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m K : ℕ) (S : Stratum 0 (n + m)), S.Good → S.X.fmt ≤ F →
        (S.X.set.Nonempty → n + m - S.j ≤ K) →
        ∃ Y : SemiPf (n + m),
          Y.fmt ≤ A ∧ Y.deg ≤ B.eval S.deg ∧
          NullDimLT (projFirst n m '' Y.set) K ∧
          absPt '' {z | z ∈ S.X.set ∧ projRank S z < n + m - S.j} ⊆ Y.set := by
  obtain ⟨A₁, B₁, h₁⟩ := rankLeSlice_nullDim F
  refine ⟨max F A₁, B₁, ?_⟩
  intro n m K S hS hSf hdK
  have hNF : n + m ≤ F := by
    have h := hSf
    simp only [SemiPf.fmt] at h
    omega
  by_cases hne : S.X.set.Nonempty
  · by_cases hK : K = 0
    · subst hK
      have hdS : n + m - S.j ≤ 0 := hdK hne
      refine ⟨emptySemiPf (n + m), ?_, ?_, ?_, ?_⟩
      · rw [emptySemiPf_fmt]; exact le_trans hNF (le_max_left _ _)
      · rw [emptySemiPf_deg]; exact Nat.zero_le _
      · rw [emptySemiPf_set]; simp
      · intro z hz
        obtain ⟨w, hw, -⟩ := hz
        have hwlt : projRank S w < n + m - S.j := hw.2
        rw [emptySemiPf_set]
        exact absurd hwlt (by omega)
    · have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
      have hdS : n + m - S.j ≤ K := hdK hne
      obtain ⟨Y, hYset, hYfmt, hYdeg, hYnull⟩ := h₁ n m (K - 1) K S hS hSf (by omega)
      refine ⟨Y, le_trans hYfmt (le_max_right _ _), hYdeg, hYnull, ?_⟩
      intro z hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hwlt : projRank S w < n + m - S.j := hw.2
      have hwmem : w ∈ S.X.set := hw.1
      rw [hYset]
      exact ⟨w, ⟨hwmem, by omega⟩, rfl⟩
  · have hempty : S.X.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨emptySemiPf (n + m), ?_, ?_, ?_, ?_⟩
    · rw [emptySemiPf_fmt]; exact le_trans hNF (le_max_left _ _)
    · rw [emptySemiPf_deg]; exact Nat.zero_le _
    · rw [emptySemiPf_set]; simp
    · rw [hempty]; simp

/-! ## 2. The endgame node -/

theorem frontier_restrat (hE5 : HypE5) (hE6 : HypE6) : FrontierRestrat := by
  classical
  intro F
  -- the uniform frontier family (`E5` + `E6`), the full-rank split of a stratum, the low pieces
  obtain ⟨A₀, B₀, hFam⟩ := Work.WilE7.frontierFamily_uniform hE5 hE6 F
  obtain ⟨Ag, Bg, hGc⟩ := gcase_strata_uniform hE5 A₀
  obtain ⟨As, Bs, hLow⟩ := rankLeSlice_lowPiece A₀
  set M : Polynomial ℕ := B₀ + Bg.comp B₀ + Bs.comp B₀ + 1 with hMdef
  refine ⟨max A₀ (max Ag As), (Polynomial.X + 1) * M * M, ?_⟩
  intro n m K D T hTgood hTfmt hTdeg hdimT
  obtain ⟨L, hLgood, hLprops, hLsub, hLcov, hLlen⟩ := hFam n m D T hTgood hTfmt hTdeg
  -- the degree bookkeeping
  have hMev : M.eval D = B₀.eval D + Bg.eval (B₀.eval D) + Bs.eval (B₀.eval D) + 1 := by
    rw [hMdef]
    simp [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_comp]
  have hBev : ((Polynomial.X + 1) * M * M).eval D = (D + 1) * M.eval D * M.eval D := by
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have harith := poly_arith (a := B₀.eval D) (b := Bg.eval (B₀.eval D))
    (c := Bs.eval (B₀.eval D)) (D := D)
  have hle_ab : B₀.eval D * Bg.eval (B₀.eval D) ≤ ((Polynomial.X + 1) * M * M).eval D := by
    rw [hBev, hMev]; exact harith.1
  have hle_a : B₀.eval D ≤ ((Polynomial.X + 1) * M * M).eval D := by
    rw [hBev, hMev]; exact harith.2.1
  have hle_b : Bg.eval (B₀.eval D) ≤ ((Polynomial.X + 1) * M * M).eval D := by
    rw [hBev, hMev]; exact harith.2.2.1
  have hle_c : Bs.eval (B₀.eval D) ≤ ((Polynomial.X + 1) * M * M).eval D := by
    rw [hBev, hMev]; exact harith.2.2.2
  have hAgA : Ag ≤ max A₀ (max Ag As) :=
    le_trans (le_max_left Ag As) (le_max_right A₀ (max Ag As))
  have hAsA : As ≤ max A₀ (max Ag As) :=
    le_trans (le_max_right Ag As) (le_max_right A₀ (max Ag As))
  -- per-stratum data: the full-rank pieces and the low pieces
  have hLdEx : ∀ p : {S : Stratum 0 (n + (m + 1)) // S ∈ L},
      ∃ Ld : List (Stratum 0 (n + (m + 1))),
        (∀ S' ∈ Ld, S'.Good) ∧
        (∀ S' ∈ Ld, S'.X.fmt ≤ Ag ∧ S'.deg ≤ Bg.eval (B₀.eval D)) ∧
        Ld.length ≤ Bg.eval (B₀.eval D) ∧
        (∀ S' ∈ Ld, S'.X.set ⊆ {z | z ∈ p.1.X.set ∧
          projRank p.1 z = n + (m + 1) - p.1.j}) ∧
        (∀ S' ∈ Ld, ∀ z ∈ S'.X.set, projRank S' z = n + (m + 1) - S'.j) ∧
        {z | z ∈ p.1.X.set ∧ projRank p.1 z = n + (m + 1) - p.1.j} = ⋃ S' ∈ Ld, S'.X.set := by
    intro p
    exact hGc n m (B₀.eval D) p.1 (hLgood p.1 p.2) (hLprops p.1 p.2).1 (hLprops p.1 p.2).2
  have hYEx : ∀ p : {S : Stratum 0 (n + (m + 1)) // S ∈ L},
      ∃ Y : SemiPf (n + (m + 1)),
        Y.fmt ≤ As ∧ Y.deg ≤ Bs.eval (B₀.eval D) ∧
        NullDimLT (projFirst n (m + 1) '' Y.set) K ∧
        absPt '' {z | z ∈ p.1.X.set ∧ projRank p.1 z < n + (m + 1) - p.1.j} ⊆ Y.set := by
    intro p
    have hdK' : p.1.X.set.Nonempty → n + (m + 1) - p.1.j ≤ K := by
      intro hne
      have h1 : T.j < p.1.j :=
        frontierDrop_abs T p.1 hTgood (hLgood p.1 p.2) (hLsub p.1 p.2) hne
      omega
    obtain ⟨Y, hYfmt, hYdeg, hYnull, hYsub⟩ :=
      hLow n (m + 1) K p.1 (hLgood p.1 p.2) (hLprops p.1 p.2).1 hdK'
    exact ⟨Y, hYfmt,
      le_trans hYdeg (Work.WilE7.coreLT_succ.eval_mono_nat Bs (hLprops p.1 p.2).2),
      hYnull, hYsub⟩
  choose Ld hLdSpec using hLdEx
  choose Yf hYfSpec using hYEx
  let Lg : List (Stratum 0 (n + (m + 1))) :=
    (L.attach.flatMap Ld).filter (fun S' => decide (S'.X.set.Nonempty))
  let Ly : List (SemiPf (n + (m + 1))) := L.attach.map Yf
  have hLgmem : ∀ p ∈ L.attach, ∀ S' ∈ Ld p, S' ∈ Lg ↔ S'.X.set.Nonempty := by
    intro p hp S' hS'
    constructor
    · intro h
      have h2 := (List.mem_filter.mp h).2
      simpa using h2
    · intro h
      exact List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨p, hp, hS'⟩, by simpa using h⟩
  refine ⟨Lg, Ly, ?_, ?_, ?_, ?_, ?_⟩
  · -- length of `Lg`
    have h1 : (L.attach.flatMap Ld).length ≤ L.length * Bg.eval (B₀.eval D) := by
      have h := length_flatMap_le L.attach Ld (Bg.eval (B₀.eval D))
        (fun p _ => (hLdSpec p).2.2.1)
      rwa [List.length_attach] at h
    have h2 : Lg.length ≤ (L.attach.flatMap Ld).length := by
      simpa only [Lg] using
        List.length_filter_le (fun S' : Stratum 0 (n + (m + 1)) => decide (S'.X.set.Nonempty))
          (L.attach.flatMap Ld)
    have h3 : L.length * Bg.eval (B₀.eval D) ≤ B₀.eval D * Bg.eval (B₀.eval D) :=
      Nat.mul_le_mul_right _ hLlen
    exact le_trans (le_trans h2 h1) (le_trans h3 hle_ab)
  · -- length of `Ly`
    have h1 : Ly.length = L.length := by
      simp only [Ly, List.length_map, List.length_attach]
    exact le_trans (le_of_eq h1) (le_trans hLlen hle_a)
  · -- the `Lg` clauses
    intro S' hS'Lg
    obtain ⟨hS'mem, hS'ne'⟩ := List.mem_filter.mp hS'Lg
    obtain ⟨q, hq, hS'Ld⟩ := List.mem_flatMap.mp hS'mem
    have hqne : S'.X.set.Nonempty := by simpa using hS'ne'
    obtain ⟨hqgood, hqbnd, hqlen, hqsub, hqrank, hqcov⟩ := hLdSpec q
    have hS'good : S'.Good := hqgood S' hS'Ld
    refine ⟨hS'good, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (hqbnd S' hS'Ld).1 hAgA
    · exact le_trans (hqbnd S' hS'Ld).2 hle_b
    · -- containment in the frontier of `T`
      exact fun y hy => hLsub q.1 q.2 ((hqsub S' hS'Ld hy).1)
    · -- the dimension bound
      obtain ⟨z, hz⟩ := hqne
      have hsub1 : S'.X.set ⊆ q.1.X.set := fun y hy => (hqsub S' hS'Ld hy).1
      have h1 : q.1.j ≤ S'.j :=
        Work.WilE7.coreLT_succ.j_le_of_sub S' q.1 hS'good (hLgood q.1 q.2) hsub1 hz
      have h2 : T.j < q.1.j :=
        frontierDrop_abs T q.1 hTgood (hLgood q.1 q.2) (hLsub q.1 q.2) ⟨z, hsub1 hz⟩
      omega
    · exact hqrank S' hS'Ld
  · -- the `Ly` clauses
    intro Y hY
    obtain ⟨q, hq, hYeq⟩ := List.mem_map.mp hY
    rw [← hYeq]
    obtain ⟨hYfmt, hYdeg, hYnull, -⟩ := hYfSpec q
    exact ⟨le_trans hYfmt hAsA, le_trans hYdeg hle_c, hYnull⟩
  · -- the covering
    rw [Work.CoreStep.frontier_absSet]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw1 : w ∈ ⋃ S ∈ L, S.X.set := hLcov ⟨hw.1, hw.2⟩
    obtain ⟨S, hSL, hwS⟩ := Set.mem_iUnion₂.mp hw1
    let p₀ : {S : Stratum 0 (n + (m + 1)) // S ∈ L} := ⟨S, hSL⟩
    have hp₀ : p₀ ∈ L.attach := List.mem_attach _ _
    have hqprops := hLdSpec p₀
    obtain ⟨hqgood, hqbnd, hqlen, hqsub, hqrank, hqcov⟩ := hqprops
    have hSgood : S.Good := hLgood S hSL
    have hcover : absSet S ⊆ (⋃ S' ∈ Ld p₀, absSet S') ∪ (Yf p₀).set := by
      intro y hy
      rw [Work.CoreStep.absSet_eq_image] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      by_cases hfr : projRank S u = n + (m + 1) - S.j
      · left
        have hu' : u ∈ ⋃ S' ∈ Ld p₀, S'.X.set := by
          rw [← hqcov]
          exact ⟨hu, hfr⟩
        obtain ⟨S', hS'mem, huS'⟩ := Set.mem_iUnion₂.mp hu'
        exact Set.mem_iUnion₂.mpr ⟨S', hS'mem, ⟨u, huS', rfl⟩⟩
      · right
        have hbad : projRank S u < n + (m + 1) - S.j :=
          lt_of_le_of_ne (Work.WilE7.coreLT_succ.projRank_le_dim S hSgood hu) hfr
        exact (hYfSpec p₀).2.2.2 ⟨u, ⟨hu, hbad⟩, rfl⟩
    have hmem : absPt w ∈ (⋃ S' ∈ Lg, absSet S') ∪ ⋃ Y ∈ Ly, Y.set := by
      rcases hcover ⟨w, hwS, rfl⟩ with h | h
      · left
        obtain ⟨S', hS'mem, hy⟩ := Set.mem_iUnion₂.mp h
        rw [Work.CoreStep.absSet_eq_image] at hy
        obtain ⟨u, hu, hEq⟩ := hy
        have hwit : u = w := Work.CoreStep.absPt_injective (n + (m + 1)) hEq
        exact Set.mem_iUnion₂.mpr ⟨S',
          (hLgmem p₀ hp₀ S' hS'mem).mpr ⟨u, hwit ▸ hu⟩, ⟨w, hwit ▸ hu, rfl⟩⟩
      · right
        exact Set.mem_iUnion₂.mpr ⟨Yf p₀, List.mem_map.mpr ⟨p₀, hp₀, rfl⟩, h⟩
    exact hmem

end

end Work.WilE7.Endgame
