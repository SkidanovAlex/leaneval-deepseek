import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.Endgame.gcase_strata_uniform
import Submission.Work.WilE7.coreLT_succ.gcase_strata
import Submission.Work.WilE7.coreLT_succ.Classification

namespace Work.WilE7.Endgame

set_option autoImplicit false
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-- If `L'` consists of members of `L` together with strata of empty set, the unions of the sets
of the two lists agree.  (The case at hand is `L' = L.filter (fun S => S.X.set.Nonempty)`.) -/
theorem iUnion_eq_of_mem_or_empty {N : ℕ} {L L' : List (Stratum 0 N)}
    (hmem : ∀ S ∈ L', S ∈ L) (hempty : ∀ S ∈ L, S ∉ L' → S.X.set = ∅) :
    ⋃ S ∈ L, S.X.set = ⋃ S ∈ L', S.X.set := by
  apply le_antisymm
  · intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨S, hS, hz⟩ := hz
    by_cases hS' : S ∈ L'
    · exact Set.mem_biUnion hS' hz
    · rw [hempty S hS hS'] at hz
      exact (Set.notMem_empty z hz).elim
  · intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨S, hS, hz⟩ := hz
    exact Set.mem_biUnion (hmem S hS) hz

theorem E2_rank_strata (hE5 : HypE5) (F : ℕ) :
    ∃ (A : ℕ) (P : Polynomial ℕ),
      ∀ (D K n m : ℕ) (Pie : List (Stratum 0 (n + (m + 1)))),
        (∀ T ∈ Pie, T.Good) → (∀ T ∈ Pie, T.X.fmt ≤ F) → (∀ T ∈ Pie, T.deg ≤ D) →
        (∀ T ∈ Pie, ∀ z ∈ T.X.set, projRank T z ≤ K) →
        ∃ (Ld : (Fin Pie.length) → List (Stratum 0 (n + (m + 1))))
          (SloR : (Fin Pie.length) → Fin K → SemiPf (n + (m + 1))),
          (∀ p : Fin Pie.length, (Ld p).length ≤ P.eval D ∧
            (∀ S ∈ Ld p, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ A ∧ S.deg ≤ P.eval D ∧
              n + (m + 1) - S.j ≤ K ∧
              (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
              S.X.set ⊆ (Pie.get p).X.set ∧
              S.X.set ⊆ {z | projRank (Pie.get p) z = n + (m + 1) - (Pie.get p).j})) ∧
          (∀ p : Fin Pie.length,
            {z | z ∈ (Pie.get p).X.set ∧ projRank (Pie.get p) z = n + (m + 1) - (Pie.get p).j}
              = ⋃ S ∈ Ld p, S.X.set) ∧
          (∀ (p : Fin Pie.length) (r : Fin K), (SloR p r).fmt ≤ A ∧ (SloR p r).deg ≤ P.eval D ∧
            (SloR p r).set = absPt '' {z | z ∈ (Pie.get p).X.set ∧
              projRank (Pie.get p) z = (r : ℕ)} ∧
            NullDimLT (projFirst n (m + 1) '' (SloR p r).set) K) := by
  classical
  -- The two producers, with bounds uniform in everything but `F`.
  obtain ⟨Ag, Bg, hGc⟩ := gcase_strata_uniform hE5 F
  obtain ⟨Ar, Br, hRs⟩ := Work.WilE7.coreLT_succ.rankSlice_sigmaLow_data F
  refine ⟨max Ag Ar, Bg + Br, ?_⟩
  intro D K n m Pie hGood hFmt hDeg hRank
  -- The rank-full strata of each piece, with the empty ones removed.
  have hex : ∀ p : Fin Pie.length, ∃ L : List (Stratum 0 (n + (m + 1))),
      (L.length ≤ (Bg + Br).eval D ∧
        (∀ S ∈ L, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ max Ag Ar ∧
          S.deg ≤ (Bg + Br).eval D ∧ n + (m + 1) - S.j ≤ K ∧
          (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
          S.X.set ⊆ (Pie.get p).X.set ∧
          S.X.set ⊆ {z | projRank (Pie.get p) z = n + (m + 1) - (Pie.get p).j})) ∧
      ({z | z ∈ (Pie.get p).X.set ∧ projRank (Pie.get p) z = n + (m + 1) - (Pie.get p).j}
        = ⋃ S ∈ L, S.X.set) := by
    intro p
    have hTgood : (Pie.get p).Good := hGood _ (Pie.get_mem p)
    have hTfmt : (Pie.get p).X.fmt ≤ F := hFmt _ (Pie.get_mem p)
    have hTdeg : (Pie.get p).deg ≤ D := hDeg _ (Pie.get_mem p)
    obtain ⟨L₀, hg₁, hg₂, hg₃, hg₄, hg₅, hg₆⟩ :=
      hGc n m D (Pie.get p) hTgood hTfmt hTdeg
    have hdegn : Bg.eval D ≤ (Bg + Br).eval D := by
      rw [Polynomial.eval_add]; exact Nat.le_add_right _ _
    refine ⟨L₀.filter (fun S => S.X.set.Nonempty), ⟨?_, ?_⟩, ?_⟩
    · -- length
      calc (L₀.filter (fun S => S.X.set.Nonempty)).length ≤ L₀.length :=
            List.length_filter_le _ _
        _ ≤ Bg.eval D := hg₃
        _ ≤ (Bg + Br).eval D := hdegn
    · -- the properties of the members
      intro S hS
      have hS₀ : S ∈ L₀ := List.mem_of_mem_filter hS
      have hSne : S.X.set.Nonempty := decide_eq_true_iff.mp (List.mem_filter.mp hS).2
      have hSG : S.Good := hg₁ S hS₀
      have hSfmt : S.X.fmt ≤ Ag := (hg₂ S hS₀).1
      have hSdeg : S.deg ≤ Bg.eval D := (hg₂ S hS₀).2
      have hSloc : S.X.set ⊆ {z | z ∈ (Pie.get p).X.set ∧
          projRank (Pie.get p) z = n + (m + 1) - (Pie.get p).j} := hg₄ S hS₀
      have hSrank : ∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j := hg₅ S hS₀
      have hsub : S.X.set ⊆ (Pie.get p).X.set := fun x hx => (hSloc hx).1
      obtain ⟨z, hz⟩ := hSne
      have hzT : z ∈ (Pie.get p).X.set := (hSloc hz).1
      -- the equation count of `S` is at least that of the piece
      have hjle : (Pie.get p).j ≤ S.j :=
        Work.WilE7.coreLT_succ.j_le_of_sub S (Pie.get p) hSG hTgood hsub hz
      have hTK : n + (m + 1) - (Pie.get p).j ≤ K := by
        have h1 : projRank (Pie.get p) z = n + (m + 1) - (Pie.get p).j := (hSloc hz).2
        have h2 : projRank (Pie.get p) z ≤ K := hRank _ (Pie.get_mem p) z hzT
        omega
      refine ⟨hSG, ⟨z, hz⟩, le_trans hSfmt (le_max_left _ _), ?_, ?_, hSrank, hsub,
        fun x hx => (hSloc hx).2⟩
      · calc S.deg ≤ Bg.eval D := hSdeg
          _ ≤ (Bg + Br).eval D := hdegn
      · exact le_trans (Nat.sub_le_sub_left hjle (n + (m + 1))) hTK
    · -- the covering, unchanged by the removal of the empty members
      rw [hg₆]
      exact iUnion_eq_of_mem_or_empty (L := L₀)
        (L' := L₀.filter (fun S => S.X.set.Nonempty))
        (fun S hS => List.mem_of_mem_filter hS)
        (fun S hS₀ hS' => by
          have hne : ¬ S.X.set.Nonempty := fun hne =>
            hS' (List.mem_filter.mpr ⟨hS₀, by rw [decide_eq_true_iff]; exact hne⟩)
          exact Set.not_nonempty_iff_eq_empty.mp hne)
  choose Ld hLd using hex
  -- The rank-`r` slices of each piece.
  have hSlo : ∀ p : Fin Pie.length, ∀ r : Fin K, ∃ Y : SemiPf (n + (m + 1)),
      Y.fmt ≤ max Ag Ar ∧ Y.deg ≤ (Bg + Br).eval D ∧
      Y.set = absPt '' {z | z ∈ (Pie.get p).X.set ∧
        projRank (Pie.get p) z = (r : ℕ)} ∧
      NullDimLT (projFirst n (m + 1) '' Y.set) K := by
    intro p r
    have hTgood : (Pie.get p).Good := hGood _ (Pie.get_mem p)
    have hTfmt : (Pie.get p).X.fmt ≤ F := hFmt _ (Pie.get_mem p)
    have hTdeg : (Pie.get p).deg ≤ D := hDeg _ (Pie.get_mem p)
    have hr : (r : ℕ) + 1 ≤ K := by
      have := r.isLt
      omega
    obtain ⟨Y, hYset, hYfmt, hYdeg, hYnull⟩ :=
      hRs n m (r : ℕ) K (Pie.get p) hTgood hTfmt hr
    refine ⟨Y, le_trans hYfmt (le_max_right _ _), ?_, hYset, hYnull⟩
    calc Y.deg ≤ Br.eval (Pie.get p).deg := hYdeg
      _ ≤ Br.eval D := Work.WilE7.coreLT_succ.eval_mono_nat Br hTdeg
      _ ≤ (Bg + Br).eval D := by
          rw [Polynomial.eval_add]; exact Nat.le_add_left _ _
  choose SloR hSloSpec using hSlo
  exact ⟨Ld, SloR, fun p => ⟨(hLd p).1.1, (hLd p).1.2⟩, fun p => (hLd p).2,
    fun p r => hSloSpec p r⟩

end Work.WilE7.Endgame
