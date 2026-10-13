/-
  Subproject WilE9G — **the deliverable**: `Work.WilE9G.EffStratAE_of_frozen`.

  From the two frozen hypotheses `E2_components` (`hE2`) and `E5_strat` (`hE5`) we prove the
  corrected geometric input `Work.WilE9G.EffStratAE` of area E9.

  For a fixed format bound `F`:

  * `Assembly.exists_ambStrata` turns the frozen `E5_strat` into lists of ambient
    Gabrielov–Vorobjov strata of each basic of `X` (`Assembly.FrozenAux.exists_ambStrata_of_basic`);
  * for every such stratum `T` and every basic `B` we extend the chain of `T` by the chain of `X`
    (`Assembly.ambCatX`) and use the "barrier" weight `Φ_B = ∏_{g ∈ B.pos} g` lifted to that
    chain (`Assembly.FrozenAux.ambCatX_lagStratumAE_*` bound its format and degree);
  * the nondegeneracy direction `c` is chosen outside the finitely many null sets of
    `Assembly.exists_null_of_degenerate_all` and the base-critical values of
    `WilE9G.Sard.exists_null_of_Good_amb` (`Assembly.FrozenAux.exists_null_of_degenerate_stratum`);
  * `Assembly.exists_maximiser` (the barrier argument) plus the local connectivity
    (`Assembly.stratum_fibre_locally_connected`) put the maximiser of `Φ_B·e^{c·(y,t)}` inside `B`
    and on the fibre of `T`, where `Assembly.exists_lagrange_of_localmax` produces the Lagrange
    multipliers and `Assembly.lagStratumAE_mem` the membership in the constructed stratum
    (`Assembly.FrozenCover.cover_step'`);
  * the hitting sets of `hE2` cut the components of the constructed strata, giving the list `L`.

  The bounds are collected in `Assembly.masterPoly`.
-/
import Mathlib
import Submission.Work.WilE9G.Defs
import Submission.Work.WilE9G.Collapse
import Submission.Work.WilE9G.Cover
import Submission.Work.WilE9G.G1
import Submission.Work.WilE9G.Sard.exists_null_of_Good_amb
import Submission.Work.WilE9G.Assembly.Defs
import Submission.Work.WilE9G.Assembly.Step1
import Submission.Work.WilE9G.Assembly.Step2
import Submission.Work.WilE9G.Assembly.Step3
import Submission.Work.WilE9G.Assembly.exists_ambStrata
import Submission.Work.WilE9G.Assembly.exists_null_of_degenerate_all
import Submission.Work.WilE9G.Assembly.lagStratumAE_good
import Submission.Work.WilE9G.Assembly.lagStratumAE_mem
import Submission.Work.WilE9G.Assembly.lagStratumAE_deg_uniform
import Submission.Work.WilE9G.Assembly.ambCatX_props
import Submission.Work.WilE9G.Assembly.masterPoly_bound
import Submission.Work.WilE9G.Assembly.poly_eval_mono
import Submission.Work.WilE9G.Assembly.exists_notMem_of_volume_zero
import Submission.Work.WilE9G.Assembly.FrozenAux
import Submission.Work.WilE9G.Assembly.FrozenCover

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G

open WilkiesDesign WilkiesDesign.E Work.WilE9G.Lagrange
open Work.WilE9G.Assembly

theorem EffStratAE_of_frozen
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set)) :
    Work.WilE9G.EffStratAE := by
  classical
  intro F
  obtain ⟨a5, b5, h5⟩ := Assembly.exists_ambStrata hE5 F
  obtain ⟨p2, hp2⟩ := hE2 (a5 + 2 * F + 2)
  obtain ⟨b4, hb4⟩ := Assembly.lagStratumAE_deg_uniform (a5 + 2 * F + 2)
  refine ⟨a5 + 2 * F + 2, Assembly.masterPoly p2 b4 b5, ?_⟩
  intro n m X z₀ hfmt hz₀
  -- the normalised presentation of `X`
  let X0 : WilkiesDesign.E.SemiPf (n + (1 + m)) := semiPf_normalize X
  have hX0set : X0.set = X.set := semiPf_normalize_set X
  have hX0fmt : X0.fmt = X.fmt := semiPf_normalize_fmt X
  have hX0deg : X0.deg ≤ X.deg := semiPf_normalize_deg_le X
  have hX0len : X0.basics.length ≤ max 1 X.deg := semiPf_normalize_basics_length_le X
  have hz0 : z₀ ∈ X0.set := by rw [hX0set]; exact hz₀
  have hX0fmtF : X0.fmt ≤ F := by rw [hX0fmt]; exact hfmt
  have hnF : n + (1 + m) ≤ F := by
    have h2 : X0.fmt = (n + (1 + m)) + X0.r := rfl
    omega
  have hX0rF : X0.r ≤ F := by
    have h2 : X0.fmt = (n + (1 + m)) + X0.r := rfl
    omega
  by_cases hcub : ∃ B ∈ X0.basics, B.deg = 0
  · -- `X` is the whole cube: the covering clause is vacuous
    have hXset : X.set = cubeC (n + (1 + m)) := by
      rw [← hX0set, SemiPf.set_eq_cubeC_of_deg_zero X0 hcub]
    refine ⟨[], by simp, by simp, ∅, by simp, ?_⟩
    intro y hy _ hfin
    exact absurd hfin (not_finite_fibre_of_set_eq_cubeC hXset z₀ hz₀ y hy)
  · ---------------------------------------------------------------------------------------------
    -- Step 1: the ambient strata of each basic of `X0`
    ---------------------------------------------------------------------------------------------
    choose LB hLBlen hLBgood hLBunion using
      exists_ambStrata_of_basic X0 hX0fmtF a5 b5 h5
    have hBobt : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length),
        (((LB i).get j).X.set ⊆ X0.set) ∧
          (∀ z ∈ ((LB i).get j).X.set, (X0.basics.get i).holds X0.c z) :=
      fun i j => basic_holds_of_union X0 (X0.basics.get i) (List.get_mem X0.basics i)
        (LB i) (hLBunion i) (List.get_mem (LB i) j)
    ---------------------------------------------------------------------------------------------
    -- Step 2: the null sets of the degenerate situations (they do not depend on `c`)
    ---------------------------------------------------------------------------------------------
    have hbpos := fun (i : Fin X0.basics.length) (j : Fin (LB i).length) =>
      ambCatX_good_pos X0 ((LB i).get j) (X0.basics.get i)
        (hLBgood i _ (List.get_mem (LB i) j)).2.2.2.1 (hBobt i j).2
    choose NcF NxF N1F hNcF0 hNxF0 hN1F0 hconclF hN1F using
      fun (i : Fin X0.basics.length) (j : Fin (LB i).length) =>
        exists_null_of_degenerate_stratum (Assembly.ambCatX ((LB i).get j) X0)
          (hbpos i j).1
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r) (X0.basics.get i).pos.prod)
          (hbpos i j).2.1
    ---------------------------------------------------------------------------------------------
    -- Step 3: choose the direction `c` generically
    ---------------------------------------------------------------------------------------------
    let Ncall : Set (Fin (1 + m) → ℝ) :=
      ⋃ p : (Σ i : Fin X0.basics.length, Fin (LB i).length), NcF p.1 p.2
    have hNcall0 : volume Ncall = 0 := by
      show volume (⋃ p : (Σ i : Fin X0.basics.length, Fin (LB i).length), NcF p.1 p.2) = 0
      exact MeasureTheory.measure_iUnion_null (fun p => hNcF0 p.1 p.2)
    obtain ⟨c, hcNcall⟩ : ∃ c : Fin (1 + m) → ℝ, c ∉ Ncall :=
      Assembly.exists_notMem_of_volume_zero (by omega : 0 < 1 + m) Ncall hNcall0
    have hcNcF : ∀ p : (Σ i : Fin X0.basics.length, Fin (LB i).length), c ∉ NcF p.1 p.2 :=
      fun p hp => hcNcall (show c ∈ Ncall from Set.mem_iUnion.mpr ⟨p, hp⟩)
    ---------------------------------------------------------------------------------------------
    -- Step 4: the Lagrange strata and their hitting sets
    ---------------------------------------------------------------------------------------------
    have keyData : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length),
        ∃ (E : Work.WilE9.Sharp.EffStratum n (m + ((LB i).get j).j + 1))
          (s : Finset (Fin (n + (1 + (m + ((LB i).get j).j + 1))) → ℝ)),
          E = Assembly.lagStratumAE (Assembly.ambCatX ((LB i).get j) X0)
                (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r) (X0.basics.get i).pos.prod) c ∧
          s.card ≤ p2.eval E.X.deg ∧ (↑s ⊆ E.X.set) ∧
          (∀ x ∈ E.X.set, ∃ y ∈ s,
            connectedComponentIn E.X.set x = connectedComponentIn E.X.set y) ∧
          E.Good ∧ E.X.fmt ≤ a5 + 2 * F + 2 ∧
          E.deg ≤ (Assembly.masterPoly p2 b4 b5).eval X.deg ∧
          E.X.basics.length ≤ (Assembly.masterPoly p2 b4 b5).eval X.deg := by
      intro i j
      have hTj : ((LB i).get j).j ≤ F :=
        le_trans (Assembly.ambStratum_j_le_ambient _ (hLBgood i _ (List.get_mem (LB i) j)).2.2.2.1
          (hLBgood i _ (List.get_mem (LB i) j)).2.2.2.2) hnF
      have hBdeg : (X0.basics.get i).deg ≤ X0.deg :=
        List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem X0.basics i))
      have hEfmt := ambCatX_lagStratumAE_fmt X0 ((LB i).get j) (X0.basics.get i).pos.prod
        c a5 (hLBgood i _ (List.get_mem (LB i) j)).1 hX0rF hTj
      have hEdeg := ambCatX_lagStratumAE_deg_bound X0 ((LB i).get j) (X0.basics.get i) c
        b4 b5 a5 X.deg (hLBgood i _ (List.get_mem (LB i) j)).2.2.2.1
        (hLBgood i _ (List.get_mem (LB i) j)).2.2.2.2
        (hLBgood i _ (List.get_mem (LB i) j)).2.1
        (hLBgood i _ (List.get_mem (LB i) j)).2.2.1 hBdeg hX0deg
        (hLBgood i _ (List.get_mem (LB i) j)).1 hX0rF
        (fun S Psi c' hj hf => (hb4 n m S Psi c' hj hf).2)
      have hElen := ambCatX_lagStratumAE_len_bound X0 ((LB i).get j) (X0.basics.get i) c
        b5 X.deg p2 b4 (hLBgood i _ (List.get_mem (LB i) j)).2.2.1 hBdeg hX0deg
      have hEgood : (Assembly.lagStratumAE (Assembly.ambCatX ((LB i).get j) X0)
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r) (X0.basics.get i).pos.prod) c).Good :=
        Assembly.lagStratumAE_good (Assembly.ambCatX ((LB i).get j) X0) (hbpos i j).1
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r) (X0.basics.get i).pos.prod) c
      have hEdeg' : (Assembly.lagStratumAE (Assembly.ambCatX ((LB i).get j) X0)
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r) (X0.basics.get i).pos.prod) c).deg
          ≤ (Assembly.masterPoly p2 b4 b5).eval X.deg :=
        hEdeg.trans (le_trans (le_of_eq (Polynomial.eval_comp (p := b4)
            (q := Assembly.combineR b5) (x := X.deg)).symm)
          (Assembly.masterPoly_bound p2 b4 b5 X.deg).2.1)
      obtain ⟨s, hs1, hs2, hs3⟩ := hp2 (n + (1 + (m + ((LB i).get j).j + 1)))
        (Assembly.lagStratumAE (Assembly.ambCatX ((LB i).get j) X0)
          (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r) (X0.basics.get i).pos.prod) c).X hEfmt
      exact ⟨_, s, rfl, hs1, hs2, hs3, hEgood, hEfmt, hEdeg', hElen⟩
    choose Ef sf hEf_eq hsf_card hsf_sub hsf_hit hEf_good hEf_fmt hEf_deg hEf_len using keyData
    ---------------------------------------------------------------------------------------------
    -- Step 5: the base null set and the list `L`
    ---------------------------------------------------------------------------------------------
    let Nall : Set (Fin n → ℝ) :=
      ⋃ p : (Σ i : Fin X0.basics.length, Fin (LB i).length), (NxF p.1 p.2 c ∪ N1F p.1 p.2)
    have hNall0 : volume Nall = 0 := by
      show volume (⋃ p : (Σ i : Fin X0.basics.length, Fin (LB i).length),
        (NxF p.1 p.2 c ∪ N1F p.1 p.2)) = 0
      exact MeasureTheory.measure_iUnion_null (fun p =>
        MeasureTheory.measure_union_null (hNxF0 p.1 p.2 c) (hN1F0 p.1 p.2))
    let Lall : List (Σ m' : ℕ,
        Work.WilE9.Sharp.EffStratum n m' × (Fin (n + (1 + m')) → ℝ)) :=
      (List.finRange X0.basics.length).flatMap (fun i =>
        (List.finRange (LB i).length).flatMap (fun j =>
          (sf i j).toList.map (fun q =>
            (⟨m + ((LB i).get j).j + 1, Ef i j, q⟩ :
              Σ m' : ℕ, Work.WilE9.Sharp.EffStratum n m' × (Fin (n + (1 + m')) → ℝ)))))
    let L : List (Σ m' : ℕ,
        Work.WilE9.Sharp.EffStratum n m' × (Fin (n + (1 + m')) → ℝ)) :=
      Lall.filter (fun t => decide (∀ w ∈ connectedComponentIn t.2.1.X.set t.2.2,
        Work.WilE9.Sharp.stratProj w ∈
          Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀))
    have hLall_mem : ∀ {E : Σ m' : ℕ,
          Work.WilE9.Sharp.EffStratum n m' × (Fin (n + (1 + m')) → ℝ)},
        E ∈ Lall →
        ∃ (i : Fin X0.basics.length) (j : Fin (LB i).length)
          (q : Fin (n + (1 + (m + ((LB i).get j).j + 1))) → ℝ),
          q ∈ sf i j ∧ E = ⟨m + ((LB i).get j).j + 1, Ef i j, q⟩ := by
      intro E hE
      have hE' : E ∈ (List.finRange X0.basics.length).flatMap (fun i =>
        (List.finRange (LB i).length).flatMap (fun j =>
          (sf i j).toList.map (fun q =>
            (⟨m + ((LB i).get j).j + 1, Ef i j, q⟩ :
              Σ m' : ℕ, Work.WilE9.Sharp.EffStratum n m' × (Fin (n + (1 + m')) → ℝ))))) := hE
      obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp hE'
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hi
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hj
      exact ⟨i, j, q, Finset.mem_toList.mp hq, hqe.symm⟩
    refine ⟨L, ?_, ?_, Nall, hNall0, ?_⟩
    ---------------------------------------------------------------------------------------------
    -- Step 6: the length bound
    ---------------------------------------------------------------------------------------------
    · refine le_trans (List.length_filter_le _ _) ?_
      have hP : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length),
          (sf i j).card
            ≤ (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg := by
        intro i j
        refine le_trans (hsf_card i j) ?_
        have h1 : (Ef i j).X.deg ≤ b4.eval ((Assembly.combineR b5).eval X.deg) := by
          rw [hEf_eq i j]
          have hEdeg := ambCatX_lagStratumAE_deg_bound X0 ((LB i).get j)
            (X0.basics.get i) c b4 b5 a5 X.deg
            (hLBgood i _ (List.get_mem (LB i) j)).2.2.2.1
            (hLBgood i _ (List.get_mem (LB i) j)).2.2.2.2
            (hLBgood i _ (List.get_mem (LB i) j)).2.1
            (hLBgood i _ (List.get_mem (LB i) j)).2.2.1
            (List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem X0.basics i))) hX0deg
            (hLBgood i _ (List.get_mem (LB i) j)).1 hX0rF
            (fun S Psi c' hj hf => (hb4 n m S Psi c' hj hf).2)
          exact le_trans (Nat.le_add_right _ _) hEdeg
        calc p2.eval (Ef i j).X.deg
            ≤ p2.eval (b4.eval ((Assembly.combineR b5).eval X.deg)) :=
              Assembly.poly_eval_mono p2 h1
          _ = (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg := by
              simp only [Polynomial.eval_comp]
      have hinner : ∀ i : Fin X0.basics.length,
          ((List.finRange (LB i).length).flatMap (fun j =>
            (sf i j).toList.map (fun q =>
              (⟨m + ((LB i).get j).j + 1, Ef i j, q⟩ :
                Σ m' : ℕ, Work.WilE9.Sharp.EffStratum n m' ×
                  (Fin (n + (1 + m')) → ℝ))))).length
            ≤ b5.eval X0.deg * (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg := by
        intro i
        refine le_trans (length_flatMap_le _ _
          ((p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg) (fun j _ => ?_)) ?_
        · rw [List.length_map, Finset.length_toList]
          exact hP i j
        · rw [List.length_finRange]
          exact Nat.mul_le_mul_right _ (le_trans (hLBlen i) (Assembly.poly_eval_mono b5
            (List.le_sum_of_mem (List.mem_map_of_mem (List.get_mem X0.basics i)))))
      have hLalllen : Lall.length
          ≤ X0.basics.length * (b5.eval X0.deg *
              (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg) := by
        show ((List.finRange X0.basics.length).flatMap (fun i =>
          (List.finRange (LB i).length).flatMap (fun j =>
            (sf i j).toList.map (fun q =>
              (⟨m + ((LB i).get j).j + 1, Ef i j, q⟩ :
                Σ m' : ℕ, Work.WilE9.Sharp.EffStratum n m' ×
                  (Fin (n + (1 + m')) → ℝ)))))).length
          ≤ X0.basics.length * (b5.eval X0.deg *
              (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg)
        refine le_trans (length_flatMap_le _ _
          (b5.eval X0.deg * (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg)
          (fun i _ => hinner i)) ?_
        rw [List.length_finRange]
      have hK : X0.basics.length ≤ X.deg + 1 := by have := hX0len; omega
      have hb5mono : b5.eval X0.deg ≤ b5.eval X.deg := Assembly.poly_eval_mono b5 hX0deg
      have hb5le : b5.eval X0.deg ≤ b5.eval X.deg + 1 := le_trans hb5mono (Nat.le_succ _)
      refine le_trans hLalllen ?_
      calc X0.basics.length * (b5.eval X0.deg *
              (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg)
          ≤ (X.deg + 1) * (b5.eval X0.deg *
              (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg) :=
            Nat.mul_le_mul_right _ hK
        _ ≤ (X.deg + 1) * ((b5.eval X.deg + 1) *
              (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb5le)
        _ = (X.deg + 1) * (b5.eval X.deg + 1) *
              (p2.comp (b4.comp (Assembly.combineR b5))).eval X.deg :=
            (Nat.mul_assoc _ _ _).symm
        _ ≤ (Assembly.masterPoly p2 b4 b5).eval X.deg :=
            (Assembly.masterPoly_bound p2 b4 b5 X.deg).2.2.2.1
    ---------------------------------------------------------------------------------------------
    -- Step 7: the per-element clauses
    ---------------------------------------------------------------------------------------------
    · intro E hE
      have hEall : E ∈ Lall := List.mem_of_mem_filter hE
      have hEpred : ∀ w ∈ connectedComponentIn E.2.1.X.set E.2.2,
          Work.WilE9.Sharp.stratProj w ∈
            Work.WilE9.Sharp.stratProj '' connectedComponentIn X.set z₀ :=
        of_decide_true (List.mem_filter.mp hE).2
      obtain ⟨i, j, q, hq, rfl⟩ := hLall_mem hEall
      exact ⟨hEf_fmt i j, hEf_deg i j, hEf_len i j, hEf_good i j, hsf_sub i j hq, hEpred⟩
    ---------------------------------------------------------------------------------------------
    -- Step 8: the covering
    ---------------------------------------------------------------------------------------------
    · intro y hy hyN hfin
      have hxall : ∀ p : (Σ i : Fin X0.basics.length, Fin (LB i).length),
          Fin.init y ∉ (NxF p.1 p.2 c ∪ N1F p.1 p.2) := by
        intro p hp
        exact hyN (show Fin.init y ∈ Nall from Set.mem_iUnion.mpr ⟨p, hp⟩)
      have hsubN : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length)
          (z : Fin (n + (1 + m)) → ℝ), z ∈ (ambCatX ((LB i).get j) X0).X.set →
          projBase (Nat.le_add_right n (1 + m)) z = Fin.init y →
          (ambCatX ((LB i).get j) X0).IsBaseSubmersiveAt (Nat.le_add_right n (1 + m)) z := by
        intro i j z hz hzb
        by_contra hnot
        exact (hxall ⟨i, j⟩) (Or.inr (by
          have h := hN1F i j z hz hnot
          rwa [hzb] at h))
      have hndN : ∀ (i : Fin X0.basics.length) (j : Fin (LB i).length)
          (z : Fin (n + (1 + m)) → ℝ), z ∈ (ambCatX ((LB i).get j) X0).X.set →
          projBase (Nat.le_add_right n (1 + m)) z = Fin.init y →
          ∀ (mu : Fin ((LB i).get j).j → ℝ) (mu0 : ℝ),
            LagEq (ambCatX ((LB i).get j) X0)
              (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r)
                (X0.basics.get i).pos.prod) c z mu mu0 →
            LagNorm mu mu0 →
            (lagJac (ambCatX ((LB i).get j) X0)
              (Work.WilE7.EAPoly.inr (r₁ := ((LB i).get j).X.r)
                (X0.basics.get i).pos.prod) c z mu mu0).det ≠ 0 := by
        intro i j z hz hzb mu mu0 hEqx hNx
        exact hconclF i j c (hcNcF ⟨i, j⟩) (Fin.init y)
          (fun h => (hxall ⟨i, j⟩) (Or.inl h)) z hz hzb mu mu0 hEqx hNx
      obtain ⟨i', j', q, hq, hyq, hqpred⟩ := cover_step' X X0 z₀ hX0set hz0 y hy hfin LB
        hLBunion (fun i S hS => (hLBgood i S hS).2.2.2.1) c Ef hEf_eq sf hsf_sub hsf_hit hsubN hndN
      have hE_in : (⟨m + ((LB i').get j').j + 1, Ef i' j', q⟩ : Σ m' : ℕ,
          Work.WilE9.Sharp.EffStratum n m' × (Fin (n + (1 + m')) → ℝ)) ∈ L := by
        refine List.mem_filter.mpr ⟨?_, ?_⟩
        · show (⟨m + ((LB i').get j').j + 1, Ef i' j', q⟩ : Σ m' : ℕ,
              Work.WilE9.Sharp.EffStratum n m' × (Fin (n + (1 + m')) → ℝ)) ∈
            (List.finRange X0.basics.length).flatMap (fun i =>
              (List.finRange (LB i).length).flatMap (fun j =>
                (sf i j).toList.map (fun q =>
                  (⟨m + ((LB i).get j).j + 1, Ef i j, q⟩ :
                    Σ m' : ℕ, Work.WilE9.Sharp.EffStratum n m' ×
                      (Fin (n + (1 + m')) → ℝ)))))
          exact List.mem_flatMap.mpr ⟨i', List.mem_finRange i',
            List.mem_flatMap.mpr ⟨j', List.mem_finRange j',
              List.mem_map.mpr ⟨q, Finset.mem_toList.mpr hq, rfl⟩⟩⟩
        · exact decide_true_of hqpred
      exact Set.mem_iUnion₂.mpr ⟨⟨m + ((LB i').get j').j + 1, Ef i' j', q⟩, hE_in, hyq⟩

end Work.WilE9G
