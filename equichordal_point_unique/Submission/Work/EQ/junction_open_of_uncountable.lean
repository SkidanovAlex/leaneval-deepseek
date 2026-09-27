import Mathlib
import Submission.Work.EQ.junction_values_countable_ns
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.exists_accPt_principal_of_uncountable
import Submission.Work.EQ.junc_common_pieces
import Submission.Work.EQ.CycleDefs

namespace Work.EQ

open Complex Filter _root_.Topology Metric

open scoped Topology

noncomputable section

/-- Identity theorem, packaged for the junction argument: two families analytic on a ball that
agree on a set accumulating at the centre of the ball agree on the whole ball. -/
lemma junc_eqOn_ball_of_accPt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (Metric.ball x ρ)) (hg : AnalyticOnNhd ℂ g (Metric.ball x ρ))
    {S : Set ℂ} (hacc : AccPt x (Filter.principal S)) (heq : ∀ z ∈ S, f z = g z) :
    Set.EqOn f g (Metric.ball x ρ) := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hf hg
    Metric.isPreconnected_ball (Metric.mem_ball_self hρ) ?_
  rw [accPt_iff_frequently] at hacc
  rw [frequently_nhdsWithin_iff]
  exact hacc.mono (fun z hz => ⟨heq z hz.2, hz.1⟩)

/-- The identity theorem for the polynomial equichordal relation `EqRelC`. -/
lemma junc_eqRelC_on_ball_of_accPt {a : ℝ} {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {P Q : ℂ → ℂ × ℂ}
    (hP : AnalyticOnNhd ℂ P (Metric.ball x ρ)) (hQ : AnalyticOnNhd ℂ Q (Metric.ball x ρ))
    {S : Set ℂ} (hacc : AccPt x (Filter.principal S))
    (hrel : ∀ z ∈ S, EqRelC a (P z) (Q z)) :
    ∀ z ∈ Metric.ball x ρ, EqRelC a (P z) (Q z) := by
  set F : ℂ → ℂ × ℂ := fun z =>
    (((Q z).1 + (P z).1) ^ 2 + ((Q z).2 + (P z).2) ^ 2 - 1,
      ((Q z).1 + (P z).1) * (P z).2 - ((Q z).2 + (P z).2) * ((P z).1 - ((a / 2 : ℝ) : ℂ)))
    with hFdef
  have hFana : AnalyticOnNhd ℂ F (Metric.ball x ρ) := by
    intro z hz
    rw [hFdef]
    have hP1 : AnalyticAt ℂ (fun z => (P z).1) z := (analyticAt_fst (p := P z)).comp (hP z hz)
    have hP2 : AnalyticAt ℂ (fun z => (P z).2) z := (analyticAt_snd (p := P z)).comp (hP z hz)
    have hQ1 : AnalyticAt ℂ (fun z => (Q z).1) z := (analyticAt_fst (p := Q z)).comp (hQ z hz)
    have hQ2 : AnalyticAt ℂ (fun z => (Q z).2) z := (analyticAt_snd (p := Q z)).comp (hQ z hz)
    have hA : AnalyticAt ℂ
        (fun z => ((Q z).1 + (P z).1) ^ 2 + ((Q z).2 + (P z).2) ^ 2 - 1) z :=
      (((hQ1.add hP1).pow 2).add ((hQ2.add hP2).pow 2)).sub analyticAt_const
    have hB : AnalyticAt ℂ
        (fun z => ((Q z).1 + (P z).1) * (P z).2 -
          ((Q z).2 + (P z).2) * ((P z).1 - ((a / 2 : ℝ) : ℂ))) z :=
      ((hQ1.add hP1).mul hP2).sub ((hQ2.add hP2).mul (hP1.sub analyticAt_const))
    exact hA.prod hB
  have hFzero : ∀ z ∈ S, F z = 0 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hrel z hz
    rw [hFdef]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_zero]
      linear_combination h1
    · simp only [Prod.snd_zero]
      linear_combination h2
  have heq : Set.EqOn F (fun _ : ℂ => (0 : ℂ × ℂ)) (Metric.ball x ρ) :=
    junc_eqOn_ball_of_accPt hρ hFana (fun _ _ => analyticAt_const) hacc hFzero
  intro z hz
  have h := heq hz
  rw [hFdef] at h
  refine ⟨?_, ?_⟩
  · have h1 := congrArg Prod.fst h
    simp only [Prod.fst_zero] at h1
    linear_combination h1
  · have h2 := congrArg Prod.snd h
    simp only [Prod.snd_zero] at h2
    linear_combination h2

/-- ROUTE (all ingredients PROVED in the workspace; `Q` = namespace `Work.EQ.JVC` of
`Submission/Work/EQ/junction_values_countable_ns.lean`).

An UNCOUNTABLE labelled junction set at depth `N` (both fan arguments below a fixed scale `δ₁`)
yields an OPEN set `B` on which the junction identity is realised by an ANALYTIC family `H j`
(`j = 0..N`) that is a chain of the relation: `H 0 = fan a h ε`, `H N` the mirrored unstable fan
with parameter `λ^N (C/z)`, and `EqRelC a (H (j+1) z) (H j z)` for `j < N`.

USE by the requester: from exactly this data a candidate chain family is assembled
(`ψ₁ = z`, `ψ₂ = C/z`, forward fan, middle `H j`, far mirrored fan) and finished with
`Work.EQ.exists_regular_of_family`; the clauses `‖z‖ < δ₁` and `‖λ^N (C/z)‖ < δ₁` on `B` are what
make every entry of that family analytic.

Steps. (1) `fan_estimates` gives `δf > 0` with `fan a h ε'` analytic on `ball 0 δf` for all `ε'`;
`germC_facts` gives `ρg > 0`; `bwdP_fan_degenerate_countable` gives `δ₂ > 0`. Take
`δ₀ := min δf δ₂ ρg` (or smaller) and let `δ₁ ≤ δ₀`. (2) For `j = 1..N`, `Q.pieces_exists` applied
to `s.take j` on `Ω := ball 0 δf` gives a countable piece family `S j` and a countable exceptional
set `E j` such that every `p ∈ S j` has `p.1` open, `p.1 ⊆ ball 0 δf`, `p.2` analytic on `p.1`, and
every `w ∈ ball 0 δf \ E j` lies in some `p.1` with `bwdP a (s.take j) (fan a h ε w) = p.2 w`.
(3) `Z := W \ (D ∪ ⋃_{j≤N} E j)` is uncountable, where `W` is the junction set of the hypothesis
(`W ⊆ {‖w‖ < δ₁ ≤ δ₂}`) and `D` is the countable degenerate set of
`bwdP_fan_degenerate_countable` (words of length `≤ N`). (4) On `Z` the labelled relations
`EqRelC a (bwdP a (s.take (j+1)) (fan a h ε w)) (bwdP a (s.take j) (fan a h ε w))` hold for `j < N`
by `Work.EQ.eqRelC_bwdP_step` (`List.take_succ`; the radicand is nonzero because `w ∉ D`).
(5) PIGEONHOLE: a choice of witnesses gives `w ↦ (p 1 w, …, p N w)` into the finite product
`∏_{j : Fin N} ↥(S j)`, which is countable (`Set.Countable.to_subtype`), so some tuple is taken on
an uncountable `Z' ⊆ Z`; `Z'` has an accumulation point `x ∈ Z'`
(`Work.EQ.exists_accPt_principal_of_uncountable`). (6) Take `B := Metric.ball x r` with `r > 0` so
small that `B ⊆ ⋂_j (p j).1 ∩ {w | w ≠ 0 ∧ ‖λ^N (C/w)‖ < δf}` and `B ⊆ Metric.ball 0 δ₁` (possible
since `x ∈ W`). (7) `H 0 := fan a h ε`, `H j := (p j).2` for `1 ≤ j ≤ N`; the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, preconnected ball, accumulation point `x`,
set `Z' ∩ B`) gives on all of `B`: `EqRelC a (H (j+1) z) (H j z)` for `j < N` (analytic polynomial
defect vanishing on `Z' ∩ B`) and `H N z = eqMirror (fan a h η (λ^N (C/z)))` (both sides analytic on
`B` by `Q.analyticOnNhd_Uc`, agreeing on `Z' ∩ B` since `Z' ⊆ W`).

Note: do NOT import `Submission.Work.EQ.junction_values_countable` (it clashes with
`Submission.Work.EQ.H0_section_local` on `Work.EQ.analyticAt_eqMirror`); the namespaced copy
`Submission/Work/EQ/junction_values_countable_ns.lean` (`Work.EQ.JVC`) is the one to import.
Note: for `j = 0` use `H 0 := fan a h ε` (it is analytic on `B ⊆ ball 0 δf`), so no piece family is
needed at level 0; the level-`j` pieces are only needed for `1 ≤ j ≤ N`.
Note: the requester takes a connected component and a smaller ball of the returned `B`, so any
`B` with the stated properties is fine; `x ∈ B` is what is used for the smallness/tail estimates. -/
theorem junction_open_of_uncountable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ₁ : ℝ}, 0 < δ₁ → δ₁ ≤ δ₀ →
      ∀ (N : ℕ) (ε η s : List Bool) (C : ℂ), ε.length = N → s.length = N → C ≠ 0 →
      ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ₁ ∧
          ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (C / w)‖ < δ₁ ∧
          Work.EQ.bwdP a s (Work.EQ.fan a h ε w) =
            Work.EQ.eqMirror (Work.EQ.fan a h η
              (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (C / w)))}.Countable →
      ∃ (B : Set ℂ) (x : ℂ) (H : ℕ → ℂ → ℂ × ℂ),
        IsOpen B ∧ x ∈ B ∧
        (∀ z ∈ B, ‖z‖ < δ₁) ∧
        B ⊆ {w : ℂ | w ≠ 0 ∧
              ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (C / w)‖ < δ₁} ∧
        H 0 = Work.EQ.fan a h ε ∧
        (∀ j : ℕ, j ≤ N → AnalyticOnNhd ℂ (H j) B) ∧
        (∀ j : ℕ, j < N → ∀ z ∈ B, Work.EQ.EqRelC a (H (j + 1) z) (H j z)) ∧
        (∀ z ∈ B, H N z = Work.EQ.eqMirror (Work.EQ.fan a h η
          (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (C / z)))) := by
  classical
  obtain ⟨δf, hδfpos, hfanE⟩ := fan_estimates ha0 ha1 hh
  obtain ⟨δ₂, hδ₂pos, hdeg⟩ := bwdP_fan_degenerate_countable ha0 ha1 hh
  obtain ⟨ρg, hρgpos, _⟩ := germC_facts ha0 ha1 hh
  have hmpos : 0 < min (min δf δ₂) ρg := lt_min (lt_min hδfpos hδ₂pos) hρgpos
  refine ⟨min (min δf δ₂) ρg / 2, by linarith, ?_⟩
  intro δ₁ hδ₁pos hδ₁le
  have hδ₁ltm : δ₁ < min (min δf δ₂) ρg := by linarith
  have hδ₁δf : δ₁ < δf := lt_of_lt_of_le hδ₁ltm (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₁δ₂ : δ₁ < δ₂ := lt_of_lt_of_le hδ₁ltm (le_trans (min_le_left _ _) (min_le_right _ _))
  intro N ε η s C hε hs hC
  -- pieces for every level `1, …, N`
  have hpiece : ∀ j : Fin N, ∃ (S : Set (Set ℂ × (ℂ → ℂ × ℂ))) (E : Set ℂ),
      JVC.IsPieceFam (fun w => bwdP a (s.take (j.val + 1)) (fan a h ε w)) (Metric.ball 0 δf) S E :=
    fun j => JVC.pieces_exists Metric.isOpen_ball (hfanE ε).1 (s.take (j.val + 1))
  let Sp : Fin N → Set (Set ℂ × (ℂ → ℂ × ℂ)) := fun j => Classical.choose (hpiece j)
  let Ep : Fin N → Set ℂ := fun j => Classical.choose (Classical.choose_spec (hpiece j))
  have hSpE : ∀ j : Fin N, JVC.IsPieceFam (fun w => bwdP a (s.take (j.val + 1)) (fan a h ε w))
      (Metric.ball 0 δf) (Sp j) (Ep j) :=
    fun j => Classical.choose_spec (Classical.choose_spec (hpiece j))
  have hSpc : ∀ j : Fin N, (Sp j).Countable := fun j => (hSpE j).1
  have hEpc : ∀ j : Fin N, (Ep j).Countable := fun j => (hSpE j).2.1
  have hSpprop : ∀ j : Fin N, ∀ p ∈ Sp j, IsOpen p.1 ∧ p.1 ⊆ Metric.ball 0 δf ∧
      AnalyticOnNhd ℂ p.2 p.1 := fun j => (hSpE j).2.2.1
  have hSpcov : ∀ j : Fin N, ∀ w ∈ Metric.ball 0 δf, w ∉ Ep j →
      ∃ p ∈ Sp j, w ∈ p.1 ∧ bwdP a (s.take (j.val + 1)) (fan a h ε w) = p.2 w :=
    fun j => (hSpE j).2.2.2
  -- the degenerate locus and the junction set
  set D : Set ℂ := {w : ℂ | ‖w‖ < δ₂ ∧ ∃ σ : List Bool, σ.length ≤ N ∧
      bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0} with hDdef
  have hDc : D.Countable := hdeg ε N
  set W : Set ℂ := {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ₁ ∧
      ‖((eqLam a : ℝ) : ℂ) ^ N * (C / w)‖ < δ₁ ∧
      bwdP a s (fan a h ε w) =
        eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / w)))} with hWdef
  intro hunc
  have hEc : (⋃ j : Fin N, Ep j).Countable := by
    have hh' := Set.Countable.biUnion (Set.countable_univ (α := Fin N))
      (fun j (_ : j ∈ Set.univ) => hEpc j)
    simpa only [Set.biUnion_univ] using hh'
  set Z : Set ℂ := W \ (D ∪ ⋃ j : Fin N, Ep j) with hZdef
  have hZunc : ¬ Z.Countable := by
    intro hZc
    refine hunc (Set.Countable.mono ?_ (hZc.union (hDc.union hEc)))
    intro w hw
    by_cases hmem : w ∈ D ∪ ⋃ j : Fin N, Ep j
    · exact Or.inr hmem
    · exact Or.inl ⟨hw, hmem⟩
  -- level-by-level data of the pieces
  let L : ℕ → ℂ → ℂ × ℂ := fun m w => bwdP a (s.take m) (fan a h ε w)
  have hcov : ∀ w ∈ Z, ∀ j : Fin N, ∃ p ∈ Sp j, w ∈ p.1 ∧ L (j.val + 1) w = p.2 w := by
    intro w hw j
    have hwW : w ∈ W := hw.1
    have hwball : w ∈ Metric.ball (0 : ℂ) δf := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_trans hwW.2.1 hδ₁δf
    have hwEp : w ∉ Ep j := fun h => hw.2 (Or.inr (Set.mem_iUnion.mpr ⟨j, h⟩))
    exact hSpcov j w hwball hwEp
  obtain ⟨t, Z', htSp, hZ'sub, hZ'unc, hZ'prop⟩ :=
    junc_common_pieces (Sp := Sp) (L := L) (Z := Z) hSpc hZunc hcov
  obtain ⟨x, hxZ', hxacc⟩ := exists_accPt_principal_of_uncountable hZ'unc
  have hxZ : x ∈ Z := hZ'sub hxZ'
  have hxW : x ∈ W := hxZ.1
  have hx0 : x ≠ 0 := hxW.1
  have hxδ₁ : ‖x‖ < δ₁ := hxW.2.1
  have hxc : ‖((eqLam a : ℝ) : ℂ) ^ N * (C / x)‖ < δ₁ := hxW.2.2.1
  have hxjunc : bwdP a s (fan a h ε x) =
      eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / x))) := hxW.2.2.2
  -- the open neighbourhood `U` of `x`
  set U : Set ℂ := Metric.ball (0 : ℂ) δ₁ ∩ JVC.omegaC a N δ₁ C ∩ ⋂ j : Fin N, (t j).1
    with hUdef
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact (Metric.isOpen_ball.inter (JVC.isOpen_omegaC C)).inter
      (isOpen_iInter_of_finite (fun j : Fin N => (hSpprop j (t j) (htSp j)).1))
  have hxU : x ∈ U := by
    rw [hUdef]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]; exact hxδ₁
    · simpa only [JVC.omegaC, Set.mem_setOf_eq] using ⟨hx0, hxδ₁, hxc⟩
    · exact Set.mem_iInter.mpr (fun j => (hZ'prop x hxZ' j).1)
  obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.mp hUopen x hxU
  set B : Set ℂ := Metric.ball x R with hBdef
  have hBδ₁ : ∀ z ∈ B, ‖z‖ < δ₁ := by
    intro z hz
    have h := (hRsub hz).1.1
    rwa [Metric.mem_ball, dist_zero_right] at h
  have hBω : ∀ z ∈ B, z ∈ JVC.omegaC a N δ₁ C := fun z hz => (hRsub hz).1.2
  have hBωf : ∀ z ∈ B, z ∈ JVC.omegaC a N δf C := by
    intro z hz
    have h := hBω z hz
    simp only [JVC.omegaC, Set.mem_setOf_eq] at h ⊢
    exact ⟨h.1, lt_trans h.2.1 hδ₁δf, lt_trans h.2.2 hδ₁δf⟩
  have hBpiece : ∀ j : Fin N, ∀ z ∈ B, z ∈ (t j).1 := fun j z hz =>
    Set.mem_iInter.mp (hRsub hz).2 j
  -- the analytic family
  set H : ℕ → ℂ → ℂ × ℂ := fun j z => if h0 : j = 0 then fan a h ε z
      else if hj : j ≤ N then (t ⟨j - 1, by omega⟩).2 z else fan a h ε z with hHdef
  have hH0 : H 0 = fan a h ε := by rw [hHdef]; funext z; simp
  have hHm : ∀ (m : ℕ) (hm1 : 1 ≤ m) (hmN : m ≤ N), H m = (t ⟨m - 1, by omega⟩).2 := by
    intro m hm1 hmN
    funext z
    rw [hHdef]
    dsimp only
    rw [dif_neg (by omega : ¬ (m = 0)), dif_pos hmN]
  have hHana : ∀ j : ℕ, j ≤ N → AnalyticOnNhd ℂ (H j) B := by
    intro j hj
    by_cases h0 : j = 0
    · rw [h0, hH0]
      exact (hfanE ε).1.mono (fun z hz => by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_trans (hBδ₁ z hz) hδ₁δf)
    · rw [hHm j (by omega) hj]
      exact (hSpprop ⟨j - 1, by omega⟩ (t ⟨j - 1, by omega⟩)
        (htSp ⟨j - 1, by omega⟩)).2.2.mono (fun z hz => hBpiece ⟨j - 1, by omega⟩ z hz)
  -- the family reproduces the labelled backward images on `Z'`
  have hHbwd : ∀ w ∈ Z', ∀ m : ℕ, m ≤ N → H m w = bwdP a (s.take m) (fan a h ε w) := by
    intro w hw m hm
    by_cases h0 : m = 0
    · subst h0
      rw [hH0, List.take_zero, bwdP_nil]
    · rw [hHm m (by omega) hm]
      have hp := (hZ'prop w hw ⟨m - 1, by omega⟩).2
      have hidx : (⟨m - 1, by omega⟩ : Fin N).val + 1 = m := by
        simp only [Fin.val_mk]
        omega
      rw [hidx] at hp
      exact hp.symm
  -- the chain relations
  have hHrel : ∀ j : ℕ, j < N → ∀ z ∈ B, EqRelC a (H (j + 1) z) (H j z) := by
    intro j hj z hz
    refine junc_eqRelC_on_ball_of_accPt (a := a) hRpos (hHana (j + 1) (by omega))
      (hHana j (le_of_lt hj)) hxacc ?_ z hz
    intro w hw
    rw [hHbwd w hw j (le_of_lt hj), hHbwd w hw (j + 1) (by omega)]
    have hjlt : j < s.length := by rw [hs]; exact hj
    have htake : s.take (j + 1) = s.take j ++ [s[j]] := (List.take_concat_get' s j hjlt).symm
    rw [htake]
    refine eqRelC_bwdP_step (s := s.take j) (t := s[j]) (P := fan a h ε w) ?_
    have hwD : w ∉ D := fun hmem => (hZ'sub hw).2 (Or.inl hmem)
    have hbsq : bsq (subO1 a (bwdP a (s.take j) (fan a h ε w))) ≠ 0 := by
      intro hzero
      refine hwD ?_
      rw [hDdef]
      exact ⟨lt_trans (hZ'sub hw).1.2.1 hδ₁δ₂, s.take j, by rw [List.length_take, hs]; omega, hzero⟩
    simpa only [bsq, subO1] using hbsq
  -- the junction identity at the far end
  have hRf : AnalyticOnNhd ℂ
      (fun z => eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z)))) B :=
    (JVC.analyticOnNhd_Uc (δf := δf) (N := N) (c := C) (η := η) (hfanE η).1).mono
      (fun z hz => hBωf z hz)
  have hHjunc : ∀ z ∈ B, H N z =
      eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (C / z))) := by
    have heq := junc_eqOn_ball_of_accPt (E := ℂ × ℂ) hRpos (hHana N le_rfl) hRf hxacc ?_
    · intro z hz
      exact heq hz
    · intro w hw
      rw [hHbwd w hw N le_rfl, List.take_of_length_le (le_of_eq hs)]
      exact (hZ'sub hw).1.2.2.2
  refine ⟨B, x, H, Metric.isOpen_ball, Metric.mem_ball_self hRpos, hBδ₁, ?_, hH0, hHana,
    hHrel, hHjunc⟩
  intro z hz
  have h := hBω z hz
  simp only [JVC.omegaC, Set.mem_setOf_eq] at h
  exact ⟨h.1, h.2.2⟩

end

end Work.EQ
