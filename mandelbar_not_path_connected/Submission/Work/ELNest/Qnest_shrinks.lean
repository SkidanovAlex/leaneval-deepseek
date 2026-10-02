import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.Qlev_facts
import Submission.Work.ELNest.g_eq_localInverse
import Submission.Work.ELNest.tendsto_iterate_g
import Submission.Work.ELTop.frontier_polyRegion_inter_K
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Topology Function
open scoped Topology ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELNest

open Work.EL

variable {c : ℂ}

/-- `F c` maps the filled Julia set `K c` into itself. -/
theorem mapsTo_F_K (c : ℂ) : MapsTo (F c) (K c) (K c) := by
  intro z hz
  show Work.ParamRays.BoundedOrbit c (F c z)
  rw [show F c z = Work.ParamRays.orbit c z 10 by rw [F_eq_tantibar]; rfl]
  exact Work.ParamRays.BoundedOrbit.shift hz 10

namespace NestData

/-- The levels of the `z₁`-nest are nested: `S.Q m ⊆ S.Q n` for `n ≤ m`. -/
theorem Q_anti (S : NestData c) : ∀ {m n : ℕ}, n ≤ m → S.Q m ⊆ S.Q n := by
  intro m n h
  induction h with
  | refl => exact subset_rfl
  | step hk ih => exact Subset.trans (NestData.Q_succ_subset S _) ih

/-- The filled Julia set is exactly the sublevel set `{pot ≤ 0}`. -/
theorem K_eq_le_pot (S : NestData c) : K c = {z : ℂ | Work.EL.pot S.d.hN z ≤ 0} := by
  ext z
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hz; rw [Work.EL.pot_of_mem S.d.hN hz]
  · intro hz
    rw [← Work.EL.pot_eq_zero_iff S.d.hN z]
    exact le_antisymm hz (Work.EL.pot_nonneg S.d.hN z)

/-- **The iterates of `F c` and of the inverse branch `g` are inverse bijections between the
levels of the nest.**  If `z` lies in the level-`(m+1)` region, then its `m`-th forward iterate
lies in the level-`1` region and `g` recovers `z` from it. -/
theorem g_pow_F_pow (S : NestData c) : ∀ (m : ℕ) {z : ℂ}, z ∈ S.Q (m + 1) →
    (F c)^[m] z ∈ S.Q 1 ∧ S.g^[m] ((F c)^[m] z) = z := by
  intro m
  induction m with
  | zero => intro z hz; exact ⟨hz, rfl⟩
  | succ k ih =>
    intro z hz
    have hz' : F c z ∈ S.Q (k + 1) := (S.pbQ (k + 1)).1 hz
    obtain ⟨h1, h2⟩ := ih hz'
    have hFz0 : F c z ∈ S.Q 0 := NestData.Q_anti S (by omega : 0 ≤ k + 1) hz'
    have hgz : S.g (F c z) = z := by
      refine (S.pbQ 0).injOn (S.g_mem (F c z) hFz0) ?_ (S.g_left (F c z) hFz0)
      exact NestData.Q_anti S (by omega : 1 ≤ k + 1 + 1) hz
    constructor
    · rwa [Function.iterate_succ_apply]
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply, h2, hgz]

/-- **The landing point of the level-`1` pair of the `z₁`-nest lies in the level-`0` region.**
`(Qp 1).y` lies on the frontier of `Q̂₁` inside `K c`, hence in `closure Q̂₁ ⊆ closure Q̂₀`; the
only points of `frontier Q̂₀ ∩ K c` are the two landing points `z₁` and `(Qp 0).y`, and `(Qp 1).y`
equals neither. -/
theorem Qp1_land_mem_Q0 (S : NestData c) : (S.Qp 1).y ∈ S.Q 0 := by
  have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
  have hR0 : (1 : ℝ) < Qlev S.L 0 := (Qlev_facts S.hL 0).1
  have hR1 : (1 : ℝ) < Qlev S.L 1 := (Qlev_facts S.hL 1).1
  have hy1K : (S.Qp 1).y ∈ K c :=
    Work.ELTop.landsN_mem_K S.d.hN (S.Qp 1).lands_a
  have hfr1 : frontier (S.Q 1) ∩ K c = {z : ℂ | ∃ P ∈ [S.P0, S.Qp 1], P.y = z} :=
    Work.ELTop.frontier_polyRegion_inter_K S.d.hN hJ [S.P0, S.Qp 1] (S.Q_adm 1) hR1
      (Work.ELTop.polyCurve_isJordan S.d.hN [S.P0, S.Qp 1] (S.Q_adm 1) hR1)
  have hfr0 : frontier (S.Q 0) ∩ K c = {z : ℂ | ∃ P ∈ [S.P0, S.Qp 0], P.y = z} :=
    Work.ELTop.frontier_polyRegion_inter_K S.d.hN hJ [S.P0, S.Qp 0] (S.Q_adm 0) hR0
      (Work.ELTop.polyCurve_isJordan S.d.hN [S.P0, S.Qp 0] (S.Q_adm 0) hR0)
  have hy1_cl1 : (S.Qp 1).y ∈ closure (S.Q 1) := by
    apply frontier_subset_closure
    have hmem : (S.Qp 1).y ∈ frontier (S.Q 1) ∩ K c := by
      rw [hfr1]
      exact ⟨S.Qp 1, by simp, rfl⟩
    exact hmem.1
  have hy1_cl0 : (S.Qp 1).y ∈ closure (S.Q 0) :=
    closure_mono (NestData.Q_succ_subset S 0) hy1_cl1
  rw [closure_eq_self_union_frontier] at hy1_cl0
  rcases hy1_cl0 with h | h
  · exact h
  · exfalso
    have hfx : (S.Qp 1).y ∈ frontier (S.Q 0) ∩ K c := ⟨h, hy1K⟩
    rw [hfr0] at hfx
    obtain ⟨P, hP, hPy⟩ := hfx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact S.Qne 1 (by rw [← hPy, S.P0y])
    · have hdisj : Disjoint (pairCurve (S.Qp 0)) (pairCurve (S.Qp 1)) :=
        S.Qp_disj 0 1 (by norm_num)
      have h1 : (S.Qp 0).y ∈ pairCurve (S.Qp 0) := by
        rw [mem_pairCurve_iff]; exact Or.inr (Or.inl rfl)
      have h2 : (S.Qp 0).y ∈ pairCurve (S.Qp 1) := by
        rw [hPy, mem_pairCurve_iff]; exact Or.inr (Or.inl rfl)
      exact (Set.disjoint_left.mp hdisj h1) h2

/-- **The region of the `z₁`-nest shrinks to `z₁` inside `K c`.** -/
theorem region_shrinks (S : NestData c) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ K c, z ∈ S.Q n → ‖z - S.d.z₁‖ < ε := by
  -- the level of the shift of the flower on the nest
  obtain ⟨R₀, hR₀⟩ := NestData.exists_halfplane_shift S
  -- the cover of the flower of radius `R₀`
  obtain ⟨r, hr_pos, hcover⟩ := S.fl.cover R₀
  -- the landing point of the level-`1` pair lies in the level-`0` region
  have hy1Q0 : (S.Qp 1).y ∈ S.Q 0 := NestData.Qp1_land_mem_Q0 S
  have hKcompact : IsCompact (K c) := by
    rw [NestData.K_eq_le_pot S]
    exact Work.EL.isCompact_le_pot S.d.hN 0
  have hKclosed : IsClosed (K c) := hKcompact.isClosed
  -- the far part of `K c ∩ Q̂₁`
  let A : Set ℂ := {z : ℂ | z ∈ K c ∧ z ∈ S.Q 1 ∧ r ≤ ‖z - S.d.z₁‖}
  have hA_subK : closure A ⊆ K c := by
    have h : closure A ⊆ closure (K c) := closure_mono (fun y hy => hy.1)
    rwa [hKclosed.closure_eq] at h
  have hA_sub_Q0 : closure A ⊆ S.Q 0 := by
    intro x hx
    have hxK : x ∈ K c := hA_subK hx
    have hclosed_ge : IsClosed {y : ℂ | r ≤ ‖y - S.d.z₁‖} :=
      isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
    have hxge : r ≤ ‖x - S.d.z₁‖ := by
      have h1 : x ∈ closure {y : ℂ | r ≤ ‖y - S.d.z₁‖} :=
        closure_mono (fun y hy => hy.2.2) hx
      rwa [hclosed_ge.closure_eq] at h1
    have hxcl1 : x ∈ closure (S.Q 1) := closure_mono (fun y hy => hy.2.1) hx
    rw [closure_eq_self_union_frontier] at hxcl1
    rcases hxcl1 with h | h
    · exact NestData.Q_succ_subset S 0 h
    · have hfx : x ∈ frontier (S.Q 1) ∩ K c := ⟨h, hxK⟩
      have hJ : Work.Top.JordanForm := Work.TopJordan.jordanForm
      have hR1 : (1 : ℝ) < Qlev S.L 1 := (Qlev_facts S.hL 1).1
      have hfr1 : frontier (S.Q 1) ∩ K c = {z : ℂ | ∃ P ∈ [S.P0, S.Qp 1], P.y = z} :=
        Work.ELTop.frontier_polyRegion_inter_K S.d.hN hJ [S.P0, S.Qp 1] (S.Q_adm 1) hR1
          (Work.ELTop.polyCurve_isJordan S.d.hN [S.P0, S.Qp 1] (S.Q_adm 1) hR1)
      rw [hfr1] at hfx
      obtain ⟨P, hP, hPy⟩ := hfx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · rw [← hPy, S.P0y, sub_self, norm_zero] at hxge
        exact absurd hxge (not_le.mpr hr_pos)
      · exact hPy ▸ hy1Q0
  have hA_compact : IsCompact (closure A) :=
    hKcompact.of_isClosed_subset isClosed_closure hA_subK
  -- uniform convergence on the far compact set
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℕ, ∀ m ≥ M₁, ∀ x ∈ closure A, ‖S.g^[m] x - S.d.z₁‖ < ε := by
    have hLUF := Work.ELNest.tendsto_iterate_g S
    have hspec := (tendstoLocallyUniformlyOn_iff_forall_isCompact (NestData.isOpen_Q S 0)).mp
      hLUF (closure A) hA_sub_Q0 hA_compact
    rw [Metric.tendstoUniformlyOn_iff] at hspec
    obtain ⟨M₁, hM₁⟩ := Filter.eventually_atTop.mp (hspec ε hε)
    refine ⟨M₁, fun m hm x hx => ?_⟩
    have hb := hM₁ m hm x hx
    rwa [dist_eq_norm, norm_sub_rev] at hb
  -- the flower estimate on the near part
  obtain ⟨Rε, hRε⟩ := S.fl.Ψ_small ε hε
  obtain ⟨M₂, hM₂⟩ : ∃ M₂ : ℕ, ∀ m ≥ M₂, ∀ v : ℂ, v.re < -R₀ →
      ‖S.fl.Ψ (v - (m : ℂ)) - S.d.z₁‖ < ε := by
    refine ⟨Nat.ceil (Rε - R₀), fun m hm v hv => ?_⟩
    apply (hRε (v - (m : ℂ)) ?_).2
    have hre : (v - (m : ℂ)).re = v.re - (m : ℝ) := by simp
    rw [hre]
    have h1 : Rε - R₀ ≤ (Nat.ceil (Rε - R₀) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Rε - R₀) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  refine ⟨max M₁ M₂ + 1, fun n hn z hzK hzQ => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hm1 : M₁ ≤ m := by omega
  have hm2 : M₂ ≤ m := by omega
  obtain ⟨hu1, hgz⟩ := NestData.g_pow_F_pow S m hzQ
  have huK : (F c)^[m] z ∈ K c := (Work.ELNest.mapsTo_F_K c).iterate m hzK
  by_cases hfar : r ≤ ‖(F c)^[m] z - S.d.z₁‖
  · have hmem : (F c)^[m] z ∈ closure A :=
      subset_closure (show (F c)^[m] z ∈ A from ⟨huK, hu1, hfar⟩)
    have hb := hM₁ m hm1 _ hmem
    rwa [hgz] at hb
  · have hlt : ‖(F c)^[m] z - S.d.z₁‖ < r := not_le.mp hfar
    -- `(F c)^[m] z ∈ Q̂₁ ⊆ pairSideNear P0` and is not `z₁`
    have hu1P0 : (F c)^[m] z ∈ pairSideNear S.P0 := by
      have h := NestData.Q_eq S 1
      rw [h] at hu1
      exact hu1.1.1
    have hune : (F c)^[m] z ≠ S.d.z₁ :=
      fun heq => NestData.z₁_not_mem_pairSideNear S (heq ▸ hu1P0)
    have hpos : 0 < ‖(F c)^[m] z - S.d.z₁‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr hune
    rcases hcover ((F c)^[m] z) hpos hlt with hpa | ⟨v, hv, hvu⟩
    · exact absurd (S.Pa_far hpa) (fun h => (Set.disjoint_left.mp S.side_disj h) hu1P0)
    · have hstep : S.g^[m] ((F c)^[m] z) = S.fl.Ψ (v - (m : ℂ)) := by
        have hQ1 : S.fl.Ψ v ∈ S.Q 0 := by rw [hvu]; exact NestData.Q_succ_subset S 0 hu1
        rw [← hvu, (NestData.psi_shift_iterate S hR₀ v hv hQ1 m).1]
      rw [← hgz, hstep]
      exact hM₂ m hm2 v hv

end NestData

/-- **N2 / the target statement**: the nest at the parabolic point `z₁` shrinks, in the form in
which `Work.ELRig.Z1Nest.shrinks` consumes it. -/
theorem Qnest_shrinks {c : ℂ} (S : Work.ELNest.NestData c) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ Work.EL.K c, z ∈ Work.EL.pairSideNear (S.Qp n) →
      z ∈ Work.EL.pairSideNear S.P0 → ‖z - S.d.z₁‖ < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := NestData.region_shrinks S ε hε
  refine ⟨N, fun n hn z hzK hzQp hzP0 => hN n hn z hzK ?_⟩
  show z ∈ Work.EL.polyRegion [S.P0, S.Qp n] (Qlev S.L n)
  rw [S.Qmem n]
  refine ⟨⟨hzP0, hzQp⟩, ?_⟩
  show Work.EL.pot S.d.hN z < Real.log (Qlev S.L n)
  rw [Work.EL.pot_of_mem S.d.hN hzK]
  exact Real.log_pos (Qlev_facts S.hL n).1

end Work.ELNest
