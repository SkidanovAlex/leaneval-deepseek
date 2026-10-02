/-
# `Work.ELNest.tendsto_iterate_g`: the inverse branch `g` of the `z₁`-nest is attracted by `z₁`

Let `S : NestData c` be the interface of the two nests of the equator-leak argument and let
`g` be the inverse branch of `F c = (T_c)^{10}` on the level-`0` region `Q̂₀ = S.Q 0` of the nest
at the parabolic point `z₁`.  This file proves

  `TendstoLocallyUniformlyOn (fun n => S.g^[n]) (fun _ => S.d.z₁) atTop (S.Q 0)`,

i.e. the iterates of `g` converge to `z₁` locally uniformly on `Q̂₀`.

The proof has three ingredients.

* **The iterates of `g` stay in the nest.**  `g` maps `Q̂₀` into `Q̂₁ ⊆ Q̂₀` (`g_mem` and the
  nesting `Q_succ_subset`), so the family `{g^[n]}` is a locally bounded family of holomorphic
  functions on the open set `Q̂₀`.

* **The repelling half-plane of the flower.**  In the repelling coordinate `Ψ` of the
  Leau–Fatou flower, `F c` is the shift `w ↦ w + 1` (`Ψ_shift`).  On the *nest* — that is, for
  `u` in the half-plane `H_R = {Re w < -R}` with `Ψ u ∈ Q̂₀` — the global inverse branch `g`
  agrees with the shift `w ↦ w - 1`: `g (Ψ u)` and `Ψ (u - 1)` are both preimages of `Ψ u` under
  `F c` lying in `Q̂₁`, where `F c` is injective (`polyPullback`).  That `Ψ (u - 1) ∈ Q̂₁` is the
  content of `exists_halfplane_shift`: `Ψ (u-1)` lies on the near side of the `α`-pair (side
  preservation `SP` and `curveF`), close to `z₁` (`Ψ_small`), hence on the near side of
  `Qp 1` (`z1_near_Q`, openness), and its potential is `pot (Ψ u) / 1024` (`pot_F`).  This gives
  `g^[n] (Ψ u) = Ψ (u - n)` (`psi_shift_iterate`), and `Ψ (u - n) → z₁` because
  `Re (u - n) → -∞` (`Ψ_small`).
  Since the flower covers a punctured neighbourhood of `z₁` (`cover`) and the attracting petal
  `Pa` is on the *other* side of the `α`-pair (`Pa_far`, `side_disj`), a small open piece
  `U = Q̂₀ ∩ ball z₁ δ` of `Q̂₀` consists entirely of points `Ψ u` with `Re u < -R`; hence
  `g^[n] → z₁` pointwise on the nonempty open set `U`.

* **Montel + the identity theorem.**  A locally bounded family of holomorphic functions on `Q̂₀`
  is normal (`Work.Normal.montel_locallyBounded`), so every subsequence of `{g^[n]}` has a
  further subsequence converging locally uniformly to a holomorphic limit `ψ`.  By the previous
  item `ψ` agrees with the constant `z₁` on the nonempty open set `U`, so `ψ ≡ z₁` on the
  preconnected set `Q̂₀`.  A standard contradiction argument then gives local uniform convergence.
-/
import Mathlib
import Submission.Work.ELNest.Setup
import Submission.Work.ELNest.bAng_nest_arc
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.Normal.montel_locallyBounded

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

namespace NestData

variable (S : NestData c)

/-! ## The region `Q̂ₙ` and its basic topology -/

/-- The `T2'` description of the level-`n` region of the `z₁`-nest. -/
theorem Q_eq (n : ℕ) :
    S.Q n = pairSideNear S.P0 ∩ pairSideNear (S.Qp n)
      ∩ {z : ℂ | pot S.d.hN z < Real.log (Qlev S.L n)} := by
  show polyRegion [S.P0, S.Qp n] (Qlev S.L n) = _
  exact S.Qmem n

/-- Each level of the nest is open. -/
theorem isOpen_Q (n : ℕ) : IsOpen (S.Q n) := by
  rw [Q_eq S n]
  exact ((Work.ELTop.isOpen_pairSide S.d.hN S.P0).2.inter
      (Work.ELTop.isOpen_pairSide S.d.hN (S.Qp n)).2).inter
    (isOpen_lt (f := fun z : ℂ => pot S.d.hN z) (g := fun _ => Real.log (Qlev S.L n))
      S.d.hN.continuous_potential continuous_const)

/-- The level-`0` region is preconnected (it is a region of a ray polygon). -/
theorem isPreconnected_Q0 : IsPreconnected (S.Q 0) := isPreconnected_polyRegion _ _

/-- The level-`0` region is bounded: it lies below the equipotential of level `L > 1`. -/
theorem isBounded_Q0 : Bornology.IsBounded (S.Q 0) := by
  refine (isCompact_le_pot S.d.hN (Real.log (Qlev S.L 0))).isBounded.subset ?_
  intro z hz
  rw [Q_eq S 0] at hz
  have h2 : pot S.d.hN z < Real.log (Qlev S.L 0) := hz.2
  exact le_of_lt h2

/-- `Qlev L k = L ^ (1/1024^k)` is positive. -/
theorem Qlev_pos (n : ℕ) : 0 < Qlev S.L n :=
  Real.rpow_pos_of_pos (lt_trans zero_lt_one S.hL) _

/-- `Qlev L 0 = L`. -/
theorem Qlev_zero : Qlev S.L 0 = S.L := by simp [Qlev]

/-- The levels of the `z₁`-nest decrease. -/
theorem Qlev_anti (n : ℕ) : Qlev S.L (n + 1) ≤ Qlev S.L n := by
  rw [Qlev, Qlev, Real.rpow_le_rpow_left_iff S.hL]
  have hp : (1024 : ℝ) ^ n ≤ (1024 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1024) n]
  exact div_le_div_of_nonneg_left (by norm_num) (pow_pos (by norm_num) n) hp

/-- **N1, nesting.** The regions of the `z₁`-nest are nested. -/
theorem Q_succ_subset (n : ℕ) : S.Q (n + 1) ⊆ S.Q n := by
  intro z hz
  rw [Q_eq S (n + 1)] at hz
  rw [Q_eq S n]
  refine ⟨⟨hz.1.1, ?_⟩, ?_⟩
  · refine S.nest_side (S.Qp (n + 1)) (S.Qp n) ?_ ?_ hz.1.2
    · -- the near arc of the level-`(n+1)` pair is contained in the near arc of the level-`n` pair
      intro θ hθ
      rw [S.Qpb (n + 1), S.Qpa (n + 1)] at hθ
      rw [S.Qpb n, S.Qpa n]
      exact InArc_bAng_nest hθ
    · exact S.Qp_disj (n + 1) n (by omega)
  · have h2 : pot S.d.hN z < Real.log (Qlev S.L (n + 1)) := hz.2
    exact lt_of_lt_of_le h2 (Real.log_le_log (Qlev_pos S (n + 1)) (Qlev_anti S n))

/-- `Q̂₁ ⊆ Q̂₀`. -/
theorem Q_one_subset : S.Q 1 ⊆ S.Q 0 := Q_succ_subset S 0

/-- The inverse branch `g` maps `Q̂₀` into itself. -/
theorem MapsTo_g : MapsTo S.g (S.Q 0) (S.Q 0) := fun _ hz => Q_one_subset S (S.g_mem _ hz)

/-! ## `z₁` and the pair curve -/

/-- The near side of a pair is contained in the complement of its curve. -/
theorem pairSideNear_subset_compl (P : CoPair S.d.hN) :
    pairSideNear P ⊆ (pairCurve P)ᶜ := by
  intro w hw
  rw [pairSideNear_eq, RawPair.sideNear, RawPair.sideThrough] at hw
  exact connectedComponentIn_subset _ _ hw

/-- `z₁` lies on the pair curve of the `α`-pair, hence is not on its near side. -/
theorem z₁_not_mem_pairSideNear : S.d.z₁ ∉ pairSideNear S.P0 :=
  fun h => (pairSideNear_subset_compl S S.P0 h)
    ((mem_pairCurve_iff S.P0 S.d.z₁).mpr (Or.inr (Or.inl S.P0y.symm)))

/-- `z₁` is the landing point of the root rays, so it lies in the filled Julia set. -/
theorem z₁_mem_K : S.d.z₁ ∈ K c := by
  have h : LandsN S.d.hN S.P0.a S.P0.y := S.P0.lands_a
  rw [S.P0a, S.P0y] at h
  exact Work.ELTop.landsN_mem_K S.d.hN h

/-- The potential vanishes at the parabolic point. -/
theorem pot_z₁ : pot S.d.hN S.d.z₁ = 0 := pot_of_mem S.d.hN (z₁_mem_K S)

/-- A ball around `z₁` on which the potential is below any prescribed positive level. -/
theorem exists_ball_pot_lt {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, Metric.ball S.d.z₁ δ ⊆ {z : ℂ | pot S.d.hN z < t} := by
  have hc : ContinuousAt (fun z : ℂ => pot S.d.hN z) S.d.z₁ :=
    S.d.hN.continuous_potential.continuousAt
  obtain ⟨δ, hδ, hsub⟩ := Metric.continuousAt_iff.mp hc t ht
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have h := hsub (x := z) (by simpa [Metric.mem_ball] using hz)
  rw [pot_z₁ S, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (pot_nonneg S.d.hN z)] at h
  exact h

/-- `z₁` is the landing point of the band side of the `α`-pair, so the repelling petal
accumulates at `z₁`: `z₁` lies in the closure of the near side of the `α`-pair. -/
theorem z₁_mem_closure_pairSideNear : S.d.z₁ ∈ closure (pairSideNear S.P0) := by
  refine frontier_subset_closure ?_
  rw [S.sides_P0.frontier_near]
  exact (mem_pairCurve_iff S.P0 S.d.z₁).mpr (Or.inr (Or.inl S.P0y.symm))

/-! ## The repelling half-plane in the flower -/

/-- **The inverse branch is the shift of the flower on the nest.**  There is a level `R` such
that for every `u` in the half plane `Re u < -R` whose `Ψ`-image lies in the level-`0` region
`Q̂₀`, the branch `g` acts on the flower coordinate as the shift `w ↦ w - 1` and lands in the
level-`1` region `Q̂₁`.

This is the corrected form of the (false) statement `Ψ (H_R) ⊆ Q̂₀ ∩ Q̂₁`: `Q̂₀` lies on the
*near* side of the `α`-pair while the far-left, large-`|Im|` part of the half plane maps into the
attracting petal `Pa ⊆ pairSide P0` (`Ψ_ends`, `Pa_far`), so the membership in `Q̂₀` has to enter
as a hypothesis (it holds in the two applications below, where the point is the image of `z ∈ Q̂₀`
or a point of a small neighbourhood of `z₁` on the near side). -/
theorem exists_halfplane_shift (S : NestData c) :
    ∃ R : ℝ, ∀ u : ℂ, u.re < -R → S.fl.Ψ u ∈ S.Q 0 →
      S.g (S.fl.Ψ u) = S.fl.Ψ (u - 1) ∧ S.fl.Ψ (u - 1) ∈ S.Q 1 := by
  obtain ⟨Rs, hSP⟩ := S.SP
  -- a ball around `z₁` inside the near side of the level-`1` pair
  obtain ⟨δ, hδpos, hδsub⟩ :=
    Metric.isOpen_iff.mp (Work.ELTop.isOpen_pairSide S.d.hN (S.Qp 1)).2 S.d.z₁ (S.z1_near_Q 1)
  obtain ⟨Rψ, hRψ⟩ := S.fl.Ψ_small δ hδpos
  refine ⟨max Rs (Rψ + 1), fun u hu hQ0 => ?_⟩
  have huRs : u.re < -Rs := lt_of_lt_of_le hu (neg_le_neg (le_max_left _ _))
  have hu1Rs : (u - 1).re < -Rs := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hu1Rψ : (u - 1).re < -Rψ := by
    simp only [Complex.sub_re, Complex.one_re]
    have h2 : Rψ + 1 ≤ max Rs (Rψ + 1) := le_max_right _ _
    linarith
  -- `Ψ u` lies on the near side of the `α`-pair and below the level
  have hQ := hQ0
  rw [S.Q_eq 0] at hQ
  have hz_near : S.fl.Ψ u ∈ pairSideNear S.P0 := hQ.1.1
  have hz_notfar : S.fl.Ψ u ∉ pairSide S.P0 :=
    fun h => Set.disjoint_left.mp S.sides_P0.disjoint h hz_near
  -- `Ψ (u - 1)` lies on the near side of the `α`-pair
  have hnearP0 : S.fl.Ψ (u - 1) ∈ pairSideNear S.P0 := by
    have hfar : S.fl.Ψ (u - 1) ∉ pairSide S.P0 := by
      intro hc
      refine hz_notfar ?_
      simpa only [sub_add_cancel] using (hSP (u - 1) hu1Rs).mp hc
    have hcurve : S.fl.Ψ (u - 1) ∉ pairCurve S.P0 := by
      intro hc
      refine pairSideNear_subset_compl S S.P0 hz_near ?_
      have h2 : F c (S.fl.Ψ (u - 1)) ∈ pairCurve S.P0 := by
        rw [← S.curveF]
        exact ⟨S.fl.Ψ (u - 1), hc, rfl⟩
      rw [← S.fl.Ψ_shift (u - 1), sub_add_cancel] at h2
      exact h2
    have h1 : S.fl.Ψ (u - 1) ∈ pairSide S.P0 ∪ pairSideNear S.P0 := by
      rw [S.sides_P0.union_eq]
      exact hcurve
    rcases h1 with h1 | h1
    · exact absurd h1 hfar
    · exact h1
  -- `Ψ (u - 1)` is close to `z₁`, hence on the near side of the level-`1` pair
  have hnearQ1 : S.fl.Ψ (u - 1) ∈ pairSideNear (S.Qp 1) := by
    refine hδsub (Metric.mem_ball.mpr ?_)
    rw [dist_eq_norm]
    exact (hRψ (u - 1) hu1Rψ).2
  -- the potential of `Ψ (u - 1)`
  have hpot : pot S.d.hN (S.fl.Ψ (u - 1)) < Real.log (Qlev S.L 1) := by
    have hlog1 : Real.log (Qlev S.L 1) = Real.log S.L / 1024 := by
      have h1 : Qlev S.L 1 = S.L ^ ((1 : ℝ) / 1024) := by simp [Qlev]
      rw [h1, Real.log_rpow (by linarith [S.hL])]
      ring
    have hlog0 : Real.log (Qlev S.L 0) = Real.log S.L := by simp [Qlev]
    have hpotu : pot S.d.hN (S.fl.Ψ u) = 1024 * pot S.d.hN (S.fl.Ψ (u - 1)) := by
      have h := S.pot_F (S.fl.Ψ (u - 1))
      rw [← S.fl.Ψ_shift (u - 1), sub_add_cancel] at h
      exact h
    have hlt : pot S.d.hN (S.fl.Ψ u) < Real.log S.L := by
      rw [← hlog0]; exact hQ.2
    rw [hlog1]
    linarith
  have hmemQ1 : S.fl.Ψ (u - 1) ∈ S.Q 1 := by
    rw [S.Q_eq 1]
    exact ⟨⟨hnearP0, hnearQ1⟩, hpot⟩
  refine ⟨?_, hmemQ1⟩
  have hg1 : S.g (S.fl.Ψ u) ∈ S.Q 1 := S.g_mem _ hQ0
  have hleft : F c (S.g (S.fl.Ψ u)) = S.fl.Ψ u := S.g_left _ hQ0
  have hF : F c (S.fl.Ψ (u - 1)) = S.fl.Ψ u := by
    rw [← S.fl.Ψ_shift (u - 1), sub_add_cancel]
  exact (S.pbQ 0).injOn hg1 hmemQ1 (by rw [hleft, hF])

/-- **The inverse branch is the shift of the flower, iterated.**  Under the shift identity of
`exists_halfplane_shift`, `g^[n] (Ψ u) = Ψ (u - n)` for every `n`, and every `Ψ (u - n)` with
`n > 0` lies in the level-`1` region. -/
theorem psi_shift_iterate {R : ℝ}
    (hR : ∀ u : ℂ, u.re < -R → S.fl.Ψ u ∈ S.Q 0 →
      S.g (S.fl.Ψ u) = S.fl.Ψ (u - 1) ∧ S.fl.Ψ (u - 1) ∈ S.Q 1)
    (u : ℂ) (hu : u.re < -R) (hQ : S.fl.Ψ u ∈ S.Q 0) :
    ∀ n : ℕ, S.g^[n] (S.fl.Ψ u) = S.fl.Ψ (u - n) ∧
      (0 < n → S.fl.Ψ (u - n) ∈ S.Q 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hu' : (u - (n : ℂ)).re < -R := by
      simp only [Complex.sub_re, Complex.natCast_re]
      linarith [hu]
    have hQ' : S.fl.Ψ (u - (n : ℂ)) ∈ S.Q 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        simpa using hQ
      · exact Q_one_subset S (ih2 h)
    obtain ⟨hstep, hmem⟩ := hR (u - (n : ℂ)) hu' hQ'
    rw [Function.iterate_succ_apply', ih1, hstep]
    have harg : u - ((n + 1 : ℕ) : ℂ) = (u - (n : ℂ)) - 1 := by
      push_cast
      ring
    refine ⟨?_, ?_⟩
    · rw [harg]
    · intro _
      rw [harg]
      exact hmem

/-- The image of the ray `u - ℝ_{≥0}` under `Ψ` converges to `z₁`. -/
theorem tendsto_psi_sub (u : ℂ) :
    Tendsto (fun n : ℕ => S.fl.Ψ (u - n)) atTop (nhds S.d.z₁) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ := S.fl.Ψ_small ε hε
  refine ⟨Nat.ceil (u.re + R + 1) + 1, fun n hn => ?_⟩
  have hre : (u - n).re < -R := by
    simp only [Complex.sub_re, Complex.natCast_re]
    have h1 : u.re + R + 1 ≤ (Nat.ceil (u.re + R + 1) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (u.re + R + 1) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast le_trans (Nat.le_succ _) hn
    linarith
  have h := (hR (u - n) hre).2
  rwa [dist_eq_norm]

/-! ## A small open piece of `Q̂₀` on which `g^[n]` tends to `z₁` -/

/-- **The flower covers a small piece of the nest.**  There is a nonempty open subset `U` of
`Q̂₀` on which the iterates of `g` converge pointwise to `z₁`. -/
theorem exists_open_tendsto (S : NestData c) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ S.Q 0 ∧
      ∀ z ∈ U, Tendsto (fun n : ℕ => S.g^[n] z) atTop (nhds S.d.z₁) := by
  obtain ⟨R, hR⟩ := exists_halfplane_shift S
  obtain ⟨r, hrpos, hcover⟩ := S.fl.cover R
  have hQp0 : ∃ δ > 0, Metric.ball S.d.z₁ δ ⊆ pairSideNear (S.Qp 0) :=
    Metric.isOpen_iff.mp (Work.ELTop.isOpen_pairSide S.d.hN (S.Qp 0)).2 S.d.z₁
      (S.z1_near_Q 0)
  obtain ⟨δa, hδapos, hδasub⟩ := hQp0
  obtain ⟨δb, hδbpos, hδbsub⟩ := exists_ball_pot_lt S (Real.log_pos S.hL)
  set δQ := min δa δb with hδQdef
  have hδQpos : 0 < δQ := lt_min hδapos hδbpos
  have hδQsub : Metric.ball S.d.z₁ δQ ⊆ pairSideNear (S.Qp 0)
      ∩ {z : ℂ | pot S.d.hN z < Real.log S.L} := fun z hz =>
    ⟨hδasub (Metric.ball_subset_ball (min_le_left _ _) hz),
      hδbsub (Metric.ball_subset_ball (min_le_right _ _) hz)⟩
  set δ := min r δQ with hδdef
  have hδpos : 0 < δ := lt_min hrpos hδQpos
  refine ⟨S.Q 0 ∩ Metric.ball S.d.z₁ δ, (isOpen_Q S 0).inter Metric.isOpen_ball, ?_, ?_, ?_⟩
  · obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp (z₁_mem_closure_pairSideNear S) δ hδpos
    have hyball : y ∈ Metric.ball S.d.z₁ δ := by simpa [dist_comm] using hyd
    have hyQ : y ∈ Metric.ball S.d.z₁ δQ := Metric.ball_subset_ball (min_le_right _ _) hyball
    have hyQ0 : y ∈ S.Q 0 := by
      rw [Q_eq S 0]
      exact ⟨⟨hy, (hδQsub hyQ).1⟩, by simpa [Qlev_zero S] using (hδQsub hyQ).2⟩
    exact ⟨y, hyQ0, hyball⟩
  · exact Set.inter_subset_left
  · intro z hz
    obtain ⟨hzQ0, hzball⟩ := hz
    have hzQ := hzQ0
    rw [Q_eq S 0] at hzQ
    obtain ⟨⟨hzP0, -⟩, -⟩ := hzQ
    have hzne : z ≠ S.d.z₁ := fun h => z₁_not_mem_pairSideNear S (h ▸ hzP0)
    have hdist : ‖z - S.d.z₁‖ < r := by
      have h1 : dist z S.d.z₁ < δ := by simpa [Metric.mem_ball] using hzball
      rw [dist_eq_norm] at h1
      have h2 : δ ≤ r := min_le_left _ _
      linarith
    have hpos : 0 < ‖z - S.d.z₁‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hzne
    rcases hcover z hpos hdist with hPa | ⟨u, hu, hzu⟩
    · exact absurd (S.Pa_far hPa) (fun h => Set.disjoint_left.mp S.side_disj h hzP0)
    · have hQ0 : S.fl.Ψ u ∈ S.Q 0 := by rw [hzu]; exact hzQ0
      rw [← hzu]
      have hfun : (fun n : ℕ => S.g^[n] (S.fl.Ψ u)) = fun n : ℕ => S.fl.Ψ (u - n) :=
        funext (fun n => (psi_shift_iterate S hR u hu hQ0 n).1)
      rw [hfun]
      exact tendsto_psi_sub S u

end NestData

/-! ## The main theorem -/

theorem tendsto_iterate_g {c : ℂ} (S : Work.ELNest.NestData c) :
    TendstoLocallyUniformlyOn (fun n : ℕ => S.g^[n]) (fun _ => S.d.z₁) atTop (S.Q 0) := by
  obtain ⟨U, hUopen, hUne, hUsub, hUconv⟩ := NestData.exists_open_tendsto S
  have hUopenQ : IsOpen (S.Q 0) := NestData.isOpen_Q S 0
  have hpre : IsPreconnected (S.Q 0) := NestData.isPreconnected_Q0 S
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ S.Q 0, ‖z‖ ≤ M := by
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
      (NestData.isBounded_Q0 S)
    exact ⟨r, fun z hz => by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hr hz⟩
  have hmaps : MapsTo S.g (S.Q 0) (S.Q 0) := NestData.MapsTo_g S
  have hdiff : ∀ f ∈ Set.range (fun n : ℕ => S.g^[n]), DifferentiableOn ℂ f (S.Q 0) := by
    rintro f ⟨n, rfl⟩
    exact S.g_diff.iterate hmaps n
  have hloc : Work.Normal.IsLocallyBoundedOn (Set.range (fun n : ℕ => S.g^[n])) (S.Q 0) := by
    intro K' hK'sub _
    refine ⟨M, fun f hf z hz => ?_⟩
    obtain ⟨n, rfl⟩ := hf
    exact hM _ (hmaps.iterate n (hK'sub hz))
  have hnorm : Work.Normal.IsNormalFamily (Set.range (fun n : ℕ => S.g^[n])) (S.Q 0) :=
    Work.Normal.montel_locallyBounded hUopenQ hdiff hloc
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hUopenQ]
  intro K hKsub hKc
  by_contra hcon
  rw [Metric.tendstoUniformlyOn_iff] at hcon
  push Not at hcon
  obtain ⟨ε, hεpos, hfreq⟩ := hcon
  have hex : ∀ N : ℕ, ∃ n, N ≤ n ∧ ∃ x ∈ K, ε ≤ dist S.d.z₁ ((S.g^[n]) x) :=
    fun N => Filter.frequently_atTop.1 hfreq N
  choose m hm using hex
  choose y hy using fun N => (hm N).2
  have hmtop : Tendsto m atTop atTop := by
    rw [tendsto_atTop_atTop]
    exact fun b => ⟨b, fun a ha => le_trans ha (hm a).1⟩
  obtain ⟨φ, hφ, hcase⟩ := hnorm (fun k => S.g^[m k]) (fun k => Set.mem_range_self _)
  have hnot_top : ¬ Work.Normal.TendstoLocallyUniformlyAtTop (fun k => S.g^[m (φ k)]) (S.Q 0) := by
    intro htop
    obtain ⟨N, hN⟩ := htop K hKsub hKc (M + 1)
    have hb : ‖S.g^[m (φ N)] (y 0)‖ ≤ M := hM _ (hmaps.iterate (m (φ N)) (hKsub (hy 0).1))
    have h2 := hN N le_rfl (y 0) (hy 0).1
    linarith
  rcases hcase with ⟨ψ, hψ⟩ | hcase2
  · have hψdiff : DifferentiableOn ℂ ψ (S.Q 0) :=
      hψ.differentiableOn (Filter.Eventually.of_forall (fun k => by
        show DifferentiableOn ℂ (S.g^[m (φ k)]) (S.Q 0)
        exact S.g_diff.iterate hmaps _)) hUopenQ
    have hψan : AnalyticOnNhd ℂ ψ (S.Q 0) := hψdiff.analyticOnNhd hUopenQ
    have hconstan : AnalyticOnNhd ℂ (fun _ : ℂ => S.d.z₁) (S.Q 0) :=
      (differentiableOn_const S.d.z₁).analyticOnNhd hUopenQ
    have heqU : ∀ z ∈ U, ψ z = S.d.z₁ := by
      intro z hz
      have h1 : Tendsto (fun k => S.g^[m (φ k)] z) atTop (nhds (ψ z)) := hψ.tendsto_at (hUsub hz)
      have h2 : Tendsto (fun k => S.g^[m (φ k)] z) atTop (nhds S.d.z₁) :=
        (hUconv z hz).comp (hmtop.comp hφ.tendsto_atTop)
      exact tendsto_nhds_unique h1 h2
    obtain ⟨z₀, hz₀U⟩ := hUne
    have hev : ψ =ᶠ[𝓝 z₀] (fun _ : ℂ => S.d.z₁) := by
      filter_upwards [hUopen.mem_nhds hz₀U] with z hz
      exact heqU z hz
    have hEq : EqOn ψ (fun _ : ℂ => S.d.z₁) (S.Q 0) :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hψan hconstan hpre (hUsub hz₀U) hev
    have hunif : TendstoUniformlyOn (fun k => S.g^[m (φ k)]) ψ atTop K :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hUopenQ).mp hψ K hKsub hKc
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (show ∀ᶠ k in atTop,
        ∀ x ∈ K, dist S.d.z₁ (S.g^[m (φ k)] x) < ε from by
      filter_upwards [hunif ε hεpos] with k hk x hx
      have hk' := hk x hx
      rw [hEq (hKsub hx)] at hk'
      simpa using hk')
    have h1 := hN N le_rfl (y (φ N)) (hy (φ N)).1
    have h2 := (hy (φ N)).2
    linarith
  · exact hnot_top hcase2

end Work.ELNest
