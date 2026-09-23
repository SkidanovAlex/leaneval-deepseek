import Mathlib
import Submission.Work.OddBound.Defs

namespace Work.OddBound

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]


/-- **The chart continuity lemma with the field identifications asked for only on the interval of
continuity.**  This is `Submission.IndexIntrinsic2.continuousOn_idxAlong_weak` with the two
hypotheses `hV` and `hZ` weakened: the chart curve data (`γ = symm ∘ u`, `HasDerivAt u w`, membership
of `u` in the chart target) are still required on the strictly larger interval `Icc A B`, but the
identifications `V = frameVector J` and `Z = frameVector (DtQ x₀ u J w J')` are only needed on the
interval `Icc a b` where continuity is claimed.  That is exactly what is available in the local
setting of `Work.OddBound.continuousOn_idxAlong_of_smoothOn`, where `SmoothAlongAt γ V` is only
hypothesised on `Icc a b` and the chart cover of `Submission.SmoothFieldCover` therefore cannot
identify `covAlong cov V` strictly outside `Icc a b`. -/
theorem continuousOn_idxAlong_weak_of_small (htor : cov.torsion = 0) (x₀ : M)
    {γ : ℝ → M} {V Z : (t : ℝ) → TangentSpace I (γ t)}
    {u w J J' : ℝ → E} {a b A B : ℝ}
    (hA : A < a) (hab : a ≤ b) (hB : b < B)
    (hγeq : ∀ t ∈ Icc A B, γ t = (extChartAt I x₀).symm (u t))
    (hu : ∀ t ∈ Icc A B, HasDerivAt u (w t) t)
    (huC : ContinuousOn u (Icc a b)) (hJC : ContinuousOn J (Icc a b))
    (hwC : ContinuousOn w (Icc a b)) (hJ'C : ContinuousOn J' (Icc a b))
    (htgt : ∀ t ∈ Icc A B, u t ∈ (extChartAt I x₀).target)
    (hV : ∀ t ∈ Icc a b, V t = frameVector (I := I) x₀ (γ t) (J t))
    (hZ : ∀ t ∈ Icc a b, Z t = frameVector (I := I) x₀ (γ t)
      (Submission.BonnetMyers.DtQ cov x₀ u J w J' t)) :
    ContinuousOn (fun t : ℝ => idxAlong (cov := cov) γ V Z t) (Icc a b) := by
  have hsub : ∀ t ∈ Icc a b, t ∈ Icc A B := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem (t : ℝ) (ht : t ∈ Icc a b) : Icc A B ∈ 𝓝 t :=
    Icc_mem_nhds (lt_of_lt_of_le hA ht.1) (lt_of_le_of_lt ht.2 hB)
  have hevγ (t : ℝ) (ht : t ∈ Icc a b) : γ =ᶠ[𝓝 t] fun s => (extChartAt I x₀).symm (u s) :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hγeq s hs)
  have hevu (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, HasDerivAt u (w s) s :=
    Filter.mem_of_superset (hmem t ht) (fun s hs => hu s hs)
  have hstay (t : ℝ) (ht : t ∈ Icc a b) : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    (hu t (hsub t ht)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (htgt t (hsub t ht)))
  have hsrc (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ (chartAt H x₀).source := by
    rw [hγeq t (hsub t ht)]
    exact Submission.ChartConnection.mem_source_chartCurve (I := I) (htgt t (hsub t ht))
  have hγmd (t : ℝ) (ht : t ∈ Icc a b) : MDifferentiableAt 𝓘(ℝ) I γ t :=
    (Submission.ChartConnection.mdifferentiableAt_chartCurve (I := I) (hu t (hsub t ht))
      (htgt t (hsub t ht)) (hstay t ht)).congr_of_eventuallyEq (hevγ t ht)
  have hneg : ContinuousOn
      (fun t : ℝ => - Submission.BonnetMyers.indexIntegrand cov x₀ u J w J' t) (Icc a b) :=
    (Submission.IndexIntrinsic2.continuousOn_indexIntegrand_Icc (cov := cov) htor huC hJC hwC hJ'C
      (fun t ht => htgt t (hsub t ht))).neg
  refine hneg.congr ?_
  intro t ht
  exact idxAlong_eq_neg_indexIntegrand (cov := cov) htor x₀ (hsrc t ht) (hstay t ht)
    (hevγ t ht) (hevu t ht) (hγmd t ht) (hV t ht) (hZ t ht)

/-- **Continuity of the intrinsic index integrand along a field smooth on an interval.** This is the
local-hypothesis version of `Submission.ConjEnergy.continuousOn_idxAlong_of_smooth`, which asks for a
*globally* `C^∞` curve `γ` with *globally* nonvanishing velocity. Here `γ` is only `C^∞` on the
slightly larger interval `Ioo (a - 1) (b + 1)`, the velocity is only nonvanishing there, and the
field `V` is smooth along `γ` on the closed interval `Icc a b`.

Route: cover `[a,b]` with `Submission.SmoothFieldCover.exists_partition_smoothField` (its hypotheses
match exactly). On a piece `[c k, c (k+1)]` with local interval `Icc (S k) (E k) ⊆ Ioo (a-1) (b+1)`,
every `t ∈ Icc (c k) (c (k+1))` is strictly inside `Icc (S k) (E k)`, so
`Submission.EnergyRay.covAlong_eq_chart_of_data` identifies `covAlong cov V t` with the chart `DtQ`;
the symmetric interval `Ioo (t-1) (t+1)` it asks for is available since `t ∈ Icc a b` gives
`Ioo (t-1) (t+1) ⊆ Ioo (a-1) (b+1)`. Then `idxAlong γ V (∇V) t = - indexIntegrand ... t` at each
such `t` by `Submission.IndexIntrinsic.idxAlong_eq_neg_indexIntegrand`, whose "eventually near `t`"
hypotheses follow from the plain data on `Icc (S k) (E k)` via `Icc_mem_nhds`. The right-hand side is
continuous on `Icc (c k) (c (k+1))` by `Submission.IndexIntrinsic2.continuousOn_indexIntegrand_Icc`
(cf. also `Submission.EnergyRayCover.continuousOn_idxAlong_piece`, whose proof is a template, but
whose `hZ`/`hγ1` hypotheses are quantified over a room interval -- here one should instead derive
the `hZ` congruence pointwise on `Icc (c k) (c (k+1))` from `covAlong_eq_chart_of_data`, which is
available at those points). Glue with
`Commons.Topology.continuousOn_Icc_of_continuousOn_pieces`. -/
theorem continuousOn_idxAlong_of_smoothOn
    (htor : cov.torsion = 0)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace I (γ t)} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (a - 1) (b + 1)))
    (hne : ∀ t ∈ Ioo (a - 1) (b + 1), curveVelocity (I := I) γ t ≠ 0)
    (hVs : ∀ t ∈ Icc a b, SmoothAlongAt (I := I) γ V t) :
    ContinuousOn (fun t => idxAlong (cov := cov) γ V (covAlong cov V) t) (Icc a b) := by
  classical
  obtain ⟨N, c, Sf, Ef, z, hc0, hcN, hmono, hSB, hsrc, hcdU, hcdV, hVfr, hroom⟩ :=
    Submission.SmoothFieldCover.exists_partition_smoothField (I := I) hab hγ hVs
  -- the chain is monotone from `0` to `N`
  have hmono_le : ∀ j ≤ N, ∀ i ≤ j, c i ≤ c j := by
    intro j
    induction j with
    | zero =>
        intro _ i hi
        obtain rfl := Nat.le_zero.mp hi
        exact le_rfl
    | succ j ih =>
        intro hj i hi
        rcases Nat.lt_or_ge i (j + 1) with hlt | hge
        · rw [Nat.lt_succ_iff] at hlt
          exact le_trans (ih (by omega) i hlt) (hmono j (by omega)).le
        · have hii : i = j + 1 := by omega
          rw [hii]
  have hpiece : ∀ k < N, ContinuousOn (fun t => idxAlong (cov := cov) γ V (covAlong cov V) t)
      (Icc (c k) (c (k + 1))) := by
    intro k hk
    have hck_ge : a ≤ c k := by
      have h := hmono_le k (le_of_lt hk) 0 (Nat.zero_le k)
      rwa [hc0] at h
    have hck1_le : c (k + 1) ≤ b := by
      have h := hmono_le N le_rfl (k + 1) (by omega)
      rwa [hcN] at h
    have hSk : Sf k < c k := (hSB k hk).1
    have hTk : c (k + 1) < Ef k := (hSB k hk).2
    -- the piece `[c k, c (k+1)]` is strictly inside the local interval `Icc (Sf k) (Ef k)`
    have hpiece_sub : Icc (c k) (c (k + 1)) ⊆ Ioo (Sf k) (Ef k) :=
      fun t ht => ⟨by linarith [ht.1, hSk], by linarith [ht.2, hTk]⟩
    -- enlarge the piece slightly, staying inside the open local interval
    set η : ℝ := min (c k - Sf k) (Ef k - c (k + 1)) / 2 with hηdef
    have hηpos : 0 < η := by
      rw [hηdef]
      exact div_pos (lt_min (by linarith) (by linarith)) two_pos
    have h2η1 : 2 * η ≤ c k - Sf k := by
      rw [hηdef]
      have h := min_le_left (c k - Sf k) (Ef k - c (k + 1))
      linarith
    have h2η2 : 2 * η ≤ Ef k - c (k + 1) := by
      rw [hηdef]
      have h := min_le_right (c k - Sf k) (Ef k - c (k + 1))
      linarith
    have hηs1 : Sf k < c k - η := by linarith [h2η1, hηpos]
    have hηs2 : c (k + 1) + η < Ef k := by linarith [h2η2, hηpos]
    have hsubAB : Icc (c k - η) (c (k + 1) + η) ⊆ Icc (Sf k) (Ef k) :=
      fun t ht => ⟨by linarith [ht.1, hηs1], by linarith [ht.2, hηs2]⟩
    have hsubU : Icc (c k - η) (c (k + 1) + η) ⊆ Ioo (Sf k) (Ef k) :=
      fun t ht => ⟨by linarith [ht.1, hηs1], by linarith [ht.2, hηs2]⟩
    -- the chart data of the piece
    set u : ℝ → E := Submission.IntrinsicVariation.chartCoord (I := I) (z k) γ with hudef
    set J : ℝ → E := Submission.JacobiCoords.chartCoords (I := I) (z k) γ V with hJdef
    set w : ℝ → E := deriv u with hwdef
    set J' : ℝ → E := deriv J with hJ'def
    have hUo : ContDiffOn ℝ ∞ u (Ioo (Sf k) (Ef k)) :=
      (hcdU k hk).mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)
    have hJo : ContDiffOn ℝ ∞ J (Ioo (Sf k) (Ef k)) :=
      (hcdV k hk).mono (fun t ht => ⟨ht.1.le, ht.2.le⟩)
    have hγeq : ∀ t ∈ Icc (c k - η) (c (k + 1) + η),
        γ t = (extChartAt I (z k)).symm (u t) := by
      intro t ht
      have hst : γ t ∈ (chartAt H (z k)).source := hsrc k hk t (hsubAB ht)
      rw [hudef]
      show γ t = (extChartAt I (z k)).symm ((extChartAt I (z k)) (γ t))
      exact (PartialEquiv.left_inv (extChartAt I (z k)) (by rwa [extChartAt_source])).symm
    have hu : ∀ t ∈ Icc (c k - η) (c (k + 1) + η), HasDerivAt u (w t) t := by
      intro t ht
      rw [hudef, hwdef]
      exact (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn isOpen_Ioo
        (hsubU ht) hUo).self_of_nhds
    have hJder : ∀ t ∈ Icc (c k - η) (c (k + 1) + η), HasDerivAt J (J' t) t := by
      intro t ht
      rw [hJ'def]
      exact (Submission.JacobiGlobal.eventually_hasDerivAt_of_contDiffOn isOpen_Ioo
        (hsubU ht) hJo).self_of_nhds
    have huC : ContinuousOn u (Icc (c k) (c (k + 1))) := (hUo.continuousOn).mono hpiece_sub
    have hJC : ContinuousOn J (Icc (c k) (c (k + 1))) := (hJo.continuousOn).mono hpiece_sub
    have hwCd : ContDiffOn ℝ ∞ w (Ioo (Sf k) (Ef k)) := by
      rw [hwdef]
      exact hUo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
    have hwC : ContinuousOn w (Icc (c k) (c (k + 1))) := hwCd.continuousOn.mono hpiece_sub
    have hJ'Cd : ContDiffOn ℝ ∞ J' (Ioo (Sf k) (Ef k)) := by
      rw [hJ'def]
      exact hJo.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
    have hJ'C : ContinuousOn J' (Icc (c k) (c (k + 1))) := hJ'Cd.continuousOn.mono hpiece_sub
    have htgt : ∀ t ∈ Icc (c k - η) (c (k + 1) + η),
        u t ∈ (extChartAt I (z k)).target := by
      intro t ht
      rw [hudef]
      exact (extChartAt I (z k)).map_source (by
        rw [extChartAt_source]
        exact hsrc k hk t (hsubAB ht))
    -- the field identifications, on the piece only
    have hVloc : ∀ t ∈ Icc (c k) (c (k + 1)),
        V t = frameVector (I := I) (z k) (γ t) (J t) := by
      intro t ht
      rw [hJdef]
      exact (hVfr k hk t ⟨(hpiece_sub ht).1.le, (hpiece_sub ht).2.le⟩).symm
    have hZloc : ∀ t ∈ Icc (c k) (c (k + 1)),
        covAlong cov V t = frameVector (I := I) (z k) (γ t)
          (Submission.BonnetMyers.DtQ cov (z k) u J w J' t) := by
      intro t ht
      have htI : t ∈ Ioo (Sf k) (Ef k) := hpiece_sub ht
      have htab : t ∈ Icc a b := ⟨le_trans hck_ge ht.1, le_trans ht.2 hck1_le⟩
      have hγ1 : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (t - 1) (t + 1)) :=
        hγ.mono (fun s hs => ⟨by linarith [hs.1, htab.1], by linarith [hs.2, htab.2]⟩)
      have hne1 : curveVelocity (I := I) γ t ≠ 0 :=
        hne t ⟨by linarith [htab.1], by linarith [htab.2]⟩
      have hVs1 : SmoothAlongAt (I := I) γ V t := hVs t htab
      exact Submission.EnergyRay.covAlong_eq_chart_of_data (cov := cov) (V := V) (z := z k)
        htor htI (hsrc k hk) (hcdU k hk) (hcdV k hk) (hVfr k hk) hγ1 hne1 hVs1
    exact continuousOn_idxAlong_weak_of_small (cov := cov) htor (z k)
      (A := c k - η) (B := c (k + 1) + η) (a := c k) (b := c (k + 1))
      (u := u) (w := w) (J := J) (J' := J') (V := V) (Z := covAlong cov V)
      (by linarith [hηpos]) (hmono k hk).le (by linarith [hηpos])
      hγeq hu huC hJC hwC hJ'C htgt hVloc hZloc
  exact Commons.Topology.continuousOn_Icc_of_continuousOn_pieces hc0 hcN
    (fun k hk => (hmono k hk).le) hpiece

end Work.OddBound
