import Mathlib
import Submission.Work.Drive.meridianFibreDefs
import Submission.Work.Drive.analyticLocalCurve
import Submission.Work.Drive.genericFullDefs
import Submission.TorusCollinearity
import Submission.TrisecantTransverse
import Submission.Work.Drive.fmfCore

/-!
# Auxiliary lemmas for the finite-meridian-fibre lemma

This module collects, in order:

* a general-topology counting lemma (a locally finite subset of a second-countable space is
  countable);
* the transport of the torus-level general position hypothesis to an *arbitrary* real
  representative of a collinear off-diagonal triple;
* the *slice dichotomy*: at a general-position collinear off-diagonal triple `(a,b,m)`, either the
  collinearity zero set is locally contained in the slice `{first = a}` ("vertical chart"), or the
  slice through `a` is locally finite at `(b,m)`.
-/

open LeanEval.KnotTheory.Quadrisecant
open scoped Topology
open Filter

noncomputable section

set_option maxHeartbeats 1600000

namespace Work.Drive

/-! ## 1. A locally finite subset of a second-countable space is countable -/

/-- **A locally finite subset of a second-countable space is countable.**  If every point has a
neighbourhood meeting `S` finitely, then `S` is a countable union of finite sets (one for each
member of a countable basis whose intersection with `S` is finite). -/
theorem countable_of_locallyFinite_of_secondCountable {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {S : Set X}
    (h : ∀ z : X, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ (S ∩ U).Finite) : S.Countable := by
  classical
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  set b' : Set (Set X) := {B ∈ b | (S ∩ B).Finite} with hb'def
  have hb'c : b'.Countable := hbc.mono (fun B hB => hB.1)
  have hsub : S ⊆ ⋃ B ∈ b', (S ∩ B) := by
    intro s hs
    obtain ⟨U, hUo, hsU, hUfin⟩ := h s
    obtain ⟨B, hBb, hsB, hBU⟩ := hb.exists_subset_of_mem_open hsU hUo
    exact Set.mem_biUnion ⟨hBb, Set.Finite.subset hUfin (Set.inter_subset_inter_right S hBU)⟩
      ⟨hs, hsB⟩
  exact Set.Countable.mono hsub (hb'c.biUnion (fun B hB => hB.2.countable))

/-! ## 2. Period-shift invariance of the hinge partials, and the transport of general position -/

/-- The real representative of a circle point: if `(x : AddCircle period) = y` then `x` and `y`
differ by an integer multiple of the period. -/
lemma exists_zsmul_period_eq_of_coe_eq {x y : ℝ} (h : (x : KnotParam) = (y : KnotParam)) :
    ∃ n : ℤ, x = y + n • period := by
  have hmem : x - y ∈ AddSubgroup.zmultiples period :=
    (QuotientAddGroup.eq_iff_sub_mem).mp h
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  exact ⟨n, by rw [hn]; ring⟩

/-- `r` at two representatives of the same circle point. -/
lemma knot_periodic_of_coe_eq {r : ℝ → Space} (hr : IsSmoothKnot r) {x y : ℝ}
    (h : (x : KnotParam) = (y : KnotParam)) : r x = r y := by
  obtain ⟨n, rfl⟩ := exists_zsmul_period_eq_of_coe_eq h
  exact (hr.periodic.zsmul n) y

/-- `velocity r` at two representatives of the same circle point. -/
lemma velocity_periodic_of_coe_eq {r : ℝ → Space} (hr : IsSmoothKnot r) {x y : ℝ}
    (h : (x : KnotParam) = (y : KnotParam)) : velocity r x = velocity r y := by
  obtain ⟨n, rfl⟩ := exists_zsmul_period_eq_of_coe_eq h
  exact Function.Periodic.zsmul (fun t => hr.velocity_periodic t) n y

/-- **The hinge partials depend only on the classes of the three parameters.** -/
lemma collPartial_congr {r : ℝ → Space} (hr : IsSmoothKnot r) {a a' b b' m m' : ℝ}
    (ha : (a : KnotParam) = (a' : KnotParam)) (hb : (b : KnotParam) = (b' : KnotParam))
    (hm : (m : KnotParam) = (m' : KnotParam)) :
    collPartialA r a b m = collPartialA r a' b' m' ∧
      collPartialB r a b m = collPartialB r a' b' m' ∧
      collPartialM r a b m = collPartialM r a' b' m' := by
  have hra := knot_periodic_of_coe_eq hr ha
  have hrb := knot_periodic_of_coe_eq hr hb
  have hrm := knot_periodic_of_coe_eq hr hm
  have hva := velocity_periodic_of_coe_eq hr ha
  have hvb := velocity_periodic_of_coe_eq hr hb
  have hvm := velocity_periodic_of_coe_eq hr hm
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [collPartialA, collPartialB, collPartialM, hra, hrb, hrm, hva, hvb, hvm]

/-- Two `Fin 3`-indexed families with equal components give the same independence statement for
any pair of indices. -/
lemma linearIndependent_pair_congr {f g : Fin 3 → Space} {i j : Fin 3}
    (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2) :
    LinearIndependent ℝ ![f i, f j] ↔ LinearIndependent ℝ ![g i, g j] := by
  have hvec : ∀ k : Fin 3, f k = g k := by
    intro k
    fin_cases k <;> assumption
  have hpair : (![f i, f j] : Fin 2 → Space) = ![g i, g j] := by
    ext k
    fin_cases k <;> simp [hvec]
  rw [hpair]

/-- **Rank two is invariant under replacing the parameters by congruent ones.** -/
lemma partialRankTwo_congr {r : ℝ → Space} (hr : IsSmoothKnot r) {a a' b b' m m' : ℝ}
    (ha : (a : KnotParam) = (a' : KnotParam)) (hb : (b : KnotParam) = (b' : KnotParam))
    (hm : (m : KnotParam) = (m' : KnotParam)) :
    PartialRankTwo r a b m ↔ PartialRankTwo r a' b' m' := by
  obtain ⟨hA, hB, hM⟩ := collPartial_congr hr ha hb hm
  have h0 : collPartial r a b m (0 : Fin 3) = collPartial r a' b' m' (0 : Fin 3) := by
    rw [collPartial_eq_A, collPartial_eq_A]; exact hA
  have h1 : collPartial r a b m (1 : Fin 3) = collPartial r a' b' m' (1 : Fin 3) := by
    rw [collPartial_eq_B, collPartial_eq_B]; exact hB
  have h2 : collPartial r a b m (2 : Fin 3) = collPartial r a' b' m' (2 : Fin 3) := by
    rw [collPartial_eq_M, collPartial_eq_M]; exact hM
  constructor <;> rintro ⟨i, j, hij, hLI⟩ <;> refine ⟨i, j, hij, ?_⟩
  · exact (linearIndependent_pair_congr (f := collPartial r a b m)
      (g := collPartial r a' b' m') h0 h1 h2).mp hLI
  · exact (linearIndependent_pair_congr (f := collPartial r a b m)
      (g := collPartial r a' b' m') h0 h1 h2).mpr hLI

/-- **Transport of the torus-level general position to an arbitrary real triple.**  If `(a,b,m)`
is a collinear off-diagonal triple of a knot in torus-level transverse general position, then it is
in general position in the rank-two sense (the partials are period-invariant, so the
fundamental-domain representative supplied by the hypothesis transfers). -/
theorem trisecantGeneralPosition_of_torusTransverse {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hg : TorusGeneralPositionTransverse r) {a b m : ℝ}
    (hcol : collinearityValue r a b m = 0)
    (hoff : (a, (b, m)) ∈ RealOffDiagonalTriples r) : TrisecantGeneralPosition r a b m := by
  have hpZ : torusCollinearity r (torusQuotient (a, (b, m))) = 0 := by
    rw [torusCollinearity_quotient hr]
    exact hcol
  have hpOff : torusQuotient (a, (b, m)) ∈ TorusOffDiag r :=
    (TorusOffDiag_quotient_iff hr _).mpr hoff
  obtain ⟨a', b', m', -, -, -, hpa, hpb, hpm, hGP⟩ := hg _ hpZ hpOff
  have hpa' : (a' : KnotParam) = (a : KnotParam) := by simpa [torusQuotient] using hpa
  have hpb' : (b' : KnotParam) = (b : KnotParam) := by simpa [torusQuotient] using hpb
  have hpm' : (m' : KnotParam) = (m : KnotParam) := by simpa [torusQuotient] using hpm
  have hP : PartialRankTwo r a b m :=
    (partialRankTwo_congr hr hpa'.symm hpb'.symm hpm'.symm).mpr hGP.1.2.2.2
  exact ⟨hoff.1, hoff.2.1, hoff.2.2, hP⟩

/-! ## 3. The slice dichotomy at a general-position collinear triple -/

/-- **The slice dichotomy.**  At a general-position collinear off-diagonal triple `(a,b,m)` of a
smooth knot, either the collinearity zero set is locally contained in the slice `{first = a}`
("vertical chart"), or the slice through `a` is locally finite at `(b,m)`.

Proof: the analytic local-curve theorem (`Work.Drive.analyticLocalCurve`) parametrises the zero set
near `(a,b,m)` by an analytic curve `γ` with a continuous local inverse `τ`; the first coordinate
`s ↦ (γ s).1` is analytic, so either it is locally constant `= a` (whence `τ`-continuity forces
every nearby zero of the collinearity map into the slice, giving the first alternative), or its
zeros are isolated (whence only the point `γ 0` of the chart lies in the slice `{first = a}`, giving
the second alternative). -/
theorem slice_dichotomy {r : ℝ → Space} (hr : IsSmoothKnot r) {a b m : ℝ}
    (hcol : collinearityValue r a b m = 0) (hoff : (a, (b, m)) ∈ RealOffDiagonalTriples r)
    (hrank : PartialRankTwo r a b m) :
    (∃ U : Set RealParamTriple, IsOpen U ∧ (a, (b, m)) ∈ U ∧
        ∀ q ∈ U, collinearityMap r q = 0 → q ∈ RealOffDiagonalTriples r → q.1 = a) ∨
    (∃ V : Set (ℝ × ℝ), IsOpen V ∧ (b, m) ∈ V ∧
        ({p : ℝ × ℝ | collinearityMap r (a, (p.1, p.2)) = 0 ∧
            (a, (p.1, p.2)) ∈ RealOffDiagonalTriples r} ∩ V).Finite) := by
  obtain ⟨-, -, U, hUo, hU0, lo, hi, hlo, hhi, γ, hγcd, hγinj, hγ0, hγmem, hγcov, τ, hτc, hτ⟩ :=
    Work.Drive.analyticLocalCurve r hr a b m ⟨hoff.1, hoff.2.1, hoff.2.2, hrank⟩ hcol
  -- analyticity of the first coordinate along the chart
  have hγan : AnalyticAt ℝ (fun s : ℝ => (γ s).1 - a) 0 := by
    have h1 : ContDiffWithinAt ℝ ⊤ (fun s : ℝ => (γ s).1) (Set.Ioo lo hi) 0 := by
      have hg : ContDiffWithinAt ℝ ⊤ γ (Set.Ioo lo hi) 0 := hγcd.contDiffWithinAt ⟨hlo, hhi⟩
      have hf : ContDiffWithinAt ℝ ⊤ (fun q : RealParamTriple => q.1) Set.univ (γ 0) :=
        contDiff_fst.contDiffWithinAt
      have hcomp := ContDiffWithinAt.comp (0 : ℝ) hf hg (fun s _ => Set.mem_univ _)
      exact hcomp
    have h2 : AnalyticWithinAt ℝ (fun s : ℝ => (γ s).1) (Set.Ioo lo hi) 0 :=
      contDiffWithinAt_omega_iff_analyticWithinAt.mp h1
    have h3 : AnalyticAt ℝ (fun s : ℝ => (γ s).1) 0 := by
      have hev : (Set.Ioo lo hi) =ᶠ[𝓝 (0 : ℝ)] Set.univ :=
        eventuallyEq_univ.mpr (isOpen_Ioo.mem_nhds ⟨hlo, hhi⟩)
      exact analyticWithinAt_univ.mp (h2.congr_set hev)
    exact h3.sub analyticAt_const
  rcases hγan.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · -- Case 1: the chart is vertical in the column `a`
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp hzero
    refine Or.inl ⟨U ∩ τ ⁻¹' (Set.Ioo (-δ) δ), ?_, ?_, ?_⟩
    · exact hτc.isOpen_inter_preimage hUo isOpen_Ioo
    · refine ⟨hU0, ?_⟩
      have hτ0 : τ (a, (b, m)) = 0 := by
        rw [← hγ0]
        exact hτ 0 ⟨hlo, hhi⟩
      simpa [hτ0] using hδ
    · intro q hqU hqcol hqoff
      obtain ⟨t, ht, hγt⟩ := hγcov q hqU.1 hqcol hqoff
      have htτ : τ q = t := by rw [← hγt]; exact hτ t ht
      have hsmall : t ∈ Metric.ball (0 : ℝ) δ := by
        rw [Metric.mem_ball, ← htτ, Real.dist_eq, sub_zero, abs_lt]
        exact Set.mem_Ioo.mp hqU.2
      have hthis : (γ t).1 - a = 0 := hδ' hsmall
      rw [hγt] at hthis
      exact sub_eq_zero.mp hthis
  · -- Case 2: the zeros of the first coordinate along the chart are isolated
    rw [eventually_nhdsWithin_iff] at hne
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.mp hne
    refine Or.inr ⟨{p : ℝ × ℝ | (a, (p.1, p.2)) ∈ U ∩ τ ⁻¹' (Set.Ioo (-δ) δ)}, ?_, ?_, ?_⟩
    · exact (hτc.isOpen_inter_preimage hUo isOpen_Ioo).preimage (by fun_prop)
    · refine ⟨hU0, ?_⟩
      have hτ0 : τ (a, (b, m)) = 0 := by
        rw [← hγ0]
        exact hτ 0 ⟨hlo, hhi⟩
      simpa [hτ0] using hδ
    · refine Set.Finite.subset (Set.finite_singleton (b, m)) ?_
      rintro p ⟨hpslice, hpV⟩
      simp only [Set.mem_setOf_eq] at hpslice
      obtain ⟨hcolp, hoffp⟩ := hpslice
      obtain ⟨t, ht, hγt⟩ := hγcov (a, (p.1, p.2)) hpV.1 hcolp hoffp
      have htτ : τ (a, (p.1, p.2)) = t := by rw [← hγt]; exact hτ t ht
      have hsmall : t ∈ Metric.ball (0 : ℝ) δ := by
        rw [Metric.mem_ball, ← htτ, Real.dist_eq, sub_zero, abs_lt]
        exact Set.mem_Ioo.mp hpV.2
      have ht0 : t = 0 := by
        by_contra htne
        have htne' : t ∈ ({0}ᶜ : Set ℝ) := by simpa [Set.mem_compl_iff] using htne
        have hthis : (γ t).1 - a ≠ 0 := (hδ' hsmall) htne'
        rw [hγt] at hthis
        exact hthis (by simp)
      have hp : (a, (p.1, p.2)) = (a, (b, m)) := by rw [← hγt, ht0, hγ0]
      have hpm : (p.1, p.2) = (b, m) := ((Prod.mk.injEq _ _ _ _).mp hp).2
      simpa using hpm

/-! ## 4. The vertical columns: definition, the dichotomy corollary, and countability -/

/-- **The vertical columns of the trisecant zero set.**  A column `ξ` is *vertical* when some
neighbourhood `U` of a point of the trisecant zero set contains only points of the slice through
`ξ`.  These are the columns over which the trace of the zero set is a whole curve. -/
def VerticalColumn (r : ℝ → Space) : Set ℝ :=
  {ξ : ℝ | ∃ U : Set RealParamTriple, IsOpen U ∧
      (∃ q ∈ U, q ∈ TrisecantZeroSet r ∧ q.1 = ξ) ∧
      ∀ q ∈ U, q ∈ TrisecantZeroSet r → q.1 = ξ}

/-- **A slice accumulation point at a general-position triple makes its column vertical.**  If the
slice `{first = a}` of the trisecant zero set accumulates at the general-position (rank-two)
collinear off-diagonal triple `(a,b,m)`, then `a` is a vertical column.

This is the slice dichotomy: the other alternative of `Work.Drive.slice_dichotomy` would make the
slice *locally finite* at `(b,m)`, contradicting the accumulation. -/
theorem verticalColumn_of_sliceAccumulates {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hg : TorusGeneralPositionTransverse r) {a b m : ℝ}
    (hcol : collinearityValue r a b m = 0) (hoff : (a, (b, m)) ∈ RealOffDiagonalTriples r)
    (hacc : ∃ (bseq : ℕ → ℝ) (mseq : ℕ → ℝ),
      Function.Injective bseq ∧
      (∀ n, collinearityValue r a (bseq n) (mseq n) = 0) ∧
      (∀ n, (a, (bseq n, mseq n)) ∈ RealOffDiagonalTriples r) ∧
      Tendsto (fun n => (bseq n, mseq n)) atTop (𝓝 (b, m))) :
    a ∈ VerticalColumn r := by
  have hrank : PartialRankTwo r a b m :=
    (trisecantGeneralPosition_of_torusTransverse hr hg hcol hoff).2.2.2
  rcases slice_dichotomy hr hcol hoff hrank with hvert | hfin
  · obtain ⟨U, hUo, hU0, hUvert⟩ := hvert
    exact ⟨U, hUo, ⟨(a, (b, m)), hU0, ⟨hcol, hoff⟩, rfl⟩,
      fun q hq hqZ => hUvert q hq hqZ.1 hqZ.2⟩
  · obtain ⟨V, hVo, hV0, hVfin⟩ := hfin
    obtain ⟨bseq, mseq, hbinj, hcolseq, hoffseq, htend⟩ := hacc
    have hev : ∀ᶠ n in atTop, (bseq n, mseq n) ∈ V :=
      htend.eventually (hVo.mem_nhds hV0)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have hrange : (Set.range (fun n : ℕ => (bseq (n + N), mseq (n + N)))).Infinite := by
      refine Set.infinite_range_of_injective (f := fun n : ℕ => (bseq (n + N), mseq (n + N))) ?_
      intro n k hnk
      have h1 : bseq (n + N) = bseq (k + N) := congrArg Prod.fst hnk
      exact Nat.add_right_cancel (hbinj h1)
    have hsub : Set.range (fun n : ℕ => (bseq (n + N), mseq (n + N))) ⊆
        ({p : ℝ × ℝ | collinearityMap r (a, (p.1, p.2)) = 0 ∧
          (a, (p.1, p.2)) ∈ RealOffDiagonalTriples r} ∩ V) := by
      rintro p ⟨n, rfl⟩
      exact ⟨⟨by simpa [collinearityValue] using hcolseq (n + N), hoffseq (n + N)⟩,
        hN (n + N) (Nat.le_add_left N n)⟩
    exact absurd (Set.Infinite.mono hsub hrange) (Set.not_infinite.mpr hVfin)

/-- **The vertical columns are countable.**  Choose, for every vertical column, a basic open set
(`TopologicalSpace.exists_countable_basis`) contained in its vertical neighbourhood; distinct
columns give distinct basic opens (each basic open meets the zero set in points of a single
column), and there are only countably many basic opens. -/
theorem countable_verticalColumn (r : ℝ → Space) : (VerticalColumn r).Countable := by
  classical
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis RealParamTriple
  have hchoice : ∀ ξ : VerticalColumn r, ∃ B : {B : Set RealParamTriple // B ∈ b},
      (∃ q ∈ (B : Set RealParamTriple), q ∈ TrisecantZeroSet r ∧ q.1 = ξ) ∧
      (∀ q ∈ (B : Set RealParamTriple), q ∈ TrisecantZeroSet r → q.1 = ξ) := by
    intro ξ
    obtain ⟨U, hUo, ⟨q, hqU, hqZ, hqξ⟩, hUvert⟩ := ξ.2
    obtain ⟨B, hBb, hqB, hBU⟩ := hb.exists_subset_of_mem_open hqU hUo
    exact ⟨⟨B, hBb⟩, ⟨q, hqB, hqZ, hqξ⟩, fun q' hq' hq'Z => hUvert q' (hBU hq') hq'Z⟩
  choose F hF using hchoice
  have hinj : Function.Injective F := by
    intro ξ ξ' hEq
    obtain ⟨q, hqF, hqZ, hqξ⟩ := (hF ξ).1
    have hqF' : q ∈ (F ξ' : Set RealParamTriple) := by rw [← hEq]; exact hqF
    have hξ' : q.1 = ξ' := (hF ξ').2 q hqF' hqZ
    exact Subtype.ext (hqξ.symm.trans hξ')
  have hcount : Countable {B : Set RealParamTriple // B ∈ b} :=
    Set.countable_coe_iff.mp hbc
  haveI := hcount
  exact Set.countable_coe_iff.mpr (Function.Injective.countable hinj)

/-! ## 5. An infinite fibre forces the column to be a tangent column or a vertical column -/

/-- **An infinite vertical trace forces a tangency or a vertical column.**  If the trace of the
lifted trisecant locus over the meridian `ξ` is infinite, then `ξ` is the column of a tangent chord
(`Work.Drive.TangentColumns`) or a vertical column (`Work.Drive.VerticalColumn`).

Route: the fibre is bounded away from the edges (`shortSecantsFree_of_noInflection`), so it has an
accumulation point `y₀`; extracting an injective sequence of fibre parameters and a convergent
subsequence of their middles, the limit triple is either (i) a tangent chord — the middle escapes to
an endpoint, and `cross_zero_of_tendsto_middle_endpoint_a`/`_b` give the tangency — or (ii) a strict
trisecant `(ξ, ξ+y₀, m₀)`, in which case the slice accumulates there and
`verticalColumn_of_sliceAccumulates` makes the column vertical. -/
theorem fmf_bad_imp_tangent_or_vertical {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hg : TorusGeneralPositionTransverse r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) (ξ : ℝ)
    (hinf : ¬ (liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ}).Finite) :
    ξ ∈ TangentColumns r ∪ VerticalColumn r := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := shortSecantsFree_of_noInflection hr hinfl
  set T : Set ℝ := {y : ℝ | (ξ, y) ∈ liftedTrisecant r} with hTdef
  have hTinf : T.Infinite := by
    have h1 : (fun y : ℝ => ((ξ, y) : ℝ × ℝ)) '' T
        = liftedTrisecant r ∩ {q : ℝ × ℝ | q.1 = ξ} := by
      ext q; constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨hy, rfl⟩
      · rintro ⟨hqA, hq1⟩
        refine ⟨q.2, ?_, ?_⟩
        · show (ξ, q.2) ∈ liftedTrisecant r
          rw [← hq1]; exact hqA
        · exact Prod.ext hq1.symm rfl
    exact Set.Infinite.of_image (f := fun y : ℝ => ((ξ, y) : ℝ × ℝ))
      (by rw [h1]; exact Set.not_finite.mpr hinf)
  have hTK : T ⊆ Set.Icc δ (period - δ) := fun y hy => hδ (ξ, y) hy
  -- an injective sequence in `T`, and a convergent subsequence
  let yseq : ℕ → ℝ := fun n => ((Set.Infinite.natEmbedding T hTinf n : T) : ℝ)
  have hysT : ∀ n, yseq n ∈ T := fun n => (Set.Infinite.natEmbedding T hTinf n).2
  have hyinj : Function.Injective yseq := fun a b hab =>
    (Set.Infinite.natEmbedding T hTinf).injective (Subtype.ext hab)
  obtain ⟨y₀, hy₀K, φ, hφ, hyφ⟩ := isCompact_Icc.tendsto_subseq (x := yseq)
    (fun n => hTK (hysT n))
  have hy₀01 : δ ≤ y₀ := (Set.mem_Icc.mp hy₀K).1
  have hy₀K2 : y₀ ≤ period - δ := (Set.mem_Icc.mp hy₀K).2
  have hy₀0 : 0 < y₀ := lt_of_lt_of_le hδpos hy₀01
  have hy₀lt : y₀ < period := by linarith
  set y : ℕ → ℝ := fun n => yseq (φ n) with hydef
  have hyT : ∀ n, y n ∈ T := fun n => hysT (φ n)
  have hyine : Function.Injective y := fun a b hab => hφ.injective (hyinj hab)
  have hytend : Tendsto y atTop (𝓝 y₀) := hyφ
  -- middles of the chords
  have hmid : ∀ n : ℕ, ∃ m : KnotParam, IsMiddleOnChord r (ξ : KnotParam)
      (((ξ + y n : ℝ)) : KnotParam) m :=
    fun n => exists_middle_of_mem_liftedTrisecant (hyT n)
  choose mc hmc using hmid
  obtain ⟨m₀, -, θ, hθ, hmθ⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set KnotParam)).tendsto_subseq (x := mc)
      (fun n => Set.mem_univ _)
  -- real lifts of the middles, and a convergent subsequence of them
  have hlif : ∀ k : ℕ, ∃ t : ℝ, t ∈ Set.Ico 0 period ∧ (t : KnotParam) = mc (θ k) :=
    fun k => AddCircle.eq_coe_Ico (mc (θ k))
  choose mr hmrwin hmrcoe using hlif
  obtain ⟨m₀R, hm₀Rwin, ψ, hψ, hmψ⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) period)).tendsto_subseq (x := mr)
      (fun k => ⟨(hmrwin k).1, (hmrwin k).2.le⟩)
  have hm₀coe : ((m₀R : ℝ) : KnotParam) = m₀ := by
    have hcoe : Continuous (fun t : ℝ => (t : KnotParam)) := QuotientAddGroup.continuous_mk
    have h1 : Tendsto (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) atTop
        (𝓝 ((m₀R : ℝ) : KnotParam)) := (hcoe.tendsto m₀R).comp hmψ
    have h2 : Tendsto (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) atTop (𝓝 m₀) := by
      have h3 : (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) = fun k : ℕ => mc (θ (ψ k)) :=
        funext fun k => hmrcoe (ψ k)
      rw [h3]
      exact hmθ.comp hψ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hyt : Tendsto (fun k : ℕ => y (θ (ψ k))) atTop (𝓝 y₀) :=
    hytend.comp (hθ.tendsto_atTop.comp hψ.tendsto_atTop)
  -- the limit lies on the closed chord
  have hclosed : IsMiddleOnClosedChord r (ξ : KnotParam)
      (((ξ + y₀ : ℝ)) : KnotParam) m₀ := by
    have hcoe : Continuous (fun t : ℝ => (t : KnotParam)) := QuotientAddGroup.continuous_mk
    have hsec : Tendsto (fun k : ℕ => (((ξ + y (θ (ψ k)) : ℝ)) : KnotParam)) atTop
        (𝓝 (((ξ + y₀ : ℝ)) : KnotParam)) :=
      (hcoe.tendsto (ξ + y₀)).comp (tendsto_const_nhds.add hyt)
    have hmc' : Tendsto (fun k : ℕ => mc (θ (ψ k))) atTop (𝓝 m₀) := hmθ.comp hψ.tendsto_atTop
    have hseq : Tendsto (fun k : ℕ => ((ξ : KnotParam), ((((ξ + y (θ (ψ k)) : ℝ)) : KnotParam),
        mc (θ (ψ k))))) atTop (𝓝 ((ξ : KnotParam), ((((ξ + y₀ : ℝ)) : KnotParam), m₀))) :=
      Tendsto.prodMk_nhds tendsto_const_nhds (Tendsto.prodMk_nhds hsec hmc')
    refine (isClosed_closedMiddleData hr).mem_of_tendsto hseq ?_
    filter_upwards with k
    exact openMiddleData_subset_closedMiddleData r (by
      change IsMiddleOnOpenChord r (ξ : KnotParam) (((ξ + y (θ (ψ k)) : ℝ)) : KnotParam)
        (mc (θ (ψ k)))
      simpa [IsMiddleOnOpenChord, IsMiddleOnChord] using hmc (θ (ψ k)))
  have hseg : r m₀R ∈ segment ℝ (r ξ) (r (ξ + y₀)) := by
    have h := hclosed
    rw [IsMiddleOnClosedChord, knotMap_eq_r hr ξ, knotMap_eq_r hr (ξ + y₀),
      show knotMap r m₀ = r m₀R from by rw [← hm₀coe, knotMap_eq_r hr m₀R]] at h
    exact h
  have hmidreal : ∀ k : ℕ, r (mr (ψ k)) ∈ openSegment ℝ (r ξ) (r (ξ + y (θ (ψ k)))) := by
    intro k
    have h1 : IsMiddleOnChord r (ξ : KnotParam) (((ξ + y (θ (ψ k)) : ℝ)) : KnotParam)
        ((mr (ψ k) : ℝ) : KnotParam) := by
      rw [hmrcoe (ψ k)]; exact hmc (θ (ψ k))
    exact (IsMiddleOnChord_iff_real hr ξ (ξ + y (θ (ψ k))) (mr (ψ k))).mp h1
  have hAne : r ξ ≠ r (ξ + y₀) := by
    intro hk
    have hk' : ((ξ : ℝ) : KnotParam) = (((ξ + y₀ : ℝ)) : KnotParam) :=
      (knotMap_inj_iff hr).mp (by rw [knotMap_eq_r hr ξ, knotMap_eq_r hr (ξ + y₀)]; exact hk)
    exact coe_ne_coe_of_lt hy₀0 hy₀lt hk'
  rcases eq_or_ne (r m₀R) (r ξ) with h1 | h1
  · -- the middle escapes to the first endpoint: tangency at `ξ`
    left
    refine ⟨y₀, hy₀0, hy₀lt, Or.inl ?_⟩
    have hcls : ((m₀R : ℝ) : KnotParam) = ((ξ : ℝ) : KnotParam) :=
      (knotMap_inj_iff hr).mp (by rw [knotMap_eq_r hr m₀R, knotMap_eq_r hr ξ]; exact h1)
    have hcoe : Continuous (fun t : ℝ => (t : KnotParam)) := QuotientAddGroup.continuous_mk
    have hu : Tendsto (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) atTop (𝓝 ((ξ : ℝ) : KnotParam)) := by
      rw [← hcls]
      exact (hcoe.tendsto m₀R).comp hmψ
    have hb : Tendsto (fun k : ℕ => (((ξ + y (θ (ψ k)) : ℝ)) : KnotParam)) atTop
        (𝓝 (((ξ + y₀ : ℝ)) : KnotParam)) :=
      (hcoe.tendsto (ξ + y₀)).comp (tendsto_const_nhds.add hyt)
    have hstr : ∀ᶠ k in atTop, IsMiddleOnChord r (ξ : KnotParam)
        (((ξ + y (θ (ψ k)) : ℝ)) : KnotParam) ((mr (ψ k) : ℝ) : KnotParam) := by
      filter_upwards with k
      rw [hmrcoe (ψ k)]; exact hmc (θ (ψ k))
    exact cross_zero_of_tendsto_middle_endpoint_a hr hAne tendsto_const_nhds hb hu hstr
  rcases eq_or_ne (r m₀R) (r (ξ + y₀)) with h2 | h2
  · -- the middle escapes to the second endpoint: tangency at `ξ + y₀`
    left
    refine ⟨y₀, hy₀0, hy₀lt, Or.inr ?_⟩
    have hcls : ((m₀R : ℝ) : KnotParam) = (((ξ + y₀ : ℝ)) : KnotParam) :=
      (knotMap_inj_iff hr).mp (by rw [knotMap_eq_r hr m₀R, knotMap_eq_r hr (ξ + y₀)]; exact h2)
    have hcoe : Continuous (fun t : ℝ => (t : KnotParam)) := QuotientAddGroup.continuous_mk
    have hu : Tendsto (fun k : ℕ => ((mr (ψ k) : ℝ) : KnotParam)) atTop
        (𝓝 (((ξ + y₀ : ℝ)) : KnotParam)) := by
      rw [← hcls]
      exact (hcoe.tendsto m₀R).comp hmψ
    have hb : Tendsto (fun k : ℕ => (((ξ + y (θ (ψ k)) : ℝ)) : KnotParam)) atTop
        (𝓝 (((ξ + y₀ : ℝ)) : KnotParam)) :=
      (hcoe.tendsto (ξ + y₀)).comp (tendsto_const_nhds.add hyt)
    have hstr : ∀ᶠ k in atTop, IsMiddleOnChord r (ξ : KnotParam)
        (((ξ + y (θ (ψ k)) : ℝ)) : KnotParam) ((mr (ψ k) : ℝ) : KnotParam) := by
      filter_upwards with k
      rw [hmrcoe (ψ k)]; exact hmc (θ (ψ k))
    exact cross_zero_of_tendsto_middle_endpoint_b hr hAne tendsto_const_nhds hb hu hstr
  · -- the limit is a strict trisecant: the slice accumulates, so the column is vertical
    right
    have hcol : collinearityValue r ξ (ξ + y₀) m₀R = 0 := by
      simpa [collinearityValue, collinearityMap] using cross3_eq_zero_of_mem_segment hseg
    have hoff : (ξ, (ξ + y₀, m₀R)) ∈ RealOffDiagonalTriples r :=
      ⟨sub_ne_zero.mpr hAne, sub_ne_zero.mpr h1.symm, sub_ne_zero.mpr h2⟩
    refine verticalColumn_of_sliceAccumulates hr hg hcol hoff
      ⟨fun n => ξ + y (θ (ψ n)), fun n => mr (ψ n), ?_, ?_, ?_, ?_⟩
    · intro n k hnk
      have h1' : y (θ (ψ n)) = y (θ (ψ k)) := by linarith
      exact hψ.injective (hθ.injective (hyine h1'))
    · intro n
      have h1' : IsMiddleOnChord r (ξ : KnotParam) (((ξ + y (θ (ψ n)) : ℝ)) : KnotParam)
          ((mr (ψ n) : ℝ) : KnotParam) := by
        rw [hmrcoe (ψ n)]; exact hmc (θ (ψ n))
      have h2' := (IsMiddleOnChord_iff_real hr ξ (ξ + y (θ (ψ n))) (mr (ψ n))).mp h1'
      simpa [collinearityValue, collinearityMap] using mem_openSegment_cross3 h2'
    · intro n
      have h1' : IsMiddleOnChord r (ξ : KnotParam) (((ξ + y (θ (ψ n)) : ℝ)) : KnotParam)
          ((mr (ψ n) : ℝ) : KnotParam) := by
        rw [hmrcoe (ψ n)]; exact hmc (θ (ψ n))
      have hend : ((ξ : ℝ) : KnotParam) ≠ (((ξ + y (θ (ψ n)) : ℝ)) : KnotParam) := by
        have hyK := hTK (hyT (θ (ψ n)))
        exact coe_ne_coe_of_lt (lt_of_lt_of_le hδpos (Set.mem_Icc.mp hyK).1)
          (by linarith [(Set.mem_Icc.mp hyK).2])
      have hne := h1'.ne_params hr hend
      refine ⟨sub_ne_zero.mpr ?_, sub_ne_zero.mpr ?_, sub_ne_zero.mpr ?_⟩
      · intro hk
        exact hend ((knotMap_inj_iff hr).mp (by
          rw [knotMap_eq_r hr ξ, knotMap_eq_r hr (ξ + y (θ (ψ n)))]; exact hk))
      · intro hk
        exact hne.1 ((knotMap_inj_iff hr).mp (by
          rw [knotMap_eq_r hr (mr (ψ n)), knotMap_eq_r hr ξ]; exact hk.symm))
      · intro hk
        exact hne.2 ((knotMap_inj_iff hr).mp (by
          rw [knotMap_eq_r hr (mr (ψ n)), knotMap_eq_r hr (ξ + y (θ (ψ n)))]; exact hk))
    · have hb : Tendsto (fun n : ℕ => ξ + y (θ (ψ n))) atTop (𝓝 (ξ + y₀)) :=
        tendsto_const_nhds.add hyt
      have hm : Tendsto (fun n : ℕ => mr (ψ n)) atTop (𝓝 m₀R) := hmψ
      exact hb.prodMk_nhds hm


/-! ## 6. Countability of the tangent-chord columns from the local finiteness of the chords -/

/-- **The tangent-chord columns are countable**, given the local finiteness of the set of tangent
chords (`Work.Drive.tangentChordLocallyFinite`).  The columns are the first-coordinate projection
of that locally finite set of pairs. -/
theorem countable_tangentColumns {r : ℝ → Space}
    (h : ∀ z : ℝ × ℝ, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ z ∈ U ∧
      (({p : ℝ × ℝ | 0 < p.2 ∧ p.2 < period ∧
          (cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1) = 0 ∨
           cross3 (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2)) = 0)} ∩ U).Finite)) :
    (TangentColumns r).Countable := by
  have hc : ({p : ℝ × ℝ | 0 < p.2 ∧ p.2 < period ∧
      (cross3 (r (p.1 + p.2) - r p.1) (velocity r p.1) = 0 ∨
       cross3 (r (p.1 + p.2) - r p.1) (velocity r (p.1 + p.2)) = 0)}).Countable :=
    countable_of_locallyFinite_of_secondCountable h
  refine Set.Countable.mono ?_ (hc.image (fun p : ℝ × ℝ => p.1))
  rintro ξ ⟨y, hy0, hylt, hF⟩
  exact ⟨(ξ, y), ⟨hy0, hylt, hF⟩, rfl⟩

end Work.Drive

end
