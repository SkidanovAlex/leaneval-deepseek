import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_SectorAux_sectorAppInteractionEstNormK
import Submission.Work.BoseFixB1S.blockWeightA0A2Qimp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators
open Submission.BoseGases
open Work.BoseFixB1.SectorAux

set_option maxHeartbeats 0
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-
PROOF RECIPE.  This is a *strengthened* copy of the PROVED `Work.BoseFixB1.SectorAux.a0A2QJointNormB1FixGood`
(file `Submission/Work/BoseFixB1/SectorAux/jointCoreGoodState.lean`, 637 lines, 0 sorries).
NOTE (this is the reason a copy is needed rather than a wrapper): the new conclusion's left side is
SMALLER than the old one's (by `pcb - (M1/(4V^2))*Var ≥ 0`), and a claim `LHS ≥ RHS` with a smaller
LHS is the STRONGER claim — the old result does NOT imply it.  It is nevertheless *established by the
same proof*, because the original proof already derives (unconditionally, as an intermediate step)

    hLb  : boxCrossPart V ℓ A w₁ Φ ≥ 2*μ*Pm - Xq - Xp ,      with Xp := (M1/V^2)*((1/4)*(S+1-m)^2+(1/4)*Var+m),
    hXq_le : Xq + μ*Qm ≤ Cred ,    hSqnn : 0 ≤ Sq ,
and it then only *weakens* `Xp = M1*G + (M1/(4V^2))*Var` (a ring identity from the existing
`hXpdef`/`hGid`) to `Xp ≤ M1*G + pcb` (via `supplyP`) before finishing.  The sharpened conclusion is
obtained by NOT doing that final weakening.

STEPS:
 1. copy `Submission/Work/BoseFixB1/SectorAux/jointCoreGoodState.lean` to this path (keep its
    namespace `Work.BoseFixB1.SectorAux` and all `import`/`open` lines verbatim, so that every
    unqualified name in the body still resolves);
 2. rename the declaration to `A0A2QJointSharp`;
 3. in the STATEMENT replace the two conclusion rows
        `+ (1/2) * (boxM2 ... / boxMass^2) * boxPairCount ...`  and
        `- (1/2) * (boxM1 ... / boxMass^2) * (boxFlatCount^2 - boxFlatCount)`
    by the single row
        `+ (1/4) * (boxM1 ... / boxMass^2) * (boxPairCount - boxFlatCount^2 + boxFlatCount)`
    (the statement below already does this);
 4. in the PROOF BODY only the final block changes.  Keep everything up to and including
    `hLb`, `hXq_le`, `hSqnn`; then delete the `hXp_le := supplyP ...` step and the
    `set Ph`/`set Sh`/`hXp_le'`/`hgoal` block, replacing them by
        `have hXp_eq : Xp = M1 * G + (1 / 4) * (M1 / V ^ 2) * Var := by rw [hXpdef, hGid]; ring`
        `have hgoal : Sq + Cross + M1 * G + (1 / 4) * (M1 / V ^ 2) * Var + Cred
              ≥ 2 * μ * Pm + μ * Qm := by
           rw [hXp_eq] at hLb
           linarith [hSqnn, hLb, hXq_le]`
    followed by the original ending `rw [hPorder]; exact hgoal`.
    Careful points flagged by the reviewer: write the new row in EXACTLY the shape it has in the
    statement (`(1/4) * (M1 / V^2) * Var` with `Var := Pc - S*S + S`, not `M1/(4*V^2)`), and since the
    statement's row is `(1/4)*(boxM1.../boxMass^2)*(boxPairCount - boxFlatCount^2 + boxFlatCount)` the
    final `exact hgoal` may need `simp only [...]`/`convert ... using 2 <;> ring` instead of a bare
    `exact` (the original's `exact hgoal` only matched because `Ph`/`Sh` were `set` to the statement's
    literal shapes — reproduce that trick with a `set Var' : ℝ := ... with hVar'def` if convenient).
-/
theorem a0A2QJointSharpImp {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
        (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
        (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
        (hμv : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
        {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
        (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb)
        (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
        {c : ℝ}
        (hcount : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
          (Work.FockBridge.boxCount (Submission.BoseGases.dlBox ℓ d u) x) * (Φ x) ^ 2
            = c * (Φ x) ^ 2)
        (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u))
        (hM2 : Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
              (Submission.BoseGases.wSmall1Pair h M ℓ d u)
            ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)))
        (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) Φ)
        (hcS2 : Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                * Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
                - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
              ≤ Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ),
        Work.BoseFixB1.boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
            (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v)
            (Submission.BoseGases.omC (Classical.choose h)) Φ
          + Work.BoseFixB1.boxCrossPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmall1Pair h M ℓ d u) Φ
          + (1 / 4) * (Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
                (Submission.BoseGases.wSmall1Pair h M ℓ d u)
              / (Work.SmallBoxSliding.boxMass ℓ d u) ^ 2)
              * ((Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ + 1
                  - μ * Work.SmallBoxSliding.boxMass ℓ d u) ^ 2
                + (Work.BoseFixB1S.boxPairCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                      (Submission.BoseGases.dlBox ℓ d u) Φ
                    - Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                      (Submission.BoseGases.dlBox ℓ d u) Φ ^ 2
                    + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                      (Submission.BoseGases.dlBox ℓ d u) Φ)
                + 1)
          + C * (_root_.BoseGases.a v)
              * (μ + Work.BoseFixB1S.boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                    (Submission.BoseGases.dlBox ℓ d u) Φ / Work.SmallBoxSliding.boxMass ℓ d u)
              * Work.BoseFixB1S.boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
                  (Submission.BoseGases.dlBox ℓ d u) Φ
        ≥ 2 * μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ x)
                * (Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)))
          + μ * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) i Φ x) ^ 2
                * (Submission.BoseGases.w1Fibre ℓ
                    (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))) := by
  classical
  set K : ℝ := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M *
      ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        / Work.SmallBoxSliding.smallConvLower M) * (8 * Real.pi)) with hKdef
  refine ⟨100 * |K| + 1, by positivity, ?_⟩
  intro ℓ d μ hℓ hd hμ hR hRχ u hvol hμv N Φ hΦm Cb hΦb hnorm c hcount
    hM1nn hM2 hPcnn hcS2
  have hG : Work.BoseFixB1S.GoodState ℓ Φ := ⟨hΦm, Cb, hΦb⟩
  set Cc : ℝ := 100 * |K| + 1 with hCcdef
  set V : ℝ := Work.SmallBoxSliding.boxMass ℓ d u with hVdef
  set A : Set E3 := Submission.BoseGases.dlBox ℓ d u with hAdef
  set w : E3 → E3 → ℝ := Submission.BoseGases.wSmallPair M ℓ d u v with hwdef
  set w₁ : E3 → E3 → ℝ := Submission.BoseGases.wSmall1Pair h M ℓ d u with hw1def
  set ω : E3 → E3 → ℝ := Submission.BoseGases.omC (Classical.choose h) with hωdef
  set fib : E3 → ℝ := Submission.BoseGases.w1Fibre ℓ w₁ with hfibdef
  set M1 : ℝ := Work.BoseFixB1S.boxM1 ℓ A w₁ with hM1def
  have hVpos : 0 < V := hvol
  have hAmeas : MeasurableSet A := by
    rw [hAdef]; exact Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hVeq : V = (MeasureTheory.volume A).toReal := by
    rw [hVdef, hAdef]; exact Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hAc : A ⊆ Submission.BoseGases.acube ℓ := by
    rw [hAdef]; exact Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  -- ### the fibre facts
  have hfibnn : ∀ z : E3, 0 ≤ fib z := by
    intro z
    rw [hfibdef, hw1def]
    exact Work.BoseFixB1S.boxFibLine_fibre_nonneg (v := v) (R0 := R0) hR0 hv hvrad hv_supp h u z
  have hfibK : ∀ z : E3, fib z ≤ K * _root_.BoseGases.a v := by
    intro z
    have hle := Work.BoseFixB1S.boxFibLine_fibre_le (v := v) (R0 := R0) hv_supp hR0 hv hvrad h
      (M := M) hM hℓ hd hR hRχ u z
    have hEq : (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            / Work.SmallBoxSliding.smallConvLower M)
          * (8 * Real.pi * _root_.BoseGases.a v)) = K * _root_.BoseGases.a v := by
      rw [hKdef]; ring
    rw [hEq] at hle
    rw [← hw1def, ← hfibdef] at hle
    exact hle
  have haa : 0 ≤ _root_.BoseGases.a v :=
    Work.BoseFixB1.a_nonneg (v := v) hR0 hv hvrad hv_supp h
  set Cf : ℝ := K * _root_.BoseGases.a v with hCfdef
  have hCfnn : 0 ≤ Cf := by
    rw [hCfdef]; exact le_trans (hfibnn 0) (hfibK 0)
  have hfible : ∀ z : E3, fib z ≤ Cf := fun z => by rw [hCfdef]; exact hfibK z
  have hfible' : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Cf :=
    fun z _ => by rw [abs_of_nonneg (hfibnn z)]; exact hfible z
  obtain ⟨-, ⟨hFibAesm, Cf0, hCf0nn, hCf0b⟩⟩ :=
    Work.BoseFixB1.q1Fib_aem_bound (v := v) (R0 := R0) hv_supp hR0 hv hvrad (h := h) (M := M)
      hM hℓ hd hR hRχ u
  have hfibae : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := by
    rw [hfibdef, hw1def]
    simpa only [Work.BoseFixB1.q1Fib1] using hFibAesm
  -- ### the counts
  set S : ℝ := Work.BoseFixB1S.boxFlatCount V ℓ A Φ with hSdef
  set nq : ℝ := Work.BoseFixB1S.boxQCount V ℓ A Φ with hnqdef
  set Pc : ℝ := Work.BoseFixB1S.boxPairCount V ℓ A Φ with hPcdef
  -- ### the four component moments, at `GoodState`
  have hmS : (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) *
      ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
      = S := by
    have hflat := Work.BoseFixB1.SectorAux.goodBoxFlatCount_eq_sum_compT
      (N := N) (ℓ := ℓ) (volA := V) hℓ hVpos hAmeas hVeq hAc hG
    rw [hSdef, hflat]
    rfl
  have hmPc : (∑ p ∈ Work.BoseFixB1.disjPairs N,
      ((p.1.card : ℝ) * ((p.1.card : ℝ) - 1)) *
      ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
      = Pc := by
    have hpair := Work.BoseFixB1.SectorAux.goodBoxPairCount_eq_sum_compT
      (N := N) (ℓ := ℓ) (volA := V) hℓ hVpos hAmeas hVeq hAc hG
    rw [hPcdef, hpair]
    rfl
  have hmnq : (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.2.card : ℝ) *
      ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
      = nq := by
    have hqc := Work.BoseFixB1.SectorAux.goodBoxQCount_eq_sum_compT
      (N := N) (ℓ := ℓ) (volA := V) hℓ hVpos hAmeas hVeq hAc hG
    rw [hnqdef, hqc]
    rfl
  have hmS2 : (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) ^ 2 *
      ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
      = Pc + S := by
    rw [← hmPc, ← hmS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => by ring)
  have hSnn : 0 ≤ S := by
    rw [hSdef, Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hnqnn : 0 ≤ nq := by
    rw [hnqdef, Work.BoseFixB1S.boxQCount]
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hmass : (∑ p ∈ Work.BoseFixB1.disjPairs N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2) = 1 := by
    have hh := Work.BoseFixB1.SectorAux.measCompTParseval (N := N) (ℓ := ℓ) (V := V)
      hℓ hVpos hAmeas hVeq hAc hΦm hΦb
    rw [hh, hnorm]
  -- ### the variance
  set Var : ℝ := Pc - S * S + S with hVardef
  have hVarsum : Var = (∑ p ∈ Work.BoseFixB1.disjPairs N, ((p.1.card : ℝ) - S) ^ 2 *
      ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2) := by
    have hexpand : (∑ p ∈ Work.BoseFixB1.disjPairs N, ((p.1.card : ℝ) - S) ^ 2 *
          ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
        = (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) ^ 2 *
              ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
          - 2 * S * (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) *
              ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
          + S ^ 2 * (∑ p ∈ Work.BoseFixB1.disjPairs N,
              ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2) := by
      have hper : ∀ p ∈ Work.BoseFixB1.disjPairs N,
          ((p.1.card : ℝ) - S) ^ 2 *
              ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2
            = ((p.1.card : ℝ) ^ 2 *
                ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
              - 2 * S * ((p.1.card : ℝ) *
                ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2)
              + S ^ 2 * (∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2) := by
        intro p _
        ring
      rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hexpand, hmS2, hmS, hmass, hVardef]
    ring
  have hVarnn : 0 ≤ Var := by
    rw [hVarsum]
    exact Finset.sum_nonneg
      (fun p _ => mul_nonneg (sq_nonneg _) (integral_nonneg (fun x => sq_nonneg _)))
  -- ### the parameters
  set m : ℝ := μ * V with hmdef
  have hm1 : 1 ≤ m := hμv
  have hm0 : 0 ≤ m := le_trans zero_le_one hm1
  set M2 : ℝ := Work.BoseFixB1S.boxM2 V A
      (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h)) with hM2def
  have hM1M2 : M1 ≤ M2 := by rw [hM1def, hM2def]; exact hM2
  have hM1nn' : 0 ≤ M1 := by rw [hM1def]; exact hM1nn
  have hPcnn' : 0 ≤ Pc := by rw [hPcdef]; exact hPcnn
  set G : ℝ := (1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2) with hGdef
  set pcb : ℝ := (1 / 2) * (M2 / V ^ 2) * Pc - (1 / 2) * (M1 / V ^ 2) * (S ^ 2 - S) with hpcbdef
  have hGid : M1 * G = (M1 / V ^ 2) * ((1 / 4) * (S + 1 - m) ^ 2 + m) := by
    rw [hGdef, hmdef]; field_simp; ring
  have hpcb_lb : (M1 / (2 * V ^ 2)) * Var ≤ pcb := by
    have h1 : 0 ≤ ((M2 - M1) / (2 * V ^ 2)) * Pc := by
      refine mul_nonneg (div_nonneg (by linarith) (by positivity)) hPcnn'
    have hdiff : pcb - (M1 / (2 * V ^ 2)) * Var = ((M2 - M1) / (2 * V ^ 2)) * Pc := by
      rw [hpcbdef, hVardef]; ring
    linarith [hdiff, h1]
  -- ### the hop ledger
  have hexp := Work.BoseFixB1.SectorAux.measHopExpansionFibCorr (v := v) (R0 := R0) hv_supp hR0
    hv hvrad hv1 h (M := M) hM (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hR hRχ u hvol
    (N := N) (Φ := Φ) hΦm hΦb
  set Pm : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) * (fib (x i))
        * (Work.UBBInputs8.boxPInd V A i Φ x) with hPmdef
  set Qm : ℝ := ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd V A i Φ x) ^ 2 * fib (x i) with hQmdef
  set DQm : ℝ := ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
      4 * (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2 *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x) ^ 2 * fib (x i) with hDQmdef
  set DPm : ℝ := ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
      ((((p.1.card : ℝ) - 1 - m) ^ 2 / (16 * (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2)) *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2 * fib (x i)) with hDPmdef
  have hsum1 : (V / 2) * (Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ - 2 * μ * Pm) ≥ -(DQm + DPm) := by
    rw [← hVdef, ← hAdef, ← hw1def, ← hfibdef] at hexp
    rw [hexp]
    set TT : Fin N → Finset (Fin N) × Finset (Fin N) → ℝ := fun i p =>
        (((p.1.card : ℝ) - 1 - m) *
              (∫ x in Submission.BoseGases.abox N ℓ,
                Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x * fib (x i)
                  * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x)
            + 4 * (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2 *
              (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x) ^ 2 * fib (x i))
            + ((((p.1.card : ℝ) - 1 - m) ^ 2
                  / (16 * (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2)) *
                (∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x) ^ 2 * fib (x i)))) with hTTdef
    have hstep : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ p ∈ Work.BoseFixB1S.hopPairSet i,
        0 ≤ TT i p := by
      intro i _ p hp
      have h := Work.BoseFixB1.SectorAux.measEdgeAtomSharpGoodState (ℓ := ℓ) (d := d) (μ := μ)
        hℓ hd u hvol hμv (A := A) hAmeas (by rw [← hVdef]; exact hVeq) hAc
        (fib := fib) hfibae (fun z _ => hfibnn z) hfible' (M1 := M1)
        (by simp only [hM1def, hfibdef, hw1def, Work.BoseFixB1S.boxM1]) hM1nn' hG i p hp
      rw [← hVdef, ← hmdef] at h
      simp only [hTTdef]
      linarith [h]
    have hnn : 0 ≤ ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i, TT i p :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun p hp => hstep i (Finset.mem_univ i) p hp))
    have hdecomp : (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i, TT i p)
        = (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
              (((p.1.card : ℝ) - 1 - m) *
                ∫ x in Submission.BoseGases.abox N ℓ,
                  Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x * fib (x i)
                    * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x))
          + (DQm + DPm) := by
      simp only [hTTdef]
      rw [hDQmdef, hDPmdef]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring
    have hfin2 : (0 : ℝ) ≤ (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
        (((p.1.card : ℝ) - 1 - m) *
          ∫ x in Submission.BoseGases.abox N ℓ,
            Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x * fib (x i)
              * Work.BoseFixB1S.boxCompT V A p.1 p.2 Φ x)) + (DQm + DPm) := by
      rw [← hdecomp]
      exact hnn
    linarith [hfin2]
  -- ### the Q-side
  set Xq : ℝ := (16 * Cf / V) * (S + 2 + m) * nq with hXqdef
  have hDQ1 : DQm ≤ 4 * Cf * (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
      (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2 *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x) ^ 2) := by
    rw [hDQmdef, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    obtain ⟨hψm, Cψ, hψb⟩ := Work.BoseFixB1S.goodState_boxCompT hℓ hVpos hAmeas hVeq hAc
      (p.1.erase i) (insert i p.2) hG
    have h := sq_mul_fib_le (N := N) (ℓ := ℓ) hℓ hfibae hCfnn hfibnn hfible
      hψm.aestronglyMeasurable
      (B := max Cψ 0) (fun x hx => le_trans (hψb x hx) (le_max_left _ _)) i
    calc 4 * (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2 *
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x) ^ 2 * fib (x i)
        ≤ 4 * (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2 *
            (Cf * ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x) ^ 2) := by
          refine mul_le_mul_of_nonneg_left h ?_
          positivity
      _ = 4 * Cf * ((Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2 *
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x) ^ 2) := by ring
  have hDQ2 : (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
      (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2 *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x) ^ 2)
      = ∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) *
          ((Real.sqrt ((q.1.card : ℝ) + 2) + Real.sqrt m) ^ 2 *
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) := by
    have hchild := a0A2QJointHopChildReindex (N := N)
      (G := fun q : Finset (Fin N) × Finset (Fin N) =>
        (Real.sqrt ((q.1.card : ℝ) + 2) + Real.sqrt m) ^ 2 *
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
    have hL : (∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
        (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2 *
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.BoseFixB1S.boxCompT V A (p.1.erase i) (insert i p.2) Φ x) ^ 2)
        = ∑ i : Fin N, ∑ p ∈ Work.BoseFixB1S.hopPairSet i,
            (fun q : Finset (Fin N) × Finset (Fin N) =>
              (Real.sqrt ((q.1.card : ℝ) + 2) + Real.sqrt m) ^ 2 *
                ∫ x in Submission.BoseGases.abox N ℓ,
                  (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) (Work.BoseFixB1S.hopChild i p) := by
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun p hp => ?_))
      have hmem : i ∈ p.1 := (Work.BoseFixB1S.mem_hopPairSet.mp hp).2
      have hcard : (((p.1.erase i).card : ℝ) + 2) = (p.1.card : ℝ) + 1 := by
        have h1 : (p.1.erase i).card + 1 = p.1.card := Finset.card_erase_add_one hmem
        have h2 : ((p.1.erase i).card : ℝ) + 1 = (p.1.card : ℝ) := by exact_mod_cast h1
        linarith
      rw [Work.BoseFixB1S.hopChild]
      dsimp only
      rw [hcard]
    rw [hL, hchild]
  have hDQ3 : (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) *
          ((Real.sqrt ((q.1.card : ℝ) + 2) + Real.sqrt m) ^ 2 *
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2))
      ≤ 2 * (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) *
          (((q.1.card : ℝ) + 2 + m) *
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun q _ => ?_)
    have h1 : (Real.sqrt ((q.1.card : ℝ) + 2) + Real.sqrt m) ^ 2
        ≤ 2 * (((q.1.card : ℝ) + 2) + m) := by
      have hsa : 0 ≤ (q.1.card : ℝ) + 2 := by positivity
      have hs1 : Real.sqrt ((q.1.card : ℝ) + 2) ^ 2 = (q.1.card : ℝ) + 2 := Real.sq_sqrt hsa
      have hs2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0
      nlinarith [sq_nonneg (Real.sqrt ((q.1.card : ℝ) + 2) - Real.sqrt m), hs1, hs2]
    have hJ : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have hcq : 0 ≤ (q.2.card : ℝ) := by positivity
    have hJc : 0 ≤ (q.2.card : ℝ) * (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) := mul_nonneg hcq hJ
    calc (q.2.card : ℝ) * ((Real.sqrt ((q.1.card : ℝ) + 2) + Real.sqrt m) ^ 2 *
          ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
        = (Real.sqrt ((q.1.card : ℝ) + 2) + Real.sqrt m) ^ 2 *
            ((q.2.card : ℝ) * ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) := by ring
      _ ≤ (2 * (((q.1.card : ℝ) + 2) + m)) *
            ((q.2.card : ℝ) * ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 hJc
      _ = 2 * ((q.2.card : ℝ) * ((((q.1.card : ℝ) + 2) + m) *
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)) := by ring
  set X0 : ℝ := ∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) * ((q.1.card : ℝ) *
      ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) with hX0def
  have hDQ4 : (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) *
          (((q.1.card : ℝ) + 2 + m) *
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2))
      = X0 + (2 + m) * nq := by
    rw [hX0def, ← hmnq]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have hDQ5 : X0 ≤ S * nq := by
    have hb := Work.BoseFixB1.SectorAux.countBridgePairQ (N := N) (ℓ := ℓ) (volA := V)
      hℓ hVpos hAmeas hVeq hAc hΦm hΦb hnorm (c := c) hcount hcS2
    rw [← hSdef, ← hnqdef] at hb
    rw [hX0def]
    refine le_trans (le_of_eq ?_) hb
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have hDQbound : DQm ≤ 8 * Cf * (S + 2 + m) * nq := by
    have hq1 := hDQ1
    rw [hDQ2] at hq1
    have hq2 : (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.2.card : ℝ) *
          ((Real.sqrt ((q.1.card : ℝ) + 2) + Real.sqrt m) ^ 2 *
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2))
        ≤ 2 * (S * nq + (2 + m) * nq) := by
      have := hDQ3
      rw [hDQ4] at this
      linarith [hDQ5]
    have hq3 : 2 * (S * nq + (2 + m) * nq) = 2 * ((S + 2 + m) * nq) := by ring
    have hstep : DQm ≤ 4 * Cf * (2 * ((S + 2 + m) * nq)) := by
      refine le_trans hq1 ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith [hq2, hq3.le, hq3.ge]
    calc DQm ≤ 4 * Cf * (2 * ((S + 2 + m) * nq)) := hstep
      _ = 8 * Cf * (S + 2 + m) * nq := by ring
  -- ### the P-side
  have hDP1 : DPm = (M1 / V) * (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.1.card : ℝ) *
      ((((q.1.card : ℝ) - 1 - m) ^ 2 / (16 * (Real.sqrt ((q.1.card : ℝ) + 1) + Real.sqrt m) ^ 2)) *
        ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)) := by
    have hpeel := Work.BoseFixB1.SectorAux.measHopPeelSum (v := v) (R0 := R0) hv_supp hR0
      hv hvrad hv1 h (M := M) hM (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hR hRχ u hvol
      (N := N) (Φ := Φ) hΦm hΦb
      (H := fun p : Finset (Fin N) × Finset (Fin N) =>
        ((((p.1.card : ℝ) - 1 - m) ^ 2 / (16 * (Real.sqrt ((p.1.card : ℝ) + 1) + Real.sqrt m) ^ 2))))
    rw [← hVdef, ← hAdef, ← hw1def, ← hM1def, ← hfibdef] at hpeel
    rw [hDPmdef, hpeel]
    congr 1
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have hDP2 : (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.1.card : ℝ) *
      ((((q.1.card : ℝ) - 1 - m) ^ 2 / (16 * (Real.sqrt ((q.1.card : ℝ) + 1) + Real.sqrt m) ^ 2)) *
        ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2))
      ≤ (∑ q ∈ Work.BoseFixB1.disjPairs N,
          ((1 / 8) * ((q.1.card : ℝ) + 1 - m) ^ 2 + 1 / 8) *
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) := by
    refine Finset.sum_le_sum (fun q _ => ?_)
    have hJ : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have hle : (q.1.card : ℝ) * (((q.1.card : ℝ) - 1 - m) ^ 2
          / (16 * (Real.sqrt ((q.1.card : ℝ) + 1) + Real.sqrt m) ^ 2))
        ≤ (1 / 8) * ((q.1.card : ℝ) + 1 - m) ^ 2 + 1 / 8 := by
      have h := blockWeightA0A2Qimp (t := (q.1.card : ℝ)) (m := m) (Nat.cast_nonneg _) hm0
      have he : (q.1.card : ℝ) * (((q.1.card : ℝ) - 1 - m) ^ 2
            / (16 * (Real.sqrt ((q.1.card : ℝ) + 1) + Real.sqrt m) ^ 2))
          = (q.1.card : ℝ) * ((q.1.card : ℝ) - 1 - m) ^ 2
              / (16 * (Real.sqrt ((q.1.card : ℝ) + 1) + Real.sqrt m) ^ 2) := by ring
      rw [he]; exact h
    have := mul_le_mul_of_nonneg_right hle hJ
    linarith [this]
  have hDP3 : (∑ q ∈ Work.BoseFixB1.disjPairs N,
        ((1 / 8) * ((q.1.card : ℝ) + 1 - m) ^ 2 + 1 / 8) *
          ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
      = (1 / 8) * (Var + (S + 1 - m) ^ 2) + 1 / 8 := by
    have hmid : (∑ q ∈ Work.BoseFixB1.disjPairs N, ((q.1.card : ℝ) - S) *
        ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) = 0 := by
      have hsp : (∑ q ∈ Work.BoseFixB1.disjPairs N, ((q.1.card : ℝ) - S) *
          ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
          = (∑ q ∈ Work.BoseFixB1.disjPairs N, (q.1.card : ℝ) *
              ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
            - S * (∑ q ∈ Work.BoseFixB1.disjPairs N,
                ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun q _ => by ring)
      rw [hsp, hmS, hmass]; ring
    have hexpand : (∑ q ∈ Work.BoseFixB1.disjPairs N, ((q.1.card : ℝ) + 1 - m) ^ 2 *
          ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
        = Var + (S + 1 - m) ^ 2 := by
      rw [hVarsum]
      have hexp2 : (∑ q ∈ Work.BoseFixB1.disjPairs N, ((q.1.card : ℝ) + 1 - m) ^ 2 *
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
          = (∑ q ∈ Work.BoseFixB1.disjPairs N, ((q.1.card : ℝ) - S) ^ 2 *
                ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
            + 2 * (S + 1 - m) * (∑ q ∈ Work.BoseFixB1.disjPairs N, ((q.1.card : ℝ) - S) *
                ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
            + (S + 1 - m) ^ 2 * (∑ q ∈ Work.BoseFixB1.disjPairs N,
                ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun q _ => by ring)
      rw [hexp2, hmid, hmass]
      ring
    have hsummand : (∑ q ∈ Work.BoseFixB1.disjPairs N,
          ((1 / 8) * ((q.1.card : ℝ) + 1 - m) ^ 2 + 1 / 8) *
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
        = (1 / 8) * (∑ q ∈ Work.BoseFixB1.disjPairs N, ((q.1.card : ℝ) + 1 - m) ^ 2 *
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2)
          + (1 / 8) * (∑ q ∈ Work.BoseFixB1.disjPairs N,
              ∫ x in Submission.BoseGases.abox N ℓ, (Work.BoseFixB1S.boxCompT V A q.1 q.2 Φ x) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun q _ => by ring)
    rw [hsummand, hexpand, hmass]
    ring
  set Xp : ℝ := (1 / 4) * (M1 / V ^ 2) * ((S + 1 - m) ^ 2 + Var + 1) with hXpdef
  have hDPbound : (2 / V) * DPm ≤ Xp := by
    have h1 : DPm ≤ (M1 / V) * ((1 / 8) * (Var + (S + 1 - m) ^ 2) + 1 / 8) := by
      rw [hDP1]
      have h := mul_le_mul_of_nonneg_left (le_trans hDP2 hDP3.le) (by positivity : (0:ℝ) ≤ M1 / V)
      linarith [h]
    rw [hXpdef]
    have h2 : (2 / V) * ((M1 / V) * ((1 / 8) * (Var + (S + 1 - m) ^ 2) + 1 / 8))
        = (1 / 4) * (M1 / V ^ 2) * ((S + 1 - m) ^ 2 + Var + 1) := by
      field_simp; ring
    calc (2 / V) * DPm ≤ (2 / V) * ((M1 / V) * ((1 / 8) * (Var + (S + 1 - m) ^ 2) + 1 / 8)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 / 4) * (M1 / V ^ 2) * ((S + 1 - m) ^ 2 + Var + 1) := h2
  -- ### the Q-side supply
  have hQm_le : Qm ≤ Cf * nq := by
    rw [hQmdef, hnqdef, Work.BoseFixB1S.boxQCount, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    obtain ⟨hψm, Cψ, hψb⟩ := Work.BoseFixB1S.goodState_boxQInd hℓ hVpos hAmeas hVeq hAc i hG
    exact sq_mul_fib_le (N := N) (ℓ := ℓ) hℓ hfibae hCfnn hfibnn hfible hψm.aestronglyMeasurable
      (B := max Cψ 0) (fun x hx => le_trans (hψb x hx) (le_max_left _ _)) i
  have hcaa : 49 * Cf ≤ Cc * _root_.BoseGases.a v := by
    rw [hCcdef, hCfdef]
    have hh : (49 : ℝ) * K ≤ 100 * |K| := by
      have h1 := le_abs_self K
      have h2 := neg_abs_le K
      nlinarith [h1, h2]
    have h3 : 49 * K * _root_.BoseGases.a v ≤ 100 * |K| * _root_.BoseGases.a v :=
      mul_le_mul_of_nonneg_right hh haa
    nlinarith [h3, haa]
  have hXq_le : Xq + μ * Qm ≤ Cc * _root_.BoseGases.a v * (μ + S / V) * nq := by
    have hcoef : (16 * Cf / V) * (S + 2 + m) + Cf * μ ≤ Cc * _root_.BoseGases.a v * (μ + S / V) :=
      creditCoef (Cf := Cf) (Cc := Cc) (av := _root_.BoseGases.a v) (S := S) (mu := μ) (m := m)
        (V := V) hVpos hmdef hm1 hSnn hμ haa hCfnn hcaa
    rw [hXqdef]
    have h1 : μ * Qm ≤ μ * (Cf * nq) := mul_le_mul_of_nonneg_left hQm_le hμ.le
    calc (16 * Cf / V) * (S + 2 + m) * nq + μ * Qm
        ≤ (16 * Cf / V) * (S + 2 + m) * nq + μ * (Cf * nq) := by linarith
      _ = ((16 * Cf / V) * (S + 2 + m) + Cf * μ) * nq := by ring
      _ ≤ (Cc * _root_.BoseGases.a v * (μ + S / V)) * nq := mul_le_mul_of_nonneg_right hcoef hnqnn
      _ = Cc * _root_.BoseGases.a v * (μ + S / V) * nq := by ring
  -- ### the final assembly
  have hLb : Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ ≥ 2 * μ * Pm - Xq - Xp := by
    have h2 : (2 / V) * ((V / 2) * (Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ - 2 * μ * Pm)) ≥ -(2 / V) * (DQm + DPm) := by
      have hV2 : (0 : ℝ) ≤ 2 / V := by positivity
      have := mul_le_mul_of_nonneg_left hsum1 hV2
      linarith [this]
    have h3 : (2 / V) * ((V / 2) * (Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ - 2 * μ * Pm))
        = Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ - 2 * μ * Pm := by
      field_simp
    have h4 : (2 / V) * (DQm + DPm) ≤ Xq + Xp := by
      have h5 : (2 / V) * DQm ≤ Xq :=
        qsideArith (Cf := Cf) (V := V) (S := S) (m := m) (nq := nq) (DQm := DQm) (Xq := Xq)
          hVpos hDQbound hXqdef
      have h6 : (2 / V) * DPm ≤ Xp := hDPbound
      linarith [h5, h6]
    linarith [h2, h3, h4]
  have hSqnn : 0 ≤ Work.BoseFixB1.boxSqPart V ℓ A w ω Φ := by
    rw [hVdef, hAdef, hwdef, hωdef]
    exact Work.BoseFixB1.Clean.boxSqPart_nonneg hv (M := M) u
      (Submission.BoseGases.omC (Classical.choose h)) Φ
  -- ### the endgame
  have hVar' : Var = Pc - S ^ 2 + S := by rw [hVardef]; ring
  have hXp_eq' : Xp = (1 / 4) * (M1 / V ^ 2) * ((S + 1 - m) ^ 2 + (Pc - S ^ 2 + S) + 1) := by
    rw [hXpdef, hVar']
  set Sq : ℝ := Work.BoseFixB1.boxSqPart V ℓ A w ω Φ with hSqdef
  set Cross : ℝ := Work.BoseFixB1.boxCrossPart V ℓ A w₁ Φ with hCrossdef
  set Imp : ℝ := (1 / 4) * (M1 / V ^ 2) * ((S + 1 - m) ^ 2 + (Pc - S ^ 2 + S) + 1) with hImpdef
  set Cred : ℝ := Cc * _root_.BoseGases.a v * (μ + S / V) * nq with hCreddef
  have hSqnn' : 0 ≤ Sq := by rw [hSqdef]; exact hSqnn
  have hLb' : Cross ≥ 2 * μ * Pm - Xq - Xp := by rw [hCrossdef]; exact hLb
  have hXq_le' : Xq + μ * Qm ≤ Cred := by rw [hCreddef]; exact hXq_le
  have hgoal : Sq + Cross + Imp + Cred ≥ 2 * μ * Pm + μ * Qm := by
    rw [hImpdef]
    rw [hXp_eq'] at hLb'
    linarith [hSqnn', hLb', hXq_le']
  have hPorder : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * (Work.UBBInputs8.boxPInd V A i Φ x) * (fib (x i)))
      = Pm := by
    rw [hPmdef]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable N ℓ)
      (fun x _ => by ring)
  rw [hPorder]
  exact hgoal

end Work.BoseFixB1S
