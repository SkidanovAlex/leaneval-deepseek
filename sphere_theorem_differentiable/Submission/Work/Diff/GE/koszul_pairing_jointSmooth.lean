import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.kosDefs
import Submission.Work.Diff.EXT.covK_metric_pairing_family
import Submission.Work.Diff.EXT.covK_mlieBracket_family
import Submission.Work.Diff.EXT.covK_spatialDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the Koszul pairing `⟪∇^{G t}_{X t} σ t, Z t⟫_{G t}`

`Work.Diff.GE.koszul_pairing_jointSmooth`: for a jointly smooth family of metrics `G` on an open
set `V ⊆ ℝ × M` (`Work.Diff.EXT.JointMet`) and jointly smooth families of tangent fields `σ`, `X`,
`Z` (`Work.Diff.EXT.JointField`), the function

`(t,y) ↦ (G t).inner y (∇^{G t}_{X t} σ t)(y) (Z t y)`

is jointly `C^∞` on `V`.

ROUTE.  On `V` the pairing equals the Koszul expression `Work.Diff.EXT.kosGen`
(`Work.Diff.EXT.lcOf_pairing_eq_kosGen`, i.e. Mathlib's `leviCivitaConnection_apply_inner` with the
instance inner product transported to `G t`), whose six terms are jointly smooth:

* the three metric pairings: `Work.Diff.EXT.covK_metric_pairing_family`;
* the three directional derivatives of those pairings (along `X`, `σ`, `Z` respectively):
  `Work.Diff.EXT.covK_spatialDeriv`;
* the three bracket terms: `Work.Diff.EXT.covK_mlieBracket_family` (joint smoothness of
  `VectorField.mlieBracket`) followed by `Work.Diff.EXT.covK_metric_pairing_family`.

Smoothness is then transported through the pointwise Koszul identity.
-/

namespace Work.Diff.GE

set_option maxHeartbeats 1000000

theorem koszul_pairing_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {V : Set (ℝ × M)} (hV : IsOpen V)
    (hG : Work.Diff.EXT.JointMet G V)
    {σ X Z : ℝ → Work.Diff.EXT.TField (I := I) (M := M)}
    (hσ : Work.Diff.EXT.JointField σ V) (hX : Work.Diff.EXT.JointField X V)
    (hZ : Work.Diff.EXT.JointField Z V) :
    ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (G p.1).inner p.2
        (Submission.Diff.lcOf (G p.1) (σ p.1) p.2 (X p.1 p.2)) (Z p.1 p.2)) V := by
  -- the three metric pairings appearing in the Koszul formula
  have hA := Work.Diff.EXT.covK_metric_pairing_family (I := I) hG hσ hZ
  have hB := Work.Diff.EXT.covK_metric_pairing_family (I := I) hG hZ hX
  have hC := Work.Diff.EXT.covK_metric_pairing_family (I := I) hG hX hσ
  -- the three directional derivatives of those pairings
  have hd1 := Work.Diff.EXT.covK_spatialDeriv (I := I) (M := M) (V := V)
    (Φ := fun t y => (G t).inner y (σ t y) (Z t y)) hV hA hX
  have hd2 := Work.Diff.EXT.covK_spatialDeriv (I := I) (M := M) (V := V)
    (Φ := fun t y => (G t).inner y (Z t y) (X t y)) hV hB hσ
  have hd3 := Work.Diff.EXT.covK_spatialDeriv (I := I) (M := M) (V := V)
    (Φ := fun t y => (G t).inner y (X t y) (σ t y)) hV hC hZ
  -- the three Lie brackets
  have hb1 := Work.Diff.EXT.covK_mlieBracket_family (I := I) (M := M) hV hX hZ
  have hb2 := Work.Diff.EXT.covK_mlieBracket_family (I := I) (M := M) hV hσ hX
  have hb3 := Work.Diff.EXT.covK_mlieBracket_family (I := I) (M := M) hV hZ hσ
  -- the three bracket terms
  have ht4 := Work.Diff.EXT.covK_metric_pairing_family (I := I) hG hσ hb1
  have ht5 := Work.Diff.EXT.covK_metric_pairing_family (I := I) hG hZ hb2
  have ht6 := Work.Diff.EXT.covK_metric_pairing_family (I := I) hG hX hb3
  -- assemble the (unhalved) Koszul expression
  have hsum0 := ((((hd1.add hd2).sub hd3).sub ht4).sub ht5).add ht6
  have hsum : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ (1 / 2 : ℝ) * (
          mvfderiv I (fun y' : M ↦ (G p.1).inner y' (σ p.1 y') (Z p.1 y')) p.2 (X p.1 p.2)
        + mvfderiv I (fun y' : M ↦ (G p.1).inner y' (Z p.1 y') (X p.1 y')) p.2 (σ p.1 p.2)
        - mvfderiv I (fun y' : M ↦ (G p.1).inner y' (X p.1 y') (σ p.1 y')) p.2 (Z p.1 p.2)
        - (G p.1).inner p.2 (σ p.1 p.2) (VectorField.mlieBracket I (X p.1) (Z p.1) p.2)
        - (G p.1).inner p.2 (Z p.1 p.2) (VectorField.mlieBracket I (σ p.1) (X p.1) p.2)
        + (G p.1).inner p.2 (X p.1 p.2) (VectorField.mlieBracket I (Z p.1) (σ p.1) p.2))) V := by
    simpa [div_eq_mul_inv, mul_comm] using hsum0.div_const (2 : ℝ)
  -- identify it with the Koszul expression `kosGen`
  have hK : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun p : ℝ × M ↦
        Work.Diff.EXT.kosGen (I := I) G (X p.1) (σ p.1) (Z p.1) p.1 p.2) V :=
    hsum.congr (fun p _ => by simp only [Work.Diff.EXT.kosGen])
  -- and with the pairing of the covariant derivative through the pointwise Koszul formula
  refine hK.congr (fun p hp => ?_)
  simpa only [Work.Diff.EXT.kosGen] using
    (Work.Diff.EXT.lcOf_pairing_eq_kosGen (I := I) G (X p.1) (σ p.1) (Z p.1) p.1
      (Work.Diff.EXT.contMDiffAt_slice hV hX hp)
      (Work.Diff.EXT.contMDiffAt_slice hV hσ hp)
      (Work.Diff.EXT.contMDiffAt_slice hV hZ hp))

end Work.Diff.GE
