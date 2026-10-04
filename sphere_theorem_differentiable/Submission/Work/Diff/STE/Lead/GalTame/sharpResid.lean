import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.mat_ENormSq_le_clean
import Submission.Work.Diff.STE.B3.Rres_eq_residualLow
import Submission.Work.Diff.STE.Lead.Gal.residualDataPsi
import Submission.Work.Diff.STE.Lead.GalTame.sup_pdList_le_of_energy
import Submission.Work.Diff.STE.GN_torus
import Submission.Work.Diff.STE.Lead.GalTame.Level
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Man.Sect
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Lead.GalTame.residGn.sharpResidAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

/-- **The `L²` (tame) energy bound for the local residual of the DeTurck transport.**

`residualLow D h j · a b` (`Work.Diff.STE.B3.residualLow`) is the lower-order residual of the
transport identity `R_j(P h) = Σ_{pq} (Gf⁻¹)_{pq} ∂_p∂_q (R_j h) + residualLow` of the DeTurck
operator in the Layer B3 components (see `Work.Diff.STE.B3.Rres_eq_residualLow`, axiom-clean).  It
is an explicit smooth function of `(z, mat, ∂mat)` — the `g₀`-orthonormal-frame chart matrix
`Mf = D.mat j h` and its first jet — and it vanishes identically off the closed `σ_j`-ball.

The claim is the `L²` bound for the `m`-th iterated partial derivative of this residual, for
`m ≤ k`, over the closed `σ_j`-ball (a ball inside the chart, cf. `B3Data.htarget`):

  `∫_{ball 0 (σ j)} ‖∂^β (residualLow)‖² ≤ CT · (1 + ENormB (m+1) h)`,

with `CT` uniform in the section `h`, the chart `j`, the frame indices `a b` and the multi-index
`β`.  The level `m + 1` is the natural one: `∂^m` of an explicit smooth function of the jet
`(mat, ∂mat)` involves the derivatives of `mat` up to order `m + 1`, and all lower levels are
dominated by the level `m + 1` in the composite energy `ENormB` (the Poincaré chain
`Level.ENormSq_Rper_le_succ`).

Note: only the FIRST-order bound `hjet` on `h`'s chart matrix is assumed (together with the
sandwich `lam g₀ ≤ h ≤ K g₀`, which bounds `mat` and `∂mat` pointwise on the ball); the higher
jets of `h` are controlled only through the *energy* `ENormB (·) h`.

Route.  (i) `residualLow` is supported in the closed `σ_j`-ball
(`residualLow_eq_zero_of_sigma_lt_gal`); (ii) `pN = pPhi(·,·,·,A,L,0)` is quadratic in `L = ∂mat`
with coefficients rational in `A = Gf`, and the remaining terms are affine in `∂mat`; all the
coefficients are pointwise bounded on the ball through `hjet`/`hell`/`hub`, the ellipticity window
and the fixed chart data; (iii) the `L²` energy of `∂^j mat` on the ball is controlled by
`Σ_{i,c,d} ENormSq j (D.Rper i h c d)` — apply `Work.Diff.STE.B3.mat_ENormSq_le_clean`
(axiom-clean) to a cut-off supported in the centre cube and `≡ 1` on the closed `2σ_j`-ball;
(iv) bound the products either by putting the lowest-order factors in `L^∞` (the torus Sobolev sup
bound `Work.Diff.STE.Lead.GalTame.sup_pdList_le_of_energy`) and the remaining factor in `L²`, or by
Gagliardo–Nirenberg interpolation (`Work.Diff.STE.GN_torus`, axiom-clean) together with Hölder's
inequality. -/
theorem sharpResid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : 1 ≤ k) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ CT : ℝ, 0 ≤ CT ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
            |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
          ∀ j : ι₀, ∀ (a b : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k)
            (β : Fin m → Fin (Module.finrank ℝ E)),
            ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ j),
              ‖Work.Diff.STE.pdVec m β
                (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ)) z‖ ^ 2
              ≤ CT * (1 + D.ENormB (m + 1) h) := by
  intro lam K hlam hK
  obtain ⟨C, hC0, hC⟩ := ResidGn.residStep (I := I) (M := M) D hLC lam K hlam hK
  refine ⟨1 + ∑ m' ∈ Finset.range (k + 1), ∑ j' : ι₀, (C j' m' + 1), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ m' ∈ Finset.range (k + 1), ∑ j' : ι₀, (C j' m' + 1) :=
      Finset.sum_nonneg fun m' _ => Finset.sum_nonneg fun j' _ => by linarith [hC0 j' m']
    linarith
  · intro h hsym hpos hsmooth hell hub hjet j a b m hm β
    have h1 := hC h hsym hpos hsmooth hell hub hjet j a b m β
    have hCT : C j m ≤ 1 + ∑ m' ∈ Finset.range (k + 1), ∑ j' : ι₀, (C j' m' + 1) := by
      have hle1 : C j m ≤ ∑ j' : ι₀, (C j' m + 1) :=
        le_trans (le_add_of_nonneg_right zero_le_one)
          (Finset.single_le_sum (f := fun j' : ι₀ => C j' m + 1)
            (fun j' _ => by linarith [hC0 j' m]) (Finset.mem_univ j))
      have hle2 : (∑ j' : ι₀, (C j' m + 1))
          ≤ ∑ m' ∈ Finset.range (k + 1), ∑ j' : ι₀, (C j' m' + 1) :=
        Finset.single_le_sum (f := fun m' => ∑ j' : ι₀, (C j' m' + 1))
          (fun m' _ => Finset.sum_nonneg fun j' _ => by linarith [hC0 j' m'])
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
      linarith
    have hEN : 0 ≤ 1 + D.ENormB (m + 1) h := by
      have hb := Work.Diff.STE.B3Data.ENormB_nonneg D (m + 1) h
        (fun i a b' => ResidGn.ENormSq_nonnegR (m + 1) (D.Rper i h a b'))
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hCT hEN)

end Work.Diff.STE.Lead.GalTame
