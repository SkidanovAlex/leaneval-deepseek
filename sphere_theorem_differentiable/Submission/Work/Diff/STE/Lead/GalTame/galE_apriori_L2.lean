import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.Defs
import Submission.Work.Diff.STE.Lead.Gal.hasDerivAt_galE
import Submission.Work.Diff.STE.Lead.Gal.galE_exp_bound
import Submission.Work.Diff.STE.Lead.Gal.galE_apriori
import Submission.Work.Diff.STE.Lead.Gal.galE_J_bounded
import Submission.Work.Diff.STE.Lead.Gal.galE_J_L2_bounded
import Submission.Work.Diff.STE.Lead.Gal.galE_ENormB_pair_abs_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

Critical-path piece of gal_uniform_v2 (H2387), on its tame L² route. The statement is H2387's own draft (GalTame/_stmtApriori.lean, elaborated cleanly on 3.22), dispatched top-level by the lead so that it runs now. Every analytic input is a HYPOTHESIS: the J-commutator hJ, the J-bound hJN, the sharp Gårding estimate hG and the low-order bound hLow. So this is a pure energy/ODE argument. Do not prove hG, hLow or hJ here; H2387 discharges them via GalTame/gardingSharp, GardDataL2 and B3/ENormB_pair_J_commutator_v2.
ROUTE. Write u = galState D ε (c t), ũ = J ρ ε u, P = deTurckSec(ũ). galE k = ENormB k u + ENormB 0 u.
1. hasDerivAt_galE (PROVED) together with genMap_galVF2 / isGalSol_of_galVF2 (Lead/Gal/Prelude, Lead/gal_uniform_v2) gives
   d/dt galE = 2·ENormB_pair k (J P) u + 2·ENormB_pair 0 (J P) u.
2. Level k: by hJ, ENormB_pair k (J P) u = ENormB_pair k P (J u) + err, with |err| ≤ CJ·√(E_{k−1}P + E_0 P)·√(E_k u) ≤ CJ·√(Cl(1 + E_{k+1} ũ))·√(E_k u), using hLow. Then hG gives 2·ENormB_pair k P ũ ≤ −lam'·E_{k+1} ũ + 2Cg(1 + E_k ũ).
3. Level 0: J is self-adjoint at level 0 (BPair_J_self_smooth / galE_ENormB_pair_zero_eq_BPair, PROVED). So ENormB_pair 0 (J P) u = ENormB_pair 0 P ũ ≤ √(E_0 P)·√(E_0 ũ) ≤ √(Cl(1 + E_{k+1} ũ))·√(E_0 ũ).
4. Young: absorb every √(1 + E_{k+1} ũ) factor into −lam'·E_{k+1} ũ / 2. Bound E_k ũ and E_0 ũ by C·galE k u through hJN plus BNorm_ENormB_equiv (BNorm_le_ENormB / ENormB_le_BNorm), or reuse the PROVED galE_J_bounded / galE_J_L2_bounded / galE_ENormB_pair_abs_le (Lead/Gal). Result: (galE + 1)' ≤ C·(galE + 1), with C independent of ε and of the level-k energy.
5. Comparison: galE_exp_bound (PROVED) gives galE(c t) ≤ (galE(c 0) + 1)·e^{Ct} − 1.
Reuse first: grep Submission/Work/Diff/STE/Lead/Gal and Lead/GalTame. Lead/Gal/galE_apriori.lean (H2387-L2745, cancelled as superseded; the file is kept and sorry-free, 452 lines) proves the SAME estimate for the pointwise-hjet route: galE_apriori_aux takes the commutator as hypothesis hcomm and calls gardingAssembly at about line 142. Adapt that proof: replace the gardingAssembly call with hG plus hLow, and drop hjet. Most of the 300 lines carry over. Import its helpers (galE_nonneg, ENormB_le_galE) instead of copying them. Run python3 REFS/tools/dupcheck.py . | grep galE before declare_proven. Prove directly; split at most once.
-/

namespace Work.Diff.STE.Lead.GalTame

open Classical LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
  Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Elementary arithmetic -/

/-- **Young's inequality in the square-root form used below.**  For `m, y ≥ 0`, `P ≥ 0` and
`lam > 0`, `P √m √y ≤ (lam/4) m + (P²/lam) y`.  (The standard `2uv ≤ u² + v²` applied to
`u = √lam √m`, `v = 2 P √y`; stated without division so that no square roots are normalised.) -/
private lemma young_sqrt_sq {m y P lam : ℝ} (hm : 0 ≤ m) (hy : 0 ≤ y) (hP : 0 ≤ P)
    (hlam : 0 < lam) :
    P * Real.sqrt m * Real.sqrt y ≤ (lam / 4) * m + (P ^ 2 / lam) * y := by
  have hrhs : 4 * lam * ((lam / 4) * m + (P ^ 2 / lam) * y) = lam ^ 2 * m + 4 * P ^ 2 * y := by
    field_simp
  have hkey : 4 * lam * (P * Real.sqrt m * Real.sqrt y)
      ≤ 4 * lam * ((lam / 4) * m + (P ^ 2 / lam) * y) := by
    rw [hrhs]
    have h2ab : 2 * (lam * Real.sqrt m) * (2 * P * Real.sqrt y)
        ≤ (lam * Real.sqrt m) ^ 2 + (2 * P * Real.sqrt y) ^ 2 := by
      nlinarith [sq_nonneg (lam * Real.sqrt m - 2 * P * Real.sqrt y)]
    have hexp : (lam * Real.sqrt m) ^ 2 + (2 * P * Real.sqrt y) ^ 2
        = lam ^ 2 * m + 4 * P ^ 2 * y := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hm, Real.sq_sqrt hy]
      ring
    rw [hexp] at h2ab
    nlinarith [h2ab]
  have hpos : 0 < 4 * lam := by linarith
  exact le_of_mul_le_mul_left hkey hpos

/-- `√(1 + m) ≤ 1 + √m` for `m ≥ 0`. -/
private lemma sqrt_one_add_le {m : ℝ} (hm : 0 ≤ m) :
    Real.sqrt (1 + m) ≤ 1 + Real.sqrt m := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hm, Real.sqrt_nonneg m]

/-- `√y ≤ 1 + y` for `y ≥ 0`. -/
private lemma sqrt_le_one_add {y : ℝ} (hy : 0 ≤ y) : Real.sqrt y ≤ 1 + y := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

/-- The physical energy `ENormSq` is nonnegative (a sum of integrals of squares). -/
private lemma ENormSq_nonneg_gal {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (f : (ι → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq k f := by
  rw [Work.Diff.STE.ENormSq]
  exact Finset.sum_nonneg fun l _ =>
    MeasureTheory.integral_nonneg fun x => by positivity

/-- **The arithmetic heart of the a priori estimate.**  From the two bounds
`L ≤ -(lam'/2) m + Cg (1 + κ y) + CJ √Cl √(1+m) √y` (Gårding plus commutator) and
`M ≤ √(C₀ Cl) √(1+m) √y` (level-`0` Cauchy–Schwarz), with `m, y ≥ 0` and all constants
nonnegative, one gets `L + M ≤ 2 K (1 + y)` with `K` as displayed — the factor `2` being the `2`
of `d/dt galE` and `K` the resulting growth rate. -/
private lemma apriori_arith {lam' Cg Cl CJ C0 kap m y : ℝ}
    (hlam' : 0 < lam') (hCg : 0 ≤ Cg) (hCl : 0 ≤ Cl) (hCJ : 0 ≤ CJ) (hC0 : 0 ≤ C0)
    (hkap : 0 ≤ kap) (hm : 0 ≤ m) (hy : 0 ≤ y) {L M : ℝ}
    (h1 : L ≤ -(lam' / 2) * m + Cg * (1 + kap * y)
        + CJ * Real.sqrt Cl * Real.sqrt (1 + m) * Real.sqrt y)
    (h2 : M ≤ Real.sqrt (C0 * Cl) * Real.sqrt (1 + m) * Real.sqrt y) :
    L + M ≤ (Cg * (1 + kap) + (CJ * Real.sqrt Cl + Real.sqrt (C0 * Cl))
        + (CJ * Real.sqrt Cl + Real.sqrt (C0 * Cl)) ^ 2 / lam') * (1 + y) := by
  set P : ℝ := CJ * Real.sqrt Cl + Real.sqrt (C0 * Cl) with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  have hsq1 : Real.sqrt (1 + m) ≤ 1 + Real.sqrt m := sqrt_one_add_le hm
  have hyoung : P * Real.sqrt m * Real.sqrt y ≤ (lam' / 4) * m + (P ^ 2 / lam') * y :=
    young_sqrt_sq hm hy hP0 hlam'
  have hsy : Real.sqrt y ≤ 1 + y := sqrt_le_one_add hy
  -- (1) combine the two bounds into one, with the common factor `P`
  have hsum : L + M ≤ -(lam' / 2) * m + Cg * (1 + kap * y)
      + P * (1 + Real.sqrt m) * Real.sqrt y := by
    have hsqy : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have hCJCl : 0 ≤ CJ * Real.sqrt Cl := by positivity
    have hC0Cl : 0 ≤ Real.sqrt (C0 * Cl) := Real.sqrt_nonneg _
    have e1 : CJ * Real.sqrt Cl * Real.sqrt (1 + m) * Real.sqrt y
        ≤ CJ * Real.sqrt Cl * (1 + Real.sqrt m) * Real.sqrt y := by
      calc CJ * Real.sqrt Cl * Real.sqrt (1 + m) * Real.sqrt y
          = (CJ * Real.sqrt Cl) * (Real.sqrt (1 + m) * Real.sqrt y) := by ring
        _ ≤ (CJ * Real.sqrt Cl) * ((1 + Real.sqrt m) * Real.sqrt y) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hsq1 hsqy) hCJCl
        _ = CJ * Real.sqrt Cl * (1 + Real.sqrt m) * Real.sqrt y := by ring
    have e2 : Real.sqrt (C0 * Cl) * Real.sqrt (1 + m) * Real.sqrt y
        ≤ Real.sqrt (C0 * Cl) * (1 + Real.sqrt m) * Real.sqrt y := by
      calc Real.sqrt (C0 * Cl) * Real.sqrt (1 + m) * Real.sqrt y
          = Real.sqrt (C0 * Cl) * (Real.sqrt (1 + m) * Real.sqrt y) := by ring
        _ ≤ Real.sqrt (C0 * Cl) * ((1 + Real.sqrt m) * Real.sqrt y) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hsq1 hsqy) hC0Cl
        _ = Real.sqrt (C0 * Cl) * (1 + Real.sqrt m) * Real.sqrt y := by ring
    have hPP : CJ * Real.sqrt Cl * (1 + Real.sqrt m) * Real.sqrt y
          + Real.sqrt (C0 * Cl) * (1 + Real.sqrt m) * Real.sqrt y
        = P * (1 + Real.sqrt m) * Real.sqrt y := by
      rw [hPdef]; ring
    linarith [h1, h2, e1, e2, hPP]
  -- (2) the three elementary estimates
  have hexp : P * (1 + Real.sqrt m) * Real.sqrt y
      = P * Real.sqrt y + P * Real.sqrt m * Real.sqrt y := by ring
  have hmono : Cg * (1 + kap * y) ≤ Cg * (1 + kap) * (1 + y) := by
    have h : (1 + kap * y) ≤ (1 + kap) * (1 + y) := by
      nlinarith [hkap, hy, mul_nonneg hkap hy]
    calc Cg * (1 + kap * y) ≤ Cg * ((1 + kap) * (1 + y)) := mul_le_mul_of_nonneg_left h hCg
      _ = Cg * (1 + kap) * (1 + y) := by ring
  have hPsy : P * Real.sqrt y ≤ P * (1 + y) := mul_le_mul_of_nonneg_left hsy hP0
  have hQ0 : 0 ≤ P ^ 2 / lam' := div_nonneg (sq_nonneg P) hlam'.le
  have hP2y : (P ^ 2 / lam') * y ≤ (P ^ 2 / lam') * (1 + y) :=
    mul_le_mul_of_nonneg_left (by linarith) hQ0
  have hneg : -(lam' / 4) * m ≤ 0 := by nlinarith
  have hbound : L + M ≤ (Cg * (1 + kap) + P + P ^ 2 / lam') * (1 + y) := by
    have h3 : -(lam' / 2) * m + Cg * (1 + kap * y) + P * Real.sqrt y
          + P * Real.sqrt m * Real.sqrt y
        ≤ (Cg * (1 + kap) + P + P ^ 2 / lam') * (1 + y) := by
      have hK : (Cg * (1 + kap) + P + P ^ 2 / lam') * (1 + y)
          = Cg * (1 + kap) * (1 + y) + P * (1 + y) + (P ^ 2 / lam') * (1 + y) := by ring
      rw [hK]
      linarith [hmono, hPsy, hyoung, hP2y, hneg]
    linarith [hsum, hexp, h3]
  rw [hPdef] at hbound
  exact hbound

/-- **Grönwall's comparison in the form used below**: if `y` has derivative `y'` on `[0,T)` and
`y' ≤ C (1 + y)` there with `C ≥ 0`, then `y t ≤ (y 0 + 1) e^{C t} - 1` for `t ∈ [0,T)`.
(Reduced to `gronwall_linear_bound` on the slightly shorter interval `[0, (t+T)/2]`, which turns
the one-sided `HasDerivAt` hypothesis on the half-open interval into the
`HasDerivWithinAt` hypothesis on the closed interval.) -/
private lemma galE_gronwall {y y' : ℝ → ℝ} {T C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (y' t) t)
    (hineq : ∀ t ∈ Set.Ico (0 : ℝ) T, y' t ≤ C * (1 + y t)) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, y t ≤ (y 0 + 1) * Real.exp (C * t) - 1 := by
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  have hT0 : 0 < T := lt_of_le_of_lt ht0 htT
  set T' : ℝ := (t + T) / 2 with hT'def
  have htT' : t ≤ T' := by rw [hT'def]; linarith
  have hT'T : T' < T := by rw [hT'def]; linarith
  have hderiv' : ∀ s ∈ Set.Icc 0 T', HasDerivWithinAt y (y' s) (Set.Icc 0 T') s := by
    intro s hs
    exact (hderiv s ⟨hs.1, lt_of_le_of_lt hs.2 hT'T⟩).hasDerivWithinAt
  have hineq' : ∀ s ∈ Set.Icc 0 T', y' s ≤ C * (1 + y s) := fun s hs =>
    hineq s ⟨hs.1, lt_of_le_of_lt hs.2 hT'T⟩
  exact Work.Diff.STE.gronwall_linear_bound hC hderiv' hineq' (le_refl (y 0)) t ⟨ht0, htT'⟩

theorem galE_apriori_L2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (k k₀ : ℕ) (hk : Module.finrank ℝ E + 12 < 2 * k)
    (hk₀ : Module.finrank ℝ E + 4 < 2 * k₀)
    (lam K B₀ : ℝ) (hlam : 0 < lam) (hK : 0 < K) (hB₀ : 0 ≤ B₀)
    (CJ : ℝ) (hCJ : 0 ≤ CJ)
    (hJ : ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (f u : Work.Diff.STE.Bil (I := I) (M := M)),
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b)) →
        (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b)) →
        |D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)|
          ≤ CJ * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
            * Real.sqrt (D.ENormB k u))
    (CJN : ℕ → ℝ) (hCJN : ∀ m, 0 ≤ CJN m)
    (hJN : ∀ (m : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h →
        D.BNorm m (D.J ρ ε h) ≤ CJN m * D.BNorm m h)
    (lam' Cg Cl : ℝ) (hlam' : 0 < lam') (hCg : 0 ≤ Cg) (hCl : 0 ≤ Cl)
    (hG : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v),
        D.ENormB k₀ h + D.ENormB 0 h ≤ B₀ →
        D.ENormB_pair k
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
          ≤ -(lam' / 2) * D.ENormB (k + 1) h + Cg * (1 + D.ENormB k h))
    (hLow : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v),
        D.ENormB k₀ h + D.ENormB 0 h ≤ B₀ →
        D.ENormB (k - 1)
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
          + D.ENormB 0
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
          ≤ Cl * (1 + D.ENormB (k + 1) h)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v ≤ K * g₀.inner x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        D.ENormB k₀ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t)))
          + D.ENormB 0 (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) ≤ B₀) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        Work.Diff.STE.Lead.galE D k ε (c t)
          ≤ (Work.Diff.STE.Lead.galE D k ε (c 0) + 1) * Real.exp (C * t) - 1 := by
  classical
  have hk' : Module.finrank ℝ E < 2 * k := by omega
  obtain ⟨kap, hkap0, hJbk⟩ := Work.Diff.STE.Lead.Gal.galE_J_bounded (I := I) (M := M) D ρ hρ k hk'
  obtain ⟨C0, hC00, hJb0⟩ := Work.Diff.STE.Lead.Gal.galE_J_L2_bounded (I := I) (M := M) D ρ hρ
  set P : ℝ := CJ * Real.sqrt Cl + Real.sqrt (C0 * Cl) with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  set Cf : ℝ := 2 * (Cg * (1 + kap) + P + P ^ 2 / lam') with hCfdef
  have hCf0 : 0 ≤ Cf := by rw [hCfdef]; positivity
  refine ⟨Cf, hCf0, ?_⟩
  intro ε hε hε1 c T hT hder hpos hlow hup hB0 t ht
  set y : ℝ → ℝ := fun s => Work.Diff.STE.Lead.galE D k ε (c s) with hydef
  set y' : ℝ → ℝ := fun s =>
    2 * (D.ENormB_pair k
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε
            (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c s)))
          (Submission.Diff.STEGal.galState D ε (c s)) +
         D.ENormB_pair 0
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε
            (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c s)))
          (Submission.Diff.STEGal.galState D ε (c s))) with hy'def
  have hderiv : ∀ s ∈ Set.Ico (0 : ℝ) T, HasDerivAt y (y' s) s := by
    intro s hs
    have h := Work.Diff.STE.Lead.Gal.hasDerivAt_galE (I := I) (M := M) D k ε hg (hder s hs)
    rw [hydef, hy'def]
    exact h
  have hineq : ∀ s ∈ Set.Ico (0 : ℝ) T, y' s ≤ Cf * (1 + y s) := by
    intro s hs
    -- the state, the foreground, and the DeTurck tensor of the foreground
    let u : Work.Diff.STE.Bil (I := I) (M := M) := Submission.Diff.STEGal.galState D ε (c s)
    let v : Work.Diff.STE.Bil (I := I) (M := M) := D.J ρ ε u
    have hsym_u : ∀ (x : M) (p q : TangentSpace I x), u x p q = u x q p :=
      isSymm_galState D ε (c s)
    have hcd_u : Work.Diff.STE.D.ChartData (I := I) (M := M) u :=
      chartData_galState D ε hg (c s)
    have hsym_v : ∀ (x : M) (p q : TangentSpace I x), v x p q = v x q p :=
      isSymm_J D ρ ε hε hρ0 u hsym_u
    have hcd_v : Work.Diff.STE.D.ChartData (I := I) (M := M) v :=
      chartData_J D ρ ε hε hρ0 u hsym_u
    have hpos_v : ∀ (x : M) (p : TangentSpace I x), p ≠ 0 → 0 < v x p p := hpos s hs
    let f : Work.Diff.STE.Bil (I := I) (M := M) :=
      Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ v hsym_v hpos_v hcd_v
    -- component smoothness of the three sections
    have hsm_u : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b) :=
      Work.Diff.STE.Lead.Gal.galE_sm_galState D ε hg (c s)
    have hcd_f : Work.Diff.STE.D.ChartData (I := I) (M := M) f :=
      Work.Diff.STE.B3.chartData_deTurckSec (I := I) (g₀ := g₀) hLC v hsym_v hpos_v hcd_v
    have hsm_f : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b) :=
      fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData D f hcd_f i a b
    have hsm_Jf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (D.J ρ ε f) a b) :=
      fun i a b => Work.Diff.STE.Lead.Gal.R_J_contDiff_noInst D ρ f hsm_f hρ i a b ε
    -- nonnegativity of the energies
    have hEk0 : 0 ≤ D.ENormB k u :=
      Work.Diff.STE.B3Data.ENormB_nonneg D k u (fun i a b => ENormSq_nonneg_gal k _)
    have hE00 : 0 ≤ D.ENormB 0 u :=
      Work.Diff.STE.B3Data.ENormB_nonneg D 0 u (fun i a b => ENormSq_nonneg_gal 0 _)
    have hm10 : 0 ≤ D.ENormB (k + 1) v :=
      Work.Diff.STE.B3Data.ENormB_nonneg D (k + 1) v (fun i a b => ENormSq_nonneg_gal (k + 1) _)
    have hk1f0 : 0 ≤ D.ENormB (k - 1) f :=
      Work.Diff.STE.B3Data.ENormB_nonneg D (k - 1) f (fun i a b => ENormSq_nonneg_gal (k - 1) _)
    have h0f0 : 0 ≤ D.ENormB 0 f :=
      Work.Diff.STE.B3Data.ENormB_nonneg D 0 f (fun i a b => ENormSq_nonneg_gal 0 _)
    have hy_eq : y s = D.ENormB k u + D.ENormB 0 u := rfl
    have hy0 : 0 ≤ y s := by rw [hy_eq]; linarith
    -- the two mollifier bounds at this state
    have hkv : D.ENormB k v ≤ kap * y s := by
      have h := hJbk ε hε hε1 u hsm_u
      rw [hy_eq]
      exact h
    have hE0_Jf : D.ENormB 0 (D.J ρ ε f) ≤ C0 * D.ENormB 0 f := hJb0 ε hε hε1 f hsm_f
    -- the two Gårding-type inputs at the foreground `v`
    have hGv := hG v hsym_v hpos_v hcd_v (hlow s hs) (hup s hs) (hB0 s hs)
    have hLv := hLow v hsym_v hpos_v hcd_v (hlow s hs) (hup s hs) (hB0 s hs)
    -- the commutator estimate
    have hcom := hJ ε hε hε1 f u hsm_f hsm_u
    -- the two square-root comparisons with the energy `y s`
    have hsqrt_Ek : Real.sqrt (D.ENormB k u) ≤ Real.sqrt (y s) := by
      refine Real.sqrt_le_sqrt ?_
      rw [hy_eq]; linarith
    have hsqrt_E0 : Real.sqrt (D.ENormB 0 u) ≤ Real.sqrt (y s) := by
      refine Real.sqrt_le_sqrt ?_
      rw [hy_eq]; linarith
    -- ### level `k`
    have h1 : D.ENormB_pair k (D.J ρ ε f) u
        ≤ -(lam' / 2) * D.ENormB (k + 1) v + Cg * (1 + kap * y s)
          + CJ * Real.sqrt Cl * Real.sqrt (1 + D.ENormB (k + 1) v) * Real.sqrt (y s) := by
      have hcom' : D.ENormB_pair k (D.J ρ ε f) u
          ≤ D.ENormB_pair k f v
            + CJ * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
              * Real.sqrt (D.ENormB k u) :=
        sub_le_iff_le_add'.mp (abs_le.mp hcom).2
      have hsqrt_low : Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
          ≤ Real.sqrt Cl * Real.sqrt (1 + D.ENormB (k + 1) v) := by
        rw [← Real.sqrt_mul hCl]
        exact Real.sqrt_le_sqrt hLv
      have herr : CJ * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f) * Real.sqrt (D.ENormB k u)
          ≤ CJ * Real.sqrt Cl * Real.sqrt (1 + D.ENormB (k + 1) v) * Real.sqrt (y s) := by
        calc CJ * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f) * Real.sqrt (D.ENormB k u)
            = CJ * (Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
                * Real.sqrt (D.ENormB k u)) := by ring
          _ ≤ CJ * ((Real.sqrt Cl * Real.sqrt (1 + D.ENormB (k + 1) v)) * Real.sqrt (y s)) := by
              refine mul_le_mul_of_nonneg_left ?_ hCJ
              exact mul_le_mul hsqrt_low hsqrt_Ek (Real.sqrt_nonneg _)
                (by positivity)
          _ = CJ * Real.sqrt Cl * Real.sqrt (1 + D.ENormB (k + 1) v) * Real.sqrt (y s) := by ring
      have hgard : D.ENormB_pair k f v
          ≤ -(lam' / 2) * D.ENormB (k + 1) v + Cg * (1 + kap * y s) := by
        have h1'' : Cg * (1 + D.ENormB k v) ≤ Cg * (1 + kap * y s) := by
          refine mul_le_mul_of_nonneg_left ?_ hCg
          linarith [hkv]
        linarith [hGv, h1'']
      linarith [hcom', herr, hgard]
    -- ### level `0`
    have h2 : D.ENormB_pair 0 (D.J ρ ε f) u
        ≤ Real.sqrt (C0 * Cl) * Real.sqrt (1 + D.ENormB (k + 1) v) * Real.sqrt (y s) := by
      have hE0_f : D.ENormB 0 f ≤ Cl * (1 + D.ENormB (k + 1) v) := by
        linarith [hLv, hk1f0]
      have hcs0 := Work.Diff.STE.Lead.Gal.galE_ENormB_pair_abs_le (I := I) (M := M) D 0
        (D.J ρ ε f) u hsm_Jf hsm_u
      calc D.ENormB_pair 0 (D.J ρ ε f) u
          ≤ |D.ENormB_pair 0 (D.J ρ ε f) u| := le_abs_self _
        _ ≤ Real.sqrt (D.ENormB 0 (D.J ρ ε f)) * Real.sqrt (D.ENormB 0 u) := hcs0
        _ ≤ Real.sqrt (C0 * D.ENormB 0 f) * Real.sqrt (y s) := by
              refine mul_le_mul (Real.sqrt_le_sqrt hE0_Jf) hsqrt_E0
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (C0 * (Cl * (1 + D.ENormB (k + 1) v))) * Real.sqrt (y s) := by
              refine mul_le_mul ?_ le_rfl (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
              exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE0_f hC00)
        _ = Real.sqrt (C0 * Cl) * Real.sqrt (1 + D.ENormB (k + 1) v) * Real.sqrt (y s) := by
              rw [show C0 * (Cl * (1 + D.ENormB (k + 1) v))
                    = (C0 * Cl) * (1 + D.ENormB (k + 1) v) by ring,
                  Real.sqrt_mul (mul_nonneg hC00 hCl)]
    -- ### assembly
    have harith := apriori_arith (lam' := lam') (Cg := Cg) (Cl := Cl) (CJ := CJ) (C0 := C0)
      (kap := kap) (m := D.ENormB (k + 1) v) (y := y s) hlam' hCg hCl hCJ hC00 hkap0 hm10 hy0 h1 h2
    have hy'expr : y' s = 2 * (D.ENormB_pair k (D.J ρ ε f) u + D.ENormB_pair 0 (D.J ρ ε f) u) := by
      simp only [hy'def, Work.Diff.STE.Lead.genMap_galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0
        (c s) (hpos s hs)]
      rfl
    rw [hy'expr, hCfdef]
    linarith [harith]
  have ht' := galE_gronwall hCf0 hderiv hineq t ht
  simpa only [hydef] using ht'

end

end Work.Diff.STE.Lead.GalTame
