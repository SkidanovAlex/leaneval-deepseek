import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.QkDef
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.CPair_eq_L2re_periodisation
import Submission.Work.Diff.STE.B3.BPair_J_self_smooth
import Submission.Work.Diff.STE.B3.flat_diag_pairing_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart term of the commutator pairing, written in the *flat* (periodised) vocabulary

The assembly of `Work.Diff.STE.B3.ENormB_pair_J_commutator_v2` produces the difference

  `CPair_l (S_l (R_l f), R_l (Q u)) − CPair_l (S_l (R_l (Q f)), R_l u)`

of component pairings, where `S_l = B3Data.STruncR ρ ε` is the Friedrichs cutoff (a **real** Fourier
multiplier) applied to the *localised* component, while the whole flat symbol calculus
(`SymCalc*`, `SymCalcStep5.lapPow`, `SymCalcStep7`) knows only operators acting on
**periodisations** `Rper_l h`, i.e. `flatCut ρ ε (Rper_l h)`.

This file performs that bookkeeping in full generality for a single chart `l`:

  `CPair_l (S_l (R_l f), R_l (Q u)) = Σ_{a b} L2re (Rper_l f a b) (flatCut ρ ε (Rper_l (Q u) a b))`

and the same with `f, u` replaced by `Q f, u`; subtracting the two identities gives the target.

The proof is a single-chart computation.  For a real function `p` supported in the open centred
cube, the periodisation `perF p` is a smooth `1`-periodic function agreeing with `p` on the cube
(`perF_self`), and `STruncR ρ ε p = (flatCut ρ ε (perF p)).re` (both sides unfold to the real part
of the Fourier series with coefficients `ρ (ε • m) ĝ(m)`).  Hence, with
`c := trunc ρ ε (fourierCoeff (perF q))`:

* `∫_{cube} (S p) q = ∫_{cube} p (S q) = (Σ_m c m · conj (fourierCoeff (perF p) m)).re`
  (self-adjointness `STruncR_selfadjoint_smooth`, the fundamental-domain identity
  `fd_unitCube_centreCube_real` and Parseval `integral_seriesFun_re_mul_perF`);
* `L2re (perF p) (seriesFun c) = (Σ_m c m · conj (fourierCoeff (perF p) m)).re` by Parseval
  (`L2re_seriesFun_eq`) and the symmetry `Re (a conj b) = Re (b conj a)`, which is legitimate
  because the multiplier family `ρ (ε • m)` is **real**.

No manifold hypothesis is used in the single-chart computation (only the support of the localised
components and their smoothness), so the statements below are made for an arbitrary finite
dimensional real normed space; the target is then an immediate instantiation.
-/

noncomputable section

open MeasureTheory BigOperators
open scoped ComplexConjugate

namespace Work.Diff.STE.B3.VarCoef

/-- **One component of the chart term.**  For real `p`, `q` supported in the open centred cube and
smooth, the Friedrichs cutoff of `p` paired with `q` over the centred cube is the `L²` pairing of
the periodisation of `p` against the *flat* cutoff `flatCut ρ ε` of the periodisation of `q`.

(Only the smoothness of `p` and `q` is used, to make their periodisations smooth `1`-periodic
functions and their Fourier coefficients `ℓ¹`.) -/
private lemma integral_ccube_STruncR_mul_eq_L2re_flatCut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (p q : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hps : Function.support p ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : Function.support q ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :
    (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
        Work.Diff.STE.B3Data.STruncR ρ ε p z * q z)
      = Work.Diff.STE.L2re (Work.Diff.STE.B3.perF p)
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.perF q)) := by
  classical
  have hsum_p : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m‖) :=
    Work.Diff.STE.B3.perF_summable p hp hps
  have hsum_q : Summable (fun m : Fin (Module.finrank ℝ E) → ℤ =>
      ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF q) m‖) :=
    Work.Diff.STE.B3.perF_summable q hq hqs
  set c := Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF q))
    with hcdef
  have hc : Summable (fun m => ‖c m‖) :=
    Work.Diff.STE.B3.summable_trunc_norm ρ hρ ε _ hsum_q
  -- ## Step 1: the integral against the supported factor, with the multiplier on the `q`-side
  have hInt : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
        p z * Work.Diff.STE.B3Data.STruncR ρ ε q z)
      = (∑' m, c m * star (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m)).re := by
    have h0 : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          p z * Work.Diff.STE.B3Data.STruncR ρ ε q z)
        = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            p z * (Work.Diff.STE.seriesFun c z).re := rfl
    have h1 : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          p z * (Work.Diff.STE.seriesFun c z).re)
        = ∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            p z * (Work.Diff.STE.seriesFun c z).re :=
      Work.Diff.STE.B3.setIntegral_centreCube_eq_openCube_of_forall_eq_zero _ _ (fun z hz => by
        have hz0 : p z = 0 := by
          by_contra hne
          exact hz (hps (Function.mem_support.mpr hne))
        rw [hz0, zero_mul])
    have h2 : (∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            p z * (Work.Diff.STE.seriesFun c z).re)
        = ∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re := by
      refine MeasureTheory.setIntegral_congr_fun
        (Work.Diff.STE.B3.measurableSet_openCube (E := E)) (fun z hz => ?_)
      rw [Work.Diff.STE.B3.perF_self p hp hps z
        (fun i => Set.mem_pi.mp hz i (Set.mem_univ i))]
      simp
    have h3 : (∫ z in Set.pi Set.univ
            (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)),
            (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re)
        = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re :=
      Work.Diff.STE.B3.setIntegral_openCube_eq_centreCube (E := E)
        (fun z => (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re)
    have hper4 : Work.Diff.STE.Periodic1
        (fun z => (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re) := by
      intro i z
      show (Work.Diff.STE.B3.perF p (z + Pi.single i 1)).re
            * (Work.Diff.STE.seriesFun c (z + Pi.single i 1)).re
          = (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re
      rw [show Work.Diff.STE.B3.perF p (z + Pi.single i 1) = Work.Diff.STE.B3.perF p z from
            Work.Diff.STE.B3.perF_periodic p i z,
          show (Work.Diff.STE.seriesFun c (z + Pi.single i 1)).re
              = (Work.Diff.STE.seriesFun c z).re from
            congrArg Complex.re (Work.Diff.STE.flat.periodic1_seriesFun c i z)]
    have hcont4 : Continuous
        (fun z => (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re) :=
      (Complex.continuous_re.comp (Work.Diff.STE.B3.perF_contDiff p hp hps).continuous).mul
        (Complex.continuous_re.comp
          (Work.Diff.STE.flat.continuous_seriesFun_of_summable c hc))
    have h4 : (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
            (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re)
        = ∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re :=
      (Work.Diff.STE.B3.fd_unitCube_centreCube_real
        (fun z => (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re)
        hper4 hcont4).symm
    have h5 : (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re)
        = (∑' m, c m * star (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m)).re := by
      rw [show (∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (Work.Diff.STE.B3.perF p z).re * (Work.Diff.STE.seriesFun c z).re)
          = ∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
            (Work.Diff.STE.seriesFun c z).re * (Work.Diff.STE.B3.perF p z).re from
        MeasureTheory.setIntegral_congr_fun
          (Work.Diff.STE.B3.measurableSet_unitCube' (E := E)) (fun z _ => mul_comm _ _)]
      exact Work.Diff.STE.B3.integral_seriesFun_re_mul_perF p hp hps c hc
    rw [h0, h1, h2, h3, h4, h5]
  -- ## Step 2: the same coefficient pairing, now from the `L²` pairing of the periodisations
  have hL2re : Work.Diff.STE.L2re (Work.Diff.STE.B3.perF p) (Work.Diff.STE.seriesFun c)
      = (∑' m, c m * star (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m)).re := by
    rw [Work.Diff.STE.B3.L2re_seriesFun_eq (Work.Diff.STE.B3.perF p)
      (Work.Diff.STE.B3.perF_contDiff p hp hps) (Work.Diff.STE.B3.perF_periodic p) c hc]
    have hsum1 : Summable (fun m =>
        Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m * star (c m)) := by
      have hK : ∀ m, ‖c m‖ ≤ ∑' m, ‖c m‖ :=
        fun m => hc.le_tsum m (fun _ _ => norm_nonneg _)
      refine Summable.of_norm ?_
      have hnorm : (fun m =>
            ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m * star (c m)‖)
          = fun m => ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m‖ * ‖c m‖ := by
        funext m
        rw [norm_mul, norm_star]
      rw [hnorm]
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun m => mul_le_mul_of_nonneg_left (hK m) (norm_nonneg _)) (hsum_p.mul_right _)
    have hsum2 : Summable (fun m =>
        c m * star (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m)) := by
      have hK : ∀ m, ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m‖
          ≤ ∑' m, ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m‖ :=
        fun m => hsum_p.le_tsum m (fun _ _ => norm_nonneg _)
      refine Summable.of_norm ?_
      have hnorm : (fun m =>
            ‖c m * star (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m)‖)
          = fun m => ‖c m‖ * ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perF p) m‖ := by
        funext m
        rw [norm_mul, norm_star]
      rw [hnorm]
      refine Summable.of_nonneg_of_le (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun m => mul_le_mul_of_nonneg_left (hK m) (norm_nonneg _)) (hc.mul_right _)
    rw [Complex.re_tsum hsum1, Complex.re_tsum hsum2]
    exact tsum_congr (fun m => Work.Diff.STE.B3.re_mul_star_comm _ _)
  -- ## Conclusion: self-adjointness of the cutoff plus Step 1, then Step 2
  have hS := Work.Diff.STE.B3.STruncR_selfadjoint_smooth ρ hρ ε p q hp hps hq hqs
  rw [hS, hInt]
  exact hL2re.symm

/-- **The chart term, component-wise, in the flat vocabulary.**  For two families `p`, `q` of real
smooth functions supported in the open centred cube, the component pairing of the Friedrichs
cutoffs of `p` against `q` is the sum of the flat `L²` pairings of the periodisations of `p` against
the flat cutoffs of the periodisations of `q`. -/
theorem CPair_STruncR_eq_L2re_flatCut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι₀ : Type*} (i : ι₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (ε : ℝ)
    (p q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hp : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (p a b))
    (hps : ∀ a b, Function.support (p a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hq : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (q a b))
    (hqs : ∀ a b, Function.support (q a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2))) :
    Work.Diff.STE.B3Data.CPair (E := E) i
        (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (p a b) z) q
      = ∑ a, ∑ b, Work.Diff.STE.L2re (Work.Diff.STE.B3.perF (p a b))
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.perF (q a b))) := by
  rw [Work.Diff.STE.B3Data.CPair]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  exact integral_ccube_STruncR_mul_eq_L2re_flatCut ρ hρ ε (p a b) (q a b)
    (hp a b) (hps a b) (hq a b) (hqs a b)

theorem CPair_chart_term_eq_periodised
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) (f u : Work.Diff.STE.Bil (I := I) (M := M))
    (hf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i f a b))
    (hu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i u a b))
    (hQf : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Work.Diff.STE.B3.Qk D k f) a b))
    (hQu : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i (Work.Diff.STE.B3.Qk D k u) a b))
    (l : ι₀) :
    (Work.Diff.STE.B3Data.CPair (E := E) l
        (fun a b z => Work.Diff.STE.B3Data.STruncR (E := E) ρ ε (D.R l f a b) z)
        (D.R l (Work.Diff.STE.B3.Qk D k u))
      - Work.Diff.STE.B3Data.CPair (E := E) l
        (fun a b z => Work.Diff.STE.B3Data.STruncR (E := E) ρ ε
          (D.R l (Work.Diff.STE.B3.Qk D k f) a b) z) (D.R l u))
    = ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.L2re (D.Rper l f a b)
            (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (D.Rper l (Work.Diff.STE.B3.Qk D k u) a b)))
        - ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
            Work.Diff.STE.L2re (D.Rper l (Work.Diff.STE.B3.Qk D k f) a b)
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (D.Rper l u a b))) := by
  have h1 : Work.Diff.STE.B3Data.CPair (E := E) l
        (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε (D.R l f a b) z)
        (D.R l (Work.Diff.STE.B3.Qk D k u))
      = ∑ a, ∑ b, Work.Diff.STE.L2re (Work.Diff.STE.B3.perF (D.R l f a b))
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.perF (D.R l (Work.Diff.STE.B3.Qk D k u) a b))) :=
    CPair_STruncR_eq_L2re_flatCut (E := E) l ρ hρ ε (D.R l f)
      (D.R l (Work.Diff.STE.B3.Qk D k u))
      (fun a b => hf l a b) (fun a b => Work.Diff.STE.B3.support_R_subset D l f a b)
      (fun a b => hQu l a b)
      (fun a b => Work.Diff.STE.B3.support_R_subset D l (Work.Diff.STE.B3.Qk D k u) a b)
  have h2 : Work.Diff.STE.B3Data.CPair (E := E) l
        (fun a b z => Work.Diff.STE.B3Data.STruncR ρ ε
          (D.R l (Work.Diff.STE.B3.Qk D k f) a b) z)
        (D.R l u)
      = ∑ a, ∑ b, Work.Diff.STE.L2re (Work.Diff.STE.B3.perF (D.R l (Work.Diff.STE.B3.Qk D k f) a b))
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.perF (D.R l u a b))) :=
    CPair_STruncR_eq_L2re_flatCut (E := E) l ρ hρ ε (D.R l (Work.Diff.STE.B3.Qk D k f))
      (D.R l u)
      (fun a b => hQf l a b)
      (fun a b => Work.Diff.STE.B3.support_R_subset D l (Work.Diff.STE.B3.Qk D k f) a b)
      (fun a b => hu l a b) (fun a b => Work.Diff.STE.B3.support_R_subset D l u a b)
  have hper : ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (a b : Fin (Module.finrank ℝ E)),
      D.Rper l h a b = Work.Diff.STE.B3.perF (D.R l h a b) := fun h a b => rfl
  rw [h1, h2]
  simp only [hper]

end Work.Diff.STE.B3.VarCoef
