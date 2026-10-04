import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.galerkin_trapped_solution
import Submission.Work.Diff.STE.Lead.GalTame.Defs
import Submission.Work.Diff.STE.Lead.Gal.galVF2_lipschitz_on_pos
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.Prelude2
import Submission.Work.Diff.STE.flat.exists_uniform_local_solution
import Submission.Work.Diff.STE.B3.J_finite_rank
import Submission.Work.Diff.STE.Lead.Gal.SpanLin
import Submission.Work.Diff.STE.Lead.Gal.hasDerivAt_galE
import Submission.Work.Diff.STE.Lead.GalTame.energy_trap
import Submission.Work.Diff.STE.Lead.GalTame.pinched_closed
import Submission.Work.Diff.STE.Lead.GalTame.galVF2_coeff_bound
import Submission.Work.Diff.STE.D.psi.Positivity
import Submission.Work.Diff.STE.B3.dens_lower_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `galerkin_trapped_strong`: trapping + uniform Picard–Lindelöf + gluing, with the coefficient
derivative

The public content of this module is the single theorem `galerkin_trapped_strong`: the trapping
statement `Work.Diff.STE.Lead.GalTame.galerkin_trapped_solution`, **strengthened** by the
coefficient-level derivative `HasDerivAt c (galVF2 … (c t)) t` on `[0, τ₀)` that the final assembly
(`Work.Diff.STE.Lead.GalTame.galE_apriori_L2`) needs for every level `k`.

Structure of the file.

* The supporting layer is **imported** from its owner
  `Submission/Work/Diff/STE/Lead/GalTame/galerkin_trapped_solution.lean`
  (`Pinched`, `pinning_estimate`, `J_add`, `J_galState_decomp`, the off-diagonal bounds …): one lemma
  has exactly one owner.
* `trapped_of_envelope_strong` is the *private* trapping assembly of this file.  It is the owner's
  `trapped_of_envelope` with one extra conjunct in the conclusion: the produced curve carries the
  coefficient-level derivative.  The derivation is not a corollary of `IsGalSol` (from which the
  coefficient-level derivative would require `genMap D ε` to be injective, a separate obligation) —
  it is produced *inside* the trapping argument, where it is available anyway: it feeds the a priori
  estimate `hapr` at `lam = 1/4`, and `exists_uniform_local_solution` supplies it on every
  Picard–Lindelöf step.  The finitely many local pieces are glued by induction on the step count,
  tracking the derivative (the two sides agree on the overlaps, so the two-sided derivative exists at
  the junction points).
* `galerkin_trapped_strong` discharges the four envelope hypotheses of `trapped_of_envelope_strong`
  from proved lemmas: `J_pointwise_le_any` (`hJpt`), `galVF2_velocity_bound` (`hVel`),
  `galVF2_coeff_bound` (`hM`) and `pinched_closed` (`hCpt`).
-/

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 4000000

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- **Envelope form of the trapped Galerkin solution.**

All analytic content of the trapping lemma is taken as a hypothesis, with constants **uniform in
`ε ∈ (0, ε₁]`**:

* `hJpt` — the Friedrichs mollifier `D.J ρ ε` is bounded on the pointwise `g₀`-sup-norm;
* `hVel` — the pointwise bound of the velocity `genMap (galVF2 c)` on the trap;
* `hM` — the Galerkin field `galVF2 c` is bounded on the trap;
* `hCpt` — the pinching region of the mollifier is closed.

The trapping (via the a priori estimate `hapr`), the uniform Picard–Lindelöf step and the patching
of the local solutions into one solution on `[0, τ₀]` are done in this proof. -/
private theorem trapped_of_envelope_strong
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    {D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀}
    {hLC : Submission.Diff.LCSmooth I M}
    {ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ}
    (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    {hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0}
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    {hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner)}
    {k₀ : ℕ} {B : ℝ} {ε₁ : ℝ}
    (hB : 0 < B)
    (hE0 : ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ → Work.Diff.STE.Lead.galE D k₀ ε
      (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ≤ B - 1)
    (hseed : ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ → ∀ (x : M) (v : TangentSpace I x),
      (1 / 2 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (g₀.inner)) x v v)
    (Cof : ℝ → ℝ) (hCof : ∀ lam, 0 < lam → 0 ≤ Cof lam)
    (hapr : ∀ (lam : ℝ), 0 < lam →
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        Work.Diff.STE.Lead.galE D k₀ ε (c t)
          ≤ (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1) * Real.exp (Cof lam * t) - 1)
    (hJpt : ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ (X : Work.Diff.STE.Bil (I := I) (M := M)) (K : ℝ), 0 ≤ K →
        (∀ (y : M) (u v : TangentSpace I y),
          |X y u v| ≤ K * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)) →
        ∀ (x : M) (u v : TangentSpace I x),
          |(D.J ρ ε X) x u v| ≤ C * K * Real.sqrt (g₀.inner x u u)
            * Real.sqrt (g₀.inner x v v))
    (hVel : ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ (hε : 0 < ε)
        (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        Work.Diff.STE.Lead.galE D k₀ ε c ≤ B → Pinched D ρ (1 / 4) ε c →
        ∀ (y : M) (u v : TangentSpace I y),
          |Work.Diff.STE.D.genMap (I := I) (M := M) D ε
            (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c) y u v|
            ≤ C * (1 + B) * (1 + B) * Real.sqrt (g₀.inner y u u)
              * Real.sqrt (g₀.inner y v v))
    (hM : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ (hε : 0 < ε)
        (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        Work.Diff.STE.Lead.galE D k₀ ε c ≤ B → Pinched D ρ (1 / 4) ε c →
        ‖Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c‖ ≤ Cb)
    (hCpt : ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ (hε : 0 < ε),
        IsClosed {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
          Pinched D ρ (1 / 4) ε c}) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ →
        ∃ c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        Submission.Diff.STEGal.IsGalSol hLC D ρ ε τ₀ c ∧
        (∀ t ∈ Set.Ico (0 : ℝ) τ₀,
          HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
          (1 / 4 : ℝ) * g₀.inner x v v
            ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) τ₀, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B) := by
  classical
  obtain ⟨Cp, hCppos, hCpb⟩ := pinning_estimate (D := D) (hLC := hLC) (ρ := ρ) (hρ0 := hρ0)
    (hg := hg) (k₀ := k₀) (B := B) (ε₁ := ε₁) hJpt hseed hVel
  obtain ⟨Cb, hCbnn, hCbb⟩ := hM
  obtain ⟨C₁, hC₁nn, hC₁b⟩ := hJpt
  have hCofnn : (0 : ℝ) ≤ Cof (1 / 4) := hCof (1 / 4) (by norm_num)
  have hden : 0 < Cof (1 / 4) + 1 := by linarith
  set δE : ℝ := Real.log (1 + (2 * B)⁻¹) with hδEdef
  have hδEpos : 0 < δE := by
    rw [hδEdef]
    refine Real.log_pos ?_
    have h2B : (0 : ℝ) < 2 * B := by linarith
    have := inv_pos.mpr h2B
    linarith
  set τ₀ : ℝ := min 1 (min (1 / (8 * Cp)) (δE / (Cof (1 / 4) + 1))) with hτ₀def
  have hτ₀pos : 0 < τ₀ := by
    rw [hτ₀def]
    exact lt_min one_pos (lt_min (div_pos one_pos (by linarith)) (div_pos hδEpos hden))
  have hτ₀le1 : τ₀ ≤ 1 := by rw [hτ₀def]; exact min_le_left _ _
  have hτ₀le2 : τ₀ ≤ 1 / (8 * Cp) := by
    rw [hτ₀def]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hτ₀δ : Cof (1 / 4) * τ₀ ≤ δE := by
    rw [hτ₀def]
    have h1 : Cof (1 / 4) * min 1 (min (1 / (8 * Cp)) (δE / (Cof (1 / 4) + 1)))
        ≤ Cof (1 / 4) * (δE / (Cof (1 / 4) + 1)) :=
      mul_le_mul_of_nonneg_left (le_trans (min_le_right _ _) (min_le_right _ _)) hCofnn
    have h2 : Cof (1 / 4) * (δE / (Cof (1 / 4) + 1)) ≤ δE := by
      rw [mul_div_assoc', div_le_iff₀ hden]
      nlinarith [hδEpos.le, hCofnn]
    linarith
  have hτ₀log : Cof (1 / 4) * τ₀ ≤ Real.log (1 + B⁻¹) := by
    have hle : δE ≤ Real.log (1 + B⁻¹) := by
      rw [hδEdef]
      refine Real.log_le_log (by positivity) ?_
      have h1 : (2 * B)⁻¹ ≤ B⁻¹ := by
        rw [inv_le_inv₀ (by linarith : (0 : ℝ) < 2 * B) hB]
        linarith
      linarith
    linarith
  have hexpτ : Real.exp (Cof (1 / 4) * τ₀) ≤ 1 + (2 * B)⁻¹ := by
    have h := Real.exp_le_exp.mpr hτ₀δ
    rw [hδEdef, Real.exp_log (by positivity : (0 : ℝ) < 1 + (2 * B)⁻¹)] at h
    exact h
  refine ⟨τ₀, hτ₀pos, ?_⟩
  intro ε hε hε1
  have hεIoc : ε ∈ Set.Ioc (0 : ℝ) ε₁ := ⟨hε, hε1⟩
  set R : ℝ := τ₀ * Cb + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith [mul_nonneg hτ₀pos.le hCbnn]
  set Kc : Set (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :=
    {c | ‖c‖ ≤ R ∧ Pinched D ρ (1 / 4) ε c} with hKcdef
  have hKcclosed : IsClosed Kc := by
    rw [hKcdef]
    exact IsClosed.inter (isClosed_le continuous_norm continuous_const)
      (hCpt ε hεIoc hε)
  have hKcsub : Kc ⊆ Metric.closedBall
      (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) R := by
    intro c hc
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hc.1
  have hKccpt : IsCompact Kc :=
    (isCompact_closedBall (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) R)
      |>.of_isClosed_subset hKcclosed hKcsub
  have h0K : (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ∈ Kc := by
    refine ⟨by rw [norm_zero]; exact hRpos.le, ?_⟩
    intro x v
    have h1 := hseed ε hε hε1 x v
    rw [galState_zero_eq]
    have h2 : (0 : ℝ) ≤ g₀.inner x v v := smet_inner_nonneg' (g₀ := g₀) v
    linarith
  have hloc : ∀ p ∈ Kc, ∃ L : NNReal, ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith L
        (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0)
        (Metric.closedBall p r) := by
    intro p hp
    have hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε p)) x v v := by
      intro x v hv
      have h1 := hp.2 x v
      have h2 : 0 < g₀.inner x v v := g₀.pos x v hv
      linarith
    obtain ⟨δ, hδ, -, L, hLip⟩ :=
      Work.Diff.STE.Lead.Gal.galVF2_lipschitz_on_pos D ρ hρ hρ0 hρs hρ1 hLC hg ε hε p hpos
    exact ⟨L, δ, hδ, hLip⟩
  obtain ⟨ρstep, hρsteppos, hflow⟩ :=
    Work.Diff.STE.flat.exists_uniform_local_solution (F :=
      Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0) hKccpt hloc
  -- ## Persistence of the pinching: `J` is Lipschitz in the coefficients with weight `g₀`
  obtain ⟨d₀, hd₀, hdens⟩ :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  set Kgen : ℝ := (Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ)
    * (2 * (Real.sqrt d₀)⁻¹) with hKgendef
  have hKgennn : 0 ≤ Kgen := by
    rw [hKgendef]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg two_pos.le (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  have hgenbd : ∀ (w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
      (x : M) (u v : TangentSpace I x),
      |Work.Diff.STE.D.genMap (I := I) (M := M) D ε w x u v|
        ≤ Kgen * ‖w‖ * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
    intro w x u v
    have h1 := abs_genMap_apply_le_off (I := I) (M := M) D ε d₀ hd₀ hdens w x u v
    have h2 : (∑ z, |w z|)
        ≤ (Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) * ‖w‖ := by
      calc (∑ z, |w z|) ≤ ∑ _z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε, ‖w‖ :=
            Finset.sum_le_sum (fun z _ => by simpa using norm_le_pi_norm w z)
        _ = (Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) * ‖w‖ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h3 : (0 : ℝ) ≤ 2 * (Real.sqrt d₀)⁻¹ :=
      mul_nonneg two_pos.le (inv_nonneg.mpr (Real.sqrt_nonneg _))
    have h5 : (∑ z, |w z|) * (2 * (Real.sqrt d₀)⁻¹) * Real.sqrt (g₀.inner x u u)
        * Real.sqrt (g₀.inner x v v) ≤ Kgen * ‖w‖ * Real.sqrt (g₀.inner x u u)
        * Real.sqrt (g₀.inner x v v) := by
      have h6 : (∑ z, |w z|) * (2 * (Real.sqrt d₀)⁻¹) ≤ Kgen * ‖w‖ := by
        rw [hKgendef]
        calc (∑ z, |w z|) * (2 * (Real.sqrt d₀)⁻¹)
            ≤ ((Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ) * ‖w‖)
              * (2 * (Real.sqrt d₀)⁻¹) := mul_le_mul_of_nonneg_right h2 h3
          _ = ((Fintype.card (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) : ℝ)
              * (2 * (Real.sqrt d₀)⁻¹)) * ‖w‖ := by ring
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h6 (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    linarith [h1, h5]
  have hJdiff : ∀ (w : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
      (x : M) (v : TangentSpace I x),
      |(D.J ρ ε (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)) x v v|
        ≤ (C₁ * Kgen) * ‖w‖ * g₀.inner x v v := by
    intro w x v
    have hbou := hC₁b ε hεIoc (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)
      (Kgen * ‖w‖) (mul_nonneg hKgennn (norm_nonneg _)) (fun y u v' => hgenbd w y u v') x v v
    have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v :=
      Real.mul_self_sqrt (smet_inner_nonneg' (g₀ := g₀) v)
    calc |(D.J ρ ε (Work.Diff.STE.D.genMap (I := I) (M := M) D ε w)) x v v|
        ≤ C₁ * (Kgen * ‖w‖) * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := hbou
      _ = C₁ * (Kgen * ‖w‖) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by
          ring
      _ = C₁ * (Kgen * ‖w‖) * g₀.inner x v v := by rw [hsq]
      _ = (C₁ * Kgen) * ‖w‖ * g₀.inner x v v := by ring
  -- `J` is additive over `galState`, so `hJdiff` gives the persistence of the pinching
  have hJpers : ∀ (c₁ c₂ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
      (x : M) (v : TangentSpace I x),
      (D.J ρ ε (Submission.Diff.STEGal.galState D ε c₁)) x v v
        - (C₁ * Kgen) * ‖c₂ - c₁‖ * g₀.inner x v v
        ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε c₂)) x v v := by
    intro c₁ c₂ x v
    have hstate : Submission.Diff.STEGal.galState D ε c₂
        = Submission.Diff.STEGal.galState D ε c₁
          + Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c₂ - c₁) := by
      funext x'
      ext u v'
      have h := genMap_add_apply D ε c₁ (c₂ - c₁) x' u v'
      have hc : c₁ + (c₂ - c₁) = c₂ := by
        funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [hc] at h
      simp only [Submission.Diff.STEGal.galState, Work.Diff.STE.D.addSec_apply, Pi.add_apply,
        ContinuousLinearMap.add_apply]
      linarith [h]
    have hadd := J_add D ρ ε hε hρ0
      (Submission.Diff.STEGal.galState D ε c₁)
      (Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c₂ - c₁))
      (Work.Diff.STE.Lead.chartData_galState D ε hg c₁)
      (Work.Diff.STE.D.ChartData_genMap (I := I) (M := M) D ε (c₂ - c₁))
      (Work.Diff.STE.Lead.isSymm_galState D ε c₁)
      (Work.Diff.STE.D.isSymm_genMap (I := I) (M := M) D ε (c₂ - c₁))
    have hval : (D.J ρ ε (Submission.Diff.STEGal.galState D ε c₂)) x v v
        = (D.J ρ ε (Submission.Diff.STEGal.galState D ε c₁)) x v v
          + (D.J ρ ε (Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c₂ - c₁))) x v v := by
      rw [hstate, hadd]
      simp only [Pi.add_apply, ContinuousLinearMap.add_apply]
    have h2 := (abs_le.mp (hJdiff (c₂ - c₁) x v)).1
    linarith [hval, h2]
  -- ## The joint trap: any solution starting at the origin keeps both traps up to `τ₀`
  have htraps : ∀ (T : ℝ) (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)),
      0 ≤ T → T ≤ τ₀ → c 0 = 0 →
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B ∧
        Pinched D ρ (1 / 4) ε (c t) := by
    intro T c hT0 hTτ hc0 hode
    by_contra hcon
    have hex : ∃ t ∈ Set.Icc (0 : ℝ) T,
        ¬ (Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B ∧ Pinched D ρ (1 / 4) ε (c t)) := by
      by_contra h
      exact hcon (fun t ht => by by_contra h2; exact h ⟨t, ht, h2⟩)
    obtain ⟨t₀, ht₀I, ht₀bad⟩ := hex
    set S : Set ℝ := Set.Icc 0 (min T τ₀) ∩
      {s : ℝ | ¬ (Work.Diff.STE.Lead.galE D k₀ ε (c s) ≤ B ∧ Pinched D ρ (1 / 4) ε (c s))}
      with hSdef
    have hS₁ : ∀ s ∈ S, 0 ≤ s := fun s hs => by
      have h := hs; rw [hSdef] at h; exact h.1.1
    have hS₂ : ∀ s ∈ S, s ≤ min T τ₀ := fun s hs => by
      have h := hs; rw [hSdef] at h; exact h.1.2
    have hS₃ : ∀ s ∈ S, ¬ (Work.Diff.STE.Lead.galE D k₀ ε (c s) ≤ B ∧
        Pinched D ρ (1 / 4) ε (c s)) := fun s hs => by
      have h := hs; rw [hSdef] at h; exact h.2
    have hSne : S.Nonempty := ⟨t₀, ⟨⟨ht₀I.1, le_min ht₀I.2 (le_trans ht₀I.2 hTτ)⟩, ht₀bad⟩⟩
    have hSbdd : BddBelow S := ⟨0, fun s hs => hS₁ s hs⟩
    set T₁ : ℝ := sInf S with hT₁def
    have hT₁le : T₁ ≤ min T τ₀ := by
      obtain ⟨s₁, hs₁⟩ := hSne
      exact le_trans (csInf_le hSbdd hs₁) (hS₂ s₁ hs₁)
    have hT₁ge : 0 ≤ T₁ := le_csInf hSne (fun s hs => hS₁ s hs)
    have hT₁T : T₁ ≤ T := le_trans hT₁le (min_le_left _ _)
    have hT₁τ : T₁ ≤ τ₀ := le_trans hT₁le (min_le_right _ _)
    have hT₁Icc : T₁ ∈ Set.Icc (0 : ℝ) T := ⟨hT₁ge, hT₁T⟩
    have hbelow : ∀ s ∈ Set.Ico (0 : ℝ) T₁, Work.Diff.STE.Lead.galE D k₀ ε (c s) ≤ B ∧
        Pinched D ρ (1 / 4) ε (c s) := by
      intro s hs
      by_contra hc
      have hsS : s ∈ S := ⟨⟨hs.1, le_trans hs.2.le hT₁le⟩, hc⟩
      have := csInf_le hSbdd hsS
      linarith [hs.2]
    have hode₁ : ∀ s ∈ Set.Icc (0 : ℝ) T₁,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c s)) s :=
      fun s hs => hode s ⟨hs.1, le_trans hs.2 hT₁T⟩
    have hE₁ : Work.Diff.STE.Lead.galE D k₀ ε (c T₁) < B := by
      rcases eq_or_lt_of_le hT₁ge with h0 | hpos
      · rw [← h0, hc0]
        linarith [hE0 ε hε hε1]
      · have hraw := hapr (1 / 4) (by norm_num) ε hε hε1 c T₁ hpos
          (fun t ht => hode₁ t ⟨ht.1, le_of_lt ht.2⟩)
          (fun t ht x v hv => by
            have h1 := (hbelow t ht).2 x v
            have h2 : 0 < g₀.inner x v v := g₀.pos x v hv
            linarith)
          (fun t ht x v => (hbelow t ht).2 x v)
          (fun t ht => (hbelow t ht).1)
        have hcontT₁ : ContinuousAt (fun s => Work.Diff.STE.Lead.galE D k₀ ε (c s)) T₁ :=
          (Work.Diff.STE.Lead.Gal.hasDerivAt_galE D k₀ ε hg
            (hode₁ T₁ ⟨hT₁ge, le_rfl⟩)).continuousAt
        have hlim : Filter.Tendsto (fun s => Work.Diff.STE.Lead.galE D k₀ ε (c s))
            (nhdsWithin T₁ (Set.Iio T₁)) (nhds (Work.Diff.STE.Lead.galE D k₀ ε (c T₁))) :=
          hcontT₁.tendsto.mono_left nhdsWithin_le_nhds
        have hPhicont : ContinuousAt
            (fun s : ℝ => (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
              * Real.exp (Cof (1 / 4) * s) - 1) T₁ :=
          ContinuousAt.sub
            (ContinuousAt.mul continuousAt_const
              (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id)))
            continuousAt_const
        have hdiff : ContinuousAt
            (fun s : ℝ => Work.Diff.STE.Lead.galE D k₀ ε (c s)
              - ((Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
                * Real.exp (Cof (1 / 4) * s) - 1)) T₁ :=
          hcontT₁.sub hPhicont
        have hmaxT₁ : max 0 (T₁ - 1) < T₁ := by
          rw [max_lt_iff]; exact ⟨hpos, by linarith⟩
        have hmono : ∀ᶠ s in nhdsWithin T₁ (Set.Iio T₁),
            Work.Diff.STE.Lead.galE D k₀ ε (c s)
              - ((Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
                * Real.exp (Cof (1 / 4) * s) - 1) ≤ 0 := by
          filter_upwards [Ioo_mem_nhdsLT hmaxT₁]
            with s hs
          have hmem : s ∈ Set.Ico (0 : ℝ) T₁ :=
            ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs.1), hs.2⟩
          linarith [hraw s hmem]
        have hle : Work.Diff.STE.Lead.galE D k₀ ε (c T₁)
            - ((Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
              * Real.exp (Cof (1 / 4) * T₁) - 1) ≤ 0 :=
          le_of_tendsto (hdiff.tendsto.mono_left nhdsWithin_le_nhds) hmono
        have hA : Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1 ≤ B := by
          rw [hc0]; linarith [hE0 ε hε hε1]
        have h3 : (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1)
            * Real.exp (Cof (1 / 4) * T₁) - 1 ≤ B - 1 / 2 := by
          have hexp₁ : Real.exp (Cof (1 / 4) * T₁) ≤ Real.exp (Cof (1 / 4) * τ₀) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT₁τ hCofnn)
          have h1 : (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1) * Real.exp (Cof (1 / 4) * T₁)
              ≤ B * Real.exp (Cof (1 / 4) * τ₀) :=
            mul_le_mul hA hexp₁ (Real.exp_pos _).le hB.le
          have h2 : B * Real.exp (Cof (1 / 4) * τ₀) ≤ B * (1 + (2 * B)⁻¹) :=
            mul_le_mul_of_nonneg_left hexpτ hB.le
          have h4 : B * (1 + (2 * B)⁻¹) = B + 1 / 2 := by
            rw [mul_add, mul_one, mul_inv]
            field_simp
          linarith
        linarith
    have hpin₁ : Pinched D ρ (1 / 4) ε (c T₁) := by
      have h := hCpb ε hε hε1 T₁ c hT₁ge hc0 hode₁
        (fun s hs => (hbelow s hs).1) (fun s hs => (hbelow s hs).2)
      have hm := h T₁ ⟨hT₁ge, le_rfl⟩
      intro x v
      have hCpT : Cp * T₁ ≤ 1 / 8 := by
        have hle : T₁ ≤ 1 / (8 * Cp) := le_trans hT₁τ hτ₀le2
        have hle' : T₁ * (8 * Cp) ≤ 1 :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * Cp)).mp hle
        nlinarith [hCppos]
      have h1 : (1 / 4 : ℝ) * g₀.inner x v v ≤ (1 / 2 - Cp * T₁) * g₀.inner x v v := by
        have hv := smet_inner_nonneg' (g₀ := g₀) v
        nlinarith [hCpT, hv]
      linarith [hm x v]
    -- a neighbourhood of `T₁` on which both traps hold
    have hcontE : ContinuousAt (fun s => Work.Diff.STE.Lead.galE D k₀ ε (c s)) T₁ :=
      (Work.Diff.STE.Lead.Gal.hasDerivAt_galE D k₀ ε hg (hode T₁ hT₁Icc)).continuousAt
    obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp
      (hcontE.tendsto.eventually (isOpen_Iio.mem_nhds hE₁))
    -- the Lipschitz bound for `c` near `T₁`, from its differentiability there
    have hCbT₁ : ‖Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c T₁)‖ ≤ Cb :=
      hCbb ε hεIoc hε (c T₁) hE₁.le hpin₁
    obtain ⟨δ₃, hδ₃pos, hδ₃⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - T₁| < δ →
        ‖c s - c T₁‖ ≤ (Cb + 1) * |s - T₁| := by
      have htend := (hode T₁ hT₁Icc).tendsto_slope.norm
      have hev : ∀ᶠ s in 𝓝[≠] T₁, ‖slope c T₁ s‖ ≤ Cb + 1 :=
        htend.eventually (eventually_le_nhds (by linarith))
      rw [nhdsWithin, eventually_inf_principal] at hev
      obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
      refine ⟨δ, hδpos, fun s hs => ?_⟩
      by_cases hseq : s = T₁
      · subst hseq
        rw [sub_self, norm_zero]
        exact mul_nonneg (by linarith) (abs_nonneg _)
      · have hdist : dist s T₁ < δ := by rwa [Real.dist_eq]
        have hb := hδ hdist hseq
        have hval : c s - c T₁ = (s - T₁) • slope c T₁ s := by
          rw [slope_def_module, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hseq), one_smul]
        rw [hval, norm_smul, Real.norm_eq_abs]
        calc |s - T₁| * ‖slope c T₁ s‖ ≤ |s - T₁| * (Cb + 1) :=
              mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ = (Cb + 1) * |s - T₁| := by ring
    obtain ⟨s, hsS, hslt⟩ : ∃ s ∈ S,
        s < T₁ + min δ₁ (min δ₃ (1 / (8 * (C₁ * Kgen) * (Cb + 1) + 1))) := by
      by_contra hcon'
      push_neg at hcon'
      have hle : T₁ + min δ₁ (min δ₃ (1 / (8 * (C₁ * Kgen) * (Cb + 1) + 1))) ≤ T₁ :=
        le_csInf hSne (fun s hs => hcon' s hs)
      have hminpos : 0 < min δ₁ (min δ₃ (1 / (8 * (C₁ * Kgen) * (Cb + 1) + 1))) :=
        lt_min hδ₁pos (lt_min hδ₃pos (by positivity))
      linarith
    have hsge : T₁ ≤ s := csInf_le hSbdd hsS
    have hsabs : |s - T₁| < min δ₁ (min δ₃ (1 / (8 * (C₁ * Kgen) * (Cb + 1) + 1))) := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h1 : Work.Diff.STE.Lead.galE D k₀ ε (c s) < B :=
      hδ₁sub (by
        rw [Metric.mem_ball, Real.dist_eq]
        exact lt_of_lt_of_le hsabs (min_le_left _ _))
    have h2 : Pinched D ρ (1 / 4) ε (c s) := by
      intro x v
      have hm := (hCpb ε hε hε1 T₁ c hT₁ge hc0 hode₁
        (fun u hu => (hbelow u hu).1) (fun u hu => (hbelow u hu).2)) T₁
        ⟨hT₁ge, le_rfl⟩ x v
      have hp := hJpers (c T₁) (c s) x v
      have hcl : ‖c s - c T₁‖ ≤ (Cb + 1) * |s - T₁| :=
        hδ₃ s (lt_of_lt_of_le hsabs (le_trans (min_le_right _ _) (min_le_left _ _)))
      have hkey : (C₁ * Kgen) * ‖c s - c T₁‖ ≤ 1 / 8 := by
        have hAb : (0 : ℝ) ≤ (C₁ * Kgen) * (Cb + 1) :=
          mul_nonneg (mul_nonneg hC₁nn hKgennn) (by linarith)
        have hden : (0 : ℝ) < 8 * ((C₁ * Kgen) * (Cb + 1)) + 1 := by linarith
        have h1 : (C₁ * Kgen) * ‖c s - c T₁‖ ≤ ((C₁ * Kgen) * (Cb + 1)) * |s - T₁| := by
          calc (C₁ * Kgen) * ‖c s - c T₁‖ ≤ (C₁ * Kgen) * ((Cb + 1) * |s - T₁|) :=
                mul_le_mul_of_nonneg_left hcl (mul_nonneg hC₁nn hKgennn)
            _ = ((C₁ * Kgen) * (Cb + 1)) * |s - T₁| := by ring
        have h3 : |s - T₁| < 1 / (8 * ((C₁ * Kgen) * (Cb + 1)) + 1) := by
          have h4 : |s - T₁| < 1 / (8 * (C₁ * Kgen) * (Cb + 1) + 1) :=
            lt_of_lt_of_le hsabs (le_trans (min_le_right _ _) (min_le_right _ _))
          have heq : 8 * ((C₁ * Kgen) * (Cb + 1)) + 1
              = 8 * (C₁ * Kgen) * (Cb + 1) + 1 := by ring
          rwa [heq]
        rcases eq_or_lt_of_le hAb with hA0 | hApos
        · rw [← hA0, zero_mul] at h1
          linarith [h1]
        · have h5 := mul_lt_mul_of_pos_left h3 hApos
          have h6 : ((C₁ * Kgen) * (Cb + 1))
              * (1 / (8 * ((C₁ * Kgen) * (Cb + 1)) + 1)) ≤ 1 / 8 := by
            rw [mul_div_assoc', div_le_iff₀ hden]
            linarith
          linarith
      have hCpT : Cp * T₁ ≤ 1 / 8 := by
        have hle : T₁ ≤ 1 / (8 * Cp) := le_trans hT₁τ hτ₀le2
        have hle' : T₁ * (8 * Cp) ≤ 1 :=
          (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * Cp)).mp hle
        nlinarith [hCppos]
      have hgv : (0 : ℝ) ≤ g₀.inner x v v := smet_inner_nonneg' (g₀ := g₀) v
      have hstep1 : (3 / 8 : ℝ) * g₀.inner x v v
          ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c T₁))) x v v := by
        nlinarith [hm, hCpT, hgv]
      have hstep2 : (C₁ * Kgen) * ‖c s - c T₁‖ * g₀.inner x v v
          ≤ (1 / 8) * g₀.inner x v v := mul_le_mul_of_nonneg_right hkey hgv
      linarith [hstep1, hstep2, hp]
    exact hS₃ s hsS ⟨h1.le, h2⟩
  -- ## The patching induction
  have hind : ∀ m : ℕ, ∃ α : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
      α 0 = 0 ∧
      (∀ t ∈ Set.Icc 0 (min ((m : ℝ) * ρstep) τ₀),
        HasDerivAt α (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (α t)) t) ∧
      (∀ t ∈ Set.Icc 0 (min ((m : ℝ) * ρstep) τ₀), Work.Diff.STE.Lead.galE D k₀ ε (α t) ≤ B ∧
        Pinched D ρ (1 / 4) ε (α t)) := by
    intro m
    induction m with
    | zero =>
      obtain ⟨α, hα0, hαd⟩ := hflow 0 h0K
      have hzero : min (((0 : ℕ) : ℝ) * ρstep) τ₀ = 0 := by
        rw [Nat.cast_zero, zero_mul, min_eq_left hτ₀pos.le]
      refine ⟨α, hα0, ?_, ?_⟩
      · intro t ht
        have ht0 : t = 0 := by
          have h1 := ht.2
          rw [hzero] at h1
          exact le_antisymm h1 ht.1
        rw [ht0]
        exact hαd 0 (by rw [abs_zero]; exact hρsteppos.le)
      · intro t ht
        have ht0 : t = 0 := by
          have h1 := ht.2
          rw [hzero] at h1
          exact le_antisymm h1 ht.1
        rw [ht0, hα0]
        exact ⟨by linarith [hE0 ε hε hε1], h0K.2⟩
    | succ m ih =>
      obtain ⟨α, hα0, hαode, hαtrap⟩ := ih
      by_cases hmτ : τ₀ ≤ (m : ℝ) * ρstep
      · have h1 : min (((m + 1 : ℕ) : ℝ) * ρstep) τ₀ = τ₀ := by
          rw [min_eq_right]
          have hcast : ((m + 1 : ℕ) : ℝ) * ρstep = (m : ℝ) * ρstep + ρstep := by
            push_cast; ring
          rw [hcast]; linarith [hmτ, hρsteppos.le]
        have h2 : min ((m : ℝ) * ρstep) τ₀ = τ₀ := min_eq_right hmτ
        refine ⟨α, hα0, ?_, ?_⟩
        · intro t ht
          rw [h1] at ht
          exact hαode t (by rw [h2]; exact ht)
        · intro t ht
          rw [h1] at ht
          exact hαtrap t (by rw [h2]; exact ht)
      · have hmτ' : (m : ℝ) * ρstep < τ₀ := lt_of_not_ge hmτ
        set T : ℝ := (m : ℝ) * ρstep with hTdef
        have hTmin : min T τ₀ = T := min_eq_left hmτ'.le
        have hT0 : 0 ≤ T := by rw [hTdef]; positivity
        have hodeT : ∀ t ∈ Set.Icc (0 : ℝ) T,
            HasDerivAt α (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0
              (α t)) t :=
          fun t ht => hαode t (by rw [hTmin]; exact ht)
        have htrapsT : ∀ t ∈ Set.Icc (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (α t) ≤ B ∧
            Pinched D ρ (1 / 4) ε (α t) := htraps T α hT0 hmτ'.le hα0 hodeT
        have hball : ‖α T‖ ≤ R := by
          have hbound : ∀ t ∈ Set.Ico (0 : ℝ) T,
              ‖Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (α t)‖ ≤ Cb :=
            fun t ht => hCbb ε hεIoc hε (α t)
              (htrapsT t ⟨ht.1, le_of_lt ht.2⟩).1 (htrapsT t ⟨ht.1, le_of_lt ht.2⟩).2
          have hder : ∀ t ∈ Set.Icc (0 : ℝ) T,
              HasDerivWithinAt α (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0
                (α t)) (Set.Icc (0 : ℝ) T) t :=
            fun t ht => (hodeT t ht).hasDerivWithinAt
          have hmain := norm_image_sub_le_of_norm_deriv_le_segment' (f := α)
            (f' := fun t => Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0
              (α t)) (a := 0) (b := T) (C := Cb) hder hbound T ⟨hT0, le_rfl⟩
          have hmain' : ‖α T‖ ≤ Cb * T := by
            rw [hα0, sub_zero, sub_zero] at hmain
            exact hmain
          calc ‖α T‖ ≤ Cb * T := hmain'
            _ ≤ Cb * τ₀ := mul_le_mul_of_nonneg_left hmτ'.le hCbnn
            _ ≤ R := by rw [hRdef]; linarith
        have hαTK : α T ∈ Kc := ⟨hball, (htrapsT T ⟨hT0, le_rfl⟩).2⟩
        obtain ⟨γ, hγ0, hγd⟩ := hflow (α T) hαTK
        let α' : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :=
          fun t => if t ≤ T then α t else γ (t - T)
        have hα'0 : α' 0 = 0 := by
          dsimp only [α']
          rw [if_pos hT0]
          exact hα0
        have hα'T : α' T = α T := by
          dsimp only [α']
          rw [if_pos le_rfl]
        have hodeα' : ∀ t ∈ Set.Icc 0 (T + ρstep),
            HasDerivAt α' (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0
              (α' t)) t := by
          intro t ht
          rcases lt_trichotomy t T with hlt | heq | hgt
          · have hev : α' =ᶠ[nhds t] α := by
              filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
              dsimp only [α']
              rw [if_pos hs.le]
            have hα't : α' t = α t := by
              dsimp only [α']
              rw [if_pos hlt.le]
            rw [hα't]
            exact (hodeT t ⟨ht.1, hlt.le⟩).congr_of_eventuallyEq hev
          · subst heq
            have hleft : HasDerivWithinAt α' (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε
                hε hρ0 (α' T)) (Set.Iic T) T := by
              rw [hα'T]
              refine (((hodeT T ⟨hT0, le_rfl⟩).hasDerivWithinAt).mono
                (Set.subset_univ _)).congr ?_ ?_
              · intro s hs
                dsimp only [α']
                rw [if_pos (Set.mem_Iic.mp hs)]
              · exact hα'T
            have hright : HasDerivWithinAt α' (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε
                hε hρ0 (α' T)) (Set.Ici T) T := by
              have hbase : HasDerivAt γ (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε
                  hρ0 (γ (T - T))) (T - T) := by
                rw [sub_self]
                exact hγd 0 (by rw [abs_zero]; exact hρsteppos.le)
              have h2 : HasDerivAt (fun s : ℝ => γ (s - T))
                  (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0
                    (γ (T - T))) T :=
                HasDerivAt.comp_sub_const T T hbase
              have hγT : γ (T - T) = α' T := by
                rw [sub_self, hγ0]
                exact hα'T.symm
              rw [hγT] at h2
              refine h2.hasDerivWithinAt.congr ?_ ?_
              · intro s hs
                rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with h | h
                · rw [← h]
                  dsimp only [α']
                  rw [if_pos le_rfl, sub_self, hγ0]
                · dsimp only [α']
                  rw [if_neg (not_le.mpr h)]
              · dsimp only [α']
                rw [if_pos le_rfl, sub_self, hγ0]
            have hunion := hleft.union hright
            rw [Set.Iic_union_Ici] at hunion
            exact hunion.hasDerivAt Filter.univ_mem
          · have htval : α' t = γ (t - T) := by
              dsimp only [α']
              rw [if_neg (not_le.mpr hgt)]
            have hev : α' =ᶠ[nhds t] (fun s => γ (s - T)) := by
              filter_upwards [isOpen_Ioi.mem_nhds hgt] with s hs
              dsimp only [α']
              rw [if_neg (not_le.mpr hs)]
            have hle : |t - T| ≤ ρstep := by
              rw [abs_of_pos (sub_pos.mpr hgt)]
              linarith [ht.2]
            have hbase : HasDerivAt γ (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε
                hρ0 (γ (t - T))) (t - T) := hγd (t - T) hle
            have h2 : HasDerivAt (fun s : ℝ => γ (s - T))
                (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε
                  hρ0 (γ (t - T))) t :=
              HasDerivAt.comp_sub_const t T hbase
            rw [htval]
            exact h2.congr_of_eventuallyEq hev
        have hcast : (((m + 1 : ℕ) : ℝ) * ρstep) = T + ρstep := by
          rw [hTdef]; push_cast; ring
        refine ⟨α', hα'0, ?_, ?_⟩
        · intro t ht
          rw [hcast] at ht
          exact hodeα' t ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
        · intro t ht
          rw [hcast] at ht
          have hT'0 : 0 ≤ min (T + ρstep) τ₀ := le_trans ht.1 ht.2
          have htraps' := htraps (min (T + ρstep) τ₀) α' hT'0 (min_le_right _ _) hα'0
            (fun s hs => hodeα' s ⟨hs.1, le_trans hs.2 (min_le_left _ _)⟩)
          exact htraps' t ⟨ht.1, ht.2⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, τ₀ ≤ (m : ℝ) * ρstep := by
    obtain ⟨m, hm⟩ := exists_nat_ge (τ₀ / ρstep)
    refine ⟨m, ?_⟩
    rw [div_le_iff₀ hρsteppos] at hm
    linarith [hm]
  obtain ⟨α, hα0, hαode, hαtrap⟩ := hind m
  have hminτ : min ((m : ℝ) * ρstep) τ₀ = τ₀ := min_eq_right hm
  have hodeτ : ∀ t ∈ Set.Icc (0 : ℝ) τ₀,
      HasDerivAt α (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (α t)) t :=
    fun t ht => hαode t (by rw [hminτ]; exact ht)
  have htrapsτ : ∀ t ∈ Set.Icc (0 : ℝ) τ₀, Work.Diff.STE.Lead.galE D k₀ ε (α t) ≤ B ∧
      Pinched D ρ (1 / 4) ε (α t) := htraps τ₀ α hτ₀pos.le le_rfl hα0 hodeτ
  refine ⟨α, ?_, ?_, ?_, ?_⟩
  · refine Work.Diff.STE.Lead.isGalSol_of_galVF2 hLC D ρ ε hε hρ0 τ₀ hα0 (fun t ht x v hv => ?_)
      (fun t ht => (hodeτ t ht).hasDerivWithinAt)
    have h1 := (htrapsτ t ht).2 x v
    have h2 : 0 < g₀.inner x v v := g₀.pos x v hv
    linarith
  · intro t ht
    exact hodeτ t ⟨ht.1, ht.2.le⟩
  · intro t ht x v
    exact (htrapsτ t ht).2 x v
  · intro t ht
    exact (htrapsτ t ⟨ht.1, ht.2.le⟩).1

/-- **Trapping + uniform Picard–Lindelöf step + gluing, with the coefficient derivative exported.**

This is `Work.Diff.STE.Lead.GalTame.galerkin_trapped_solution` (same hypotheses, same conclusion)
**plus one extra conjunct**: the produced curve `c` has the *coefficient-level* derivative
`HasDerivAt c (galVF2 hLC D ρ ε hε hρ0 (c t)) t` on `[0, τ₀)`, not merely the per-component
derivative that `IsGalSol` records.

**Why the extra conjunct is needed.**  The final assembly must run the level-`k` a priori estimate
`Work.Diff.STE.Lead.GalTame.galE_apriori_L2` on the *same* curve and the *same* interval for every
level `k`; its hypothesis `hode` is `∀ t ∈ Ico 0 T, HasDerivAt c (galVF2 … (c t)) t`.  `IsGalSol`
records only `HasDerivWithinAt` of each *component* `s ↦ galState D ε (c s) x u v`, from which the
coefficient-level derivative does **not** follow without proving that `genMap D ε` is injective (a
genuinely separate obligation); therefore the derivative is *produced inside* the trapping argument,
where it is available anyway (`hapr` at `lam = 1/4` needs exactly it, and
`exists_uniform_local_solution` supplies it on each Picard–Lindelöf step).

**How it is proved.**  The whole trapping assembly is carried out in `trapped_of_envelope_strong`
(below, private to this file): the trap
`Kc := {c | galE D k₀ ε c ≤ B} ∩ {c | ∀ x v, (1/4)·g₀.inner x v v ≤ (D.J ρ ε (galState D ε c)) x v v}`
is closed (`pinched_closed`) and bounded (`energy_trap`), hence compact; `galVF2_coeff_bound` bounds
`|c'|` on it, so finitely many uniform Picard–Lindelöf steps reach `τ₀`, and the pieces are glued by
induction on the step count — tracking the `HasDerivAt` along the way (the gluings agree on overlaps,
so the two-sided derivative exists at the junctions).  The envelope hypotheses of
`trapped_of_envelope_strong` are then discharged here by `J_pointwise_le_any` (`hJpt`),
`galVF2_velocity_bound` (`hVel`), `galVF2_coeff_bound` (`hM`) and `pinched_closed` (`hCpt`). -/
theorem galerkin_trapped_strong
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (k₀ : ℕ) (hk₀ : Module.finrank ℝ E + 12 < 2 * k₀)
    (B : ℝ) (hB : D.ENormB k₀ (g₀.inner) + D.ENormB 0 (g₀.inner) + 1 ≤ B)
    (ε₁ : ℝ) (hε₁ : 0 < ε₁)
    (hseed : ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ → ∀ (x : M) (v : TangentSpace I x),
      (1 / 2 : ℝ) * g₀.inner x v v ≤ (D.J ρ ε (g₀.inner)) x v v)
    (Cof : ℝ → ℝ) (hCof : ∀ lam, 0 < lam → 0 ≤ Cof lam)
    (hapr : ∀ (lam : ℝ), 0 < lam →
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ →
      ∀ (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)) (T : ℝ), 0 < T →
      (∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) →
      (∀ t ∈ Set.Ico (0 : ℝ) T, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B) →
      ∀ t ∈ Set.Ico (0 : ℝ) T,
        Work.Diff.STE.Lead.galE D k₀ ε (c t)
          ≤ (Work.Diff.STE.Lead.galE D k₀ ε (c 0) + 1) * Real.exp (Cof lam * t) - 1) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ → ∃ c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
        Submission.Diff.STEGal.IsGalSol hLC D ρ ε τ₀ c ∧
        (∀ t ∈ Set.Ico (0 : ℝ) τ₀,
          HasDerivAt c (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 (c t)) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
          (1 / 4 : ℝ) * g₀.inner x v v
            ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε (c t))) x v v) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) τ₀, Work.Diff.STE.Lead.galE D k₀ ε (c t) ≤ B) := by
  classical
  -- ## The energy of the origin, and `B ≥ 1`
  have hE0eq : ∀ (ε : ℝ), Work.Diff.STE.Lead.galE D k₀ ε
      (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
      = D.ENormB k₀ (g₀.inner) + D.ENormB 0 (g₀.inner) := by
    intro ε
    rw [Work.Diff.STE.Lead.galE, galState_zero_eq D ε]
  have hE0 : ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ ε₁ → Work.Diff.STE.Lead.galE D k₀ ε
      (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ≤ B - 1 := by
    intro ε hε hε1
    rw [hE0eq ε]
    linarith [hB]
  have hB1 : (1 : ℝ) ≤ B := by
    have h1 := Work.Diff.STE.Lead.Gal.galE_nonneg (D := D) k₀ ε₁
      (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε₁ → ℝ)
    have h2 := hE0 ε₁ hε₁ le_rfl
    linarith
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  -- ## Envelope 1: the mollifier is bounded in the pointwise `g₀`-sup-norm
  obtain ⟨CJ, hCJnn, hCJb⟩ :=
    Work.Diff.STE.Lead.GalTame.J_pointwise_le_any (I := I) (M := M) D ρ hρ hρ0 hρs ε₁ hε₁
  -- ## Envelope 3: `galVF2` is bounded on the trap
  obtain ⟨Cb, hCbnn, hCbb⟩ :=
    galVF2_coeff_bound (I := I) (M := M) D hLC ρ hρ hρ0 hρs hg k₀ hk₀ B hB0 ε₁ hε₁
  -- ## Envelope 4: the pinching region is closed
  have hCpt : ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ (hε : 0 < ε),
      IsClosed {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
        Pinched D ρ (1 / 4) ε c} := by
    intro ε hεIoc hε
    have hset : {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
          Pinched D ρ (1 / 4) ε c}
        = {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
            ∀ (x : M) (v : TangentSpace I x),
              (1 / 4 : ℝ) * g₀.inner x v v
                ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v} := rfl
    rw [hset]
    exact pinched_closed (I := I) (M := M) D ρ (1 / 4) ε hε hρ0
  -- ## Envelope 2: the pointwise bound for the velocity `genMap (galVF2 c)` on the trap
  --
  -- `genMap D ε (galVF2 … c) = J ρ ε (P u~)` on the positivity region, where `u~ = J ρ ε (galState
  -- D ε c)`; the claimed bound (with constants uniform in `ε ∈ (0, ε₁]`) is the content of
  -- `Work.Diff.STE.Lead.GalTame.galVF2_velocity_bound`, proved by bounding the DeTurck tensor `P u~`
  -- pointwise (`deTurck_bound`), the upper pinching `u~ ≤ K g₀` by the uniform Sobolev bound, and
  -- then the mollifier by `J_pointwise_le_any`.
  obtain ⟨CV, hCVnn, hCVb⟩ :=
    Work.Diff.STE.Lead.GalTame.galVF2_velocity_bound (I := I) (M := M) D hLC ρ hρ hρ0 hρs hg
      k₀ hk₀ B hB0 ε₁ hε₁
  -- ## Assembly
  exact trapped_of_envelope_strong (D := D) (hLC := hLC) (ρ := ρ) (hρ := hρ) (hρ0 := hρ0)
    (hρs := hρs) (hρ1 := hρ1) (hg := hg) (k₀ := k₀) (B := B) (ε₁ := ε₁)
    (hB := hBpos) (hE0 := hE0) (hseed := hseed) (Cof := Cof) (hCof := hCof) (hapr := hapr)
    (hJpt := ⟨CJ, hCJnn, hCJb⟩) (hVel := ⟨CV, hCVnn, hCVb⟩) (hM := ⟨Cb, hCbnn, hCbb⟩)
    (hCpt := hCpt)

end

end Work.Diff.STE.Lead.GalTame
